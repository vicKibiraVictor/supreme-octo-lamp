// Uniswap v4 Triangular MEV Arbitrage Engine — Base mainnet (chain 8453)
//
// Flow:
//   Bootstrap  → scan all PoolManager Initialize logs → enrich via StateView → build graph
//   Detection  → Bellman-Ford on -ln(rate) weighted edges → negative cycle = profit
//   Validation → REVM simulation with forked state + Balancer flash loan patch
//   Execution  → sign EIP-1559 tx → Flashbots bundle → next block
//   Live sync  → WebSocket Swap/ModifyLiquidity stream → refresh only changed pools
//
// Required env vars:
//   BASE_HTTP_RPC, BASE_WS_RPC, PRIVATE_KEY, EXECUTOR_ADDR, TREASURY_ADDR

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
    time::Duration,
};

use anyhow::{anyhow, bail, Context, Result};
use ethers::{
    abi::{encode as abi_encode, Token},
    prelude::*,
    providers::{Http, Provider, Ws},
    signers::{LocalWallet, Signer},
    types::{
        transaction::eip2718::TypedTransaction, BlockId, BlockNumber, Bytes,
        Eip1559TransactionRequest, Filter, H160, H256, U256, U64,
    },
    utils::keccak256,
};
use ethers_flashbots::{BundleRequest, FlashbotsMiddleware};
use futures::future::join_all;
use petgraph::{
    algo::find_negative_cycle,
    graph::{DiGraph, NodeIndex},
    visit::EdgeRef,
};
use revm::{
    db::{CacheDB, EmptyDB, EthersDB},
    primitives::{
        keccak256 as revm_keccak256, AccountInfo, Address as B160, ExecutionResult, TransactTo,
        U256 as rU256,
    },
    Database, EVM,
};
use tokio::{sync::RwLock, time::sleep};
use tracing::{debug, error, info, warn};
use url::Url;

// ── Constants ─────────────────────────────────────────────────────────────────

const POOL_MANAGER_ADDR: &str = "0x498581ff718922c3f8e6a244956af099B2652b2b";
const STATE_VIEW_ADDR: &str = "0xa3c0c9b65bad0b08107aa264b0f3db444b867a71";
const BALANCER_VAULT_ADDR: &str = "0xBA12222222228d8Ba445958a75a0704d566BF2C8";
const FLASHBOTS_RELAY_URL: &str = "https://relay.flashbots.net";
const CHAIN_ID: u64 = 8453;
const V4_DEPLOY_BLOCK: u64 = 23_145_980;
const LOG_PAGE_SIZE: u64 = 2_000;
const LOAN_MIN_WEI: u128 = 1_000_000_000_000_000_000;
const LOAN_MAX_WEI: u128 = 15_000_000_000_000_000_000;
const LOAN_LIQUIDITY_FRACTION: f64 = 0.003;
const GAS_LIMIT: u64 = 700_000;
const MIN_LIQUIDITY_RAW: u128 = 50_000_000_000;
const BOOTSTRAP_CONCURRENCY: usize = 20;

// keccak256 of each event signature — verified against Base mainnet logs
const TOPIC_INITIALIZE: &str = "0xdd466e674ea557f56295e2d0218a125ea4b4f0f6f3307b95f85e6110838d6438";
const TOPIC_SWAP: &str = "0x40e9cecb9f5f1f1c5b9c97dec2917b7ee92e57ba5563708daca94dd84ad7112f";
const TOPIC_MODIFY_LIQ: &str = "0xf208f4912782fd25c7f114ca3723a2d5dd6f3bcc3ac8db5af63baa85f711d5ec";

// ── Core types ────────────────────────────────────────────────────────────────

type PoolId = [u8; 32];

#[derive(Debug, Clone)]
struct Edge {
    pool_id: PoolId,
    zero_for_one: bool,
    weight: f64,
    rate: f64,
}

#[derive(Debug, Clone)]
struct Pool {
    pool_id: PoolId,
    token0: H160,
    token1: H160,
    lp_fee: u32,
    protocol_fee: u32,
    hook: H160,
    tick_spacing: i32,
    liquidity: u128,
    sqrt_price_x96: U256,
    tick: i32,
}

impl Pool {
    fn swap_fee_ppm(&self) -> u64 {
        let p = self.protocol_fee as u64;
        let l = self.lp_fee as u64;
        p + l - (p * l) / 1_000_000
    }

    fn fee_multiplier(&self) -> f64 {
        1.0 - (self.swap_fee_ppm() as f64) / 1_000_000.0
    }

    fn rate_1_per_0(&self) -> f64 {
        let s = self.sqrt_price_x96.as_u128() as f64 / 2f64.powi(96);
        s * s * self.fee_multiplier()
    }

    fn rate_0_per_1(&self) -> f64 {
        let denom = (self.sqrt_price_x96.as_u128() as f64 / 2f64.powi(96)).powi(2);
        if denom == 0.0 {
            return 0.0;
        }
        (1.0 / denom) * self.fee_multiplier()
    }

    fn hook_accepted(&self) -> bool {
        self.hook == H160::zero()
    }
    fn liquidity_ok(&self) -> bool {
        self.liquidity >= MIN_LIQUIDITY_RAW
    }
}

#[derive(Debug, Clone)]
struct PoolKey {
    token0: H160,
    token1: H160,
    fee: u32,
    tick_spacing: i32,
    hook: H160,
}

#[derive(Debug, Clone)]
struct Candidate {
    token_a: H160,
    token_b: H160,
    token_c: H160,
    pool_ab: PoolId,
    key_ab: PoolKey,
    dir_ab: bool,
    pool_bc: PoolId,
    key_bc: PoolKey,
    dir_bc: bool,
    pool_ca: PoolId,
    key_ca: PoolKey,
    dir_ca: bool,
    loan_amount: U256,
    estimated_out: U256,
    sim_passed: bool,
    sim_net_profit: U256,
}

// ── Safe signed integer decoding ──────────────────────────────────────────────
//
// ABI-encodes int24 as a full 32-byte two's-complement word (sign-extended to
// 256 bits).  Negative values therefore appear as very large U256 numbers and
// will panic inside U256::as_u32().  We read only the low 32 bits (never
// panics), then arithmetic-shift to recover the sign from bit 23.

fn u256_to_i24(v: U256) -> i32 {
    // low_u32() truncates to the lowest 32 bits — never panics regardless of
    // how large the U256 value is.
    let low = v.low_u32() as i32;
    // Shift left 8 bits so bit 23 lands at bit 31 (the i32 sign bit),
    // then arithmetic-shift right 8 bits to restore the original magnitude
    // while propagating the sign.  This correctly sign-extends a 24-bit
    // two's-complement value into a full i32.
    (low << 8) >> 8
}

// ── Graph state ───────────────────────────────────────────────────────────────
//
// meta_graph   DiGraph<H160, Edge> — pool metadata; used when building Candidates
// weight_graph DiGraph<H160, f64>  — bare weights only; required by Bellman-Ford
//
// Both graphs share NodeIndex values (added in lockstep) and are kept in sync
// via sync_weight_graph() after every structural change to meta_graph.

struct EngineState {
    pools: HashMap<PoolId, Pool>,
    meta_graph: DiGraph<H160, Edge>,
    weight_graph: DiGraph<H160, f64>,
    node_map: HashMap<H160, NodeIndex>,
    balance_slot_cache: HashMap<H160, u32>,
}

impl EngineState {
    fn new() -> Self {
        Self {
            pools: HashMap::new(),
            meta_graph: DiGraph::new(),
            weight_graph: DiGraph::new(),
            node_map: HashMap::new(),
            balance_slot_cache: HashMap::new(),
        }
    }

    fn get_or_add_node(&mut self, token: H160) -> NodeIndex {
        if let Some(&idx) = self.node_map.get(&token) {
            return idx;
        }
        let idx = self.meta_graph.add_node(token);
        let idx2 = self.weight_graph.add_node(token);
        debug_assert_eq!(idx, idx2, "graph node index mismatch");
        self.node_map.insert(token, idx);
        debug!(token = ?token, node_idx = idx.index(), "Graph: new token node added");
        idx
    }

    fn upsert_pool_edges(&mut self, pool: &Pool) {
        self.meta_graph
            .retain_edges(|g, e| g[e].pool_id != pool.pool_id);

        if !pool.hook_accepted() {
            debug!(
                pool_id = hex::encode(pool.pool_id),
                hook = ?pool.hook,
                "Pool excluded: non-zero hook"
            );
            return;
        }
        if pool.sqrt_price_x96.is_zero() || pool.liquidity == 0 {
            debug!(
                pool_id = hex::encode(pool.pool_id),
                sqrt_price = ?pool.sqrt_price_x96,
                liquidity = pool.liquidity,
                "Pool excluded: zero price or zero liquidity"
            );
            return;
        }
        if !pool.liquidity_ok() {
            debug!(
                pool_id = hex::encode(pool.pool_id),
                liq = pool.liquidity,
                min = MIN_LIQUIDITY_RAW,
                "Pool excluded: below liquidity threshold"
            );
            return;
        }

        let n0 = self.get_or_add_node(pool.token0);
        let n1 = self.get_or_add_node(pool.token1);
        let r10 = pool.rate_1_per_0();
        let r01 = pool.rate_0_per_1();

        debug!(
            pool_id = hex::encode(pool.pool_id),
            token0 = ?pool.token0,
            token1 = ?pool.token1,
            rate_1_per_0 = r10,
            rate_0_per_1 = r01,
            liquidity = pool.liquidity,
            tick = pool.tick,
            lp_fee = pool.lp_fee,
            protocol_fee = pool.protocol_fee,
            "Graph: upserting pool edges"
        );

        if r10 > 0.0 {
            self.meta_graph.add_edge(
                n0,
                n1,
                Edge {
                    pool_id: pool.pool_id,
                    zero_for_one: true,
                    weight: -r10.ln(),
                    rate: r10,
                },
            );
            debug!(
                pool_id = hex::encode(pool.pool_id),
                direction = "token0→token1",
                weight = -r10.ln(),
                rate = r10,
                "Graph: edge added"
            );
        }
        if r01 > 0.0 {
            self.meta_graph.add_edge(
                n1,
                n0,
                Edge {
                    pool_id: pool.pool_id,
                    zero_for_one: false,
                    weight: -r01.ln(),
                    rate: r01,
                },
            );
            debug!(
                pool_id = hex::encode(pool.pool_id),
                direction = "token1→token0",
                weight = -r01.ln(),
                rate = r01,
                "Graph: edge added"
            );
        }

        self.sync_weight_graph();
    }

    fn drop_pool_edges(&mut self, pool_id: PoolId) {
        debug!(pool_id = hex::encode(pool_id), "Graph: dropping edges for pool");
        self.meta_graph.retain_edges(|g, e| g[e].pool_id != pool_id);
        self.sync_weight_graph();
    }

    fn sync_weight_graph(&mut self) {
        self.weight_graph.clear_edges();
        for e in self.meta_graph.edge_references() {
            self.weight_graph
                .add_edge(e.source(), e.target(), e.weight().weight);
        }
        debug!(
            nodes = self.weight_graph.node_count(),
            edges = self.weight_graph.edge_count(),
            "Graph: weight_graph synced"
        );
    }
}

// ── StateView RPC calls ───────────────────────────────────────────────────────

async fn call_get_slot0(provider: &Provider<Http>, pool_id: PoolId) -> Result<(U256, i32, u8, u8)> {
    debug!(pool_id = hex::encode(pool_id), "StateView: calling getSlot0");
    let mut cd = hex::decode("4c73e8ed")?;
    cd.extend_from_slice(&pool_id);

    let sv: H160 = STATE_VIEW_ADDR.parse()?;
    let raw = provider
        .call(&TransactionRequest::new().to(sv).data(cd).into(), None)
        .await
        .context("getSlot0 failed")?;

    if raw.len() < 128 {
        bail!("getSlot0: short response ({} bytes)", raw.len());
    }

    let sqrt_price = U256::from_big_endian(&raw[0..32]);

    let tick_raw = U256::from_big_endian(&raw[32..64]).as_u64() as i64;
    let tick = if tick_raw & (1 << 23) != 0 {
        (tick_raw | !((1i64 << 24) - 1)) as i32
    } else {
        tick_raw as i32
    };

    let protocol_fee = raw[63];
    let lp_fee = raw[95];

    debug!(
        pool_id = hex::encode(pool_id),
        sqrt_price = ?sqrt_price,
        tick,
        protocol_fee,
        lp_fee,
        "StateView: getSlot0 OK"
    );

    Ok((sqrt_price, tick, protocol_fee, lp_fee))
}

async fn call_get_liquidity(provider: &Provider<Http>, pool_id: PoolId) -> Result<u128> {
    debug!(pool_id = hex::encode(pool_id), "StateView: calling getLiquidity");
    let mut cd = hex::decode("4e33be86")?;
    cd.extend_from_slice(&pool_id);

    let sv: H160 = STATE_VIEW_ADDR.parse()?;
    let raw = provider
        .call(&TransactionRequest::new().to(sv).data(cd).into(), None)
        .await
        .context("getLiquidity failed")?;

    if raw.len() < 32 {
        bail!("getLiquidity: short response ({} bytes)", raw.len());
    }
    let liq = U256::from_big_endian(&raw[0..32]).as_u128();
    debug!(pool_id = hex::encode(pool_id), liquidity = liq, "StateView: getLiquidity OK");
    Ok(liq)
}

async fn enrich_pool(provider: &Provider<Http>, pool: &mut Pool) -> Result<()> {
    debug!(pool_id = hex::encode(pool.pool_id), "Enriching pool from StateView");
    let (slot0_res, liq_res) = tokio::join!(
        call_get_slot0(provider, pool.pool_id),
        call_get_liquidity(provider, pool.pool_id),
    );
    let (sqrt_price, tick, protocol_fee, lp_fee) = slot0_res?;
    let liquidity = liq_res?;

    pool.sqrt_price_x96 = sqrt_price;
    pool.tick = tick;
    pool.protocol_fee = protocol_fee as u32;
    pool.lp_fee = lp_fee as u32;
    pool.liquidity = liquidity;

    debug!(
        pool_id = hex::encode(pool.pool_id),
        token0 = ?pool.token0,
        token1 = ?pool.token1,
        sqrt_price = ?pool.sqrt_price_x96,
        tick = pool.tick,
        liquidity = pool.liquidity,
        lp_fee = pool.lp_fee,
        protocol_fee = pool.protocol_fee,
        "Pool enrichment complete"
    );
    Ok(())
}

// ── Pool discovery ────────────────────────────────────────────────────────────

fn parse_initialize_log(log: &ethers::types::Log) -> Option<Pool> {
    if log.topics.len() < 4 {
        debug!(
            tx = ?log.transaction_hash,
            topics = log.topics.len(),
            "Initialize log: skipped — too few topics"
        );
        return None;
    }

    let pool_id: PoolId = log.topics[1].into();
    let token0 = H160::from(log.topics[2]);
    let token1 = H160::from(log.topics[3]);

    let data = log.data.as_ref();
    if data.len() < 160 {
        debug!(
            pool_id = hex::encode(pool_id),
            data_len = data.len(),
            "Initialize log: skipped — data too short"
        );
        return None;
    }

    let fee = U256::from_big_endian(&data[0..32]).low_u32();

    // ── FIX: tick_spacing is ABI-encoded as int24 (sign-extended to 256 bits).
    // Negative values appear as huge U256 numbers and would panic with as_u32().
    // u256_to_i24() reads only the low 32 bits then arithmetic-shifts to recover
    // the sign, which is always safe.
    let tick_spacing = u256_to_i24(U256::from_big_endian(&data[32..64]));

    let hook = H160::from_slice(&data[76..96]);
    let sqrt_price = U256::from_big_endian(&data[96..128]);

    // ── FIX: tick is also ABI-encoded as int24; same treatment.
    let tick = u256_to_i24(U256::from_big_endian(&data[128..160]));

    debug!(
        pool_id = hex::encode(pool_id),
        token0 = ?token0,
        token1 = ?token1,
        fee,
        tick_spacing,
        hook = ?hook,
        sqrt_price = ?sqrt_price,
        tick,
        "Initialize log: parsed OK"
    );

    Some(Pool {
        pool_id,
        token0,
        token1,
        lp_fee: fee,
        protocol_fee: 0,
        hook,
        tick_spacing,
        liquidity: 0,
        sqrt_price_x96: sqrt_price,
        tick,
    })
}

async fn discover_pools(provider: &Provider<Http>) -> Result<Vec<Pool>> {
    let pm: H160 = POOL_MANAGER_ADDR.parse()?;
    let topic: H256 = TOPIC_INITIALIZE.parse()?;
    let latest = provider.get_block_number().await?.as_u64();

    info!(
        from_block = V4_DEPLOY_BLOCK,
        to_block = latest,
        page_size = LOG_PAGE_SIZE,
        "Discovery: scanning Initialize logs"
    );

    let mut pools = Vec::new();
    let mut from = V4_DEPLOY_BLOCK;
    let mut page = 0u64;

    while from <= latest {
        let to = (from + LOG_PAGE_SIZE - 1).min(latest);
        page += 1;

        debug!(page, from_block = from, to_block = to, "Discovery: fetching log page");

        let filter = Filter::new()
            .address(pm)
            .topic0(topic)
            .from_block(from)
            .to_block(to);

        let logs = provider.get_logs(&filter).await.unwrap_or_else(|e| {
            warn!(page, from_block = from, to_block = to, error = %e, "Discovery: get_logs failed, skipping page");
            vec![]
        });

        debug!(page, log_count = logs.len(), "Discovery: logs received for page");

        let before = pools.len();
        for log in &logs {
            if let Some(pool) = parse_initialize_log(log) {
                pools.push(pool);
            }
        }
        let parsed = pools.len() - before;

        debug!(page, parsed, total_so_far = pools.len(), "Discovery: page done");

        from = to + 1;
        sleep(Duration::from_millis(30)).await;
    }

    info!(total_pools_found = pools.len(), pages = page, "Discovery: complete");
    Ok(pools)
}

// ── Bellman-Ford cycle detection ──────────────────────────────────────────────
//
// Edge weight = -ln(rate). A negative-weight cycle means rate_A * rate_B * rate_C > 1,
// i.e. a round trip returns more than it started with — textbook arbitrage transform.

fn find_triangular_cycles(state: &EngineState) -> Vec<[NodeIndex; 3]> {
    debug!(
        nodes = state.weight_graph.node_count(),
        edges = state.weight_graph.edge_count(),
        "Bellman-Ford: starting cycle search"
    );

    let mut seen: HashSet<[u32; 3]> = HashSet::new();
    let mut out = Vec::new();

    for start in state.weight_graph.node_indices() {
        if state.weight_graph.edges(start).next().is_none() {
            continue;
        }
        if let Some(cycle) = find_negative_cycle(&state.weight_graph, start) {
            if cycle.len() != 3 {
                debug!(
                    cycle_len = cycle.len(),
                    "Bellman-Ford: non-triangular cycle ignored"
                );
                continue;
            }
            let mut key = [
                cycle[0].index() as u32,
                cycle[1].index() as u32,
                cycle[2].index() as u32,
            ];
            key.sort_unstable();
            if seen.insert(key) {
                debug!(
                    node_a = cycle[0].index(),
                    node_b = cycle[1].index(),
                    node_c = cycle[2].index(),
                    "Bellman-Ford: triangular negative cycle found"
                );
                out.push([cycle[0], cycle[1], cycle[2]]);
            }
        }
    }

    debug!(cycles_found = out.len(), "Bellman-Ford: search complete");
    out
}

fn dynamic_loan_size(pool_liquidities: [u128; 3]) -> U256 {
    let min_liq = pool_liquidities.iter().copied().min().unwrap_or(0);
    let raw = (min_liq as f64 * LOAN_LIQUIDITY_FRACTION) as u128;
    let loan = raw.max(LOAN_MIN_WEI).min(LOAN_MAX_WEI);
    debug!(
        min_liquidity = min_liq,
        raw_loan = raw,
        clamped_loan = loan,
        "Loan size: calculated"
    );
    U256::from(loan)
}

fn build_candidate(
    cycle: &[NodeIndex; 3],
    state: &EngineState,
    gas_price_wei: U256,
) -> Option<Candidate> {
    let mut tokens = [H160::zero(); 3];
    let mut pool_ids = [[0u8; 32]; 3];
    let mut dirs = [false; 3];
    let mut rates = [0f64; 3];
    let mut liquidities = [0u128; 3];
    let mut keys: Vec<PoolKey> = Vec::new();

    for i in 0..3 {
        let from = cycle[i];
        let to = cycle[(i + 1) % 3];

        tokens[i] = *state.meta_graph.node_weight(from)?;

        let edge = state.meta_graph.edges_connecting(from, to).next()?.weight();
        pool_ids[i] = edge.pool_id;
        dirs[i] = edge.zero_for_one;
        rates[i] = edge.rate;

        let pool = state.pools.get(&edge.pool_id)?;
        liquidities[i] = pool.liquidity;
        keys.push(PoolKey {
            token0: pool.token0,
            token1: pool.token1,
            fee: pool.lp_fee,
            tick_spacing: pool.tick_spacing,
            hook: pool.hook,
        });
    }

    let loan = dynamic_loan_size(liquidities);
    let cumulative = rates[0] * rates[1] * rates[2];

    debug!(
        token_a = ?tokens[0],
        token_b = ?tokens[1],
        token_c = ?tokens[2],
        rate_ab = rates[0],
        rate_bc = rates[1],
        rate_ca = rates[2],
        cumulative_rate = cumulative,
        loan = ?loan,
        "Candidate: evaluating cycle"
    );

    if cumulative <= 1.0 {
        debug!(cumulative_rate = cumulative, "Candidate: rejected — cumulative rate ≤ 1.0");
        return None;
    }

    let est_out = U256::from((loan.as_u128() as f64 * cumulative) as u128);
    let gas_cost = gas_price_wei * U256::from(GAS_LIMIT);

    debug!(
        est_out = ?est_out,
        loan = ?loan,
        gas_cost = ?gas_cost,
        "Candidate: profitability pre-check"
    );

    if est_out <= loan + gas_cost {
        debug!("Candidate: rejected — estimated output does not cover loan + gas");
        return None;
    }

    debug!(
        token_a = ?tokens[0],
        token_b = ?tokens[1],
        token_c = ?tokens[2],
        pool_ab = hex::encode(pool_ids[0]),
        pool_bc = hex::encode(pool_ids[1]),
        pool_ca = hex::encode(pool_ids[2]),
        est_out = ?est_out,
        "Candidate: accepted for simulation"
    );

    Some(Candidate {
        token_a: tokens[0],
        token_b: tokens[1],
        token_c: tokens[2],
        pool_ab: pool_ids[0],
        key_ab: keys[0].clone(),
        dir_ab: dirs[0],
        pool_bc: pool_ids[1],
        key_bc: keys[1].clone(),
        dir_bc: dirs[1],
        pool_ca: pool_ids[2],
        key_ca: keys[2].clone(),
        dir_ca: dirs[2],
        loan_amount: loan,
        estimated_out: est_out,
        sim_passed: false,
        sim_net_profit: U256::zero(),
    })
}

// ── ERC-20 balance slot discovery ─────────────────────────────────────────────
//
// Tries slots 0..29 against a probe address to find where balanceOf() is stored.
// Covers OpenZeppelin, Solmate, WETH, and most standard ERC-20 layouts.

async fn find_balance_slot(provider: &Provider<Http>, token: H160) -> u32 {
    debug!(token = ?token, "Balance slot: probing ERC-20 storage layout");
    let probe = H160::from_low_u64_be(1);

    let real_bal = {
        let mut cd = hex::decode("70a08231").unwrap();
        cd.extend_from_slice(&[0u8; 12]);
        cd.extend_from_slice(probe.as_bytes());
        let raw = provider
            .call(&TransactionRequest::new().to(token).data(cd).into(), None)
            .await
            .unwrap_or_default();
        if raw.len() >= 32 {
            U256::from_big_endian(&raw[0..32])
        } else {
            U256::zero()
        }
    };

    debug!(token = ?token, probe = ?probe, balance = ?real_bal, "Balance slot: probe address balance fetched");

    for slot in 0u32..30 {
        let key_h256 = H256::from(keccak256({
            let mut b = [0u8; 64];
            b[12..32].copy_from_slice(probe.as_bytes());
            b[60..64].copy_from_slice(&slot.to_be_bytes());
            b
        }));
        let stored = provider
            .get_storage_at(token, key_h256, None)
            .await
            .unwrap_or(H256::zero());
        let stored_u256 = U256::from_big_endian(stored.as_bytes());
        if stored_u256 == real_bal && !real_bal.is_zero() {
            debug!(token = ?token, slot, "Balance slot: found at slot");
            return slot;
        }
    }

    warn!(token = ?token, "Balance slot: not found in slots 0-29, defaulting to 0");
    0
}

fn mapping_slot_key(account: H160, mapping_slot: u32) -> rU256 {
    let mut preimage = [0u8; 64];
    preimage[12..32].copy_from_slice(account.as_bytes());
    preimage[60..64].copy_from_slice(&mapping_slot.to_be_bytes());
    rU256::from_be_bytes(revm_keccak256(&preimage).0)
}

// ── REVM simulation ───────────────────────────────────────────────────────────
//
// Forks live state into CacheDB<EmptyDB>, patches the Balancer Vault balance so
// the flash loan succeeds, runs transact_commit(), then compares treasury token_a
// balance before and after. Returns (passed, net_profit_after_gas).

fn build_calldata(c: &Candidate, treasury: H160) -> Bytes {
    let sig = "execute(address,uint256,(address,address,address,address,uint24,int24,address,uint256,uint256)[3],address)";
    let selector = &keccak256(sig.as_bytes())[0..4];

    let make_step = |tin: H160, tout: H160, key: &PoolKey, amount_in: U256| -> Token {
        Token::Tuple(vec![
            Token::Address(tin),
            Token::Address(tout),
            Token::Address(key.token0),
            Token::Address(key.token1),
            Token::Uint(U256::from(key.fee)),
            Token::Int(U256::from(key.tick_spacing.unsigned_abs())),
            Token::Address(key.hook),
            Token::Uint(amount_in),
            Token::Uint(U256::zero()),
        ])
    };

    let encoded = abi_encode(&[
        Token::Address(c.token_a),
        Token::Uint(c.loan_amount),
        Token::FixedArray(vec![
            make_step(c.token_a, c.token_b, &c.key_ab, c.loan_amount),
            make_step(c.token_b, c.token_c, &c.key_bc, U256::zero()),
            make_step(c.token_c, c.token_a, &c.key_ca, U256::zero()),
        ]),
        Token::Address(treasury),
    ]);

    let mut out = selector.to_vec();
    out.extend_from_slice(&encoded);
    Bytes::from(out)
}

async fn simulate(
    c: &Candidate,
    http_rpc: &str,
    block_number: u64,
    executor_addr: H160,
    treasury: H160,
    gas_price_wei: U256,
    balance_slot: u32,
) -> Result<(bool, U256)> {
    debug!(
        token_a = ?c.token_a,
        token_b = ?c.token_b,
        token_c = ?c.token_c,
        block_number,
        loan = ?c.loan_amount,
        balance_slot,
        "Simulation: starting REVM fork"
    );

    let provider = Arc::new(Provider::<Http>::try_from(http_rpc).context("REVM http provider")?);
    let block_id = Some(BlockId::Number(BlockNumber::Number(U64::from(
        block_number,
    ))));

    let mut ethers_db = EthersDB::new(Arc::clone(&provider), block_id)
        .ok_or_else(|| anyhow!("EthersDB::new returned None — check RPC URL"))?;

    let token_a_b160: B160 = B160::from(c.token_a.0);
    let executor_b160: B160 = B160::from(executor_addr.0);
    let vault_b160: B160 = B160::from(BALANCER_VAULT_ADDR.parse::<H160>()?.0);
    let treasury_b160: B160 = B160::from(treasury.0);
    let pm_b160: B160 = B160::from(POOL_MANAGER_ADDR.parse::<H160>()?.0);

    debug!("Simulation: loading account state into CacheDB");
    let mut cache_db = CacheDB::new(EmptyDB::default());
    for addr in [
        token_a_b160,
        vault_b160,
        executor_b160,
        treasury_b160,
        pm_b160,
    ] {
        if let Ok(Some(info)) = ethers_db.basic(addr) {
            cache_db.insert_account_info(addr, info);
        }
    }

    let vault_balance_slot = mapping_slot_key(BALANCER_VAULT_ADDR.parse::<H160>()?, balance_slot);
    let treasury_slot = mapping_slot_key(treasury, balance_slot);

    let bal_before: rU256 = ethers_db
        .storage(token_a_b160, treasury_slot)
        .unwrap_or(rU256::ZERO);

    debug!(
        treasury_balance_before = ?bal_before,
        loan = ?c.loan_amount,
        "Simulation: patching Balancer Vault balance for flash loan"
    );

    cache_db
        .insert_account_storage(
            token_a_b160,
            vault_balance_slot,
            rU256::from(c.loan_amount.as_u128()),
        )
        .map_err(|e| anyhow!("vault balance patch: {:?}", e))?;

    cache_db.insert_account_info(
        executor_b160,
        AccountInfo {
            balance: rU256::from(10u128.pow(20)),
            nonce: 1,
            code_hash: revm::primitives::KECCAK_EMPTY,
            code: None,
        },
    );

    let calldata = build_calldata(c, treasury);
    debug!(calldata_len = calldata.len(), "Simulation: calldata built");

    let mut evm = EVM::new();
    evm.database(cache_db);
    evm.env.block.number = rU256::from(block_number + 1);
    evm.env.block.gas_limit = rU256::from(30_000_000u64);
    evm.env.tx.caller = executor_b160;
    evm.env.tx.transact_to = TransactTo::Call(executor_b160);
    evm.env.tx.data = calldata.0.to_vec().into();
    evm.env.tx.value = rU256::ZERO;
    evm.env.tx.gas_limit = GAS_LIMIT;
    evm.env.tx.gas_price = rU256::from(gas_price_wei.as_u128());

    debug!("Simulation: calling transact_commit");
    let result = evm
        .transact_commit()
        .map_err(|e| anyhow!("REVM transact_commit: {:?}", e))?;

    let gas_used: u64 = match result {
        ExecutionResult::Success { gas_used, .. } => {
            debug!(gas_used, "Simulation: execution succeeded");
            gas_used
        }
        ExecutionResult::Revert { output, gas_used, .. } => {
            debug!(
                gas_used,
                reason = %String::from_utf8_lossy(&output),
                "Simulation: execution reverted"
            );
            return Ok((false, U256::zero()));
        }
        ExecutionResult::Halt { reason, gas_used, .. } => {
            debug!(gas_used, reason = ?reason, "Simulation: execution halted");
            return Ok((false, U256::zero()));
        }
    };

    let bal_after: rU256 = evm
        .db
        .as_ref()
        .and_then(|db| db.accounts.get(&token_a_b160))
        .and_then(|acc| acc.storage.get(&treasury_slot))
        .copied()
        .unwrap_or(bal_before);

    debug!(
        treasury_balance_before = ?bal_before,
        treasury_balance_after = ?bal_after,
        "Simulation: treasury balance comparison"
    );

    if bal_after <= bal_before {
        debug!("Simulation: no treasury balance increase — not profitable");
        return Ok((false, U256::zero()));
    }

    let diff = bal_after - bal_before;
    let limbs = diff.as_limbs();
    let gross_gain = U256::from(limbs[0] as u128 | ((limbs[1] as u128) << 64));
    let gas_cost = gas_price_wei * U256::from(gas_used);

    debug!(
        gross_gain = ?gross_gain,
        gas_cost = ?gas_cost,
        gas_used,
        "Simulation: gross gain vs gas cost"
    );

    if gross_gain <= gas_cost {
        debug!("Simulation: profitable before gas but not after — rejected");
        return Ok((false, U256::zero()));
    }

    let net = gross_gain - gas_cost;
    debug!(net_profit = ?net, "Simulation: net profitable — passed");
    Ok((true, net))
}

// ── Flashbots submission ──────────────────────────────────────────────────────

async fn submit_bundle(
    c: &Candidate,
    treasury: H160,
    executor_addr: H160,
    wallet: &LocalWallet,
    http_rpc: &str,
) -> Result<()> {
    info!(
        token_a = ?c.token_a,
        token_b = ?c.token_b,
        token_c = ?c.token_c,
        net_profit = ?c.sim_net_profit,
        "Bundle: preparing submission"
    );

    let provider = Provider::<Http>::try_from(http_rpc).context("submission http provider")?;
    let chain_id = provider.get_chainid().await?.as_u64();

    debug!(chain_id, "Bundle: chain ID confirmed");

    let fb_middleware = FlashbotsMiddleware::new(
        provider.clone(),
        Url::parse(FLASHBOTS_RELAY_URL).context("invalid relay URL")?,
        wallet.clone().with_chain_id(chain_id),
    );

    let current_block = provider.get_block_number().await?;
    let target_block = current_block.as_u64() + 1;

    let base_fee = provider
        .get_block(BlockNumber::Latest)
        .await?
        .and_then(|b| b.base_fee_per_gas)
        .unwrap_or(U256::from(1_000_000_000u64));
    let priority_fee = U256::from(2_000_000_000u64);
    let max_fee = base_fee * 2 + priority_fee;

    debug!(
        current_block = current_block.as_u64(),
        target_block,
        base_fee = ?base_fee,
        priority_fee = ?priority_fee,
        max_fee = ?max_fee,
        "Bundle: gas pricing"
    );

    let nonce = provider
        .get_transaction_count(wallet.address(), None)
        .await?;
    debug!(nonce = ?nonce, "Bundle: signer nonce fetched");

    let calldata = build_calldata(c, treasury);

    let tx: TypedTransaction = Eip1559TransactionRequest::new()
        .to(executor_addr)
        .data(calldata)
        .nonce(nonce)
        .gas(GAS_LIMIT)
        .max_priority_fee_per_gas(priority_fee)
        .max_fee_per_gas(max_fee)
        .chain_id(chain_id)
        .into();

    let sig = wallet
        .sign_transaction(&tx)
        .await
        .context("tx signing failed")?;
    let signed_bytes = Bytes::from(tx.rlp_signed(&sig).to_vec());

    debug!("Bundle: transaction signed and RLP-encoded");

    let bundle = BundleRequest::new()
        .push_transaction(signed_bytes)
        .set_block(U64::from(target_block))
        .set_simulation_block(current_block);

    let pending = fb_middleware
        .send_bundle(&bundle)
        .await
        .context("send_bundle failed")?;

    info!(
        bundle_hash  = ?pending.bundle_hash,
        target_block,
        net_profit   = ?c.sim_net_profit,
        token_a      = ?c.token_a,
        token_b      = ?c.token_b,
        token_c      = ?c.token_c,
        "Bundle submitted"
    );

    Ok(())
}

// ── Controller ────────────────────────────────────────────────────────────────

struct Controller {
    http_rpc: String,
    ws_rpc: String,
    wallet: LocalWallet,
    executor_addr: H160,
    treasury: H160,
    state: Arc<RwLock<EngineState>>,
}

impl Controller {
    fn new(
        http_rpc: String,
        ws_rpc: String,
        private_key: &str,
        executor_addr: H160,
        treasury: H160,
    ) -> Result<Self> {
        let wallet = private_key
            .parse::<LocalWallet>()
            .context("invalid PRIVATE_KEY")?
            .with_chain_id(CHAIN_ID);
        Ok(Self {
            http_rpc,
            ws_rpc,
            wallet,
            executor_addr,
            treasury,
            state: Arc::new(RwLock::new(EngineState::new())),
        })
    }

    async fn run(&self) -> Result<()> {
        info!("Engine starting — Base chain {}", CHAIN_ID);
        self.bootstrap().await.context("bootstrap failed")?;
        info!(
            pools = self.state.read().await.pools.len(),
            "Bootstrap complete"
        );
        self.event_loop().await
    }

    async fn bootstrap(&self) -> Result<()> {
        info!("Bootstrap: beginning pool discovery");
        let provider = Arc::new(Provider::<Http>::try_from(&self.http_rpc)?);
        let mut raw = discover_pools(&provider).await?;
        info!(found = raw.len(), "Bootstrap: raw pools discovered");

        let mut loaded = 0usize;
        let mut skipped = 0usize;
        let total = raw.len();
        let chunk_count = (total + BOOTSTRAP_CONCURRENCY - 1) / BOOTSTRAP_CONCURRENCY;

        for (chunk_idx, chunk) in raw.chunks_mut(BOOTSTRAP_CONCURRENCY).enumerate() {
            debug!(
                chunk = chunk_idx + 1,
                of = chunk_count,
                chunk_size = chunk.len(),
                "Bootstrap: enriching chunk"
            );

            let futs: Vec<_> = chunk
                .iter_mut()
                .map(|p| enrich_pool(&provider, p))
                .collect();
            let results = join_all(futs).await;

            let mut s = self.state.write().await;
            for (pool, res) in chunk.iter().zip(results) {
                match res {
                    Ok(()) => {
                        s.upsert_pool_edges(pool);
                        s.pools.insert(pool.pool_id, pool.clone());
                        loaded += 1;
                    }
                    Err(e) => {
                        skipped += 1;
                        debug!(
                            pool_id = hex::encode(pool.pool_id),
                            error = %e,
                            "Bootstrap: pool enrichment failed — skipped"
                        );
                    }
                }
            }

            debug!(
                chunk = chunk_idx + 1,
                loaded_so_far = loaded,
                skipped_so_far = skipped,
                "Bootstrap: chunk complete"
            );

            sleep(Duration::from_millis(50)).await;
        }

        info!(
            loaded,
            skipped,
            total,
            graph_nodes = self.state.read().await.meta_graph.node_count(),
            graph_edges = self.state.read().await.meta_graph.edge_count(),
            "Bootstrap: enrichment complete"
        );
        Ok(())
    }

    async fn event_loop(&self) -> Result<()> {
        info!("Event loop: connecting WebSocket");
        let ws = Ws::connect(&self.ws_rpc)
            .await
            .context("WebSocket connect failed")?;
        let ws_provider = Provider::new(ws);
        let http_provider = Provider::<Http>::try_from(&self.http_rpc)?;

        let pm: H160 = POOL_MANAGER_ADDR.parse()?;
        let swap: H256 = TOPIC_SWAP.parse()?;
        let mod_: H256 = TOPIC_MODIFY_LIQ.parse()?;

        let filter = Filter::new().address(pm).topic0(vec![swap, mod_]);
        let mut stream = ws_provider
            .subscribe_logs(&filter)
            .await
            .context("subscribe_logs failed")?;

        info!("Event loop: listening for Swap and ModifyLiquidity events");

        while let Some(log) = stream.next().await {
            let pool_id: PoolId = match log.topics.get(1) {
                Some(t) => (*t).into(),
                None => {
                    debug!("Event loop: log missing topic[1] — skipped");
                    continue;
                }
            };

            let event_kind = if log.topics.get(0).map(|t| format!("{t:?}")) == Some(format!("{swap:?}")) {
                "Swap"
            } else {
                "ModifyLiquidity"
            };

            debug!(
                pool_id = hex::encode(pool_id),
                event = event_kind,
                block = ?log.block_number,
                tx = ?log.transaction_hash,
                "Event loop: pool event received"
            );

            self.refresh_pool(&http_provider, pool_id).await;

            if let Err(e) = self.search_and_execute(&http_provider).await {
                warn!(error = %e, "Event loop: search_and_execute error");
            }
        }

        Err(anyhow!("Event loop: WebSocket stream closed"))
    }

    async fn refresh_pool(&self, provider: &Provider<Http>, pool_id: PoolId) {
        debug!(pool_id = hex::encode(pool_id), "Refresh: updating pool state");

        let mut state = self.state.write().await;
        let pool = match state.pools.get_mut(&pool_id) {
            Some(p) => p,
            None => {
                debug!(pool_id = hex::encode(pool_id), "Refresh: pool not in local state — skipped");
                return;
            }
        };
        match enrich_pool(provider, pool).await {
            Ok(()) => {
                let updated = pool.clone();
                debug!(pool_id = hex::encode(pool_id), "Refresh: pool enriched, upserting edges");
                state.upsert_pool_edges(&updated);
            }
            Err(e) => {
                debug!(
                    pool_id = hex::encode(pool_id),
                    error = %e,
                    "Refresh: enrichment failed — dropping edges"
                );
                state.drop_pool_edges(pool_id);
            }
        }
    }

    async fn search_and_execute(&self, provider: &Provider<Http>) -> Result<()> {
        debug!("Search: fetching block number and gas price");

        let (block_res, gas_res) =
            tokio::join!(provider.get_block_number(), provider.get_gas_price());
        let block_number = block_res?.as_u64();
        let gas_price = gas_res.unwrap_or(U256::from(1_000_000_000u64));

        debug!(block_number, gas_price = ?gas_price, "Search: block and gas price fetched");

        let cycles: Vec<[NodeIndex; 3]> = {
            let state = self.state.read().await;
            find_triangular_cycles(&state)
        };

        debug!(cycle_count = cycles.len(), "Search: cycles found");

        if cycles.is_empty() {
            debug!("Search: no negative cycles — nothing to do");
            return Ok(());
        }

        let mut candidates: Vec<Candidate> = {
            let state = self.state.read().await;
            cycles
                .iter()
                .filter_map(|cyc| build_candidate(cyc, &state, gas_price))
                .collect()
        };

        debug!(candidate_count = candidates.len(), "Search: candidates after pre-sim filter");

        if candidates.is_empty() {
            debug!("Search: no candidates survive profitability pre-check");
            return Ok(());
        }

        candidates.sort_by(|a, b| b.estimated_out.cmp(&a.estimated_out));
        debug!(
            top_est_out = ?candidates[0].estimated_out,
            "Search: candidates sorted by estimated output"
        );

        for (i, mut c) in candidates.into_iter().enumerate() {
            debug!(
                rank = i + 1,
                token_a = ?c.token_a,
                token_b = ?c.token_b,
                token_c = ?c.token_c,
                est_out = ?c.estimated_out,
                "Search: simulating candidate"
            );

            let balance_slot = {
                let cached = self
                    .state
                    .read()
                    .await
                    .balance_slot_cache
                    .get(&c.token_a)
                    .copied();
                match cached {
                    Some(s) => {
                        debug!(token_a = ?c.token_a, slot = s, "Search: balance slot from cache");
                        s
                    }
                    None => {
                        debug!(token_a = ?c.token_a, "Search: balance slot not cached — probing");
                        let s = find_balance_slot(provider, c.token_a).await;
                        self.state
                            .write()
                            .await
                            .balance_slot_cache
                            .insert(c.token_a, s);
                        s
                    }
                }
            };

            let (passed, net_profit) = simulate(
                &c,
                &self.http_rpc,
                block_number,
                self.executor_addr,
                self.treasury,
                gas_price,
                balance_slot,
            )
            .await
            .unwrap_or_else(|e| {
                warn!(error = %e, "Search: simulation error — treating as failed");
                (false, U256::zero())
            });

            debug!(
                rank = i + 1,
                passed,
                net_profit = ?net_profit,
                token_a = ?c.token_a,
                "Search: simulation result"
            );

            if passed {
                c.sim_passed = true;
                c.sim_net_profit = net_profit;

                info!(
                    token_a    = ?c.token_a,
                    token_b    = ?c.token_b,
                    token_c    = ?c.token_c,
                    net_profit = ?net_profit,
                    pool_ab    = hex::encode(c.pool_ab),
                    pool_bc    = hex::encode(c.pool_bc),
                    pool_ca    = hex::encode(c.pool_ca),
                    "Search: simulation passed — submitting bundle"
                );

                if let Err(e) = submit_bundle(
                    &c,
                    self.treasury,
                    self.executor_addr,
                    &self.wallet,
                    &self.http_rpc,
                )
                .await
                {
                    error!(error = %e, "Search: bundle submission failed");
                }

                break; // one bundle per event to avoid nonce collisions
            }
        }

        Ok(())
    }
}

// ── Entry point ───────────────────────────────────────────────────────────────

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt()
        .json()
        .with_env_filter(
            tracing_subscriber::EnvFilter::from_default_env()
                .add_directive("arb_engine=debug".parse()?)
                .add_directive("warn".parse()?),
        )
        .init();

    let http_rpc = std::env::var("BASE_HTTP_RPC").context("BASE_HTTP_RPC not set")?;
    let ws_rpc = std::env::var("BASE_WS_RPC").context("BASE_WS_RPC not set")?;
    let pk = std::env::var("PRIVATE_KEY").context("PRIVATE_KEY not set")?;

    let executor_addr: H160 = std::env::var("EXECUTOR_ADDR")
        .context("EXECUTOR_ADDR not set")?
        .parse()
        .context("EXECUTOR_ADDR: invalid address")?;

    let treasury: H160 = std::env::var("TREASURY_ADDR")
        .context("TREASURY_ADDR not set")?
        .parse()
        .context("TREASURY_ADDR: invalid address")?;

    info!("Startup: all env vars loaded OK");
    info!(
        executor = ?executor_addr,
        treasury = ?treasury,
        chain_id = CHAIN_ID,
        "Startup: configuration"
    );

    let controller = Controller::new(http_rpc, ws_rpc, &pk, executor_addr, treasury)?;

    loop {
        match controller.run().await {
            Ok(()) => warn!("Controller exited cleanly — restarting"),
            Err(e) => error!(error = %e, "Controller crashed — restarting in 5s"),
        }
        sleep(Duration::from_secs(5)).await;
    }
}