// Uniswap v4 Triangular MEV Arbitrage Engine — Base mainnet (chain 8453)
//
// Flow:
//   Ingestion   → paginated subgraph query (id_gt cursor) → pool universe
//   Enrichment  → StateView RPC (sqrtPriceX96, liquidity, tick, protocol_fee)
//   Fast loop   → StateView refresh → graph update → Bellman-Ford → REVM → Flashbots
//   Slow loop   → periodic subgraph re-ingestion to pick up newly qualifying pools
//
// Required env vars:
//   BASE_HTTP_RPC, PRIVATE_KEY, EXECUTOR_ADDR, TREASURY_ADDR
//
// Optional env vars:
//   FAST_LOOP_MS   (default 400)   — StateView refresh cadence in milliseconds
//   SUBGRAPH_LOOP_S (default 120)  — pool universe refresh cadence in seconds

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
    time::Duration,
};

use anyhow::{anyhow, bail, Context, Result};
use ethers::{
    abi::{encode as abi_encode, Token},
    prelude::*,
    providers::{Http, Provider},
    signers::{LocalWallet, Signer},
    types::{
        transaction::eip2718::TypedTransaction, BlockId, BlockNumber, Bytes,
        Eip1559TransactionRequest, H160, H256, U256, U64,
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
use serde::Deserialize;
use tokio::{sync::RwLock, time::sleep};
use tracing::{debug, error, info, warn};
use url::Url;

// ── Constants ─────────────────────────────────────────────────────────────────

const POOL_MANAGER_ADDR: &str  = "0x498581ff718922c3f8e6a244956af099B2652b2b";
const STATE_VIEW_ADDR: &str    = "0xa3c0c9b65bad0b08107aa264b0f3db444b867a71";
const BALANCER_VAULT_ADDR: &str = "0xBA12222222228d8Ba445958a75a0704d566BF2C8";
const FLASHBOTS_RELAY_URL: &str = "https://relay.flashbots.net";
const CHAIN_ID: u64 = 8453;

const SUBGRAPH_URL: &str =
    "https://gateway.thegraph.com/api/25e2802b9b016903d316a56fb0e96db3/subgraphs/id/DiYPVdygkfjDWhbxGSqAQxwBKmfKnkWQojqeM2rkLb3G";

const SUBGRAPH_PAGE_SIZE: usize = 1_000;
const ENRICH_CONCURRENCY: usize = 40;
const GAS_LIMIT: u64 = 700_000;

// 50 000 USD expressed in the smallest sensible unit.
// Loan sizing uses raw liquidity units; we set a flat minimum of 50 000e6 (USDC-like decimals).
// For non-stable tokens the dynamic formula already picks a larger value in practice.
const LOAN_MIN: u128 = 50_000 * 1_000_000;        // 50 000 USDC-equivalent (6 dec)
const LOAN_MAX_WEI: u128 = 15_000_000_000_000_000_000; // 15 ETH-equivalent ceiling
const LOAN_LIQUIDITY_FRACTION: f64 = 0.003;

// ── Core types ────────────────────────────────────────────────────────────────

type PoolId = [u8; 32];

#[derive(Debug, Clone)]
struct Pool {
    pool_id:        PoolId,
    token0:         H160,
    token1:         H160,
    lp_fee:         u32,
    tick_spacing:   i32,
    // enriched from StateView
    sqrt_price_x96: U256,
    liquidity:      u128,
    tick:           i32,
    protocol_fee:   u32,
}

impl Pool {
    #[inline]
    fn swap_fee_ppm(&self) -> u64 {
        let p = self.protocol_fee as u64;
        let l = self.lp_fee as u64;
        p + l - (p * l) / 1_000_000
    }

    #[inline]
    fn fee_multiplier(&self) -> f64 {
        1.0 - (self.swap_fee_ppm() as f64) / 1_000_000.0
    }

    #[inline]
    fn rate_1_per_0(&self) -> f64 {
        let s = self.sqrt_price_x96.as_u128() as f64 / 2f64.powi(96);
        s * s * self.fee_multiplier()
    }

    #[inline]
    fn rate_0_per_1(&self) -> f64 {
        let denom = (self.sqrt_price_x96.as_u128() as f64 / 2f64.powi(96)).powi(2);
        if denom == 0.0 { return 0.0; }
        (1.0 / denom) * self.fee_multiplier()
    }
}

#[derive(Debug, Clone)]
struct Edge {
    pool_id:      PoolId,
    zero_for_one: bool,
    weight:       f64,
    rate:         f64,
}

#[derive(Debug, Clone)]
struct PoolKey {
    token0:       H160,
    token1:       H160,
    fee:          u32,
    tick_spacing: i32,
}

#[derive(Debug, Clone)]
struct Candidate {
    token_a:        H160,
    token_b:        H160,
    token_c:        H160,
    pool_ab:        PoolId,
    key_ab:         PoolKey,
    pool_bc:        PoolId,
    key_bc:         PoolKey,
    pool_ca:        PoolId,
    key_ca:         PoolKey,
    loan_amount:    U256,
    estimated_out:  U256,
    sim_passed:     bool,
    sim_net_profit: U256,
}

// ── Graph state ───────────────────────────────────────────────────────────────

struct EngineState {
    pools:               HashMap<PoolId, Pool>,
    meta_graph:          DiGraph<H160, Edge>,
    weight_graph:        DiGraph<H160, f64>,
    node_map:            HashMap<H160, NodeIndex>,
    balance_slot_cache:  HashMap<H160, u32>,
}

impl EngineState {
    fn new() -> Self {
        Self {
            pools:              HashMap::new(),
            meta_graph:         DiGraph::new(),
            weight_graph:       DiGraph::new(),
            node_map:           HashMap::new(),
            balance_slot_cache: HashMap::new(),
        }
    }

    fn get_or_add_node(&mut self, token: H160) -> NodeIndex {
        if let Some(&idx) = self.node_map.get(&token) { return idx; }
        let idx  = self.meta_graph.add_node(token);
        let idx2 = self.weight_graph.add_node(token);
        debug_assert_eq!(idx, idx2, "graph node index mismatch");
        self.node_map.insert(token, idx);
        idx
    }

    fn upsert_pool_edges(&mut self, pool: &Pool) {
        self.meta_graph.retain_edges(|g, e| g[e].pool_id != pool.pool_id);

        if pool.sqrt_price_x96.is_zero() || pool.liquidity == 0 {
            return;
        }

        let n0  = self.get_or_add_node(pool.token0);
        let n1  = self.get_or_add_node(pool.token1);
        let r10 = pool.rate_1_per_0();
        let r01 = pool.rate_0_per_1();

        if r10 > 0.0 {
            self.meta_graph.add_edge(n0, n1, Edge {
                pool_id:      pool.pool_id,
                zero_for_one: true,
                weight:       -r10.ln(),
                rate:         r10,
            });
        }
        if r01 > 0.0 {
            self.meta_graph.add_edge(n1, n0, Edge {
                pool_id:      pool.pool_id,
                zero_for_one: false,
                weight:       -r01.ln(),
                rate:         r01,
            });
        }

        self.sync_weight_graph();
    }

    fn drop_pool_edges(&mut self, pool_id: PoolId) {
        self.meta_graph.retain_edges(|g, e| g[e].pool_id != pool_id);
        self.sync_weight_graph();
    }

    fn sync_weight_graph(&mut self) {
        self.weight_graph.clear_edges();
        for e in self.meta_graph.edge_references() {
            self.weight_graph.add_edge(e.source(), e.target(), e.weight().weight);
        }
    }
}

// ── Subgraph types & ingestion ────────────────────────────────────────────────

#[derive(Debug, Deserialize)]
struct SubgraphToken {
    id:       String,
    decimals: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct SubgraphPool {
    id:          String,
    fee_tier:    String,
    tick_spacing: String,
    token0:      SubgraphToken,
    token1:      SubgraphToken,
}

#[derive(Debug, Deserialize)]
struct SubgraphData {
    pools: Vec<SubgraphPool>,
}

#[derive(Debug, Deserialize)]
struct SubgraphResponse {
    data: SubgraphData,
}

fn parse_h160(s: &str) -> Result<H160> {
    s.parse::<H160>().with_context(|| format!("invalid address: {s}"))
}

fn parse_pool_id(id_hex: &str) -> Result<PoolId> {
    let s = id_hex.trim_start_matches("0x");
    if s.len() != 64 {
        bail!("pool id wrong length: {id_hex}");
    }
    let mut out = [0u8; 32];
    hex::decode_to_slice(s, &mut out)?;
    Ok(out)
}

/// Single paginated fetch.  Returns the pools in this page.
async fn fetch_subgraph_page(
    client:  &reqwest::Client,
    last_id: &str,
) -> Result<Vec<SubgraphPool>> {
    let query = format!(
        r#"{{
          pools(
            first: {page_size}
            where: {{
              totalValueLockedUSD_gt: "50000"
              liquidity_gt: "0"
              hooks: "0x0000000000000000000000000000000000000000"
              id_gt: "{last_id}"
            }}
            orderBy: id
            orderDirection: asc
          ) {{
            id
            feeTier
            tickSpacing
            token0 {{ id decimals }}
            token1 {{ id decimals }}
          }}
        }}"#,
        page_size = SUBGRAPH_PAGE_SIZE,
    );

    let body = serde_json::json!({ "query": query });
    let resp = client
        .post(SUBGRAPH_URL)
        .json(&body)
        .send()
        .await
        .context("subgraph POST failed")?;

    let sg: SubgraphResponse = resp.json().await.context("subgraph JSON decode failed")?;
    Ok(sg.data.pools)
}

/// Full paginated ingest — returns all qualifying pools from the subgraph.
async fn ingest_subgraph(client: &reqwest::Client) -> Result<Vec<Pool>> {
    let mut all: Vec<Pool> = Vec::new();
    let mut last_id = String::new();

    loop {
        let page = fetch_subgraph_page(client, &last_id).await?;
        let page_len = page.len();

        for sp in &page {
            let pool_id  = match parse_pool_id(&sp.id)       { Ok(v) => v, Err(e) => { warn!(%e, "skip bad pool_id"); continue; } };
            let token0   = match parse_h160(&sp.token0.id)   { Ok(v) => v, Err(e) => { warn!(%e, "skip bad token0"); continue; } };
            let token1   = match parse_h160(&sp.token1.id)   { Ok(v) => v, Err(e) => { warn!(%e, "skip bad token1"); continue; } };
            let lp_fee: u32 = sp.fee_tier.parse().unwrap_or(0);
            let tick_spacing: i32 = sp.tick_spacing.parse().unwrap_or(0);

            all.push(Pool {
                pool_id,
                token0,
                token1,
                lp_fee,
                tick_spacing,
                sqrt_price_x96: U256::zero(),
                liquidity:      0,
                tick:           0,
                protocol_fee:   0,
            });
        }

        info!(page_pools = page_len, total_so_far = all.len(), "Subgraph: page ingested");

        if page_len < SUBGRAPH_PAGE_SIZE {
            break; // last page
        }
        // advance cursor to the last id seen
        if let Some(last) = page.last() {
            last_id = last.id.clone();
        }
    }

    info!(total = all.len(), "Subgraph: ingestion complete");
    Ok(all)
}

// ── StateView RPC calls ───────────────────────────────────────────────────────

async fn call_get_slot0(provider: &Provider<Http>, pool_id: PoolId) -> Result<(U256, i32, u32, u32)> {
    let mut cd = hex::decode("4c73e8ed")?;
    cd.extend_from_slice(&pool_id);
    let sv: H160 = STATE_VIEW_ADDR.parse()?;
    let raw = provider
        .call(&TransactionRequest::new().to(sv).data(cd).into(), None)
        .await
        .context("getSlot0 failed")?;

    if raw.len() < 128 { bail!("getSlot0: short ({} bytes)", raw.len()); }

    let sqrt_price = U256::from_big_endian(&raw[0..32]);

    // tick is int24 ABI-encoded as 256-bit two's-complement
    let tick_raw = U256::from_big_endian(&raw[32..64]).low_u32() as i32;
    let tick = (tick_raw << 8) >> 8;

    let protocol_fee = raw[63] as u32;
    let lp_fee       = raw[95] as u32;

    Ok((sqrt_price, tick, protocol_fee, lp_fee))
}

async fn call_get_liquidity(provider: &Provider<Http>, pool_id: PoolId) -> Result<u128> {
    let mut cd = hex::decode("4e33be86")?;
    cd.extend_from_slice(&pool_id);
    let sv: H160 = STATE_VIEW_ADDR.parse()?;
    let raw = provider
        .call(&TransactionRequest::new().to(sv).data(cd).into(), None)
        .await
        .context("getLiquidity failed")?;
    if raw.len() < 32 { bail!("getLiquidity: short ({} bytes)", raw.len()); }
    Ok(U256::from_big_endian(&raw[0..32]).as_u128())
}

async fn enrich_pool(provider: &Provider<Http>, pool: &mut Pool) -> Result<()> {
    let (slot0_res, liq_res) = tokio::join!(
        call_get_slot0(provider, pool.pool_id),
        call_get_liquidity(provider, pool.pool_id),
    );
    let (sqrt_price, tick, protocol_fee, lp_fee_on_chain) = slot0_res?;
    let liquidity = liq_res?;

    pool.sqrt_price_x96 = sqrt_price;
    pool.tick           = tick;
    pool.protocol_fee   = protocol_fee;
    // prefer on-chain lp_fee if non-zero (subgraph is source of truth only for schema fields)
    if lp_fee_on_chain > 0 { pool.lp_fee = lp_fee_on_chain; }
    pool.liquidity      = liquidity;
    Ok(())
}

// ── Bellman-Ford cycle detection ──────────────────────────────────────────────

fn find_triangular_cycles(state: &EngineState) -> Vec<[NodeIndex; 3]> {
    let mut seen: HashSet<[u32; 3]> = HashSet::new();
    let mut out  = Vec::new();

    for start in state.weight_graph.node_indices() {
        if state.weight_graph.edges(start).next().is_none() { continue; }
        if let Some(cycle) = find_negative_cycle(&state.weight_graph, start) {
            if cycle.len() != 3 { continue; }
            let mut key = [
                cycle[0].index() as u32,
                cycle[1].index() as u32,
                cycle[2].index() as u32,
            ];
            key.sort_unstable();
            if seen.insert(key) {
                out.push([cycle[0], cycle[1], cycle[2]]);
            }
        }
    }
    out
}

// ── Loan sizing ───────────────────────────────────────────────────────────────

fn dynamic_loan_size(pool_liquidities: [u128; 3]) -> U256 {
    let min_liq = pool_liquidities.iter().copied().min().unwrap_or(0);
    let raw  = (min_liq as f64 * LOAN_LIQUIDITY_FRACTION) as u128;
    let loan = raw.max(LOAN_MIN).min(LOAN_MAX_WEI);
    U256::from(loan)
}

// ── Candidate construction ────────────────────────────────────────────────────

fn build_candidate(
    cycle:         &[NodeIndex; 3],
    state:         &EngineState,
    gas_price_wei: U256,
) -> Option<Candidate> {
    let mut tokens      = [H160::zero(); 3];
    let mut pool_ids    = [[0u8; 32]; 3];
    let mut rates       = [0f64; 3];
    let mut liquidities = [0u128; 3];
    let mut keys: Vec<PoolKey> = Vec::with_capacity(3);

    for i in 0..3 {
        let from = cycle[i];
        let to   = cycle[(i + 1) % 3];
        tokens[i] = *state.meta_graph.node_weight(from)?;
        let edge  = state.meta_graph.edges_connecting(from, to).next()?.weight();
        pool_ids[i] = edge.pool_id;
        rates[i]    = edge.rate;
        let pool = state.pools.get(&edge.pool_id)?;
        liquidities[i] = pool.liquidity;
        keys.push(PoolKey {
            token0:       pool.token0,
            token1:       pool.token1,
            fee:          pool.lp_fee,
            tick_spacing: pool.tick_spacing,
        });
    }

    let loan       = dynamic_loan_size(liquidities);
    let cumulative = rates[0] * rates[1] * rates[2];
    if cumulative <= 1.0 { return None; }

    let est_out  = U256::from((loan.as_u128() as f64 * cumulative) as u128);
    let gas_cost = gas_price_wei * U256::from(GAS_LIMIT);
    if est_out <= loan + gas_cost { return None; }

    Some(Candidate {
        token_a:        tokens[0],
        token_b:        tokens[1],
        token_c:        tokens[2],
        pool_ab:        pool_ids[0],
        key_ab:         keys[0].clone(),
        pool_bc:        pool_ids[1],
        key_bc:         keys[1].clone(),
        pool_ca:        pool_ids[2],
        key_ca:         keys[2].clone(),
        loan_amount:    loan,
        estimated_out:  est_out,
        sim_passed:     false,
        sim_net_profit: U256::zero(),
    })
}

// ── ERC-20 balance slot discovery ─────────────────────────────────────────────

async fn find_balance_slot(provider: &Provider<Http>, token: H160) -> u32 {
    let probe = H160::from_low_u64_be(1);
    let mut cd = hex::decode("70a08231").unwrap();
    cd.extend_from_slice(&[0u8; 12]);
    cd.extend_from_slice(probe.as_bytes());
    let real_bal = provider
        .call(&TransactionRequest::new().to(token).data(cd).into(), None)
        .await
        .ok()
        .and_then(|r| if r.len() >= 32 { Some(U256::from_big_endian(&r[0..32])) } else { None })
        .unwrap_or_default();

    for slot in 0u32..30 {
        let key_h256 = H256::from(keccak256({
            let mut b = [0u8; 64];
            b[12..32].copy_from_slice(probe.as_bytes());
            b[60..64].copy_from_slice(&slot.to_be_bytes());
            b
        }));
        let stored = provider.get_storage_at(token, key_h256, None).await.unwrap_or(H256::zero());
        let stored_u256 = U256::from_big_endian(stored.as_bytes());
        if stored_u256 == real_bal && !real_bal.is_zero() {
            return slot;
        }
    }
    warn!(token = ?token, "balance slot not found in 0-29, defaulting to 0");
    0
}

fn mapping_slot_key(account: H160, mapping_slot: u32) -> rU256 {
    let mut preimage = [0u8; 64];
    preimage[12..32].copy_from_slice(account.as_bytes());
    preimage[60..64].copy_from_slice(&mapping_slot.to_be_bytes());
    rU256::from_be_bytes(revm_keccak256(&preimage).0)
}

// ── REVM simulation ───────────────────────────────────────────────────────────

fn build_calldata(c: &Candidate, treasury: H160) -> Bytes {
    let sig      = "execute(address,uint256,(address,address,address,address,uint24,int24,address,uint256,uint256)[3],address)";
    let selector = &keccak256(sig.as_bytes())[0..4];

    let make_step = |tin: H160, tout: H160, key: &PoolKey, amount_in: U256| -> Token {
        Token::Tuple(vec![
            Token::Address(tin),
            Token::Address(tout),
            Token::Address(key.token0),
            Token::Address(key.token1),
            Token::Uint(U256::from(key.fee)),
            Token::Int(U256::from(key.tick_spacing.unsigned_abs())),
            Token::Address(H160::zero()), // hooks == 0x0 guaranteed by subgraph filter
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
    c:             &Candidate,
    http_rpc:      &str,
    block_number:  u64,
    executor_addr: H160,
    treasury:      H160,
    gas_price_wei: U256,
    balance_slot:  u32,
) -> Result<(bool, U256)> {
    let provider = Arc::new(Provider::<Http>::try_from(http_rpc).context("REVM http provider")?);
    let block_id = Some(BlockId::Number(BlockNumber::Number(U64::from(block_number))));

    let mut ethers_db = EthersDB::new(Arc::clone(&provider), block_id)
        .ok_or_else(|| anyhow!("EthersDB::new returned None"))?;

    let token_a_b160: B160  = B160::from(c.token_a.0);
    let executor_b160: B160 = B160::from(executor_addr.0);
    let vault_b160: B160    = B160::from(BALANCER_VAULT_ADDR.parse::<H160>()?.0);
    let treasury_b160: B160 = B160::from(treasury.0);
    let pm_b160: B160       = B160::from(POOL_MANAGER_ADDR.parse::<H160>()?.0);

    let mut cache_db = CacheDB::new(EmptyDB::default());
    for addr in [token_a_b160, vault_b160, executor_b160, treasury_b160, pm_b160] {
        if let Ok(Some(info)) = ethers_db.basic(addr) {
            cache_db.insert_account_info(addr, info);
        }
    }

    let vault_balance_slot = mapping_slot_key(BALANCER_VAULT_ADDR.parse::<H160>()?, balance_slot);
    let treasury_slot      = mapping_slot_key(treasury, balance_slot);

    let bal_before: rU256 = ethers_db.storage(token_a_b160, treasury_slot).unwrap_or(rU256::ZERO);

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

    let mut evm = EVM::new();
    evm.database(cache_db);
    evm.env.block.number    = rU256::from(block_number + 1);
    evm.env.block.gas_limit = rU256::from(30_000_000u64);
    evm.env.tx.caller       = executor_b160;
    evm.env.tx.transact_to  = TransactTo::Call(executor_b160);
    evm.env.tx.data         = calldata.0.to_vec().into();
    evm.env.tx.value        = rU256::ZERO;
    evm.env.tx.gas_limit    = GAS_LIMIT;
    evm.env.tx.gas_price    = rU256::from(gas_price_wei.as_u128());

    let result = evm.transact_commit().map_err(|e| anyhow!("REVM: {:?}", e))?;

    let gas_used: u64 = match result {
        ExecutionResult::Success { gas_used, .. } => gas_used,
        _ => return Ok((false, U256::zero())),
    };

    let bal_after: rU256 = evm
        .db
        .as_ref()
        .and_then(|db| db.accounts.get(&token_a_b160))
        .and_then(|acc| acc.storage.get(&treasury_slot))
        .copied()
        .unwrap_or(bal_before);

    if bal_after <= bal_before { return Ok((false, U256::zero())); }

    let diff  = bal_after - bal_before;
    let limbs = diff.as_limbs();
    let gross = U256::from(limbs[0] as u128 | ((limbs[1] as u128) << 64));
    let gas_cost = gas_price_wei * U256::from(gas_used);
    if gross <= gas_cost { return Ok((false, U256::zero())); }

    Ok((true, gross - gas_cost))
}

// ── Flashbots submission ──────────────────────────────────────────────────────

async fn submit_bundle(
    c:             &Candidate,
    treasury:      H160,
    executor_addr: H160,
    wallet:        &LocalWallet,
    http_rpc:      &str,
) -> Result<()> {
    let provider    = Provider::<Http>::try_from(http_rpc).context("bundle http provider")?;
    let chain_id    = provider.get_chainid().await?.as_u64();
    let fb_mw       = FlashbotsMiddleware::new(
        provider.clone(),
        Url::parse(FLASHBOTS_RELAY_URL).context("invalid relay URL")?,
        wallet.clone().with_chain_id(chain_id),
    );
    let current_block = provider.get_block_number().await?;
    let target_block  = current_block.as_u64() + 1;
    let base_fee      = provider
        .get_block(BlockNumber::Latest)
        .await?
        .and_then(|b| b.base_fee_per_gas)
        .unwrap_or(U256::from(1_000_000_000u64));
    let priority_fee  = U256::from(2_000_000_000u64);
    let max_fee       = base_fee * 2 + priority_fee;
    let nonce         = provider.get_transaction_count(wallet.address(), None).await?;

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

    let sig          = wallet.sign_transaction(&tx).await.context("tx signing failed")?;
    let signed_bytes = Bytes::from(tx.rlp_signed(&sig).to_vec());

    let bundle = BundleRequest::new()
        .push_transaction(signed_bytes)
        .set_block(U64::from(target_block))
        .set_simulation_block(current_block);

    let pending = fb_mw.send_bundle(&bundle).await.context("send_bundle failed")?;
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
    http_rpc:      String,
    wallet:        LocalWallet,
    executor_addr: H160,
    treasury:      H160,
    state:         Arc<RwLock<EngineState>>,
    sg_client:     reqwest::Client,
}

impl Controller {
    fn new(
        http_rpc:      String,
        private_key:   &str,
        executor_addr: H160,
        treasury:      H160,
    ) -> Result<Self> {
        let wallet = private_key
            .parse::<LocalWallet>()
            .context("invalid PRIVATE_KEY")?
            .with_chain_id(CHAIN_ID);
        Ok(Self {
            http_rpc,
            wallet,
            executor_addr,
            treasury,
            state:     Arc::new(RwLock::new(EngineState::new())),
            sg_client: reqwest::Client::builder()
                .timeout(Duration::from_secs(30))
                .build()?,
        })
    }

    async fn run(&self) -> Result<()> {
        info!("Engine starting — Base chain {}", CHAIN_ID);

        let fast_ms = std::env::var("FAST_LOOP_MS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(400u64);
        let sg_secs = std::env::var("SUBGRAPH_LOOP_S")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(120u64);

        // initial ingest + enrich
        self.refresh_pool_universe().await.context("initial pool ingest failed")?;

        let state_clone      = Arc::clone(&self.state);
        let http_clone       = self.http_rpc.clone();
        let executor_clone   = self.executor_addr;
        let treasury_clone   = self.treasury;
        let wallet_clone     = self.wallet.clone();

        // ── Fast loop: StateView refresh → graph → BF → REVM → Flashbots
        let fast_handle = {
            let state    = Arc::clone(&state_clone);
            let http     = http_clone.clone();
            let executor = executor_clone;
            let treasury = treasury_clone;
            let wallet   = wallet_clone.clone();
            tokio::spawn(async move {
                loop {
                    if let Err(e) =
                        Self::fast_loop_tick(&state, &http, executor, treasury, &wallet).await
                    {
                        warn!(error = %e, "Fast loop tick error");
                    }
                    sleep(Duration::from_millis(fast_ms)).await;
                }
            })
        };

        // ── Slow loop: subgraph re-ingest
        let sg_client_clone = self.sg_client.clone();
        let slow_handle = {
            let state  = Arc::clone(&state_clone);
            let http   = http_clone.clone();
            let client = sg_client_clone;
            tokio::spawn(async move {
                loop {
                    sleep(Duration::from_secs(sg_secs)).await;
                    info!("Slow loop: re-ingesting subgraph");
                    if let Err(e) =
                        Self::ingest_and_enrich(&state, &http, &client).await
                    {
                        warn!(error = %e, "Slow loop ingest error");
                    }
                }
            })
        };

        tokio::select! {
            _ = fast_handle => bail!("fast loop exited"),
            _ = slow_handle => bail!("slow loop exited"),
        }
    }

    // ── Shared ingest + enrich helper ─────────────────────────────────────────

    async fn refresh_pool_universe(&self) -> Result<()> {
        Self::ingest_and_enrich(&self.state, &self.http_rpc, &self.sg_client).await
    }

    async fn ingest_and_enrich(
        state:    &Arc<RwLock<EngineState>>,
        http_rpc: &str,
        client:   &reqwest::Client,
    ) -> Result<()> {
        let mut pools = ingest_subgraph(client).await?;
        let total     = pools.len();
        let provider  = Arc::new(Provider::<Http>::try_from(http_rpc)?);

        let mut loaded  = 0usize;
        let mut skipped = 0usize;

        for chunk in pools.chunks_mut(ENRICH_CONCURRENCY) {
            let futs: Vec<_> = chunk.iter_mut().map(|p| enrich_pool(&provider, p)).collect();
            let results = join_all(futs).await;

            let mut s = state.write().await;
            for (pool, res) in chunk.iter().zip(results) {
                match res {
                    Ok(()) => {
                        s.upsert_pool_edges(pool);
                        s.pools.insert(pool.pool_id, pool.clone());
                        loaded += 1;
                    }
                    Err(e) => {
                        debug!(pool_id = hex::encode(pool.pool_id), error = %e, "enrich failed");
                        skipped += 1;
                    }
                }
            }
        }

        info!(loaded, skipped, total, "Pool universe refreshed");
        Ok(())
    }

    // ── Fast-loop tick: refresh all tracked pools, then search ────────────────

    async fn fast_loop_tick(
        state:         &Arc<RwLock<EngineState>>,
        http_rpc:      &str,
        executor_addr: H160,
        treasury:      H160,
        wallet:        &LocalWallet,
    ) -> Result<()> {
        let provider = Provider::<Http>::try_from(http_rpc)?;

        // Collect pool_ids to refresh (avoid holding write lock across async calls)
        let pool_ids: Vec<PoolId> = state.read().await.pools.keys().copied().collect();

        // Enrich in parallel batches
        for chunk in pool_ids.chunks(ENRICH_CONCURRENCY) {
            let mut pools: Vec<Pool> = {
                let s = state.read().await;
                chunk.iter().filter_map(|id| s.pools.get(id).cloned()).collect()
            };

            let futs: Vec<_> = pools.iter_mut().map(|p| enrich_pool(&provider, p)).collect();
            let results = join_all(futs).await;

            let mut s = state.write().await;
            for (pool, res) in pools.iter().zip(results) {
                match res {
                    Ok(()) => {
                        s.upsert_pool_edges(pool);
                        s.pools.insert(pool.pool_id, pool.clone());
                    }
                    Err(_) => {
                        s.drop_pool_edges(pool.pool_id);
                    }
                }
            }
        }

        let (block_res, gas_res) =
            tokio::join!(provider.get_block_number(), provider.get_gas_price());
        let block_number = block_res?.as_u64();
        let gas_price    = gas_res.unwrap_or(U256::from(1_000_000_000u64));

        let cycles: Vec<[NodeIndex; 3]> = {
            let s = state.read().await;
            find_triangular_cycles(&s)
        };

        if cycles.is_empty() { return Ok(()); }

        let mut candidates: Vec<Candidate> = {
            let s = state.read().await;
            cycles.iter().filter_map(|c| build_candidate(c, &s, gas_price)).collect()
        };

        if candidates.is_empty() { return Ok(()); }
        candidates.sort_by(|a, b| b.estimated_out.cmp(&a.estimated_out));

        for mut c in candidates {
            let balance_slot = {
                let cached = state.read().await.balance_slot_cache.get(&c.token_a).copied();
                match cached {
                    Some(s) => s,
                    None => {
                        let s = find_balance_slot(&provider, c.token_a).await;
                        state.write().await.balance_slot_cache.insert(c.token_a, s);
                        s
                    }
                }
            };

            let (passed, net_profit) = simulate(
                &c, http_rpc, block_number, executor_addr, treasury, gas_price, balance_slot,
            )
            .await
            .unwrap_or((false, U256::zero()));

            if passed {
                c.sim_passed     = true;
                c.sim_net_profit = net_profit;
                info!(
                    token_a    = ?c.token_a,
                    token_b    = ?c.token_b,
                    token_c    = ?c.token_c,
                    net_profit = ?net_profit,
                    pool_ab    = hex::encode(c.pool_ab),
                    pool_bc    = hex::encode(c.pool_bc),
                    pool_ca    = hex::encode(c.pool_ca),
                    "Simulation passed — submitting bundle"
                );
                if let Err(e) = submit_bundle(&c, treasury, executor_addr, wallet, http_rpc).await {
                    error!(error = %e, "Bundle submission failed");
                }
                break; // one bundle per tick
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
    let pk       = std::env::var("PRIVATE_KEY").context("PRIVATE_KEY not set")?;

    let executor_addr: H160 = std::env::var("EXECUTOR_ADDR")
        .context("EXECUTOR_ADDR not set")?
        .parse()
        .context("EXECUTOR_ADDR: invalid")?;

    let treasury: H160 = std::env::var("TREASURY_ADDR")
        .context("TREASURY_ADDR not set")?
        .parse()
        .context("TREASURY_ADDR: invalid")?;

    info!(executor = ?executor_addr, treasury = ?treasury, chain_id = CHAIN_ID, "Startup");

    let controller = Controller::new(http_rpc, &pk, executor_addr, treasury)?;

    loop {
        match controller.run().await {
            Ok(()) => warn!("Controller exited cleanly — restarting"),
            Err(e) => error!(error = %e, "Controller crashed — restarting in 5s"),
        }
        sleep(Duration::from_secs(5)).await;
    }
}