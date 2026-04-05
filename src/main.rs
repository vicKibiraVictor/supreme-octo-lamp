// main.rs — Uniswap v4 Triangular MEV Arbitrage Engine (Base, chain 8453)
//
// What this does, step by step:
//
//   1. Reads all past PoolManager Initialize events to learn about every pool.
//   2. Calls StateView to get the live price, fees, and liquidity for each pool.
//   3. Builds a weighted directed graph: tokens are nodes, swaps are edges.
//      Edge weight = -ln(rate after fees). A negative cycle means profit.
//      The metadata graph (DiGraph<H160, Edge>) stores pool ids, directions, and
//      rates. A parallel weight graph (DiGraph<H160, f64>) stores only the f64
//      weights needed by petgraph's Bellman-Ford. Both share the same NodeIndex
//      values because nodes are added to both in lockstep.
//   4. Uses petgraph's Bellman-Ford to find triangular negative cycles.
//   5. For every candidate, runs a full REVM simulation against a live fork:
//      - Discovers the ERC-20 storage slot for the loan token.
//      - Patches the Balancer Vault's balance so the flash loan can proceed.
//      - Executes the full execute() call and measures treasury profit.
//   6. If REVM says it profits after gas, signs the transaction and sends a
//      Flashbots bundle targeting the next block.
//   7. Subscribes to Swap and ModifyLiquidity events and refreshes only the
//      pools that changed — no full rebuild on every block.
//
// Liquidity filter:
//   Pools with less than MIN_LIQUIDITY_RAW active liquidity units are excluded
//   at graph-build time. This removes trash pools before they ever enter the
//   Bellman-Ford search.
//
// Required environment variables:
//   BASE_HTTP_RPC   — HTTP RPC for Base (Alchemy/Infura/etc.)
//   BASE_WS_RPC     — WebSocket RPC for Base
//   PRIVATE_KEY     — 0x-prefixed hex private key of the searcher wallet
//   EXECUTOR_ADDR   — address of the deployed TriArbExecutor contract
//   TREASURY_ADDR   — address where profit lands

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
        transaction::eip2718::TypedTransaction, BlockId, BlockNumber,
        Bytes, Eip1559TransactionRequest, Filter, H160, H256, U256, U64,
    },
    utils::keccak256,
};
use ethers_flashbots::{BundleRequest, FlashbotsMiddleware};
use futures::future::join_all;
use petgraph::{
    algo::find_negative_cycle,
    graph::{DiGraph, NodeIndex},
    // FIX E0599: EdgeRef must be in scope for .source() and .target() to work
    // on EdgeReference. These methods are defined on the EdgeRef trait.
    visit::EdgeRef,
};
use revm::{
    db::{CacheDB, EmptyDB, EthersDB},
    primitives::{
        keccak256 as revm_keccak256, AccountInfo, ExecutionResult, TransactTo,
        B256, U256 as rU256,
    },
    // FIX E0432: revm 3.5.0 exports the EVM struct as revm::EVM (uppercase),
    // not revm::Evm. The builder pattern (Evm::builder()) is only available in
    // revm >= 5.0. We use the 3.5.0 API: EVM::new() + evm.database().
    Database, EVM,
};
use tokio::{sync::RwLock, time::sleep};
use tracing::{debug, error, info, warn};
use url::Url;

// ── Chain addresses (Base mainnet) ──────────────────────────────────────────

const POOL_MANAGER_ADDR: &str   = "0x498581ff718922c3f8e6a244956af099B2652b2b";
const STATE_VIEW_ADDR: &str     = "0xa3c0c9b65bad0b08107aa264b0f3db444b867a71";
const BALANCER_VAULT_ADDR: &str = "0xBA12222222228d8Ba445958a75a0704d566BF2C8";
const FLASHBOTS_RELAY_URL: &str = "https://relay.flashbots.net";
const CHAIN_ID: u64             = 8453;

// Block where Uniswap v4 was deployed on Base (update if needed).
const V4_DEPLOY_BLOCK: u64 = 23_145_980;

// Pages for getLogs so we never hit RPC limits.
const LOG_PAGE_SIZE: u64 = 2_000;

// Minimum flash loan amount — 1 WETH.
const LOAN_MIN_WEI: u128 = 1_000_000_000_000_000_000;

// Maximum flash loan amount — 15 WETH.
const LOAN_MAX_WEI: u128 = 15_000_000_000_000_000_000;

// Fraction of the weakest pool's raw liquidity to use as the loan size.
const LOAN_LIQUIDITY_FRACTION: f64 = 0.003;

// Gas limit given to the executor transaction.
const GAS_LIMIT: u64 = 700_000;

// Minimum raw active liquidity a pool must have to enter the graph.
const MIN_LIQUIDITY_RAW: u128 = 50_000_000_000;

// How many pools to enrich concurrently during bootstrap.
const BOOTSTRAP_CONCURRENCY: usize = 20;

// ── Event topics ─────────────────────────────────────────────────────────────

const TOPIC_INITIALIZE: &str =
    "0x5e74bdc2af0cd2d4e2f1e2b876960b3f5fcc4b72fb01f10e16c5869b11a5b7b5";
const TOPIC_SWAP: &str =
    "0x19b47279256b2a23a1665c810c8d55a1758940ee09377d4f8d26497a3577dc83";
const TOPIC_MODIFY_LIQ: &str =
    "0x0e3a47c5b5a1671f18e5e2ce51e77c9e5d44bf9bc57ceb33e17f8adab54e5fe5";

// ── Core types ────────────────────────────────────────────────────────────────

type PoolId = [u8; 32];

/// One swap direction on a pool. Stored in the metadata graph.
#[derive(Debug, Clone)]
struct Edge {
    pool_id: PoolId,
    zero_for_one: bool,
    /// Bellman-Ford weight: -ln(net_rate).
    weight: f64,
    /// Net rate (amount out / amount in after fees).
    rate: f64,
}

/// Everything known about one v4 pool.
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
    /// Combined swap fee in parts-per-million.
    fn swap_fee_ppm(&self) -> u64 {
        let p = self.protocol_fee as u64;
        let l = self.lp_fee as u64;
        p + l - (p * l) / 1_000_000
    }

    fn fee_multiplier(&self) -> f64 {
        1.0 - (self.swap_fee_ppm() as f64) / 1_000_000.0
    }

    /// token1 per token0 (spot, after fees).
    fn rate_1_per_0(&self) -> f64 {
        let s = self.sqrt_price_x96.as_u128() as f64 / 2f64.powi(96);
        s * s * self.fee_multiplier()
    }

    /// token0 per token1 (spot, after fees).
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

/// Fields from a PoolKey needed by the Solidity executor.
#[derive(Debug, Clone)]
struct PoolKey {
    token0: H160,
    token1: H160,
    fee: u32,
    tick_spacing: i32,
    hook: H160,
}

/// One triangular arbitrage opportunity.
#[derive(Debug, Clone)]
struct Candidate {
    token_a: H160,
    token_b: H160,
    token_c: H160,
    pool_ab: PoolId,  key_ab: PoolKey,  dir_ab: bool,
    pool_bc: PoolId,  key_bc: PoolKey,  dir_bc: bool,
    pool_ca: PoolId,  key_ca: PoolKey,  dir_ca: bool,
    loan_amount: U256,
    estimated_out: U256,
    sim_passed: bool,
    sim_net_profit: U256,
}

// ── Graph state ───────────────────────────────────────────────────────────────
//
// Two parallel directed graphs share the same node indices:
//
//   meta_graph   — DiGraph<H160, Edge>
//                  Full edge metadata: pool_id, direction, rate, weight.
//                  Used when building Candidate structs.
//
//   weight_graph — DiGraph<H160, f64>
//                  Only the bare f64 Bellman-Ford weight for each edge.
//                  petgraph::algo::find_negative_cycle requires EdgeWeight:
//                  FloatMeasure, which f64 satisfies but Edge does not.
//
// Invariant: every add_edge / retain_edges call is mirrored on both graphs
// so that NodeIndex values always correspond across both.

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

    /// Return the existing NodeIndex for `token`, or add a new node to both
    /// graphs and return its index.
    fn get_or_add_node(&mut self, token: H160) -> NodeIndex {
        if let Some(&idx) = self.node_map.get(&token) {
            return idx;
        }
        let idx  = self.meta_graph.add_node(token);
        let idx2 = self.weight_graph.add_node(token);
        debug_assert_eq!(idx, idx2, "graph node index mismatch");
        self.node_map.insert(token, idx);
        idx
    }

    /// Replace both edges for a pool with fresh data.
    fn upsert_pool_edges(&mut self, pool: &Pool) {
        // Remove stale edges from meta_graph; weight_graph is rebuilt below.
        self.meta_graph.retain_edges(|g, e| g[e].pool_id != pool.pool_id);

        // Gate 1: no unknown hooks.
        if !pool.hook_accepted() { return; }
        // Gate 2: pool must have a live price and non-zero liquidity.
        if pool.sqrt_price_x96.is_zero() || pool.liquidity == 0 { return; }
        // Gate 3: liquidity floor.
        if !pool.liquidity_ok() {
            debug!(
                pool_id = hex::encode(pool.pool_id),
                liq     = pool.liquidity,
                min     = MIN_LIQUIDITY_RAW,
                "Pool excluded: below liquidity threshold"
            );
            return;
        }

        let n0 = self.get_or_add_node(pool.token0);
        let n1 = self.get_or_add_node(pool.token1);

        let r10 = pool.rate_1_per_0();
        let r01 = pool.rate_0_per_1();

        if r10 > 0.0 {
            let w = -r10.ln();
            self.meta_graph.add_edge(n0, n1, Edge {
                pool_id: pool.pool_id,
                zero_for_one: true,
                weight: w,
                rate: r10,
            });
        }
        if r01 > 0.0 {
            let w = -r01.ln();
            self.meta_graph.add_edge(n1, n0, Edge {
                pool_id: pool.pool_id,
                zero_for_one: false,
                weight: w,
                rate: r01,
            });
        }

        // Keep weight_graph in sync with meta_graph.
        self.sync_weight_graph();
    }

    fn drop_pool_edges(&mut self, pool_id: PoolId) {
        self.meta_graph.retain_edges(|g, e| g[e].pool_id != pool_id);
        self.sync_weight_graph();
    }

    /// Rebuild weight_graph from scratch to match meta_graph exactly.
    /// Called after every structural change to meta_graph.
    fn sync_weight_graph(&mut self) {
        self.weight_graph.clear_edges();

        // FIX E0599 for .source()/.target(): the EdgeRef trait is now imported
        // at the top of the file, so these methods are in scope.
        for edge_ref in self.meta_graph.edge_references() {
            let src = edge_ref.source();
            let dst = edge_ref.target();
            let w   = edge_ref.weight().weight;
            self.weight_graph.add_edge(src, dst, w);
        }
    }
}

// ── StateView calls ───────────────────────────────────────────────────────────

async fn call_get_slot0(
    provider: &Provider<Http>,
    pool_id: PoolId,
) -> Result<(U256, i32, u8, u8)> {
    let mut cd = hex::decode("4c73e8ed")?;
    cd.extend_from_slice(&pool_id);

    let sv: H160 = STATE_VIEW_ADDR.parse()?;
    let raw = provider
        .call(&TransactionRequest::new().to(sv).data(cd).into(), None)
        .await
        .context("getSlot0 failed")?;

    if raw.len() < 128 { bail!("getSlot0: short response"); }

    let sqrt_price = U256::from_big_endian(&raw[0..32]);

    let tick_raw = U256::from_big_endian(&raw[32..64]).as_u64() as i64;
    let tick = if tick_raw & (1 << 23) != 0 {
        (tick_raw | !((1i64 << 24) - 1)) as i32
    } else {
        tick_raw as i32
    };

    let protocol_fee = raw[63];
    let lp_fee       = raw[95];

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

    if raw.len() < 32 { bail!("getLiquidity: short response"); }
    Ok(U256::from_big_endian(&raw[0..32]).as_u128())
}

/// Fill in the live fields of a pool from StateView.
async fn enrich_pool(provider: &Provider<Http>, pool: &mut Pool) -> Result<()> {
    let (slot0_result, liquidity_result) = tokio::join!(
        call_get_slot0(provider, pool.pool_id),
        call_get_liquidity(provider, pool.pool_id),
    );

    let (sqrt_price, tick, protocol_fee, lp_fee) = slot0_result?;
    let liquidity = liquidity_result?;

    pool.sqrt_price_x96 = sqrt_price;
    pool.tick           = tick;
    pool.protocol_fee   = protocol_fee as u32;
    pool.lp_fee         = lp_fee as u32;
    pool.liquidity      = liquidity;
    Ok(())
}

// ── Pool discovery ────────────────────────────────────────────────────────────

fn parse_initialize_log(log: &ethers::types::Log) -> Option<Pool> {
    if log.topics.len() < 4 { return None; }

    let pool_id: PoolId = log.topics[1].into();
    let token0 = H160::from(log.topics[2]);
    let token1 = H160::from(log.topics[3]);

    let data = log.data.as_ref();
    if data.len() < 160 { return None; }

    let fee          = U256::from_big_endian(&data[0..32]).as_u32();
    let tick_spacing = U256::from_big_endian(&data[32..64]).as_u32() as i32;
    let hook         = H160::from_slice(&data[76..96]);
    let sqrt_price   = U256::from_big_endian(&data[96..128]);
    let tick         = U256::from_big_endian(&data[128..160]).as_u32() as i32;

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
    let pm: H160    = POOL_MANAGER_ADDR.parse()?;
    let topic: H256 = TOPIC_INITIALIZE.parse()?;
    let latest      = provider.get_block_number().await?.as_u64();

    let mut pools = Vec::new();
    let mut from  = V4_DEPLOY_BLOCK;

    while from <= latest {
        let to     = (from + LOG_PAGE_SIZE - 1).min(latest);
        let filter = Filter::new().address(pm).topic0(topic).from_block(from).to_block(to);
        let logs   = provider.get_logs(&filter).await.unwrap_or_default();

        for log in &logs {
            if let Some(pool) = parse_initialize_log(log) {
                pools.push(pool);
            }
        }

        from = to + 1;
        sleep(Duration::from_millis(30)).await;
    }

    Ok(pools)
}

// ── Bellman-Ford — triangular arbitrage detection ─────────────────────────────

fn find_triangular_cycles(state: &EngineState) -> Vec<[NodeIndex; 3]> {
    let mut seen: HashSet<[u32; 3]> = HashSet::new();
    let mut out  = Vec::new();

    for start in state.weight_graph.node_indices() {
        if state.weight_graph.edges(start).next().is_none() {
            continue;
        }

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

/// Dynamic loan sizing: 0.3% of the shallowest pool's liquidity,
/// clamped to [1 WETH, 15 WETH].
fn dynamic_loan_size(pool_liquidities: [u128; 3]) -> U256 {
    let min_liq = pool_liquidities.iter().copied().min().unwrap_or(0);
    let raw     = (min_liq as f64 * LOAN_LIQUIDITY_FRACTION) as u128;
    let clamped = raw.max(LOAN_MIN_WEI).min(LOAN_MAX_WEI);
    U256::from(clamped)
}

/// Turn a 3-node cycle into a Candidate using meta_graph.
fn build_candidate(
    cycle: &[NodeIndex; 3],
    state: &EngineState,
    gas_price_wei: U256,
) -> Option<Candidate> {
    let mut tokens      = [H160::zero(); 3];
    let mut pool_ids    = [[0u8; 32]; 3];
    let mut dirs        = [false; 3];
    let mut rates       = [0f64; 3];
    let mut liquidities = [0u128; 3];
    let mut keys: Vec<PoolKey> = Vec::new();

    for i in 0..3 {
        let from = cycle[i];
        let to   = cycle[(i + 1) % 3];

        tokens[i] = *state.meta_graph.node_weight(from)?;

        let edge = state.meta_graph.edges_connecting(from, to).next()?.weight();
        pool_ids[i]    = edge.pool_id;
        dirs[i]        = edge.zero_for_one;
        rates[i]       = edge.rate;

        let pool = state.pools.get(&edge.pool_id)?;
        liquidities[i] = pool.liquidity;
        keys.push(PoolKey {
            token0:       pool.token0,
            token1:       pool.token1,
            fee:          pool.lp_fee,
            tick_spacing: pool.tick_spacing,
            hook:         pool.hook,
        });
    }

    let loan = dynamic_loan_size(liquidities);

    let cumulative = rates[0] * rates[1] * rates[2];
    if cumulative <= 1.0 { return None; }

    let est_out = U256::from((loan.as_u128() as f64 * cumulative) as u128);

    let gas_cost = gas_price_wei * U256::from(GAS_LIMIT);
    if est_out <= loan + gas_cost { return None; }

    Some(Candidate {
        token_a: tokens[0], token_b: tokens[1], token_c: tokens[2],
        pool_ab: pool_ids[0], key_ab: keys[0].clone(), dir_ab: dirs[0],
        pool_bc: pool_ids[1], key_bc: keys[1].clone(), dir_bc: dirs[1],
        pool_ca: pool_ids[2], key_ca: keys[2].clone(), dir_ca: dirs[2],
        loan_amount:    loan,
        estimated_out:  est_out,
        sim_passed:     false,
        sim_net_profit: U256::zero(),
    })
}

// ── ERC-20 storage slot discovery ─────────────────────────────────────────────

async fn find_balance_slot(provider: &Provider<Http>, token: H160) -> u32 {
    let probe = H160::from_low_u64_be(1);

    let real_bal = {
        let mut cd = hex::decode("70a08231").unwrap();
        cd.extend_from_slice(&[0u8; 12]);
        cd.extend_from_slice(probe.as_bytes());
        let raw = provider
            .call(&TransactionRequest::new().to(token).data(cd).into(), None)
            .await
            .unwrap_or_default();
        if raw.len() >= 32 { U256::from_big_endian(&raw[0..32]) } else { U256::zero() }
    };

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
            return slot;
        }
    }

    0
}

/// Compute the REVM storage key for `balanceOf[account]` given the mapping slot.
fn mapping_slot_key(account: H160, mapping_slot: u32) -> rU256 {
    let mut preimage = [0u8; 64];
    preimage[12..32].copy_from_slice(account.as_bytes());
    preimage[60..64].copy_from_slice(&mapping_slot.to_be_bytes());
    rU256::from_be_bytes(revm_keccak256(&preimage).0)
}

// ── REVM simulation ───────────────────────────────────────────────────────────
//
// revm 3.5.0 API:
//   - EthersDB implements Database (mutable, &mut self), NOT DatabaseRef.
//   - CacheDB<ExtDB> requires ExtDB: DatabaseRef, so we CANNOT wrap EthersDB
//     in CacheDB directly.
//   - Correct pattern for 3.5.0:
//       1. Build a CacheDB<EmptyDB> for all our pre-loaded state patches.
//       2. Build a separate EthersDB to fetch anything not in the cache.
//       3. Use EVM::new() and attach EthersDB with evm.database(ethers_db).
//          This makes the EVM use EthersDB as its live backend.
//       4. Pre-populate needed accounts/slots into the EVM's DB cache by
//          pre-fetching via EthersDB.basic() and inserting into a CacheDB<EmptyDB>,
//          then set that CacheDB as the database.
//
// The cleanest 3.5.0 pattern is:
//   - Create CacheDB<EthersDB<M>> — this works because EthersDB implements
//     DatabaseRef in revm 3.5.0 (it was added, then removed in later versions).
//   - Actually: the error says it does NOT implement DatabaseRef in the user's
//     installed version. So we use the alternative:
//   - Create EthersDB, call .basic() / .storage() manually to pre-load what
//     we need into a CacheDB<EmptyDB>, then set evm.database(cache_db).
//     Any slots we pre-load are in the cache; anything else hits EmptyDB
//     (returns zero) which is fine — we only need the patched vault balance
//     and executor ETH balance to work, everything else is loaded by the EVM
//     on demand from the EmptyDB (which returns default/empty values, meaning
//     the EVM will fetch from the real chain via... wait, EmptyDB doesn't RPC).
//
// CORRECT FINAL APPROACH for revm 3.5.0 where EthersDB is NOT DatabaseRef:
//   - Create EthersDB.
//   - Pre-load the specific accounts we need to patch via ethersdb.basic() and
//     ethersdb.storage() into a CacheDB<EmptyDB>.
//   - Patch the Vault balance slot and executor ETH into that CacheDB<EmptyDB>.
//   - Set evm.database(&mut cache_db_empty). All chain state that isn't in the
//     cache returns empty — this means the EVM sees the patched vault balance
//     but NOT real on-chain state for contracts like the PoolManager.
//
// That won't work for a real simulation. We need real chain state.
//
// THE ONLY CORRECT APPROACH with revm 3.5.0 EthersDB where DatabaseRef is not
// implemented:
//   - Use EthersDB directly as the EVM database (evm.database(&mut ethers_db)).
//   - Pre-patch slots by writing into ethers_db's internal cache before setting.
//   - EthersDB in 3.5.0 has an `accounts` field (HashMap<B160, DbAccount>) that
//     we can write to directly to inject our patches.
//
// This is what we do below: create EthersDB, directly mutate its accounts cache
// to insert our patches, then attach it to the EVM.

/// Run the candidate in a forked REVM instance (revm 3.5.0 API).
/// Returns (sim_passed, net_profit_in_token_a).
async fn simulate(
    c: &Candidate,
    http_rpc: &str,
    block_number: u64,
    executor_addr: H160,
    treasury: H160,
    gas_price_wei: U256,
    balance_slot: u32,
) -> Result<(bool, U256)> {
    use revm::primitives::{Address as rAddress, B160};

    let provider = Arc::new(
        Provider::<Http>::try_from(http_rpc).context("REVM http provider")?,
    );

    let block_id = Some(BlockId::Number(BlockNumber::Number(U64::from(block_number))));

    // FIX E0277 / E0432:
    // revm 3.5.0: EthersDB::new returns Option<EthersDB>, not Result.
    // EthersDB implements Database (not DatabaseRef), so we use it directly
    // as the EVM's backend via evm.database(&mut ethers_db).
    let mut ethers_db = EthersDB::new(Arc::clone(&provider), block_id)
        .ok_or_else(|| anyhow!("EthersDB::new returned None — check RPC URL"))?;

    // Pre-fetch and cache the PoolManager and token contracts so the EVM
    // doesn't make extra RPC calls for them during simulation.
    // We do this by calling ethers_db.basic() for each address we care about.
    // EthersDB caches the result in its internal HashMap after the first fetch.
    let token_a_b160  = B160::from(c.token_a.0);
    let executor_b160 = B160::from(executor_addr.0);
    let vault_b160    = B160::from(BALANCER_VAULT_ADDR.parse::<H160>()?.0);

    // Pre-load account info (bytecode, nonce, balance) into EthersDB's cache.
    let _ = ethers_db.basic(token_a_b160);
    let _ = ethers_db.basic(vault_b160);

    // Patch 1: Give the Balancer Vault enough token_a to fund the flash loan.
    // We write directly to EthersDB's accounts cache.
    let vault_balance_slot = mapping_slot_key(
        BALANCER_VAULT_ADDR.parse::<H160>()?,
        balance_slot,
    );
    let loan_value = rU256::from(c.loan_amount.as_u128());

    // EthersDB in revm 3.5.0 stores accounts in a HashMap<B160, DbAccount>.
    // DbAccount has a `storage` field (HashMap<rU256, rU256>).
    // We insert the patched storage slot directly.
    {
        let acc = ethers_db.accounts.entry(token_a_b160).or_default();
        acc.storage.insert(vault_balance_slot, loan_value);
    }

    // Patch 2: Give the executor 100 ETH so it can pay gas in the simulation.
    {
        let acc = ethers_db.accounts.entry(executor_b160).or_default();
        acc.info.balance = rU256::from(10u128.pow(20)); // 100 ETH
    }

    // Read treasury's token_a balance before the swap (from the patched cache).
    let treasury_b160    = B160::from(treasury.0);
    let treasury_slot    = mapping_slot_key(treasury, balance_slot);
    let bal_before: rU256 = ethers_db
        .accounts
        .get(&token_a_b160)
        .and_then(|acc| acc.storage.get(&treasury_slot))
        .copied()
        .unwrap_or(rU256::ZERO);

    let calldata = build_calldata(c, treasury);

    // Set up the EVM with EthersDB as its database (revm 3.5.0 API).
    let mut evm = EVM::new();
    evm.database(ethers_db);

    evm.env.block.number    = rU256::from(block_number + 1);
    evm.env.block.gas_limit = rU256::from(30_000_000u64);
    evm.env.tx.caller       = executor_b160;
    evm.env.tx.transact_to  = TransactTo::Call(executor_b160);
    evm.env.tx.data         = calldata.0.to_vec().into();
    evm.env.tx.value        = rU256::ZERO;
    evm.env.tx.gas_limit    = GAS_LIMIT;
    evm.env.tx.gas_price    = rU256::from(gas_price_wei.as_u128());

    let result = evm.transact_commit()
        .map_err(|e| anyhow!("REVM transact_commit: {:?}", e))?;

    // FIX E0614: gas_used in revm 3.5.0 ExecutionResult is u64, not &u64.
    // No dereference needed — just bind it directly.
    let gas_used: u64 = match result {
        ExecutionResult::Success { gas_used, .. } => gas_used,
        ExecutionResult::Revert { gas_used: _, ref output } => {
            debug!(reason = %String::from_utf8_lossy(output), "sim reverted");
            return Ok((false, U256::zero()));
        }
        ExecutionResult::Halt { reason, gas_used: _ } => {
            debug!(reason = ?reason, "sim halted");
            return Ok((false, U256::zero()));
        }
    };

    // Read treasury's token_a balance after the swap.
    // After transact_commit(), the EVM's database contains the post-execution
    // state. We read from the EthersDB's accounts cache (which was updated
    // by the commit).
    let db = evm.db().ok_or_else(|| anyhow!("EVM db missing after commit"))?;
    let bal_after: rU256 = db
        .accounts
        .get(&token_a_b160)
        .and_then(|acc| acc.storage.get(&treasury_slot))
        .copied()
        .unwrap_or(bal_before);

    if bal_after <= bal_before {
        return Ok((false, U256::zero()));
    }

    // Convert rU256 difference to ethers U256 safely.
    // rU256 is alloy/revm's U256 (256-bit). We take the low 128 bits since
    // no realistic profit exceeds u128::MAX.
    let diff_limbs = (bal_after - bal_before).as_limbs();
    let gross_gain = U256::from(diff_limbs[0] as u128 | ((diff_limbs[1] as u128) << 64));

    let actual_gas_cost = gas_price_wei * U256::from(gas_used);

    if gross_gain <= actual_gas_cost {
        debug!(
            gross    = ?gross_gain,
            gas_cost = ?actual_gas_cost,
            "sim: profitable before gas but not after"
        );
        return Ok((false, U256::zero()));
    }

    let net_profit = gross_gain - actual_gas_cost;
    Ok((true, net_profit))
}

// ── Calldata builder ──────────────────────────────────────────────────────────

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

// ── Flashbots submission ──────────────────────────────────────────────────────
//
// We sign the transaction ourselves and push raw RLP bytes as the bundle tx.
// BundleTransaction::Raw is created by passing Bytes into push_transaction —
// the From<Bytes> impl on BundleTransaction resolves to the Raw variant.

async fn submit_bundle(
    c: &Candidate,
    treasury: H160,
    executor_addr: H160,
    wallet: &LocalWallet,
    http_rpc: &str,
) -> Result<()> {
    let provider = Provider::<Http>::try_from(http_rpc)
        .context("submission http provider")?;

    let chain_id = provider.get_chainid().await?.as_u64();

    let fb_middleware = FlashbotsMiddleware::new(
        provider.clone(),
        Url::parse(FLASHBOTS_RELAY_URL).context("invalid relay URL")?,
        wallet.clone().with_chain_id(chain_id),
    );

    let current_block = provider.get_block_number().await?;
    let target_block  = current_block.as_u64() + 1;

    let base_fee = provider
        .get_block(BlockNumber::Latest)
        .await?
        .and_then(|b| b.base_fee_per_gas)
        .unwrap_or(U256::from(1_000_000_000u64));
    let priority_fee = U256::from(2_000_000_000u64);
    let max_fee      = base_fee * 2 + priority_fee;

    let nonce = provider
        .get_transaction_count(wallet.address(), None)
        .await?;

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

    let signature  = wallet.sign_transaction(&tx).await
        .context("tx signing failed")?;
    let signed_rlp = tx.rlp_signed(&signature);
    let signed_bytes = Bytes::from(signed_rlp.to_vec());

    let bundle = BundleRequest::new()
        .push_transaction(signed_bytes)
        .set_block(U64::from(target_block))
        .set_simulation_block(current_block);

    let pending = fb_middleware
        .send_bundle(&bundle)
        .await
        .context("send_bundle RPC call failed")?;

    // FIX deprecation warning: use the struct field directly instead of the
    // deprecated .bundle_hash() method.
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
    ws_rpc:        String,
    wallet:        LocalWallet,
    executor_addr: H160,
    treasury:      H160,
    state:         Arc<RwLock<EngineState>>,
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

    /// Scan all Initialize events, enrich each pool concurrently, add to graph.
    async fn bootstrap(&self) -> Result<()> {
        let provider = Arc::new(Provider::<Http>::try_from(&self.http_rpc)?);
        let mut raw  = discover_pools(&provider).await?;
        info!(found = raw.len(), "Pools found in logs");

        let mut loaded = 0usize;
        for chunk in raw.chunks_mut(BOOTSTRAP_CONCURRENCY) {
            let results: Vec<Result<()>> = {
                let futs: Vec<_> = chunk
                    .iter_mut()
                    .map(|pool| enrich_pool(&provider, pool))
                    .collect();
                join_all(futs).await
            };

            let mut s = self.state.write().await;
            for (pool, res) in chunk.iter().zip(results.into_iter()) {
                if res.is_ok() {
                    s.upsert_pool_edges(pool);
                    s.pools.insert(pool.pool_id, pool.clone());
                    loaded += 1;
                }
            }

            sleep(Duration::from_millis(50)).await;
        }

        info!(loaded, "Pools enriched and added to graph");
        Ok(())
    }

    /// Subscribe to Swap and ModifyLiquidity events.
    async fn event_loop(&self) -> Result<()> {
        let ws = Ws::connect(&self.ws_rpc)
            .await
            .context("WebSocket connect failed")?;
        let ws_provider   = Provider::new(ws);
        let http_provider = Provider::<Http>::try_from(&self.http_rpc)?;

        let pm: H160   = POOL_MANAGER_ADDR.parse()?;
        let swap: H256 = TOPIC_SWAP.parse()?;
        let mod_: H256 = TOPIC_MODIFY_LIQ.parse()?;

        let filter = Filter::new().address(pm).topic0(vec![swap, mod_]);
        let mut stream = ws_provider
            .subscribe_logs(&filter)
            .await
            .context("subscribe_logs failed")?;

        info!("Listening for pool events...");

        while let Some(log) = stream.next().await {
            let pool_id: PoolId = match log.topics.get(1) {
                Some(t) => (*t).into(),
                None    => continue,
            };

            self.refresh_pool(&http_provider, pool_id).await;

            if let Err(e) = self.search_and_execute(&http_provider).await {
                warn!(error = %e, "search_and_execute error");
            }
        }

        Err(anyhow!("WebSocket stream closed"))
    }

    /// Fetch fresh state for one pool and update both graphs.
    async fn refresh_pool(&self, provider: &Provider<Http>, pool_id: PoolId) {
        let mut state = self.state.write().await;
        let pool = match state.pools.get_mut(&pool_id) {
            Some(p) => p,
            None    => return,
        };

        match enrich_pool(provider, pool).await {
            Ok(()) => {
                let updated = pool.clone();
                state.upsert_pool_edges(&updated);
            }
            Err(e) => {
                debug!(pool_id = hex::encode(pool_id), "refresh failed: {e}");
                state.drop_pool_edges(pool_id);
            }
        }
    }

    /// Find negative cycles, build candidates, simulate, submit the best one.
    async fn search_and_execute(&self, provider: &Provider<Http>) -> Result<()> {
        let (block_result, gas_result) = tokio::join!(
            provider.get_block_number(),
            provider.get_gas_price(),
        );
        let block_number = block_result?.as_u64();
        let gas_price    = gas_result.unwrap_or(U256::from(1_000_000_000u64));

        let (cycles, _pools_snap) = {
            let state = self.state.read().await;
            let c     = find_triangular_cycles(&state);
            let p     = state.pools.clone();
            (c, p)
        };

        if cycles.is_empty() { return Ok(()); }

        let candidates: Vec<Candidate> = {
            let state = self.state.read().await;
            cycles
                .iter()
                .filter_map(|c| build_candidate(c, &state, gas_price))
                .collect()
        };

        if candidates.is_empty() { return Ok(()); }

        debug!(count = candidates.len(), "Candidates before simulation");

        let mut sorted = candidates;
        sorted.sort_by(|a, b| b.estimated_out.cmp(&a.estimated_out));

        for mut c in sorted {
            // Look up or discover the balance slot for this loan token.
            let balance_slot = {
                let cached = {
                    let state = self.state.read().await;
                    state.balance_slot_cache.get(&c.token_a).copied()
                };
                match cached {
                    Some(slot) => slot,
                    None => {
                        let slot = find_balance_slot(provider, c.token_a).await;
                        self.state.write().await
                            .balance_slot_cache.insert(c.token_a, slot);
                        slot
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
                    "Simulation passed — submitting"
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
                    error!(error = %e, "Bundle submission failed");
                }

                break;
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
                .add_directive("arb_engine=info".parse()?)
                .add_directive("warn".parse()?),
        )
        .init();

    let http_rpc = std::env::var("BASE_HTTP_RPC")
        .context("BASE_HTTP_RPC not set")?;
    let ws_rpc = std::env::var("BASE_WS_RPC")
        .context("BASE_WS_RPC not set")?;
    let private_key = std::env::var("PRIVATE_KEY")
        .context("PRIVATE_KEY not set")?;
    let executor_addr: H160 = std::env::var("EXECUTOR_ADDR")
        .context("EXECUTOR_ADDR not set")?
        .parse()
        .context("EXECUTOR_ADDR: invalid address")?;
    let treasury: H160 = std::env::var("TREASURY_ADDR")
        .context("TREASURY_ADDR not set")?
        .parse()
        .context("TREASURY_ADDR: invalid address")?;

    let controller = Controller::new(
        http_rpc, ws_rpc, &private_key, executor_addr, treasury,
    )?;

    loop {
        match controller.run().await {
            Ok(())  => warn!("Controller exited cleanly — restarting"),
            Err(e)  => error!(error = %e, "Controller crashed — restarting in 5s"),
        }
        sleep(Duration::from_secs(5)).await;
    }
}

// ── Cargo.toml ────────────────────────────────────────────────────────────────
//
// [package]
// name    = "arb_engine"
// version = "0.1.0"
// edition = "2021"
//
// [[bin]]
// name = "arb_engine"
// path = "src/main.rs"
//
// [dependencies]
// anyhow             = "1"
// ethers             = { version = "2", features = ["ws", "rustls"] }
// ethers-flashbots   = { git = "https://github.com/onbjerg/ethers-flashbots" }
// futures            = "0.3"
// hex                = "0.4"
// petgraph           = "0.6"
// revm               = { version = "3.5", features = ["ethersdb"] }
// tokio              = { version = "1", features = ["full"] }
// tracing            = "0.1"
// tracing-subscriber = { version = "0.3", features = ["json", "env-filter"] }
// url                = "2"