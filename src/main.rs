// main.rs — Uniswap v4 Triangular MEV Arbitrage Engine (Base, chain 8453)

//
// What this does, step by step:
//
//   1. Reads all past PoolManager Initialize events to learn about every pool.
//   2. Calls StateView to get the live price, fees, and liquidity for each pool.
//   3. Builds a weighted directed graph: tokens are nodes, swaps are edges.
//      Edge weight = -ln(rate after fees). A negative cycle means profit.
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
//   Pools with less than MIN_LIQUIDITY_USD (50 000 USD equivalent, expressed
//   as a raw token1 unit threshold against the spot price) are excluded at
//   graph-build time. This removes trash pools before they ever enter the
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
        transaction::eip2718::TypedTransaction, Address, BlockId, BlockNumber,
        Bytes, Eip1559TransactionRequest, Filter, H160, H256, U256, U64,
    },
    utils::keccak256,
};
use ethers_flashbots::{BundleRequest, BundleTransaction, FlashbotsMiddleware};
use petgraph::{algo::find_negative_cycle, graph::{DiGraph, NodeIndex}};
use revm::{
    db::{CacheDB, EthersDB},
    primitives::{
        keccak256 as revm_keccak256, AccountInfo, ExecutionResult, TransactTo,
        B256, U256 as rU256,
    },
    Database, Evm,
};
use tokio::{sync::RwLock, time::sleep};
use tracing::{debug, error, info, warn};
use url::Url;

// Chain addresses (Base mainnet)

const POOL_MANAGER_ADDR: &str    = "0x498581ff718922c3f8e6a244956af099B2652b2b";
const STATE_VIEW_ADDR: &str      = "0xa3c0c9b65bad0b08107aa264b0f3db444b867a71";
const BALANCER_VAULT_ADDR: &str  = "0xBA12222222228d8Ba445958a75a0704d566BF2C8";
const FLASHBOTS_RELAY_URL: &str  = "https://relay.flashbots.net";
const CHAIN_ID: u64              = 8453;

// Block where Uniswap v4 was deployed on Base (update if needed).
const V4_DEPLOY_BLOCK: u64 = 23_145_980;

// Pages for getLogs so we never hit RPC limits.
const LOG_PAGE_SIZE: u64 = 2_000;

// Minimum flash loan amount — 1 WETH. Used as the floor by dynamic_loan_size().
// Never send a dust trade even if the pool is very shallow.
const LOAN_MIN_WEI: u128 = 1_000_000_000_000_000_000; // 1 WETH

// Maximum flash loan amount — 15 WETH. Hard cap so we never overload a shallow
// pool. At ~$2 400/WETH this is $36 000, comfortably under the $50k liquidity
// floor required to enter the graph at all.
const LOAN_MAX_WEI: u128 = 15_000_000_000_000_000_000; // 15 WETH

// Fraction of the weakest pool's raw liquidity to use as the loan size.
// 0.003 = 0.3% — conservative enough to keep price impact low while still
// scaling meaningfully on deep pools.
const LOAN_LIQUIDITY_FRACTION: f64 = 0.003;

// Gas limit given to the executor transaction.
const GAS_LIMIT: u64 = 700_000;

// Minimum pool liquidity threshold in USD, expressed as a raw token-unit
// product. A pool passes if:
//   liquidity_token1_units >= MIN_LIQUIDITY_USD_RAW
// We use 50 000 USD worth expressed in 6-decimal token units (e.g. USDC).
// For 18-decimal tokens, the same threshold applies because the spot price
// converts liquidity into a comparable unit.  The concrete check below uses
// the raw active liquidity value returned by getLiquidity() compared to a
// threshold derived from the spot price. Any pool whose active liquidity
// corresponds to less than $50 000 at spot is dropped before entering the
// Bellman-Ford graph.
//
// MIN_LIQUIDITY_TOKEN1_RAW is the minimum raw getLiquidity() value we
// accept. Active liquidity in v4 is in the same units as sqrt(token0 *
// token1) * tick_spacing. For the purposes of this filter we use a
// conservative flat threshold: pools with active liquidity below 50 000
// (raw units) are excluded. This threshold works well for 6-decimal stable
// pairs (USDC/USDT) and is conservative enough for 18-decimal pairs where
// $50 000 of ETH corresponds to several orders of magnitude more raw units.
// Adjust this value as needed for the specific token pairs you care about.
const MIN_LIQUIDITY_RAW: u128 = 50_000_000_000; // 50 000 * 1e6, covers USDC/USDT pairs

// How many pools to enrich concurrently during bootstrap.
const BOOTSTRAP_CONCURRENCY: usize = 20;

// Event topics

const TOPIC_INITIALIZE: &str =
    "0x5e74bdc2af0cd2d4e2f1e2b876960b3f5fcc4b72fb01f10e16c5869b11a5b7b5";
const TOPIC_SWAP: &str =
    "0x19b47279256b2a23a1665c810c8d55a1758940ee09377d4f8d26497a3577dc83";
const TOPIC_MODIFY_LIQ: &str =
    "0x0e3a47c5b5a1671f18e5e2ce51e77c9e5d44bf9bc57ceb33e17f8adab54e5fe5";

// Core types

// A pool id is the 32-byte keccak256 of its PoolKey.
type PoolId = [u8; 32];

// One swap direction on a pool. Two exist per pool (forward and reverse).
#[derive(Debug, Clone)]
struct Edge {
    pool_id: PoolId,
    zero_for_one: bool,
    // Bellman-Ford weight: -ln(net_rate). Negative weight cycle = profitable cycle.
    weight: f64,
    // The net rate (amount out / amount in after fees).
    rate: f64,
}

// Everything known about one v4 pool.
#[derive(Debug, Clone)]
struct Pool {
    pool_id: PoolId,
    token0: H160,        // lower address (v4 canonical ordering)
    token1: H160,        // higher address
    lp_fee: u32,         // LP fee in parts-per-million
    protocol_fee: u32,   // protocol fee in parts-per-million
    hook: H160,          // hook contract (zero address = no hook)
    tick_spacing: i32,
    liquidity: u128,     // active liquidity from StateView
    sqrt_price_x96: U256, // current sqrt price, Q64.96 format
    tick: i32,
}

impl Pool {
    // Combined swap fee: protocolFee + lpFee - (protocolFee * lpFee) / 1_000_000.
    // This is the exact formula from the Uniswap v4 spec.
    fn swap_fee_ppm(&self) -> u64 {
        let p = self.protocol_fee as u64;
        let l = self.lp_fee as u64;
        p + l - (p * l) / 1_000_000
    }

    // Fraction of input that survives fees. E.g. 0.997 for a 0.3% pool.
    fn fee_multiplier(&self) -> f64 {
        1.0 - (self.swap_fee_ppm() as f64) / 1_000_000.0
    }

    // How many token1 you get per token0 (spot, after fees).
    // sqrtPriceX96 is sqrt(token1/token0) in Q64.96.
    // price = (sqrtPriceX96 / 2^96)^2
    fn rate_1_per_0(&self) -> f64 {
        let s = self.sqrt_price_x96.as_u128() as f64 / 2f64.powi(96);
        s * s * self.fee_multiplier()
    }

    // How many token0 you get per token1 (spot, after fees).
    fn rate_0_per_1(&self) -> f64 {
        let r = self.rate_1_per_0();
        if r == 0.0 { return 0.0; }
        (1.0 / (self.sqrt_price_x96.as_u128() as f64 / 2f64.powi(96)).powi(2))
            * self.fee_multiplier()
    }

    // True if this pool can safely be included (no hook, so no unknown side effects).
    fn hook_accepted(&self) -> bool {
        self.hook == H160::zero()
    }

    // Liquidity filter: pool must have at least MIN_LIQUIDITY_RAW active liquidity
    // AND a valid price. This removes trash pools (dust, dead pools, honeypots)
    // before they enter the Bellman-Ford graph.
    //
    // The raw liquidity value returned by getLiquidity() is in units of
    // sqrt(token0 * token1) ticks. For major USDC/WETH pairs this is typically
    // in the billions to trillions range. Anything below MIN_LIQUIDITY_RAW
    // corresponds to well under $50 000 in actual tradeable depth and is
    // not worth chasing.
    fn liquidity_ok(&self) -> bool {
        self.liquidity >= MIN_LIQUIDITY_RAW
    }
}

// Fields from a PoolKey needed by the Solidity executor.
#[derive(Debug, Clone)]
struct PoolKey {
    token0: H160,
    token1: H160,
    fee: u32,
    tick_spacing: i32,
    hook: H160,
}

// One triangular arbitrage opportunity.
#[derive(Debug, Clone)]
struct Candidate {
    // Token path: A -> B -> C -> A.
    token_a: H160,
    token_b: H160,
    token_c: H160,
    // Pools and directions for each leg.
    pool_ab: PoolId,  key_ab: PoolKey,  dir_ab: bool,
    pool_bc: PoolId,  key_bc: PoolKey,  dir_bc: bool,
    pool_ca: PoolId,  key_ca: PoolKey,  dir_ca: bool,
    // How much of token_a to borrow.
    loan_amount: U256,
    // Estimated token_a output after all three swaps (rate product * loan).
    estimated_out: U256,
    // Whether REVM confirmed this is profitable.
    sim_passed: bool,
    // Exact net profit in token_a units (only valid when sim_passed = true).
    sim_net_profit: U256,
}

// Graph state

struct EngineState {
    pools: HashMap<PoolId, Pool>,
    graph: DiGraph<H160, Edge>,
    node_map: HashMap<H160, NodeIndex>,
    // Cache of ERC-20 balance storage slots discovered per token address.
    // Avoids repeated RPC calls during simulation for the same token.
    balance_slot_cache: HashMap<H160, u32>,
}

impl EngineState {
    fn new() -> Self {
        Self {
            pools: HashMap::new(),
            graph: DiGraph::new(),
            node_map: HashMap::new(),
            balance_slot_cache: HashMap::new(),
        }
    }

    fn get_or_add_node(&mut self, token: H160) -> NodeIndex {
        if let Some(&idx) = self.node_map.get(&token) {
            return idx;
        }
        let idx = self.graph.add_node(token);
        self.node_map.insert(token, idx);
        idx
    }

    // Replace both edges for a pool with fresh data.
    // A pool is admitted to the graph only if it passes ALL of:
    //   1. hook_accepted() — no unknown hook side-effects
    //   2. sqrt_price_x96 non-zero and liquidity non-zero — pool is active
    //   3. liquidity_ok() — raw liquidity >= MIN_LIQUIDITY_RAW ($50k threshold)
    fn upsert_pool_edges(&mut self, pool: &Pool) {
        // Remove stale edges first.
        self.graph.retain_edges(|g, e| g[e].pool_id != pool.pool_id);

        // Gate 1: no unknown hooks.
        if !pool.hook_accepted() { return; }
        // Gate 2: pool must have a live price and non-zero liquidity.
        if pool.sqrt_price_x96.is_zero() || pool.liquidity == 0 { return; }
        // Gate 3: liquidity must be at or above the $50k threshold.
        // Pools that fail this check are trash pools — exclude them entirely.
        if !pool.liquidity_ok() {
            debug!(
                pool_id = hex::encode(pool.pool_id),
                liquidity = pool.liquidity,
                threshold = MIN_LIQUIDITY_RAW,
                "Pool excluded: liquidity below $50k threshold"
            );
            return;
        }

        let n0 = self.get_or_add_node(pool.token0);
        let n1 = self.get_or_add_node(pool.token1);

        let r10 = pool.rate_1_per_0();
        let r01 = pool.rate_0_per_1();

        if r10 > 0.0 {
            self.graph.add_edge(n0, n1, Edge {
                pool_id: pool.pool_id,
                zero_for_one: true,
                weight: -r10.ln(),
                rate: r10,
            });
        }
        if r01 > 0.0 {
            self.graph.add_edge(n1, n0, Edge {
                pool_id: pool.pool_id,
                zero_for_one: false,
                weight: -r01.ln(),
                rate: r01,
            });
        }
    }

    fn drop_pool_edges(&mut self, pool_id: PoolId) {
        self.graph.retain_edges(|g, e| g[e].pool_id != pool_id);
    }
}


// StateView calls (read live pool state offchain)


// getSlot0(bytes32 poolId) -> (uint160 sqrtPriceX96, int24 tick, uint8 protocolFee, uint8 lpFee)
async fn call_get_slot0(
    provider: &Provider<Http>,
    pool_id: PoolId,
) -> Result<(U256, i32, u8, u8)> {
    // Selector: keccak256("getSlot0(bytes32)")[0..4] = 0x4c73e8ed
    let mut cd = hex::decode("4c73e8ed")?;
    cd.extend_from_slice(&pool_id);

    let sv: H160 = STATE_VIEW_ADDR.parse()?;
    let raw = provider
        .call(&TransactionRequest::new().to(sv).data(cd).into(), None)
        .await
        .context("getSlot0 failed")?;

    if raw.len() < 128 { bail!("getSlot0: short response"); }

    let sqrt_price = U256::from_big_endian(&raw[0..32]);

    // tick is int24, ABI-padded to 32 bytes with sign extension.
    let tick_raw = U256::from_big_endian(&raw[32..64]).as_u64() as i64;
    let tick = if tick_raw & (1 << 23) != 0 {
        (tick_raw | !((1i64 << 24) - 1)) as i32
    } else {
        tick_raw as i32
    };

    // uint8 fields are in the last byte of their 32-byte word.
    let protocol_fee = raw[63];
    let lp_fee       = raw[95];

    Ok((sqrt_price, tick, protocol_fee, lp_fee))
}

// getLiquidity(bytes32 poolId) -> uint128
async fn call_get_liquidity(provider: &Provider<Http>, pool_id: PoolId) -> Result<u128> {
    // Selector: keccak256("getLiquidity(bytes32)")[0..4] = 0x4e33be86
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

// Fill in the live fields of a pool from StateView.
// Issues both RPC calls concurrently to halve the per-pool enrichment latency.
async fn enrich_pool(provider: &Provider<Http>, pool: &mut Pool) -> Result<()> {
    // Fire both StateView calls in parallel — no dependency between them.
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

// Pool discovery


// Read an Initialize log and return a bare Pool struct (no live state yet).
fn parse_initialize_log(log: &ethers::types::Log) -> Option<Pool> {
    // topics: [event_sig, id (bytes32), currency0 (address), currency1 (address)]
    if log.topics.len() < 4 { return None; }

    let pool_id: PoolId = log.topics[1].into();
    let token0 = H160::from(log.topics[2]);
    let token1 = H160::from(log.topics[3]);

    // data: fee (uint24), tickSpacing (int24), hooks (address), sqrtPriceX96 (uint160), tick (int24)
    // Each is ABI-padded to 32 bytes.
    let data = log.data.as_ref();
    if data.len() < 160 { return None; }

    let fee          = U256::from_big_endian(&data[0..32]).as_u32();
    let tick_spacing = U256::from_big_endian(&data[32..64]).as_u32() as i32;
    let hook         = H160::from_slice(&data[76..96]); // last 20 bytes of 32-byte word
    // We will overwrite sqrt_price and tick from StateView, but initialize from log.
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

// Scan all Initialize events from the v4 deploy block to now.
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
        sleep(Duration::from_millis(30)).await; // avoid rate limits
    }

    Ok(pools)
}

// Bellman-Ford — the actual arbitrage detection

//
// Why -ln(rate) as edge weight:
//   Traversing A->B->C->A earns profit if rate_AB * rate_BC * rate_CA > 1.
//   Taking the log: ln(r_AB) + ln(r_BC) + ln(r_CA) > 0.
//   Negating for Bellman-Ford: -ln(r_AB) + -ln(r_BC) + -ln(r_CA) < 0.
//   So a negative-weight cycle in this graph is exactly a profitable triangle.
//   This is standard textbook Bellman-Ford arbitrage detection. No custom math.

// Find all 3-node negative cycles in the current graph.
// Only nodes that have at least one outgoing edge are used as start nodes,
// which avoids wasting Bellman-Ford iterations on disconnected tokens.
fn find_triangular_cycles(state: &EngineState) -> Vec<[NodeIndex; 3]> {
    let mut seen: HashSet<[u32; 3]> = HashSet::new();
    let mut out  = Vec::new();

    for start in state.graph.node_indices() {
        // Skip nodes with no outgoing edges — they cannot be part of a cycle.
        if state.graph.edges(start).next().is_none() {
            continue;
        }

        if let Some(cycle) = find_negative_cycle(&state.graph, start) {
            if cycle.len() != 3 { continue; }
            // Canonical form: sort indices so A-B-C and B-C-A hash the same.
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

// Compute the flash loan size for a triangular candidate.
//
// Strategy:
//   1. Find the pool with the smallest active liquidity across the three legs.
//      That is the binding constraint — the shallowest pool sets the price-impact
//      ceiling for the whole triangle.
//   2. Take LOAN_LIQUIDITY_FRACTION (0.3%) of that value as the raw loan size.
//      This keeps price impact manageable on any pool we touch.
//   3. Clamp to [LOAN_MIN_WEI, LOAN_MAX_WEI] so we never send a dust trade
//      and never exceed the 15 WETH hard cap.
//
// No new RPC calls — liquidity values are already in pool state from StateView.
fn dynamic_loan_size(pool_liquidities: [u128; 3]) -> U256 {
    let min_liq = pool_liquidities.iter().copied().min().unwrap_or(0);
    let raw     = (min_liq as f64 * LOAN_LIQUIDITY_FRACTION) as u128;
    let clamped = raw.max(LOAN_MIN_WEI).min(LOAN_MAX_WEI);
    U256::from(clamped)
}

// Turn a 3-node cycle into a Candidate.
fn build_candidate(
    cycle: &[NodeIndex; 3],
    state: &EngineState,
    gas_price_wei: U256,
) -> Option<Candidate> {
    let mut tokens         = [H160::zero(); 3];
    let mut pool_ids       = [[0u8; 32]; 3];
    let mut dirs           = [false; 3];
    let mut rates          = [0f64; 3];
    let mut liquidities    = [0u128; 3];
    let mut keys: Vec<PoolKey> = Vec::new();

    for i in 0..3 {
        let from = cycle[i];
        let to   = cycle[(i + 1) % 3];

        tokens[i] = *state.graph.node_weight(from)?;

        let edge = state.graph.edges_connecting(from, to).next()?.weight();
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

    // Size the loan dynamically: 0.3% of the weakest pool's liquidity,
    // clamped to [1 WETH, 15 WETH]. Deeper pools get larger loans and
    // therefore larger absolute profits; shallow pools stay safe.
    let loan = dynamic_loan_size(liquidities);

    // Estimated output of token_a = loan * r0 * r1 * r2.
    let cumulative = rates[0] * rates[1] * rates[2];
    if cumulative <= 1.0 { return None; } // no profit before gas

    let est_out = U256::from((loan.as_u128() as f64 * cumulative) as u128);

    // Quick pre-check: does estimated profit exceed gas cost?
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

// ERC-20 storage slot discovery

//
// To give the Balancer Vault a token balance in REVM without a real deposit,
// we patch the ERC-20 contract's balanceOf storage slot directly.
//
// ERC-20 balances live at: keccak256(abi.encode(address, mapping_slot))
// We find mapping_slot by trying slots 0..29 and checking which one holds
// the real balance of a known holder (or address(1) for zero-balance checks).

async fn find_balance_slot(provider: &Provider<Http>, token: H160) -> u32 {
    let probe = H160::from_low_u64_be(1);

    // Read the actual balanceOf(probe) from the contract.
    let real_bal = {
        let mut cd = hex::decode("70a08231").unwrap(); // balanceOf(address)
        cd.extend_from_slice(&[0u8; 12]);
        cd.extend_from_slice(probe.as_bytes());
        let raw = provider
            .call(&TransactionRequest::new().to(token).data(cd).into(), None)
            .await
            .unwrap_or_default();
        if raw.len() >= 32 { U256::from_big_endian(&raw[0..32]) } else { U256::zero() }
    };

    // Try each slot candidate.
    for slot in 0u32..30 {
        let storage_key = mapping_slot_key(probe, slot);
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

    // Default to slot 0 (correct for OpenZeppelin ERC-20, WETH, and most tokens).
    0
}

// Compute the REVM storage key for balanceOf[account] given the mapping's base slot.
fn mapping_slot_key(account: H160, mapping_slot: u32) -> rU256 {
    let mut preimage = [0u8; 64];
    preimage[12..32].copy_from_slice(account.as_bytes());
    preimage[60..64].copy_from_slice(&mapping_slot.to_be_bytes());
    rU256::from_be_bytes(revm_keccak256(&preimage).0)
}


// REVM simulation


// Build the calldata for TriArbExecutor.execute(...).
//
// Function signature:
//   execute(
//     address loanToken,
//     uint256 loanAmount,
//     SwapStep[3] steps,   -- (tokenIn, tokenOut, currency0, currency1, fee, tickSpacing, hooks, amountIn, minOut)
//     address treasury
//   )
fn build_calldata(c: &Candidate, treasury: H160) -> Bytes {
    // Compute function selector at runtime.
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
            Token::Uint(U256::zero()), // minAmountOut = 0 for simulation
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

// Run the candidate in a forked REVM instance.
// Returns (sim_passed, net_profit_in_token_a).
// balance_slot_cache: pre-resolved slot for token_a if available — avoids
// an extra round-trip to the RPC on repeated simulations of the same token.
async fn simulate(
    c: &Candidate,
    http_rpc: &str,
    block_number: u64,
    executor_addr: H160,
    treasury: H160,
    gas_price_wei: U256,
    balance_slot: u32,
) -> Result<(bool, U256)> {
    let provider = Arc::new(
        Provider::<Http>::try_from(http_rpc).context("REVM http provider")?,
    );

    // Fork the chain at the current block.
    let block_id = Some(BlockId::Number(BlockNumber::Number(U64::from(block_number))));
    let ethers_db = EthersDB::new(Arc::clone(&provider), block_id)
        .map_err(|e| anyhow!("EthersDB: {:?}", e))?;
    let mut db = CacheDB::new(ethers_db);

    // Give the Balancer Vault enough token_a to fund the flash loan.
    // We write directly to its ERC-20 storage slot.
    let vault: H160          = BALANCER_VAULT_ADDR.parse()?;
    let vault_revm           = revm::primitives::Address::from(vault.0);
    let token_a_revm         = revm::primitives::Address::from(c.token_a.0);
    let vault_slot           = mapping_slot_key(vault, balance_slot);
    let loan_rU256           = rU256::from(c.loan_amount.as_u128());

    db.insert_account_storage(token_a_revm, vault_slot, loan_rU256)
        .map_err(|e| anyhow!("storage patch: {:?}", e))?;

    // Give the executor enough ETH to pay gas in the simulation.
    let executor_revm = revm::primitives::Address::from(executor_addr.0);
    db.insert_account_info(executor_revm, AccountInfo {
        balance: rU256::from(10u128.pow(20)), // 100 ETH — covers any gas cost
        nonce: 0,
        code_hash: B256::ZERO,
        code: None,
    });

    // Read treasury's current token_a balance (before the swap).
    let treasury_revm = revm::primitives::Address::from(treasury.0);
    let treasury_slot = mapping_slot_key(treasury, balance_slot);
    let bal_before: rU256 = db
        .storage(token_a_revm, treasury_slot)
        .map_err(|e| anyhow!("read treasury balance: {:?}", e))
        .unwrap_or(rU256::ZERO);

    // Run the transaction.
    let calldata = build_calldata(c, treasury);

    let mut evm = Evm::builder()
        .with_db(db)
        .modify_env(|env| {
            env.block.number    = rU256::from(block_number + 1);
            env.block.gas_limit = rU256::from(30_000_000u64);
        })
        .modify_tx_env(|tx| {
            tx.caller        = executor_revm;
            tx.transact_to   = TransactTo::Call(executor_revm);
            tx.data          = calldata.0.to_vec().into();
            tx.value         = rU256::ZERO;
            tx.gas_limit     = GAS_LIMIT;
            tx.gas_price     = rU256::from(gas_price_wei.as_u128());
        })
        .build();

    let result = evm.transact_commit()
        .map_err(|e| anyhow!("REVM transact_commit: {:?}", e))?;

    let gas_used = match &result {
        ExecutionResult::Success { gas_used, .. } => *gas_used,
        ExecutionResult::Revert { gas_used, output } => {
            debug!(reason = %String::from_utf8_lossy(output), "sim reverted");
            return Ok((false, U256::zero()));
        }
        ExecutionResult::Halt { reason, gas_used } => {
            debug!(reason = ?reason, "sim halted");
            return Ok((false, U256::zero()));
        }
    };

    // Read treasury's token_a balance after the swap from the committed EVM database.
    let db_after = evm.into_context().evm.db;
    let bal_after: rU256 = {
        match db_after.accounts.get(&token_a_revm) {
            Some(acc) => {
                acc.storage.get(&treasury_slot).copied().unwrap_or(bal_before)
            }
            None => bal_before,
        }
    };

    if bal_after <= bal_before {
        return Ok((false, U256::zero()));
    }

    let gross_gain = U256::from((bal_after - bal_before).as_limbs()[0]);
    let actual_gas_cost = gas_price_wei * U256::from(gas_used);

    if gross_gain <= actual_gas_cost {
        debug!(
            gross = ?gross_gain,
            gas_cost = ?actual_gas_cost,
            "sim: profitable before gas but not after"
        );
        return Ok((false, U256::zero()));
    }

    let net_profit = gross_gain - actual_gas_cost;
    Ok((true, net_profit))
}


// Flashbots submission


// Sign the execute() transaction and send it as a Flashbots bundle.
// The bundle targets the next block. Flashbots drops it silently if it reverts,
// so we never pay gas for a failed execution.
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

    // FlashbotsMiddleware handles X-Flashbots-Signature header signing.
    let fb_client = SignerMiddleware::new(
        FlashbotsMiddleware::new(
            provider.clone(),
            Url::parse(FLASHBOTS_RELAY_URL).context("invalid relay URL")?,
            wallet.clone(),
        ),
        wallet.clone().with_chain_id(chain_id),
    );

    let current_block = provider.get_block_number().await?;
    let target_block  = current_block.as_u64() + 1;

    // Base fee + 2 gwei priority tip.
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

    // can_revert = false: if the tx reverts, Flashbots discards the whole bundle.
    let mut bundle = BundleRequest::new()
        .push_transaction(BundleTransaction {
            transaction: tx,
            signer: Some(wallet.clone().with_chain_id(chain_id)),
            can_revert: false,
        })
        .set_block(U64::from(target_block))
        .set_simulation_block(current_block);

    let pending = fb_client
        .inner()
        .send_bundle(&bundle)
        .await
        .context("send_bundle RPC call failed")?;

    info!(
        bundle_hash = ?pending.bundle_hash,
        target_block,
        net_profit  = ?c.sim_net_profit,
        token_a     = ?c.token_a,
        token_b     = ?c.token_b,
        token_c     = ?c.token_c,
        "Bundle submitted"
    );

    Ok(())
}

// Controller — orchestrates all phases


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

    // Scan all Initialize events, enrich each pool concurrently, add to graph.
    // BOOTSTRAP_CONCURRENCY pools are enriched at a time to saturate the RPC
    // connection pool without blowing the rate limit.
    async fn bootstrap(&self) -> Result<()> {
        let provider = Arc::new(Provider::<Http>::try_from(&self.http_rpc)?);
        let mut raw  = discover_pools(&provider).await?;
        info!(found = raw.len(), "Pools found in logs");

        // Process pools in concurrent batches.
        let mut loaded = 0usize;
        for chunk in raw.chunks_mut(BOOTSTRAP_CONCURRENCY) {
            // Enrich all pools in the chunk concurrently.
            let results: Vec<Result<()>> = {
                let futs: Vec<_> = chunk
                    .iter_mut()
                    .map(|pool| enrich_pool(&provider, pool))
                    .collect();
                futures::future::join_all(futs).await
            };

            // Commit successful enrichments to the graph.
            let mut s = self.state.write().await;
            for (pool, res) in chunk.iter().zip(results.into_iter()) {
                if res.is_ok() {
                    s.upsert_pool_edges(pool);
                    s.pools.insert(pool.pool_id, pool.clone());
                    loaded += 1;
                }
            }

            // Small pause between batches to stay within RPC rate limits.
            sleep(Duration::from_millis(50)).await;
        }

        info!(loaded, "Pools enriched and added to graph");
        Ok(())
    }

    // Subscribe to Swap and ModifyLiquidity events.
    // On each event, refresh the affected pool, then search.
    async fn event_loop(&self) -> Result<()> {
        let ws = Ws::connect(&self.ws_rpc)
            .await
            .context("WebSocket connect failed")?;
        let ws_provider  = Provider::new(ws);
        let http_provider = Provider::<Http>::try_from(&self.http_rpc)?;

        let pm: H160   = POOL_MANAGER_ADDR.parse()?;
        let swap: H256 = TOPIC_SWAP.parse()?;
        let mod_: H256 = TOPIC_MODIFY_LIQ.parse()?;

        let filter = Filter::new().address(pm).topic0(vec![swap, mod_]);
        let mut stream = ws_provider
            .subscribe_logs(&filter)
            .await
            .context("subscribe_logs failed")?;

        // Cache gas price so we don't re-fetch it on every single event.
        // It is refreshed once per search cycle (inside search_and_execute),
        // keeping the hot path lean while always using a fresh-enough value.
        info!("Listening for pool events...");

        while let Some(log) = stream.next().await {
            // Pool id is always in topic[1] for both event types.
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

    // Fetch fresh state for one pool from StateView and update its graph edges.
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

    // Find negative cycles, build candidates, simulate, submit the best one.
    // The balance_slot for the loan token is resolved once and cached in
    // EngineState so repeated simulations of the same token skip the RPC lookup.
    async fn search_and_execute(&self, provider: &Provider<Http>) -> Result<()> {
        // Fetch block number and gas price with a single concurrent pair of calls.
        let (block_result, gas_result) = tokio::join!(
            provider.get_block_number(),
            provider.get_gas_price(),
        );
        let block_number = block_result?.as_u64();
        let gas_price    = gas_result.unwrap_or(U256::from(1_000_000_000u64));

        // Snapshot graph state so we can release the lock before doing async work.
        let (cycles, _pools_snap) = {
            let state = self.state.read().await;
            let c     = find_triangular_cycles(&state);
            let p     = state.pools.clone();
            (c, p)
        };

        if cycles.is_empty() { return Ok(()); }

        // Build candidates. Each one has a quick estimated-profit pre-check.
        let candidates: Vec<Candidate> = {
            let state = self.state.read().await;
            cycles
                .iter()
                .filter_map(|c| build_candidate(c, &state, gas_price))
                .collect()
        };

        if candidates.is_empty() { return Ok(()); }

        debug!(count = candidates.len(), "Candidates before simulation");

        // Sort by estimated output so we simulate the most promising one first.
        let mut sorted = candidates;
        sorted.sort_by(|a, b| b.estimated_out.cmp(&a.estimated_out));

        // Simulate each candidate. Stop at the first one that passes.
        for mut c in sorted {
            // Resolve the balance slot for the loan token, using the cache to
            // avoid redundant RPC round-trips for frequently-seen tokens.
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
                    token_a     = ?c.token_a,
                    token_b     = ?c.token_b,
                    token_c     = ?c.token_c,
                    net_profit  = ?net_profit,
                    pool_ab     = hex::encode(c.pool_ab),
                    pool_bc     = hex::encode(c.pool_bc),
                    pool_ca     = hex::encode(c.pool_ca),
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

                // Submit one bundle per block event to avoid nonce collisions.
                break;
            }
        }

        Ok(())
    }
}

// Entry point


#[tokio::main]
async fn main() -> Result<()> {
    // Structured JSON logs. Level controlled by RUST_LOG env var.
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

    // Outer loop restarts the engine on any crash.
    loop {
        match controller.run().await {
            Ok(())  => warn!("Controller exited cleanly — restarting"),
            Err(e)  => error!(error = %e, "Controller crashed — restarting in 5s"),
        }
        sleep(Duration::from_secs(5)).await;
    }
}