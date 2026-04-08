// Uniswap v4 Triangular MEV Arbitrage Engine — Base mainnet (chain 8453)
//
// Flow:
//   Ingest    → paginated subgraph (id_gt cursor) → pool universe
//   Enrich    → StateView via uniswap-v4-sdk extensions (sqrtPriceX96, liquidity, tick, protocol_fee)
//   Fast loop → refresh tracked pools → Bellman-Ford → REVM sim → Flashbots
//   Slow loop → subgraph re-ingest to discover newly qualifying pools
//
// Required env:  BASE_HTTP_RPC, PRIVATE_KEY, EXECUTOR_ADDR, TREASURY_ADDR
// Optional env:  FAST_LOOP_MS (default 400), SUBGRAPH_LOOP_S (default 120)

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
    time::Duration,
};

use alloy::{
    consensus::{SignableTransaction, TxEip1559},
    network::{EthereumWallet, TransactionBuilder},
    primitives::{
        address, keccak256, Address, Bytes, FixedBytes, TxHash, U256,
    },
    providers::{Provider, ProviderBuilder, RootProvider},
    rpc::types::{BlockId, BlockNumberOrTag, TransactionRequest},
    signers::local::PrivateKeySigner,
    sol,
    transports::http::{Client, Http},
};
use anyhow::{anyhow, bail, Context, Result};
use futures::future::join_all;
use petgraph::{
    algo::find_negative_cycle,
    graph::{DiGraph, NodeIndex},
    visit::EdgeRef,
};
use revm::{
    db::{CacheDB, EmptyDB},
    primitives::{
        keccak256 as revm_keccak256, AccountInfo, Address as B160, ExecutionResult, TransactTo,
        U256 as rU256,
    },
    Database, EVM,
};
use serde::Deserialize;
use tokio::{sync::RwLock, time::sleep};
use tracing::{debug, error, info, warn};
use uniswap_v4_sdk::extensions::pool_manager_lens::PoolManagerLens;

// ── Constants ──────────────────────────────────────────────────────────────────

const POOL_MANAGER_ADDR: Address = address!("498581ff718922c3f8e6a244956af099B2652b2b");
const STATE_VIEW_ADDR:   Address = address!("a3c0c9b65bad0b08107aa264b0f3db444b867a71");
const BALANCER_VAULT_ADDR: Address = address!("BA12222222228d8Ba445958a75a0704d566BF2C8");
const FLASHBOTS_RELAY_URL: &str  = "https://relay.flashbots.net";
const CHAIN_ID: u64 = 8453;

const SUBGRAPH_URL: &str =
    "https://gateway.thegraph.com/api/25e2802b9b016903d316a56fb0e96db3/subgraphs/id/DiYPVdygkfjDWhbxGSqAQxwBKmfKnkWQojqeM2rkLb3G";

const SUBGRAPH_PAGE_SIZE: usize = 1_000;
const ENRICH_CONCURRENCY: usize = 40;
const GAS_LIMIT: u64 = 700_000;

const LOAN_MIN: u128         = 50_000 * 1_000_000;
const LOAN_MAX_WEI: u128     = 15_000_000_000_000_000_000;
const LOAN_LIQ_FRACTION: f64 = 0.003;

const TWO_POW_96: f64 = 79_228_162_514_264_337_593_543_950_336.0;

// execute(address,uint256,(address,address,address,address,uint24,int24,address,uint256,uint256)[3],address)
// keccak256 → 093dbfdb
const SEL_EXECUTE: [u8; 4] = [0x09, 0x3d, 0xbf, 0xdb];

// ERC-20 balanceOf(address) → 0x70a08231
const SEL_BALANCE_OF: [u8; 4] = [0x70, 0xa0, 0x82, 0x31];

// ── Alloy sol! macro — ERC-20 balanceOf for balance slot discovery ─────────────

sol! {
    #[sol(rpc)]
    interface IERC20 {
        function balanceOf(address account) external view returns (uint256);
    }
}

// ── Core types ────────────────────────────────────────────────────────────────

type PoolId = FixedBytes<32>;
type AlloyProvider = RootProvider<Http<Client>>;

#[derive(Debug, Clone)]
struct Pool {
    pool_id:        PoolId,
    token0:         Address,
    token1:         Address,
    lp_fee:         u32,
    tick_spacing:   i32,
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
        1.0 - self.swap_fee_ppm() as f64 / 1_000_000.0
    }

    #[inline]
    fn rate_1_per_0(&self) -> f64 {
        let s = u128::try_from(self.sqrt_price_x96).unwrap_or(u128::MAX) as f64 / TWO_POW_96;
        s * s * self.fee_multiplier()
    }

    #[inline]
    fn rate_0_per_1(&self) -> f64 {
        let s = u128::try_from(self.sqrt_price_x96).unwrap_or(u128::MAX) as f64 / TWO_POW_96;
        let denom = s * s;
        if denom == 0.0 { return 0.0; }
        self.fee_multiplier() / denom
    }
}

#[derive(Debug, Clone)]
struct Edge {
    pool_id: PoolId,
    weight:  f64,
    rate:    f64,
}

#[derive(Debug, Clone)]
struct PoolKey {
    token0:       Address,
    token1:       Address,
    fee:          u32,
    tick_spacing: i32,
}

#[derive(Debug, Clone)]
struct Candidate {
    token_a:        Address,
    token_b:        Address,
    token_c:        Address,
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
    pools:              HashMap<PoolId, Pool>,
    meta_graph:         DiGraph<Address, Edge>,
    weight_graph:       DiGraph<Address, f64>,
    node_map:           HashMap<Address, NodeIndex>,
    balance_slot_cache: HashMap<Address, Option<u32>>,
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

    fn get_or_add_node(&mut self, token: Address) -> NodeIndex {
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
            self.sync_weight_graph();
            return;
        }

        let n0  = self.get_or_add_node(pool.token0);
        let n1  = self.get_or_add_node(pool.token1);
        let r10 = pool.rate_1_per_0();
        let r01 = pool.rate_0_per_1();

        if r10 > 0.0 {
            self.meta_graph.add_edge(n0, n1, Edge { pool_id: pool.pool_id, weight: -r10.ln(), rate: r10 });
        }
        if r01 > 0.0 {
            self.meta_graph.add_edge(n1, n0, Edge { pool_id: pool.pool_id, weight: -r01.ln(), rate: r01 });
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

// ── Parsed contract addresses ─────────────────────────────────────────────────

struct Addrs {
    state_view:     Address,
    balancer_vault: Address,
    pool_manager:   Address,
}

impl Addrs {
    fn load() -> Self {
        Self {
            state_view:     STATE_VIEW_ADDR,
            balancer_vault: BALANCER_VAULT_ADDR,
            pool_manager:   POOL_MANAGER_ADDR,
        }
    }
}

// ── Subgraph ingestion ────────────────────────────────────────────────────────

#[derive(Debug, Deserialize)]
struct SubgraphToken {
    id:       String,
    #[allow(dead_code)]
    decimals: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct SubgraphPool {
    id:           String,
    fee_tier:     String,
    tick_spacing: String,
    token0:       SubgraphToken,
    token1:       SubgraphToken,
}

#[derive(Debug, Deserialize)]
struct SubgraphData     { pools: Vec<SubgraphPool> }
#[derive(Debug, Deserialize)]
struct SubgraphResponse { data: SubgraphData }

fn parse_address(s: &str) -> Result<Address> {
    s.parse::<Address>().with_context(|| format!("bad address: {s}"))
}

fn parse_pool_id(hex_str: &str) -> Result<PoolId> {
    let s = hex_str.trim_start_matches("0x");
    if s.len() != 64 { bail!("pool_id wrong length: {hex_str}"); }
    let mut out = [0u8; 32];
    hex::decode_to_slice(s, &mut out)?;
    Ok(FixedBytes::from(out))
}

async fn fetch_subgraph_page(client: &reqwest::Client, last_id: &str) -> Result<Vec<SubgraphPool>> {
    let query = format!(
        r#"{{
          pools(
            first: {n}
            where: {{
              totalValueLockedUSD_gt: "50000"
              liquidity_gt: "0"
              hooks: "0x0000000000000000000000000000000000000000"
              id_gt: "{last_id}"
            }}
            orderBy: id
            orderDirection: asc
          ) {{
            id feeTier tickSpacing
            token0 {{ id decimals }}
            token1 {{ id decimals }}
          }}
        }}"#,
        n = SUBGRAPH_PAGE_SIZE,
    );
    let resp: SubgraphResponse = client
        .post(SUBGRAPH_URL)
        .json(&serde_json::json!({ "query": query }))
        .send().await.context("subgraph POST failed")?
        .json().await.context("subgraph JSON decode failed")?;
    Ok(resp.data.pools)
}

async fn ingest_subgraph(client: &reqwest::Client) -> Result<Vec<Pool>> {
    let mut all     = Vec::new();
    let mut last_id = String::new();

    loop {
        let page     = fetch_subgraph_page(client, &last_id).await?;
        let page_len = page.len();

        for sp in &page {
            let pool_id = match parse_pool_id(&sp.id)       { Ok(v) => v, Err(e) => { warn!(%e, "skip pool_id"); continue; } };
            let token0  = match parse_address(&sp.token0.id) { Ok(v) => v, Err(e) => { warn!(%e, "skip token0"); continue; } };
            let token1  = match parse_address(&sp.token1.id) { Ok(v) => v, Err(e) => { warn!(%e, "skip token1"); continue; } };
            let lp_fee: u32       = sp.fee_tier.parse().unwrap_or(0);
            let tick_spacing: i32 = sp.tick_spacing.parse().unwrap_or(0);
            all.push(Pool {
                pool_id, token0, token1, lp_fee, tick_spacing,
                sqrt_price_x96: U256::ZERO, liquidity: 0, tick: 0, protocol_fee: 0,
            });
        }

        debug!(page_pools = page_len, total = all.len(), "Subgraph page ingested");
        if page_len < SUBGRAPH_PAGE_SIZE { break; }
        if let Some(last) = page.last() { last_id = last.id.clone(); }
    }

    info!(total = all.len(), "Subgraph ingestion complete");
    Ok(all)
}

// ── StateView enrichment via uniswap-v4-sdk PoolManagerLens ──────────────────
//
// Directly uses the SDK pattern from the docs:
//   let lens = PoolManagerLens::new(manager, provider);
//   lens.get_slot0(pool_id, block_id).await   → (sqrtPriceX96, tick, protocolFee, lpFee)
//   lens.get_liquidity(pool_id, block_id).await → liquidity

async fn enrich_pool(provider: &Arc<AlloyProvider>, pool: &mut Pool) -> Result<()> {
    let lens = PoolManagerLens::new(STATE_VIEW_ADDR, Arc::clone(provider));

    let (slot0_res, liq_res) = tokio::join!(
        lens.get_slot0(pool.pool_id, None),
        lens.get_liquidity(pool.pool_id, None),
    );

    // get_slot0 returns (sqrtPriceX96: U160, tick: i24, protocolFee: u24, lpFee: u24)
    let (sqrt_price, tick, protocol_fee, lp_fee_chain) = slot0_res.context("getSlot0 failed")?;

    pool.sqrt_price_x96 = U256::from(sqrt_price);
    pool.tick           = tick;
    pool.protocol_fee   = protocol_fee;
    if lp_fee_chain > 0 { pool.lp_fee = lp_fee_chain; } // on-chain beats subgraph

    // get_liquidity returns u128
    pool.liquidity = liq_res.context("getLiquidity failed")?;

    Ok(())
}

// ── Bellman-Ford cycle detection ──────────────────────────────────────────────

fn find_triangular_cycles(state: &EngineState) -> Vec<[NodeIndex; 3]> {
    let mut seen = HashSet::new();
    let mut out  = Vec::new();
    for start in state.weight_graph.node_indices() {
        if state.weight_graph.edges(start).next().is_none() { continue; }
        if let Some(cycle) = find_negative_cycle(&state.weight_graph, start) {
            if cycle.len() != 3 { continue; }
            let mut key = [cycle[0].index() as u32, cycle[1].index() as u32, cycle[2].index() as u32];
            key.sort_unstable();
            if seen.insert(key) {
                out.push([cycle[0], cycle[1], cycle[2]]);
            }
        }
    }
    out
}

// ── Loan sizing ───────────────────────────────────────────────────────────────

#[inline]
fn dynamic_loan_size(liquidities: [u128; 3]) -> U256 {
    let min_liq = liquidities.iter().copied().min().unwrap_or(0);
    let raw     = (min_liq as f64 * LOAN_LIQ_FRACTION) as u128;
    U256::from(raw.max(LOAN_MIN).min(LOAN_MAX_WEI))
}

// ── Candidate construction ────────────────────────────────────────────────────

fn build_candidate(cycle: &[NodeIndex; 3], state: &EngineState, gas_price: U256) -> Option<Candidate> {
    let mut tokens      = [Address::ZERO; 3];
    let mut pool_ids    = [FixedBytes::<32>::ZERO; 3];
    let mut rates       = [0f64; 3];
    let mut liquidities = [0u128; 3];
    let mut keys        = [
        PoolKey { token0: Address::ZERO, token1: Address::ZERO, fee: 0, tick_spacing: 0 },
        PoolKey { token0: Address::ZERO, token1: Address::ZERO, fee: 0, tick_spacing: 0 },
        PoolKey { token0: Address::ZERO, token1: Address::ZERO, fee: 0, tick_spacing: 0 },
    ];

    for i in 0..3 {
        let from    = cycle[i];
        let to      = cycle[(i + 1) % 3];
        tokens[i]   = *state.meta_graph.node_weight(from)?;
        let edge    = state.meta_graph.edges_connecting(from, to).next()?.weight();
        pool_ids[i] = edge.pool_id;
        rates[i]    = edge.rate;
        let pool    = state.pools.get(&edge.pool_id)?;
        liquidities[i] = pool.liquidity;
        keys[i] = PoolKey { token0: pool.token0, token1: pool.token1, fee: pool.lp_fee, tick_spacing: pool.tick_spacing };
    }

    let loan       = dynamic_loan_size(liquidities);
    let cumulative = rates[0] * rates[1] * rates[2];
    if cumulative <= 1.0 { return None; }

    let est_out  = U256::from((u128::try_from(loan).unwrap_or(u128::MAX) as f64 * cumulative) as u128);
    let gas_cost = gas_price * U256::from(GAS_LIMIT);
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
        sim_net_profit: U256::ZERO,
    })
}

// ── ERC-20 balance slot discovery ─────────────────────────────────────────────

async fn find_balance_slot(provider: &Arc<AlloyProvider>, token: Address) -> Option<u32> {
    let probe = Address::from_low_u64_be(1);

    // Call balanceOf(probe) to get the real balance we're looking for
    let mut cd = [0u8; 36];
    cd[..4].copy_from_slice(&SEL_BALANCE_OF);
    cd[16..36].copy_from_slice(probe.as_slice());
    let req = TransactionRequest::default()
        .to(token)
        .input(Bytes::from(cd.to_vec()).into());
    let raw = provider.call(&req).await.ok()?;
    if raw.len() < 32 { return None; }
    let real_bal = U256::from_be_slice(&raw[..32]);
    if real_bal.is_zero() { return None; }

    for slot in 0u32..30 {
        let mut preimage = [0u8; 64];
        preimage[12..32].copy_from_slice(probe.as_slice());
        preimage[60..64].copy_from_slice(&slot.to_be_bytes());
        let key     = alloy::primitives::B256::from(keccak256(preimage));
        let stored  = provider.get_storage_at(token, key.into()).await.unwrap_or_default();
        let stored_u256 = U256::from_be_slice(stored.as_slice());
        if stored_u256 == real_bal {
            debug!(token = ?token, slot, "Balance slot found");
            return Some(slot);
        }
    }
    warn!(token = ?token, "Balance slot not found in 0-29");
    None
}

fn mapping_slot_key(account: Address, mapping_slot: u32) -> rU256 {
    let mut preimage = [0u8; 64];
    preimage[12..32].copy_from_slice(account.as_slice());
    preimage[60..64].copy_from_slice(&mapping_slot.to_be_bytes());
    rU256::from_be_bytes(revm_keccak256(&preimage).0)
}

// ── REVM simulation ───────────────────────────────────────────────────────────

fn build_calldata(c: &Candidate, treasury: Address) -> Bytes {
    use alloy::sol_types::SolValue;

    // Encode the execute call manually using alloy ABI encoding
    // execute(address,uint256,(address,address,address,address,uint24,int24,address,uint256,uint256)[3],address)
    let make_step = |tin: Address, tout: Address, key: &PoolKey, amount_in: U256| -> Vec<u8> {
        (tin, tout, key.token0, key.token1,
         U256::from(key.fee),
         U256::from(key.tick_spacing.unsigned_abs()),
         Address::ZERO,
         amount_in,
         U256::ZERO,
        ).abi_encode()
    };

    let mut payload = Vec::new();
    payload.extend_from_slice(&SEL_EXECUTE);
    payload.extend_from_slice(&(
        c.token_a,
        c.loan_amount,
        (
            make_step(c.token_a, c.token_b, &c.key_ab, c.loan_amount),
            make_step(c.token_b, c.token_c, &c.key_bc, U256::ZERO),
            make_step(c.token_c, c.token_a, &c.key_ca, U256::ZERO),
        ),
        treasury,
    ).abi_encode());

    Bytes::from(payload)
}

async fn simulate(
    c:             &Candidate,
    provider:      &Arc<AlloyProvider>,
    addrs:         &Addrs,
    block_number:  u64,
    executor_addr: Address,
    treasury:      Address,
    gas_price:     U256,
    balance_slot:  u32,
) -> Result<(bool, U256)> {
    let block_id = BlockId::Number(BlockNumberOrTag::Number(block_number));

    let token_a_b160:  B160 = B160::from(c.token_a.0 .0);
    let executor_b160: B160 = B160::from(executor_addr.0 .0);
    let vault_b160:    B160 = B160::from(addrs.balancer_vault.0 .0);
    let treasury_b160: B160 = B160::from(treasury.0 .0);
    let pm_b160:       B160 = B160::from(addrs.pool_manager.0 .0);

    // Fetch account state for relevant addresses
    let mut cache_db = CacheDB::new(EmptyDB::default());
    for addr in [token_a_b160, vault_b160, executor_b160, treasury_b160, pm_b160] {
        // For the alloy rewrite, seed with zero-state accounts; full EthersDB equivalent
        // would require an alloy-compatible DB adapter which is outside current revm 3.5 scope.
        cache_db.insert_account_info(addr, AccountInfo::default());
    }

    let vault_slot    = mapping_slot_key(addrs.balancer_vault, balance_slot);
    let treasury_slot = mapping_slot_key(treasury, balance_slot);

    cache_db
        .insert_account_storage(token_a_b160, vault_slot, rU256::from(u128::try_from(c.loan_amount).unwrap_or(u128::MAX)))
        .map_err(|e| anyhow!("vault balance patch: {e:?}"))?;

    cache_db.insert_account_info(executor_b160, AccountInfo {
        balance:   rU256::from(10u128.pow(20)),
        nonce:     1,
        code_hash: revm::primitives::KECCAK_EMPTY,
        code:      None,
    });

    let mut evm = EVM::new();
    evm.database(cache_db);
    evm.env.block.number    = rU256::from(block_number + 1);
    evm.env.block.gas_limit = rU256::from(30_000_000u64);
    evm.env.tx.caller       = executor_b160;
    evm.env.tx.transact_to  = TransactTo::Call(executor_b160);
    evm.env.tx.data         = build_calldata(c, treasury).to_vec().into();
    evm.env.tx.value        = rU256::ZERO;
    evm.env.tx.gas_limit    = GAS_LIMIT;
    evm.env.tx.gas_price    = rU256::from(u128::try_from(gas_price).unwrap_or(u128::MAX));

    let gas_used = match evm.transact_commit().map_err(|e| anyhow!("REVM: {e:?}"))? {
        ExecutionResult::Success { gas_used, .. } => gas_used,
        _ => return Ok((false, U256::ZERO)),
    };

    let bal_after: rU256 = evm.db.as_ref()
        .and_then(|db| db.accounts.get(&token_a_b160))
        .and_then(|acc| acc.storage.get(&treasury_slot))
        .copied()
        .unwrap_or(rU256::ZERO);

    let bal_before = rU256::ZERO; // seeded as zero
    if bal_after <= bal_before { return Ok((false, U256::ZERO)); }

    let diff  = bal_after - bal_before;
    let limbs = diff.as_limbs();
    let gross = U256::from(limbs[0] as u128 | ((limbs[1] as u128) << 64));
    let cost  = gas_price * U256::from(gas_used);
    if gross <= cost { return Ok((false, U256::ZERO)); }

    Ok((true, gross - cost))
}

// ── Flashbots submission ──────────────────────────────────────────────────────

async fn submit_bundle(
    c:             &Candidate,
    treasury:      Address,
    executor_addr: Address,
    signer:        &PrivateKeySigner,
    provider:      &Arc<AlloyProvider>,
) -> Result<()> {
    let nonce     = provider.get_transaction_count(signer.address()).await?;
    let cur_block = provider.get_block_number().await?;
    let base_fee  = provider.get_block(BlockId::latest()).await?
        .and_then(|b| b.header.base_fee_per_gas)
        .unwrap_or(1_000_000_000u64);
    let priority_fee: u128 = 2_000_000_000;

    let tx = TxEip1559 {
        chain_id:              CHAIN_ID,
        nonce,
        gas_limit:             GAS_LIMIT,
        max_fee_per_gas:       base_fee as u128 * 2 + priority_fee,
        max_priority_fee_per_gas: priority_fee,
        to:                    alloy::primitives::TxKind::Call(executor_addr),
        value:                 U256::ZERO,
        input:                 build_calldata(c, treasury),
        access_list:           Default::default(),
    };

    let wallet  = EthereumWallet::from(signer.clone());
    let signed  = tx.build(&wallet).await.context("tx signing failed")?;
    let raw_tx  = signed.encoded_2718();

    // Flashbots bundle submission via raw HTTP (ethers-flashbots not available in alloy stack)
    let bundle_body = serde_json::json!({
        "jsonrpc": "2.0",
        "method":  "eth_sendBundle",
        "params": [{
            "txs":         [format!("0x{}", hex::encode(&raw_tx))],
            "blockNumber": format!("0x{:x}", cur_block + 1),
        }],
        "id": 1
    });

    let fb_client = reqwest::Client::new();
    let resp = fb_client
        .post(FLASHBOTS_RELAY_URL)
        .json(&bundle_body)
        .send().await.context("Flashbots send failed")?
        .json::<serde_json::Value>().await?;

    info!(
        response     = %resp,
        target_block = cur_block + 1,
        net_profit   = ?c.sim_net_profit,
        token_a      = ?c.token_a,
        token_b      = ?c.token_b,
        token_c      = ?c.token_c,
        "Bundle submitted"
    );
    Ok(())
}

// ── Shared ingest + enrich ────────────────────────────────────────────────────

async fn ingest_and_enrich(
    state:    &Arc<RwLock<EngineState>>,
    http_rpc: &str,
    client:   &reqwest::Client,
) -> Result<()> {
    let mut pools  = ingest_subgraph(client).await?;
    let total      = pools.len();
    let provider   = Arc::new(
        ProviderBuilder::new().on_http(http_rpc.parse().context("invalid RPC url")?)
    );
    let mut loaded = 0usize;
    let mut failed = 0usize;

    for chunk in pools.chunks_mut(ENRICH_CONCURRENCY) {
        let futs: Vec<_> = chunk.iter_mut().map(|p| enrich_pool(&provider, p)).collect();
        let results = join_all(futs).await;
        let mut s = state.write().await;
        for (pool, res) in chunk.iter().zip(results) {
            match res {
                Ok(()) => { s.upsert_pool_edges(pool); s.pools.insert(pool.pool_id, pool.clone()); loaded += 1; }
                Err(e) => { debug!(pool_id = %pool.pool_id, error = %e, "Enrich failed"); failed += 1; }
            }
        }
    }

    let s = state.read().await;
    info!(loaded, failed, total, nodes = s.meta_graph.node_count(), edges = s.meta_graph.edge_count(), "Pool universe updated");
    Ok(())
}

// ── Fast loop tick ────────────────────────────────────────────────────────────

async fn fast_loop_tick(
    state:         &Arc<RwLock<EngineState>>,
    provider:      &Arc<AlloyProvider>,
    addrs:         &Addrs,
    executor_addr: Address,
    treasury:      Address,
    signer:        &PrivateKeySigner,
) -> Result<()> {
    let pool_ids: Vec<PoolId> = state.read().await.pools.keys().copied().collect();

    let (block_res, gas_res) = tokio::join!(
        provider.get_block_number(),
        provider.get_gas_price(),
    );
    let block_number = block_res?;
    let gas_price    = gas_res.map(U256::from).unwrap_or(U256::from(1_000_000_000u64));

    debug!(pools = pool_ids.len(), block = block_number, "Fast loop tick");

    for chunk in pool_ids.chunks(ENRICH_CONCURRENCY) {
        let mut pools: Vec<Pool> = {
            let s = state.read().await;
            chunk.iter().filter_map(|id| s.pools.get(id).cloned()).collect()
        };
        let futs: Vec<_> = pools.iter_mut().map(|p| enrich_pool(provider, p)).collect();
        let results = join_all(futs).await;
        let mut s = state.write().await;
        for (pool, res) in pools.iter().zip(results) {
            match res {
                Ok(()) => { s.upsert_pool_edges(pool); s.pools.insert(pool.pool_id, pool.clone()); }
                Err(_) => { s.drop_pool_edges(pool.pool_id); }
            }
        }
    }

    let cycles: Vec<[NodeIndex; 3]> = {
        let s = state.read().await;
        find_triangular_cycles(&s)
    };

    if cycles.is_empty() {
        debug!("No negative cycles found");
        return Ok(());
    }

    let mut candidates: Vec<Candidate> = {
        let s = state.read().await;
        cycles.iter().filter_map(|c| build_candidate(c, &s, gas_price)).collect()
    };

    if candidates.is_empty() { return Ok(()); }

    candidates.sort_unstable_by(|a, b| b.estimated_out.cmp(&a.estimated_out));

    info!(
        cycles     = cycles.len(),
        candidates = candidates.len(),
        block      = block_number,
        "Candidates found — simulating"
    );

    for mut c in candidates {
        let balance_slot = {
            let cached = state.read().await.balance_slot_cache.get(&c.token_a).copied();
            match cached {
                Some(slot) => slot,
                None => {
                    let slot = find_balance_slot(provider, c.token_a).await;
                    state.write().await.balance_slot_cache.insert(c.token_a, slot);
                    slot
                }
            }
        };
        let balance_slot = match balance_slot {
            Some(s) => s,
            None => { warn!(token_a = ?c.token_a, "Skipping candidate — balance slot unknown"); continue; }
        };

        let (passed, net_profit) = simulate(
            &c, provider, addrs, block_number, executor_addr, treasury, gas_price, balance_slot,
        ).await.unwrap_or_else(|e| { warn!(error = %e, "Simulation error"); (false, U256::ZERO) });

        if passed {
            c.sim_passed     = true;
            c.sim_net_profit = net_profit;
            info!(
                token_a    = ?c.token_a,
                token_b    = ?c.token_b,
                token_c    = ?c.token_c,
                net_profit = ?net_profit,
                pool_ab    = %c.pool_ab,
                pool_bc    = %c.pool_bc,
                pool_ca    = %c.pool_ca,
                "Simulation passed — submitting bundle"
            );
            if let Err(e) = submit_bundle(&c, treasury, executor_addr, signer, provider).await {
                error!(error = %e, "Bundle submission failed");
            }
            break;
        }
    }

    Ok(())
}

// ── Controller ────────────────────────────────────────────────────────────────

struct Controller {
    http_rpc:      String,
    signer:        PrivateKeySigner,
    executor_addr: Address,
    treasury:      Address,
    addrs:         Addrs,
    state:         Arc<RwLock<EngineState>>,
    sg_client:     reqwest::Client,
}

impl Controller {
    fn new(http_rpc: String, private_key: &str, executor_addr: Address, treasury: Address) -> Result<Self> {
        let signer: PrivateKeySigner = private_key.parse().context("invalid PRIVATE_KEY")?;
        Ok(Self {
            signer,
            addrs:     Addrs::load(),
            state:     Arc::new(RwLock::new(EngineState::new())),
            sg_client: reqwest::Client::builder().timeout(Duration::from_secs(30)).build()?,
            http_rpc,
            executor_addr,
            treasury,
        })
    }

    async fn run(&self) -> Result<()> {
        info!(chain_id = CHAIN_ID, "Engine starting");

        let fast_ms = std::env::var("FAST_LOOP_MS").ok().and_then(|v| v.parse().ok()).unwrap_or(400u64);
        let sg_secs = std::env::var("SUBGRAPH_LOOP_S").ok().and_then(|v| v.parse().ok()).unwrap_or(120u64);

        ingest_and_enrich(&self.state, &self.http_rpc, &self.sg_client).await
            .context("initial pool ingest failed")?;

        {
            let s = self.state.read().await;
            info!(pools = s.pools.len(), nodes = s.meta_graph.node_count(), edges = s.meta_graph.edge_count(), "Pool universe ready");
        }

        let provider = Arc::new(
            ProviderBuilder::new().on_http(self.http_rpc.parse().context("invalid RPC url")?)
        );

        let fast_handle = {
            let state         = Arc::clone(&self.state);
            let provider      = Arc::clone(&provider);
            let addrs         = Addrs::load();
            let executor_addr = self.executor_addr;
            let treasury      = self.treasury;
            let signer        = self.signer.clone();
            tokio::spawn(async move {
                loop {
                    if let Err(e) = fast_loop_tick(&state, &provider, &addrs, executor_addr, treasury, &signer).await {
                        warn!(error = %e, "Fast loop error");
                    }
                    sleep(Duration::from_millis(fast_ms)).await;
                }
            })
        };

        let slow_handle = {
            let state     = Arc::clone(&self.state);
            let http_rpc  = self.http_rpc.clone();
            let sg_client = self.sg_client.clone();
            tokio::spawn(async move {
                loop {
                    sleep(Duration::from_secs(sg_secs)).await;
                    info!("Slow loop: re-ingesting subgraph for new pools");
                    if let Err(e) = ingest_and_enrich(&state, &http_rpc, &sg_client).await {
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

    let executor_addr: Address = std::env::var("EXECUTOR_ADDR")
        .context("EXECUTOR_ADDR not set")?
        .parse().context("EXECUTOR_ADDR: invalid")?;

    let treasury: Address = std::env::var("TREASURY_ADDR")
        .context("TREASURY_ADDR not set")?
        .parse().context("TREASURY_ADDR: invalid")?;

    info!(executor = ?executor_addr, treasury = ?treasury, chain_id = CHAIN_ID, "Startup");

    let controller = Controller::new(http_rpc, &pk, executor_addr, treasury)?;

    loop {
        match controller.run().await {
            Ok(())  => warn!("Controller exited cleanly — restarting"),
            Err(e)  => error!(error = %e, "Controller crashed — restarting in 5s"),
        }
        sleep(Duration::from_secs(5)).await;
    }
}