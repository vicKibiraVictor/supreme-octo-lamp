// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

// =============================================================================
// TriArbExecutor.sol — Minimal Triangular Arbitrage Executor
// Deployed on Base (chain 8453).
//
// Flow when execute() is called:
//   1. Requests a flash loan from the Balancer V2 Vault.
//   2. Balancer transfers the loan to this contract and calls receiveFlashLoan.
//   3. Inside receiveFlashLoan: unlocks the Uniswap v4 PoolManager.
//   4. Inside unlockCallback: executes three sequential swaps using v4 flash
//      accounting. Each swap settles its own delta before moving to the next.
//   5. After the third swap, token_a balance = loan + profit.
//   6. Repays Balancer (Balancer V2 has zero flash loan fees).
//   7. Sends remaining profit to the treasury address.
//   8. Any shortfall causes a full revert — nothing is lost.
//
// Design choices:
//   - No state between transactions. The contract holds no tokens.
//   - Only the owner can call execute(). Owner is set once at deployment.
//   - SwapStep carries explicit tokenIn and tokenOut so the contract never
//     has to guess currency ordering. The engine provides these.
//   - tick_spacing is stored as uint24 but interpreted as int24 — fine because
//     tick spacings are never negative in practice.
// =============================================================================

// =============================================================================
// Interfaces
// =============================================================================

interface IERC20 {
    function transfer(address to, uint256 amount) external returns (bool);
    function approve(address spender, uint256 amount) external returns (bool);
    function balanceOf(address account) external view returns (uint256);
}

// Balancer V2 Vault flash loan entry point.
interface IBalancerVault {
    function flashLoan(
        address recipient,
        address[] calldata tokens,
        uint256[] calldata amounts,
        bytes calldata userData
    ) external;
}

// Uniswap v4 PoolManager — only the functions we use.
interface IPoolManager {
    struct SwapParams {
        bool    zeroForOne;
        int256  amountSpecified;     // negative = exact input
        uint160 sqrtPriceLimitX96;
    }

    // Unlock and call unlockCallback on the caller.
    function unlock(bytes calldata data) external returns (bytes memory);

    // Execute a swap. Caller must be inside an unlock() context.
    function swap(
        PoolKey calldata key,
        SwapParams calldata params,
        bytes calldata hookData
    ) external returns (BalanceDelta);

    // Required before settling an ERC-20 input token.
    function sync(address currency) external;

    // Confirm that we have transferred tokens to the PoolManager.
    function settle() external payable returns (uint256);

    // Pull an output token from the PoolManager to a recipient.
    function take(address currency, address to, uint256 amount) external;
}

// A PoolKey uniquely identifies one v4 pool.
struct PoolKey {
    address currency0;   // lower address
    address currency1;   // higher address
    uint24  fee;         // LP fee in parts-per-million
    int24   tickSpacing;
    address hooks;
}

// BalanceDelta is returned by swap(). High 128 bits = amount0, low 128 = amount1.
// Negative = owed TO the pool. Positive = owed FROM the pool (we can claim it).
type BalanceDelta is int256;

library BalanceDeltaLib {
    function amount0(BalanceDelta d) internal pure returns (int128) {
        return int128(BalanceDelta.unwrap(d) >> 128);
    }
    function amount1(BalanceDelta d) internal pure returns (int128) {
        return int128(BalanceDelta.unwrap(d));
    }
}

// =============================================================================
// TriArbExecutor
// =============================================================================

contract TriArbExecutor {
    using BalanceDeltaLib for BalanceDelta;

    // Fixed addresses on Base.
    IBalancerVault public constant BALANCER_VAULT =
        IBalancerVault(0xBA12222222228d8Ba445958a75a0704d566BF2C8);
    IPoolManager public constant POOL_MANAGER =
        IPoolManager(0x498581ff718922c3f8e6a244956af099B2652b2b);

    // The account that is allowed to call execute().
    address public immutable owner;

    // Simple reentrancy guard.
    uint256 private _lock = 1;

    // ==========================================================================
    // Data types
    // ==========================================================================

    // One leg of the triangle.
    struct SwapStep {
        address tokenIn;     // token we provide to the pool
        address tokenOut;    // token we receive from the pool
        address currency0;   // PoolKey.currency0 (lower address)
        address currency1;   // PoolKey.currency1 (higher address)
        uint24  fee;         // PoolKey.fee
        int24   tickSpacing; // PoolKey.tickSpacing
        address hooks;       // PoolKey.hooks (zero for no-hook pools)
        uint256 amountIn;    // used for step 0 only; subsequent steps chain output
        uint256 minAmountOut;// slippage guard; set to 0 for REVM simulation
    }

    // Packed into userData for the Balancer callback.
    struct ExecParams {
        address   loanToken;
        uint256   loanAmount;
        SwapStep[3] steps;
        address   treasury;
    }

    // ==========================================================================
    // Constructor
    // ==========================================================================

    constructor() {
        owner = msg.sender;
    }

    // ==========================================================================
    // Public entry point
    // ==========================================================================

    // Called by the offchain engine after REVM confirms profitability.
    // loanToken  — the token to borrow and profit in (e.g. WETH)
    // loanAmount — how much to borrow
    // steps      — the three swap legs A->B, B->C, C->A
    // treasury   — where profit goes after repaying the loan
    function execute(
        address      loanToken,
        uint256      loanAmount,
        SwapStep[3] calldata steps,
        address      treasury
    ) external {
        require(msg.sender == owner, "not owner");
        require(_lock == 1,         "reentrant");
        require(loanAmount > 0,     "zero loan");
        require(treasury != address(0), "zero treasury");

        _lock = 2;

        bytes memory userData = abi.encode(ExecParams({
            loanToken:  loanToken,
            loanAmount: loanAmount,
            steps:      steps,
            treasury:   treasury
        }));

        address[] memory tokens  = new address[](1);
        uint256[] memory amounts = new uint256[](1);
        tokens[0]  = loanToken;
        amounts[0] = loanAmount;

        // Balancer V2 transfers amounts[0] of tokens[0] here, then calls
        // receiveFlashLoan. The loan must be repaid before that call returns.
        BALANCER_VAULT.flashLoan(address(this), tokens, amounts, userData);

        _lock = 1;
    }

    // ==========================================================================
    // Balancer flash loan callback
    // ==========================================================================

    // Called by the Balancer Vault after transferring the loan.
    // The loan must be repaid before this function returns, or Balancer reverts.
    function receiveFlashLoan(
        address[] calldata,  // tokens (not needed — already in userData)
        uint256[] calldata,  // amounts (not needed — already in userData)
        uint256[] calldata feeAmounts,
        bytes calldata userData
    ) external {
        require(msg.sender == address(BALANCER_VAULT), "caller not vault");
        require(feeAmounts[0] == 0, "unexpected fee"); // Balancer V2 is fee-free

        ExecParams memory p = abi.decode(userData, (ExecParams));

        // Approve the PoolManager to pull the loan token for the first swap.
        IERC20(p.loanToken).approve(address(POOL_MANAGER), p.loanAmount);

        // Run all three swaps inside a PoolManager unlock context.
        // The unlock call returns the final token_a balance after all swaps.
        bytes memory result = POOL_MANAGER.unlock(abi.encode(p));
        uint256 finalBalance = abi.decode(result, (uint256));

        // Check we have enough to repay.
        require(finalBalance >= p.loanAmount, "insufficient for repayment");

        // Repay the Balancer Vault (zero fee on V2, so repay exactly loanAmount).
        bool repaid = IERC20(p.loanToken).transfer(
            address(BALANCER_VAULT), p.loanAmount
        );
        require(repaid, "repayment transfer failed");

        // Send the profit to the treasury.
        uint256 profit = finalBalance - p.loanAmount;
        if (profit > 0) {
            IERC20(p.loanToken).transfer(p.treasury, profit);
        }
    }

    // ==========================================================================
    // Uniswap v4 unlock callback
    // ==========================================================================

    // Called by the PoolManager after unlock(). All three swaps happen here.
    // Must resolve all token deltas before returning, or PoolManager reverts.
    function unlockCallback(bytes calldata data) external returns (bytes memory) {
        require(msg.sender == address(POOL_MANAGER), "caller not pool manager");

        ExecParams memory p = abi.decode(data, (ExecParams));

        // currentAmount tracks the output of each step, which becomes the
        // input of the next step.
        uint256 currentAmount = p.loanAmount;

        for (uint256 i = 0; i < 3; i++) {
            currentAmount = _executeStep(p.steps[i], currentAmount);
        }

        // Return the final output so receiveFlashLoan can check repayment.
        return abi.encode(currentAmount);
    }

    // ==========================================================================
    // Internal: execute one swap step and resolve its delta
    // ==========================================================================

    // Executes one swap and settles the resulting delta.
    // Returns the amount of tokenOut received (which is used as amountIn next).
    function _executeStep(
        SwapStep memory step,
        uint256 amountIn
    ) internal returns (uint256 amountOut) {
        PoolKey memory key = PoolKey({
            currency0:   step.currency0,
            currency1:   step.currency1,
            fee:         step.fee,
            tickSpacing: step.tickSpacing,
            hooks:       step.hooks
        });

        // amountSpecified < 0 means exact-input swap (spend exactly amountIn).
        bool zeroForOne = step.tokenIn == step.currency0;

        IPoolManager.SwapParams memory params = IPoolManager.SwapParams({
            zeroForOne:        zeroForOne,
            amountSpecified:   -int256(amountIn),
            sqrtPriceLimitX96: zeroForOne
                ? uint160(4295128739 + 1)           // just above MIN_SQRT_RATIO
                : uint160(1461446703485210103287273052203988822378723970342 - 1) // just below MAX
        });

        BalanceDelta delta = POOL_MANAGER.swap(key, params, "");

        // Extract the two sides of the delta.
        int128 d0 = delta.amount0();
        int128 d1 = delta.amount1();

        // Determine which side is the input (negative = owed to pool)
        // and which is the output (positive = owed to us).
        int128 inputDelta  = zeroForOne ? d0 : d1;
        int128 outputDelta = zeroForOne ? d1 : d0;

        // Settle the input: sync -> transfer -> settle.
        // This follows the pattern from the Uniswap v4 flash accounting docs.
        if (inputDelta < 0) {
            uint256 owed = uint256(uint128(-inputDelta));
            POOL_MANAGER.sync(step.tokenIn);
            IERC20(step.tokenIn).transfer(address(POOL_MANAGER), owed);
            POOL_MANAGER.settle();
        }

        // Claim the output.
        if (outputDelta > 0) {
            amountOut = uint256(uint128(outputDelta));
            POOL_MANAGER.take(step.tokenOut, address(this), amountOut);
            require(amountOut >= step.minAmountOut, "slippage exceeded");
            // Approve the PoolManager to use the output as input for the next step.
            IERC20(step.tokenOut).approve(address(POOL_MANAGER), amountOut);
        }
    }

    // ==========================================================================
    // Recovery
    // ==========================================================================

    // Recover any ERC-20 tokens sent here by mistake.
    function rescue(address token, uint256 amount) external {
        require(msg.sender == owner, "not owner");
        IERC20(token).transfer(owner, amount);
    }

    receive() external payable {}
}