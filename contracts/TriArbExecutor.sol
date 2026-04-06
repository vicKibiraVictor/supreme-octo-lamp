// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

// TriArbExecutor — Triangular arbitrage executor for Uniswap v4 on Base (chain 8453).
//
// Flow:
//   execute()           → request Balancer V2 flash loan (zero fee)
//   receiveFlashLoan()  → unlock PoolManager, run three swaps, repay loan, send profit
//   unlockCallback()    → execute each SwapStep under flash accounting, return final balance
//   _executeStep()      → swap → sync → transfer → settle input; take output
//
// Invariants:
//   - No token balance is held between transactions.
//   - Only owner can call execute().
//   - All deltas must net to zero before unlockCallback returns or PoolManager reverts.
//   - Any shortfall on repayment causes a full revert — nothing is lost.

interface IERC20 {
    function transfer(address to, uint256 amount) external returns (bool);
    function approve(address spender, uint256 amount) external returns (bool);
    function balanceOf(address account) external view returns (uint256);
}

interface IBalancerVault {
    function flashLoan(
        address recipient,
        address[] calldata tokens,
        uint256[] calldata amounts,
        bytes calldata userData
    ) external;
}

interface IPoolManager {
    struct SwapParams {
        bool    zeroForOne;
        int256  amountSpecified;
        uint160 sqrtPriceLimitX96;
    }

    function unlock(bytes calldata data) external returns (bytes memory);
    function swap(PoolKey calldata key, SwapParams calldata params, bytes calldata hookData)
        external returns (BalanceDelta);
    function sync(address currency) external;
    function settle() external payable returns (uint256);
    function take(address currency, address to, uint256 amount) external;
}

struct PoolKey {
    address currency0;
    address currency1;
    uint24  fee;
    int24   tickSpacing;
    address hooks;
}

type BalanceDelta is int256;

library BalanceDeltaLib {
    function amount0(BalanceDelta d) internal pure returns (int128) {
        return int128(BalanceDelta.unwrap(d) >> 128);
    }
    function amount1(BalanceDelta d) internal pure returns (int128) {
        return int128(BalanceDelta.unwrap(d));
    }
}

contract TriArbExecutor {
    using BalanceDeltaLib for BalanceDelta;

    IBalancerVault public constant BALANCER_VAULT =
        IBalancerVault(0xBA12222222228d8Ba445958a75a0704d566BF2C8);
    IPoolManager public constant POOL_MANAGER =
        IPoolManager(0x498581fF718922c3f8e6A244956aF099B2652b2b);

    address public immutable owner;
    uint256 private _lock = 1;

    struct SwapStep {
        address tokenIn;
        address tokenOut;
        address currency0;
        address currency1;
        uint24  fee;
        int24   tickSpacing;
        address hooks;
        uint256 amountIn;
        uint256 minAmountOut;
    }

    struct ExecParams {
        address     loanToken;
        uint256     loanAmount;
        SwapStep[3] steps;
        address     treasury;
    }

    constructor() {
        owner = msg.sender;
    }

    function execute(
        address      loanToken,
        uint256      loanAmount,
        SwapStep[3] calldata steps,
        address      treasury
    ) external {
        require(msg.sender == owner,        "not owner");
        require(_lock == 1,                 "reentrant");
        require(loanAmount > 0,             "zero loan");
        require(treasury != address(0),     "zero treasury");

        _lock = 2;

        address[] memory tokens  = new address[](1);
        uint256[] memory amounts = new uint256[](1);
        tokens[0]  = loanToken;
        amounts[0] = loanAmount;

        BALANCER_VAULT.flashLoan(
            address(this),
            tokens,
            amounts,
            abi.encode(ExecParams({ loanToken: loanToken, loanAmount: loanAmount,
                                    steps: steps, treasury: treasury }))
        );

        _lock = 1;
    }

    function receiveFlashLoan(
        address[] calldata,
        uint256[] calldata,
        uint256[] calldata feeAmounts,
        bytes calldata userData
    ) external {
        require(msg.sender == address(BALANCER_VAULT), "caller not vault");
        require(feeAmounts.length > 0 && feeAmounts[0] == 0, "unexpected fee");

        ExecParams memory p = abi.decode(userData, (ExecParams));

        bytes memory result    = POOL_MANAGER.unlock(abi.encode(p));
        uint256 finalBalance   = abi.decode(result, (uint256));

        require(finalBalance >= p.loanAmount, "insufficient for repayment");

        require(
            IERC20(p.loanToken).transfer(address(BALANCER_VAULT), p.loanAmount),
            "repayment failed"
        );

        uint256 profit = finalBalance - p.loanAmount;
        if (profit > 0) {
            IERC20(p.loanToken).transfer(p.treasury, profit);
        }
    }

    function unlockCallback(bytes calldata data) external returns (bytes memory) {
        require(msg.sender == address(POOL_MANAGER), "caller not pool manager");

        ExecParams memory p = abi.decode(data, (ExecParams));

        uint256 currentAmount = p.loanAmount;
        for (uint256 i = 0; i < 3; i++) {
            currentAmount = _executeStep(p.steps[i], currentAmount);
        }

        return abi.encode(currentAmount);
    }

    function _executeStep(
        SwapStep memory step,
        uint256 amountIn
    ) internal returns (uint256 amountOut) {
        bool zeroForOne = step.tokenIn == step.currency0;

        BalanceDelta delta = POOL_MANAGER.swap(
            PoolKey({
                currency0:   step.currency0,
                currency1:   step.currency1,
                fee:         step.fee,
                tickSpacing: step.tickSpacing,
                hooks:       step.hooks
            }),
            IPoolManager.SwapParams({
                zeroForOne:        zeroForOne,
                amountSpecified:   -int256(amountIn),
                sqrtPriceLimitX96: zeroForOne
                    ? uint160(4295128739 + 1)
                    : uint160(1461446703485210103287273052203988822378723970342 - 1)
            }),
            ""
        );

        int128 inputDelta  = zeroForOne ? delta.amount0() : delta.amount1();
        int128 outputDelta = zeroForOne ? delta.amount1() : delta.amount0();

        if (inputDelta < 0) {
            uint256 owed = uint256(uint128(-inputDelta));
            POOL_MANAGER.sync(step.tokenIn);
            IERC20(step.tokenIn).approve(address(POOL_MANAGER), 0);      // reset allowance
            IERC20(step.tokenIn).approve(address(POOL_MANAGER), owed);
            IERC20(step.tokenIn).transfer(address(POOL_MANAGER), owed);
            POOL_MANAGER.settle();
        }

        if (outputDelta > 0) {
            amountOut = uint256(uint128(outputDelta));
            POOL_MANAGER.take(step.tokenOut, address(this), amountOut);
            require(amountOut >= step.minAmountOut, "slippage exceeded");
        }
    }

    function rescue(address token, uint256 amount) external {
        require(msg.sender == owner, "not owner");
        require(IERC20(token).transfer(owner, amount), "rescue failed");
    }
}