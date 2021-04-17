/**
 *Submitted for verification at hecoinfo.com on 2021-04-15
*/

// SPDX-License-Identifier: MIT


pragma solidity >=0.6.0 <0.8.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

pragma solidity >=0.6.0 <0.8.0;

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryAdd(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        uint256 c = a + b;
        if (c < a) return (false, 0);
        return (true, c);
    }

    /**
     * @dev Returns the substraction of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function trySub(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        if (b > a) return (false, 0);
        return (true, a - b);
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryMul(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) return (true, 0);
        uint256 c = a * b;
        if (c / a != b) return (false, 0);
        return (true, c);
    }

    /**
     * @dev Returns the division of two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryDiv(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        if (b == 0) return (false, 0);
        return (true, a / b);
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryMod(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        if (b == 0) return (false, 0);
        return (true, a % b);
    }

    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");
        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b <= a, "SafeMath: subtraction overflow");
        return a - b;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        if (a == 0) return 0;
        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");
        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b > 0, "SafeMath: division by zero");
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b > 0, "SafeMath: modulo by zero");
        return a % b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {trySub}.
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        return a - b;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryDiv}.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting with custom message when dividing by zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryMod}.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        return a % b;
    }
}

pragma solidity >=0.6.0 <0.8.0;

/*
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with GSN meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

pragma solidity >=0.6.2 <0.8.0;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        // solhint-disable-next-line no-inline-assembly
        assembly { size := extcodesize(account) }
        return size > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
      return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: value }(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data, string memory errorMessage) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.staticcall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    function _verifyCallResult(bool success, bytes memory returndata, string memory errorMessage) private pure returns(bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

pragma solidity >=0.6.0 <0.8.0;


/**
 * @dev Implementation of the {IERC20} interface.
 *
 * This implementation is agnostic to the way tokens are created. This means
 * that a supply mechanism has to be added in a derived contract using {_mint}.
 * For a generic mechanism see {ERC20PresetMinterPauser}.
 *
 * TIP: For a detailed writeup see our guide
 * https://forum.zeppelin.solutions/t/how-to-implement-erc20-supply-mechanisms/226[How
 * to implement supply mechanisms].
 *
 * We have followed general OpenZeppelin guidelines: functions revert instead
 * of returning `false` on failure. This behavior is nonetheless conventional
 * and does not conflict with the expectations of ERC20 applications.
 *
 * Additionally, an {Approval} event is emitted on calls to {transferFrom}.
 * This allows applications to reconstruct the allowance for all accounts just
 * by listening to said events. Other implementations of the EIP may not emit
 * these events, as it isn't required by the specification.
 *
 * Finally, the non-standard {decreaseAllowance} and {increaseAllowance}
 * functions have been added to mitigate the well-known issues around setting
 * allowances. See {IERC20-approve}.
 */
contract ERC20 is Context, IERC20 {
    using SafeMath for uint256;

    mapping (address => uint256) private _balances;

    mapping (address => mapping (address => uint256)) private _allowances;

    uint256 private _totalSupply;

    string private _name;
    string private _symbol;
    uint8 private _decimals;

    /**
     * @dev Sets the values for {name} and {symbol}, initializes {decimals} with
     * a default value of 18.
     *
     * To select a different value for {decimals}, use {_setupDecimals}.
     *
     * All three of these values are immutable: they can only be set once during
     * construction.
     */
    constructor (string memory name_, string memory symbol_) public {
        _name = name_;
        _symbol = symbol_;
        _decimals = 18;
    }

    /**
     * @dev Returns the name of the token.
     */
    function name() public view virtual returns (string memory) {
        return _name;
    }

    /**
     * @dev Returns the symbol of the token, usually a shorter version of the
     * name.
     */
    function symbol() public view virtual returns (string memory) {
        return _symbol;
    }

    /**
     * @dev Returns the number of decimals used to get its user representation.
     * For example, if `decimals` equals `2`, a balance of `505` tokens should
     * be displayed to a user as `5,05` (`505 / 10 ** 2`).
     *
     * Tokens usually opt for a value of 18, imitating the relationship between
     * Ether and Wei. This is the value {ERC20} uses, unless {_setupDecimals} is
     * called.
     *
     * NOTE: This information is only used for _display_ purposes: it in
     * no way affects any of the arithmetic of the contract, including
     * {IERC20-balanceOf} and {IERC20-transfer}.
     */
    function decimals() public view virtual returns (uint8) {
        return _decimals;
    }

    /**
     * @dev See {IERC20-totalSupply}.
     */
    function totalSupply() public view virtual override returns (uint256) {
        return _totalSupply;
    }

    /**
     * @dev See {IERC20-balanceOf}.
     */
    function balanceOf(address account) public view virtual override returns (uint256) {
        return _balances[account];
    }

    /**
     * @dev See {IERC20-transfer}.
     *
     * Requirements:
     *
     * - `recipient` cannot be the zero address.
     * - the caller must have a balance of at least `amount`.
     */
    function transfer(address recipient, uint256 amount) public virtual override returns (bool) {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    /**
     * @dev See {IERC20-allowance}.
     */
    function allowance(address owner, address spender) public view virtual override returns (uint256) {
        return _allowances[owner][spender];
    }

    /**
     * @dev See {IERC20-approve}.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function approve(address spender, uint256 amount) public virtual override returns (bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    /**
     * @dev See {IERC20-transferFrom}.
     *
     * Emits an {Approval} event indicating the updated allowance. This is not
     * required by the EIP. See the note at the beginning of {ERC20}.
     *
     * Requirements:
     *
     * - `sender` and `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     * - the caller must have allowance for ``sender``'s tokens of at least
     * `amount`.
     */
    function transferFrom(address sender, address recipient, uint256 amount) public virtual override returns (bool) {
        _transfer(sender, recipient, amount);
        _approve(sender, _msgSender(), _allowances[sender][_msgSender()].sub(amount, "ERC20: transfer amount exceeds allowance"));
        return true;
    }

    /**
     * @dev Atomically increases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].add(addedValue));
        return true;
    }

    /**
     * @dev Atomically decreases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `spender` must have allowance for the caller of at least
     * `subtractedValue`.
     */
    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].sub(subtractedValue, "ERC20: decreased allowance below zero"));
        return true;
    }

    /**
     * @dev Moves tokens `amount` from `sender` to `recipient`.
     *
     * This is internal function is equivalent to {transfer}, and can be used to
     * e.g. implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event.
     *
     * Requirements:
     *
     * - `sender` cannot be the zero address.
     * - `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     */
    function _transfer(address sender, address recipient, uint256 amount) internal virtual {
        require(sender != address(0), "ERC20: transfer from the zero address");
        require(recipient != address(0), "ERC20: transfer to the zero address");

        _beforeTokenTransfer(sender, recipient, amount);

        _balances[sender] = _balances[sender].sub(amount, "ERC20: transfer amount exceeds balance");
        _balances[recipient] = _balances[recipient].add(amount);
        emit Transfer(sender, recipient, amount);
    }

    /** @dev Creates `amount` tokens and assigns them to `account`, increasing
     * the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements:
     *
     * - `to` cannot be the zero address.
     */
    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

        _beforeTokenTransfer(address(0), account, amount);

        _totalSupply = _totalSupply.add(amount);
        _balances[account] = _balances[account].add(amount);
        emit Transfer(address(0), account, amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, reducing the
     * total supply.
     *
     * Emits a {Transfer} event with `to` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     * - `account` must have at least `amount` tokens.
     */
    function _burn(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: burn from the zero address");

        _beforeTokenTransfer(account, address(0), amount);

        _balances[account] = _balances[account].sub(amount, "ERC20: burn amount exceeds balance");
        _totalSupply = _totalSupply.sub(amount);
        emit Transfer(account, address(0), amount);
    }

    /**
     * @dev Sets `amount` as the allowance of `spender` over the `owner` s tokens.
     *
     * This internal function is equivalent to `approve`, and can be used to
     * e.g. set automatic allowances for certain subsystems, etc.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `owner` cannot be the zero address.
     * - `spender` cannot be the zero address.
     */
    function _approve(address owner, address spender, uint256 amount) internal virtual {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    /**
     * @dev Sets {decimals} to a value other than the default one of 18.
     *
     * WARNING: This function should only be called from the constructor. Most
     * applications that interact with token contracts will not expect
     * {decimals} to ever change, and may work incorrectly if it does.
     */
    function _setupDecimals(uint8 decimals_) internal virtual {
        _decimals = decimals_;
    }

    /**
     * @dev Hook that is called before any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * will be to transferred to `to`.
     * - when `from` is zero, `amount` tokens will be minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens will be burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _beforeTokenTransfer(address from, address to, uint256 amount) internal virtual { }
}

pragma solidity 0.6.12;

interface ISafeBox {

    function bank() external view returns(address);

    function token() external view returns(address);

    function getSource() external view returns (string memory);

    function supplyRatePerBlock() external view returns (uint256);
    function borrowRatePerBlock() external view returns (uint256);

    function getBorrowInfo(uint256 _bid) external view 
            returns (address owner, uint256 amount, address strategy, uint256 pid);
    function getBorrowId(address _strategy, uint256 _pid, address _account) external view returns (uint256 borrowId);
    function getBorrowId(address _strategy, uint256 _pid, address _account, bool _add) external returns (uint256 borrowId);
    function getDepositTotal() external view returns (uint256);
    function getBorrowTotal() external view returns (uint256);
    // function getBorrowAmount(address _account) external view returns (uint256 value); 
    function getBaseTokenPerLPToken() external view returns (uint256);

    function deposit(uint256 _value) external;
    function withdraw(uint256 _value) external;
    
    function emergencyWithdraw() external;
    function emergencyRepay(uint256 _bid) external;

    function borrowInfoLength() external view returns (uint256);

    function borrow(uint256 _bid, uint256 _value, address _to) external;
    function repay(uint256 _bid, uint256 _value) external;
    function claim(uint256 _tTokenAmount) external;

    function update() external;
    function mintDonate(uint256 _value) external;

    function pendingSupplyAmount(address _account) external view returns (uint256 value);   
    function pendingBorrowAmount(uint256 _bid) external view returns (uint256 value);
    function pendingBorrowRewards(uint256 _bid) external view returns (uint256 value);
}
pragma solidity >=0.6.0 <0.8.0;

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor () internal {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

pragma solidity >=0.6.0 <0.8.0;


/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require((value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(value, "SafeERC20: decreased allowance below zero");
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) { // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}
pragma solidity 0.6.12;

interface ICTokenInterface {

  function isCToken() external view returns (bool);

  // function decimals() external returns (uint8);

  // function underlying() external returns (address);

  // function mint(uint mintAmount) external returns (uint);

  // function redeem(uint redeemTokens) external returns (uint);

  // function balanceOf(address user) external view returns (uint);

  // function borrowBalanceCurrent(address account) external returns (uint);

  // function borrowBalanceStored(address account) external view returns (uint);

  // function borrow(uint borrowAmount) external returns (uint);

  // function repayBorrow(uint repayAmount) external returns (uint);
  // function transfer(address dst, uint amount) external returns (bool);
  // function transferFrom(address src, address dst, uint amount) external returns (bool);
  // function approve(address spender, uint amount) external returns (bool);
  // function allowance(address owner, address spender) external view returns (uint);
  // function balanceOf(address owner) external view returns (uint);
  function balanceOfUnderlying(address owner) external view returns (uint);
  function getAccountSnapshot(address account) external view returns (uint, uint, uint, uint);
  function borrowRatePerBlock() external view returns (uint);
  function supplyRatePerBlock() external view returns (uint);
  function totalBorrowsCurrent() external returns (uint);
  function borrowBalanceCurrent(address account) external returns (uint);
  function borrowBalanceStored(address account) external view returns (uint);
  function exchangeRateCurrent() external returns (uint);
  function exchangeRateStored() external view returns (uint);
  function getCash() external view returns (uint);
  function accrueInterest() external returns (uint);
  function seize(address liquidator, address borrower, uint seizeTokens) external returns (uint);
}

pragma solidity 0.6.12;

interface IErc20Interface {

    /*** User Interface ***/
    function underlying() external view returns (address);

    function mint(uint mintAmount) external returns (uint);  //
    function redeem(uint redeemTokens) external returns (uint);
    function redeemUnderlying(uint redeemAmount) external returns (uint);
    function borrow(uint borrowAmount) external returns (uint);
    function repayBorrow(uint repayAmount) external returns (uint);
    // function repayBorrowBehalf(address borrower, uint repayAmount) external returns (uint);
    // function liquidateBorrow(address borrower, uint repayAmount, CTokenInterface cTokenCollateral) external returns (uint);

}
pragma solidity >=0.6.0 <0.8.0;

/**
 * @dev Contract module that helps prevent reentrant calls to a function.
 *
 * Inheriting from `ReentrancyGuard` will make the {nonReentrant} modifier
 * available, which can be applied to functions to make sure there are no nested
 * (reentrant) calls to them.
 *
 * Note that because there is a single `nonReentrant` guard, functions marked as
 * `nonReentrant` may not call one another. This can be worked around by making
 * those functions `private`, and then adding `external` `nonReentrant` entry
 * points to them.
 *
 * TIP: If you would like to learn more about reentrancy and alternative ways
 * to protect against it, check out our blog post
 * https://blog.openzeppelin.com/reentrancy-after-istanbul/[Reentrancy After Istanbul].
 */
abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor () internal {
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and make it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        // On the first call to nonReentrant, _notEntered will be true
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;

        _;

        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }
}

pragma solidity 0.6.12;

interface IActionPools {

    function getPoolInfo(uint256 _pid) external view 
        returns (address callFrom, uint256 callId, address rewardToken);
    function mintRewards(uint256 _callId) external;
    function getPoolIndex(address _callFrom, uint256 _callId) external view returns (uint256[] memory);

    function onAcionIn(uint256 _callId, address _account, uint256 _fromAmount, uint256 _toAmount) external;
    function onAcionOut(uint256 _callId, address _account, uint256 _fromAmount, uint256 _toAmount) external;
    function onAcionClaim(uint256 _callId, address _account) external;
    function onAcionEmergency(uint256 _callId, address _account) external;
    function onAcionUpdate(uint256 _callId) external;
}
pragma solidity 0.6.12;

interface IBuyback {
    function buyback(address _token, uint256 _value) external returns (uint256 value);
}
pragma solidity 0.6.12;

interface ICompActionTrigger {
    function getCATPoolInfo(uint256 _pid) external view 
        returns (address lpToken, uint256 allocRate, uint256 totalPoints, uint256 totalAmount);
    function getCATUserAmount(uint256 _pid, address _account) external view 
        returns (uint256 points);
}
pragma solidity 0.6.12;



// Safebox vault, deposit, withdrawal, borrowing, repayment
contract SafeBoxCTokenImpl is ERC20 {
    using SafeMath for uint256;
    using SafeERC20 for IERC20;

    IErc20Interface public eToken;
    ICTokenInterface public cToken;

    constructor (
        address _cToken
    ) public 
        ERC20(string(abi.encodePacked("bof-", ERC20(IErc20Interface(_cToken).underlying()).name())),
            string(abi.encodePacked("bof", ERC20(IErc20Interface(_cToken).underlying()).symbol()))) {
        _setupDecimals(ERC20(_cToken).decimals());
        eToken = IErc20Interface(_cToken);
        cToken = ICTokenInterface(_cToken);
        require(cToken.isCToken(), 'not ctoken address');
        IERC20(baseToken()).approve(_cToken, uint256(-1));
    }

    function baseToken() public virtual view returns (address) {
        return eToken.underlying();
    }

    function ctokenSupplyRatePerBlock() public virtual view returns (uint256) {
        return cToken.supplyRatePerBlock();
    }

    function ctokenBorrowRatePerBlock() public virtual view returns (uint256) {
        return cToken.borrowRatePerBlock();
    }

    function call_balanceOf(address _token, address _account) public virtual view returns (uint256 balance) {
        balance = IERC20(_token).balanceOf(_account);
    }
    
    function call_balanceOfCToken_this() public virtual view returns (uint256 balance) {
        balance = call_balanceOf(address(cToken), address(this));
    }    
    
    function call_balanceOfBaseToken_this() public virtual returns (uint256) {
        return call_balanceOfCToken_this().mul(cToken.exchangeRateCurrent()).div(1e18);
    }

    function call_borrowBalanceCurrent_this() public virtual returns (uint256) {
        return cToken.borrowBalanceCurrent(address(this));
    }

    function getBaseTokenPerCToken() public virtual view returns (uint256) {
        return cToken.exchangeRateStored();
    }

    // deposit
    function ctokenDeposit(uint256 _value) internal virtual returns (uint256 lpAmount) {
        uint256 cBalanceBefore = call_balanceOf(address(cToken), address(this));
        require(eToken.mint(uint256(_value)) == 0, 'deposit token error');
        uint256 cBalanceAfter = call_balanceOf(address(cToken), address(this));
        lpAmount = cBalanceAfter.sub(cBalanceBefore);
    }
    
    function ctokenWithdraw(uint256 _lpAmount) internal virtual returns (uint256 value) {
        uint256 cBalanceBefore = call_balanceOf(baseToken(), address(this));
        require(eToken.redeem(_lpAmount) == 0, 'withdraw supply ctoken error');
        uint256 cBalanceAfter = call_balanceOf(baseToken(), address(this));
        value = cBalanceAfter.sub(cBalanceBefore);
    }

    function ctokenClaim(uint256 _lpAmount) internal virtual returns (uint256 value) {
        value = ctokenWithdraw(_lpAmount);
    }

    function ctokenBorrow(uint256 _value) internal virtual returns (uint256 value) {
        uint256 cBalanceBefore = call_balanceOf(baseToken(), address(this));
        require(eToken.borrow(_value) == 0, 'borrow ubalance error');
        uint256 cBalanceAfter = call_balanceOf(baseToken(), address(this));
        value = cBalanceAfter.sub(cBalanceBefore);
    }

    function ctokenRepayBorrow(uint256 _value) internal virtual {
        require(eToken.repayBorrow(_value) == 0, 'repayBorrow ubalance error');
    }
}
pragma solidity 0.6.12;


library TenMath {
  using SafeMath for uint256;

  function min(uint256 v1, uint256 v2) public pure returns (uint256 vr) {
    vr = v1 > v2 ? v2 : v1; 
  }
    
  function safeSub(uint256 v1, uint256 v2) internal pure returns (uint256 vr) {
    vr = v1 > v2 ? v1.sub(v2) : 0; 
  }

  // implementation from https://github.com/Uniswap/uniswap-lib/commit/99f3f28770640ba1bb1ff460ac7c5292fb8291a0
  // original implementation: https://github.com/abdk-consulting/abdk-libraries-solidity/blob/master/ABDKMath64x64.sol#L687
  function sqrt(uint256 x) internal pure returns (uint256) {
    if (x == 0) return 0;
    uint256 xx = x;
    uint256 r = 1;

    if (xx >= 0x100000000000000000000000000000000) {
      xx >>= 128;
      r <<= 64;
    }

    if (xx >= 0x10000000000000000) {
      xx >>= 64;
      r <<= 32;
    }
    if (xx >= 0x100000000) {
      xx >>= 32;
      r <<= 16;
    }
    if (xx >= 0x10000) {
      xx >>= 16;
      r <<= 8;
    }
    if (xx >= 0x100) {
      xx >>= 8;
      r <<= 4;
    }
    if (xx >= 0x10) {
      xx >>= 4;
      r <<= 2;
    }
    if (xx >= 0x8) {
      r <<= 1;
    }

    r = (r + x / r) >> 1;
    r = (r + x / r) >> 1;
    r = (r + x / r) >> 1;
    r = (r + x / r) >> 1;
    r = (r + x / r) >> 1;
    r = (r + x / r) >> 1;
    r = (r + x / r) >> 1; // Seven iterations should be enough
    uint256 r1 = x / r;
    return (r < r1 ? r : r1);
  }
}

pragma solidity 0.6.12;

interface IFilDaPool {

    // 查询各种池子信息
    function claimComp(address holder) external;
    function claimComp(address holder, address[] memory cTokens) external;
    function claimComp(address[] memory holders, address[] memory cTokens, bool borrowers, bool suppliers) external;
}
pragma solidity 0.6.12;




contract SafeBoxCToken is SafeBoxCTokenImpl, ReentrancyGuard, Ownable, ICompActionTrigger, ISafeBox {
    using SafeMath for uint256;
    using SafeERC20 for IERC20;

    struct BorrowInfo {
        address strategy;      // borrow from strategy
        uint256 pid;           // borrow to pool
        address owner;         // borrower
        uint256 amount;        // borrow amount
        uint256 bPoints;       // borrow proportion
    }

    // supply manager
    uint256 public accDebtPerSupply;    // platform debt is shared to each supply lptoken

    // borrow manager
    BorrowInfo[] public borrowInfo;     // borrow order info
    mapping(address => mapping(address => mapping(uint256 => uint256))) public borrowIndex;   // _account, _strategy, _pid,  mapping id of borrowinfo, base from 1
    mapping(address => uint256) public  accountBorrowPoints;   // _account,  amount
    uint256 public lastBorrowCurrent;   // last settlement for 

    uint256 public borrowTotalPoints;          // total of user bPoints
    uint256 public borrowTotalAmountWithPlatform;  // total of user borrows and interests and platform
    uint256 public borrowTotalAmount;          // total of user borrows and interests
    uint256 public borrowTotal;                // total of user borrows

    uint256 public borrowLimitRate = 7.5e8;    // borrow limit,  max = borrowTotal * borrowLimitRate / 1e9, default=75%
    uint256 public borrowMinAmount;          // borrow min amount limit

    mapping(address => bool) public blacklist;  // deposit blacklist
    bool public depositEnabled = true;
    bool public emergencyRepayEnabled;
    bool public emergencyWithdrawEnabled;

    address public override bank;       // borrow can from bank only 
    address public override token;      // deposit and borrow token

    address public compActionPool;          // action pool for borrow rewards
    uint256 public constant CTOKEN_BORROW = 1;  // action pool borrow action id

    uint256 public optimalUtilizationRate1 = 6e8;  // Lending rate 1, ideal 1e9, default = 60%
    uint256 public optimalUtilizationRate2 = 7e8;  // Lending rate 2, ideal 1e9, default = 70%
    uint256 public stableRateSlope1 = 3e9;         // loan interest times in max borrow rate 1
    uint256 public stableRateSlope2 = 55e9;        // loan interest times in max borrow rate 2

    address public iBuyback;

    event SafeBoxDeposit(address indexed user, uint256 amount);
    event SafeBoxWithdraw(address indexed user, uint256 amount);
    event SafeBoxClaim(address indexed user, uint256 amount);

    event SetBlacklist(address indexed _account, bool _newset);
    event SetBuyback(address indexed buyback);
    event SetBorrowLimitRate(uint256 oldRate, uint256 newRate);
    event SetOptimalUtilizationRate(uint256 oldV1, uint256 oldV2, uint256 newV1, uint256 newV2);
    event SetStableRateSlope(uint256 oldV1, uint256 oldV2, uint256 newV1, uint256 newV2);

    constructor (
        address _bank,
        address _cToken
    ) public SafeBoxCTokenImpl(_cToken) {
        token = baseToken();
        require(IERC20(token).totalSupply() >= 0, 'token error');
        bank = _bank;
        // 0 id  Occupied,  Available bid never be zero
        borrowInfo.push(BorrowInfo(address(0), 0, address(0), 0, 0));
    }

    modifier onlyBank() {
        require(bank == msg.sender, 'borrow only from bank');
        _;
    }

    // link to actionpool , for borrower s allowance
    function getCATPoolInfo(uint256 _pid) external virtual override view 
        returns (address lpToken, uint256 allocRate, uint256 totalPoints, uint256 totalAmount) {
            _pid;
            lpToken = token;
            allocRate = 5e8; // never use
            totalPoints = borrowTotalPoints;
            totalAmount = borrowTotalAmountWithPlatform;
    }

    function getCATUserAmount(uint256 _pid, address _account) external virtual override view 
        returns (uint256 acctPoints) {
            _pid;
            acctPoints = accountBorrowPoints[_account];
    }

    function getSource() external virtual override view returns (string memory) {
        return 'filda';
    }

    // blacklist
    function setBlacklist(address _account, bool _newset) external onlyOwner {
        blacklist[_account] = _newset;
        emit SetBlacklist(_account, _newset);
    }

    function setCompAcionPool(address _compActionPool) public onlyOwner {
        compActionPool = _compActionPool;
    }

    function setBuyback(address _iBuyback) public onlyOwner {
        iBuyback = _iBuyback;
        emit SetBuyback(_iBuyback);
    }

    function setBorrowLimitRate(uint256 _borrowLimitRate) external onlyOwner {
        require(_borrowLimitRate <= 1e9, 'rate too high');
        emit SetBorrowLimitRate(borrowLimitRate, _borrowLimitRate);
        borrowLimitRate = _borrowLimitRate;
    }

    function setBorrowMinAmount(uint256 _borrowMinAmount) external onlyOwner {
        borrowMinAmount = _borrowMinAmount;
    }

    function setEmergencyRepay(bool _emergencyRepayEnabled) external onlyOwner {
        emergencyRepayEnabled = _emergencyRepayEnabled;
    }

    function setEmergencyWithdraw(bool _emergencyWithdrawEnabled) external onlyOwner {
        emergencyWithdrawEnabled = _emergencyWithdrawEnabled;
    }
    
    // for platform borrow interest rate
    function setOptimalUtilizationRate(uint256 _optimalUtilizationRate1, uint256 _optimalUtilizationRate2) external onlyOwner {
        require(_optimalUtilizationRate1 <= 1e9 && 
                _optimalUtilizationRate2 <= 1e9 && 
                _optimalUtilizationRate1 < _optimalUtilizationRate2
                , 'rate set error');
        emit SetOptimalUtilizationRate(optimalUtilizationRate1, optimalUtilizationRate2, _optimalUtilizationRate1, _optimalUtilizationRate2);
        optimalUtilizationRate1 = _optimalUtilizationRate1;
        optimalUtilizationRate2 = _optimalUtilizationRate2;
    }

    function setStableRateSlope(uint256 _stableRateSlope1, uint256 _stableRateSlope2) external onlyOwner {
        require(_stableRateSlope1 <= 1e4*1e9 && _stableRateSlope1 >= 1e9 &&
                 _stableRateSlope2 <= 1e4*1e9 && _stableRateSlope2 >= 1e9 , 'rate set error');
        emit SetStableRateSlope(stableRateSlope1, stableRateSlope2, _stableRateSlope1, _stableRateSlope2);
        stableRateSlope1 = _stableRateSlope1;
        stableRateSlope2 = _stableRateSlope2;
    }

    function supplyRatePerBlock() external override view returns (uint256) {
        return ctokenSupplyRatePerBlock();
    }

    function borrowRatePerBlock() external override view returns (uint256) {
        return ctokenBorrowRatePerBlock().mul(getBorrowFactorPrewiew()).div(1e9);
    }

    function borrowInfoLength() external override view returns (uint256) {
        return borrowInfo.length.sub(1);
    }

    function getBorrowInfo(uint256 _bid) external override view 
        returns (address owner, uint256 amount, address strategy, uint256 pid) {

        strategy = borrowInfo[_bid].strategy;
        pid = borrowInfo[_bid].pid;
        owner = borrowInfo[_bid].owner;
        amount = borrowInfo[_bid].amount;
    }

    function getBorrowFactorPrewiew() public virtual view returns (uint256) {
        return _getBorrowFactor(getDepositTotal());
    }

    function getBorrowFactor() public virtual returns (uint256) {
        return _getBorrowFactor(call_balanceOfBaseToken_this());
    }

    function _getBorrowFactor(uint256 supplyAmount) internal virtual view returns (uint256 value) {
        if(supplyAmount <= 0) {
            return uint256(1e9);
        }
        uint256 borrowRate = getBorrowTotal().mul(1e9).div(supplyAmount);
        if(borrowRate <= optimalUtilizationRate1) {
            return uint256(1e9);
        }
        uint256 value1 = stableRateSlope1.sub(1e9).mul(borrowRate.sub(optimalUtilizationRate1))
                    .div(uint256(1e9).sub(optimalUtilizationRate1))
                    .add(uint256(1e9));
        if(borrowRate <= optimalUtilizationRate2) {
            value = value1;
            return value;
        }
        uint256 value2 = stableRateSlope2.sub(1e9).mul(borrowRate.sub(optimalUtilizationRate2))
                    .div(uint256(1e9).sub(optimalUtilizationRate2))
                    .add(uint256(1e9));
        value = value2 > value1 ? value2 : value1;
    }

    function getBorrowTotal() public virtual override view returns (uint256) {
        return borrowTotalAmountWithPlatform;
    }

    function getDepositTotal() public virtual override view returns (uint256) {
        return totalSupply().mul(getBaseTokenPerLPToken()).div(1e18);
    }

    function getBaseTokenPerLPToken() public virtual override view returns (uint256) {
        return getBaseTokenPerCToken();
    }

    function pendingSupplyAmount(address _account) external virtual override view returns (uint256 value) {
        value = call_balanceOf(address(this), _account).mul(getBaseTokenPerLPToken()).div(1e18);
    }

    function pendingBorrowAmount(uint256 _bid) public virtual override view returns (uint256 value) {
        value = borrowInfo[_bid].amount;
    }

    // borrow interest, the sum of filda interest and platform interest
    function pendingBorrowRewards(uint256 _bid) public virtual override view returns (uint256 value) {
        if(borrowTotalPoints <= 0) {
            return 0;
        }
        value = borrowInfo[_bid].bPoints.mul(borrowTotalAmountWithPlatform).div(borrowTotalPoints);
        value = TenMath.safeSub(value, borrowInfo[_bid].amount);
    }

    // deposit
    function deposit(uint256 _value) external virtual override nonReentrant {
        update();
        IERC20(token).safeTransferFrom(msg.sender, address(this), _value);
        _deposit(msg.sender, _value);
    }

    function _deposit(address _account, uint256 _value) internal returns (uint256) {
        require(depositEnabled, 'safebox closed');
        require(!blacklist[_account], 'address in blacklist');
        // token held in contract
        uint256 balanceInput = call_balanceOf(token, address(this));
        require(balanceInput > 0 &&  balanceInput >= _value, 'where s token?');

        // update booking, mintValue is number of deposit credentials
        uint256 mintValue = ctokenDeposit(_value);
        if(mintValue > 0) {
            _mint(_account, mintValue);
        }
        emit SafeBoxDeposit(_account, mintValue);
        return mintValue;
    }

    function withdraw(uint256 _tTokenAmount) external virtual override nonReentrant {
        update();
        _withdraw(msg.sender, _tTokenAmount);
    }

    function _withdraw(address _account, uint256 _tTokenAmount) internal returns (uint256) {
        // withdraw if lptokens value is not up borrowLimitRate
        if(_tTokenAmount > balanceOf(_account)) {
            _tTokenAmount = balanceOf(_account);
        }
        uint256 maxBorrowAmount = call_balanceOfCToken_this().sub(_tTokenAmount)
                                    .mul(getBaseTokenPerLPToken()).div(1e18)
                                    .mul(borrowLimitRate).div(1e9);
        require(maxBorrowAmount >= borrowTotalAmountWithPlatform, 'no money to withdraw');

        _burn(_account, uint256(_tTokenAmount));

        if(accDebtPerSupply > 0) {
            // If platform loss, the loss will be shared by supply
            uint256 debtAmount = _tTokenAmount.mul(accDebtPerSupply).div(1e18);
            require(_tTokenAmount >= debtAmount, 'debt too much');
            _tTokenAmount = _tTokenAmount.sub(debtAmount);
        }

        ctokenWithdraw(_tTokenAmount);
        tokenSafeTransfer(address(token), _account);
        emit SafeBoxWithdraw(_account, _tTokenAmount);
        return _tTokenAmount;
    }

    function claim(uint256 _value) external virtual override nonReentrant {
        update();
        _claim(msg.sender, uint256(_value));
    }

    function _claim(address _account, uint256 _value) internal {
        emit SafeBoxClaim(_account, _value);
    }

    function getBorrowId(address _strategy, uint256 _pid, address _account)
        public virtual override view returns (uint256 borrowId) {
        borrowId = borrowIndex[_account][_strategy][_pid];
    }

    function getBorrowId(address _strategy, uint256 _pid, address _account, bool _add) 
        external virtual override onlyBank returns (uint256 borrowId) {

        require(_strategy != address(0), 'borrowid _strategy error');
        require(_account != address(0), 'borrowid _account error');
        borrowId = getBorrowId(_strategy, _pid, _account);
        if(borrowId == 0 && _add) {
            borrowInfo.push(BorrowInfo(_strategy, _pid, _account, 0, 0));
            borrowId = borrowInfo.length.sub(1);
            borrowIndex[_account][_strategy][_pid] = borrowId;
        }
        require(borrowId > 0, 'not found borrowId');
    }

    function borrow(uint256 _bid, uint256 _value, address _to) external virtual override onlyBank {
        update();
        _borrow(_bid, _value, _to);
    }

    function _borrow(uint256 _bid, uint256 _value, address _to) internal {
        // withdraw if lptokens value is not up borrowLimitRate
        uint256 maxBorrowAmount = call_balanceOfCToken_this()
                                    .mul(getBaseTokenPerLPToken()).div(1e18)
                                    .mul(borrowLimitRate).div(1e9);
        require(maxBorrowAmount >= borrowTotalAmountWithPlatform.add(_value), 'no money to borrow');
        require(_value >= borrowMinAmount, 'borrow amount too low');

        BorrowInfo storage borrowCurrent = borrowInfo[_bid];

        // borrow
        uint256 ubalance = ctokenBorrow(_value);
        require(ubalance == _value, 'token borrow error');

        tokenSafeTransfer(address(token), _to);

        // booking
        uint256 addPoint = _value;
        if(borrowTotalPoints > 0) {
            addPoint = _value.mul(borrowTotalPoints).div(borrowTotalAmountWithPlatform);
        }

        borrowCurrent.bPoints = borrowCurrent.bPoints.add(addPoint);
        borrowTotalPoints = borrowTotalPoints.add(addPoint);
        borrowTotalAmountWithPlatform = borrowTotalAmountWithPlatform.add(_value);
        lastBorrowCurrent = call_borrowBalanceCurrent_this();

        borrowCurrent.amount = borrowCurrent.amount.add(_value);
        borrowTotal = borrowTotal.add(_value);
        borrowTotalAmount = borrowTotalAmount.add(_value);
        
        // notify for action pool
        uint256 accountBorrowPointsOld = accountBorrowPoints[borrowCurrent.owner];
        accountBorrowPoints[borrowCurrent.owner] = accountBorrowPoints[borrowCurrent.owner].add(addPoint);

        if(compActionPool != address(0) && addPoint > 0) {
            IActionPools(compActionPool).onAcionIn(CTOKEN_BORROW, borrowCurrent.owner,
                    accountBorrowPointsOld, accountBorrowPoints[borrowCurrent.owner]);
        }
        return ;
    }

    function repay(uint256 _bid, uint256 _value) external virtual override {
        update();
        _repay(_bid, _value);
    }

    function _repay(uint256 _bid, uint256 _value) internal {
        BorrowInfo storage borrowCurrent = borrowInfo[_bid];

        uint256 removedPoints;
        if(_value >= pendingBorrowRewards(_bid).add(borrowCurrent.amount)) {
            removedPoints = borrowCurrent.bPoints;
        }else{
            removedPoints = _value.mul(borrowTotalPoints).div(borrowTotalAmountWithPlatform);
            removedPoints = TenMath.min(removedPoints, borrowCurrent.bPoints);
        }

        // booking
        uint256 userAmount = removedPoints.mul(borrowCurrent.amount).div(borrowCurrent.bPoints); // to reduce amount for booking
        uint256 repayAmount = removedPoints.mul(borrowTotalAmount).div(borrowTotalPoints); // to repay = amount + interest
        uint256 platformAmount = TenMath.safeSub(removedPoints.mul(borrowTotalAmountWithPlatform).div(borrowTotalPoints),
                                 repayAmount);  // platform interest
    
        borrowCurrent.bPoints = TenMath.safeSub(borrowCurrent.bPoints, removedPoints);
        borrowTotalPoints = TenMath.safeSub(borrowTotalPoints, removedPoints);
        borrowTotalAmountWithPlatform = TenMath.safeSub(borrowTotalAmountWithPlatform, repayAmount.add(platformAmount));
        lastBorrowCurrent = call_borrowBalanceCurrent_this();

        borrowCurrent.amount = TenMath.safeSub(borrowCurrent.amount, userAmount);
        borrowTotal = TenMath.safeSub(borrowTotal, userAmount);
        borrowTotalAmount = TenMath.safeSub(borrowTotalAmount, repayAmount);
        
        // platform interest will buyback
        if(platformAmount > 0 && iBuyback != address(0)) {
            IERC20(token).approve(iBuyback, platformAmount);
            IBuyback(iBuyback).buyback(token, platformAmount);
        }

        // repay borrow
        repayAmount = TenMath.min(repayAmount, lastBorrowCurrent);

        ctokenRepayBorrow(repayAmount);
        lastBorrowCurrent = call_borrowBalanceCurrent_this();

        // return of the rest
        tokenSafeTransfer(token, msg.sender);

        // notify for action pool
        uint256 accountBorrowPointsOld = accountBorrowPoints[borrowCurrent.owner];
        accountBorrowPoints[borrowCurrent.owner] = TenMath.safeSub(accountBorrowPoints[borrowCurrent.owner], removedPoints);

        if(compActionPool != address(0) && removedPoints > 0) {
            IActionPools(compActionPool).onAcionOut(CTOKEN_BORROW, borrowCurrent.owner,
                    accountBorrowPointsOld, accountBorrowPoints[borrowCurrent.owner]);
        }
        return ;
    }

    function emergencyWithdraw() external virtual override nonReentrant {
        require(emergencyWithdrawEnabled, 'not in emergency');

        uint256 withdrawAmount = call_balanceOf(address(this), msg.sender);
        _burn(msg.sender, withdrawAmount);

        if(accDebtPerSupply > 0) {
            // If platform loss, the loss will be shared by supply
            uint256 debtAmount = withdrawAmount.mul(accDebtPerSupply).div(1e18);
            require(withdrawAmount >= debtAmount, 'debt too much');
            withdrawAmount = withdrawAmount.sub(debtAmount);
        }

        // withdraw ctoken
        ctokenWithdraw(withdrawAmount);

        tokenSafeTransfer(address(token), msg.sender);
    }

    function emergencyRepay(uint256 _bid) external virtual override nonReentrant {
        require(emergencyRepayEnabled, 'not in emergency');
        // in emergency mode , only repay loan
        BorrowInfo storage borrowCurrent = borrowInfo[_bid];

        uint256 repayAmount = borrowCurrent.amount;

        IERC20(baseToken()).safeTransferFrom(msg.sender, address(this), repayAmount);
        ctokenRepayBorrow(repayAmount);

        uint256 accountBorrowPointsOld = accountBorrowPoints[borrowCurrent.owner];
        accountBorrowPoints[borrowCurrent.owner] = TenMath.safeSub(accountBorrowPoints[borrowCurrent.owner], borrowCurrent.bPoints);

        // booking
        borrowTotal = TenMath.safeSub(borrowTotal, repayAmount);
        borrowTotalPoints = TenMath.safeSub(borrowTotalPoints, borrowCurrent.bPoints);
        borrowTotalAmount = TenMath.safeSub(borrowTotalAmount, repayAmount);
        borrowTotalAmountWithPlatform = TenMath.safeSub(borrowTotalAmountWithPlatform, repayAmount);
        borrowCurrent.amount = 0;
        borrowCurrent.bPoints = 0;
        lastBorrowCurrent = call_borrowBalanceCurrent_this();
    }

    function update() public virtual override {
        _update();
    }

    function _update() internal {
        // update borrow interest
        uint256 lastBorrowCurrentNow = call_borrowBalanceCurrent_this();
        if(lastBorrowCurrentNow != lastBorrowCurrent && borrowTotal > 0) {
            if(lastBorrowCurrentNow >= lastBorrowCurrent) {
                // booking
                uint256 newDebtAmount1 = lastBorrowCurrentNow.sub(lastBorrowCurrent);
                uint256 newDebtAmount2 = newDebtAmount1.mul(getBorrowFactor()).div(1e9);
                borrowTotalAmount = borrowTotalAmount.add(newDebtAmount1);
                borrowTotalAmountWithPlatform = borrowTotalAmountWithPlatform.add(newDebtAmount2);
            }
            lastBorrowCurrent = lastBorrowCurrentNow;
        }

        // manage ctoken amount
        uint256 uCTokenTotalAmount = call_balanceOfCToken_this();
        if(uCTokenTotalAmount >= totalSupply()) {
            // The platform has no debt
            accDebtPerSupply = 0;
        }
        if(totalSupply() > 0 && accDebtPerSupply > 0) {
            // The platform has debt, uCTokenTotalAmount will be totalSupply()
            uCTokenTotalAmount = uCTokenTotalAmount.add(accDebtPerSupply.mul(totalSupply()).div(1e18));
        }
        if(uCTokenTotalAmount < totalSupply()) {
            // totalSupply() != 0  new debt divided equally
            accDebtPerSupply = accDebtPerSupply.add(totalSupply().sub(uCTokenTotalAmount).mul(1e18).div(totalSupply()));
        } else if(uCTokenTotalAmount > totalSupply() && accDebtPerSupply > 0) {
            // reduce debt divided equally
            uint256 accDebtReduce = uCTokenTotalAmount.sub(totalSupply()).mul(1e18).div(totalSupply());
            accDebtReduce = TenMath.min(accDebtReduce, accDebtPerSupply);
            accDebtPerSupply = accDebtPerSupply.sub(accDebtReduce);
        }

        if(compActionPool != address(0)) {
            IActionPools(compActionPool).onAcionUpdate(CTOKEN_BORROW);
        }
    }

    function mintDonate(uint256 _value) public virtual override nonReentrant {
        IERC20(token).safeTransferFrom(msg.sender, address(this), _value);
        ctokenDeposit(_value);
        update();
    }

    function tokenSafeTransfer(address _token, address _to) internal {
        uint256 value = IERC20(_token).balanceOf(address(this));
        if(value > 0) {
            IERC20(_token).transfer(_to, value);
        }
    }
}

pragma solidity 0.6.12;




// Distribution of FILDA token
contract SafeBoxFilDa is SafeBoxCToken {
    using SafeMath for uint256;
    using SafeERC20 for IERC20;

    IFilDaPool public constant ipools = IFilDaPool(0xb74633f2022452f377403B638167b0A135DB096d);
    IERC20 public constant FILDA_TOKEN = IERC20(0xE36FFD17B2661EB57144cEaEf942D95295E637F0);

    uint256 public lastFildaTokenBlock;        // fileda update
    
    address public actionPoolFilda;             // address for action pool
    uint256 public poolDepositId;               // poolid of depositor s filda token rewards in action pool, the action pool relate boopool deposit
    uint256 public poolBorrowId;                // poolid of borrower s filda token rewards in action pool 

    uint256 public constant FILDA_DEPOSIT_CALLID = 16;      // depositinfo callid for action callback
    uint256 public constant FILDA_BORROW_CALLID = 18;       // borrowinfo callid for comp action callback

    event SetFildaDepositPool(address _actionPoolFilda, uint256 _piddeposit);
    event SetFildaBorrowPool(address _compActionPool, uint256 _pidborrow);

    constructor (
        address _bank,
        address _cToken
    ) public SafeBoxCToken(_bank, _cToken) {
    }

    function update() public virtual override {
        _update();
        updatetoken();
    }

    // mint filda for supplies to action pools
    function setFildaDepositPool(address _actionPoolFilda, uint256 _piddeposit) public onlyOwner {
        actionPoolFilda = _actionPoolFilda;
        poolDepositId = _piddeposit;
        emit SetFildaDepositPool(_actionPoolFilda, _piddeposit);
    }

    // mint filda for borrows to comp action pools
    function setFildaBorrowPool(uint256 _pidborrow) public onlyOwner {
        checkFildaPool(compActionPool, _pidborrow, FILDA_BORROW_CALLID);
        poolBorrowId = _pidborrow;
        emit SetFildaBorrowPool(compActionPool, _pidborrow);
    }

    function checkFildaPool(address _fildaPool, uint256 _pid, uint256 _fildacallid) internal view {
        (address callFrom, uint256 callId, address rewardToken)
            = IActionPools(_fildaPool).getPoolInfo(_pid);
        require(callFrom == address(this), 'call from error');
        require(callId == _fildacallid, 'callid error');
        require(rewardToken == address(FILDA_TOKEN), 'rewardToken error');
    }

    function deposit(uint256 _value) external virtual override nonReentrant {
        update();
        IERC20(token).safeTransferFrom(msg.sender, address(this), _value);
        _deposit(msg.sender, _value);
    }

    function withdraw(uint256 _tTokenAmount) external virtual override nonReentrant {
        update();
        _withdraw(msg.sender, _tTokenAmount);
    }
    
    function borrow(uint256 _bid, uint256 _value, address _to) external virtual override onlyBank {
        update();
        address owner = borrowInfo[_bid].owner;
        uint256 accountBorrowPointsOld = accountBorrowPoints[owner];
        _borrow(_bid, _value, _to);

        if(compActionPool != address(0) && _value > 0) {
            IActionPools(compActionPool).onAcionIn(FILDA_BORROW_CALLID, owner, 
                    accountBorrowPointsOld, accountBorrowPoints[owner]);
        }
    }

    function repay(uint256 _bid, uint256 _value) external virtual override {
        update();
        address owner = borrowInfo[_bid].owner;
        uint256 accountBorrowPointsOld = accountBorrowPoints[owner];
        _repay(_bid, _value);

        if(compActionPool != address(0) && _value > 0) {
            IActionPools(compActionPool).onAcionOut(FILDA_BORROW_CALLID, owner, 
                    accountBorrowPointsOld, accountBorrowPoints[owner]);
        }
    }

    function updatetoken() public {
        if(lastFildaTokenBlock == block.number) {
            return ;
        }
        lastFildaTokenBlock = block.number;
        
        // FILDA pools
        address[] memory holders = new address[](1);
        holders[0] = address(this);
        address[] memory cTokens = new address[](1);
        cTokens[0] = address(cToken);

        uint256 uBalanceBefore;
        uint256 uBalanceAfter;

        // rewards for borrow, mint for comp action pool
        if(borrowTotalAmountWithPlatform > 0 && compActionPool != address(0)) {
            uBalanceBefore = FILDA_TOKEN.balanceOf(address(this));
            ipools.claimComp(holders, cTokens, true, false);
            uBalanceAfter = FILDA_TOKEN.balanceOf(address(this));
            uint256 borrowerRewards = uBalanceAfter.sub(uBalanceBefore);
            FILDA_TOKEN.transfer(compActionPool, borrowerRewards);
            IActionPools(compActionPool).mintRewards(poolBorrowId);
        }

        // rewards for supply, mint for action pool
        if(totalSupply() > 0 && actionPoolFilda != address(0)) {
            uBalanceBefore = FILDA_TOKEN.balanceOf(address(this));
            ipools.claimComp(holders, cTokens, false, true);
            uBalanceAfter = FILDA_TOKEN.balanceOf(address(this));
            uint256 supplyerRewards = uBalanceAfter.sub(uBalanceBefore);
            FILDA_TOKEN.transfer(actionPoolFilda, supplyerRewards);
            IActionPools(actionPoolFilda).mintRewards(poolDepositId);
        }
    }

    function claim(uint256 _value) external virtual override nonReentrant {
        update();
        _claim(msg.sender, _value);
    }
}
