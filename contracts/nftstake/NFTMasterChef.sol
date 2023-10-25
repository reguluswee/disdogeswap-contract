// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts (last updated v4.5.0) (utils/Address.sol)

pragma solidity ^0.8.12;

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
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.

        return account.code.length > 0;
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

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
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
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
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
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return verifyCallResult(success, returndata, errorMessage);
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
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResult(success, returndata, errorMessage);
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
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verifies that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

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


// OpenZeppelin Contracts v4.4.1 (utils/introspection/IERC165.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC165 standard, as defined in the
 * https://eips.ethereum.org/EIPS/eip-165[EIP].
 *
 * Implementers can declare support of contract interfaces, which can then be
 * queried by others ({ERC165Checker}).
 *
 * For an implementation, see {ERC165}.
 */
interface IERC165 {
    /**
     * @dev Returns true if this contract implements the interface defined by
     * `interfaceId`. See the corresponding
     * https://eips.ethereum.org/EIPS/eip-165#how-interfaces-are-identified[EIP section]
     * to learn more about how these ids are created.
     *
     * This function call must use less than 30 000 gas.
     */
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

// OpenZeppelin Contracts (last updated v4.6.0) (token/ERC20/IERC20.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
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

    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

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
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);
}

// OpenZeppelin Contracts (last updated v4.6.0) (interfaces/IERC2981.sol)

pragma solidity ^0.8.0;



/**
 * @dev Interface for the NFT Royalty Standard.
 *
 * A standardized way to retrieve royalty payment information for non-fungible tokens (NFTs) to enable universal
 * support for royalty payments across all NFT marketplaces and ecosystem participants.
 *
 * _Available since v4.5._
 */
interface IERC2981 is IERC165 {
    /**
     * @dev Returns how much royalty is owed and to whom, based on a sale price that may be denominated in any unit of
     * exchange. The royalty amount is denominated and should be paid in that same unit of exchange.
     */
    function royaltyInfo(uint256 tokenId, uint256 salePrice)
        external
        view
        returns (address receiver, uint256 royaltyAmount);
}


// OpenZeppelin Contracts (last updated v4.6.0) (token/ERC721/IERC721.sol)

pragma solidity ^0.8.0;


/**
 * @dev Required interface of an ERC721 compliant contract.
 */
interface IERC721 is IERC165 {
    /**
     * @dev Emitted when `tokenId` token is transferred from `from` to `to`.
     */
    event Transfer(address indexed from, address indexed to, uint256 indexed tokenId);

    /**
     * @dev Emitted when `owner` enables `approved` to manage the `tokenId` token.
     */
    event Approval(address indexed owner, address indexed approved, uint256 indexed tokenId);

    /**
     * @dev Emitted when `owner` enables or disables (`approved`) `operator` to manage all of its assets.
     */
    event ApprovalForAll(address indexed owner, address indexed operator, bool approved);

    /**
     * @dev Returns the number of tokens in ``owner``'s account.
     */
    function balanceOf(address owner) external view returns (uint256 balance);

    /**
     * @dev Returns the owner of the `tokenId` token.
     *
     * Requirements:
     *
     * - `tokenId` must exist.
     */
    function ownerOf(uint256 tokenId) external view returns (address owner);

    /**
     * @dev Safely transfers `tokenId` token from `from` to `to`.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `tokenId` token must exist and be owned by `from`.
     * - If the caller is not `from`, it must be approved to move this token by either {approve} or {setApprovalForAll}.
     * - If `to` refers to a smart contract, it must implement {IERC721Receiver-onERC721Received}, which is called upon a safe transfer.
     *
     * Emits a {Transfer} event.
     */
    function safeTransferFrom(
        address from,
        address to,
        uint256 tokenId,
        bytes calldata data
    ) external;

    /**
     * @dev Safely transfers `tokenId` token from `from` to `to`, checking first that contract recipients
     * are aware of the ERC721 protocol to prevent tokens from being forever locked.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `tokenId` token must exist and be owned by `from`.
     * - If the caller is not `from`, it must be have been allowed to move this token by either {approve} or {setApprovalForAll}.
     * - If `to` refers to a smart contract, it must implement {IERC721Receiver-onERC721Received}, which is called upon a safe transfer.
     *
     * Emits a {Transfer} event.
     */
    function safeTransferFrom(
        address from,
        address to,
        uint256 tokenId
    ) external;

    /**
     * @dev Transfers `tokenId` token from `from` to `to`.
     *
     * WARNING: Usage of this method is discouraged, use {safeTransferFrom} whenever possible.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `tokenId` token must be owned by `from`.
     * - If the caller is not `from`, it must be approved to move this token by either {approve} or {setApprovalForAll}.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 tokenId
    ) external;

    /**
     * @dev Gives permission to `to` to transfer `tokenId` token to another account.
     * The approval is cleared when the token is transferred.
     *
     * Only a single account can be approved at a time, so approving the zero address clears previous approvals.
     *
     * Requirements:
     *
     * - The caller must own the token or be an approved operator.
     * - `tokenId` must exist.
     *
     * Emits an {Approval} event.
     */
    function approve(address to, uint256 tokenId) external;

    /**
     * @dev Approve or remove `operator` as an operator for the caller.
     * Operators can call {transferFrom} or {safeTransferFrom} for any token owned by the caller.
     *
     * Requirements:
     *
     * - The `operator` cannot be the caller.
     *
     * Emits an {ApprovalForAll} event.
     */
    function setApprovalForAll(address operator, bool _approved) external;

    /**
     * @dev Returns the account approved for `tokenId` token.
     *
     * Requirements:
     *
     * - `tokenId` must exist.
     */
    function getApproved(uint256 tokenId) external view returns (address operator);

    /**
     * @dev Returns if the `operator` is allowed to manage all of the assets of `owner`.
     *
     * See {setApprovalForAll}
     */
    function isApprovedForAll(address owner, address operator) external view returns (bool);
}

// OpenZeppelin Contracts (last updated v4.5.0) (token/ERC721/extensions/IERC721Enumerable.sol)

pragma solidity ^0.8.0;



/**
 * @title ERC-721 Non-Fungible Token Standard, optional enumeration extension
 * @dev See https://eips.ethereum.org/EIPS/eip-721
 */
interface IERC721Enumerable is IERC721 {
    /**
     * @dev Returns the total amount of tokens stored by the contract.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns a token ID owned by `owner` at a given `index` of its token list.
     * Use along with {balanceOf} to enumerate all of ``owner``'s tokens.
     */
    function tokenOfOwnerByIndex(address owner, uint256 index) external view returns (uint256);

    /**
     * @dev Returns a token ID at a given `index` of all the tokens stored by the contract.
     * Use along with {totalSupply} to enumerate all tokens.
     */
    function tokenByIndex(uint256 index) external view returns (uint256);
}

// OpenZeppelin Contracts v4.4.1 (token/ERC721/extensions/IERC721Metadata.sol)

pragma solidity ^0.8.0;



/**
 * @title ERC-721 Non-Fungible Token Standard, optional metadata extension
 * @dev See https://eips.ethereum.org/EIPS/eip-721
 */
interface IERC721Metadata is IERC721 {
    /**
     * @dev Returns the token collection name.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the token collection symbol.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the Uniform Resource Identifier (URI) for `tokenId` token.
     */
    function tokenURI(uint256 tokenId) external view returns (string memory);
}

// OpenZeppelin Contracts (last updated v4.6.0) (token/ERC721/IERC721Receiver.sol)

pragma solidity ^0.8.0;

/**
 * @title ERC721 token receiver interface
 * @dev Interface for any contract that wants to support safeTransfers
 * from ERC721 asset contracts.
 */
interface IERC721Receiver {
    /**
     * @dev Whenever an {IERC721} `tokenId` token is transferred to this contract via {IERC721-safeTransferFrom}
     * by `operator` from `from`, this function is called.
     *
     * It must return its Solidity selector to confirm the token transfer.
     * If any other value is returned or the interface is not implemented by the recipient, the transfer will be reverted.
     *
     * The selector can be obtained in Solidity with `IERC721Receiver.onERC721Received.selector`.
     */
    function onERC721Received(
        address operator,
        address from,
        uint256 tokenId,
        bytes calldata data
    ) external returns (bytes4);
}

// StarBlock DAO Contracts

pragma solidity ^0.8.0;

library ArrayUtils {
    function hasDuplicate(uint256[] memory self) external pure returns(bool) {
        uint256 ivalue;
        uint256 jvalue;
        for(uint256 i = 0; i < self.length - 1; i ++){
            ivalue = self[i];
            for(uint256 j = i + 1; j < self.length; j ++){
                jvalue = self[j];
                if(ivalue == jvalue){
                    return true;
                }
            }
        }
        return false;
    }
}

// OpenZeppelin Contracts v4.4.1 (utils/Context.sol)

pragma solidity ^0.8.0;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

// OpenZeppelin Contracts v4.4.1 (utils/introspection/ERC165.sol)

pragma solidity ^0.8.0;



/**
 * @dev Implementation of the {IERC165} interface.
 *
 * Contracts that want to implement ERC165 should inherit from this contract and override {supportsInterface} to check
 * for the additional interface id that will be supported. For example:
 *
 * ```solidity
 * function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
 *     return interfaceId == type(MyInterface).interfaceId || super.supportsInterface(interfaceId);
 * }
 * ```
 *
 * Alternatively, {ERC165Storage} provides an easier to use but more expensive implementation.
 */
abstract contract ERC165 is IERC165 {
    /**
     * @dev See {IERC165-supportsInterface}.
     */
    function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
        return interfaceId == type(IERC165).interfaceId;
    }
}

// OpenZeppelin Contracts v4.4.1 (access/Ownable.sol)

pragma solidity ^0.8.0;


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
    constructor() {
        _transferOwnership(_msgSender());
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
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

// OpenZeppelin Contracts v4.4.1 (security/ReentrancyGuard.sol)

pragma solidity ^0.8.0;

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

    constructor() {
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
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

// OpenZeppelin Contracts v4.4.1 (token/ERC20/utils/SafeERC20.sol)

pragma solidity ^0.8.0;


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
    using Address for address;

    function safeTransfer(
        IERC20 token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender) + value;
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        unchecked {
            uint256 oldAllowance = token.allowance(address(this), spender);
            require(oldAllowance >= value, "SafeERC20: decreased allowance below zero");
            uint256 newAllowance = oldAllowance - value;
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
        }
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
        if (returndata.length > 0) {
            // Return data is optional
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}

// OpenZeppelin Contracts (last updated v4.6.0) (utils/math/SafeMath.sol)

pragma solidity ^0.8.0;

// CAUTION
// This version of SafeMath should only be used with Solidity 0.8 or later,
// because it relies on the compiler's built in overflow checks.

/**
 * @dev Wrappers over Solidity's arithmetic operations.
 *
 * NOTE: `SafeMath` is generally not needed starting with Solidity 0.8, since the compiler
 * now has built in overflow checking.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryAdd(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            uint256 c = a + b;
            if (c < a) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function trySub(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b > a) return (false, 0);
            return (true, a - b);
        }
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryMul(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
            // benefit is lost if 'b' is also tested.
            // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
            if (a == 0) return (true, 0);
            uint256 c = a * b;
            if (c / a != b) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the division of two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryDiv(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a / b);
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryMod(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a % b);
        }
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
        return a + b;
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
        return a * b;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator.
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
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
    function sub(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b <= a, errorMessage);
            return a - b;
        }
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting with custom message on
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
    function div(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a / b;
        }
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
    function mod(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a % b;
        }
    }
}

// OpenZeppelin Contracts v4.4.1 (utils/Strings.sol)

pragma solidity ^0.8.0;

/**
 * @dev String operations.
 */
library Strings {
    bytes16 private constant _HEX_SYMBOLS = "0123456789abcdef";

    /**
     * @dev Converts a `uint256` to its ASCII `string` decimal representation.
     */
    function toString(uint256 value) internal pure returns (string memory) {
        // Inspired by OraclizeAPI's implementation - MIT licence
        // https://github.com/oraclize/ethereum-api/blob/b42146b063c7d6ee1358846c198246239e9360e8/oraclizeAPI_0.4.25.sol

        if (value == 0) {
            return "0";
        }
        uint256 temp = value;
        uint256 digits;
        while (temp != 0) {
            digits++;
            temp /= 10;
        }
        bytes memory buffer = new bytes(digits);
        while (value != 0) {
            digits -= 1;
            buffer[digits] = bytes1(uint8(48 + uint256(value % 10)));
            value /= 10;
        }
        return string(buffer);
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation.
     */
    function toHexString(uint256 value) internal pure returns (string memory) {
        if (value == 0) {
            return "0x00";
        }
        uint256 temp = value;
        uint256 length = 0;
        while (temp != 0) {
            length++;
            temp >>= 8;
        }
        return toHexString(value, length);
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation with fixed length.
     */
    function toHexString(uint256 value, uint256 length) internal pure returns (string memory) {
        bytes memory buffer = new bytes(2 * length + 2);
        buffer[0] = "0";
        buffer[1] = "x";
        for (uint256 i = 2 * length + 1; i > 1; --i) {
            buffer[i] = _HEX_SYMBOLS[value & 0xf];
            value >>= 4;
        }
        require(value == 0, "Strings: hex length insufficient");
        return string(buffer);
    }
}

// StarBlock DAO Contracts

pragma solidity ^0.8.0;



interface IERC2981Mutable is IERC165, IERC2981 {
    function setDefaultRoyalty(address _receiver, uint96 _feeNumerator) external;
    function deleteDefaultRoyalty() external;
}

interface IBaseWrappedNFT is IERC165, IERC2981Mutable, IERC721Receiver, IERC721, IERC721Metadata {
    event DelegatorChanged(address _delegator);
    event Deposit(address _forUser, uint256[] _tokenIds);
    event Withdraw(address _forUser, uint256[] _wnftTokenIds);

    function nft() external view returns (IERC721Metadata);
    function factory() external view returns (IWrappedNFTFactory);

    function deposit(address _forUser, uint256[] memory _tokenIds) external;
    function withdraw(address _forUser, uint256[] memory _wnftTokenIds) external;

    function exists(uint256 _tokenId) external view returns (bool);
    
    function delegator() external view returns (address);
    function setDelegator(address _delegator) external;
    
    function isEnumerable() external view returns (bool);
}

interface IWrappedNFT is IBaseWrappedNFT {
    function totalSupply() external view returns (uint256);
}

interface IWrappedNFTEnumerable is IWrappedNFT, IERC721Enumerable {
    function totalSupply() external view override(IWrappedNFT, IERC721Enumerable) returns (uint256);
}

interface IWrappedNFTFactory {
    event WrappedNFTDeployed(IERC721Metadata _nft, IWrappedNFT _wnft, bool _isEnumerable);
    event WNFTDelegatorChanged(address _wnftDelegator);

    function wnftDelegator() external view returns (address);

    function deployWrappedNFT(IERC721Metadata _nft, bool _isEnumerable) external returns (IWrappedNFT);
    function wnfts(IERC721Metadata _nft) external view returns (IWrappedNFT);
    function wnftsNumber() external view returns (uint);
}

// StarBlock DAO Contracts

pragma solidity ^0.8.0;



// harvest strategy contract, for havesting permission
interface IHarvestStrategy {
    function canHarvest(uint256 _pid, address _forUser, uint256[] memory _wnfTokenIds) external view returns (bool);
}

interface INFTMasterChef {
    event AddPoolInfo(IERC721Metadata nft, IWrappedNFT wnft, uint256 startBlock, 
                    RewardInfo[] rewards, uint256 depositFee, IERC20 dividendToken, bool withUpdate);
    event SetStartBlock(uint256 pid, uint256 startBlock);
    event UpdatePoolReward(uint256 pid, uint256 rewardIndex, uint256 rewardBlock, uint256 rewardForEachBlock, uint256 rewardPerNFTForEachBlock);
    event SetPoolDepositFee(uint256 pid, uint256 depositFee);
    event SetHarvestStrategy(IHarvestStrategy harvestStrategy);
    event SetPoolDividendToken(uint256 pid, IERC20 dividendToken);

    event AddTokenRewardForPool(uint256 pid, uint256 addTokenPerPool, uint256 addTokenPerBlock, bool withTokenTransfer);
    event AddDividendForPool(uint256 pid, uint256 addDividend);

    event UpdateDevAddress(address payable devAddress);
    event EmergencyStop(address user, address to);
    event ClosePool(uint256 pid, address payable to);

    event Deposit(address indexed user, uint256 indexed pid, uint256[] tokenIds);
    event Withdraw(address indexed user, uint256 indexed pid, uint256[] wnfTokenIds);
    event WithdrawWithoutHarvest(address indexed user, uint256 indexed pid, uint256[] wnfTokenIds);
    event Harvest(address indexed user, uint256 indexed pid, uint256[] wnftTokenIds, 
                    uint256 mining, uint256 dividend);

    // Info of each NFT.
    struct NFTInfo {
        bool deposited;     // If the NFT is deposited.
        uint256 rewardDebt; // Reward debt.

        uint256 dividendDebt; // Dividend debt.
    }

    //Info of each Reward 
    struct RewardInfo {
        uint256 rewardBlock;
        uint256 rewardForEachBlock;    //Reward for each block, can only be set one with rewardPerNFTForEachBlock
        uint256 rewardPerNFTForEachBlock;    //Reward for each block for every NFT, can only be set one with rewardForEachBlock
    }

    // Info of each pool.
    struct PoolInfo {
        IWrappedNFT wnft;// Address of wnft contract.

        uint256 startBlock; // Reward start block.

        uint256 currentRewardIndex;// the current reward phase index for poolsRewardInfos
        uint256 currentRewardEndBlock;  // the current reward end block.

        uint256 amount;     // How many NFTs the pool has.
        
        uint256 lastRewardBlock;  // Last block number that token distribution occurs.
        uint256 accTokenPerShare; // Accumulated tokens per share, times 1e12.
        
        IERC20 dividendToken;
        uint256 accDividendPerShare; // Accumulated dividend per share, times 1e12.
        
        uint256 depositFee;// ETH charged when user deposit.
    }
    
    function poolLength() external view returns (uint256);
    function poolRewardLength(uint256 _pid) external view returns (uint256);

    function poolInfos(uint256 _pid) external view returns (IWrappedNFT _wnft, 
                uint256 _startBlock, uint256 _currentRewardIndex, uint256 _currentRewardEndBlock, uint256 _amount, uint256 _lastRewardBlock, 
                uint256 _accTokenPerShare, IERC20 _dividendToken, uint256 _accDividendPerShare, uint256 _depositFee);
    function poolsRewardInfos(uint256 _pid, uint256 _rewardInfoId) external view returns (uint256 _rewardBlock, uint256 _rewardForEachBlock, uint256 _rewardPerNFTForEachBlock);
    function poolNFTInfos(uint256 _pid, uint256 _nftTokenId) external view returns (bool _deposited, uint256 _rewardDebt, uint256 _dividendDebt);

    function getPoolCurrentReward(uint256 _pid) external view returns (RewardInfo memory _rewardInfo, uint256 _currentRewardIndex);
    function getPoolEndBlock(uint256 _pid) external view returns (uint256 _poolEndBlock);
    function isPoolEnd(uint256 _pid) external view returns (bool);

    function pending(uint256 _pid, uint256[] memory _wnftTokenIds) external view returns (uint256 _mining, uint256 _dividend);
    function deposit(uint256 _pid, uint256[] memory _tokenIds) external payable;
    function withdraw(uint256 _pid, uint256[] memory _wnftTokenIds) external;
    function withdrawWithoutHarvest(uint256 _pid, uint256[] memory _wnftTokenIds) external;
    function harvest(uint256 _pid, address _forUser, uint256[] memory _wnftTokenIds) external returns (uint256 _mining, uint256 _dividend);
}

contract NFTMasterChef is INFTMasterChef, Ownable, ReentrancyGuard {
    using SafeMath for uint256;
    using SafeERC20 for IERC20;
    using ArrayUtils for uint256[];

    uint256 private constant ACC_TOKEN_PRECISION = 1e12;

    IWrappedNFTFactory public immutable wnftFactory;
    IERC20 public immutable token;// The reward TOKEN!
    
    IHarvestStrategy public harvestStrategy;

    address payable public devAddress;

    PoolInfo[] public poolInfos;// Info of each pool.
    RewardInfo[][] public poolsRewardInfos;
    mapping (uint256 => NFTInfo)[] public poolNFTInfos;// the nftInfo for pool

    modifier validatePoolByPid(uint256 _pid) {
        require(_pid < poolInfos.length, "NFTMasterChef: Pool does not exist");
        _;
    }

    constructor(
        IWrappedNFTFactory _wnftFactory,
        IERC20 _token,
        address payable _devAddress
    )  {
        require(address(_wnftFactory) != address(0) && address(_token) != address(0) 
                && address(_devAddress) != address(0), "NFTMasterChef: invalid parameters!");
        wnftFactory = _wnftFactory;
        token = _token;
        devAddress = _devAddress;
    }

    function poolLength() external view returns (uint256) {
        return poolInfos.length;
    }

    function poolRewardLength(uint256 _pid) external view validatePoolByPid(_pid) returns (uint256) {
        return poolsRewardInfos[_pid].length;
    }

    // Add a new NFT to the pool. Can only be called by the owner.
    function addPoolInfo(IERC721Metadata _nft, uint256 _startBlock, RewardInfo[] memory _rewards, 
            uint256 _depositFee, IERC20 _dividendToken, bool _withUpdate) external onlyOwner nonReentrant {
        require(address(_nft) != address(0), "NFTMasterChef: wrong _nft or _dividendToken!");
        require(_rewards.length > 0, "NFTMasterChef: _rewards must be set!");
        uint256 rewardForEachBlock = _rewards[0].rewardForEachBlock;
        uint256 rewardPerNFTForEachBlock = _rewards[0].rewardPerNFTForEachBlock;
        //allow pool with dividend and without mining, or must have mining. Mining can only have either rewardForEachBlock or _rewardPerNFTForEachBlock set.
        require((address(_dividendToken) != address(0) && (rewardForEachBlock == 0 && rewardPerNFTForEachBlock == 0)) || 
                ((rewardForEachBlock == 0 && rewardPerNFTForEachBlock > 0) || (rewardForEachBlock > 0 && rewardPerNFTForEachBlock == 0)), 
                "NFTMasterChef: rewardForEachBlock or rewardPerNFTForEachBlock must be greater than zero!");
        IWrappedNFT wnft = wnftFactory.wnfts(_nft);
        require(address(wnft) != address(0) && wnft.nft() == _nft && wnft.factory() == wnftFactory && wnft.delegator() == address(this), "NFTMasterChef: wrong wnft!");
        if (_withUpdate) {
            massUpdatePools();
        }
        PoolInfo storage pool = poolInfos.push();
        pool.wnft = wnft;
        pool.amount = 0;
        pool.startBlock = block.number > _startBlock ? block.number : _startBlock;
        pool.lastRewardBlock = pool.startBlock;
        pool.accTokenPerShare = 0;
        pool.depositFee = _depositFee;

        pool.dividendToken = _dividendToken;
        pool.accDividendPerShare = 0;
        
        RewardInfo[] storage rewards = poolsRewardInfos.push();
        _setPoolRewards(poolInfos.length - 1, _rewards);
        pool.currentRewardEndBlock = pool.startBlock + rewards[0].rewardBlock; 

        poolNFTInfos.push();
        
        emit AddPoolInfo(_nft, wnft, _startBlock, _rewards, _depositFee, _dividendToken, _withUpdate);
    }

    function _setPoolRewards(uint256 _pid, RewardInfo[] memory _rewards) internal {
        RewardInfo[] storage rewards = poolsRewardInfos[_pid];
        bool rewardForEachBlockSet;
        if(_rewards.length > 0){
            rewardForEachBlockSet = _rewards[0].rewardForEachBlock > 0;
        }
        for (uint256 i = 0; i < _rewards.length; i++) {
            RewardInfo memory reward = _rewards[i];
            require(reward.rewardBlock > 0, "NFTMasterChef: rewardBlock error!");
            require(!(reward.rewardForEachBlock > 0 && reward.rewardPerNFTForEachBlock > 0), "NFTMasterChef: reward can only set one!");
            require((rewardForEachBlockSet && reward.rewardForEachBlock > 0) || (!rewardForEachBlockSet && reward.rewardPerNFTForEachBlock > 0)
                    || (reward.rewardForEachBlock == 0 && reward.rewardPerNFTForEachBlock == 0), "NFTMasterChef: setting error!");
            rewards.push(RewardInfo({
                rewardBlock: reward.rewardBlock,
                rewardForEachBlock: reward.rewardForEachBlock,
                rewardPerNFTForEachBlock: reward.rewardPerNFTForEachBlock
            }));
        }
    }

    // update the pool reward of specified index
    function updatePoolReward(uint256 _pid, uint256 _rewardIndex, uint256 _rewardBlock, uint256 _rewardForEachBlock, uint256 _rewardPerNFTForEachBlock) 
                            external validatePoolByPid(_pid) onlyOwner nonReentrant {
        PoolInfo storage pool = poolInfos[_pid];
        require(!isPoolEnd(_pid), "NFTMasterChef: pool is end!");
        require(_rewardBlock > 0, "NFTMasterChef: rewardBlock error!");
        require(_rewardIndex < poolsRewardInfos[_pid].length, "NFTMasterChef: _rewardIndex not exists!");
        (, uint256 _currentRewardIndex) = getPoolCurrentReward(_pid);
        require(_rewardIndex >= _currentRewardIndex, "NFTMasterChef: _rewardIndex error!");
        RewardInfo storage reward = poolsRewardInfos[_pid][_rewardIndex];
        require(_rewardBlock >= reward.rewardBlock, "NFTMasterChef: _rewardBlock error!");
        require(!(_rewardForEachBlock > 0 && _rewardPerNFTForEachBlock > 0), "NFTMasterChef: reward can only set one!");
        require((reward.rewardForEachBlock > 0 && _rewardForEachBlock > 0) || (reward.rewardPerNFTForEachBlock > 0 && _rewardPerNFTForEachBlock > 0) 
                || (_rewardForEachBlock == 0 && _rewardPerNFTForEachBlock == 0), "NFTMasterChef: invalid parameters!");
        updatePool(_pid);
        if(_rewardIndex == _currentRewardIndex){
            pool.currentRewardEndBlock = pool.currentRewardEndBlock + _rewardBlock - reward.rewardBlock;
        }
        reward.rewardBlock = _rewardBlock;
        reward.rewardForEachBlock = _rewardForEachBlock;
        reward.rewardPerNFTForEachBlock = _rewardPerNFTForEachBlock;
        
        emit UpdatePoolReward(_pid, _rewardIndex, _rewardBlock, _rewardForEachBlock, _rewardPerNFTForEachBlock);
    }

    // Update the given pool's pool info. Can only be called by the owner.
    function setStartBlock(uint256 _pid, uint256 _startBlock) external validatePoolByPid(_pid) onlyOwner nonReentrant {
        PoolInfo storage pool = poolInfos[_pid];
        require(block.number < pool.startBlock, "NFTMasterChef: can not change start block of started pool!");
        require(block.number < _startBlock, "NFTMasterChef: _startBlock must be less than block.number!");
        pool.startBlock = _startBlock;
        emit SetStartBlock(_pid, _startBlock);
    }

    function isPoolEnd(uint256 _pid) public view returns (bool) {
        uint256 poolEndBlock = getPoolEndBlock(_pid);
        return block.number > poolEndBlock;
    }

    function getPoolEndBlock(uint256 _pid) public view returns (uint256 _poolEndBlock) {
        PoolInfo storage pool = poolInfos[_pid];
        _poolEndBlock = pool.currentRewardEndBlock;
        RewardInfo[] storage rewards = poolsRewardInfos[_pid];
        for(uint256 index = pool.currentRewardIndex + 1; index < rewards.length; index ++){
            _poolEndBlock = _poolEndBlock.add(rewards[index].rewardBlock);
        }
    }

    function getPoolCurrentReward(uint256 _pid) public view returns (RewardInfo memory _rewardInfo, uint256 _currentRewardIndex){
        PoolInfo storage pool = poolInfos[_pid];
        _currentRewardIndex = pool.currentRewardIndex;
        uint256 poolCurrentRewardEndBlock = pool.currentRewardEndBlock;
        uint256 poolRewardNumber = poolsRewardInfos[_pid].length;
        _rewardInfo = poolsRewardInfos[_pid][_currentRewardIndex];
        // Check whether to adjust multipliers and reward per block
        while ((block.number > poolCurrentRewardEndBlock) && (_currentRewardIndex < (poolRewardNumber - 1))) {
            // Update rewards per block
            _currentRewardIndex ++;
            _rewardInfo = poolsRewardInfos[_pid][_currentRewardIndex];
            // Adjust the end block
            poolCurrentRewardEndBlock = poolCurrentRewardEndBlock.add(_rewardInfo.rewardBlock);
        }
    }

    // Update the given pool's pool info. Can only be called by the owner.
    function setPoolDividendToken(uint256 _pid, IERC20 _dividendToken) external validatePoolByPid(_pid) onlyOwner nonReentrant {
        PoolInfo storage pool = poolInfos[_pid];
        require(!isPoolEnd(_pid), "NFTMasterChef: pool is end!");
        require(address(pool.dividendToken) == address(0) || pool.accDividendPerShare == 0, "NFTMasterChef: dividendToken can not be modified!");
        pool.dividendToken = _dividendToken;
        emit SetPoolDividendToken(_pid, _dividendToken);
    }

    // Update the given pool's operation fee
    function setPoolDepositFee(uint256 _pid, uint256 _depositFee) public validatePoolByPid(_pid) onlyOwner nonReentrant {
        PoolInfo storage pool = poolInfos[_pid];
        require(!isPoolEnd(_pid), "NFTMasterChef: pool is end!");
        pool.depositFee = _depositFee;
        emit SetPoolDepositFee(_pid, _depositFee);
    }

    //harvestStrategy change be changed and can be zero.
    function setHarvestStrategy(IHarvestStrategy _harvestStrategy) external onlyOwner nonReentrant {
        harvestStrategy = _harvestStrategy;
        emit SetHarvestStrategy(_harvestStrategy);
    }

    // Return reward multiplier over the given _from to _to block.
    function getMultiplier(uint256 _from, uint256 _to) public pure returns (uint256) {
        if(_to > _from){
            return _to.sub(_from);
        }
        return 0;
    }

    function _getMultiplier(uint256 _lastRewardBlock, uint256 _currentRewardEndBlock) internal view returns (uint256 _multiplier) {
        if(block.number < _lastRewardBlock){
            return 0;
        }else if (block.number > _currentRewardEndBlock){
            _multiplier = getMultiplier(_lastRewardBlock, _currentRewardEndBlock);
        }else{
            _multiplier = getMultiplier(_lastRewardBlock, block.number);
        }
    }

    // Update reward variables of the given pool to be up-to-date.
    function updatePool(uint256 _pid) public validatePoolByPid(_pid) {
        PoolInfo storage pool = poolInfos[_pid];
        if (block.number <= pool.lastRewardBlock){
            return;
        }
        if (block.number < pool.startBlock){
            return;
        }
        if (pool.lastRewardBlock >= getPoolEndBlock(_pid)){
             return;
        }
        RewardInfo[] storage rewards = poolsRewardInfos[_pid];
        if(rewards.length == 0 || pool.currentRewardIndex > (rewards.length - 1)){
            return;
        }
        RewardInfo storage reward = rewards[pool.currentRewardIndex];
        if(reward.rewardForEachBlock == 0 && reward.rewardPerNFTForEachBlock == 0){// only dividend pool do not need update pool
            return;
        }
        if (pool.lastRewardBlock < pool.startBlock) {
            pool.lastRewardBlock = pool.startBlock;
        }
        if (pool.amount == 0) {
            pool.lastRewardBlock = block.number;
            // update current reward index
            while ((pool.lastRewardBlock > pool.currentRewardEndBlock) && (pool.currentRewardIndex < (poolsRewardInfos[_pid].length - 1))) {
                // Update rewards per block
                pool.currentRewardIndex ++;
                // Adjust the end block
                pool.currentRewardEndBlock = pool.currentRewardEndBlock.add(reward.rewardBlock);
            }
            return;
        }
        uint256 multiplier = _getMultiplier(pool.lastRewardBlock, pool.currentRewardEndBlock);
        uint256 rewardForEachBlock = reward.rewardForEachBlock;
        if(rewardForEachBlock == 0){
            rewardForEachBlock = pool.amount.mul(reward.rewardPerNFTForEachBlock);
        }
        uint256 poolReward = multiplier.mul(rewardForEachBlock);
        uint256 poolRewardNumber = poolsRewardInfos[_pid].length;
        // Check whether to adjust multipliers and reward per block
        while ((block.number > pool.currentRewardEndBlock) && (pool.currentRewardIndex < (poolRewardNumber - 1))) {
            // Update rewards per block
            pool.currentRewardIndex ++;
            
            uint256 previousEndBlock = pool.currentRewardEndBlock;
            
            reward = poolsRewardInfos[_pid][pool.currentRewardIndex];
            // Adjust the end block
            pool.currentRewardEndBlock = pool.currentRewardEndBlock.add(reward.rewardBlock);
            
            // Adjust multiplier to cover the missing periods with other lower inflation schedule
            uint256 newMultiplier = _getMultiplier(previousEndBlock, pool.currentRewardEndBlock);
            rewardForEachBlock = reward.rewardForEachBlock;
            if(rewardForEachBlock == 0){
                rewardForEachBlock = pool.amount.mul(reward.rewardPerNFTForEachBlock);
            }
            // Adjust token rewards
            poolReward = poolReward.add(newMultiplier.mul(rewardForEachBlock));
        }

        if (block.number > pool.currentRewardEndBlock){
            pool.lastRewardBlock = pool.currentRewardEndBlock;
        }else{
            pool.lastRewardBlock = block.number;
        }
        pool.accTokenPerShare = pool.accTokenPerShare.add(poolReward.mul(ACC_TOKEN_PRECISION).div(pool.amount));
    }

    // View function to see mining tokens and dividend on frontend.
    function pending(uint256 _pid, uint256[] memory _wnftTokenIds) public view validatePoolByPid(_pid) returns (uint256 _mining, uint256 _dividend) {
        _requireTokenIds(_wnftTokenIds);

        PoolInfo storage pool =  poolInfos[_pid];

        mapping(uint256 => NFTInfo) storage nfts = poolNFTInfos[_pid];
        RewardInfo[] storage rewards = poolsRewardInfos[_pid];
        RewardInfo storage reward = rewards[pool.currentRewardIndex];
        uint256 accTokenPerShare = pool.accTokenPerShare;
        uint256 rewardForEachBlock = reward.rewardForEachBlock;
        if(rewardForEachBlock == 0){
            rewardForEachBlock = pool.amount.mul(reward.rewardPerNFTForEachBlock);
        }
        if(rewardForEachBlock > 0){
            uint256 lastRewardBlock = pool.lastRewardBlock;
            if (lastRewardBlock < pool.startBlock) {
                lastRewardBlock = pool.startBlock;
            }
            if (block.number > lastRewardBlock && block.number >= pool.startBlock && pool.amount > 0){
                uint256 multiplier = _getMultiplier(lastRewardBlock, pool.currentRewardEndBlock);

                uint256 poolReward = multiplier.mul(rewardForEachBlock);
                uint256 poolRewardNumber = poolsRewardInfos[_pid].length;
                uint256 poolCurrentRewardIndex = pool.currentRewardIndex;
                uint256 poolEndBlock = pool.currentRewardEndBlock;
                // Check whether to adjust multipliers and reward per block
                while ((block.number > poolEndBlock) && (poolCurrentRewardIndex < (poolRewardNumber - 1))) {
                    // Update rewards per block
                    poolCurrentRewardIndex ++;

                    uint256 previousEndBlock = poolEndBlock;
                    
                    reward = rewards[poolCurrentRewardIndex];
                    // Adjust the end block
                    poolEndBlock = poolEndBlock.add(reward.rewardBlock);

                    // Adjust multiplier to cover the missing periods with other lower inflation schedule
                    uint256 newMultiplier = getMultiplier(previousEndBlock, poolEndBlock);
                    
                    rewardForEachBlock = reward.rewardForEachBlock;
                    if(rewardForEachBlock == 0){
                        rewardForEachBlock = pool.amount.mul(reward.rewardPerNFTForEachBlock);
                    }
                    // Adjust token rewards
                    poolReward = poolReward.add(newMultiplier.mul(rewardForEachBlock));
                }

                accTokenPerShare = accTokenPerShare.add(poolReward.mul(ACC_TOKEN_PRECISION).div(pool.amount));
            }
        }

        uint256 temp;
        NFTInfo storage nft;
        for(uint256 i = 0; i < _wnftTokenIds.length; i ++){
            uint256 wnftTokenId = _wnftTokenIds[i];
            nft = nfts[wnftTokenId];
            if(nft.deposited == true){
                temp = accTokenPerShare.div(ACC_TOKEN_PRECISION);
                _mining = _mining.add(temp.sub(nft.rewardDebt));

                if(pool.accDividendPerShare > 0 && address(pool.dividendToken) != address(0)){
                    _dividend = _dividend.add(pool.accDividendPerShare.div(ACC_TOKEN_PRECISION).sub(nft.dividendDebt));
                }
            }
        }
    }
   
    // Update reward vairables for all pools. Be careful of gas spending!
    function massUpdatePools() public {
        uint256 length = poolInfos.length;
        for (uint256 pid = 0; pid < length; ++pid) {
            updatePool(pid);
        }
    }

    // Deposit NFTs to MasterChef for token allocation, do not give user reward.
    function deposit(uint256 _pid, uint256[] memory _tokenIds) external validatePoolByPid(_pid) payable nonReentrant {
        _requireTokenIds(_tokenIds);
        updatePool(_pid);
        PoolInfo storage pool = poolInfos[_pid];
        require(block.number >= pool.startBlock, "NFTMasterChef: pool is not start!");
        require(!isPoolEnd(_pid), "NFTMasterChef: pool is end!");
        if(pool.depositFee > 0){// charge for fee
            require(msg.value == pool.depositFee, "NFTMasterChef: Fee is not enough or too much!");
            devAddress.transfer(pool.depositFee);
        }
        mapping(uint256 => NFTInfo) storage nfts = poolNFTInfos[_pid];
        uint256 tokenId;
        NFTInfo storage nft;
        uint256 depositNumber;
        for(uint256 i = 0; i < _tokenIds.length; i ++){
            tokenId = _tokenIds[i];
            //ownerOf will return error if tokenId does not exist.
            require(pool.wnft.nft().ownerOf(tokenId) == msg.sender, "NFTMasterChef: can not deposit nft not owned!");
            nft = nfts[tokenId];
            //If tokenId have reward not harvest, drop it.
            if(nft.deposited == false){
                depositNumber ++;
                nft.deposited = true;
            }
            nft.rewardDebt = pool.accTokenPerShare.div(ACC_TOKEN_PRECISION);
            nft.dividendDebt = pool.accDividendPerShare.div(ACC_TOKEN_PRECISION);
        }
        pool.wnft.deposit(msg.sender, _tokenIds);
        pool.amount = pool.amount.add(depositNumber);
        emit Deposit(msg.sender, _pid, _tokenIds);
    }

    // Withdraw NFTs from MasterChef.
    function withdraw(uint256 _pid, uint256[] memory _wnftTokenIds) external validatePoolByPid(_pid) nonReentrant {
        _harvest(_pid, msg.sender, _wnftTokenIds);
        _withdrawWithoutHarvest(_pid, _wnftTokenIds);
        emit Withdraw(msg.sender, _pid, _wnftTokenIds);
    }

    // Withdraw NFTs from MasterChef without reward
    function _withdrawWithoutHarvest(uint256 _pid, uint256[] memory _wnftTokenIds) internal validatePoolByPid(_pid) {
        _requireTokenIds(_wnftTokenIds);
        PoolInfo storage pool = poolInfos[_pid];
        mapping(uint256 => NFTInfo) storage nfts = poolNFTInfos[_pid];
        uint256 wnftTokenId;
        NFTInfo storage nft;
        uint256 withdrawNumber;
        for(uint256 i = 0; i < _wnftTokenIds.length; i ++){
            wnftTokenId = _wnftTokenIds[i];
            require(pool.wnft.ownerOf(wnftTokenId) == msg.sender, "NFTMasterChef: can not withdraw nft now owned!");
            nft = nfts[wnftTokenId];
            if(nft.deposited == true){
                withdrawNumber ++;
                nft.deposited = false;
            }
            nft.rewardDebt = 0;
            nft.dividendDebt = 0;
        }
        pool.wnft.withdraw(msg.sender, _wnftTokenIds);
        pool.amount = pool.amount.sub(withdrawNumber);
    }

    // Withdraw without caring about rewards. EMERGENCY ONLY.
    function withdrawWithoutHarvest(uint256 _pid, uint256[] memory _wnftTokenIds) external validatePoolByPid(_pid) nonReentrant {
        updatePool(_pid);
        _withdrawWithoutHarvest(_pid, _wnftTokenIds);
        emit WithdrawWithoutHarvest(msg.sender, _pid, _wnftTokenIds);
    }

    // Harvest the mining reward and dividend
    function harvest(uint256 _pid, address _forUser, uint256[] memory _wnftTokenIds) external validatePoolByPid(_pid) nonReentrant returns (uint256 _mining, uint256 _dividend) {
       return _harvest(_pid, _forUser, _wnftTokenIds);
    }

    function canHarvest(uint256 _pid, address _forUser, uint256[] memory _wnftTokenIds) public view validatePoolByPid(_pid) returns (bool) {
        if(address(harvestStrategy) != address(0)){
            return harvestStrategy.canHarvest(_pid, _forUser, _wnftTokenIds);
        }
        return true;
    }

    function _harvest(uint256 _pid, address _forUser, uint256[] memory _wnftTokenIds) internal validatePoolByPid(_pid) returns (uint256 _mining, uint256 _dividend) {
        _requireTokenIds(_wnftTokenIds);
        if(_forUser == address(0)){
            _forUser = msg.sender;
        }
        require(canHarvest(_pid, _forUser, _wnftTokenIds), "NFTMasterChef: can not harvest!");
        updatePool(_pid);
        PoolInfo storage pool =  poolInfos[_pid];
        mapping(uint256 => NFTInfo) storage nfts = poolNFTInfos[_pid];
        uint256 wnftTokenId;
        NFTInfo storage nft;
        uint256 temp = 0;
        for(uint256 i = 0; i < _wnftTokenIds.length; i ++){
            wnftTokenId = _wnftTokenIds[i];
            nft = nfts[wnftTokenId];
            require(pool.wnft.ownerOf(wnftTokenId) == _forUser, "NFTMasterChef: can not harvest nft now owned!");
            if(nft.deposited == true){
                temp = pool.accTokenPerShare.div(ACC_TOKEN_PRECISION);
                _mining = _mining.add(temp.sub(nft.rewardDebt));
                nft.rewardDebt = temp;

                if(pool.accDividendPerShare > 0 && address(pool.dividendToken) != address(0)){
                    temp = pool.accDividendPerShare.div(ACC_TOKEN_PRECISION);
                    _dividend = _dividend.add(temp.sub(nft.dividendDebt));
                    nft.dividendDebt = temp;
                }
            }
        }
        if (_mining > 0) {
            _safeTransferTokenFromThis(token, _forUser, _mining);
        }
        if(_dividend > 0){
            _safeTransferTokenFromThis(pool.dividendToken, _forUser, _dividend);
        }
        emit Harvest(_forUser, _pid, _wnftTokenIds, _mining, _dividend);
    }

    function emergencyStop(address payable _to) external onlyOwner nonReentrant {
        if(_to == address(0)){
            _to = payable(msg.sender);
        }
        uint256 addrBalance = token.balanceOf(address(this));
        if(addrBalance > 0){
            token.safeTransfer(_to, addrBalance);
        }
        uint256 length = poolInfos.length;
        for (uint256 pid = 0; pid < length; ++ pid) {
            closePool(pid, _to);

            PoolInfo storage pool = poolInfos[pid];
            if(pool.accDividendPerShare > 0 && address(pool.dividendToken) != address(0)){
                uint256 bal = pool.dividendToken.balanceOf(address(this));
                if(bal > 0){
                    pool.dividendToken.safeTransfer(_to, bal);
                }
            }
        }
        emit EmergencyStop(msg.sender, _to);
    }

    function closePool(uint256 _pid, address payable _to) public validatePoolByPid(_pid) onlyOwner {
        PoolInfo storage pool = poolInfos[_pid];
        if(isPoolEnd(_pid)){
            return;
        }
        if(poolsRewardInfos[_pid].length > 0){
            pool.currentRewardIndex = poolsRewardInfos[_pid].length - 1;
        }
        pool.currentRewardEndBlock = block.number;
        if(_to == address(0)){
            _to = payable(msg.sender);
        }
        emit ClosePool(_pid, _to);
    }

    function _safeTransferTokenFromThis(IERC20 _token, address _to, uint256 _amount) internal {
        uint256 bal = _token.balanceOf(address(this));
        if (_amount > bal) {
            _token.safeTransfer(_to, bal);
        } else {
            _token.safeTransfer(_to, _amount);
        }
    }

    // Update dev1 address by the previous dev.
    function updateDevAddress(address payable _devAddress) external nonReentrant {
        require(msg.sender == devAddress, "NFTMasterChef: dev: wut?");
        require(_devAddress != address(0), "NFTMasterChef: address can not be zero!");
        devAddress = _devAddress;
        emit UpdateDevAddress(_devAddress);
    }

    function addDividendForPool(uint256 _pid, uint256 _addDividend) external validatePoolByPid(_pid) onlyOwner nonReentrant {
        PoolInfo storage pool = poolInfos[_pid];
        require(_addDividend > 0, "NFTMasterChef: add token error!");
        require(address(pool.dividendToken) != address(0), "NFTMasterChef: no dividend token set!");
        require(!isPoolEnd(_pid), "NFTMasterChef: pool is end!");

        pool.accDividendPerShare = pool.accDividendPerShare.add(_addDividend.mul(ACC_TOKEN_PRECISION).div(pool.amount));
        pool.dividendToken.safeTransferFrom(msg.sender, address(this), _addDividend);
        emit AddDividendForPool(_pid, _addDividend);
    }

    function _requireTokenIds(uint256[] memory _tokenIds) internal pure {
        require(_tokenIds.length > 0, "NFTMasterChef: tokenIds can not be empty!");
        require(!_tokenIds.hasDuplicate(), "NFTMasterChef: tokenIds can not contain duplicate ones!");
    }
}

