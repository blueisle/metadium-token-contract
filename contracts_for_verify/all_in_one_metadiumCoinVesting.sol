pragma solidity ^0.4.18;

/**
 * @title SafeMath
 * @dev Math operations with safety checks that throw on error
 */
library SafeMath {

  /**
  * @dev Multiplies two numbers, throws on overflow.
  */
  function mul(uint256 a, uint256 b) internal pure returns (uint256) {
    if (a == 0) {
      return 0;
    }
    uint256 c = a * b;
    assert(c / a == b);
    return c;
  }

  /**
  * @dev Integer division of two numbers, truncating the quotient.
  */
  function div(uint256 a, uint256 b) internal pure returns (uint256) {
    // assert(b > 0); // Solidity automatically throws when dividing by 0
    uint256 c = a / b;
    // assert(a == b * c + a % b); // There is no case in which this doesn't hold
    return c;
  }

  /**
  * @dev Substracts two numbers, throws on overflow (i.e. if subtrahend is greater than minuend).
  */
  function sub(uint256 a, uint256 b) internal pure returns (uint256) {
    assert(b <= a);
    return a - b;
  }

  /**
  * @dev Adds two numbers, throws on overflow.
  */
  function add(uint256 a, uint256 b) internal pure returns (uint256) {
    uint256 c = a + b;
    assert(c >= a);
    return c;
  }
}


/**
 * @title Ownable
 * @dev The Ownable contract has an owner address, and provides basic authorization control
 * functions, this simplifies the implementation of "user permissions".
 */
contract Ownable {
  address public owner;


  event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);


  /**
   * @dev The Ownable constructor sets the original `owner` of the contract to the sender
   * account.
   */
  function Ownable() public {
    owner = msg.sender;
  }

  /**
   * @dev Throws if called by any account other than the owner.
   */
  modifier onlyOwner() {
    require(msg.sender == owner);
    _;
  }

  /**
   * @dev Allows the current owner to transfer control of the contract to a newOwner.
   * @param newOwner The address to transfer ownership to.
   */
  function transferOwnership(address newOwner) public onlyOwner {
    require(newOwner != address(0));
    OwnershipTransferred(owner, newOwner);
    owner = newOwner;
  }

}

/**
 * @title Helps contracts guard against reentrancy attacks.
 * @author Remco Bloemen <remco@2π.com>, Eenae <alexey@mixbytes.io>
 * @dev If you mark a function `nonReentrant`, you should also
 * mark it `external`.
 */
contract ReentrancyGuard {

  /// @dev Constant for unlocked guard state - non-zero to prevent extra gas costs.
  /// See: https://github.com/OpenZeppelin/openzeppelin-solidity/issues/1056
  uint private constant REENTRANCY_GUARD_FREE = 1;

  /// @dev Constant for locked guard state
  uint private constant REENTRANCY_GUARD_LOCKED = 2;

  /**
   * @dev We use a single lock for the whole contract.
   */
  uint private reentrancyLock = REENTRANCY_GUARD_FREE;

  /**
   * @dev Prevents a contract from calling itself, directly or indirectly.
   * If you mark a function `nonReentrant`, you should also
   * mark it `external`. Calling one `nonReentrant` function from
   * another is not supported. Instead, you can implement a
   * `private` function doing the actual work, and an `external`
   * wrapper marked as `nonReentrant`.
   */
  modifier nonReentrant() {
    require(reentrancyLock == REENTRANCY_GUARD_FREE);
    reentrancyLock = REENTRANCY_GUARD_LOCKED;
    _;
    reentrancyLock = REENTRANCY_GUARD_FREE;
  }

}

/**
 * @title CoinVesting
 * @dev A token holder contract that can release its token balance gradually like a
 * typical vesting scheme, with a cliff and vesting period. Optionally revocable by the
 * owner.
 */
contract CoinVesting is Ownable, ReentrancyGuard {
    using SafeMath for uint256;

    event Released(uint256 amount);
    event Revoked();

    // beneficiary of tokens after they are released
    address public beneficiary;

    uint256 public cliff;
    uint256 public start;
    uint256 public duration;

    bool public revocable;

    uint256 public released = 0;
    bool public revoked = false;

    /**
    * @dev Creates a vesting contract that vests its balance of coin to the
    * _beneficiary, gradually in a linear fashion until _start + _duration. By then all
    * of the balance will have vested.
    * @param _beneficiary address of the beneficiary to whom vested tokens are transferred
    * @param _cliff duration in seconds of the cliff in which tokens will begin to vest
    * @param _duration duration in seconds of the period in which the tokens will vest
    * @param _revocable whether the vesting is revocable or not
    */
    function CoinVesting(address _beneficiary, uint256 _start, uint256 _cliff, uint256 _duration, bool _revocable) public {
        require(_beneficiary != address(0));
        require(_cliff <= _duration);

        require(_duration > 0);
        require(_start.add(_duration) > now);

        beneficiary = _beneficiary;
        revocable = _revocable;
        duration = _duration;
        cliff = _start.add(_cliff);
        start = _start;
    }

    /**
    * @notice fallback function
    */
    function () payable nonReentrant public {

    }

    /**
    * @notice Transfers vested coins to beneficiary.
    */
    function release() public {
        uint256 unreleased = releasableAmount();

        require(unreleased > 0);

        released = released.add(unreleased);

        beneficiary.transfer(unreleased);

        Released(unreleased);
    }

    /**
    * @notice Allows the owner to revoke the vesting. Coins already vested
    * remain in the contract, the rest are returned to the owner.
    */
    function revoke() public onlyOwner {
        require(revocable);
        require(!revoked);

        uint256 balance = address(this).balance;

        uint256 unreleased = releasableAmount();
        uint256 refund = balance.sub(unreleased);

        revoked = true;

        require(refund > 0);
        owner.transfer(refund);

        Revoked();
    }

    /**
    * @dev Calculates the amount that has already vested but hasn't been released yet.
    */
    function releasableAmount() public view returns (uint256) {

        return vestedAmount().sub(released);
    }

    /**
    * @dev Calculates the amount that has already vested.
    */
    function vestedAmount() public view returns (uint256) {

        uint256 currentBalance = address(this).balance;
        uint256 totalBalance = currentBalance.add(released);

        if (now < cliff) {
            return 0;
        } else if (now >= start.add(duration) || revoked) {
            return totalBalance;
        } else {
            return totalBalance.mul(now.sub(start)).div(duration);
        }
    }
}

/**
 * @title MetadiumCoinVesting
 * @dev A token holder contract that can release its token balance gradually like a
 * typical vesting scheme, with a cliff and vesting period. Optionally revocable by the
 * owner.
 */
contract MetadiumCoinVesting is CoinVesting {
    function MetadiumCoinVesting(address _beneficiary, uint256 _start, uint256 _cliff, uint256 _duration, bool _revocable) public
    CoinVesting(_beneficiary, _start, _cliff, _duration, _revocable)
    {
      
    }
}
