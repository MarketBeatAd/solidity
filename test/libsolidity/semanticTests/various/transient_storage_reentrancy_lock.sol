contract C {
    bool transient locked;
    constructor() {
        locked = false;
    }
    mapping (address=>bool) registered;
    modifier nonReentrant {
        require(!locked);
        locked = true;
        _;
        locked = false;
    }

    function test(address newAddress, bool reentrancy) nonReentrant public {
        require(!registered[newAddress]);

        if (reentrancy)
            reentrantCall(newAddress);

        registered[newAddress] = true;
    }

    function reentrantCall(address a) public {
        test(a, false);
    }
}
// ====
// EVMVersion: >=cancun
// compileViaYul: false
// ----
// test(address,bool): 0x1234abcd, true ->
// test(address,bool): 0x1234abcd, false -> FAILURE
