contract A {
    uint transient public x = 0;
    uint transient y = f();
    function f() public returns (uint) {
        ++x;
        return 42;
    }
}
contract B is A {
    uint transient public z;
    constructor() {
        z = x;
    }
    function getY() public returns (uint) {
        return y;
    }
 }
// ====
// EVMVersion: >=cancun
// compileViaYul: false
// ----
// x() -> 0
// z() -> 0
// getY() -> 0

