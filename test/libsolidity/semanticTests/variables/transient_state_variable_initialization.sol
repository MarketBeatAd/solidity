contract C {
    uint transient public x = 2;

    constructor() {
        x = 1;
    }

}
// ====
// EVMVersion: >=cancun
// compileViaYul: false
// ----
// constructor()
// gas legacy: 57897
// gas legacy code: 57200
// x() -> 0
