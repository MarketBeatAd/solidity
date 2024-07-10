// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.0.0;

contract C {
    uint transient x = 42;
    function f() public {
        x = x + 1;
    }
}
