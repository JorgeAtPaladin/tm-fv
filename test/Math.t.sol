// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console} from "forge-std/Test.sol";
import {Math} from "../src/Math.sol";

contract MathTest is Test {
    Math public math;

    function setUp() public {
        math = new Math();
        
    }
    // @note Tests that sqrt(i**2 + offset) is i for offset so that i**2 + offset < (i+1)**2
    function test_sqrt(uint256 i, uint256 offset) public {
        uint256 x1 = 0; // We test single word sqrt first.
    }

    // @note Tests that sqrt(i**2) is i
    function test_sqrtSimple(uint16 i) public {
        
        uint256 squared = uint256(i)**2; 
        //if (i == 25432) squared -= 1;// @todo replace with math full width pow
        assert(math.sqrt(squared, true) == i);
       // assert(math.sqrt(squared, false)== i);
    }

    function test_sqrtWide(uint256 i) public {
        (uint256 squared0, uint256 squared1) = math.mul512(i, i); 
        assert(math.sqrt512(squared0, squared1, true) == i);
       // assert(math.sqrt(squared, false)== i);
    }
}
