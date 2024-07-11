// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console} from "forge-std/Test.sol";
import {Math} from "../src/Math.sol";
import {SymTest} from "halmos-cheatcodes/SymTest.sol";


contract MathTest is Test, SymTest {
    Math public math;

    function setUp() public {
        math = new Math();
        
    }
    // @note Tests that sqrt(i**2 + offset) is i for offset so that i**2 + offset < (i+1)**2
    function test_sqrt(uint256 i, uint256 offset) public {
        i = bound(i, uint256(0),type(uint256).max-1);
       // uint256 squaredMin = 
    }

    function test_div() public {
        uint256 x0 = svm.createUint256("x0");
        uint256 x1 = svm.createUint256("x1");

        assertEq(math.div(x0, x1, false), x0/x1);
    }

    // @note Tests that sqrt(i**2) is i
    function test_sqrtSimple(uint16 i) public {
        
        uint256 squared = uint256(i)**2; 
        //if (i == 25432) squared -= 1;// @todo replace with math full width pow
        assert(math.sqrt(squared, true) == i);
       // assert(math.sqrt(squared, false)== i);
    }

    function test_sqrtEquivallence(uint256 x) public {
        uint256 ozSqrt = math.sqrtOZ(x);
        uint256 sqrt = math.sqrt(x, false);
        assertEq(ozSqrt, sqrt);
    }

    function test_sqrtWide(uint256 i) public {

        i = bound(i, uint256(2),type(uint256).max-2);
        (uint256 squared0, uint256 squared1) = math.mul512(i, i); 
        assert(math.sqrt512(squared0, squared1, true) == i);
        (uint256 squared0next,uint256 squared1next) = (squared0, squared1);
        if(squared0next > 0) {
            squared0next -=1;// smaller than one 

        } else {
            squared0next = type(uint256).max;
            squared1next -=1;
        }

        
        assert(math.sqrt512(squared0next, squared1next, false) == i - 1);
        assert(math.sqrt512(squared0next, squared1next, true) == i);


        (uint256 two0, uint256 two1) = (2, 0);
        ( squared0next, squared1next) = math.add512(squared0, squared1, two0, two1);
        
        assert(math.sqrt512(squared0next, squared1next, false) == i);
        assert(math.sqrt512(squared0next, squared1next, true) == i + 1);

    }

    function test_sqrtWide() public {
        uint256 i = 211107574290920554242752163802824480411312838049648942863099187697372515;
         (uint256 squared0, uint256 squared1) = math.mul512(i, i); 
        assert(math.sqrt512(squared0, squared1, true) == i);

    }
}
