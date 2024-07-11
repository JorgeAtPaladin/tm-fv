// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console} from "forge-std/Test.sol";
import {Math} from "../src/Math.sol";
import {SymTest} from "halmos-cheatcodes/SymTest.sol";


contract MathTest is Test,SymTest {
    Math public math;

    function setUp() public {
        math = new Math();
        
    }
    // @note Tests that sqrt(i**2 + offset) is i for offset so that i**2 + offset < (i+1)**2
    function test_sqrt(uint256 i, uint256 offset) public {
        i = bound(i, uint256(0),type(uint256).max-1);
       // uint256 squaredMin = 
    }
    

    function check_div_down() public {
        uint256 x0 = svm.createUint256("x0");
        uint256 x1 = svm.createUint256("x1");
        uint256 expected = 0;
        vm.assume(x1 > 0);
        assembly {
            expected := div(x0, x1)
        }
        uint256 actual = math.div(x0, x1, false);

        assert(expected == actual);
    }
    function check_div_up() public {
        uint256 x0 = svm.createUint256("x0");
        uint256 x1 = svm.createUint256("x1");
        vm.assume(x1 > 0);
        uint256 expected = 0;
        assembly {
            expected := div(x0, x1)
        }
        if (x0 % x1 != 0) {
            expected += 1;
        }
        uint256 actual = math.div(x0, x1, true);

        assert(expected == actual);
    }

    function check_add_512() public {
        uint256 x0 = svm.createUint256("x0");
        uint256 x1 = svm.createUint256("x1");
        uint256 y0 = svm.createUint256("y0");
        uint256 y1 = svm.createUint256("y1");
        uint256 expected0;
        uint256 expected1;
        bool expectedSuccess = true;
        unchecked {
            expected0 = x0 + y0;
            expected1 = x1 + y1;
            if (expected0 < x0) {
                expected1 += 1;
                if (expected1 <= x1) {
                    expectedSuccess = false;
                }
            }else if (expected1 < x1) {
                expectedSuccess = false;
            }
        }
        (uint256 success, uint256 r0, uint256 r1) = math.add512(x0, x1, y0, y1);
        assert(success > 0 == expectedSuccess);
        if (success > 0) {
            assert(r0 == expected0);
            assert(r1 == expected1);
        }
    }

    function check_addDelta(uint256 x, int256 delta) public {
        (uint256 success, uint256 r) = math.addDelta(x, delta);
        if (delta > 0) {
            unchecked {
                bool failed = r < x || x > 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff || r > 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
                assert(failed == (success == 0));  // if result is smaller than x, then success should fail?
            }

            if (success > 0) {
                assert(r == x + uint256(delta));
            }
        } else {
            bool failed = uint256(-delta) > x || x > 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
            assert(failed == (success == 0));
            if (success > 0) {
                assert (r == x - uint256(-delta));
            }
        }
    }

    function check_msb(uint256 x, uint256 offset) public {
        vm.assume(x <= 256);
        vm.assume(x > 0);
        
        uint256 power = 2**x;
        uint256 nextPower = x > 255 ? type(uint256).max : 2**(x+1); // 4
        uint256 number = power + offset;

        vm.assume(number < nextPower);
        assert(math.mostSignificantBit(number) == x);
    }

    function test_msb() public {
        uint256 expected = 254;
        uint256 number = 2**254 + 14781102765942169835520577181131799096738994847799794405261356486870684883614;
        assertLt(number, 2**255);// 1000
        uint256 actual = math.mostSignificantBit(number);
        assertEq(actual, expected);

    }

    function test_addDelta() public {
        (uint256 success, uint256 r) = math.addDelta(57327340636640518468457039079805553046355113516022174739549961637362501894203,29179479386868943058007335382510332845094181103526605434495761264262799952907);
        console.log(success, r); // success = 0, r = 77268938920344962238264518703819710791885536423063042704286885751619591434032
    }
    // @note Tests that sqrt(i**2) is i
    function test_sqrtSimple(uint16 i) public {
        
        uint256 squared = uint256(i)**2; 
        //if (i == 25432) squared -= 1;// @todo replace with math full width pow
        assert(math.sqrt(squared, true) == i);
       // assert(math.sqrt(squared, false)== i);
    }

    function check_sqrt(uint8 x) public {
        uint256 ozSqrt = math.sqrtUni(x);
        uint256 sqrt = math.sqrt(x, false);
        assertEq(ozSqrt, sqrt);
    }
    function check_min(uint256 x, uint256 y) public {
        uint256 actual = math.min(x, y);
        if (x < y) {
            assert(actual == x);
        } else {
            assert(actual == y);
        }
    }

    function check_max(uint256 x, uint256 y) public {
        uint256 actual = math.max(x, y);
        if (x > y) {
            assert(actual == x);
        } else {
            assert(actual == y);
        }
    }

    function check_abs(int256 x) public {
        uint256 actual = math.abs(x);
        
        if (x == type(int256).min) {
            assert(actual == 2**255);
        } else if (x < 0) {
            assert(actual == uint256(-x)); // @todo does this actually work due to -x being a negative number?
        } else {
            assert(actual == uint256(x));
        }
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
        (, squared0next, squared1next) = math.add512(squared0, squared1, two0, two1);
        
        assert(math.sqrt512(squared0next, squared1next, false) == i);
        assert(math.sqrt512(squared0next, squared1next, true) == i + 1);

    }

    function test_sqrtWide() public {
        uint256 i = 211107574290920554242752163802824480411312838049648942863099187697372515;
         (uint256 squared0, uint256 squared1) = math.mul512(i, i); 
        assert(math.sqrt512(squared0, squared1, true) == i);

    }


    function check_mul512(uint256 x, uint256 y) public {
        uint256 success;
        (uint256 r0,uint256 r1) = (0, 0);
        for(uint256 i = 0; i < 256; i++) {
            uint256 mask = y & 1<< i;// @note offset our bit by i.
            if (mask > 0) { // if the bit at i is set in y
                (success, r0, r1) = math.add512(r0, r1, x << i, x >> (256 - i));
                assert(success > 0);
            }
        }

        // assert r0 r1 equals math mul512
        (uint256 r0expected, uint256 r1expected) = math.mul512(x, y);
        assert(r0expected == r0);
        assert (r1expected == r1);
    }
}
