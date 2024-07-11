// STRICTLY UNLICENSED. DO NOT USE THIS CODE.
contract Math {
    uint256 internal constant MAX_INT256 = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
    function mostSignificantBit(uint256 x) public pure returns (uint256 msb) {
        assembly {
            let n := mul(128, gt(x, 0xffffffffffffffffffffffffffffffff))
            x := shr(n, x)
            msb := add(msb, n)

            n := mul(64, gt(x, 0xffffffffffffffff))
            x := shr(n, x)
            msb := add(msb, n)

            n := mul(32, gt(x, 0xffffffff))
            x := shr(n, x)
            msb := add(msb, n)

            n := mul(16, gt(x, 0xffff))
            x := shr(n, x)
            msb := add(msb, n)

            n := mul(8, gt(x, 0xff))
            x := shr(n, x)
            msb := add(msb, n)

            n := mul(4, gt(x, 0xf))
            x := shr(n, x)
            msb := add(msb, n)

            n := mul(2, gt(x, 0x3))
            x := shr(n, x)
            msb := add(msb, n)

            msb := add(msb, gt(x, 0x1))
        }
    }

        function sqrtOZ(uint256 a) public pure returns (uint256) {
        unchecked {
            // Take care of easy edge cases when a == 0 or a == 1
            if (a <= 1) {
                return a;
            }

            // In this function, we use Newton's method to get a root of `f(x) := x² - a`. It involves building a
            // sequence x_n that converges toward sqrt(a). For each iteration x_n, we also define the error between
            // the current value as `ε_n = | x_n - sqrt(a) |`.
            //
            // For our first estimation, we consider `e` the smallest power of 2 which is bigger than the square root
            // of the target. (i.e. `2**(e-1) ≤ sqrt(a) < 2**e`). We know that `e ≤ 128` because `(2¹²⁸)² = 2²⁵⁶` is
            // bigger than any uint256.
            //
            // By noticing that
            // `2**(e-1) ≤ sqrt(a) < 2**e → (2**(e-1))² ≤ a < (2**e)² → 2**(2*e-2) ≤ a < 2**(2*e)`
            // we can deduce that `e - 1` is `log2(a) / 2`. We can thus compute `x_n = 2**(e-1)` using a method similar
            // to the msb function.
            uint256 aa = a;
            uint256 xn = 1;

            if (aa >= (1 << 128)) {
                aa >>= 128;
                xn <<= 64;
            }
            if (aa >= (1 << 64)) {
                aa >>= 64;
                xn <<= 32;
            }
            if (aa >= (1 << 32)) {
                aa >>= 32;
                xn <<= 16;
            }
            if (aa >= (1 << 16)) {
                aa >>= 16;
                xn <<= 8;
            }
            if (aa >= (1 << 8)) {
                aa >>= 8;
                xn <<= 4;
            }
            if (aa >= (1 << 4)) {
                aa >>= 4;
                xn <<= 2;
            }
            if (aa >= (1 << 2)) {
                xn <<= 1;
            }

            // We now have x_n such that `x_n = 2**(e-1) ≤ sqrt(a) < 2**e = 2 * x_n`. This implies ε_n ≤ 2**(e-1).
            //
            // We can refine our estimation by noticing that the middle of that interval minimizes the error.
            // If we move x_n to equal 2**(e-1) + 2**(e-2), then we reduce the error to ε_n ≤ 2**(e-2).
            // This is going to be our x_0 (and ε_0)
            xn = (3 * xn) >> 1; // ε_0 := | x_0 - sqrt(a) | ≤ 2**(e-2)

            // From here, Newton's method give us:
            // x_{n+1} = (x_n + a / x_n) / 2
            //
            // One should note that:
            // x_{n+1}² - a = ((x_n + a / x_n) / 2)² - a
            //              = ((x_n² + a) / (2 * x_n))² - a
            //              = (x_n⁴ + 2 * a * x_n² + a²) / (4 * x_n²) - a
            //              = (x_n⁴ + 2 * a * x_n² + a² - 4 * a * x_n²) / (4 * x_n²)
            //              = (x_n⁴ - 2 * a * x_n² + a²) / (4 * x_n²)
            //              = (x_n² - a)² / (2 * x_n)²
            //              = ((x_n² - a) / (2 * x_n))²
            //              ≥ 0
            // Which proves that for all n ≥ 1, sqrt(a) ≤ x_n
            //
            // This gives us the proof of quadratic convergence of the sequence:
            // ε_{n+1} = | x_{n+1} - sqrt(a) |
            //         = | (x_n + a / x_n) / 2 - sqrt(a) |
            //         = | (x_n² + a - 2*x_n*sqrt(a)) / (2 * x_n) |
            //         = | (x_n - sqrt(a))² / (2 * x_n) |
            //         = | ε_n² / (2 * x_n) |
            //         = ε_n² / | (2 * x_n) |
            //
            // For the first iteration, we have a special case where x_0 is known:
            // ε_1 = ε_0² / | (2 * x_0) |
            //     ≤ (2**(e-2))² / (2 * (2**(e-1) + 2**(e-2)))
            //     ≤ 2**(2*e-4) / (3 * 2**(e-1))
            //     ≤ 2**(e-3) / 3
            //     ≤ 2**(e-3-log2(3))
            //     ≤ 2**(e-4.5)
            //
            // For the following iterations, we use the fact that, 2**(e-1) ≤ sqrt(a) ≤ x_n:
            // ε_{n+1} = ε_n² / | (2 * x_n) |
            //         ≤ (2**(e-k))² / (2 * 2**(e-1))
            //         ≤ 2**(2*e-2*k) / 2**e
            //         ≤ 2**(e-2*k)
            xn = (xn + a / xn) >> 1; // ε_1 := | x_1 - sqrt(a) | ≤ 2**(e-4.5)  -- special case, see above
            xn = (xn + a / xn) >> 1; // ε_2 := | x_2 - sqrt(a) | ≤ 2**(e-9)    -- general case with k = 4.5
            xn = (xn + a / xn) >> 1; // ε_3 := | x_3 - sqrt(a) | ≤ 2**(e-18)   -- general case with k = 9
            xn = (xn + a / xn) >> 1; // ε_4 := | x_4 - sqrt(a) | ≤ 2**(e-36)   -- general case with k = 18
            xn = (xn + a / xn) >> 1; // ε_5 := | x_5 - sqrt(a) | ≤ 2**(e-72)   -- general case with k = 36
            xn = (xn + a / xn) >> 1; // ε_6 := | x_6 - sqrt(a) | ≤ 2**(e-144)  -- general case with k = 72

            // Because e ≤ 128 (as discussed during the first estimation phase), we know have reached a precision
            // ε_6 ≤ 2**(e-144) < 1. Given we're operating on integers, then we can ensure that xn is now either
            // sqrt(a) or sqrt(a) + 1.
            uint256 f = 0;
            if (xn > a / xn) f = 1;
            return xn - f;
        }
    }

    function addDelta(uint256 x, int256 delta) public pure returns (uint256 success, uint256 y) {
        assembly {
            y := add(x, delta)

            success := iszero(or(gt(x, MAX_INT256), gt(y, MAX_INT256)))
        }
    }



        function sqrt512(uint256 x0, uint256 x1, bool roundUp) public pure returns (uint256 s) {
        if (x1 == 0) return sqrt(x0, roundUp);
        if (x1 == type(uint256).max) revert (); // max allowed is sqrt((2^256-1)^2), orelse round up would overflow

        uint256 mx0 = x0; // Cache x0

        uint256 shift;

        // Condition: a_3 >= b / 4
        // => x_1 >= b^2 / 4 = 2^254
        assembly {
            let n := mul(lt(x1, 0x100000000000000000000000000000000), 128)
            x1 := shl(n, x1)
            shift := n

            n := mul(lt(x1, 0x1000000000000000000000000000000000000000000000000), 64)
            x1 := shl(n, x1)
            shift := add(shift, n)

            n := mul(lt(x1, 0x100000000000000000000000000000000000000000000000000000000), 32)
            x1 := shl(n, x1)
            shift := add(shift, n)

            n := mul(lt(x1, 0x1000000000000000000000000000000000000000000000000000000000000), 16)
            x1 := shl(n, x1)
            shift := add(shift, n)

            n := mul(lt(x1, 0x100000000000000000000000000000000000000000000000000000000000000), 8)
            x1 := shl(n, x1)
            shift := add(shift, n)

            n := mul(lt(x1, 0x1000000000000000000000000000000000000000000000000000000000000000), 4)
            x1 := shl(n, x1)
            shift := add(shift, n)

            n := mul(lt(x1, 0x4000000000000000000000000000000000000000000000000000000000000000), 2)
            x1 := shl(n, x1)
            shift := add(shift, n)

            x1 := or(x1, shr(sub(256, shift), x0))
            x0 := shl(shift, x0)
        }

        uint256 sp = sqrt(x1, false); // s' = sqrt(x1)

        assembly {
            let rp := sub(x1, mul(sp, sp)) // r' = x1 - s^2

            let nom := or(shl(128, rp), shr(128, x0)) // r'b + a_1
            let denom := shl(1, sp) // 2s'
            let q := div(nom, denom) // q = floor(nom / denom)
            let u := mod(nom, denom) // u = nom % denom

            {
                // The nominator can be bigger than 2**256. We know that rp < (sp+1) * (sp+1). As sp can be
                // at most floor(sqrt(2**256 - 1)) we can conclude that the nominator has at most 513 bits
                // set. An expensive 512x256 bit division can be avoided by treating the bit at position 513 manually
                let carry := shr(128, rp)
                let x := mul(carry, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
                q := add(q, div(x, denom))
                u := add(u, add(carry, mod(x, denom)))
                q := add(q, div(u, denom))
                u := mod(u, denom)

                s := add(shl(128, sp), q) // s'b + q
            }

            // r = u'b + a_0 - q^2
            // r = (u_1 * b + u_0) * b + a_0 - (q_1 * b + q_0)^2
            // r = u_1 * b^2 + u_0 * b + a_0 - q_1^2 * b^2 - 2 * q_1 * q_0 * b - q_0^2
            // r < 0 <=> u_1 < q_1 or (u_1 == q_1 and u_0 * b + a_0 - 2 * q_1 * q_0 * b - q_0^2)
            let rl := or(shl(128, u), and(x0, 0xffffffffffffffffffffffffffffffff)) // u_0 *b + a_0
            let rr := mul(q, q) // q^2
            let q1 := shr(128, q)
            let u1 := shr(128, u)
            s := sub(s, or(lt(u1, q1), and(eq(u1, q1), lt(rl, rr)))) // if r < 0 { s -= 1 }
            s := shr(shr(1, shift), s) // s >>= (shift / 2)

            s := add(s, iszero(or(eq(mul(s, s), mx0), iszero(roundUp)))) // round up if necessary
        }
    }
    function sqrtUni(uint y) public pure returns (uint z) {
        if (y > 3) {
            z = y;
            uint x = y / 2 + 1;
            while (x < z) {
                z = x;
                x = (y / x + x) / 2;
            }
        } else if (y != 0) {
            z = 1;
        }
    }

        function min(uint256 x, uint256 y) public pure returns (uint256 r) {
        assembly {
            r := xor(y, mul(xor(x, y), lt(x, y)))
        }
    }

    /**
     * @notice Returns the maximum of two numbers
     * @param x The first number
     * @param y The second number
     * @return r The maximum of the two numbers
     */
    function max(uint256 x, uint256 y) public pure returns (uint256 r) {
        assembly {
            r := xor(y, mul(xor(x, y), gt(x, y)))
        }
    }

    /**
     * @notice Returns the absolute value of x
     * @param x The number to find the absolute value of
     * @return r The absolute value of x
     */
    function abs(int256 x) public pure returns (uint256 r) {
        assembly {
            let mask := sar(255, x)
            r := xor(add(x, mask), mask)
        }
    }


    // /**
    //  * @notice Calculates the square root of x
    //  * @dev Credit to OpenZeppelin's Math library under MIT license
    //  * @param x The number to find the square root of
    //  * @param roundUp Whether to round up the result
    //  * @return sqrtX The square root of x
    //  */
    function sqrt(uint256 x, bool roundUp) public pure returns (uint256 sqrtX) {
        if (x == 0) return 0;

        uint256 msb = mostSignificantBit(x);

        assembly {
            sqrtX := shl(shr(1, msb), 1)

            sqrtX := shr(1, add(sqrtX, div(x, sqrtX)))
            sqrtX := shr(1, add(sqrtX, div(x, sqrtX)))
            sqrtX := shr(1, add(sqrtX, div(x, sqrtX)))
            sqrtX := shr(1, add(sqrtX, div(x, sqrtX)))
            sqrtX := shr(1, add(sqrtX, div(x, sqrtX)))
            sqrtX := shr(1, add(sqrtX, div(x, sqrtX)))
            sqrtX := shr(1, add(sqrtX, div(x, sqrtX)))

            sqrtX := sub(sqrtX, gt(sqrtX, div(x, sqrtX)))
            sqrtX := add(sqrtX, mul(iszero(iszero(roundUp)), lt(mul(sqrtX, sqrtX), x)))
        }
    }

    // function sqrt512Dumb(uint256 y0, uint256 y1) external view returns (uint256 z0, uint256 z1) {
    //     if (y1 > 0 || y0 > 3) {
    //         (z0, z1) = (y0, y1);
    //         (uint256 x0, uint256 x1) = div512(y0, y1, 0, 2);
    //         (x0, x1) = add512    (0, 1, x0, x1);
    //         while (x1 < z1 || (x1 == z1 && x0 < z0)) {
    //             (z0, z1) = (x0, x1);
    //             (uint256 t0, uint256 t1) = div512(y0, y1, x0, x1);
    //             (x0, x1) = add512(t0, t1, x0, x1);
    //             (x0, x1) = add512(t0, t1, 0, 2);
    //         }
    //     } else if (y0 != 0 || y1 != 0) {
    //         z0 = 1;
    //     }
    // }

    function div(uint256 x, uint256 y, bool roundUp) public pure returns (uint256 z) {
        assert (y != 0);

        assembly {
            z := add(div(x, y), iszero(or(iszero(mod(x, y)), iszero(roundUp))))
        }
    }


    // function sqrt512(uint256 x0, uint256 x1, bool roundUp) public pure returns (uint256 s) {
    //     if (x1 == 0) return sqrt(x0, roundUp);
    //     if (x1 == type(uint256).max) revert(); // max allowed is sqrt((2^256-1)^2), orelse round up would overflow

    //     uint256 shift;

    //     // Condition: a_3 >= b / 4
    //     // => x_1 >= b^2 / 4 = 2^254
    //     assembly {
    //         let n := mul(lt(x1, 0x100000000000000000000000000000000), 128)
    //         x1 := shl(n, x1)
    //         shift := n

    //         n := mul(lt(x1, 0x1000000000000000000000000000000000000000000000000), 64)
    //         x1 := shl(n, x1)
    //         shift := add(shift, n)

    //         n := mul(lt(x1, 0x100000000000000000000000000000000000000000000000000000000), 32)
    //         x1 := shl(n, x1)
    //         shift := add(shift, n)

    //         n := mul(lt(x1, 0x1000000000000000000000000000000000000000000000000000000000000), 16)
    //         x1 := shl(n, x1)
    //         shift := add(shift, n)

    //         n := mul(lt(x1, 0x100000000000000000000000000000000000000000000000000000000000000), 8)
    //         x1 := shl(n, x1)
    //         shift := add(shift, n)

    //         n := mul(lt(x1, 0x1000000000000000000000000000000000000000000000000000000000000000), 4)
    //         x1 := shl(n, x1)
    //         shift := add(shift, n)

    //         n := mul(lt(x1, 0x4000000000000000000000000000000000000000000000000000000000000000), 2)
    //         x1 := shl(n, x1)
    //         shift := add(shift, n)

    //         x1 := or(x1, shr(sub(256, shift), x0))
    //         x0 := shl(shift, x0)
    //     }

    //     uint256 sp = sqrt(x1, false); // s' = sqrt(x1)

    //     assembly {
    //         let rp := sub(x1, mul(sp, sp)) // r' = x1 - s^2

    //         let nom := or(shl(128, rp), shr(128, x0)) // r'b + a_1
    //         let denom := shl(1, sp) // 2s'
    //         let q := div(nom, denom) // q = floor(nom / denom)
    //         let u := mod(nom, denom) // u = nom % denom

    //         {
    //             // The nominator can be bigger than 2**256. We know that rp < (sp+1) * (sp+1). As sp can be
    //             // at most floor(sqrt(2**256 - 1)) we can conclude that the nominator has at most 513 bits
    //             // set. An expensive 512x256 bit division can be avoided by treating the bit at position 513 manually
    //             let carry := shr(128, rp)
    //             let x := mul(carry, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
    //             q := add(q, div(x, denom))
    //             u := add(u, add(carry, mod(x, denom)))
    //             q := add(q, div(u, denom))
    //             u := mod(u, denom)

    //             s := add(shl(128, sp), q) // s'b + q
    //         }

    //         // r = u'b + a_0 - q^2
    //         // r = (u_1 * b + u_0) * b + a_0 - (q_1 * b + q_0)^2
    //         // r = u_1 * b^2 + u_0 * b + a_0 - q_1^2 * b^2 - 2 * q_1 * q_0 * b - q_0^2
    //         // r < 0 <=> u_1 < q_1 or (u_1 == q_1 and u_0 * b + a_0 - 2 * q_1 * q_0 * b - q_0^2)
    //         let rl := or(shl(128, u), and(x0, 0xffffffffffffffffffffffffffffffff)) // u_0 *b + a_0
    //         let rr := mul(q, q) // q^2
    //         let q1 := shr(128, q)
    //         let u1 := shr(128, u)
    //         s := sub(s, or(lt(u1, q1), and(eq(u1, q1), lt(rl, rr)))) // if r < 0 { s -= 1 }
    //         s := shr(shr(1, shift), s) // s >>= (shift / 2)

    //         s := add(s, iszero(or(eq(mul(s, s), x0), iszero(roundUp)))) // round up if necessary
    //     }
    // }   
    function mul512(uint256 x, uint256 y) public pure returns (uint256 z0, uint256 z1) {
        assembly {
            let mm := mulmod(x, y, not(0))
            z0 := mul(x, y)
            z1 := sub(sub(mm, z0), lt(mm, z0))
        }
    } 

    function add512(uint256 x0, uint256 x1, uint256 y0, uint256 y1) public pure returns (uint256 success, uint256 z0, uint256 z1) {

        assembly {
            let rz1 := add(x1, y1)

        z0 := add(x0, y0)
        z1 := add(rz1, lt(z0, x0))

        success := iszero(or(lt(rz1, x1), lt(z1, rz1)))

        }

    }

}