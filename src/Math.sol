// STRICTLY UNLICENSED. DO NOT USE THIS CODE.
contract Math {
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

    /**
     * @notice Calculates the square root of x
     * @dev Credit to OpenZeppelin's Math library under MIT license
     * @param x The number to find the square root of
     * @param roundUp Whether to round up the result
     * @return sqrtX The square root of x
     */
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

    function sqrt512(uint256 x0, uint256 x1, bool roundUp) public pure returns (uint256 s) {
        if (x1 == 0) return sqrt(x0, roundUp);
        if (x1 == type(uint256).max) revert(); // max allowed is sqrt((2^256-1)^2), orelse round up would overflow

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

            s := add(s, iszero(or(eq(mul(s, s), x0), iszero(roundUp)))) // round up if necessary
        }
    }   
    function mul512(uint256 x, uint256 y) public pure returns (uint256 z0, uint256 z1) {
        assembly {
            let mm := mulmod(x, y, not(0))
            z0 := mul(x, y)
            z1 := sub(sub(mm, z0), lt(mm, z0))
        }
    }

}