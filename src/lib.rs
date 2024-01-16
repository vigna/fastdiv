//! This crate performs fast division by a runtime constant divisor,
//! by precomputing a division factor that can be used repeatedly.
//!
//! # Example
//! ```
//! use fastdiv::FastDiv;
//!
//! let d: u32 = 3;
//! let m = d.precompute_div();
//!
//! let n1 = 4;
//! let n2 = 9;
//!
//! assert_eq!(n1 / d, n1.fast_div(m));
//! assert_eq!(n2 / d, n2.fast_div(m));
//!
//! assert_eq!(n1 % d, n1.fast_mod(m, d));
//! assert_eq!(n2 % d, n2.fast_mod(m, d));
//!
//! assert_eq!(n1 % d == 0, n1.is_multiple_of(m));
//! assert_eq!(n2 % d == 0, n2.is_multiple_of(m));
//! ```

use std::ops::{Div, Rem};

trait IsMult<Rhs> {
    fn is_mult(self, rhs: Rhs) -> bool;
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "epserde", derive(Epserde))]
#[cfg_attr(feature = "mem_dbg", derive(MemSize, MemDbg))]
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct DivisorU64(u128);

impl DivisorU64 {
    #[inline(always)]
    pub fn from(d: u64) -> Self {
        Self(compute_m_u64(d))
    }
}

impl IsMult<DivisorU64> for u64 {
    #[inline(always)]
    fn is_mult(self, rhs: DivisorU64) -> bool {
        is_divisible_u64(self, rhs.0)
    }
}

impl From<RemainderU64> for DivisorU64 {
    #[inline(always)]
    fn from(r: RemainderU64) -> Self {
        Self(r.0)
    }
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "epserde", derive(Epserde))]
#[cfg_attr(feature = "mem_dbg", derive(MemSize, MemDbg))]
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct DivisorU32(u64);

impl DivisorU32 {
    #[inline(always)]
    pub fn from(d: u32) -> Self {
        Self(compute_m_u32(d))
    }
}

impl IsMult<DivisorU32> for u32 {
    #[inline(always)]
    fn is_mult(self, rhs: DivisorU32) -> bool {
        is_divisible_u32(self, rhs.0)
    }
}

impl From<RemainderU32> for DivisorU32 {
    #[inline(always)]
    fn from(r: RemainderU32) -> Self {
        Self(r.0)
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub struct RemainderU64(u128, u64);

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "epserde", derive(Epserde))]
#[cfg_attr(feature = "mem_dbg", derive(MemSize, MemDbg))]
impl RemainderU64 {
    #[inline(always)]
    pub fn from(d: u64) -> Self {
        Self(compute_m_u64(d), d)
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub struct RemainderU32(u64, u32);

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "epserde", derive(Epserde))]
#[cfg_attr(feature = "mem_dbg", derive(MemSize, MemDbg))]
impl RemainderU32 {
    #[inline(always)]
    pub fn from(d: u32) -> Self {
        Self(compute_m_u32(d), d)
    }
}

impl Div<DivisorU64> for u64 {
    type Output = u64;
    #[inline(always)]
    fn div(self, rhs: DivisorU64) -> Self::Output {
        fastdiv_u64(self, rhs.0)
    }
}

impl Div<DivisorU32> for u32 {
    type Output = u32;
    #[inline(always)]
    fn div(self, rhs: DivisorU32) -> Self::Output {
        fastdiv_u32(self, rhs.0)
    }
}

impl Div<RemainderU64> for u64 {
    type Output = u64;
    #[inline(always)]
    fn div(self, rhs: RemainderU64) -> Self::Output {
        fastdiv_u64(self, rhs.0)
    }
}

impl Div<RemainderU32> for u32 {
    type Output = u32;
    #[inline(always)]
    fn div(self, rhs: RemainderU32) -> Self::Output {
        fastdiv_u32(self, rhs.0)
    }
}

impl Rem<RemainderU64> for u64 {
    type Output = u64;
    #[inline(always)]
    fn rem(self, rhs: RemainderU64) -> Self::Output {
        fastmod_u64(self, rhs.0, rhs.1)
    }
}

impl Rem<RemainderU32> for u32 {
    type Output = u32;
    #[inline(always)]
    fn rem(self, rhs: RemainderU32) -> Self::Output {
        fastmod_u32(self, rhs.0, rhs.1)
    }
}

#[inline(always)]
const fn mul128_u32(lowbits: u64, d: u32) -> u64 {
    (lowbits as u128 * d as u128 >> 64) as u64
}
#[inline(always)]
const fn mul128_u64(lowbits: u128, d: u64) -> u64 {
    let mut bottom_half = (lowbits & 0xFFFFFFFFFFFFFFFF) * d as u128;
    bottom_half >>= 64;
    let top_half = (lowbits >> 64) * d as u128;
    let both_halves = bottom_half + top_half;
    (both_halves >> 64) as u64
}

#[inline(always)]
const fn compute_m_u32(d: u32) -> u64 {
    (0xFFFFFFFFFFFFFFFF / d as u64) + 1
}
#[inline(always)]
const fn fastmod_u32(a: u32, m: u64, d: u32) -> u32 {
    let lowbits = m.wrapping_mul(a as u64);
    mul128_u32(lowbits, d) as u32
}
// for d > 1
#[inline(always)]
const fn fastdiv_u32(a: u32, m: u64) -> u32 {
    mul128_u32(m, a) as u32
}
#[inline(always)]
const fn is_divisible_u32(n: u32, m: u64) -> bool {
    (n as u64).wrapping_mul(m) <= m - 1
}

#[inline(always)]
const fn compute_m_u64(d: u64) -> u128 {
    (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF / d as u128) + 1
}
#[inline(always)]
const fn fastmod_u64(a: u64, m: u128, d: u64) -> u64 {
    let lowbits = m.wrapping_mul(a as u128);
    mul128_u64(lowbits, d)
}
// for d > 1
#[inline(always)]
const fn fastdiv_u64(a: u64, m: u128) -> u64 {
    mul128_u64(m, a)
}
#[inline(always)]
const fn is_divisible_u64(n: u64, m: u128) -> bool {
    (n as u128).wrapping_mul(m) <= m - 1
}

/// Allows precomputing the division factor for fast division, modulo, and divisibility checks.
pub trait FastDiv: Copy {
    type PrecomputedDiv: Copy;
    /// Precompute the division factor from the divisor `self`.
    fn precompute_div(self) -> Self::PrecomputedDiv;
    /// Divide by the divisor, given the precomputed division factor.
    fn fast_div(self, precomputed: Self::PrecomputedDiv) -> Self;
    /// Compute the remainder of the division of `self` by the divisor, given the precomputed division factor and the divisor `d`.
    /// If the precomputed division factor does not come from the same provided divisor, the
    /// result is unspecified.
    fn fast_mod(self, precomputed: Self::PrecomputedDiv, d: Self) -> Self;
    /// Check if `self` is a multiple of the divisor, given the precomputed division factor.
    fn is_multiple_of(self, precomputed: Self::PrecomputedDiv) -> bool;
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub struct PrecomputedDivU32 {
    m: u64,
}
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct PrecomputedDivU64 {
    m: u128,
}

impl FastDiv for u32 {
    type PrecomputedDiv = PrecomputedDivU32;

    #[inline(always)]
    fn precompute_div(self) -> Self::PrecomputedDiv {
        assert!(self > 1);
        Self::PrecomputedDiv {
            m: compute_m_u32(self),
        }
    }

    #[inline(always)]
    fn fast_div(self, precomputed: Self::PrecomputedDiv) -> Self {
        fastdiv_u32(self, precomputed.m)
    }

    #[inline(always)]
    fn fast_mod(self, precomputed: Self::PrecomputedDiv, d: Self) -> Self {
        fastmod_u32(self, precomputed.m, d)
    }

    #[inline(always)]
    fn is_multiple_of(self, precomputed: Self::PrecomputedDiv) -> bool {
        is_divisible_u32(self, precomputed.m)
    }
}

impl FastDiv for u64 {
    type PrecomputedDiv = PrecomputedDivU64;

    #[inline(always)]
    fn precompute_div(self) -> Self::PrecomputedDiv {
        assert!(self > 1);
        Self::PrecomputedDiv {
            m: compute_m_u64(self),
        }
    }

    #[inline(always)]
    fn fast_div(self, precomputed: Self::PrecomputedDiv) -> Self {
        fastdiv_u64(self, precomputed.m)
    }

    #[inline(always)]
    fn fast_mod(self, precomputed: Self::PrecomputedDiv, d: Self) -> Self {
        fastmod_u64(self, precomputed.m, d)
    }

    #[inline(always)]
    fn is_multiple_of(self, precomputed: Self::PrecomputedDiv) -> bool {
        is_divisible_u64(self, precomputed.m)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn div_u32() {
        let n: u32 = 1000;
        for j in 2..n {
            let p = j.precompute_div();
            for i in 0..n {
                assert_eq!(i.fast_mod(p, j), i % j);
                assert_eq!(i.fast_div(p), i / j);
                assert_eq!(i.is_multiple_of(p), i % j == 0);
            }

            let d = DivisorU32::from(j);
            let r = RemainderU32::from(j);
            for i in 0..n {
                assert_eq!(i % r, i % j);
                assert_eq!(i / d, i / j);
                assert_eq!(i.is_multiple_of(p), i % j == 0);
            }
        }
    }

    #[test]
    fn div_u64() {
        let n: u64 = 1000;
        for j in 2..n {
            let p = j.precompute_div();
            for i in 0..n {
                assert_eq!(i.fast_mod(p, j), i % j);
                assert_eq!(i.fast_div(p), i / j);
                assert_eq!(i.is_multiple_of(p), i % j == 0);
            }
        }
    }
}
