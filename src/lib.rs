#![cfg_attr(not(feature = "std"), no_std)]

/// Section 3.1 and 3.2
pub mod hash;

/// Section 3.3
pub mod polynomial;

/// Section 3.4
pub mod code;

/// Section 3.5
pub mod pke;

/// Section 3.6
pub mod kem;

mod size_traits;

#[derive(PartialEq, Eq, Debug, PartialOrd, Ord, Default, Clone, Copy)]
pub struct Hqc1;
#[derive(PartialEq, Eq, Debug, PartialOrd, Ord, Default, Clone, Copy)]
pub struct Hqc3;
#[derive(PartialEq, Eq, Debug, PartialOrd, Ord, Default, Clone, Copy)]
pub struct Hqc5;
