#![cfg_attr(
    not(feature = "std"),
    no_std,
    feature(alloc_error_handler, core_intrinsics)
)]
#![feature(register_tool)]
#![register_tool(hax)]

#[hax_lib_macros::exclude]
extern crate hax_lib_macros;
#[hax_lib_macros::exclude]
use hax_lib_macros::*;

#[cfg(not(feature = "hacspec"))]
#[cfg(not(feature = "std"))]
pub extern crate alloc;

/// Terminate execution immediately without panicking.
/// When the `std` feature is enabled this is just [std::process::abort](https://doc.rust-lang.org/std/process/fn.abort.html).
/// When `std` is not present and the target architecture is `wasm32` this will
/// simply emit the [unreachable](https://doc.rust-lang.org/core/arch/wasm32/fn.unreachable.html) instruction.
#[cfg(not(feature = "hacspec"))]
#[cfg(feature = "std")]
pub use std::process::abort as trap;
#[cfg(not(feature = "hacspec"))]
#[cfg(all(not(feature = "std"), target_arch = "wasm32"))]
#[inline(always)]
pub fn trap() -> ! {
    unsafe { core::arch::wasm32::unreachable() }
}
#[cfg(not(feature = "hacspec"))]
#[cfg(all(not(feature = "std"), not(target_arch = "wasm32")))]
#[inline(always)]
pub fn trap() -> ! {
    core::intrinsics::abort()
}

// Provide some re-exports to make it easier to use the library.
// This should be expanded in the future.
/// Re-export.
#[cfg(not(feature = "hacspec"))]
#[cfg(not(feature = "std"))]
pub use alloc::{borrow::ToOwned, string, string::String, string::ToString, vec, vec::Vec};
/// Re-export.
#[cfg(not(feature = "hacspec"))]
#[cfg(not(feature = "std"))]
pub use core::{convert, hash, marker, mem, num, result::*};

#[cfg(not(feature = "hacspec"))]
#[cfg(not(feature = "std"))]
pub use alloc::collections;

pub mod constants;
mod concordium_prims;
mod concordium_impls;
mod concordium_types;
mod concordium_traits;

pub mod test_infrastructure;

use concordium_prims::*; // TODO: Does not re-export anything, nothing is public enough (removed pub)
pub use concordium_impls::*;
pub use concordium_types::*;
pub use concordium_traits::*;


#[cfg(not(feature = "hacspec"))]
extern crate concordium_contracts_common;
#[cfg(not(feature = "hacspec"))]
/// Chain constants that impose limits on various aspects of smart contract
/// execution.
pub use concordium_contracts_common::*;

// TODO: Need derive
#[cfg(not(feature = "hacspec"))]
extern crate hacspec_concordium_derive;
#[cfg(not(feature = "hacspec"))]
pub use hacspec_concordium_derive::*;
