#![deny(warnings)]
#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

//! `wasm_sync` offers synchronization primitives that work in both browser and native contexts.
//! 
//! In web browsers, use of atomic wait instructions on the main thread [causes an error](https://github.com/WebAssembly/threads/issues/106). This prevents the use of standard library synchronization primitives within web contexts. `wasm_sync` solves this problem by busy-spinning on the main thread. Other threads, like dedicated web workers, still use atomic wait instructions.
//! 
//! On native platforms, `wasm_sync` simply re-exports the standard library's synchronization primitives.
//! 
//! ## Supported primitives
//! 
//! - [`wasm_sync::Condvar`](crate::Condvar)
//! - [`wasm_sync::Mutex`](crate::Mutex)
//! - [`wasm_sync::RwLock`](crate::RwLock)
//! - [`wasm_sync::Once`](crate::Once)
//! - [`wasm_sync::OnceLock`](crate::OnceLock)
//! 
//! ## Usage
//! 
//! Instead of importing a standard library primitive, import the `wasm_sync` variant. For example:
//! 
//! ```rust
//! use std::sync::Arc;
//! use std::thread;
//! use wasm_sync::Mutex;
//! 
//! let mutex = Arc::new(Mutex::new(0));
//! let c_mutex = Arc::clone(&mutex);
//! 
//! thread::spawn(move || {
//!     *c_mutex.lock().unwrap() = 10;
//! }).join().expect("thread::spawn failed");
//! assert_eq!(*mutex.lock().unwrap(), 10);
//! ```
//! 
//! 

/// Provides the ability to generate and compare type IDs in a `const` context.
#[cfg_attr(all(target_arch = "wasm32", target_feature = "atomics"), path = "wasm.rs")]
#[cfg_attr(not(all(target_arch = "wasm32", target_feature = "atomics")), path = "native.rs")]
mod backend;

pub use crate::backend::*;
pub use crate::backend::Condvar;
pub use crate::backend::Mutex;
pub use crate::backend::RwLock;