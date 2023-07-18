# wasm_sync

[![Crates.io](https://img.shields.io/crates/v/wasm_sync.svg)](https://crates.io/crates/wasm_sync)
[![Docs.rs](https://docs.rs/wasm_sync/badge.svg)](https://docs.rs/wasm_sync)

`wasm_sync` offers synchronization primitives that work in both browser and native contexts.

In web browsers, use of atomic wait instructions on the main thread [causes an error](https://github.com/WebAssembly/threads/issues/106). This prevents the use of standard library synchronization primitives within web contexts. `wasm_sync` solves this problem by busy-spinning on the main thread. Other threads, like dedicated web workers, still use atomic wait instructions.

On native platforms, `wasm_sync` simply re-exports the standard library's synchronization primitives.

## Supported primitives

- `wasm_sync::Condvar`
- `wasm_sync::Mutex`
- `wasm_sync::RwLock`

## Usage

Instead of importing a standard library primitive, import the `wasm_sync` variant. For example:

```rust
use std::sync::Arc;
use std::thread;
use wasm_sync::Mutex;

let mutex = Arc::new(Mutex::new(0));
let c_mutex = Arc::clone(&mutex);

thread::spawn(move || {
    *c_mutex.lock().unwrap() = 10;
}).join().expect("thread::spawn failed");
assert_eq!(*mutex.lock().unwrap(), 10);
```