#!/bin/sh
RUSTFLAGS='-C target-cpu=native' cargo +nightly test --release -- --ignored --nocapture run_keccak256_prover_recursive_mode_poseidon2
