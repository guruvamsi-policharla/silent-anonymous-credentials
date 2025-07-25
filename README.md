# Threshold Issuance Anonymous Credentials with Silent Setup

Rust implementation of threshold issuance anonymous credentials with silent setup introduced in [ePrint:2025/xxx](https://eprint.iacr.org/2025/xxx).

This construction is especially useful in the large number of issuers setting (such as a DAO) where coordinated setup such as distributed key generation amongst the issuers is not possible.


⚠️ **WARNING**: This is an academic proof-of-concept prototype and has not received careful security review. This implementation is **NOT ready for production use**.

## Dependencies

Install Rust via:
```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

The library depends on the [arkworks](https://github.com/arkworks-rs) ecosystem for elliptic curve operations.

## Project Structure

- **`src/crs.rs`**: Common Reference String (CRS) generation and management
- **`src/silent_ac/`**: Core anonymous credential functionality including showing protocols
- **`src/silent_sps/`**: Silent Structure-Preserving Signatures implementation with aggregation support
- **`src/gs08/`**: Groth-Sahai proof system implementation for zero-knowledge proofs
- **`src/utils.rs`**: Utility functions for hashing and other operations
- **`benches/`**: Performance benchmarks for all major operations

## Benchmarking
```bash
# Run all benchmarks
cargo bench

# Run specific benchmarks
cargo bench --bench sign          # Signature generation
cargo bench --bench verify        # Signature verification  
cargo bench --bench agg_sig        # Signature aggregation
cargo bench --bench agg_sig_verify # Aggregated signature verification
cargo bench --bench show          # Credential showing (proof generation)
cargo bench --bench show_verify   # Credential show verification
```

Benchmark results are saved in the `target/criterion` directory. A detailed HTML report is generated at `target/criterion/index.html` which can be viewed in a web browser.

## License

This library is released under the MIT License. 