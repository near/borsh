# Borsh benchmarks

To run benchmarks execute:

```bash
cargo bench
```

If you want to make a change and see how it affects the performance then
copy `criterion` folder into `target` folder so that you have `target/criterion`, and run the benchmarks.
Criterion will print whether the change has statistically significant positive/negative impact based on p-values or
whether it is within noise. Unfortunately, benchmarks related to serializing `Account` and `SignedTransaction` turned out to
be highly volatile therefore prefer using `Block` and `BlockHeader` as the measurement of the performance change.
We use default Criterion setting for determining statistical significance, which corresponds to 2 sigma.

We run benchmarks using `n1-standard-2 (2 vCPUs, 7.5 GB memory)` on GCloud. Make sure the instance
is not running any other heavy process.
