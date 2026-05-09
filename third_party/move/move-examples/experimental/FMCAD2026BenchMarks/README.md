# FMCAD2026BenchMarks Scripts

This folder contains benchmark scripts and utilities for the ConditionalBorrowChain family (2-level and 3-level variants).

## Which script to use
- `run_prover_times.ps1` — simple timing runs for the ConditionalBorrowChain benchmarks (2-level).
- `run_move_prove_3level_2_to_8.ps1` — run 3-level variants (2..8) and collect timing output.
- `run_prove_and_collect_smt_v2.ps1` — preferred SMT collector (robust: captures console output, temp dirs, and Z3 query artifacts).
- `run_prove_and_collect_smt.ps1` — simpler SMT collector (kept as a lightweight fallback).

Note: `run_prove_and_collect_smt_v2.ps1` will terminate the prover early — it watches for generated `*.smt*` files and kills the prover as soon as SMTs appear, then collects the files. This shortens collection time but means the prover may not complete full verification; `console_output.txt` contains the captured output up to termination.

## Prerequisites
1. Build the repo `move` binary first (from repository root):

```powershell
cargo build -p move-cli --release
```

This produces `target\\release\\move.exe` which the scripts call via the relative path `..\\..\\..\\..\\..\\target\\release\\move`.

2. Install Boogie and Z3:
- Boogie installed as `$env:USERPROFILE\\.dotnet\\tools\\boogie.exe`
- `z3` available on your `PATH`

Both are checked by the scripts and will stop with an explanatory error if missing.

## Notes about invocation
- The `move prove` command in these scripts forwards prover-specific options after `--` (for example `--generate-smt`).
- Do not pass explicit source file paths to the prover; the scripts copy the chosen variant into `sources/` and rely on the package layout.
- The SMT-collector scripts will automatically use a pre-generated case from `altcases/` (if present). If you need to regenerate inputs, use `inputGeneration.py`.

## Quick usage
From this folder:

```powershell
cd third_party/move/move-examples/experimental/FMCAD2026BenchMarks

# Preferred: collect SMTs (robust)
.\\run_prove_and_collect_smt_v2.ps1



# Run all 3-level proves and record timings
.\\run_move_prove_3level_2_to_8.ps1

# Run the active sources/ConditionalBorrowChain.move 10 times
.\\run_move_prove_10_times.ps1

# Timing sweeps for ConditionalBorrowChain (2-level)
.\\run_prover_times.ps1
```

## Outputs
- `move_prover_times1..8.csv` — timing CSVs produced by `run_prover_times.ps1`.
- `test_result_size/` (or `smt_results/`) — per-variant SMT collections produced by the SMT collectors.

## Repro tips
- If a script errors about names/addresses or unexpected options, make sure you built the repo `move` and are running from this folder so the package `Move.toml` and `sources/` are visible.
- To re-generate inputs instead of using `altcases/`, run:

```powershell
python .\\inputGeneration.py
```

If you want, I can add a small wrapper that optionally runs `cargo build -p move-cli --release` before executing the scripts. Tell me if you'd like that added and whether it should auto-build unconditionally or only when `target\\release\\move.exe` is missing.
