# SMT Collection Scripts for Move Prove

This directory contains PowerShell scripts to run `move prove` on each `3levelNFieldsBorrow.move` test variant and collect the SMT (Satisfiability Modulo Theories) files generated during verification.

**How it works**: The scripts use the `--generate-smt` flag and the `--output` option to specify a targeted output directory where SMT files are generated alongside the Boogie intermediate representation. This ensures SMT files are collected from a known, predictable location rather than searched for across the filesystem.

## Files

- **run_prove_and_collect_smt.ps1** - Main script (v1)
- **run_prove_and_collect_smt_v2.ps1** - Enhanced version with time-based file tracking

## Usage

From the `third_party/move/move-examples/experimental/basic-coin` directory, run:

```powershell
.\run_prove_and_collect_smt.ps1
```

Or for the enhanced version:

```powershell
.\run_prove_and_collect_smt_v2.ps1
```

## What the scripts do

1. **Find test files**: Locates all `3level*FieldsBorrow.move` files in the `altcases/` subdirectory
   - 3level2FieldsBorrow.move
   - 3level3FieldsBorrow.move
   - ... through 3level8FieldsBorrow.move

2. **For each test variant**:
   - Copies it to `sources/ConditionalBorrowChain.move`
   - Creates a temporary directory in `$env:TEMP` to capture output
   - Runs `move prove --generate-smt --output <temp_dir>/output.bpl`
   - SMT files are generated alongside the Boogie output in the temp directory
   - Copies all generated files to the final output subdirectory
   - Cleans up the temporary directory

3. **Organize results**: Saves all generated files (SMT, Boogie, etc.) to separate subdirectories by test variant:
   ```
   smt_results/
   ├── 3level2FieldsBorrow/
   │   ├── *.smt2
   │   ├── *.smt
   │   └── output.bpl
   ├── 3level3FieldsBorrow/
   │   ├── *.smt2
   │   ├── *.smt
   │   └── output.bpl
   └── ...
   ```

## Output

Each test variant gets its own subdirectory containing:
- **SMT files** (*.smt2, *.smt): The actual solver queries
- **output.bpl**: The Boogie intermediate representation
- **console_output.txt** (v2 only): The prover's console output

## Troubleshooting

- **"move prover not found"**: Ensure the move project is built with `cargo build -p move`
- **"No 3levelNFieldsBorrow.move files found"**: Verify you're in the correct directory
- **No files collected**: Check that:
  - The move prove command executed successfully (check console output in each subdir)
  - Your temporary directory (`$env:TEMP`) has sufficient disk space
  - Move prover has write permissions to the temp directory

## Key Improvements

- **Targeted collection**: Instead of searching the entire filesystem, SMT files are collected from a specific temp directory
- **Reliable**: No risk of collecting wrong files or missing files that were placed elsewhere
- **Clean**: Temporary directories are automatically cleaned up after collection

## Version Differences

Both scripts now use the same targeted directory approach with minor differences:

**v1 (run_prove_and_collect_smt.ps1)**
- Simpler, streamlined implementation
- Good for standard use cases
- Recommended for most users

**v2 (run_prove_and_collect_smt_v2.ps1)**
- Includes console output capture for debugging
- Same core functionality as v1
- Useful if you want to review detailed prover output
