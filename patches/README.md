# Plonky3 and Ziren patches behind the narrow-recursion GC measurements

Two cumulative patches: every change behind the level-4 verifier tape that
the garbled verifier (`whir-gc`) measures at **564,552 input bits**
(`paper/notes.md` §7n; the per-step patches and logs are kept locally in `paper/data/`, not in the repository).

| patch | base | files |
|---|---|---:|
| `plonky3-fb5d0d89.patch` | ProjectZKM/Plonky3 `fb5d0d89` | 22 |
| `ziren-9398469a.patch` | Ziren branch `whir-gc/narrow-verifier-input` at `9398469a` (on `feat/binary-whir-blake3` `f6137ecc`) | 10 |
| `zkm_blake3_grind.cu` | — | CUDA proof-of-work grinder that the Plonky3 patch links |
| `ziren-dumper.patch` | `f6137ecc` + `ziren-9398469a.patch` without its dumper | the dumper test, rewritten (see below) |
| `ziren-addr26.patch` | the same | 26-bit addresses and compression ids (see below) |

Both patches apply with `git apply` to a clean checkout of their base, and the
result is byte-for-byte the tree the measurements were run from (checked
2026-10-07).

## Applying

```sh
git -C Plonky3 checkout fb5d0d89 && git -C Plonky3 apply ../patches/plonky3-fb5d0d89.patch
git -C Ziren checkout 9398469a  && git -C Ziren apply ../patches/ziren-9398469a.patch
```

Ziren must build against the patched Plonky3: add a
`[patch."https://github.com/ProjectZKM/Plonky3"]` section to Ziren's root
`Cargo.toml` pointing every `p3-*` crate at the patched checkout (left out of
the patch because the paths are local).

The Plonky3 patch makes `p3-binary-field` link `libzkmgrind.so`
unconditionally (experiment only):

```sh
nvcc -O3 -arch=sm_120 -Xcompiler -fPIC -shared -o libzkmgrind.so zkm_blake3_grind.cu
export ZKM_GRIND_LIB_DIR=$PWD LD_LIBRARY_PATH=$PWD
export ZKM_GPU_GRIND=4,5,6,7          # devices; unset, grinding stays on the CPU
export ZKM_GPU_GRIND_MIN_BITS=24      # smaller grinds stay on the CPU
```

## What the patches change

Protocol changes (each reviewed only by its own tests; **none externally
reviewed**):

| change | where | effect on the level-4 GC input |
|---|---|---|
| Merged ring-switch claims: claims sharing the absorbed coordinates send one tensor (`mu`-weighted) | Plonky3 `sumcheck/src/ring_switch/bits/*`, binary-pcs readings | -1,024 elements |
| 25-byte (200-bit) Merkle digests, Blake3 truncated; collisions at 2^100 | Ziren `binary/src/config.rs`, recorder `mmcs.rs`, `bytes.rs` | -64.9 kbit |
| Linear forms: a table sends one value per linear form of its columns its constraints and buses read (derived from the symbolic AIR), a column sumcheck reduces them to the table's block claim, the verifier rebuilds columns with a constant right inverse | Plonky3 `air` (`LinearForms`), `sumcheck/src/table.rs`, `multi-stark/src/instance.rs`, `binary-pcs/src/boolean_trace*`; Ziren `binary-recursion/src/forms.rs`, `machine/mod.rs` | main values 2,176 -> 801, preprocessed 1,280 -> 391 |
| Fixed preprocessed relations: preprocessed forms cut to those independent over the fixed trace's GF(2) column basis and the all-ones column; the rest rebuilt by an affine right inverse (inverse entry `usize::MAX` = constant one) | Plonky3 `sumcheck/src/table.rs`, `binary-pcs/src/boolean_trace/plan.rs`; Ziren `binary-recursion/src/forms.rs` | preprocessed values 391 -> 101 |
| Shared forms sumcheck: one column sumcheck for every forms table, over the widest table's column variables, each table read at the trailing coordinates | Plonky3 `binary-pcs/src/boolean_trace*` | main values 801 -> 751 |
| Joint ring switch: the pair's main and preprocessed switches run as one over both packings behind a selector variable (`JointPaired` opening) | Plonky3 `binary-pcs/src/whir/{boolean,proof}.rs` | one tensor and one sumcheck fewer |
| Eq-factored bus product GKR (Gruen): a radix-four round sends `h` without its linear eq factor | Plonky3 `bus/src/product/{prover,proof}.rs` | one element per round fewer |

Schedule and recording changes (no change to soundness arguments):

| change | where | switch |
|---|---|---|
| Per-round WHIR folds and rate growth (level 4: folds 4,5,4,4, rates 14,18,21, 46-bit grinding) | Plonky3 `binary-pcs/src/whir/profile.rs`; Ziren `binary/src/lib.rs` | `ZIREN_B_FOLDS="4,5,4,4;1"` (`ZIREN_B_FIRST_ROUND=f0,bumps` for a first-round fold only) |
| Deep preprocessed cap: the re-record reads the fixed preprocessed tree down to 18 layers below its root as circuit constants (checked against the key's cap); no proof change | Plonky3 accessors (`ProvingKey::preprocessed_prover_data`, `BooleanTraceCommitmentData::inner`); Ziren `mmcs.rs`, `TapeMachine::preprocessed_tree_layer`, dumper | `ZIREN_DEEP_PREP_CAP=18` (re-record only) |
| Known opened values as constants in the re-record (forms over constant preprocessed columns, main padding) | Ziren `prover/tests/dump_binary_tape.rs` | `ZIREN_RERECORD_PROOF=<proof>` |

Experiment-only: the GPU grinder FFI in `binary-field` (`build.rs`,
`challenger.rs`), and the aligned stacked layout in
`sumcheck/src/layout/plan.rs`, which makes
`layout::witness::tests::witness_stacks_columns_and_zeros_the_tail` fail (the
only failing test in p3-air, p3-sumcheck, p3-binary-pcs, p3-multi-stark,
p3-bus, p3-whir, p3-merkle-tree).

## Rebuilding from scratch (no saved tapes)

The Ziren base `9398469a` is not published. Its parent, `feat/binary-whir-blake3`
at `f6137ecc` (ProjectZKM/Ziren), takes every file of `ziren-9398469a.patch`
except the dumper test, which `ziren-dumper.patch` rewrites (the test and its
dev-dependencies). With `Plonky3/` and `Ziren/` cloned inside this repository:

```sh
git -C Plonky3 checkout fb5d0d89 && git -C Plonky3 apply ../patches/plonky3-fb5d0d89.patch
git -C Ziren checkout f6137ecc \
  && git -C Ziren apply --exclude=crates/prover/tests/dump_binary_tape.rs ../patches/ziren-9398469a.patch \
  && git -C Ziren apply ../patches/ziren-dumper.patch \
  && git -C Ziren apply ../patches/ziren-addr26.patch
```

`ziren-addr26.patch` raises `ADDR_BITS` and `PERMUTATION_ID_BITS` from 24 to
26 (the "26-bit patches" of `paper/notes.md`): at 24 bits `Program::new`
panics on the real level-1 tape ("the program fits 24-bit addresses").
`PERMUTATION_ID_BITS` is also a column width of the binary stage, so level 1
must be recorded with it applied. The 64-byte rewire row of the original
chain was a commit on the unpublished branch and is not in these patches, so
the rebuilt machine keeps 1,024 rewire columns: about 5% more level-4 input
(2,688 main values instead of 2,176 before the forms changes).

Then the `[patch]` section and the grinder as above. Every level runs
`cargo test --release -p zkm-prover --test dump_binary_tape -- --ignored --nocapture`
in `Ziren/`, with `ZIREN_TAPE_OUT=$T VERIFY_VK=false RUST_LOG=info ZIREN_B_MAX_GRIND=50`:

| level | extra environment | writes |
|---|---|---|
| 1 | `ZIREN_BINARY_WITNESS_DUMP=$T/shrink_proof.bin` (`ZIREN_B_FOLDS` unset) | `binary_tape.bin` |
| 2 | `ZIREN_B_SCHEDULE=johnson,3,4 ZIREN_RECURSE_FROM=binary_tape.bin ZIREN_RECURSE_TO=level2_tape-johnson-3-4.bin` | the level-2 tape and proof |
| 3 | `ZIREN_B_SCHEDULE=johnson,9,5 ZIREN_RECURSE_FROM=level2_tape-johnson-3-4.bin ZIREN_RECURSE_TO=level3_tape-johnson-9-5.bin` | the level-3 tape and proof |
| 4 | the two commands below | `level4k_tape-johnson-10-5.bin` |

Level 1 builds the Fibonacci guest, so it needs the zkm toolchain (or prebuilt
ELFs under `crates/test-artifacts/guests/target`); a saved
`shrink_proof.bin` is reused. The rebuilt levels 1-3 run the patched code,
where the originals predate most of the patches, so the level-4 figures may
differ slightly from the table below. The narrow machine binds no public
values unless `ZIREN_NUM_PUBLIC` says how many of a tape's first inputs it
should.

## Reproducing the level-4 tape

From the level-3 tape (`ziren-tape-rw64/level3_tape-johnson-9-5.bin`), with
`VERIFY_VK=false RUST_LOG=info ZIREN_B_FOLDS="4,5,4,4;1"`:

```sh
# prove level 4 (1.8 h on 4 GPUs, ~470 GB peak) and record its verifier
ZIREN_B_SCHEDULE=johnson,10,5 ZIREN_B_MAX_GRIND=50 ZIREN_TAPE_OUT=$T \
ZIREN_RECURSE_FROM=level3_tape-johnson-9-5.bin ZIREN_RECURSE_TO=level4_tape-johnson-10-5.bin \
  cargo test --release -p zkm-prover --test dump_binary_tape -- --ignored --nocapture
# re-record it with known values and the deep preprocessed cap
ZIREN_B_SCHEDULE=johnson,10,5 ZIREN_B_MAX_GRIND=50 ZIREN_TAPE_OUT=$T ZIREN_DEEP_PREP_CAP=18 \
ZIREN_RECURSE_FROM=level3_tape-johnson-9-5.bin ZIREN_RERECORD_PROOF=$T/level4_proof-johnson-10-5.bin \
ZIREN_RECURSE_TO=level4k_tape-johnson-10-5.bin \
  cargo test --release -p zkm-prover --test dump_binary_tape -- --ignored --nocapture
```

then `BINARY_TAPE_DUMP=$T/level4k_tape-johnson-10-5.bin cargo test --release
-p whir-gc --test binary_tape -- --ignored --nocapture` here (gate counts, the
real proof accepted, tampered inputs refused, streaming garbling).

## Results (level 4, Johnson 1/1024, 100-bit composed security)

| step | input bits | non-free gates |
|---|---:|---:|
| 64-byte rewire row (Ziren branch) | 1,248,384 | 231.2 M |
| known values as constants | 1,137,536 | 226.8 M |
| merged claims | 1,006,464 | 221.7 M |
| 200-bit digests, first fold 3 | 895,504 | 220.2 M |
| packed Ledger/Arith columns | 834,832 | 219.2 M |
| linear forms, per-round folds, deep preprocessed cap | 643,688 | 215.8 M |
| joint ring switch, eq-factored bus | 603,112 | 216.5 M |
| fixed preprocessed relations, shared forms sumcheck (cap 14) | 574,952 | 217.8 M |
| **deep preprocessed cap 18** | **564,552** | **218.0 M** |
