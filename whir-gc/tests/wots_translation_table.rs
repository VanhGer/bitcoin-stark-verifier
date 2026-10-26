//! The off-chain cost of the WOTS translation table of
//! `dispute::wots_translation`.
//!
//! Every chunk's table has the same shape, so its size is exact from a few
//! built chunks: 24 bits of 112 points and 57 grid cells, 16 bytes each. The
//! totals follow at both verifiers' input sizes, with the challenger's
//! storage of table and garbled circuit. The ignored test builds the whole
//! table at `WHIR_GC_INPUT_BITS`, checks its size against that, and times the
//! operator's build and the challenger's recovery.

mod dispute;

use dispute::wots_translation::{self, CHUNK_BITS, GRID, POINTS_PER_BIT, WotsKeys};
use garbled_snark_verifier::core::s::S;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use std::time::Instant;

/// `(input bits, non-free gates)` of the garbled verifiers, from the README's
/// headline figures, a gate garbling to 16 B: the Keccak verifier at 2^18
/// rows and the narrow recursion.
const KECCAK: (usize, usize) = (1_041_024, 94_069_548);
const NARROW: (usize, usize) = (564_552, 218_022_788);

const CHUNK_BYTES: usize = 16 * (CHUNK_BITS * POINTS_PER_BIT + GRID);

#[test]
fn translation_table_total_bytes() {
    let mut rng = ChaCha20Rng::seed_from_u64(0x7ab1e);
    let keys = WotsKeys::new(3, &mut rng);
    let (table, labels0) = wots_translation::build(&keys, &rng.random(), S(rng.random()));
    assert_eq!(labels0.len(), 3 * CHUNK_BITS);
    assert_eq!(table.bytes(), 3 * CHUNK_BYTES, "every chunk is the same size");
    assert_eq!(CHUNK_BYTES, 43_920);

    eprintln!("verifier | input bits | chunks | table B | B per bit | garbled B | challenger stores B");
    for (name, (bits, gates), expected_table) in
        [("Keccak 2^18", KECCAK, 1_905_073_920usize), ("narrow recursion", NARROW, 1_033_130_160)]
    {
        assert_eq!(bits % CHUNK_BITS, 0);
        let chunks = bits / CHUNK_BITS;
        let table = chunks * CHUNK_BYTES;
        assert_eq!(table, expected_table);
        let garbled = 16 * gates;
        eprintln!(
            "{name} | {bits} | {chunks} | {table} | {:.0} | {garbled} | {}",
            table as f64 / bits as f64,
            table + garbled
        );
    }
}

#[test]
fn translation_table_full_build() {
    let bits: usize = std::env::var("WHIR_GC_INPUT_BITS")
        .ok()
        .map_or(KECCAK.0, |s| s.parse().expect("WHIR_GC_INPUT_BITS is a bit count"));
    let chunks = bits.div_ceil(CHUNK_BITS);
    let mut rng = ChaCha20Rng::seed_from_u64(0x7ab1f);
    let keys = WotsKeys::new(chunks, &mut rng);
    let delta = S(rng.random());

    let start = Instant::now();
    let (table, labels0) = wots_translation::build(&keys, &rng.random(), delta);
    let build = start.elapsed();
    assert_eq!(table.bytes(), chunks * CHUNK_BYTES, "the built table is the size the per-chunk count gives");

    let message: Vec<bool> = (0..chunks * CHUNK_BITS).map(|_| rng.random()).collect();
    let sig = keys.sign(&message);
    let start = Instant::now();
    let read = wots_translation::read_labels(&keys.ends, &table, &sig);
    let recover = start.elapsed();
    for (b, (value, label)) in read.iter().enumerate() {
        assert_eq!(*value, message[b]);
        assert_eq!(*label, if *value { labels0[b] ^ delta } else { labels0[b] }, "bit {b}");
    }
    eprintln!(
        "{bits} bits, {chunks} chunks: table {} B; build {:.1} s, recovery {:.1} s on {} threads",
        table.bytes(),
        build.as_secs_f64(),
        recover.as_secs_f64(),
        p3_maybe_rayon::prelude::current_num_threads(),
    );
}
