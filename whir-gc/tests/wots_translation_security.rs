//! Security regressions for the WOTS translation table of
//! `dispute::wots_translation`.
//!
//! The counting argument is checked exhaustively over every digit value and
//! checksum, without cryptography. The rest runs on real tables: a signed
//! chunk opens exactly the labels of its bits, hashing any node forward or
//! opening a later grid cell opens nothing more, assuming either threshold
//! shift opens no unearned label, one chunk's `κ` does not lower another's
//! threshold, one instance's view opens nothing of another's table under the
//! same key, and the labels are free-XOR pairs.
//!
//! Signing one key several times, as these tests do, is only to compare the
//! views of different messages against one table; the protocol signs once.

mod dispute;

use dispute::wots_translation::{self, CHAINS, CHUNK_BITS, D, DIGITS, GRID, K, RADIX, W_MAX, WotsKeys};
use garbled_snark_verifier::core::s::S;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

/// Chunk bits whose digits are `x`.
fn bits_of(x: &[u8; DIGITS]) -> Vec<bool> {
    x.iter().flat_map(|&v| (0..D).map(move |p| (v >> p) & 1 == 1)).collect()
}

/// The true label of bit `p` of digit `j` in `chunk` at `value`.
fn label(labels0: &[S], delta: S, chunk: usize, j: usize, p: usize, value: bool) -> S {
    let l0 = labels0[chunk * CHUNK_BITS + D * j + p];
    if value { l0 ^ delta } else { l0 }
}

#[test]
fn point_counts_open_exactly_the_signed_bits() {
    // For each label, each value of its digit and each checksum share of the
    // other digits: the points a signed chunk opens, counted on the layout,
    // against the threshold W + δ.
    for j in 0..DIGITS {
        for p in 0..D {
            for value in [false, true] {
                let layout = wots_translation::layout(j, p, value);
                for xj in 0..=K {
                    for others in 0..=(DIGITS - 1) * K {
                        // Spread `others` = Σ_{i≠j} (7 - x_i) over the other digits.
                        let mut x = [K; DIGITS];
                        let mut left = others;
                        for i in (0..DIGITS).filter(|&i| i != j) {
                            let take = left.min(K);
                            x[i] = K - take;
                            left -= take;
                        }
                        x[j] = xj;
                        let w: usize = x.iter().map(|&v| K - v).sum();
                        let opened = layout.iter().filter(|&&(i, k)| k >= x[i]).count();
                        let t = w + wots_translation::shift(value);
                        let matches = ((xj >> p) & 1 == 1) == value;
                        assert_eq!(opened, if matches { t } else { t - 1 }, "j {j} p {p} value {value} x_j {xj} W {w}");
                    }
                }
            }
        }
    }
}

#[test]
fn one_chunk_recovers_exactly_its_labels() {
    let mut rng = ChaCha20Rng::seed_from_u64(1684);
    let keys = WotsKeys::new(1, &mut rng);
    let delta = S(rng.random());
    let (table, labels0) = wots_translation::build(&keys, &rng.random(), delta);
    assert_eq!(table.grid.len(), GRID);
    assert_eq!(table.bytes(), 43_920, "24 bits of 112 points and 57 cells, 16 B each");
    for j in 0..DIGITS {
        for xj in 0..=K as u8 {
            let mut x: [u8; DIGITS] = core::array::from_fn(|_| rng.random_range(0..=K as u8));
            x[j] = xj;
            let sig = keys.sign(&bits_of(&x));
            assert!(wots_translation::chunk_verifies(&keys.ends[0], &sig.values[0], &sig.nodes[0]));
            let view = wots_translation::view(&table, 0, &sig.values[0], &sig.nodes[0]);
            for jj in 0..DIGITS {
                for p in 0..D {
                    let bit = (x[jj] >> p) & 1 == 1;
                    for value in [false, true] {
                        let got = wots_translation::recover(&table, 0, &view, jj, p, value);
                        if value == bit {
                            assert_eq!(got, Some(label(&labels0, delta, 0, jj, p, value)), "x {x:?} digit {jj} bit {p}");
                        } else {
                            assert_eq!(got, None, "x {x:?} digit {jj} bit {p}: the other label stays one point short");
                        }
                    }
                }
            }
            // And the challenger's reading gives the same.
            let read = wots_translation::read_labels(&keys.ends, &table, &sig);
            for (b, (value, l)) in read.iter().enumerate() {
                assert_eq!(*value, bits_of(&x)[b]);
                assert_eq!(*l, label(&labels0, delta, 0, b / D, b % D, *value));
            }
        }
    }
}

#[test]
fn hashing_forward_unlocks_nothing() {
    let mut rng = ChaCha20Rng::seed_from_u64(1685);
    let keys = WotsKeys::new(1, &mut rng);
    let delta = S(rng.random());
    let (table, labels0) = wots_translation::build(&keys, &rng.random(), delta);
    for _ in 0..8 {
        let x: [u8; DIGITS] = core::array::from_fn(|_| rng.random_range(0..=K as u8));
        let sig = keys.sign(&bits_of(&x));
        let (values, nodes) = (&sig.values[0], &sig.nodes[0]);
        let honest = wots_translation::view(&table, 0, values, nodes);
        // Every view the signature yields: any later grid cell, with each
        // digit node hashed forward, one digit at a time and all at once.
        let (u, r) = (values[DIGITS] as usize, values[DIGITS + 1] as usize);
        let mut views = Vec::new();
        for uu in u..RADIX {
            for rr in r..RADIX {
                if RADIX * uu + rr > W_MAX {
                    continue;
                }
                let mut v: [u8; CHAINS] = *values;
                let mut n = *nodes;
                v[DIGITS] = uu as u8;
                v[DIGITS + 1] = rr as u8;
                n[DIGITS] = wots_translation::forward(&nodes[DIGITS], uu - u);
                n[DIGITS + 1] = wots_translation::forward(&nodes[DIGITS + 1], rr - r);
                let base = wots_translation::view(&table, 0, &v, &n);
                assert_eq!(base.w, RADIX * uu + rr);
                views.push(base.clone());
                for i in 0..DIGITS {
                    for s in 1..=K - x[i] as usize {
                        let mut f = base.clone();
                        f.low[i] += s as u8;
                        f.nodes[i] = wots_translation::forward(&nodes[i], s);
                        views.push(f);
                    }
                }
                let mut all = base.clone();
                for i in 0..DIGITS {
                    let s = (K - x[i] as usize).min(1 + i % 3);
                    all.low[i] += s as u8;
                    all.nodes[i] = wots_translation::forward(&nodes[i], s);
                }
                views.push(all);
            }
        }
        assert!(views.len() > 1);
        for view in &views {
            for j in 0..DIGITS {
                for p in 0..D {
                    let bit = (x[j] >> p) & 1 == 1;
                    // The label of the other value never opens, and the one
                    // of the signed value opens only as itself.
                    assert_eq!(wots_translation::recover(&table, 0, view, j, p, !bit), None, "x {x:?} digit {j} bit {p}");
                    if let Some(l) = wots_translation::recover(&table, 0, view, j, p, bit) {
                        assert_eq!(l, label(&labels0, delta, 0, j, p, bit));
                    }
                }
            }
        }
        // The honest view is the one that opens everything.
        for (j, &xj) in x.iter().enumerate() {
            for p in 0..D {
                assert!(wots_translation::recover(&table, 0, &honest, j, p, (xj >> p) & 1 == 1).is_some());
            }
        }
    }
}

#[test]
fn no_shift_opens_an_unearned_label() {
    // `recover` trusts the table's own shift. An adversary need not: it may
    // assume either shift, i.e. that `W` or `W + 1` coefficients are unknown
    // and the rest are `H'(id ‖ κ_{m - shift})`. Neither opens the label of
    // the value not signed; if the table's coefficients had fewer unknowns
    // than its shift says, one of them would, and give Δ.
    let mut rng = ChaCha20Rng::seed_from_u64(1688);
    let keys = WotsKeys::new(1, &mut rng);
    let delta = S(rng.random());
    let (table, labels0) = wots_translation::build(&keys, &rng.random(), delta);
    let mut messages: Vec<[u8; DIGITS]> = vec![[K as u8; DIGITS], [0; DIGITS]];
    messages.extend((0..30).map(|_| core::array::from_fn(|_| rng.random_range(0..=K as u8))));
    for x in messages {
        let sig = keys.sign(&bits_of(&x));
        let view = wots_translation::view(&table, 0, &sig.values[0], &sig.nodes[0]);
        for j in 0..DIGITS {
            for p in 0..D {
                let unearned = (x[j] >> p) & 1 == 0;
                let other = label(&labels0, delta, 0, j, p, unearned);
                for d in 0..=1 {
                    let got = wots_translation::recover_with_shift(&table, 0, &view, j, p, unearned, d);
                    assert_ne!(got, Some(other), "x {x:?} digit {j} bit {p} shift {d}");
                }
            }
        }
    }
}

#[test]
fn instances_under_one_key_are_separate() {
    // Two garblings under one WOTS key. Their pads differ: each carries its
    // instance's tag, so XORing the two tables cancels no pad. And a signed
    // view of instance A, applied to instance B's table, opens none of B's
    // labels.
    let mut rng = ChaCha20Rng::seed_from_u64(1689);
    let keys = WotsKeys::new(1, &mut rng);
    let delta_a = S(rng.random());
    let delta_b = S(rng.random());
    let (table_a, _) = wots_translation::build(&keys, &rng.random(), delta_a);
    let (table_b, labels0_b) = wots_translation::build(&keys, &rng.random(), delta_b);
    let x: [u8; DIGITS] = [3, 0, 7, 5, 1, 6, 2, 4];
    let sig = keys.sign(&bits_of(&x));
    assert_ne!(table_a.tag, table_b.tag);
    for (node, l) in [(&sig.nodes[0][0], 0), (&sig.nodes[0][5], 56)] {
        for bit in [0, CHUNK_BITS - 1] {
            let ident = wots_translation::id(bit, true);
            assert_ne!(wots_translation::point_pad(&table_a.tag, node, &ident, l), wots_translation::point_pad(&table_b.tag, node, &ident, l));
        }
    }
    let (s1, s2) = (&sig.nodes[0][DIGITS], &sig.nodes[0][DIGITS + 1]);
    assert_ne!(wots_translation::grid_pad(&table_a.tag, 0, 1, 2, s1, s2), wots_translation::grid_pad(&table_b.tag, 0, 1, 2, s1, s2));
    let view_a = wots_translation::view(&table_a, 0, &sig.values[0], &sig.nodes[0]);
    for j in 0..DIGITS {
        for p in 0..D {
            for value in [false, true] {
                let real = label(&labels0_b, delta_b, 0, j, p, value);
                assert_ne!(wots_translation::recover(&table_b, 0, &view_a, j, p, value), Some(real), "digit {j} bit {p} value {value}");
            }
        }
    }
}

#[test]
fn chunks_have_independent_thresholds() {
    // Chunk 0 is all ones, W = 0: its grid cell gives κ_0 of chunk 0. Used as
    // a starting κ for chunk 1, it opens none of chunk 1's labels.
    let mut rng = ChaCha20Rng::seed_from_u64(1686);
    let keys = WotsKeys::new(2, &mut rng);
    let delta = S(rng.random());
    let (table, labels0) = wots_translation::build(&keys, &rng.random(), delta);
    let x1: [u8; DIGITS] = [0, 1, 2, 3, 4, 5, 6, 0];
    let mut bits = vec![true; CHUNK_BITS];
    bits.extend(bits_of(&x1));
    let sig = keys.sign(&bits);
    let low = wots_translation::view(&table, 0, &sig.values[0], &sig.nodes[0]);
    assert_eq!(low.w, 0);
    let honest = wots_translation::view(&table, 1, &sig.values[1], &sig.nodes[1]);
    assert!(honest.w > 0);
    let spliced = wots_translation::View { w: 0, kappa: low.kappa, ..honest.clone() };
    for j in 0..DIGITS {
        for p in 0..D {
            for value in [false, true] {
                let real = label(&labels0, delta, 1, j, p, value);
                let got = wots_translation::recover(&table, 1, &spliced, j, p, value);
                assert_ne!(got, Some(real), "digit {j} bit {p} value {value}");
            }
        }
    }
}

#[test]
fn labels_are_free_xor_pairs() {
    let mut rng = ChaCha20Rng::seed_from_u64(1687);
    let keys = WotsKeys::new(2, &mut rng);
    let delta = S(rng.random());
    let (table, labels0) = wots_translation::build(&keys, &rng.random(), delta);
    let ones = keys.sign(&[true; 2 * CHUNK_BITS]);
    let zeros = keys.sign(&[false; 2 * CHUNK_BITS]);
    let read1 = wots_translation::read_labels(&keys.ends, &table, &ones);
    let read0 = wots_translation::read_labels(&keys.ends, &table, &zeros);
    let mut seen = std::collections::HashSet::new();
    for b in 0..2 * CHUNK_BITS {
        assert_eq!(read0[b], (false, labels0[b]));
        assert_eq!(read1[b], (true, labels0[b] ^ delta), "bit {b}: label1 = label0 ⊕ Δ");
        assert!(seen.insert(read0[b].1) && seen.insert(read1[b].1), "bit {b}: every label is distinct");
    }
}

#[test]
fn matches_the_worked_examples() {
    // The paper's rule (section 4.3) at any K: δ = 1 - B_K, h_k = B_k - B_{k+1} + 1.
    let rule = |kk: usize, p: usize, b: bool| -> (usize, Vec<usize>) {
        let has = |k: usize| usize::from(((k >> p) & 1 == 1) == b);
        (1 - has(kk), (0..kk).map(|k| has(k) + 1 - has(k + 1)).collect())
    };
    // Section 5.1, d = 1, and 5.2, d = 2 (h_0 first; the paper lists h_2 first).
    assert_eq!(rule(1, 0, true), (0, vec![0]));
    assert_eq!(rule(1, 0, false), (1, vec![2]));
    assert_eq!(rule(3, 1, true), (0, vec![1, 0, 1]));
    assert_eq!(rule(3, 1, false), (1, vec![1, 2, 1]));
    assert_eq!(rule(3, 0, true), (0, vec![0, 2, 0]));
    assert_eq!(rule(3, 0, false), (1, vec![2, 0, 2]));
    // Our d = 3 helpers are that rule, and the bit 1 rows of WOTS-Translation.md.
    for p in 0..D {
        for value in [false, true] {
            assert_eq!(rule(K, p, value), (wots_translation::shift(value), wots_translation::helpers(p, value).to_vec()));
        }
    }
    assert_eq!(wots_translation::helpers(1, true), [1, 0, 1, 2, 1, 0, 1]);
    assert_eq!(wots_translation::helpers(1, false), [1, 2, 1, 0, 1, 2, 1]);

    // The note's example chunk: digits (5, 2, 6, 0, 7, 3, 1, 4), W = 28 = 8 * 3 + 4.
    let mut rng = ChaCha20Rng::seed_from_u64(1690);
    let keys = WotsKeys::new(1, &mut rng);
    let delta = S(rng.random());
    let (table, labels0) = wots_translation::build(&keys, &rng.random(), delta);
    let x = [5, 2, 6, 0, 7, 3, 1, 4];
    let sig = keys.sign(&bits_of(&x));
    assert_eq!(sig.values[0][DIGITS..], [3, 4]);
    let view = wots_translation::view(&table, 0, &sig.values[0], &sig.nodes[0]);
    assert_eq!(view.w, 28);
    // Digit 1 (x = 5 = 101): per label, (bit, value, points it has, opens).
    for (p, value, has, opens) in [
        (2, true, 28, true),
        (2, false, 28, false),
        (1, true, 27, false),
        (1, false, 29, true),
        (0, true, 28, true),
        (0, false, 28, false),
    ] {
        let opened = wots_translation::layout(0, p, value).iter().filter(|&&(i, k)| k >= x[i] as usize).count();
        assert_eq!(opened, has, "bit {p} = {value}");
        assert_eq!(view.w + wots_translation::shift(value), if opens { has } else { has + 1 });
        let got = wots_translation::recover(&table, 0, &view, 0, p, value);
        assert_eq!(got, opens.then(|| label(&labels0, delta, 0, 0, p, value)), "bit {p} = {value}");
    }
}

#[test]
fn grid_cells_below_w_stay_closed() {
    // A cell (u', r') with u' < u or r' < r needs a checksum node below the
    // signed one. Keyed with the nodes the signature does give, hashed forward
    // as far as needed, it decrypts to no κ that opens an unearned label.
    let mut rng = ChaCha20Rng::seed_from_u64(1691);
    let keys = WotsKeys::new(1, &mut rng);
    let delta = S(rng.random());
    let (table, labels0) = wots_translation::build(&keys, &rng.random(), delta);
    let x: [u8; DIGITS] = [2, 5, 3, 6, 1, 4, 3, 2];
    let sig = keys.sign(&bits_of(&x));
    let (values, nodes) = (&sig.values[0], &sig.nodes[0]);
    let (u, r) = (values[DIGITS] as usize, values[DIGITS + 1] as usize);
    assert!(u > 0 && r > 0, "cells below in both directions");
    let honest = wots_translation::view(&table, 0, values, nodes);
    let mut closed = 0;
    for uu in 0..RADIX {
        for rr in 0..RADIX {
            if RADIX * uu + rr > W_MAX || (uu >= u && rr >= r) {
                continue;
            }
            closed += 1;
            let s1 = wots_translation::forward(&nodes[DIGITS], uu.saturating_sub(u));
            let s2 = wots_translation::forward(&nodes[DIGITS + 1], rr.saturating_sub(r));
            let w = RADIX * uu + rr;
            let kappa: [u8; 16] = core::array::from_fn(|i| {
                table.grid[wots_translation::cell(uu, rr)][i] ^ wots_translation::grid_pad(&table.tag, 0, uu, rr, &s1, &s2)[i]
            });
            let guess = wots_translation::View { w, kappa, ..honest.clone() };
            for (j, &xj) in x.iter().enumerate() {
                for p in 0..D {
                    let unearned = (xj >> p) & 1 == 0;
                    let other = label(&labels0, delta, 0, j, p, unearned);
                    for d in 0..=1 {
                        let got = wots_translation::recover_with_shift(&table, 0, &guess, j, p, unearned, d);
                        assert_ne!(got, Some(other), "cell ({uu}, {rr}) digit {j} bit {p}");
                    }
                }
            }
        }
    }
    assert!(closed > 0);
}

#[test]
fn polynomial_ids_are_unique() {
    // Every (bit, value) has its own id. A shared id would share coefficients
    // between polynomials: with c_m = H'(id ‖ κ_{m-δ}), a label of 1 would be
    // a coefficient of the label of 0, one unknown fewer.
    let bits = 2 * 1_041_024;
    let mut seen = std::collections::HashSet::with_capacity(2 * bits);
    for bit in 0..bits {
        for value in [false, true] {
            assert!(seen.insert(wots_translation::id(bit, value)), "bit {bit} value {value}");
        }
    }
}
