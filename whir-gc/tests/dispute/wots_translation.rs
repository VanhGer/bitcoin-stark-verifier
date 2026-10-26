//! The WOTS-translation input layer: chunked Winternitz signatures on chain,
//! and the translation table of ePrint 2026/1684 off chain, which turns a
//! signed chunk into exactly the garbled labels of its bits.
//!
//! This is not the plain WOTS of BitVM2, which commits to values a script
//! then checks: here the chunk layout, its shared checksum and every key
//! exist to feed the translation table. A key signs once, here: its nodes key
//! the table's pads, so it must not also serve as a plain WOTS commitment.
//!
//! **Signature.** Input bits are cut into chunks of 8 digits of 3 bits. Each
//! digit `x` has a HASH160 chain of `K = 7` steps; signing reveals the node
//! `Y^(x)`, and anyone can hash it forward, never back. The checksum
//! `W = Σ (7 - x_i) ≤ 56` is written `W = 8u + r` and `u` and `r` are signed
//! on two more chains, so raising a digit needs a lower checksum node.
//!
//! **Table, per chunk.**
//! - A chain `κ_0 → … → κ_56`, `κ_{m+1} = H(κ_m)`, from the instance seed.
//! - An entry grid: cell `(u, r)`, `8u + r ≤ 56`, holds `κ_{8u+r}` under the
//!   checksum nodes `S_1^(u)` and `S_2^(r)`. The signed `(u, r)` opens `κ_W`,
//!   and hashing forward every later `κ`, never an earlier one.
//! - Per input bit and value `b`, a polynomial over `GF(2^128)` of degree
//!   `55 + δ`, `δ = 1 - b`, with `c_m = H'(id ‖ κ_{m-δ})` for `m ≥ δ`. The
//!   label is `P(0)`: for `b = 1` it is `c_0 = H'(id ‖ κ_0)`, and for `b = 0`
//!   the free `c_0`, set to that `⊕ Δ` so the labels are a free-XOR pair.
//!   Holding `κ_W` gives every `c_m` with `m ≥ W + δ`, leaving `W + δ`
//!   unknowns.
//! - Its points, each under one chain node: one under each node `0..=6` of
//!   every other digit of the chunk, and `h_k = 1 + B_k - B_{k+1}` under node
//!   `k` of its own digit, where `B_k` is whether value `k` has the bit at `b`.
//!   A signed chunk then opens exactly `W + δ` points of the labels its digits
//!   carry and one fewer of the others (paper section 4.3).
//!
//! The pads and coefficients are Blake3 under a one-byte domain tag; every
//! input is fixed-length after it. They carry a public instance tag, so two
//! garblings under one WOTS key share no pad.

use bitcoin::hashes::{hash160, Hash};
use bitcoin_script::{define_pushable, script};
use garbled_snark_verifier::core::s::S;
use p3_binary_field::Ghash128;
use p3_field::{PrimeCharacteristicRing, RawDataSerializable};
use p3_maybe_rayon::prelude::*;
use rand::Rng;
use rand_chacha::ChaCha20Rng;

define_pushable!();

/// Bits per digit, the largest digit, digits and chains per chunk.
pub const D: usize = 3;
pub const K: usize = (1 << D) - 1;
pub const DIGITS: usize = 8;
pub const CHAINS: usize = DIGITS + 2;
pub const CHUNK_BITS: usize = D * DIGITS;
/// The largest checksum, and its radix: `W = RADIX u + r`.
pub const W_MAX: usize = DIGITS * K;
pub const RADIX: usize = K + 1;
/// Points of a label, by value: `7 * 7` base points and 8 or 6 helpers.
pub const POINTS: [usize; 2] = [57, 55];
pub const POINTS_PER_BIT: usize = POINTS[0] + POINTS[1];
/// Grid cells per chunk: every `(u, r)` with `8u + r ≤ 56`.
pub const GRID: usize = 57;

pub type Node = [u8; 20];
pub type Block = [u8; 16];

pub fn hash_node(n: &Node) -> Node {
    hash160::Hash::hash(n).to_byte_array()
}

/// `n` hashed `steps` times.
pub fn forward(n: &Node, steps: usize) -> Node {
    (0..steps).fold(*n, |acc, _| hash_node(&acc))
}

const KAPPA0: u8 = 0;
const KAPPA_STEP: u8 = 1;
const COEFFICIENT: u8 = 2;
const POINT_PAD: u8 = 3;
const GRID_PAD: u8 = 4;
const INSTANCE: u8 = 5;

fn prf(tag: u8, parts: &[&[u8]]) -> Block {
    let mut h = blake3::Hasher::new();
    h.update(&[tag]);
    for p in parts {
        h.update(p);
    }
    h.finalize().as_bytes()[..16].try_into().unwrap()
}

fn xor(a: Block, b: Block) -> Block {
    core::array::from_fn(|i| a[i] ^ b[i])
}

fn field(b: Block) -> Ghash128 {
    Ghash128::from_le_bytes(b)
}

fn block(f: Ghash128) -> Block {
    let mut b = [0u8; 16];
    for (o, v) in b.iter_mut().zip(f.into_bytes()) {
        *o = v;
    }
    b
}

/// The polynomial id of input bit `bit` at `value`.
pub fn id(bit: usize, value: bool) -> [u8; 8] {
    (2 * bit as u64 + u64::from(value)).to_le_bytes()
}

/// The public x-coordinate of a label's point `l`: `l + 1`, nonzero and
/// distinct.
fn x_of(l: usize) -> Ghash128 {
    Ghash128::from_le_bytes((l as u128 + 1).to_le_bytes())
}

fn kappa_step(k: &Block) -> Block {
    prf(KAPPA_STEP, &[k])
}

/// `κ_from .. κ_W_MAX` from `κ_from`, indexed from `from`.
fn kappa_chain(kappa: Block, from: usize) -> Vec<Block> {
    let mut chain = vec![kappa];
    for _ in from..W_MAX {
        let next = kappa_step(chain.last().unwrap());
        chain.push(next);
    }
    chain
}

fn coefficient(tag: &Block, id: &[u8; 8], kappa: &Block) -> Ghash128 {
    field(prf(COEFFICIENT, &[tag, id, kappa]))
}

pub fn point_pad(tag: &Block, node: &Node, id: &[u8; 8], l: usize) -> Block {
    prf(POINT_PAD, &[tag, node, id, &[l as u8]])
}

pub fn grid_pad(tag: &Block, chunk: usize, u: usize, r: usize, s1: &Node, s2: &Node) -> Block {
    prf(GRID_PAD, &[tag, &(chunk as u64).to_le_bytes(), &[u as u8, r as u8], s1, s2])
}

/// The grid cell of `(u, r)`. The valid cells, row by row, are exactly
/// `W = 0..=56`, so a cell's index is its `W`.
pub fn cell(u: usize, r: usize) -> usize {
    assert!(RADIX * u + r <= W_MAX && r < RADIX);
    RADIX * u + r
}

/// The threshold shift `δ = 1 - B_K`: value `K` has every bit set, so the
/// labels of 1 open there with no helper and those of 0 need one more point.
pub fn shift(value: bool) -> usize {
    usize::from(!value)
}

/// `h_k = 1 + B_k - B_{k+1}` for the label of bit `p` at `value`.
pub fn helpers(p: usize, value: bool) -> [usize; K] {
    let has = |k: usize| usize::from(((k >> p) & 1 == 1) == value);
    core::array::from_fn(|k| 1 + has(k) - has(k + 1))
}

/// The points of the label of digit `j`, bit `p`, at `value`, in order: the
/// digit and chain node each is under.
pub fn layout(j: usize, p: usize, value: bool) -> Vec<(usize, usize)> {
    let h = helpers(p, value);
    let mut out = Vec::with_capacity(POINTS[usize::from(value)]);
    for i in 0..DIGITS {
        for (k, &hk) in h.iter().enumerate() {
            let count = if i == j { hk } else { 1 };
            out.extend(std::iter::repeat_n((i, k), count));
        }
    }
    assert_eq!(out.len(), POINTS[usize::from(value)]);
    out
}

/// The digits of a chunk's 24 bits, least significant bit first, with the
/// checksum digits `u` and `r`.
pub fn chunk_values(bits: &[bool]) -> [u8; CHAINS] {
    assert_eq!(bits.len(), CHUNK_BITS);
    let mut v = [0u8; CHAINS];
    for i in 0..DIGITS {
        v[i] = (0..D).map(|p| u8::from(bits[D * i + p]) << p).sum();
    }
    let w: usize = v[..DIGITS].iter().map(|&x| K - x as usize).sum();
    v[DIGITS] = (w / RADIX) as u8;
    v[DIGITS + 1] = (w % RADIX) as u8;
    v
}

/// The operator's WOTS key: per chunk, ten chain seeds and their public ends.
pub struct WotsKeys {
    seeds: Vec<[Node; CHAINS]>,
    pub ends: Vec<[Node; CHAINS]>,
}

/// A signature: per chunk, each chain's value and revealed node.
#[derive(Clone)]
pub struct Signature {
    pub values: Vec<[u8; CHAINS]>,
    pub nodes: Vec<[Node; CHAINS]>,
}

impl WotsKeys {
    pub fn new(chunks: usize, rng: &mut ChaCha20Rng) -> Self {
        let seeds: Vec<[Node; CHAINS]> = (0..chunks).map(|_| core::array::from_fn(|_| rng.random())).collect();
        let ends = seeds.iter().map(|s| s.map(|n| forward(&n, K))).collect();
        Self { seeds, ends }
    }

    pub fn chunks(&self) -> usize {
        self.seeds.len()
    }

    pub fn sign(&self, bits: &[bool]) -> Signature {
        assert_eq!(bits.len(), self.chunks() * CHUNK_BITS);
        let values: Vec<[u8; CHAINS]> = bits.chunks(CHUNK_BITS).map(chunk_values).collect();
        let nodes = values
            .iter()
            .zip(&self.seeds)
            .map(|(v, s)| core::array::from_fn(|i| forward(&s[i], v[i] as usize)))
            .collect();
        Signature { values, nodes }
    }
}

/// What the Assert script checks of a chunk, off chain: every node hashes to
/// its end, and the checksum digits carry `W`.
pub fn chunk_verifies(ends: &[Node; CHAINS], values: &[u8; CHAINS], nodes: &[Node; CHAINS]) -> bool {
    let chains = (0..CHAINS).all(|i| values[i] as usize <= K && forward(&nodes[i], K - values[i] as usize) == ends[i]);
    let digits: usize = values[..DIGITS].iter().map(|&x| x as usize).sum();
    chains && digits + RADIX * values[DIGITS] as usize + values[DIGITS + 1] as usize == W_MAX
}

/// The translation table, all public: per chunk `GRID` cells, per input bit
/// `POINTS_PER_BIT` points (value 0's, then value 1's).
pub struct Table {
    pub tag: Block,
    pub grid: Vec<Block>,
    pub points: Vec<Block>,
}

impl Table {
    pub fn bytes(&self) -> usize {
        16 * (self.grid.len() + self.points.len())
    }

    fn label_points(&self, bit: usize, value: bool) -> &[Block] {
        let at = bit * POINTS_PER_BIT + if value { POINTS[0] } else { 0 };
        &self.points[at..at + POINTS[usize::from(value)]]
    }
}

/// Horner's rule.
fn evaluate(coefficients: &[Ghash128], x: Ghash128) -> Ghash128 {
    coefficients.iter().rev().fold(Ghash128::ZERO, |acc, &c| acc * x + c)
}

/// The operator's build, from its WOTS key, the instance seed and `Δ`.
/// Returns the table and the false label of every input bit.
pub fn build(keys: &WotsKeys, seed: &[u8; 32], delta: S) -> (Table, Vec<S>) {
    let tag = prf(INSTANCE, &[seed]);
    let delta = field(delta.0);
    let per_chunk: Vec<(Vec<Block>, Vec<Block>, Vec<S>)> = (0..keys.chunks())
        .into_par_iter()
        .map(|c| {
            let kappa = kappa_chain(prf(KAPPA0, &[seed, &(c as u64).to_le_bytes()]), 0);
            let nodes: [[Node; K + 1]; CHAINS] = keys.seeds[c].map(|s| core::array::from_fn(|k| forward(&s, k)));
            let mut grid = Vec::with_capacity(GRID);
            for u in 0..RADIX {
                for r in 0..RADIX {
                    if RADIX * u + r <= W_MAX {
                        let pad = grid_pad(&tag, c, u, r, &nodes[DIGITS][u], &nodes[DIGITS + 1][r]);
                        grid.push(xor(kappa[RADIX * u + r], pad));
                    }
                }
            }
            assert_eq!(grid.len(), GRID);
            let mut points = Vec::with_capacity(CHUNK_BITS * POINTS_PER_BIT);
            let mut labels0 = Vec::with_capacity(CHUNK_BITS);
            for j in 0..DIGITS {
                for p in 0..D {
                    let bit = c * CHUNK_BITS + D * j + p;
                    let label1 = coefficient(&tag, &id(bit, true), &kappa[0]);
                    let label0 = label1 + delta;
                    labels0.push(S(block(label0)));
                    for value in [false, true] {
                        let d = shift(value);
                        let ident = id(bit, value);
                        let coefficients: Vec<Ghash128> = (0..W_MAX + d)
                            .map(|m| if m < d { label0 } else { coefficient(&tag, &ident, &kappa[m - d]) })
                            .collect();
                        for (l, (i, k)) in layout(j, p, value).into_iter().enumerate() {
                            let y = evaluate(&coefficients, x_of(l));
                            points.push(xor(block(y), point_pad(&tag, &nodes[i][k], &ident, l)));
                        }
                    }
                }
            }
            (grid, points, labels0)
        })
        .collect();
    let mut table = Table { tag, grid: Vec::new(), points: Vec::new() };
    let mut labels0 = Vec::new();
    for (g, p, l) in per_chunk {
        table.grid.extend(g);
        table.points.extend(p);
        labels0.extend(l);
    }
    (table, labels0)
}

/// What a holder of chain nodes and one grid cell can open in a chunk: per
/// digit its lowest node, and the lowest `κ` with its index.
#[derive(Clone)]
pub struct View {
    pub low: [u8; DIGITS],
    pub nodes: [Node; DIGITS],
    pub w: usize,
    pub kappa: Block,
}

/// The view a signed chunk gives: its digit nodes, and `κ_W` from the cell
/// its checksum nodes open.
pub fn view(table: &Table, chunk: usize, values: &[u8; CHAINS], nodes: &[Node; CHAINS]) -> View {
    let (u, r) = (values[DIGITS] as usize, values[DIGITS + 1] as usize);
    let pad = grid_pad(&table.tag, chunk, u, r, &nodes[DIGITS], &nodes[DIGITS + 1]);
    View {
        low: values[..DIGITS].try_into().unwrap(),
        nodes: nodes[..DIGITS].try_into().unwrap(),
        w: RADIX * u + r,
        kappa: xor(table.grid[chunk * GRID + cell(u, r)], pad),
    }
}

/// The label of digit `j`, bit `p`, at `value` from `view`, if the view opens
/// enough of its points: decrypt every point under a reachable node, subtract
/// the coefficients `κ` gives, and interpolate the rest at 0.
pub fn recover(table: &Table, chunk: usize, view: &View, j: usize, p: usize, value: bool) -> Option<S> {
    recover_with_shift(table, chunk, view, j, p, value, shift(value))
}

/// `recover` assuming the label's coefficients are offset by `d`: `W + d`
/// unknowns, and `c_m = H'(id ‖ κ_{m-d})` for `W + d ≤ m ≤ 55 + δ`, the
/// public degree. An adversary is free to try either offset; only the
/// label's own opens it, and only when earned.
pub fn recover_with_shift(table: &Table, chunk: usize, view: &View, j: usize, p: usize, value: bool, d: usize) -> Option<S> {
    let bit = chunk * CHUNK_BITS + D * j + p;
    let ident = id(bit, value);
    let t = view.w + d;
    let kappa = kappa_chain(view.kappa, view.w);
    // c_m for m ≥ t, from κ_{m-δ}, m - δ ≥ W.
    let known: Vec<Ghash128> =
        (t..W_MAX + shift(value)).map(|m| coefficient(&table.tag, &ident, &kappa[m - d - view.w])).collect();
    let cts = table.label_points(bit, value);
    let mut xs = Vec::with_capacity(t);
    let mut ys = Vec::with_capacity(t);
    for (l, (i, k)) in layout(j, p, value).into_iter().enumerate() {
        if k >= view.low[i] as usize && xs.len() < t {
            let node = forward(&view.nodes[i], k - view.low[i] as usize);
            let x = x_of(l);
            let y = field(xor(cts[l], point_pad(&table.tag, &node, &ident, l)));
            // Subtract the known high part: x^t Σ c_m x^(m-t).
            let high = evaluate(&known, x) * x.exp_u64(t as u64);
            xs.push(x);
            ys.push(y + high);
        }
    }
    if xs.len() < t {
        return None;
    }
    if t == 0 {
        return Some(S(block(known[0])));
    }
    Some(S(block(interpolate_at_zero(&xs, &ys))))
}

/// Lagrange interpolation at 0: `Σ y_l Π_{q≠l} x_q / (x_q - x_l)`, the
/// denominators inverted in one batch.
fn interpolate_at_zero(xs: &[Ghash128], ys: &[Ghash128]) -> Ghash128 {
    let n = xs.len();
    let numerator = xs.iter().fold(Ghash128::ONE, |acc, &x| acc * x);
    let denominators: Vec<Ghash128> = (0..n)
        .map(|l| (0..n).filter(|&q| q != l).fold(xs[l], |acc, q| acc * (xs[q] + xs[l])))
        .collect();
    // Batch inversion: prefix products, one inverse, then back.
    let mut prefix = Vec::with_capacity(n);
    let mut acc = Ghash128::ONE;
    for &d in &denominators {
        prefix.push(acc);
        acc *= d;
    }
    let mut inverse = acc.invert_or_zero();
    let mut sum = Ghash128::ZERO;
    for l in (0..n).rev() {
        let inv_l = inverse * prefix[l];
        inverse *= denominators[l];
        sum += ys[l] * inv_l;
    }
    sum * numerator
}

/// The challenger's reading of an Assert: per input bit its value, and its
/// label through the table. Panics on a chunk the Assert script would reject.
pub fn read_labels(ends: &[[Node; CHAINS]], table: &Table, sig: &Signature) -> Vec<(bool, S)> {
    assert_eq!(sig.values.len(), ends.len(), "a signature per chunk of the key");
    assert_eq!(table.grid.len(), ends.len() * GRID, "a table per chunk of the key");
    (0..ends.len())
        .into_par_iter()
        .flat_map_iter(|c| {
            assert!(chunk_verifies(&ends[c], &sig.values[c], &sig.nodes[c]), "chunk {c}: the Assert script checked it");
            let v = view(table, c, &sig.values[c], &sig.nodes[c]);
            (0..DIGITS)
                .flat_map(move |j| (0..D).map(move |p| (j, p)))
                .map(|(j, p)| {
                    let value = (v.low[j] >> p) & 1 == 1;
                    (value, recover(table, c, &v, j, p, value).expect("a signed bit opens its label"))
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

/// One chain of 3-bit digits: `node digit` on top, the digit left on the
/// altstack. The node is hashed 7 times keeping every value, and the digit
/// picks the one that must be the end. The digit is not range-checked: one
/// outside `0..=7` makes `OP_PICK` fail or reach a deeper item, a later
/// chain's node or digit. The attacker may put this chain's end there, but
/// that later chain then checks it: as a node it must hash to its own end, a
/// HASH160 preimage, and as a digit 20 bytes are no number.
pub fn verify_chain(end: &Node) -> bitcoin::ScriptBuf {
    let w = K + 1;
    script! {
        OP_DUP OP_TOALTSTACK
        OP_SWAP
        for _ in 0..K { OP_DUP OP_HASH160 }
        { w as u32 } OP_ROLL OP_PICK
        { end.to_vec() } OP_EQUALVERIFY
        for _ in 0..w / 2 { OP_2DROP }
    }
}

/// One chunk: its ten chains, then `Σ x_i + 8u + r = 56`.
pub fn chunk_lock(ends: &[Node; CHAINS]) -> bitcoin::ScriptBuf {
    script! {
        for end in ends { { verify_chain(end) } }
        // r, then u: 8u + r, plus the digits, is 56.
        OP_FROMALTSTACK OP_FROMALTSTACK
        for _ in 0..D { OP_DUP OP_ADD }
        OP_ADD
        for _ in 0..DIGITS { OP_FROMALTSTACK OP_ADD }
        { W_MAX as u32 } OP_EQUALVERIFY
    }
}

/// The Assert check of `ends`' chunks, without the final true.
pub fn assert_lock(ends: &[[Node; CHAINS]]) -> bitcoin::ScriptBuf {
    script! { for e in ends { { chunk_lock(e) } } }
}

/// The witness items of chunks `values`/`nodes`, bottom of the stack first,
/// so that chunk 0's chain 0 digit is on top. A digit is a minimal ScriptNum:
/// 0 is the empty item.
pub fn stack(values: &[[u8; CHAINS]], nodes: &[[Node; CHAINS]]) -> Vec<Vec<u8>> {
    let mut items = Vec::with_capacity(2 * CHAINS * values.len());
    for (v, n) in values.iter().zip(nodes).rev() {
        for i in (0..CHAINS).rev() {
            items.push(n[i].to_vec());
            items.push(if v[i] == 0 { vec![] } else { vec![v[i]] });
        }
    }
    items
}
