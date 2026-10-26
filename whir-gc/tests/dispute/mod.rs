//! The dispute's input layer, shared by the dispute tests: Lamport keys per
//! input bit, the translation ciphertexts that turn a revealed preimage into
//! that bit's garbled label, and the Assert and Disprove scripts. The
//! WOTS-translation input layer of ePrint 2026/1684, chunked WOTS plus its
//! translation table, is in `wots_translation`.

#![allow(dead_code)]

pub mod wots_translation;

use bitcoin::hashes::{hash160, sha256, Hash};
use bitcoin_script::{define_pushable, script};
use garbled_snark_verifier::core::s::S;
use rand::Rng;
use rand_chacha::ChaCha20Rng;

define_pushable!();

/// Preimages one Assert script can take: Bitcoin's 1000-item stack limit,
/// less the two items each check pushes on top of them.
pub const BITS_PER_SCRIPT: usize = 998;

/// The key a Lamport preimage opens a translation ciphertext with.
pub fn kdf(preimage: &[u8; 16], bit_index: usize, value: bool) -> S {
    let mut m = preimage.to_vec();
    m.extend_from_slice(&(bit_index as u64).to_le_bytes());
    m.push(u8::from(value));
    S::from_slice(&sha256::Hash::hash(&m).to_byte_array()[..16])
}

/// One Lamport key pair per input bit: the operator keeps the preimages and
/// publishes their `HASH160`s.
pub struct Lamport {
    pub preimages: Vec<[[u8; 16]; 2]>,
    pub hashes: Vec<[[u8; 20]; 2]>,
}

impl Lamport {
    pub fn new(bits: usize, rng: &mut ChaCha20Rng) -> Self {
        let preimages: Vec<[[u8; 16]; 2]> = (0..bits).map(|_| [rng.random(), rng.random()]).collect();
        let hashes = preimages.iter().map(|p| p.map(|s| hash160::Hash::hash(&s).to_byte_array())).collect();
        Self { preimages, hashes }
    }

    /// The translation ciphertexts, `[bit][value]`: the preimage of `value`
    /// opens the garbled label of `value` on that bit's input wire.
    pub fn translation(&self, label_of: impl Fn(usize, bool) -> S) -> Vec<[S; 2]> {
        (0..self.preimages.len())
            .map(|i| {
                core::array::from_fn(|b| {
                    let value = b == 1;
                    kdf(&self.preimages[i][b], i, value) ^ label_of(i, value)
                })
            })
            .collect()
    }

    /// What the operator reveals for `bits`.
    pub fn publish(&self, bits: &[bool]) -> Vec<[u8; 16]> {
        assert_eq!(bits.len(), self.preimages.len());
        bits.iter().enumerate().map(|(i, &b)| self.preimages[i][usize::from(b)]).collect()
    }
}

/// One Assert leaf: every bit's published preimage opens one of its hashes.
pub fn assert_lock(hashes: &[[[u8; 20]; 2]]) -> bitcoin::ScriptBuf {
    script! {
        for [h0, h1] in hashes {
            OP_HASH160 OP_DUP { h0.to_vec() } OP_EQUAL OP_SWAP { h1.to_vec() } OP_EQUAL OP_BOOLOR OP_VERIFY
        }
        OP_TRUE
    }
}

/// The witness of one Assert leaf: the first bit's preimage on top.
pub fn assert_witness(published: &[[u8; 16]]) -> bitcoin::ScriptBuf {
    script! { for p in published.iter().rev() { { p.to_vec() } } }
}

/// The Disprove leaf: the preimage of the reject label's hash.
pub fn disprove_lock(reject_label: &S) -> bitcoin::ScriptBuf {
    let h = sha256::Hash::hash(&reject_label.0).to_byte_array();
    script! { OP_SHA256 { h.to_vec() } OP_EQUAL }
}

/// Run `witness` then `lock` as one tapscript spend, stack limit enforced.
pub fn runs(witness: bitcoin::ScriptBuf, lock: bitcoin::ScriptBuf) -> bool {
    bitcoin_scriptexec::execute_script(script! { { witness } { lock } }).success
}

/// Whether `label` opens the Disprove leaf.
pub fn disproves(label: &S, reject_label: &S) -> bool {
    runs(script! { { label.0.to_vec() } }, disprove_lock(reject_label))
}

/// Every Assert leaf, `BITS_PER_SCRIPT` bits each, run on the published
/// preimages. Returns the number of leaves and whether all accepted.
pub fn assert_all(hashes: &[[[u8; 20]; 2]], published: &[[u8; 16]]) -> (usize, bool) {
    let mut leaves = 0;
    let mut ok = true;
    for (h, p) in hashes.chunks(BITS_PER_SCRIPT).zip(published.chunks(BITS_PER_SCRIPT)) {
        leaves += 1;
        ok &= runs(assert_witness(p), assert_lock(h));
    }
    (leaves, ok)
}

/// The challenger's reading of an Assert: each bit from which hash its
/// preimage opens, and the bit's label through the translation ciphertexts.
pub fn read_labels(hashes: &[[[u8; 20]; 2]], translation: &[[S; 2]], published: &[[u8; 16]]) -> Vec<(bool, S)> {
    published
        .iter()
        .enumerate()
        .map(|(i, p)| {
            let h = hash160::Hash::hash(p).to_byte_array();
            let value = if h == hashes[i][1] {
                true
            } else {
                assert_eq!(h, hashes[i][0], "bit {i}: the Assert script checked this preimage");
                false
            };
            (value, kdf(p, i, value) ^ translation[i][usize::from(value)])
        })
        .collect()
}
