//! Executable, transaction-bound cost fixture for the Assert of the WOTS
//! translation, `dispute::wots_translation`: 3-bit digits in chunks of 8,
//! each chunk's checksum `W = 8u + r` on two more chains, 10 chains per 24
//! bits.
//!
//! Every P2TR leaf is prefixed by a 64-byte SIGHASH_DEFAULT Schnorr check,
//! uses BIP341's NUMS internal key, and is serialized in a version-2
//! transaction with two P2TR outputs, as in `antichain_tx_cost`. Every signed
//! leaf is executed against its transaction with the stack limit on.
//! The aggregate is the signed reveal set, not a total on-chain cost:
//! funding is measured separately, and the rest of the dispute graph is not
//! constructed. The off-chain translation table is costed in `wots_translation_table`.
//!
//! The canonical chunk has digits `[1, 1, 1, 1, 1, 1, 1, 2]`, so `W = 47 =
//! 8 * 5 + 7`: every posted value is a one-byte ScriptNum, the all-nonzero
//! worst case. Each zero digit of real data saves exactly one witness byte/WU.

mod dispute;

use bitcoin::{
    absolute::LockTime,
    consensus::encode::serialize,
    hashes::Hash,
    key::{Keypair, Secp256k1},
    secp256k1::{Message, SecretKey, XOnlyPublicKey},
    sighash::{Prevouts, SighashCache, TapSighashType},
    taproot::{ControlBlock, LeafVersion, TapLeafHash, TaprootBuilder},
    transaction::Version,
    Address, Amount, Network, OutPoint, ScriptBuf, Sequence, Transaction, TxIn, TxOut, Txid,
    Witness,
};
use bitcoin_script::{define_pushable, script};
use bitvm_scriptexec::{Exec, ExecCtx, Options, TxTemplate};
use dispute::wots_translation::{self, Node, CHAINS, CHUNK_BITS, D, DIGITS, WotsKeys};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use std::str::FromStr;

define_pushable!();

/// The measured Keccak verifier's input, and the narrow-recursion verifier's;
/// the golden totals are pinned at both.
const KECCAK_INPUT_BITS: usize = 1_041_024;
const NARROW_INPUT_BITS: usize = 564_552;

/// The input size to serialize: `WHIR_GC_INPUT_BITS`, else the Keccak verifier's.
fn input_bits() -> usize {
    std::env::var("WHIR_GC_INPUT_BITS")
        .ok()
        .map_or(KECCAK_INPUT_BITS, |s| s.parse().expect("WHIR_GC_INPUT_BITS is a bit count"))
}

const CANONICAL_DIGITS: [u8; DIGITS] = [1, 1, 1, 1, 1, 1, 1, 2];
const MAX_CHUNKS_PER_INPUT: usize = 49;
const MAX_STACK_ITEMS: usize = 1_000;
const MAX_STANDARD_TX_WEIGHT: u64 = 400_000;
const FUNDING_SATS_PER_INPUT: u64 = 100_000;
const OUTPUT_SATS: u64 = 1_000;

fn internal_key() -> XOnlyPublicKey {
    // BIP341's H = lift_x(sha256(uncompressed_G)) NUMS point.
    XOnlyPublicKey::from_str("50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0")
        .expect("BIP341 NUMS internal key")
}

fn authorization_keypair(secp: &Secp256k1<bitcoin::secp256k1::All>) -> Keypair {
    let secret = SecretKey::from_slice(&[3u8; 32]).expect("fixed test signing key");
    Keypair::from_secret_key(secp, &secret)
}

/// Transaction authorization before the WOTS checks; the signature is the
/// top initial stack item.
fn authorized_leaf(authorization_key: XOnlyPublicKey, verifier: ScriptBuf) -> ScriptBuf {
    let mut bytes = Vec::with_capacity(34 + verifier.len());
    bytes.push(0x20);
    bytes.extend_from_slice(&authorization_key.serialize());
    bytes.push(0xad); // OP_CHECKSIGVERIFY
    bytes.extend_from_slice(verifier.as_bytes());
    ScriptBuf::from_bytes(bytes)
}

fn digit_bits(digits: &[u8; DIGITS]) -> Vec<bool> {
    digits.iter().flat_map(|&v| (0..D).map(move |p| (v >> p) & 1 == 1)).collect()
}

struct WotsInput {
    txin: TxIn,
    prevout: TxOut,
    tapscript: ScriptBuf,
    control: ControlBlock,
    output_key: XOnlyPublicKey,
    values: Vec<[u8; CHAINS]>,
    nodes: Vec<[Node; CHAINS]>,
}

impl WotsInput {
    fn chunks(&self) -> usize {
        self.values.len()
    }
}

/// A fresh WOTS key for `chunks` chunks of `digits`, signed, and its Assert
/// check as the only Taproot leaf.
fn wots_input(
    rng: &mut ChaCha20Rng,
    secp: &Secp256k1<bitcoin::secp256k1::All>,
    authorization_key: XOnlyPublicKey,
    funding_txid: Txid,
    funding_index: u32,
    digits: &[[u8; DIGITS]],
) -> WotsInput {
    let keys = WotsKeys::new(digits.len(), rng);
    let sig = keys.sign(&digits.iter().flat_map(digit_bits).collect::<Vec<_>>());
    let mut verifier = wots_translation::assert_lock(&keys.ends).into_bytes();
    verifier.push(0x51); // OP_TRUE
    let tapscript = authorized_leaf(authorization_key, ScriptBuf::from_bytes(verifier));

    let spend_info = TaprootBuilder::new()
        .add_leaf(0, tapscript.clone())
        .expect("one-leaf WOTS taptree")
        .finalize(secp, internal_key())
        .expect("one-leaf WOTS taptree is complete");
    let control = spend_info
        .control_block(&(tapscript.clone(), LeafVersion::TapScript))
        .expect("control block for the only leaf");
    let output_key = spend_info.output_key().to_x_only_public_key();
    assert_eq!(control.serialize().len(), 33, "depth-0 control block");
    assert!(control.verify_taproot_commitment(secp, output_key, tapscript.as_script()));

    WotsInput {
        txin: TxIn {
            previous_output: OutPoint::new(funding_txid, funding_index),
            script_sig: ScriptBuf::new(),
            sequence: Sequence::MAX,
            witness: Witness::new(),
        },
        prevout: TxOut {
            value: Amount::from_sat(FUNDING_SATS_PER_INPUT),
            script_pubkey: ScriptBuf::new_p2tr_tweaked(spend_info.output_key()),
        },
        tapscript,
        control,
        output_key,
        values: sig.values,
        nodes: sig.nodes,
    }
}

fn two_output_transaction(leaves: &[WotsInput], secp: &Secp256k1<bitcoin::secp256k1::All>) -> Transaction {
    let output_script = ScriptBuf::new_p2tr(secp, internal_key(), None);
    assert_eq!(output_script.len(), 34);
    Transaction {
        version: Version::TWO,
        lock_time: LockTime::ZERO,
        input: leaves.iter().map(|leaf| leaf.txin.clone()).collect(),
        output: vec![
            TxOut { value: Amount::from_sat(OUTPUT_SATS), script_pubkey: output_script.clone() },
            TxOut { value: Amount::from_sat(OUTPUT_SATS), script_pubkey: output_script },
        ],
    }
}

fn witness_arguments(witness: &Witness) -> Vec<Vec<u8>> {
    assert!(witness.len() >= 2);
    witness.iter().take(witness.len() - 2).map(<[u8]>::to_vec).collect()
}

/// Run a tapleaf against the real transaction and all prevouts, so that
/// OP_CHECKSIGVERIFY checks the BIP341 script-spend sighash.
fn execute_input(
    tx: &Transaction,
    prevouts: &[TxOut],
    input_index: usize,
    tapscript: &ScriptBuf,
    arguments: Vec<Vec<u8>>,
) -> (bool, usize) {
    let leaf_hash = TapLeafHash::from_script(tapscript.as_script(), LeafVersion::TapScript);
    let mut exec = Exec::new(
        ExecCtx::Tapscript,
        Options { enforce_stack_limit: true, ..Options::default() },
        TxTemplate {
            tx: tx.clone(),
            prevouts: prevouts.to_vec(),
            input_idx: input_index,
            taproot_annex_scriptleaf: Some((leaf_hash, None)),
        },
        tapscript.clone(),
        arguments,
    )
    .expect("transaction-aware Tapscript executor");
    while exec.exec_next().is_ok() {}
    let success = exec.result().expect("execution terminates").success;
    (success, exec.stats().max_nb_stack_items)
}

/// Sign every leaf once the transaction is fixed, then attach
/// `[WOTS stack..., schnorr_sig, tapscript, control]`.
fn sign_transaction(
    mut tx: Transaction,
    leaves: &[WotsInput],
    keypair: &Keypair,
    secp: &Secp256k1<bitcoin::secp256k1::All>,
) -> (Transaction, Vec<TxOut>) {
    let prevouts: Vec<TxOut> = leaves.iter().map(|leaf| leaf.prevout.clone()).collect();
    let signatures: Vec<Vec<u8>> = {
        let prevouts_ref = Prevouts::All(&prevouts);
        let mut cache = SighashCache::new(&tx);
        leaves
            .iter()
            .enumerate()
            .map(|(input_index, leaf)| {
                let leaf_hash = TapLeafHash::from_script(leaf.tapscript.as_script(), LeafVersion::TapScript);
                let sighash = cache
                    .taproot_script_spend_signature_hash(input_index, &prevouts_ref, leaf_hash, TapSighashType::Default)
                    .expect("BIP341 WOTS script-spend sighash");
                let signature = bitcoin::taproot::Signature {
                    signature: secp.sign_schnorr_no_aux_rand(&Message::from(sighash), keypair),
                    sighash_type: TapSighashType::Default,
                }
                .to_vec();
                assert_eq!(signature.len(), 64, "SIGHASH_DEFAULT has no type byte");
                signature
            })
            .collect()
    };

    for ((input, leaf), signature) in tx.input.iter_mut().zip(leaves).zip(signatures) {
        let items = wots_translation::stack(&leaf.values, &leaf.nodes);
        assert_eq!(items.len(), 2 * CHAINS * leaf.chunks());
        for item in items {
            input.witness.push(item);
        }
        input.witness.push(signature);
        input.witness.push(leaf.tapscript.as_bytes());
        input.witness.push(leaf.control.serialize());
        assert!(leaf.control.verify_taproot_commitment(secp, leaf.output_key, leaf.tapscript.as_script()));
    }
    (tx, prevouts)
}

fn signed_single_input(
    rng: &mut ChaCha20Rng,
    secp: &Secp256k1<bitcoin::secp256k1::All>,
    keypair: &Keypair,
    funding_index: u32,
    digits: &[[u8; DIGITS]],
) -> (Transaction, Vec<TxOut>, WotsInput) {
    let (authorization_key, _) = keypair.x_only_public_key();
    let leaf = wots_input(rng, secp, authorization_key, Txid::all_zeros(), funding_index, digits);
    let unsigned = two_output_transaction(std::slice::from_ref(&leaf), secp);
    let (tx, prevouts) = sign_transaction(unsigned, std::slice::from_ref(&leaf), keypair, secp);
    (tx, prevouts, leaf)
}

/// The WOTS witness items with the transaction signature on top.
fn arguments_with(values: &[[u8; CHAINS]], nodes: &[[Node; CHAINS]], signature: &[u8]) -> Vec<Vec<u8>> {
    let mut items = wots_translation::stack(values, nodes);
    items.push(signature.to_vec());
    items
}

fn encode_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Export the regtest funding commitments and signed reveals, as
/// `antichain_tx_cost` does.
fn export_regtest_fixtures(dir: &std::path::Path, prevout_scripts: &[ScriptBuf], reveals: &[Transaction]) {
    std::fs::create_dir_all(dir).expect("create WOTS export directory");
    let outputs: Vec<String> = prevout_scripts
        .iter()
        .map(|script| {
            let address = Address::from_script(script, Network::Regtest).expect("P2TR script has a regtest address");
            format!("{{\"{address}\":{:.8}}}", FUNDING_SATS_PER_INPUT as f64 / 100_000_000.0)
        })
        .collect();
    std::fs::write(dir.join("funding_outputs.json"), format!("[{}]\n", outputs.join(",")))
        .expect("write WOTS funding outputs");
    let scripts = prevout_scripts
        .iter()
        .enumerate()
        .map(|(i, script)| {
            let address = Address::from_script(script, Network::Regtest).unwrap();
            format!("{i}\t{address}\t{}", encode_hex(script.as_bytes()))
        })
        .collect::<Vec<_>>()
        .join("\n");
    std::fs::write(dir.join("funding_scripts.tsv"), format!("{scripts}\n")).expect("write WOTS funding script manifest");
    for (i, tx) in reveals.iter().enumerate() {
        std::fs::write(dir.join(format!("reveal-{i:03}.hex")), format!("{}\n", encode_hex(&serialize(tx))))
            .expect("write WOTS reveal transaction");
    }
}

#[test]
fn signed_wots_chunk_executes_and_rejects_forgery_and_tampering() {
    let secp = Secp256k1::new();
    let keypair = authorization_keypair(&secp);
    let mut rng = ChaCha20Rng::seed_from_u64(0x0075_0001);

    let (tx, prevouts, leaf) = signed_single_input(&mut rng, &secp, &keypair, 0, &[CANONICAL_DIGITS]);
    assert_eq!(leaf.values[0], [1, 1, 1, 1, 1, 1, 1, 2, 5, 7], "W = 47 = 8 * 5 + 7");
    // 34 B of key and CHECKSIGVERIFY, 488 B of chunk, OP_TRUE.
    assert_eq!(leaf.tapscript.len(), 34 + 488 + 1);
    let wots_items = wots_translation::stack(&leaf.values, &leaf.nodes);
    assert_eq!(wots_items.iter().map(|i| 1 + i.len()).sum::<usize>(), 230, "10 chains of 21 + 2 B");
    assert_eq!(serialize(&tx).len(), 995);
    assert_eq!(tx.weight().to_wu(), 1_406);
    assert_eq!(tx.vsize(), 352);
    eprintln!(
        "one chunk: tapscript {} B, {} serialized B, {} WU, {} vB",
        leaf.tapscript.len(),
        serialize(&tx).len(),
        tx.weight().to_wu(),
        tx.vsize()
    );

    let arguments = witness_arguments(&tx.input[0].witness);
    let (success, peak) = execute_input(&tx, &prevouts, 0, &leaf.tapscript, arguments.clone());
    assert!(success, "honest signed WOTS leaf executes");
    assert!(peak <= MAX_STACK_ITEMS);
    let signature = arguments.last().unwrap().clone();

    // A wrong node.
    let mut wrong_node = leaf.nodes.clone();
    wrong_node[0][3][0] ^= 1;
    assert!(!execute_input(&tx, &prevouts, 0, &leaf.tapscript, arguments_with(&leaf.values, &wrong_node, &signature)).0);

    // A digit raised by hashing its node forward, the checksum unchanged.
    let mut raised_values = leaf.values.clone();
    let mut raised_nodes = leaf.nodes.clone();
    raised_values[0][2] += 1;
    raised_nodes[0][2] = wots_translation::forward(&raised_nodes[0][2], 1);
    assert!(!execute_input(&tx, &prevouts, 0, &leaf.tapscript, arguments_with(&raised_values, &raised_nodes, &signature)).0);

    // ... and with r lowered to balance the sum, its node unchanged.
    let mut balanced = raised_values.clone();
    balanced[0][DIGITS + 1] -= 1;
    assert!(!execute_input(&tx, &prevouts, 0, &leaf.tapscript, arguments_with(&balanced, &raised_nodes, &signature)).0);

    // A digit value lie with its node unchanged.
    let mut lie = leaf.values.clone();
    lie[0][4] += 1;
    lie[0][DIGITS + 1] -= 1;
    assert!(!execute_input(&tx, &prevouts, 0, &leaf.tapscript, arguments_with(&lie, &leaf.nodes, &signature)).0);

    // Digit items no honest signer posts, in chunk 0's chain 0 (top of the
    // WOTS stack, under the signature): out of range, negative, a node, and
    // non-minimal encodings of the signed value 1. Each is rejected, so the
    // challenger's reading of a digit as one byte, or none for 0, is the only
    // one an accepted witness allows.
    let digit_at = arguments.len() - 2;
    assert_eq!(arguments[digit_at], [1]);
    for (item, what) in [
        (vec![8u8], "8"),
        (vec![9], "9"),
        (vec![15], "15"),
        (vec![0x81], "-1"),
        (leaf.nodes[0][1].to_vec(), "a node"),
        (vec![1, 0], "1 in two bytes"),
        (vec![0x80], "negative zero"),
    ] {
        let mut forged = arguments.clone();
        forged[digit_at] = item;
        assert!(!execute_input(&tx, &prevouts, 0, &leaf.tapscript, forged).0, "digit {what}");
    }

    // A digit above 7 makes `OP_PICK` read below its own ladder: 8 reaches
    // the next chain's digit, 9 its node, 10 and 11 the chain after. The
    // attacker fills that slot with this chain's public end, so this chain's
    // check passes; the slot is then a later chain's node, which fails its
    // check, or its digit, which is no number.
    let ends: [Node; CHAINS] = core::array::from_fn(|i| wots_translation::forward(&leaf.nodes[0][i], wots_translation::K - leaf.values[0][i] as usize));
    // Alone, chain 0's check does accept the redirected pick.
    let alone = script! {
        { ends[0].to_vec() } 0 { leaf.nodes[0][0].to_vec() } 9
        { wots_translation::verify_chain(&ends[0]) }
        OP_2DROP OP_TRUE
    };
    let info = bitcoin_scriptexec::execute_script(alone);
    assert!(info.success, "a lone chain is fooled: {:?}", info.error);
    for c in 0..CHAINS {
        for (depth, slot) in [(9u8, 1), (11, 2)] {
            if c + slot >= CHAINS {
                continue;
            }
            let mut values = leaf.values.clone();
            let mut nodes = leaf.nodes.clone();
            values[0][c] = depth;
            nodes[0][c + slot] = ends[c];
            assert!(
                !execute_input(&tx, &prevouts, 0, &leaf.tapscript, arguments_with(&values, &nodes, &signature)).0,
                "chain {c}: digit {depth} pointing at chain {}'s node",
                c + slot
            );
        }
        for (depth, slot) in [(8u8, 1), (10, 2)] {
            if c + slot >= CHAINS {
                continue;
            }
            // The witness items, bottom first: chain i's digit is item 2 (9 - i) + 1.
            let mut values = leaf.values.clone();
            values[0][c] = depth;
            let mut forged = arguments_with(&values, &leaf.nodes, &signature);
            let at = 2 * (CHAINS - 1 - (c + slot)) + 1;
            assert_eq!(forged[at], [leaf.values[0][c + slot]], "the slot is chain {}'s digit", c + slot);
            forged[at] = ends[c].to_vec();
            assert!(
                !execute_input(&tx, &prevouts, 0, &leaf.tapscript, forged).0,
                "chain {c}: digit {depth} pointing at chain {}'s digit",
                c + slot
            );
        }
    }

    let mut bad_signature = arguments.clone();
    bad_signature.last_mut().unwrap()[0] ^= 1;
    assert!(!execute_input(&tx, &prevouts, 0, &leaf.tapscript, bad_signature).0);

    // The Schnorr signature binds the transaction.
    let mut redirected = tx.clone();
    redirected.output[0].value = Amount::from_sat(OUTPUT_SATS + 1);
    assert!(!execute_input(&redirected, &prevouts, 0, &leaf.tapscript, arguments).0);

    let mut wrong_control = leaf.control.serialize();
    wrong_control[0] ^= 1;
    let wrong_control = ControlBlock::decode(&wrong_control).expect("parity-flipped control block decodes");
    assert!(!wrong_control.verify_taproot_commitment(&secp, leaf.output_key, leaf.tapscript.as_script()));

    // A zero digit is the empty item: one witness byte, one WU, less.
    // [0, 1, 1, 1, 1, 1, 1, 3] keeps W = 47, so u and r are unchanged.
    let (with_zero, zero_prevouts, zero_leaf) =
        signed_single_input(&mut rng, &secp, &keypair, 1, &[[0, 1, 1, 1, 1, 1, 1, 3]]);
    assert_eq!(zero_leaf.values[0][DIGITS..], [5, 7]);
    assert!(execute_input(&with_zero, &zero_prevouts, 0, &zero_leaf.tapscript, witness_arguments(&with_zero.input[0].witness)).0);
    let (nonzero, _, _) = signed_single_input(&mut rng, &secp, &keypair, 1, &[CANONICAL_DIGITS]);
    assert_eq!(nonzero.weight().to_wu(), with_zero.weight().to_wu() + 1);
}

#[test]
fn script_agrees_with_the_off_chain_check() {
    // Random changes to a signed chunk, a value moved within 0..=7, a node
    // hashed forward or replaced: the Assert leaf accepts exactly when
    // `chunk_verifies` does, the check the challenger reads labels after.
    let secp = Secp256k1::new();
    let keypair = authorization_keypair(&secp);
    let mut rng = ChaCha20Rng::seed_from_u64(0x0075_0002);
    let (tx, prevouts, leaf) = signed_single_input(&mut rng, &secp, &keypair, 0, &[CANONICAL_DIGITS]);
    let ends: [Node; CHAINS] = core::array::from_fn(|i| wots_translation::forward(&leaf.nodes[0][i], wots_translation::K - leaf.values[0][i] as usize));
    let signature = witness_arguments(&tx.input[0].witness).last().unwrap().clone();
    let (mut accepted, mut rejected) = (0, 0);
    for _ in 0..300 {
        let mut values = leaf.values.clone();
        let mut nodes = leaf.nodes.clone();
        for _ in 0..rng.random_range(1..=3) {
            let i = rng.random_range(0..CHAINS);
            match rng.random_range(0..3) {
                0 => values[0][i] = rng.random_range(0..=wots_translation::K as u8),
                1 => {
                    let s = rng.random_range(1..=2);
                    nodes[0][i] = wots_translation::forward(&nodes[0][i], s);
                    values[0][i] = (values[0][i] + s as u8).min(wots_translation::K as u8);
                }
                _ => nodes[0][i] = rng.random(),
            }
        }
        let expected = wots_translation::chunk_verifies(&ends, &values[0], &nodes[0]);
        let got = execute_input(&tx, &prevouts, 0, &leaf.tapscript, arguments_with(&values, &nodes, &signature)).0;
        assert_eq!(got, expected, "values {:?}", values[0]);
        if got { accepted += 1 } else { rejected += 1 }
    }
    // Unchanged-by-chance cases are the accepted ones; the rest are forgeries.
    assert!(rejected > 250, "{accepted} accepted, {rejected} rejected");
}

#[test]
fn signed_wots_capacity_and_full_input_packing() {
    let secp = Secp256k1::new();
    let keypair = authorization_keypair(&secp);
    let (authorization_key, _) = keypair.x_only_public_key();
    let mut rng = ChaCha20Rng::seed_from_u64(0x0075_0049);

    // 49 chunks is the most one input holds: at its peak, 978 other WOTS
    // items, the digit, the node and its 7 hashes and the ladder's index on
    // the main stack, and the digit's copy on the altstack.
    let full = [CANONICAL_DIGITS; MAX_CHUNKS_PER_INPUT];
    let (tx49, prevouts49, leaf49) = signed_single_input(&mut rng, &secp, &keypair, 0, &full);
    let (success, peak) = execute_input(&tx49, &prevouts49, 0, &leaf49.tapscript, witness_arguments(&tx49.input[0].witness));
    assert!(success, "49 chunks is an executable signed leaf");
    assert_eq!(peak, 989, "978 + 1 + 8 + 1 on the main stack, 1 on the altstack");
    assert_eq!(leaf49.tapscript.len(), 34 + 49 * 488 + 1);
    assert_eq!(tx49.input[0].witness.len(), 983);
    let one_input_weight = tx49.weight().to_wu();
    assert_eq!(one_input_weight, 35_872);
    eprintln!(
        "49 chunks: tapscript {} B, witness items {}, peak stack {peak}, {} WU, {} vB",
        leaf49.tapscript.len(),
        tx49.input[0].witness.len(),
        one_input_weight,
        tx49.vsize()
    );

    let (tx50, prevouts50, leaf50) =
        signed_single_input(&mut rng, &secp, &keypair, 1, &[CANONICAL_DIGITS; MAX_CHUNKS_PER_INPUT + 1]);
    assert!(
        !execute_input(&tx50, &prevouts50, 0, &leaf50.tapscript, witness_arguments(&tx50.input[0].witness)).0,
        "50 chunks exceeds the stack limit"
    );

    // Inputs per transaction: as many full inputs as fit in 400k WU.
    let (two, _, _) = {
        let leaves: Vec<WotsInput> = (0..2)
            .map(|i| wots_input(&mut rng, &secp, authorization_key, Txid::all_zeros(), 2 + i, &full))
            .collect();
        let unsigned = two_output_transaction(&leaves, &secp);
        let (tx, prevouts) = sign_transaction(unsigned, &leaves, &keypair, &secp);
        (tx, prevouts, leaves)
    };
    let per_input = two.weight().to_wu() - one_input_weight;
    let shell = one_input_weight - per_input;
    let inputs_per_tx = ((MAX_STANDARD_TX_WEIGHT - shell) / per_input) as usize;
    assert_eq!((per_input, shell, inputs_per_tx), (35_486, 386, 11));
    eprintln!("per full input {per_input} WU, shell {shell} WU, {inputs_per_tx} full inputs per transaction");

    let input_bits = input_bits();
    let total_chunks = input_bits.div_ceil(CHUNK_BITS);
    let funding_txid = std::env::var("WHIR_GC_FUNDING_TXID")
        .ok()
        .map(|value| value.parse().expect("WHIR_GC_FUNDING_TXID is a txid"))
        .unwrap_or_else(Txid::all_zeros);
    let mut chunks_left = total_chunks;
    let mut next_funding_index = 0u32;
    let mut transaction_count = 0usize;
    let mut input_count = 0usize;
    let mut serialized_bytes = 0usize;
    let mut summed_weight = 0u64;
    let mut summed_vsize = 0usize;
    let mut max_tx_weight = 0u64;
    let mut max_peak = 0usize;
    let mut transactions = Vec::new();
    let mut prevout_scripts = Vec::new();

    while chunks_left != 0 {
        let slots = chunks_left.div_ceil(MAX_CHUNKS_PER_INPUT).min(inputs_per_tx);
        let mut leaves = Vec::with_capacity(slots);
        for _ in 0..slots {
            let chunks = chunks_left.min(MAX_CHUNKS_PER_INPUT);
            leaves.push(wots_input(
                &mut rng,
                &secp,
                authorization_key,
                funding_txid,
                next_funding_index,
                &vec![CANONICAL_DIGITS; chunks],
            ));
            chunks_left -= chunks;
            next_funding_index += 1;
        }
        let unsigned = two_output_transaction(&leaves, &secp);
        let (tx, prevouts) = sign_transaction(unsigned, &leaves, &keypair, &secp);
        let weight = tx.weight().to_wu();
        assert!(weight <= MAX_STANDARD_TX_WEIGHT);
        for (i, leaf) in leaves.iter().enumerate() {
            let (ok, peak) = execute_input(&tx, &prevouts, i, &leaf.tapscript, witness_arguments(&tx.input[i].witness));
            assert!(ok, "transaction {transaction_count} input {i} executes");
            max_peak = max_peak.max(peak);
        }
        transaction_count += 1;
        input_count += tx.input.len();
        serialized_bytes += serialize(&tx).len();
        summed_weight += weight;
        summed_vsize += tx.vsize();
        max_tx_weight = max_tx_weight.max(weight);
        prevout_scripts.extend(prevouts.into_iter().map(|prevout| prevout.script_pubkey));
        transactions.push(tx);
    }

    assert_eq!(input_count, total_chunks.div_ceil(MAX_CHUNKS_PER_INPUT));
    assert_eq!(transaction_count, input_count.div_ceil(inputs_per_tx));
    assert!(max_peak <= MAX_STACK_ITEMS);
    eprintln!(
        "{input_bits} bits via chunked WOTS (3-bit digits, 8 per chunk): {total_chunks} chunks, \
         {input_count} signed P2TR inputs in {transaction_count} two-output transactions; \
         {serialized_bytes} serialized bytes; {summed_weight} WU; {summed_vsize} vB; \
         max tx {max_tx_weight} WU; peak stack {max_peak}"
    );
    // (inputs, transactions, serialized bytes, WU, vB) at the pinned sizes.
    let golden = match input_bits {
        KECCAK_INPUT_BITS => Some((886, 81, 31_312_270, 31_444_576, 7_861_144)),
        NARROW_INPUT_BITS => Some((481, 44, 16_980_885, 17_052_720, 4_263_180)),
        _ => None,
    };
    if let Some(expected) = golden {
        assert_eq!(input_bits % CHUNK_BITS, 0);
        assert_eq!(max_tx_weight, 390_732, "eleven full inputs");
        assert_eq!((input_count, transaction_count, serialized_bytes, summed_weight, summed_vsize), expected);
    }

    if let Ok(dir) = std::env::var("WHIR_GC_EXPORT_DIR") {
        export_regtest_fixtures(std::path::Path::new(&dir), &prevout_scripts, &transactions);
    }
}
