//! Damaged `.usdc` input must come back as an error, never a panic, an
//! allocation failure or a stack overflow: an application built with
//! `panic = "abort"` would otherwise crash on a bad file. Each case mutates
//! a known-good fixture deterministically and reads every field value.

use std::io::Cursor;
use std::panic;

use openusd::sdf::AbstractData;
use openusd::usdc::CrateData;

const FIXTURES: [&str; 5] = [
    "reference.usdc",
    "ints.usdc",
    "sdf_types.usdc",
    "payload.usdc",
    "floats.usdc",
];

/// xorshift64: the same mutations on every run and platform.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// One of: flipped bits, an extreme 64-bit value (the shape of a lying
/// count or offset), a truncation, or a large 32-bit value.
fn mutate(bytes: &mut Vec<u8>, rng: &mut Rng) {
    match rng.next() % 4 {
        0 => {
            for _ in 0..1 + rng.next() % 8 {
                let i = rng.below(bytes.len());
                bytes[i] ^= 1 << (rng.next() % 8);
            }
        }
        1 => {
            let i = rng.below(bytes.len() - 8);
            let value = [u64::MAX, i64::MAX as u64, u32::MAX as u64, 1 << 30][rng.below(4)];
            bytes[i..i + 8].copy_from_slice(&value.to_le_bytes());
        }
        2 => {
            let len = rng.below(bytes.len()).max(1);
            bytes.truncate(len);
        }
        _ => {
            let i = rng.below(bytes.len() - 4);
            bytes[i..i + 4].copy_from_slice(&((rng.next() as u32) | 0x1000_0000).to_le_bytes());
        }
    }
}

/// Opens the crate and decodes every value, as a stage would.
fn read_everything(bytes: Vec<u8>) {
    let Ok(data) = CrateData::open(Cursor::new(bytes), true) else {
        return;
    };
    for path in data.spec_paths() {
        for field in data.list_fields(&path).unwrap_or_default() {
            let _ = data.try_field(&path, &field);
        }
    }
}

#[test]
fn mutated_crate_files_are_errors_not_panics() {
    let rounds: usize = std::env::var("OPENUSD_USDC_MUTATIONS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(2_000);
    let mut rng = Rng(0x2545_F491_4F6C_DD1D);
    let mut panics = Vec::new();
    for fixture in FIXTURES {
        let path = format!("{}/fixtures/{fixture}", env!("CARGO_MANIFEST_DIR"));
        let seed = std::fs::read(&path).unwrap_or_else(|e| panic!("cannot read {path}: {e}"));
        for round in 0..rounds {
            let mut bytes = seed.clone();
            mutate(&mut bytes, &mut rng);
            if panic::catch_unwind(|| read_everything(bytes)).is_err() {
                panics.push(format!("{fixture} round {round}"));
            }
        }
    }
    assert!(
        panics.is_empty(),
        "{} panics, first: {:?}",
        panics.len(),
        &panics[..panics.len().min(5)]
    );
}
