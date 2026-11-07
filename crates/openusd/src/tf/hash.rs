//! C++ `TfHash`'s accumulated state, for the byte strings it hashes.
//!
//! A hash code C++ computes is part of what some C++ code names things
//! with: UsdImaging names a propagated point instancer prototype
//! `ForInstancer%zx` of `TfHash::Combine` over two paths' text. Hashing the
//! same bytes the same way gives the same names.

/// The accumulated state of a C++ `TfHash` over byte strings (C++
/// `Tf_HashState`). Each [`append`](Self::append) hashes the bytes with
/// SpookyHash V2 (C++ `ArchHash64`), seeded with the state so far, and
/// [`code`](Self::code) is the code `TfHash::Combine` returns. A
/// `std::string` appends its bytes, and a `std::map` of strings its entries
/// in key order, each key then its value.
///
/// C++ holds the state in a `size_t`, so the codes are those of a 64-bit
/// build.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct HashState {
    state: u64,
}

impl HashState {
    /// Appends the byte string `bytes` (C++ `Tf_HashState::_AppendBytes`).
    ///
    /// This is how C++ appends a string, and a contiguous array of integers
    /// too, as their bytes in native order. A lone integer it combines into
    /// the state by a different step,
    /// so appending one integer's bytes here does not give the code C++ does
    /// for it.
    pub fn append(&mut self, bytes: impl AsRef<[u8]>) {
        self.state = spooky::hash64(bytes.as_ref(), self.state);
    }

    /// The hash code of what was appended (C++ `Tf_HashState::_GetCode`):
    /// the state times Knuth's multiplicative constant, its bytes swapped.
    pub fn code(&self) -> u64 {
        self.state.wrapping_mul(11_400_714_819_323_198_549).swap_bytes()
    }
}

/// SpookyHash V2 (Bob Jenkins, public domain), as OpenUSD's `arch/hash.cpp`
/// carries it: little-endian reads, `Hash64` returning the first half of the
/// 128-bit hash seeded with `(seed, seed)`.
mod spooky {
    use std::array;

    /// The number of 64-bit words of internal state.
    const SC_NUM_VARS: usize = 12;
    /// The number of bytes one block mixes.
    const SC_BLOCK_SIZE: usize = SC_NUM_VARS * 8;
    /// The length from which a message takes the long path.
    const SC_BUF_SIZE: usize = 2 * SC_BLOCK_SIZE;
    /// The constant SpookyHash seeds its unseeded words with.
    const SC_CONST: u64 = 0xdead_beef_dead_beef;

    /// The little-endian `u64` at byte `at` of `bytes`.
    fn u64_at(bytes: &[u8], at: usize) -> u64 {
        let word: [u8; 8] = bytes[at..at + 8].try_into().expect("an eight-byte slice");
        u64::from_le_bytes(word)
    }

    /// `SpookyHash::ShortMix`: mixes the four words of the short hash.
    fn short_mix(h: &mut [u64; 4]) {
        let [h0, h1, h2, h3] = h;
        *h2 = h2.rotate_left(50);
        *h2 = h2.wrapping_add(*h3);
        *h0 ^= *h2;
        *h3 = h3.rotate_left(52);
        *h3 = h3.wrapping_add(*h0);
        *h1 ^= *h3;
        *h0 = h0.rotate_left(30);
        *h0 = h0.wrapping_add(*h1);
        *h2 ^= *h0;
        *h1 = h1.rotate_left(41);
        *h1 = h1.wrapping_add(*h2);
        *h3 ^= *h1;
        *h2 = h2.rotate_left(54);
        *h2 = h2.wrapping_add(*h3);
        *h0 ^= *h2;
        *h3 = h3.rotate_left(48);
        *h3 = h3.wrapping_add(*h0);
        *h1 ^= *h3;
        *h0 = h0.rotate_left(38);
        *h0 = h0.wrapping_add(*h1);
        *h2 ^= *h0;
        *h1 = h1.rotate_left(37);
        *h1 = h1.wrapping_add(*h2);
        *h3 ^= *h1;
        *h2 = h2.rotate_left(62);
        *h2 = h2.wrapping_add(*h3);
        *h0 ^= *h2;
        *h3 = h3.rotate_left(34);
        *h3 = h3.wrapping_add(*h0);
        *h1 ^= *h3;
        *h0 = h0.rotate_left(5);
        *h0 = h0.wrapping_add(*h1);
        *h2 ^= *h0;
        *h1 = h1.rotate_left(36);
        *h1 = h1.wrapping_add(*h2);
        *h3 ^= *h1;
    }

    /// `SpookyHash::ShortEnd`: the final mix of the short hash.
    fn short_end(h: &mut [u64; 4]) {
        let [h0, h1, h2, h3] = h;
        *h3 ^= *h2;
        *h2 = h2.rotate_left(15);
        *h3 = h3.wrapping_add(*h2);
        *h0 ^= *h3;
        *h3 = h3.rotate_left(52);
        *h0 = h0.wrapping_add(*h3);
        *h1 ^= *h0;
        *h0 = h0.rotate_left(26);
        *h1 = h1.wrapping_add(*h0);
        *h2 ^= *h1;
        *h1 = h1.rotate_left(51);
        *h2 = h2.wrapping_add(*h1);
        *h3 ^= *h2;
        *h2 = h2.rotate_left(28);
        *h3 = h3.wrapping_add(*h2);
        *h0 ^= *h3;
        *h3 = h3.rotate_left(9);
        *h0 = h0.wrapping_add(*h3);
        *h1 ^= *h0;
        *h0 = h0.rotate_left(47);
        *h1 = h1.wrapping_add(*h0);
        *h2 ^= *h1;
        *h1 = h1.rotate_left(54);
        *h2 = h2.wrapping_add(*h1);
        *h3 ^= *h2;
        *h2 = h2.rotate_left(32);
        *h3 = h3.wrapping_add(*h2);
        *h0 ^= *h3;
        *h3 = h3.rotate_left(25);
        *h0 = h0.wrapping_add(*h3);
        *h1 ^= *h0;
        *h0 = h0.rotate_left(63);
        *h1 = h1.wrapping_add(*h0);
    }

    /// `SpookyHash::Short` seeded with `(seed, seed)`, for messages under
    /// 192 bytes.
    fn short(message: &[u8], seed: u64) -> u64 {
        let mut h = [seed, seed, SC_CONST, SC_CONST];
        let mut chunks = message.chunks_exact(32);
        for chunk in &mut chunks {
            h[2] = h[2].wrapping_add(u64_at(chunk, 0));
            h[3] = h[3].wrapping_add(u64_at(chunk, 8));
            short_mix(&mut h);
            h[0] = h[0].wrapping_add(u64_at(chunk, 16));
            h[1] = h[1].wrapping_add(u64_at(chunk, 24));
        }
        let mut tail = chunks.remainder();
        if tail.len() >= 16 {
            h[2] = h[2].wrapping_add(u64_at(tail, 0));
            h[3] = h[3].wrapping_add(u64_at(tail, 8));
            short_mix(&mut h);
            tail = &tail[16..];
        }
        // The length, and the last 0..15 bytes as two little-endian words
        // padded with zeros, or the constant twice when none are left.
        h[3] = h[3].wrapping_add((message.len() as u64) << 56);
        let (c, d) = if tail.is_empty() {
            (SC_CONST, SC_CONST)
        } else {
            let mut padded = [0u8; 16];
            padded[..tail.len()].copy_from_slice(tail);
            (u64_at(&padded, 0), u64_at(&padded, 8))
        };
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        short_end(&mut h);
        h[0]
    }

    /// `SpookyHash::Mix`: mixes one block of `data` into the state `s`. Step
    /// `i` adds word `i`, xors word `i + 10` into word `i + 2`, xors word `i`
    /// into word `i + 11`, rotates word `i` and adds word `i + 1` into word
    /// `i + 11`, every index taken modulo the 12 state words.
    fn mix(data: &[u64; SC_NUM_VARS], s: &mut [u64; SC_NUM_VARS]) {
        const ROT: [u32; SC_NUM_VARS] = [11, 32, 43, 31, 17, 28, 39, 57, 55, 54, 22, 46];
        for (i, &r) in ROT.iter().enumerate() {
            let i1 = (i + 1) % SC_NUM_VARS;
            let i2 = (i + 2) % SC_NUM_VARS;
            let i10 = (i + 10) % SC_NUM_VARS;
            let i11 = (i + 11) % SC_NUM_VARS;
            s[i] = s[i].wrapping_add(data[i]);
            s[i2] ^= s[i10];
            s[i11] ^= s[i];
            s[i] = s[i].rotate_left(r);
            s[i11] = s[i11].wrapping_add(s[i1]);
        }
    }

    /// `SpookyHash::EndPartial`: line `i` adds word `i + 1` into word
    /// `i + 11`, xors word `i + 11` into word `i + 2` and rotates word
    /// `i + 1`, every index taken modulo the 12 state words.
    fn end_partial(h: &mut [u64; SC_NUM_VARS]) {
        const ROT: [u32; SC_NUM_VARS] = [44, 15, 34, 21, 38, 33, 10, 13, 38, 53, 42, 54];
        for (i, &r) in ROT.iter().enumerate() {
            let i1 = (i + 1) % SC_NUM_VARS;
            let i2 = (i + 2) % SC_NUM_VARS;
            let i11 = (i + 11) % SC_NUM_VARS;
            h[i11] = h[i11].wrapping_add(h[i1]);
            h[i2] ^= h[i11];
            h[i1] = h[i1].rotate_left(r);
        }
    }

    /// `SpookyHash::End`: adds the last block and mixes the state three
    /// times over.
    fn end(data: &[u64; SC_NUM_VARS], h: &mut [u64; SC_NUM_VARS]) {
        for (word, d) in h.iter_mut().zip(data) {
            *word = word.wrapping_add(*d);
        }
        end_partial(h);
        end_partial(h);
        end_partial(h);
    }

    /// The 12 little-endian words of the 96-byte `block`.
    fn words(block: &[u8]) -> [u64; SC_NUM_VARS] {
        array::from_fn(|i| u64_at(block, i * 8))
    }

    /// `SpookyHash::Hash64(message, length, seed)`.
    pub(super) fn hash64(message: &[u8], seed: u64) -> u64 {
        if message.len() < SC_BUF_SIZE {
            return short(message, seed);
        }
        // h0 = h3 = h6 = h9 and h1 = h4 = h7 = h10 are the seeds, the others
        // the constant.
        let mut h: [u64; SC_NUM_VARS] = array::from_fn(|i| if i % 3 == 2 { SC_CONST } else { seed });
        let mut blocks = message.chunks_exact(SC_BLOCK_SIZE);
        for block in &mut blocks {
            mix(&words(block), &mut h);
        }
        let rest = blocks.remainder();
        let mut last = [0u8; SC_BLOCK_SIZE];
        last[..rest.len()].copy_from_slice(rest);
        last[SC_BLOCK_SIZE - 1] = rest.len() as u8;
        end(&words(&last), &mut h);
        h[0]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// C++ `TfHash::Combine` of `strings`, in order.
    fn combine(strings: &[&str]) -> u64 {
        let mut state = HashState::default();
        for s in strings {
            state.append(s);
        }
        state.code()
    }

    // The expected codes in these tests are C++ `TfHash::Combine`'s at
    // OpenUSD 26.08 (`tf/hash.h`, `arch/hash.cpp`).

    #[test]
    fn combine_two_strings() {
        let golden: &[(&str, &str, u64)] = &[
            ("/World/Instancer", "/", 0xa61eb064d406b29f),
            ("/Tree/Leaves", "/Trees/tree/ForInstancer1", 0x14855720f51764cd),
            ("", "", 0x941f3c26d090362d),
            ("/a", "/", 0x729f030fde4ead23),
            (
                "/World/sets/Rocks/PointInstancer_with_a_long_name_for_testing_the_32_byte_blocks",
                "/",
                0x716dd884530dcda4,
            ),
            (
                "/Some/Very/Long/Path/That/Goes/On/And/On/For/Quite/A/While/To/Exceed/The/Spooky/Short/Hash/Threshold/Of/One/Hundred/And/Ninety/Two/Bytes/In/Length/For/Sure/Yes/Indeed/More/Than/Enough",
                "/Another/Prototype/Root/ForInstancer123abc",
                0xa5f33d0fd49b7d0f,
            ),
            ("/world/trees", "/", 0x27d4476d2fc5f07a),
            (
                "/world/trees/Prototypes/tree/leaves",
                "/world/trees/Prototypes/tree/ForInstancer27d4476d2fc5f07a",
                0x91211c283fb47b5f,
            ),
        ];
        for (a, b, expected) in golden {
            assert_eq!(combine(&[a, b]), *expected, "Combine({a:?}, {b:?})");
        }
    }

    /// Messages of 192 bytes and more take SpookyHash's long path.
    #[test]
    fn combine_long_messages() {
        let long192 = format!("/{}", "a".repeat(191));
        let long300: String = (0..30).map(|i| format!("/segment_{i}")).collect();
        assert!(long300.len() >= 192);
        assert_eq!(combine(&[&long192, "/"]), 0x284b94e778823972);
        assert_eq!(combine(&[&long300, &long192]), 0x35ea98eaf50ec046);
    }

    /// Short messages whose last 0..15 bytes are 4, 6, 7, 8, 9, 11, 13 and 15
    /// long, each combined with `"/"`.
    #[test]
    fn combine_tail_lengths() {
        let golden: &[(&str, u64)] = &[
            ("abcd", 0xc3386ca72e1db0c6),
            ("abcdef", 0x1a0d1c9d675149fe),
            ("abcdefg", 0xe33c6a8806cfb841),
            ("abcdefgh", 0x644144b55e5c34e7),
            ("abcdefghijk", 0x870d49a916d7dc63),
            ("abcdefghijklm", 0xbd0557e374bc449b),
            ("/World/Instance", 0x9e8c34320a6590c6),
            ("/World/Instancer/Proto_ab", 0x394c981816874dd4),
            ("/World/Instancer/Prototype_abcd", 0xa3e710a9e73eb0ea),
        ];
        for (a, expected) in golden {
            assert_eq!(combine(&[a, "/"]), *expected, "Combine({a:?}, \"/\")");
        }
    }

    /// A `std::map<std::string, std::string>` hashes as its entries in key
    /// order, each key then its value.
    #[test]
    fn combine_map() {
        assert_eq!(combine(&["displayColor", "Color"]), 0x2a699f1bd0ef6389);
        assert_eq!(
            combine(&["displayColor", "Color", "displayOpacity", "", "st", "TextureCoordinate"]),
            0xde7ff2d00ca8c5c6
        );
        assert_eq!(combine(&["foo", ""]), 0xddc3440b5e101171);
    }
}
