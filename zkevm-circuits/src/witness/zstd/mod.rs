use eth_types::Field;
use halo2_proofs::circuit::Value;

mod params;
use num::Integer;
pub use params::*;

mod types;
pub use types::*;

#[cfg(test)]
mod tui;
#[cfg(test)]
use tui::draw_rows;

mod util;
use util::{value_bits_le, le_bits_to_value, increment_idx};

/// FrameHeaderDescriptor and FrameContentSize
fn process_frame_header<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
) -> (usize, Vec<ZstdWitnessRow<F>>) {
    let fhd_byte = src
        .get(byte_offset)
        .expect("FrameHeaderDescriptor byte should exist");
    let value_bits = value_bits_le(*fhd_byte);

    assert_eq!(value_bits[0], 0, "dictionary ID should not exist");
    assert_eq!(value_bits[1], 0, "dictionary ID should not exist");
    assert_eq!(value_bits[2], 0, "content checksum should not exist");
    assert_eq!(value_bits[3], 0, "reserved bit should not be set");
    assert_eq!(value_bits[4], 0, "unused bit should not be set");
    assert_eq!(value_bits[5], 1, "single segment expected");

    let fhd_value_rlc =
        last_row.encoded_data.value_rlc * randomness + Value::known(F::from(*fhd_byte as u64));

    // the number of bytes taken to represent FrameContentSize.
    let fcs_tag_len: usize = match value_bits[7] * 2 + value_bits[6] {
        0 => 1,
        1 => 2,
        2 => 4,
        3 => 8,
        _ => unreachable!("2-bit value"),
    };

    // FrameContentSize bytes are read in little-endian, hence its in reverse mode.
    let fcs_bytes = src
        .iter()
        .skip(byte_offset + 1)
        .take(fcs_tag_len)
        .rev()
        .cloned()
        .collect::<Vec<u8>>();
    let fcs = {
        let fcs = fcs_bytes
            .iter()
            .fold(0u64, |acc, &byte| acc * 256u64 + (byte as u64));
        match fcs_tag_len {
            2 => fcs + 256,
            _ => fcs,
        }
    };
    let fcs_tag_value_iter = fcs_bytes
        .iter()
        .scan(Value::known(F::zero()), |acc, &byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        });
    let fcs_tag_value = fcs_tag_value_iter
        .clone()
        .last()
        .expect("FrameContentSize expected");
    let fcs_value_rlcs = fcs_bytes
        .iter()
        .scan(Value::known(F::zero()), |acc, &byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        })
        .collect::<Vec<Value<F>>>();
    let aux_1 = fcs_value_rlcs
        .last()
        .expect("FrameContentSize bytes expected");
    let aux_2 = fhd_value_rlc;

    (
        byte_offset + 1 + fcs_tag_len,
        std::iter::once(ZstdWitnessRow {
            state: ZstdState {
                tag: ZstdTag::FrameHeaderDescriptor,
                tag_next: ZstdTag::FrameContentSize,
                tag_len: 1,
                tag_idx: 1,
                tag_value: Value::known(F::from(*fhd_byte as u64)),
                tag_value_acc: Value::known(F::from(*fhd_byte as u64)),
            },
            encoded_data: EncodedData {
                byte_idx: (byte_offset + 1) as u64,
                encoded_len: last_row.encoded_data.encoded_len,
                value_byte: *fhd_byte,
                value_rlc: fhd_value_rlc,
                ..Default::default()
            },
            decoded_data: DecodedData {
                decoded_len: fcs,
                decoded_len_acc: 0,
                total_decoded_len: last_row.decoded_data.total_decoded_len + fcs,
                decoded_byte: 0,
                decoded_value_rlc: last_row.decoded_data.decoded_value_rlc,
            },
            huffman_data: HuffmanData::default(),
            fse_data: FseTableRow::default(),
        })
        .chain(
            fcs_bytes
                .iter()
                .zip(fcs_tag_value_iter)
                .zip(fcs_value_rlcs.iter().rev())
                .enumerate()
                .map(
                    |(i, ((&value_byte, tag_value_acc), &value_rlc))| ZstdWitnessRow {
                        state: ZstdState {
                            tag: ZstdTag::FrameContentSize,
                            tag_next: ZstdTag::BlockHeader,
                            tag_len: fcs_tag_len as u64,
                            tag_idx: (i + 1) as u64,
                            tag_value: fcs_tag_value,
                            tag_value_acc,
                        },
                        encoded_data: EncodedData {
                            byte_idx: (byte_offset + 2 + i) as u64,
                            encoded_len: last_row.encoded_data.encoded_len,
                            value_byte,
                            reverse: true,
                            reverse_idx: (fcs_tag_len - i) as u64,
                            reverse_len: fcs_tag_len as u64,
                            aux_1: *aux_1,
                            aux_2,
                            value_rlc,
                        },
                        decoded_data: last_row.decoded_data.clone(),
                        huffman_data: HuffmanData::default(),
                        fse_data: FseTableRow::default(),
                    },
                ),
        )
        .collect::<Vec<_>>(),
    )
}

fn process_block<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
) -> (usize, Vec<ZstdWitnessRow<F>>, bool) {
    let mut witness_rows = vec![];

    let (byte_offset, rows, last_block, block_type, block_size) =
        process_block_header(src, byte_offset, last_row, randomness);
    witness_rows.extend_from_slice(&rows);

    let last_row = rows.last().expect("last row expected to exist");
    let (_byte_offset, rows) = match block_type {
        BlockType::RawBlock => process_block_raw(
            src,
            byte_offset,
            last_row,
            randomness,
            block_size,
            last_block,
        ),
        BlockType::RleBlock => process_block_rle(
            src,
            byte_offset,
            last_row,
            randomness,
            block_size,
            last_block,
        ),
        BlockType::ZstdCompressedBlock => process_block_zstd(
            src,
            byte_offset,
            last_row,
            randomness,
            block_size,
            last_block,
        ),
        BlockType::Reserved => unreachable!("Reserved block type not expected"),
    };
    witness_rows.extend_from_slice(&rows);

    (byte_offset, witness_rows, last_block)
}

fn process_block_header<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
) -> (usize, Vec<ZstdWitnessRow<F>>, bool, BlockType, usize) {
    let bh_bytes = src
        .iter()
        .skip(byte_offset)
        .take(N_BLOCK_HEADER_BYTES)
        .cloned()
        .collect::<Vec<u8>>();
    let last_block = (bh_bytes[0] & 1) == 1;
    let block_type = BlockType::from((bh_bytes[0] >> 1) & 3);
    let block_size =
        (bh_bytes[2] as usize * 256 * 256 + bh_bytes[1] as usize * 256 + bh_bytes[0] as usize) >> 3;

    let tag_next = match block_type {
        BlockType::RawBlock => ZstdTag::RawBlockBytes,
        BlockType::RleBlock => ZstdTag::RleBlockBytes,
        BlockType::ZstdCompressedBlock => ZstdTag::ZstdBlockLiteralsHeader,
        _ => unreachable!("BlockType::Reserved unexpected"),
    };

    let tag_value_iter = bh_bytes.iter().scan(Value::known(F::zero()), |acc, &byte| {
        *acc = *acc * randomness + Value::known(F::from(byte as u64));
        Some(*acc)
    });
    let tag_value = tag_value_iter.clone().last().expect("BlockHeader expected");

    // BlockHeader follows FrameContentSize which is processed in reverse order.
    // Hence value_rlc at the first BlockHeader byte will be calculated as:
    //
    // value_rlc::cur == aux_1::prev * (rand ^ reverse_len) * rand
    //      + aux_2::prev * rand
    //      + value_byte::cur
    let acc_start = last_row.encoded_data.aux_1
        * randomness.map(|r| r.pow([last_row.encoded_data.reverse_len, 0, 0, 0]))
        + last_row.encoded_data.aux_2;
    let value_rlcs = bh_bytes
        .iter()
        .scan(acc_start, |acc, &byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        })
        .collect::<Vec<Value<F>>>();

    (
        byte_offset + N_BLOCK_HEADER_BYTES,
        bh_bytes
            .iter()
            .zip(tag_value_iter)
            .zip(value_rlcs.iter())
            .enumerate()
            .map(
                |(i, ((&value_byte, tag_value_acc), &value_rlc))| ZstdWitnessRow {
                    state: ZstdState {
                        tag: ZstdTag::BlockHeader,
                        tag_next,
                        tag_len: N_BLOCK_HEADER_BYTES as u64,
                        tag_idx: (i + 1) as u64,
                        tag_value,
                        tag_value_acc,
                    },
                    encoded_data: EncodedData {
                        byte_idx: (byte_offset + i + 1) as u64,
                        encoded_len: last_row.encoded_data.encoded_len,
                        value_byte,
                        reverse: false,
                        value_rlc,
                        ..Default::default()
                    },
                    decoded_data: last_row.decoded_data.clone(),
                    huffman_data: HuffmanData::default(),
                    fse_data: FseTableRow::default(),
                },
            )
            .collect::<Vec<_>>(),
        last_block,
        block_type,
        block_size,
    )
}

fn process_raw_bytes<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
    n_bytes: usize,
    tag: ZstdTag,
    tag_next: ZstdTag,
) -> (usize, Vec<ZstdWitnessRow<F>>) {
    let value_rlc_iter = src.iter().skip(byte_offset).take(n_bytes).scan(
        last_row.encoded_data.value_rlc,
        |acc, &byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        },
    );
    let decoded_value_rlc_iter = src.iter().skip(byte_offset).take(n_bytes).scan(
        last_row.decoded_data.decoded_value_rlc,
        |acc, &byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        },
    );
    let tag_value_iter = src.iter().skip(byte_offset).take(n_bytes).scan(
        Value::known(F::zero()),
        |acc, &byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        },
    );
    let tag_value = tag_value_iter
        .clone()
        .last()
        .expect("Raw bytes must be of non-zero length");

    (
        byte_offset + n_bytes,
        src.iter()
            .skip(byte_offset)
            .take(n_bytes)
            .zip(tag_value_iter)
            .zip(value_rlc_iter)
            .zip(decoded_value_rlc_iter)
            .enumerate()
            .map(
                |(i, (((&value_byte, tag_value_acc), value_rlc), decoded_value_rlc))| {
                    ZstdWitnessRow {
                        state: ZstdState {
                            tag,
                            tag_next,
                            tag_len: n_bytes as u64,
                            tag_idx: (i + 1) as u64,
                            tag_value,
                            tag_value_acc,
                        },
                        encoded_data: EncodedData {
                            byte_idx: (byte_offset + i + 1) as u64,
                            encoded_len: last_row.encoded_data.encoded_len,
                            value_byte,
                            value_rlc,
                            reverse: false,
                            ..Default::default()
                        },
                        decoded_data: DecodedData {
                            decoded_len: last_row.decoded_data.decoded_len,
                            decoded_len_acc: last_row.decoded_data.decoded_len + (i as u64) + 1,
                            total_decoded_len: last_row.decoded_data.total_decoded_len,
                            decoded_byte: value_byte,
                            decoded_value_rlc,
                        },
                        huffman_data: HuffmanData::default(),
                        fse_data: FseTableRow::default(),
                    }
                },
            )
            .collect::<Vec<_>>(),
    )
}

fn process_rle_bytes<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
    n_bytes: usize,
    tag: ZstdTag,
    tag_next: ZstdTag,
) -> (usize, Vec<ZstdWitnessRow<F>>) {
    let rle_byte = src[byte_offset];
    let value_rlc =
        last_row.encoded_data.value_rlc * randomness + Value::known(F::from(rle_byte as u64));
    let decoded_value_rlc_iter = std::iter::repeat(rle_byte).take(n_bytes).scan(
        last_row.decoded_data.decoded_value_rlc,
        |acc, byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        },
    );
    let tag_value = Value::known(F::from(rle_byte as u64));

    (
        byte_offset + 1,
        std::iter::repeat(rle_byte)
            .take(n_bytes)
            .zip(decoded_value_rlc_iter)
            .enumerate()
            .map(|(i, (value_byte, decoded_value_rlc))| ZstdWitnessRow {
                state: ZstdState {
                    tag,
                    tag_next,
                    tag_len: n_bytes as u64,
                    tag_idx: (i + 1) as u64,
                    tag_value,
                    tag_value_acc: tag_value,
                },
                encoded_data: EncodedData {
                    byte_idx: (byte_offset + 1) as u64,
                    encoded_len: last_row.encoded_data.encoded_len,
                    value_byte,
                    reverse: false,
                    value_rlc,
                    ..Default::default()
                },
                decoded_data: DecodedData {
                    decoded_len: last_row.decoded_data.decoded_len,
                    decoded_len_acc: last_row.decoded_data.decoded_len_acc + (i as u64) + 1,
                    total_decoded_len: last_row.decoded_data.total_decoded_len,
                    decoded_byte: value_byte,
                    decoded_value_rlc,
                },
                huffman_data: HuffmanData::default(),
                fse_data: FseTableRow::default(),
            })
            .collect::<Vec<_>>(),
    )
}

fn process_block_raw<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
    block_size: usize,
    last_block: bool,
) -> (usize, Vec<ZstdWitnessRow<F>>) {
    let tag_next = if last_block {
        ZstdTag::Null
    } else {
        ZstdTag::BlockHeader
    };

    process_raw_bytes(
        src,
        byte_offset,
        last_row,
        randomness,
        block_size,
        ZstdTag::RawBlockBytes,
        tag_next,
    )
}

fn process_block_rle<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
    block_size: usize,
    last_block: bool,
) -> (usize, Vec<ZstdWitnessRow<F>>) {
    let tag_next = if last_block {
        ZstdTag::Null
    } else {
        ZstdTag::BlockHeader
    };

    process_rle_bytes(
        src, 
        byte_offset, 
        last_row, 
        randomness, 
        block_size, 
        ZstdTag::RleBlockBytes, 
        tag_next,
    )
}

#[allow(unused_variables)]
fn process_block_zstd<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
    block_size: usize,
    last_block: bool,
) -> (usize, Vec<ZstdWitnessRow<F>>) {
    let mut witness_rows = vec![];

    // 1-5 bytes LiteralSectionHeader
    let (
        byte_offset, 
        rows, 
        literals_block_type, 
        n_streams, 
        regen_size, 
        compressed_size
    ) = process_block_zstd_literals_header::<F>(
        src, 
        byte_offset, 
        last_row, 
        randomness
    );
    witness_rows.extend_from_slice(&rows);

    // Depending on the literals block type, decode literals section accordingly
    let (bytes_offset, rows) = match literals_block_type {
        BlockType::RawBlock => {
            process_raw_bytes(
                src, 
                byte_offset, 
                rows.last().expect("last row expected to exist"), 
                randomness, 
                regen_size, 
                ZstdTag::ZstdBlockLiteralsRawBytes, 
                ZstdTag::ZstdBlockSequenceHeader,
            )
        },
        BlockType::RleBlock => {
            process_rle_bytes(
                src, 
                byte_offset, 
                rows.last().expect("last row expected to exist"), 
                randomness, 
                regen_size, 
                ZstdTag::ZstdBlockLiteralsRleBytes, 
                ZstdTag::ZstdBlockSequenceHeader,
            )
        },
        BlockType::ZstdCompressedBlock => {
            let mut huffman_rows = vec![];

            let (bytes_offset, rows, huffman_codes, n_huffman_bytes) = process_block_zstd_huffman_code(
                src,
                byte_offset,
                rows.last().expect("last row must exist"),
                randomness,
                n_streams,
            );
            huffman_rows.extend_from_slice(&rows);

            // Subtract huffman header (1-byte), len of huffman bytes and 6-byte jump table (if n_streams > 1)
            let mut literal_stream_size = compressed_size - (n_huffman_bytes + 1);  
            if n_streams > 1 {
                literal_stream_size -= 6;
            }

            // Start decoding the literal section
            let mut stream_offset = byte_offset;


            let (byte_offset, rows, lstream_lens) = process_block_zstd_huffman_jump_table(
                src, 
                stream_offset, 
                huffman_rows.last().expect("last row should exist"),
                n_streams,
                literal_stream_size,
                randomness
            );
            huffman_rows.extend_from_slice(&rows);


            for idx in 0..n_streams {
                let (byte_offset, rows, symbols) = process_block_zstd_lstream(
                    src, 
                    stream_offset,
                    lstream_lens[idx] as usize,
                    huffman_rows.last().expect("last row should exist"),
                    randomness,
                    idx,
                    &huffman_codes
                );
                huffman_rows.extend_from_slice(&rows);

                stream_offset = byte_offset;
            }
            
            (stream_offset, huffman_rows)
        },
        _ => unreachable!("Invalid literals section BlockType")
    };
    witness_rows.extend_from_slice(&rows);

    (bytes_offset, witness_rows)
}

fn process_block_zstd_literals_header<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
) -> (usize, Vec<ZstdWitnessRow<F>>, BlockType, usize, usize, usize) {
    let lh_bytes = src
        .iter()
        .skip(byte_offset)
        .take(N_MAX_LITERAL_HEADER_BYTES)
        .cloned()
        .collect::<Vec<u8>>();

    let literals_block_type = BlockType::from(lh_bytes[0] & 0x3);
    let size_format = (lh_bytes[0] >> 2) & 3;

    let [n_bits_fmt, n_bits_regen, n_bits_compressed, n_streams, n_bytes_header]: [usize; 5] = match literals_block_type {
        BlockType::RawBlock | BlockType::RleBlock => {
            match size_format {
                0b00 | 0b10 => [1, 5, 0, 1, 1],
                0b01 => [2, 12, 0, 1, 2],
                0b11 => [2, 20, 0, 1, 3],
                _ => unreachable!("size_format out of bound")
            }
        },
        BlockType::ZstdCompressedBlock => {
            match size_format {
                0b00 => [2, 10, 10, 1, 3],
                0b01 => [2, 10, 10, 4, 3],
                0b10 => [2, 14, 14, 4, 4],
                0b11 => [2, 18, 18, 4, 5],
                _ => unreachable!("size_format out of bound")
            }
        },
        _ => unreachable!("BlockType::Reserved unexpected or treeless literal section")
    };

    // Bits for representing regenerated_size and compressed_size
    let sizing_bits = &lh_bytes.clone().into_iter().fold(vec![], |mut acc, b| {
        acc.extend(value_bits_le(b));
        acc
    })[(2 + n_bits_fmt)..(n_bytes_header * N_BITS_PER_BYTE)];

    let regen_size = le_bits_to_value(&sizing_bits[0..n_bits_regen]);
    let compressed_size = le_bits_to_value(&sizing_bits[n_bits_regen..(n_bits_regen + n_bits_compressed)]);

    let tag_next = match literals_block_type {
        BlockType::RawBlock => ZstdTag::ZstdBlockLiteralsRawBytes,
        BlockType::RleBlock => ZstdTag::ZstdBlockLiteralsRleBytes,
        BlockType::ZstdCompressedBlock => ZstdTag::ZstdBlockHuffmanCode,
        _ => unreachable!("BlockType::Reserved unexpected or treeless literal section"),
    };

    let tag_value_iter = lh_bytes.iter().take(n_bytes_header).scan(Value::known(F::zero()), |acc, &byte| {
        *acc = *acc * randomness + Value::known(F::from(byte as u64));
        Some(*acc)
    });
    let tag_value = tag_value_iter.clone().last().expect("LiteralsHeader expected");

    let value_rlc_iter = lh_bytes
        .iter()
        .take(n_bytes_header)
        .scan(last_row.encoded_data.value_rlc, |acc, &byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        });

    (
        byte_offset + n_bytes_header,
        lh_bytes
            .iter()
            .take(n_bytes_header)
            .zip(tag_value_iter)
            .zip(value_rlc_iter)
            .enumerate()
            .map(
                |(i, ((&value_byte, tag_value_acc), value_rlc))| ZstdWitnessRow {
                    state: ZstdState {
                        tag: ZstdTag::ZstdBlockLiteralsHeader,
                        tag_next,
                        tag_len: n_bytes_header as u64,
                        tag_idx: (i + 1) as u64,
                        tag_value,
                        tag_value_acc,
                    },
                    encoded_data: EncodedData {
                        byte_idx: (byte_offset + i + 1) as u64,
                        encoded_len: last_row.encoded_data.encoded_len,
                        value_byte,
                        reverse: false,
                        value_rlc,
                        ..Default::default()
                    },
                    decoded_data: last_row.decoded_data.clone(),
                    huffman_data: HuffmanData::default(),
                    fse_data: FseTableRow::default(),
                },
            )
            .collect::<Vec<_>>(),
        literals_block_type,
        n_streams,
        regen_size as usize,
        compressed_size as usize,
    )
}

fn process_block_zstd_huffman_code_direct<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
    n_bytes: usize,
) -> (usize, Vec<ZstdWitnessRow<F>>, HuffmanCodesData) {
    // For direct representation of huffman weights, each byte (8 bits) represents two weights. 
    // weight[0] = (Byte[0] >> 4)
    // weight[1] = (Byte[0] & 0xf).

    let value_rlc_iter = src
        .iter()
        .skip(byte_offset)
        .take(n_bytes)
        .scan(
            last_row.encoded_data.value_rlc,
            |acc, &byte| {
                *acc = *acc * randomness + Value::known(F::from(byte as u64));
                Some(*acc)
            },
        )
        .into_iter()
        .flat_map(|v| vec![v, v]);

    let tag_value_iter = src
        .iter()
        .skip(byte_offset)
        .take(n_bytes)
        .scan(
            Value::known(F::zero()),
            |acc, &byte| {
                *acc = *acc * randomness + Value::known(F::from(byte as u64));
                Some(*acc)
            },
        )
        .into_iter()
        .flat_map(|v| vec![v, v]);

    let tag_value = tag_value_iter
        .clone()
        .last()
        .expect("Raw bytes must be of non-zero length");

    let mut weights: Vec<FseSymbol> = vec![];

    (
        byte_offset + n_bytes,
        src.iter()
            .skip(byte_offset)
            .take(n_bytes)
            .into_iter()
            .flat_map(|v| vec![v, v])
            .zip(tag_value_iter)
            .zip(value_rlc_iter)
            .zip((0..).cycle().take(n_bytes * 2))
            .enumerate()
            .map(
                |(i, (((&value_byte, tag_value_acc), value_rlc), b_flag))| {
                    weights.push(FseSymbol::from((if b_flag > 0 { value_byte >> 4 } else { value_byte & 0xf }) as usize));

                    ZstdWitnessRow {
                        state: ZstdState {
                            tag: ZstdTag::ZstdBlockHuffmanCode,
                            tag_next: ZstdTag::ZstdBlockSequenceHeader,
                            tag_len: n_bytes as u64,
                            tag_idx: (i / 2) as u64,
                            tag_value,
                            tag_value_acc,
                        },
                        encoded_data: EncodedData {
                            byte_idx: (byte_offset + i / 2 + 1) as u64,
                            encoded_len: last_row.encoded_data.encoded_len,
                            value_byte: value_byte,
                            value_rlc,
                            reverse: false,
                            ..Default::default()
                        },
                        decoded_data: last_row.decoded_data.clone(),
                        huffman_data: HuffmanData::default(),
                        fse_data: FseTableRow::default(),
                    }
                },
            )
            .collect::<Vec<_>>(),
            HuffmanCodesData { byte_offset: byte_offset as u64, weights: weights }
    )
}

fn process_block_zstd_huffman_code<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
    n_streams: usize,
) -> (usize, Vec<ZstdWitnessRow<F>>, HuffmanCodesData, usize) {
    // Preserve this value for later construction of HuffmanCodesDataTable
    let huffman_code_byte_offset = byte_offset;

    // Get the next tag
    let tag_next = if n_streams > 1 {
        ZstdTag::ZstdBlockJumpTable
    } else {
        ZstdTag::ZstdBlockLstream
    };

    // Parse the header byte
    let mut witness_rows: Vec<ZstdWitnessRow<F>> = vec![];
    let header_byte = src[byte_offset];

    let n_bytes = if header_byte < 128 {
        header_byte as usize
    } else {
        let n_sym: usize = header_byte as usize - 127;
        if n_sym.is_odd() {
            (n_sym + 1) / 2
        } else {
            n_sym / 2
        }
    };

    // TODO: Awaiting design decision
    // Currently the FSE decoding is assumed. Direct representation is a reserve possibility
    // The code for decoding direct representation is above. 
    assert!(header_byte < 128, "FSE encoded huffman weights assumed");

    // Get accumulators
    let mut value_rlc_iter = src.iter().skip(byte_offset).take(n_bytes + 1).scan(
        last_row.encoded_data.value_rlc,
        |acc, &byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        },
    );

    let mut tag_value_iter = src.iter().skip(byte_offset).take(n_bytes + 1).scan(
        Value::known(F::zero()),
        |acc, &byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        },
    );

    let tag_value = tag_value_iter
        .clone()
        .last()
        .expect("Raw bytes must be of non-zero length");

    // Add a witness row for Huffman header
    witness_rows.push(ZstdWitnessRow {
        state: ZstdState {
            tag: ZstdTag::ZstdBlockHuffmanCode,
            tag_next,
            tag_len: (n_bytes + 1) as u64, // include the 1 byte from huffman header
            tag_idx: 1 as u64,
            tag_value: tag_value,
            tag_value_acc: tag_value_iter.next().expect("Next value should exist"),
        },
        encoded_data: EncodedData {
            byte_idx: (byte_offset + 1) as u64,
            encoded_len: last_row.encoded_data.encoded_len,
            value_byte: header_byte.clone(),
            value_rlc: value_rlc_iter.next().expect("Next value should exist"),
            reverse: false,
            ..Default::default()
        },
        decoded_data: last_row.decoded_data.clone(),
        huffman_data: HuffmanData::default(),
        fse_data: FseTableRow::default(),
    });

    // Recover the FSE table for generating Huffman weights
    let byte_offset = byte_offset + 1;
    let (n_fse_bytes, table) = FseAuxiliaryTableData::reconstruct(&src, byte_offset).expect("Reconstructing FSE table should not fail.");

    // Witness generation
    let accuracy_log = (src[byte_offset] & 0b1111) + 5;

    // Add witness rows for FSE representation bytes
    for (idx, byte) in src.iter().skip(byte_offset).take(n_fse_bytes).enumerate() {
        witness_rows.push(ZstdWitnessRow {
            state: ZstdState {
                tag: ZstdTag::ZstdBlockHuffmanCode,
                tag_next,
                tag_len: (n_bytes + 1) as u64,
                tag_idx: (idx + 2) as u64, // count the huffman header byte
                tag_value: tag_value,
                tag_value_acc: tag_value_iter.next().expect("Next value should exist"),
            },
            encoded_data: EncodedData {
                byte_idx: (byte_offset + idx + 2) as u64, // count the huffman header byte
                encoded_len: last_row.encoded_data.encoded_len,
                value_byte: byte.clone(),
                value_rlc: value_rlc_iter.next().expect("Next value should exist"),
                reverse: false,
                ..Default::default()
            },
            decoded_data: last_row.decoded_data.clone(),
            huffman_data: HuffmanData::default(),
            fse_data: FseTableRow::default(),
        });
    }

    // Construct the Huffman bitstream
    let huffman_bitstream = 
        src
            .iter()
            .skip(byte_offset)
            .take(n_bytes)
            .rev()
            .clone()
            .flat_map(|v|{
                let mut bits = value_bits_le(*v);
                bits.reverse();
                bits
            })
            .collect::<Vec<u8>>();

    // Bitstream processing state values
    let mut last_byte_idx: usize = 1;
    let mut current_byte_idx: usize = 1; // byte_idx is 1-indexed
    let mut current_bit_idx: usize = 0;

    let mut next_tag_value_acc = tag_value_iter.next().unwrap();
    let mut next_value_rlc_acc = value_rlc_iter.next().unwrap();

    // Add a witness row for leading 0s
    witness_rows.push(ZstdWitnessRow {
        state: ZstdState {
            tag: ZstdTag::ZstdBlockHuffmanCode,
            tag_next,
            tag_len: (n_bytes + 1) as u64, // count huffman header byte
            tag_idx: ((n_fse_bytes - 1) + current_byte_idx + 1) as u64, 
            tag_value: tag_value,
            tag_value_acc: next_tag_value_acc,
        },
        encoded_data: EncodedData {
            byte_idx: (byte_offset + (n_fse_bytes - 1) + current_byte_idx) as u64,
            encoded_len: last_row.encoded_data.encoded_len,
            value_byte: src[byte_offset + (n_fse_bytes - 1) + current_byte_idx],
            value_rlc: next_value_rlc_acc,
            reverse: false,
            ..Default::default()
        },
        huffman_data: HuffmanData::default(),
        decoded_data: last_row.decoded_data.clone(),
        fse_data: FseTableRow::default(),
    });

    // Exclude the leading zero section
    while huffman_bitstream[current_bit_idx] == 0 {
        (current_byte_idx, current_bit_idx) = increment_idx(current_byte_idx, current_bit_idx);
    }
    if current_byte_idx > last_byte_idx {
        next_tag_value_acc = tag_value_iter.next().unwrap();
        next_value_rlc_acc = value_rlc_iter.next().unwrap();
        last_byte_idx = current_byte_idx;
    }

    // Add a witness row for sentinel 1-bit
    witness_rows.push(ZstdWitnessRow {
        state: ZstdState {
            tag: ZstdTag::ZstdBlockHuffmanCode,
            tag_next,
            tag_len: (n_bytes + 1) as u64,
            tag_idx: ((n_fse_bytes - 1) + current_byte_idx + 1) as u64,
            tag_value: tag_value,
            tag_value_acc: next_tag_value_acc,
        },
        encoded_data: EncodedData {
            byte_idx: (byte_offset + (n_fse_bytes - 1) + current_byte_idx) as u64,
            encoded_len: last_row.encoded_data.encoded_len,
            value_byte: src[byte_offset + (n_fse_bytes - 1) + current_byte_idx],
            value_rlc: next_value_rlc_acc,
            reverse: false,
            ..Default::default()
        },
        huffman_data: HuffmanData::default(),
        decoded_data: last_row.decoded_data.clone(),
        fse_data: FseTableRow::default(),
    });
    // Exclude the sentinel 1-bit
    (current_byte_idx, current_bit_idx) = increment_idx(current_byte_idx, current_bit_idx);
    if current_byte_idx > last_byte_idx {
        next_tag_value_acc = tag_value_iter.next().unwrap();
        next_value_rlc_acc = value_rlc_iter.next().unwrap();
        last_byte_idx = current_byte_idx;
    }

    // Now the actual weight-bearing bitstream starts
    // The Huffman bitstream is decoded by two interleaved states reading the stream in alternating order.
    // The FSE table for the two independent decoding strands are the same.
    let mut color: usize = 0; // use 0, 1 (colors) to denote two alternating decoding strands. 
    let mut prev_baseline: [u64; 2] = [0, 0];
    let mut next_nb_to_read: [usize; 2] = [accuracy_log as usize, accuracy_log as usize];
    let mut decoded_weights: Vec<u8> = vec![];
    let mut fse_table_idx: u64 = 1;

    // Convert FSE auxiliary data into a state-indexed representation
    let fse_state_table = table.parse_state_table();

    while current_bit_idx + next_nb_to_read[color] <= (n_bytes - n_fse_bytes) * N_BITS_PER_BYTE {
        let nb = next_nb_to_read[color];
        let next_state = prev_baseline[color] + le_bits_to_value(&huffman_bitstream[current_bit_idx..(current_bit_idx + nb)]);

        // Lookup the FSE table row for the state
        let fse_row = fse_state_table.get(&(next_state as u64)).expect("next state should be in fse table");

        // Decode the symbol
        decoded_weights.push(fse_row.0 as u8);

        // Add a witness row
        witness_rows.push(ZstdWitnessRow {
            state: ZstdState {
                tag: ZstdTag::ZstdBlockHuffmanCode,
                tag_next,
                tag_len: (n_bytes + 1) as u64,
                tag_idx: ((n_fse_bytes - 1) + current_byte_idx + 1) as u64,
                tag_value: tag_value,
                tag_value_acc: next_tag_value_acc,
            },
            encoded_data: EncodedData {
                byte_idx: (byte_offset + (n_fse_bytes - 1) + current_byte_idx) as u64,
                encoded_len: last_row.encoded_data.encoded_len,
                value_byte: src[byte_offset + (n_fse_bytes - 1) + current_byte_idx],
                value_rlc: next_value_rlc_acc,
                reverse: false,
                ..Default::default()
            },
            fse_data: FseTableRow {
                idx: fse_table_idx,
                state: next_state as u64,
                symbol: fse_row.0,
                baseline: fse_row.1,
                num_bits: fse_row.2,  
            },
            huffman_data: HuffmanData::default(),
            decoded_data: last_row.decoded_data.clone(),
        });

        // increment fse idx
        fse_table_idx += 1;

        // Advance byte and bit marks. Get next acc value if byte changes
        for _ in 0..nb {
            (current_byte_idx, current_bit_idx) = increment_idx(current_byte_idx, current_bit_idx);
        }
        if current_byte_idx > last_byte_idx && current_byte_idx < n_bytes {
            next_tag_value_acc = tag_value_iter.next().unwrap_or_default();
            next_value_rlc_acc = value_rlc_iter.next().unwrap_or_default();
            last_byte_idx = current_byte_idx;
        }

        // Preparing for next state
        prev_baseline[color] = fse_row.1;
        next_nb_to_read[color] = fse_row.2 as usize;

        color = if color > 0 { 0 } else { 1 };
    }

    // Construct HuffmanCodesTable
    let huffman_codes = HuffmanCodesData {
        byte_offset: huffman_code_byte_offset as u64,
        weights: decoded_weights.into_iter().map(|w| FseSymbol::from(w as usize) ).collect()
    };

    (byte_offset + n_bytes, witness_rows, huffman_codes, n_bytes)
}

fn process_block_zstd_huffman_jump_table<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    literal_stream_size: usize,
    n_streams: usize,
    randomness: Value<F>,
) -> (usize, Vec<ZstdWitnessRow<F>>, Vec<u64>) {
    if n_streams <= 1 {
        (byte_offset, vec![], vec![literal_stream_size as u64])
    } else {
        // Note: The decompressed size of each stream is equal to (regen_size + 3) / 4
        // but the compressed bitstream length will be different. 
        // Jump table provides information on the length of first 3 bitstreams. 

        let jt_bytes = src
            .iter()
            .skip(byte_offset)
            .take(N_JUMP_TABLE_BYTES)
            .cloned()
            .map(|x| x as u64)
            .collect::<Vec<u64>>();

        let l1: u64 = jt_bytes[0] + jt_bytes[1] * 256;
        let l2: u64 = jt_bytes[2] + jt_bytes[3] * 256;
        let l3: u64 = jt_bytes[4] + jt_bytes[5] * 256;
        let l4: u64 = (literal_stream_size as u64) - l1 - l2 - l3;

        let value_rlc_iter = src.iter().skip(byte_offset).take(N_JUMP_TABLE_BYTES).scan(
            last_row.encoded_data.value_rlc,
            |acc, &byte| {
                *acc = *acc * randomness + Value::known(F::from(byte as u64));
                Some(*acc)
            },
        );
        let tag_value_iter = src.iter().skip(byte_offset).take(N_JUMP_TABLE_BYTES).scan(
            Value::known(F::zero()),
            |acc, &byte| {
                *acc = *acc * randomness + Value::known(F::from(byte as u64));
                Some(*acc)
            },
        );
        let tag_value = tag_value_iter
            .clone()
            .last()
            .expect("Tag value must exist.");

        (
            byte_offset + N_JUMP_TABLE_BYTES,
            src.iter()
                .skip(byte_offset)
                .take(N_JUMP_TABLE_BYTES)
                .zip(tag_value_iter)
                .zip(value_rlc_iter)
                .enumerate()
                .map(
                    |(i, ((&value_byte, tag_value_acc), value_rlc))| {
                        ZstdWitnessRow {
                            state: ZstdState {
                                tag: ZstdTag::ZstdBlockJumpTable,
                                tag_next: ZstdTag::ZstdBlockLstream,
                                tag_len: N_JUMP_TABLE_BYTES as u64,
                                tag_idx: (i + 1) as u64,
                                tag_value,
                                tag_value_acc,
                            },
                            encoded_data: EncodedData {
                                byte_idx: (byte_offset + i + 1) as u64,
                                encoded_len: last_row.encoded_data.encoded_len,
                                value_byte,
                                value_rlc,
                                reverse: false,
                                ..Default::default()
                            },
                            decoded_data: last_row.decoded_data.clone(),
                            huffman_data: HuffmanData::default(),
                            fse_data: FseTableRow::default(),
                        }
                    },
                )
                .collect::<Vec<_>>(),
            vec![l1, l2, l3, l4]
        )
    }
}

fn process_block_zstd_lstream<F: Field>(
    src: &[u8],
    byte_offset: usize,
    len: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
    stream_idx: usize,
    huffman_code: &HuffmanCodesData,
) -> (usize, Vec<ZstdWitnessRow<F>>, Vec<u64>) {
    // Obtain literal stream bits (reversed).
    let lstream_bits = src
        .iter()
        .skip(byte_offset)
        .take(len)
        .rev()
        .clone()
        .flat_map(|v| {
            let mut bits = value_bits_le(*v);
            bits.reverse();
            bits
        })
        .collect::<Vec<u8>>();

    // Bitstream processing state helper values
    let mut witness_rows: Vec<ZstdWitnessRow<F>> = vec![];
    let mut current_byte_idx: usize = 1;
    let mut current_bit_idx: usize = 0;

    // accumulators
    let aux_1 = last_row.encoded_data.value_rlc;
    let value_rlc_acc = src.iter().skip(byte_offset).take(len).rev().scan(
        last_row.encoded_data.value_rlc,
        |acc, &byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        },
    ).collect::<Vec<Value<F>>>();
    let tag_value_acc = src.iter().skip(byte_offset).take(len).rev().scan(
        Value::known(F::zero()),
        |acc, &byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        },
    ).collect::<Vec<Value<F>>>();
    let tag_value = tag_value_acc.last().expect("Tag value exists");

    // Decide the next tag
    let tag_next = match stream_idx {
        0 | 1 | 2 => ZstdTag::ZstdBlockLstream,
        3 => ZstdTag::ZstdBlockSequenceHeader,
        _ => unreachable!("stream_idx value out of range")
    };

    // Add a witness row for leading 0s
    witness_rows.push(ZstdWitnessRow {
        state: ZstdState {
            tag: ZstdTag::ZstdBlockLstream,
            tag_next,
            tag_len: len as u64,
            tag_idx: current_byte_idx as u64,
            tag_value: *tag_value,
            tag_value_acc: tag_value_acc[current_byte_idx - 1],
        },
        encoded_data: EncodedData {
            byte_idx: (byte_offset + len - current_byte_idx) as u64,
            encoded_len: last_row.encoded_data.encoded_len,
            value_byte: src[byte_offset + len - current_byte_idx],
            value_rlc: value_rlc_acc[current_byte_idx - 1],
            // reverse specific values
            reverse: true,
            reverse_len: len as u64,
            reverse_idx: (len - (current_byte_idx - 1)) as u64,
            aux_1,
            aux_2: *tag_value,
            ..Default::default()
        },
        huffman_data: HuffmanData::default(),
        decoded_data: last_row.decoded_data.clone(),
        fse_data: FseTableRow::default(),
    });
    
    // Exclude the leading zero section
    while lstream_bits[current_bit_idx] == 0 {
        (current_byte_idx, current_bit_idx) = increment_idx(current_byte_idx, current_bit_idx);
    }

    // Add a witness row for sentinel 1-bit
    witness_rows.push(ZstdWitnessRow {
        state: ZstdState {
            tag: ZstdTag::ZstdBlockLstream,
            tag_next,
            tag_len: len as u64,
            tag_idx: current_byte_idx as u64,
            tag_value: *tag_value,
            tag_value_acc: tag_value_acc[current_byte_idx - 1],
        },
        encoded_data: EncodedData {
            byte_idx: (byte_offset + len - current_byte_idx) as u64,
            encoded_len: last_row.encoded_data.encoded_len,
            value_byte: src[byte_offset + len - current_byte_idx],
            value_rlc: value_rlc_acc[current_byte_idx - 1],
            // reverse specific values
            reverse: true,
            reverse_len: len as u64,
            reverse_idx: (len - (current_byte_idx - 1)) as u64,
            aux_1,
            aux_2: *tag_value,
            ..Default::default()
        },
        huffman_data: HuffmanData::default(),
        decoded_data: last_row.decoded_data.clone(),
        fse_data: FseTableRow::default(),
    });

    // Exclude the sentinel 1-bit
    increment_idx(current_byte_idx, current_bit_idx);

    // Now the actual symbol-bearing bitstream starts
    let huffman_bitstring_map = huffman_code.parse_bitstring_map();
    let mut decoded_symbols: Vec<u64> = vec![];
    let mut bit_value_acc: u64 = 0;
    let mut cur_bitstring_len: usize = 0;

    // compression_debug
    // log::trace!("=> huffman_bit_value_map: {:?}", huffman_bit_value_map);

    // compression_debug
    // while current_bit_idx < len * N_BITS_PER_BYTE {
    //     // compression_debug
    //     log::trace!("=> bit_value_acc: {:?}", bit_value_acc);
    //     log::trace!("=> cur_bitstring_len: {:?}", cur_bitstring_len);


    //     if huffman_bit_value_map.1.contains_key(&bit_value_acc) {
    //         decoded_symbols.push(huffman_bit_value_map.1.get(&bit_value_acc).unwrap().clone());
            
    //         let from_byte_idx = current_byte_idx;
    //         let from_bit_idx = current_bit_idx;

    //         // advance byte and bit marks to the last bit
    //         for _ in 0..(cur_bitstring_len - 1) {
    //             increment_idx(current_byte_idx, current_bit_idx);
    //         }

    //         // Add a witness row for emitted symbol
    //         witness_rows.push(ZstdWitnessRow {
    //             state: ZstdState {
    //                 tag: ZstdTag::ZstdBlockLstream,
    //                 tag_next,
    //                 tag_len: len as u64,
    //                 tag_idx: from_byte_idx as u64,
    //                 tag_value: *tag_value,
    //                 tag_value_acc: tag_value_acc[from_byte_idx - 1],
    //             },
    //             encoded_data: EncodedData {
    //                 byte_idx: (byte_offset + len - from_byte_idx) as u64,
    //                 encoded_len: last_row.encoded_data.encoded_len,
    //                 value_byte: src[byte_offset + len - from_byte_idx],
    //                 value_rlc: value_rlc_acc[from_byte_idx - 1],
    //                 // reverse specific values
    //                 reverse: true,
    //                 reverse_len: len as u64,
    //                 reverse_idx: (len - (from_byte_idx - 1)) as u64,
    //                 aux_1,
    //                 aux_2: *tag_value,
    //                 ..Default::default()
    //             },
    //             huffman_data: HuffmanData {
    //                 byte_offset: (byte_offset + len - from_byte_idx) as u64,
    //                 bit_value: bit_value_acc as u8,
    //                 k: (from_bit_idx.rem_euclid(8) as u8, current_bit_idx.rem_euclid(8) as u8),
    //             },
    //             decoded_data: last_row.decoded_data.clone(),
    //             fse_data: FseTableRow::default(),
    //         });

    //         // advance byte and bit marks again to get the start of next bitstring
    //         increment_idx(current_byte_idx, current_bit_idx);

    //         // Reset decoding state
    //         bit_value_acc = 0;
    //         cur_bitstring_len = 0;
    //     } else {
    //         bit_value_acc = bit_value_acc * 2 + lstream_bits[current_bit_idx + cur_bitstring_len] as u64;
    //         cur_bitstring_len += 1;

    //         if cur_bitstring_len > huffman_bit_value_map.0 as usize {
    //             panic!("Reading bit len greater than max bitstring len not allowed.");
    //         }
    //     }
    // }

    (byte_offset + len, witness_rows.into_iter().rev().collect::<Vec<ZstdWitnessRow<F>>>(), decoded_symbols)
}

pub fn process<F: Field>(src: &[u8], randomness: Value<F>) -> Vec<ZstdWitnessRow<F>> {
    let mut witness_rows = vec![];
    let byte_offset = 0;

    // FrameHeaderDescriptor and FrameContentSize
    let (byte_offset, rows) = process_frame_header::<F>(
        src,
        byte_offset,
        &ZstdWitnessRow::init(src.len()),
        randomness,
    );
    witness_rows.extend_from_slice(&rows);

    loop {
        let (byte_offset, rows, last_block) = process_block::<F>(
            src,
            byte_offset,
            rows.last().expect("last row expected to exist"),
            randomness,
        );
        witness_rows.extend_from_slice(&rows);

        if last_block {
            assert!(byte_offset >= src.len());
            break;
        }
    }

    #[cfg(test)]
    let _ = draw_rows(&witness_rows);

    witness_rows
}

#[cfg(test)]
mod tests {
    use halo2_proofs::halo2curves::bn256::Fr;
    use hex::FromHex;
    use std::io::Write;

    use super::*;

    #[test]
    fn batch_compression() -> Result<(), std::io::Error> {
        let raw = <Vec<u8>>::from_hex(r#"0100000000000231fb0000000064e588f7000000000000000000000000000000000000000000000000000000000000000000000000007a12000006000000000219f90216038510229a150083039bd49417afd0263d6909ba1f9a8eac697f76532365fb95880234e1a857498000b901a45ae401dc0000000000000000000000000000000000000000000000000000000064e58a1400000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000e404e45aaf0000000000000000000000005300000000000000000000000000000000000004000000000000000000000000d9692f1748afee00face2da35242417dd05a86150000000000000000000000000000000000000000000000000000000000000bb8000000000000000000000000c3100d07a5997a7f9f9cdde967d396f9a2aed6a60000000000000000000000000000000000000000000000000234e1a8574980000000000000000000000000000000000000000000000000049032ac61d5dce9e600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000083104ec1a053077484b4d7a88434c2d03c30c3c55bd3a82b259f339f1c0e1e1244189009c5a01c915dd14aed1b824bf610a95560e380ea3213f0bf345df3bddff1acaf7da84d000002d8f902d5068510229a1500830992fd94bbad0e891922a8a4a7e9c39d4cc0559117016fec87082b6be7f5b757b90264ac9650d800000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000001e00000000000000000000000000000000000000000000000000000000000000164883164560000000000000000000000005300000000000000000000000000000000000004000000000000000000000000ffd2ece82f7959ae184d10fe17865d27b4f0fb9400000000000000000000000000000000000000000000000000000000000001f4fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffce9f6fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcea0a00000000000000000000000000000000000000000000000000082b6be7f5b75700000000000000000000000000000000000000000000000000000000004c4b40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006aea61ea08dd6e4834cd43a257ed52d9a31dd3b90000000000000000000000000000000000000000000000000000000064e58a1400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000412210e8a0000000000000000000000000000000000000000000000000000000083104ec2a0bc501c59bceb707d958423bad14c0d0daec84ad067f7e42209ad2cb8d904a55da00a04de4c79ed24b7a82d523b5de63c7ff68a3b7bb519546b3fe4ba8bc90a396600000137f9013480850f7eb06980830317329446ce46951d12710d85bc4fe10bb29c6ea501207787019945ca262000b8c4b2dd898a000000000000000000000000000000000000000000000000000000000000002000000000000000000000000065e4e8d7bd50191abfee6e5bcdc4d16ddfe9975e000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000083104ec2a037979a5225dd156f51abf9a8601e9156e1b1308c0474d69af98c55627886232ea048ac197295187e7ad48aa34cc37c2625434fa812449337732d8522014f4eacfc00000137f9013480850f7eb06980830317329446ce46951d12710d85bc4fe10bb29c6ea501207787019945ca262000b8c4b2dd898a000000000000000000000000000000000000000000000000000000000000002000000000000000000000000065e4e8d7bd50191abfee6e5bcdc4d16ddfe9975e000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000083104ec1a087269dbb9e987e5d58ecd3bcb724cbc4e6c843eb9095de16a25263aebfe06f5aa07f3ac49b6847ba51c5319174e51e088117742240f8555c5c1d77108cf0df90d700000137f9013480850f7eb06980830317329446ce46951d12710d85bc4fe10bb29c6ea501207787019945ca262000b8c4b2dd898a000000000000000000000000000000000000000000000000000000000000002000000000000000000000000065e4e8d7bd50191abfee6e5bcdc4d16ddfe9975e000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000083104ec1a04abdb8572dcabf1996825de6f753124eed41c1292fcfdc4d9a90cb4f8a0f8ff1a06ef25857e2cc9d0fa8b6ecc03b4ba6ef6f3ec1515d570fcc9102e2aa653f347a00000137f9013480850f7eb06980830317329446ce46951d12710d85bc4fe10bb29c6ea501207787019945ca262000b8c4b2dd898a000000000000000000000000000000000000000000000000000000000000002000000000000000000000000065e4e8d7bd50191abfee6e5bcdc4d16ddfe9975e000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000083104ec2a0882202163cbb9a299709b443b663fbab459440deabfbe183e999c98c00ea80c2a010ecb1e5196f0b1ee3d067d9a158b47b1376706e42ce2e769cf8e986935781dd"#)
            .expect("FromHex failure");
        let compressed = {
            let mut encoder = zstd::stream::write::Encoder::new(Vec::new(), 0)?;
            encoder.set_pledged_src_size(Some(raw.len() as u64))?;
            encoder.include_checksum(false)?;
            encoder.include_magicbytes(false)?;
            encoder.include_contentsize(true)?;
            encoder.write_all(&raw)?;
            encoder.finish()?
        };

        let _witness_rows = process::<Fr>(&compressed, Value::known(Fr::from(123456789)));

        Ok(())
    }

    // Verify correct interleaved decoding of FSE-coded Huffman Weights
    // Example link: https://nigeltao.github.io/blog/2022/zstandard-part-5-fse.html
    #[test]
    fn interleaved_huffman_code_fse() -> Result<(), std::io::Error> {
        // Input includes FSE table representation (normalized symbol frequencies) and the actual Huffman bitstream
        // For structure reference: https://nigeltao.github.io/blog/2022/zstandard-part-2-structure.html
        let input: [u8; 36] = [
            0x23, 0x30, 0x6f, 0x9b, 0x03, 0x7d, 0xc7, 0x16, 
            0x0b, 0xbe, 0xc8, 0xf2, 0xd0, 0x22, 0x4b, 0x6b, 
            0xbc, 0x54, 0x5d, 0xa9, 0xd4, 0x93, 0xef, 0xc4, 
            0x54, 0x96, 0xb2, 0xe2, 0xa8, 0xa8, 0x24, 0x1c, 
            0x54, 0x40, 0x29, 0x01,
        ];

        let (_byte_offset, _witness_rows, huffman_codes, _n_huffan_bytes) = 
            process_block_zstd_huffman_code::<Fr>(
                &input, 
                0, 
                &ZstdWitnessRow::init(0), 
                Value::known(Fr::from(123456789)), 
                4
            );

        let expected_weights: Vec<FseSymbol> = vec![
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            6, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 2, 0,
            0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2,
            0, 1, 1, 1, 1, 1, 0, 0, 1, 2, 1, 0, 1, 1, 1, 2,
            0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0,
            0, 5, 3, 3, 3, 6, 3, 2, 4, 4, 0, 1, 4, 4, 5, 5,
            2, 0, 4, 4, 5, 3, 1, 3, 1, 3,
        ]
        .into_iter()
        .map(|w| FseSymbol::from(w) )
        .collect::<Vec<FseSymbol>>();

        assert_eq!(
            huffman_codes.weights,
            expected_weights, 
            "Huffman weights should be correctly decoded with interleaved states"
        );

        Ok(())
    }



    // Verify correct decoding of literal bitstream using a HuffmanCode table
    // Example link: https://nigeltao.github.io/blog/2022/zstandard-part-4-huffman.html
    #[test]
    fn decode_literal_bitstream() -> Result<(), std::io::Error> {
        let huffman_codes = HuffmanCodesData {
            byte_offset: 0,
            weights: vec![
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                6, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 2, 0,
                0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2,
                0, 1, 1, 1, 1, 1, 0, 0, 1, 2, 1, 0, 1, 1, 1, 2,
                0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0,
                0, 5, 3, 3, 3, 6, 3, 2, 4, 4, 0, 1, 4, 4, 5, 5,
                2, 0, 4, 4, 5, 3, 1, 3, 1, 3,
            ]
            .into_iter()
            .map(|w| FseSymbol::from(w) )
            .collect::<Vec<FseSymbol>>()
        };

        let lstream1: [u8; 85] = [
            0xcc, 0x51, 0x73, 0x3a, 0x85, 0x9e, 0xf7, 0x59, 
            0xfc, 0xc5, 0xca, 0x6a, 0x7a, 0xd9, 0x82, 0x9c, 
            0x65, 0xc5, 0x45, 0x92, 0xe3, 0x0d, 0xf3, 0xef, 
            0x71, 0xee, 0xdc, 0xd5, 0xa2, 0xe3, 0x48, 0xad, 
            0xa3, 0xbc, 0x41, 0x7a, 0x3c, 0xaa, 0xd6, 0xeb, 
            0xd0, 0x77, 0xea, 0xdc, 0x5d, 0x41, 0x06, 0x50, 
            0x1c, 0x49, 0x0f, 0x07, 0x10, 0x05, 0x88, 0x84, 
            0x94, 0x02, 0xfc, 0x3c, 0xe3, 0x60, 0x25, 0xc0, 
            0xcb, 0x0c, 0xb8, 0xa9, 0x73, 0xbc, 0x13, 0x77, 
            0xc6, 0xe2, 0x20, 0xed, 0x17, 0x7b, 0x12, 0xdc, 
            0x24, 0x5a, 0xdf, 0xb4, 0x21, 
            // 0x9a,
        ];

        let (_byte_offset, _witness_rows, decoded_symbols) = process_block_zstd_lstream::<Fr>(
            &lstream1,
            0,
            85,
            &ZstdWitnessRow::init(0),
            Value::known(Fr::from(123456789)),
            1,
            &huffman_codes
        );

        let ascii_symbols: String = decoded_symbols.iter().filter_map(|&s| char::from_u32(s as u32)).collect();
        

        log::trace!("=> decoded: {:?}", decoded_symbols);
        log::trace!("=> ascii: {:?}", ascii_symbols);


        // 00000000  ++ ++ ++ ++ ++ ++ ++ ++  ++ ++ 76 62 5e 23 30 6f  |++++++++++[L]H[-|
        // 00000010  9b 03 7d c7 16 0b be c8  f2 d0 22 4b 6b bc 54 5d  |- HUFFMAN CODE -|
        // 00000020  a9 d4 93 ef c4 54 96 b2  e2 a8 a8 24 1c 54 40 29  |----------------|
        // 00000030  01 55 00 57 00 51 00 *cc  51 73 3a 85 9e f7 59 fc  |][JUMP][--------|
        // 00000040  c5 ca 6a 7a d9 82 9c 65  c5 45 92 e3 0d f3 ef 71  |----------------|
        // 00000050  ee dc d5 a2 e3 48 ad a3  bc 41 7a 3c aa d6 eb d0  | LSTREAM 1 DATA |
        // 00000060  77 ea dc 5d 41 06 50 1c  49 0f 07 10 05 88 84 94  |----------------|
        // 00000070  02 fc 3c e3 60 25 c0 cb  0c b8 a9 73 bc 13 77 c6  |----------------|
        // 00000080  e2 20 ed 17 7b 12 dc 24  5a df b4 21 9a* cb 8f c7  |-----------][---|
        // 00000090  58 54 11 a9 f1 47 82 9b  ba 60 b4 92 28 0e fb 8b  |----------------|
        // 000000a0  1e 92 23 6a cf bf e5 45  b5 7e eb 81 f1 78 4b ad  |----------------|
        // 000000b0  17 4d 81 9f bc 67 a7 56  ee b4 d9 e1 95 21 66 0c  | LSTREAM 2 DATA |
        // 000000c0  95 83 27 de ac 37 20 91  22 07 0b 91 86 94 1a 7b  |----------------|
        // 000000d0  f6 4c b0 c0 e8 2e 49 65  d6 34 63 0c 88 9b 1c 48  |----------------|
        // 000000e0  ca 2b 34 a9 6b 99 3b ee  13 3b 7c 93 0b f7 0d 49  |--][------------|
        // 000000f0  69 18 57 be 3b 64 45 1d  92 63 7f e8 f9 a1 19 7b  |----------------|
        // 00000100  7b 6e d8 a3 90 23 82 f4  a7 ce c8 f8 90 15 b3 14  | LSTREAM 3 DATA |
        // 00000110  f4 40 e7 02 78 d3 17 71  23 b1 19 ad 6b 49 ae 13  |----------------|
        // 00000120  a4 75 38 51 47 89 67 b0  39 b4 53 86 a4 ac aa a3  |----------------|
        // 00000130  34 89 ca 2e e9 c1 fe f2  51 c6 51 73 aa f7 9d 2d  |---][-----------|
        // 00000140  ed d9 b7 4a b2 b2 61 e4  ef 98 f7 c5 ef 51 9b d8  |----------------|
        // 00000150  dc 60 6c 41 76 af 78 1a  62 b5 4c 1e 21 39 9a 5f  | LSTREAM 4 DATA |
        // 00000160  ac 9d e0 62 e8 e9 2f 2f  48 02 8d 53 c8 91 f2 1a  |----------------|
        // 00000170  d2 7c 0a 7c 48 bf da a9  e3 38 da 34 ce 76 a9 da  |----------------|
        // 00000180  15 91 de 21 f5 55 46 a8  21 9d 51 cc 18 42 44 81  |-----]SS[-- LLT |
        // 00000190  8c 94 b4 50 1e 20 42 82  98 c2 3b 10 48 ec a6 39  |----][CMOT][MLT]|
        // 000001a0  63 13 a7 01 94 40 ff 88  0f 98 07 4a 46 38 05 a9  |[---------------|
        // 000001b0  cb f6 c8 21 59 aa 38 45  bf 5c f8 55 9e 9f 04 ed  |----------------|
        // 000001c0  c8 03 42 2a 4b f6 78 7e  23 67 15 a2 79 29 f4 9b  |----------------|
        // 000001d0  7e 00 bc 2f 46 96 99 ea  f1 ee 1c 6e 06 9c db e4  |----------------|
        // 000001e0  8c c2 05 f7 54 51 84 c0  33 02 01 b1 8c 80 dc 99  | SEQUENCES DATA |
        // 000001f0  8f cb 46 ff d1 25 b5 b6  3a f3 25 be 85 50 84 f5  |----------------|
        // 00000200  86 5a 71 f7 bd a1 4c 52  4f 20 a3 61 23 77 12 d3  |----------------|
        // 00000210  b1 58 75 22 01 12 70 ec  14 91 f9 85 61 d5 7e 98  |----------------|
        // 00000220  84 c9 76 84 bc b8 fe 4e  53 a5 06 ++ ++ ++ ++     |----------]++++|

        Ok(())
    }


}
