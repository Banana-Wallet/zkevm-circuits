use halo2_proofs::{arithmetic::FieldExt, plonk::Expression};
use rlp::Encodable;

use crate::impl_expr;

/// Data types that are supported by the RLP circuit.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum RlpDataType {
    /// Data type for an RLP-encoded unsigned transaction. The encoding consists
    /// of: [nonce, gas, gasprice, to, value, input, chainid, 0, 0].
    #[default]
    TxSign,
    /// Data type for an RLP-encoded signed transaction. The encoding consists
    /// of: [nonce, gas, gasprice, to, value, input, v, r, s].
    /// where the fields `v`, `r` and `s` represent the compressed form of an
    /// ECDSA signature.
    TxHash,
}

impl_expr!(RlpDataType);

/// Represents the witness in a single row of the RLP circuit.
#[derive(Clone, Debug, Default)]
pub struct RlpWitnessRow<F> {
    /// Denotes the transaction or receipt ID.
    pub id: usize,
    /// Denotes the index of this row, starting from 0 and ending at n-1 where n
    /// is the byte length of the RLP-encoded data.
    pub index: usize,
    /// Denotes the data type, whether this circuit encodes a RlpDataType::Tx or
    /// a RlpDataType::Receipt.
    pub data_type: RlpDataType,
    /// Denotes the byte value in the RLP-encoded data.
    pub value: u8,
    /// Accumulator value to represent the full value of the tag.
    pub value_acc: F,
    /// Denotes the row’s tag, which can be a field from the data type encoded.
    pub tag: u8,
    /// Denotes the current tag's length in bytes.
    pub tag_length: usize,
    /// Denotes a decrementing index specific to the tag in in the current block
    /// of bytes.
    pub tag_index: usize,
    /// Denotes an accumulator for the length of data, in the case where len >
    /// 55 and the length is represented in its big-endian form.
    pub length_acc: u64,
    /// Optional field to hold the calldata length.
    pub call_data_length: Option<u64>,
    /// Optional field to hold the calldata gas cost.
    pub call_data_gas_cost: Option<u64>,
}

/// The RlpWitnessGen trait is implemented by data types who's RLP encoding can
/// be verified by the RLP-encoding circuit.
pub trait RlpWitnessGen<F: FieldExt>: Encodable + std::marker::Sized {
    /// Generate witness to the RLP-encoding verifier circuit, as a vector of
    /// RlpWitnessRow.
    fn gen_witness(&self, randomness: F) -> Vec<RlpWitnessRow<F>>;

    /// Generate the RLP summary row.
    fn rlp_row(&self, randomness: F) -> RlpWitnessRow<F>;
}
