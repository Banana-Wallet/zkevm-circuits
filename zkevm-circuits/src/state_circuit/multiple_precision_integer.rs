use super::{lookups, param::*};
use crate::util::Expr;
use eth_types::{Address, Field, ToLittleEndian, Word};
use halo2_proofs::{
    circuit::{Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use itertools::Itertools;
use std::marker::PhantomData;

pub trait ToLimbs<const N: usize> {
    fn to_limbs(&self) -> [u16; N];
    fn annotation() -> &'static str;
}

impl ToLimbs<N_LIMBS_ACCOUNT_ADDRESS> for Address {
    fn to_limbs(&self) -> [u16; 10] {
        // address bytes are be.... maybe just have everything be later?
        // you will need this in the future later because it makes the key ordering more
        // obvious
        let le_bytes: Vec<_> = self.0.iter().rev().cloned().collect();
        le_bytes_to_limbs(&le_bytes).try_into().unwrap()
    }

    fn annotation() -> &'static str {
        "Address"
    }
}

impl ToLimbs<N_LIMBS_RW_COUNTER> for u32 {
    fn to_limbs(&self) -> [u16; 2] {
        le_bytes_to_limbs(&self.to_le_bytes()).try_into().unwrap()
    }

    fn annotation() -> &'static str {
        "u32"
    }
}

impl ToLimbs<N_LIMBS_WORD> for Word {
    fn to_limbs(&self) -> [u16; N_LIMBS_WORD] {
        le_bytes_to_limbs(&self.to_le_bytes()).try_into().unwrap()
    }
    fn annotation() -> &'static str {
        "Word"
    }
}

#[derive(Clone, Copy)]
pub struct Config<T, const N: usize>
where
    T: ToLimbs<N>,
{
    // TODO: we can save a column here by not storing the lsb, and then checking that
    // value - value_from_limbs(limbs.prepend(0)) fits into a limb.
    // Does this apply for RLC's too?
    pub limbs: [Column<Advice>; N],
    _marker: PhantomData<T>,
}

#[derive(Clone)]
pub struct Queries<F: Field, const N: usize> {
    pub limbs: [Expression<F>; N],
    pub limbs_prev: [Expression<F>; N],
}

impl<F: Field, const N: usize> Queries<F, N> {
    pub fn new<T: ToLimbs<N>>(meta: &mut VirtualCells<'_, F>, c: Config<T, N>) -> Self {
        Self {
            limbs: c.limbs.map(|limb| meta.query_advice(limb, Rotation::cur())),
            limbs_prev: c
                .limbs
                .map(|limb| meta.query_advice(limb, Rotation::prev())),
        }
    }
}

// address configs
impl Config<Address, N_LIMBS_ACCOUNT_ADDRESS> {
    pub fn assign<F: Field>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: Address,
    ) -> Result<(), Error> {
        assign_to_config(region, self, value, offset, "address")
    }

    /// Annotates columns of this gadget embedded within a circuit region.
    pub fn annotate_columns_in_region<F: Field>(&self, region: &mut Region<F>, prefix: &str) {
        annotate_columns_in_config(region, self, prefix, "address")
    }
}

impl Config<u32, N_LIMBS_RW_COUNTER> {
    pub fn assign<F: Field>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: u32,
    ) -> Result<(), Error> {
        assign_to_config(region, self, value, offset, "u32")
    }

    /// Annotates columns of this gadget embedded within a circuit region.
    pub fn annotate_columns_in_region<F: Field>(&self, region: &mut Region<F>, prefix: &str) {
        annotate_columns_in_config(region, self, prefix, "u32")
    }
}

fn assign_to_config<T: ToLimbs<N>, const N: usize, F: Field>(
    region: &mut Region<'_, F>,
    config: &Config<T, N>,
    value: T,
    offset: usize,
    prefix: &str,
) -> Result<(), Error> {
    for (i, &limb) in value.to_limbs().iter().enumerate() {
        region.assign_advice(
            || format!("limb[{i}] in {prefix} mpi"),
            config.limbs[i],
            offset,
            || Value::known(F::from(limb as u64)),
        )?;
    }
    Ok(())
}

fn annotate_columns_in_config<T: ToLimbs<N>, const N: usize, F: Field>(
    region: &mut Region<'_, F>,
    config: &Config<T, N>,
    prefix: &str,
    type_ann: &str,
) {
    let mut annotations = Vec::new();
    for (i, _) in config.limbs.iter().enumerate() {
        annotations.push(format!("MPI_limbs_{type_ann}_{i}"));
    }
    config
        .limbs
        .iter()
        .zip(annotations.iter())
        .for_each(|(col, ann)| region.name_column(|| format!("{prefix}_{ann}"), *col));
}

pub struct Chip<F: Field, T, const N: usize>
where
    T: ToLimbs<N>,
{
    _config: Config<T, N>,
    _marker: PhantomData<F>,
}

impl<F: Field, T, const N: usize> Chip<F, T, N>
where
    T: ToLimbs<N>,
{
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        selector: Column<Fixed>,
        value: Column<Advice>,
        lookup: lookups::Config,
    ) -> Config<T, N> {
        let limbs = [0; N].map(|_| meta.advice_column());

        for &limb in &limbs {
            lookup.range_check_u16(meta, "mpi limb fits into u16", |meta| {
                meta.query_advice(limb, Rotation::cur())
            });
        }

        // TODO: will remove later
        // for (n, value) in values.iter().enumerate() {
        //     meta.create_gate("mpi value matches claimed limbs", |meta| {
        //         let selector = meta.query_fixed(selector, Rotation::cur());
        //         let value_expr = meta.query_advice(*value, Rotation::cur());
        //         let value_limbs = &limbs[n * limbs_per_value..(n + 1) * limbs_per_value];
        //         let limbs_expr = value_limbs
        //             .iter()
        //             .map(|limb| meta.query_advice(*limb, Rotation::cur()));
        //         vec![selector * (value_expr - value_from_limbs(&limbs_expr.collect::<Vec<_>>()))]
        //     });
        // }

        meta.create_gate("mpi value matches claimed limbs", |meta| {
            let selector = meta.query_fixed(selector, Rotation::cur());
            let value = meta.query_advice(value, Rotation::cur());
            let limbs = limbs.map(|limb| meta.query_advice(limb, Rotation::cur()));
            vec![selector * (value - value_from_limbs(&limbs))]
        });

        Config {
            limbs,
            _marker: PhantomData,
        }
    }
}

fn le_bytes_to_limbs(bytes: &[u8]) -> Vec<u16> {
    bytes
        .iter()
        .tuples()
        .map(|(lo, hi)| u16::from_le_bytes([*lo, *hi]))
        .collect()
}

fn value_from_limbs<F: Field>(limbs: &[Expression<F>]) -> Expression<F> {
    limbs.iter().rev().fold(0u64.expr(), |result, limb| {
        limb.clone() + result * (1u64 << 16).expr()
    })
}

#[cfg(test)]
mod test {
    use super::ToLimbs;
    use eth_types::Address;

    #[test]
    pub fn display_limbs() {
        let val = 10u32;
        assert_eq!(val.to_limbs(), [10, 0]);

        let val = Address::from_low_u64_be(10);
        assert_eq!(val.to_limbs(), [10, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    }
}
