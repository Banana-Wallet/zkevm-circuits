//! The ECC circuit is responsible for verifying ECC-related operations from precompiled contract
//! calls, namely, EcAdd, EcMul and EcPairing.

use std::marker::PhantomData;

use bus_mapping::{
    circuit_input_builder::{EcAddOp, EcMulOp, EcPairingOp},
    precompile::PrecompileCalls,
};
use eth_types::Field;
use halo2_base::{gates::GateInstructions, utils::modulus, AssignedValue, Context, QuantumCell};
use halo2_ecc::{
    bigint::CRTInteger,
    bn254::pairing::PairingChip,
    ecc::{EcPoint, EccChip},
    fields::{
        fp::{FpConfig, FpStrategy},
        fp12::Fp12Chip,
        FieldChip, FieldExtPoint,
    },
};
use halo2_proofs::{
    arithmetic::Field as Halo2Field,
    circuit::{Layouter, Value},
    halo2curves::bn256::{Fq, Fq12, Fr, G1Affine, G2Affine},
    plonk::{ConstraintSystem, Error, Expression},
};
use itertools::Itertools;
use log::error;

use crate::{
    table::EccTable,
    util::{Challenges, SubCircuit, SubCircuitConfig},
    witness::Block,
};

/// TODO
#[derive(Clone, Debug)]
pub struct EccCircuitConfigArgs<F: Field> {
    /// ECC table that is connected to the ECC circuit.
    pub ecc_table: EccTable,
    /// zkEVM challenge API.
    pub challenges: Challenges<Expression<F>>,
}

/// TODO
#[derive(Clone, Debug)]
pub struct EccCircuitConfig<F: Field> {
    /// TODO
    fp_config: FpConfig<F, Fq>,
    /// TODO
    ecc_table: EccTable,

    _marker: PhantomData<F>,
}

impl<F: Field> SubCircuitConfig<F> for EccCircuitConfig<F> {
    type ConfigArgs = EccCircuitConfigArgs<F>;

    fn new(
        meta: &mut ConstraintSystem<F>,
        Self::ConfigArgs {
            ecc_table,
            challenges: _,
        }: Self::ConfigArgs,
    ) -> Self {
        // TODO: verify args to the configure method.
        let fp_config = FpConfig::configure(
            meta,
            FpStrategy::Simple,
            &[10, 1], // num advice
            &[17],    // num lookup advice
            1,        // num fixed
            13,       // lookup bits
            88,       // limb bits
            3,        // num limbs
            modulus::<Fq>(),
            0,
            10, // k
        );

        Self {
            fp_config,
            ecc_table,
            _marker: PhantomData,
        }
    }
}

/// The ECC Circuit is a sub-circuit of the super circuit, responsible for verifying the following
/// ECC operations:
/// 1. Point Addition (R = P + Q)
/// 2. Scalar Multiplication (R = s.P)
/// 3. Pairing-based bilinear function
///
/// We follow a strategy to pre-allocate maximum number of cells for each of the above ECC
/// operations, which means a witness that exceeds the pre-allocated number of cells for any of the
/// operations will be invalid.
#[derive(Clone, Debug)]
pub struct EccCircuit<F: Field> {
    /// Maximum number of EcAdd operations supported in one instance of the ECC Circuit.
    pub max_add_ops: usize,
    /// Maximum number of scalar multiplication operations supported in one instance of the ECC
    /// Circuit.
    pub max_mul_ops: usize,
    /// Maximum number of pairing operations supported in one instance of the ECC Circuit.
    pub max_pairing_ops: usize,

    /// EcAdd operations provided as witness data to the ECC circuit.
    pub add_ops: Vec<EcAddOp>,
    /// EcMul operations provided as witness data to the ECC circuit.
    pub mul_ops: Vec<EcMulOp>,
    /// EcPairing operations provided as witness data to the ECC circuit.
    pub pairing_ops: Vec<EcPairingOp>,

    _marker: PhantomData<F>,
}

struct G1Decomposed<F: Field> {
    ec_point: EcPoint<F, CRTInteger<F>>,
    x_cells: Vec<QuantumCell<F>>,
    y_cells: Vec<QuantumCell<F>>,
}

struct G1Assigned<F: Field> {
    decomposed: G1Decomposed<F>,
    x_rlc: AssignedValue<F>,
    y_rlc: AssignedValue<F>,
}

struct ScalarDecomposed<F: Field> {
    scalar: CRTInteger<F>,
    cells: Vec<QuantumCell<F>>,
}

struct ScalarAssigned<F: Field> {
    decomposed: ScalarDecomposed<F>,
    rlc: AssignedValue<F>,
}

struct G2Decomposed<F: Field> {
    ec_point: EcPoint<F, FieldExtPoint<CRTInteger<F>>>,
    x_c0_cells: Vec<QuantumCell<F>>,
    x_c1_cells: Vec<QuantumCell<F>>,
    y_c0_cells: Vec<QuantumCell<F>>,
    y_c1_cells: Vec<QuantumCell<F>>,
}

struct G2Assigned<F: Field> {
    decomposed: G2Decomposed<F>,
    x_c0_rlc: AssignedValue<F>,
    x_c1_rlc: AssignedValue<F>,
    y_c0_rlc: AssignedValue<F>,
    y_c1_rlc: AssignedValue<F>,
}

struct EcAddAssigned<F: Field> {
    point_p: G1Assigned<F>,
    point_q: G1Assigned<F>,
    point_r: G1Assigned<F>,
}

struct EcMulAssigned<F: Field> {
    point_p: G1Assigned<F>,
    scalar_s: ScalarAssigned<F>,
    point_r: G1Assigned<F>,
}

struct EcPairingAssigned<F: Field> {
    g1s: Vec<G1Assigned<F>>,
    g2s: Vec<G2Assigned<F>>,
    input_rlc: AssignedValue<F>,
    success: AssignedValue<F>,
}

struct EcOpsAssigned<F: Field> {
    ec_adds_assigned: Vec<EcAddAssigned<F>>,
    ec_muls_assigned: Vec<EcMulAssigned<F>>,
    ec_pairings_assigned: Vec<EcPairingAssigned<F>>,
}

impl<F: Field> EccCircuit<F> {
    pub(crate) fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        config: &<Self as SubCircuit<F>>::Config,
        challenges: &Challenges<Value<F>>,
    ) -> Result<(), Error> {
        if self.add_ops.len() > self.max_add_ops
            || self.mul_ops.len() > self.max_mul_ops
            || self.pairing_ops.len() > self.max_pairing_ops
        {
            error!(
                "add ops = {}, mul ops = {}, pairing ops = {} > max add ops = {}, max mul ops = {}, max pairing ops = {}",
                self.add_ops.len(),
                self.mul_ops.len(),
                self.pairing_ops.len(),
                self.max_add_ops,
                self.max_mul_ops,
                self.max_pairing_ops,
            );
            return Err(Error::Synthesis);
        }

        // for each pairing check input, we only allow up to 4 pairs, i.e. 4 * 192 bytes. The aim
        // is to simplify zkEVM implementation for now, not allowing dynamic length input for
        // EcPairing precompiled contract call.
        for pairing_op in self.pairing_ops.iter() {
            if pairing_op.inputs.len() > 4 {
                error!(
                    "pairing check inputs = {} max allowed = {}",
                    pairing_op.inputs.len(),
                    4,
                );
                return Err(Error::Synthesis);
            }
        }

        // keccak powers of randomness.
        let keccak_powers = std::iter::successors(Some(Value::known(F::one())), |coeff| {
            Some(challenges.keccak_input() * coeff)
        })
        .take(192)
        .map(|x| QuantumCell::Witness(x))
        .collect_vec();

        let fp_chip = EccChip::<F, FpConfig<F, Fq>>::construct(config.fp_config.clone());
        let fr_chip =
            FpConfig::<F, Fr>::construct(config.fp_config.range.clone(), 88, 3, modulus::<Fr>());
        let pairing_chip = PairingChip::construct(config.fp_config.clone());
        let fp12_chip =
            Fp12Chip::<F, FpConfig<F, Fq>, Fq12, 9>::construct(config.fp_config.clone());

        let assigned_ec_ops = layouter.assign_region(
            || "ecc circuit",
            |region| {
                let mut ctx = config.fp_config.new_context(region);

                // P + Q == R
                let ec_adds_assigned = self
                    .add_ops
                    .iter()
                    .chain(std::iter::repeat(&EcAddOp::default()))
                    .take(self.max_add_ops)
                    .map(|add_op| {
                        let point_p =
                            self.assign_g1(&mut ctx, &fp_chip, add_op.p, keccak_powers.clone());
                        let point_q =
                            self.assign_g1(&mut ctx, &fp_chip, add_op.q, keccak_powers.clone());
                        let point_r =
                            self.assign_g1(&mut ctx, &fp_chip, add_op.r, keccak_powers.clone());
                        let point_r_got = fp_chip.add_unequal(
                            &mut ctx,
                            &point_p.decomposed.ec_point,
                            &point_q.decomposed.ec_point,
                            false, /* strict == false, as we do not check for whether or not P
                                    * == Q */
                        );
                        fp_chip.assert_equal(&mut ctx, &point_r.decomposed.ec_point, &point_r_got);
                        EcAddAssigned {
                            point_p,
                            point_q,
                            point_r,
                        }
                    })
                    .collect_vec();

                // s.P = R
                let ec_muls_assigned = self
                    .mul_ops
                    .iter()
                    .chain(std::iter::repeat(&EcMulOp::default()))
                    .take(self.max_mul_ops)
                    .map(|mul_op| {
                        let point_p =
                            self.assign_g1(&mut ctx, &fp_chip, mul_op.p, keccak_powers.clone());
                        let scalar_s =
                            self.assign_fr(&mut ctx, &fr_chip, mul_op.s, keccak_powers.clone());
                        let point_r =
                            self.assign_g1(&mut ctx, &fp_chip, mul_op.r, keccak_powers.clone());
                        let point_r_got = fp_chip.scalar_mult(
                            &mut ctx,
                            &point_p.decomposed.ec_point,
                            &scalar_s.decomposed.scalar.limbs().to_vec(),
                            fr_chip.limb_bits,
                            4, // TODO: window bits?
                        );
                        fp_chip.assert_equal(&mut ctx, &point_r.decomposed.ec_point, &point_r_got);
                        EcMulAssigned {
                            point_p,
                            scalar_s,
                            point_r,
                        }
                    })
                    .collect_vec();

                // e(G1 . G2) * ... * e(G1 . G2) -> Gt
                // Note: maximum 4 pairings per pairing op.
                let ec_pairings_assigned = self
                    .pairing_ops
                    .iter()
                    .chain(std::iter::repeat(&EcPairingOp::default()))
                    .take(self.max_pairing_ops)
                    .map(|pairing_op| {
                        let g1s = pairing_op
                            .inputs
                            .iter()
                            .map(|i| {
                                let (x_cells, y_cells) = self.decompose_g1(i.0);
                                let decomposed = G1Decomposed {
                                    ec_point: pairing_chip
                                        .load_private_g1(&mut ctx, Value::known(i.0)),
                                    x_cells: x_cells.clone(),
                                    y_cells: y_cells.clone(),
                                };
                                G1Assigned {
                                    decomposed,
                                    x_rlc: pairing_chip.fp_chip.range.gate.inner_product(
                                        &mut ctx,
                                        x_cells,
                                        keccak_powers.clone(),
                                    ),
                                    y_rlc: pairing_chip.fp_chip.range.gate.inner_product(
                                        &mut ctx,
                                        y_cells,
                                        keccak_powers.clone(),
                                    ),
                                }
                            })
                            .collect_vec();
                        let g2s = pairing_op
                            .inputs
                            .iter()
                            .map(|i| {
                                let [x_c0_cells, x_c1_cells, y_c0_cells, y_c1_cells] =
                                    self.decompose_g2(i.1);
                                let decomposed = G2Decomposed {
                                    ec_point: pairing_chip
                                        .load_private_g2(&mut ctx, Value::known(i.1)),
                                    x_c0_cells: x_c0_cells.clone(),
                                    x_c1_cells: x_c1_cells.clone(),
                                    y_c0_cells: y_c0_cells.clone(),
                                    y_c1_cells: y_c1_cells.clone(),
                                };
                                G2Assigned {
                                    decomposed,
                                    x_c0_rlc: pairing_chip.fp_chip.range.gate.inner_product(
                                        &mut ctx,
                                        x_c0_cells,
                                        keccak_powers.clone(),
                                    ),
                                    x_c1_rlc: pairing_chip.fp_chip.range.gate.inner_product(
                                        &mut ctx,
                                        x_c1_cells,
                                        keccak_powers.clone(),
                                    ),
                                    y_c0_rlc: pairing_chip.fp_chip.range.gate.inner_product(
                                        &mut ctx,
                                        y_c0_cells,
                                        keccak_powers.clone(),
                                    ),
                                    y_c1_rlc: pairing_chip.fp_chip.range.gate.inner_product(
                                        &mut ctx,
                                        y_c1_cells,
                                        keccak_powers.clone(),
                                    ),
                                }
                            })
                            .collect_vec();

                        // RLC over the entire input bytes.
                        let input_cells = g1s
                            .iter()
                            .map(|g1| g1.decomposed.x_cells.clone())
                            .chain(g1s.iter().map(|g1| g1.decomposed.y_cells.clone()))
                            .chain(g2s.iter().map(|g2| g2.decomposed.x_c0_cells.clone()))
                            .chain(g2s.iter().map(|g2| g2.decomposed.x_c1_cells.clone()))
                            .chain(g2s.iter().map(|g2| g2.decomposed.y_c0_cells.clone()))
                            .chain(g2s.iter().map(|g2| g2.decomposed.y_c1_cells.clone()))
                            .flatten()
                            .collect::<Vec<QuantumCell<F>>>();
                        let input_rlc = pairing_chip.fp_chip.range.gate.inner_product(
                            &mut ctx,
                            input_cells,
                            keccak_powers.clone(),
                        );

                        let gt = {
                            let gt = pairing_chip.multi_miller_loop(
                                &mut ctx,
                                g1s.iter()
                                    .map(|g1| &g1.decomposed.ec_point)
                                    .zip_eq(g2s.iter().map(|g2| &g2.decomposed.ec_point))
                                    .collect_vec(),
                            );
                            fp12_chip.final_exp(&mut ctx, &gt)
                        };
                        let one = fp12_chip.load_private(
                            &mut ctx,
                            Fp12Chip::<F, FpConfig<F, Fq>, Fq12, 9>::fe_to_witness(&Value::known(
                                Fq12::one(),
                            )),
                        );
                        // whether pairing check was successful.
                        let success = fp12_chip.is_equal(&mut ctx, &gt, &one);
                        EcPairingAssigned {
                            g1s,
                            g2s,
                            input_rlc,
                            success,
                        }
                    })
                    .collect_vec();

                Ok(EcOpsAssigned {
                    ec_adds_assigned,
                    ec_muls_assigned,
                    ec_pairings_assigned,
                })
            },
        )?;

        layouter.assign_region(
            || "expose ecc table",
            |mut region| {
                // handle EcAdd ops.
                for (idx, ec_add_assigned) in assigned_ec_ops.ec_adds_assigned.iter().enumerate() {
                    region.assign_fixed(
                        || "assign ecc_table op_type",
                        config.ecc_table.op_type,
                        idx,
                        || Value::known(F::from(u64::from(PrecompileCalls::Bn128Add))),
                    )?;
                    // P_x
                    ec_add_assigned.point_p.x_rlc.copy_advice(
                        &mut region,
                        config.ecc_table.arg1_rlc,
                        idx,
                    );
                    // P_y
                    ec_add_assigned.point_p.y_rlc.copy_advice(
                        &mut region,
                        config.ecc_table.arg2_rlc,
                        idx,
                    );
                    // Q_x
                    ec_add_assigned.point_q.x_rlc.copy_advice(
                        &mut region,
                        config.ecc_table.arg3_rlc,
                        idx,
                    );
                    // Q_y
                    ec_add_assigned.point_q.y_rlc.copy_advice(
                        &mut region,
                        config.ecc_table.arg4_rlc,
                        idx,
                    );
                    // R_x
                    ec_add_assigned.point_r.x_rlc.copy_advice(
                        &mut region,
                        config.ecc_table.output1_rlc,
                        idx,
                    );
                    // R_y
                    ec_add_assigned.point_r.y_rlc.copy_advice(
                        &mut region,
                        config.ecc_table.output2_rlc,
                        idx,
                    );
                }

                // handle EcMul ops.
                for (idx, ec_mul_assigned) in assigned_ec_ops.ec_muls_assigned.iter().enumerate() {
                    let idx = idx + self.max_add_ops;
                    region.assign_fixed(
                        || "assign ecc_table op_type",
                        config.ecc_table.op_type,
                        idx,
                        || Value::known(F::from(u64::from(PrecompileCalls::Bn128Mul))),
                    )?;
                    // P_x
                    ec_mul_assigned.point_p.x_rlc.copy_advice(
                        &mut region,
                        config.ecc_table.arg1_rlc,
                        idx,
                    );
                    // P_y
                    ec_mul_assigned.point_p.y_rlc.copy_advice(
                        &mut region,
                        config.ecc_table.arg2_rlc,
                        idx,
                    );
                    // s
                    ec_mul_assigned.scalar_s.rlc.copy_advice(
                        &mut region,
                        config.ecc_table.arg3_rlc,
                        idx,
                    );
                    // R_x
                    ec_mul_assigned.point_r.x_rlc.copy_advice(
                        &mut region,
                        config.ecc_table.output1_rlc,
                        idx,
                    );
                    // R_y
                    ec_mul_assigned.point_r.y_rlc.copy_advice(
                        &mut region,
                        config.ecc_table.output2_rlc,
                        idx,
                    );
                }

                // handle EcPairing ops.
                for (idx, ec_pairing_assigned) in
                    assigned_ec_ops.ec_pairings_assigned.iter().enumerate()
                {
                    let idx = idx + self.max_add_ops + self.max_mul_ops;
                    region.assign_fixed(
                        || "assign ecc_table op_type",
                        config.ecc_table.op_type,
                        idx,
                        || Value::known(F::from(u64::from(PrecompileCalls::Bn128Pairing))),
                    )?;
                    // RLC(input_bytes)
                    ec_pairing_assigned.input_rlc.copy_advice(
                        &mut region,
                        config.ecc_table.input_rlc,
                        idx,
                    );
                    // success
                    ec_pairing_assigned.success.copy_advice(
                        &mut region,
                        config.ecc_table.output1_rlc,
                        idx,
                    );
                }

                Ok(())
            },
        )?;

        Ok(())
    }

    fn assign_g1(
        &self,
        ctx: &mut Context<F>,
        fp_chip: &EccChip<F, FpConfig<F, Fq>>,
        g1: G1Affine,
        powers_of_rand: Vec<QuantumCell<F>>,
    ) -> G1Assigned<F> {
        let ec_point = fp_chip.load_private(ctx, (Value::known(g1.x), Value::known(g1.y)));
        let (x_cells, y_cells) = self.decompose_g1(g1);
        let decomposed = G1Decomposed {
            ec_point,
            x_cells: x_cells.clone(),
            y_cells: x_cells.clone(),
        };
        G1Assigned {
            decomposed,
            x_rlc: fp_chip.field_chip().range.gate.inner_product(
                ctx,
                x_cells,
                powers_of_rand.clone(),
            ),
            y_rlc: fp_chip
                .field_chip()
                .range
                .gate
                .inner_product(ctx, y_cells, powers_of_rand),
        }
    }

    fn decompose_g1(&self, g1: G1Affine) -> (Vec<QuantumCell<F>>, Vec<QuantumCell<F>>) {
        (
            g1.x.to_bytes()
                .iter()
                .map(|&x| QuantumCell::Witness(Value::known(F::from(u64::from(x)))))
                .collect_vec(),
            g1.y.to_bytes()
                .iter()
                .map(|&y| QuantumCell::Witness(Value::known(F::from(u64::from(y)))))
                .collect_vec(),
        )
    }

    fn decompose_g2(&self, g2: G2Affine) -> [Vec<QuantumCell<F>>; 4] {
        [
            g2.x.c0
                .to_bytes()
                .iter()
                .map(|&x| QuantumCell::Witness(Value::known(F::from(u64::from(x)))))
                .collect_vec(),
            g2.x.c1
                .to_bytes()
                .iter()
                .map(|&x| QuantumCell::Witness(Value::known(F::from(u64::from(x)))))
                .collect_vec(),
            g2.y.c0
                .to_bytes()
                .iter()
                .map(|&y| QuantumCell::Witness(Value::known(F::from(u64::from(y)))))
                .collect_vec(),
            g2.y.c1
                .to_bytes()
                .iter()
                .map(|&y| QuantumCell::Witness(Value::known(F::from(u64::from(y)))))
                .collect_vec(),
        ]
    }

    fn assign_fr(
        &self,
        ctx: &mut Context<F>,
        fr_chip: &FpConfig<F, Fr>,
        s: Fr,
        powers_of_rand: Vec<QuantumCell<F>>,
    ) -> ScalarAssigned<F> {
        let scalar = fr_chip.load_private(ctx, FpConfig::<F, Fr>::fe_to_witness(&Value::known(s)));
        let cells = s
            .to_bytes()
            .iter()
            .map(|&x| QuantumCell::Witness(Value::known(F::from(u64::from(x)))))
            .collect_vec();
        let decomposed = ScalarDecomposed {
            scalar,
            cells: cells.clone(),
        };
        ScalarAssigned {
            decomposed,
            rlc: fr_chip.range.gate.inner_product(ctx, cells, powers_of_rand),
        }
    }
}

impl<F: Field> SubCircuit<F> for EccCircuit<F> {
    type Config = EccCircuitConfig<F>;

    fn new_from_block(block: &Block<F>) -> Self {
        Self {
            max_add_ops: block.circuits_params.max_ec_ops.ec_add,
            max_mul_ops: block.circuits_params.max_ec_ops.ec_mul,
            max_pairing_ops: block.circuits_params.max_ec_ops.ec_pairing,
            add_ops: block.get_ec_add_ops(),
            mul_ops: block.get_ec_mul_ops(),
            pairing_ops: block.get_ec_pairing_ops(),
            _marker: PhantomData,
        }
    }

    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        config.fp_config.range.load_lookup_table(layouter)?;
        self.assign(layouter, config, challenges)?;
        Ok(())
    }

    fn min_num_rows_block(_block: &Block<F>) -> (usize, usize) {
        unimplemented!()
    }
}
