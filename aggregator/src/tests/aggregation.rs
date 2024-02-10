use std::{fs, path::Path, process};

use ark_std::{end_timer, start_timer, test_rng};
use ethers_core::k256::elliptic_curve::CurveArithmetic;
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr, poly::commitment::Params};
use itertools::Itertools;
use snark_verifier::loader::halo2::halo2_ecc::halo2_base::halo2_proofs;
use snark_verifier::loader::halo2::halo2_ecc::halo2_base::utils::fs::gen_srs;
use snark_verifier::loader::halo2::halo2_ecc::halo2_base::halo2_proofs::{
    plonk::{create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ProvingKey, VerifyingKey},
    poly::{
        commitment::{ParamsProver},
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            strategy::AccumulatorStrategy,
            multiopen::{ProverSHPLONK, VerifierSHPLONK},
        },
        VerificationStrategy,
    },
    transcript::{EncodedChallenge, TranscriptReadBuffer, TranscriptWriterBuffer},
};
use snark_verifier::loader::halo2::halo2_ecc::halo2_base::halo2_proofs::halo2curves::bn256::{Bn256, Fq, G1Affine};
use snark_verifier_sdk::{
    gen_pk,
     gen_snark_shplonk, verify_snark_shplonk, CircuitExt,
     gen_proof
    };
use rand::rngs::OsRng;

use crate::{
    aggregation::AggregationCircuit as AggregationCircuitZkEVM, batch::BatchHash, constants::MAX_AGG_SNARKS, layer_0,
    tests::mock_chunk::MockChunkCircuit, ChunkHash,
};

use std::{io::Cursor, rc::Rc};

use snark_verifier::{
    loader::{
        evm::{
            encode_calldata, EvmLoader, ExecutorBuilder, {self},
        },
        native::NativeLoader,
    },
    pcs::kzg::{Bdfg21, Kzg, KzgAs, LimbsEncoding},
    system::halo2::{compile, transcript::evm::EvmTranscript, Config},
    verifier::{
        PlonkVerifier, {self},
    },
};

const LIMBS: usize = 3;
const BITS: usize = 88;

type Pcs = Kzg<Bn256, Bdfg21>;
type As = KzgAs<Pcs>;
type Plonk = verifier::Plonk<Pcs, LimbsEncoding<LIMBS, BITS>>;

mod aggregation_zkevm {
    use super::{
        halo2_proofs::{
            circuit::{Cell, Layouter, SimpleFloorPlanner, Value},
            plonk::{
                Circuit, Column, ConstraintSystem, Instance, {self},
            },
            poly::{commitment::ParamsProver, kzg::commitment::ParamsKZG},
        },
        As, Bn256, Fq, Fr, G1Affine, Plonk, BITS, LIMBS,
    };
    use ark_std::{end_timer, start_timer};
    use snark_verifier::loader::halo2::halo2_ecc::halo2_base::{Context, ContextParams};
    use snark_verifier::loader::halo2::halo2_ecc::halo2_base as halo2_base;
    use snark_verifier::loader::halo2::halo2_ecc::ecc::EccChip;
    use snark_verifier::loader::halo2::halo2_ecc as halo2_ecc;
    use itertools::Itertools;
    use rand::rngs::OsRng;
    use snark_verifier::{
        loader::{
            native::NativeLoader,
            {self},
        },
        pcs::{
            kzg::{KzgAccumulator, KzgSuccinctVerifyingKey},
            AccumulationScheme, AccumulationSchemeProver,
        },
        system,
        util::arithmetic::fe_to_limbs,
        verifier::PlonkVerifier,
        Protocol,
    };
    use std::{fs::File, rc::Rc};

    const T: usize = 5;
    const RATE: usize = 4;
    const R_F: usize = 8;
    const R_P: usize = 60;

    type Svk = KzgSuccinctVerifyingKey<G1Affine>;
    type BaseFieldEccChip = halo2_ecc::ecc::BaseFieldEccChip<G1Affine>;
    type Halo2Loader<'a> = loader::halo2::Halo2Loader<'a, G1Affine, BaseFieldEccChip>;
    pub type PoseidonTranscript<L, S> =
        system::halo2::transcript::halo2::PoseidonTranscript<G1Affine, L, S, T, RATE, R_F, R_P>;

    pub struct Snark {
        protocol: Protocol<G1Affine>,
        instances: Vec<Vec<Fr>>,
        proof: Vec<u8>,
    }

    impl Snark {
        pub fn new(protocol: Protocol<G1Affine>, instances: Vec<Vec<Fr>>, proof: Vec<u8>) -> Self {
            Self { protocol, instances, proof }
        }
    }

    impl From<Snark> for SnarkWitness {
        fn from(snark: Snark) -> Self {
            Self {
                protocol: snark.protocol,
                instances: snark
                    .instances
                    .into_iter()
                    .map(|instances| instances.into_iter().map(Value::known).collect_vec())
                    .collect(),
                proof: Value::known(snark.proof),
            }
        }
    }

    #[derive(Clone)]
    pub struct SnarkWitness {
        protocol: Protocol<G1Affine>,
        instances: Vec<Vec<Value<Fr>>>,
        proof: Value<Vec<u8>>,
    }

    impl SnarkWitness {
        fn without_witnesses(&self) -> Self {
            SnarkWitness {
                protocol: self.protocol.clone(),
                instances: self
                    .instances
                    .iter()
                    .map(|instances| vec![Value::unknown(); instances.len()])
                    .collect(),
                proof: Value::unknown(),
            }
        }

        fn proof(&self) -> Value<&[u8]> {
            self.proof.as_ref().map(Vec::as_slice)
        }
    }

    pub fn aggregate<'a>(
        svk: &Svk,
        loader: &Rc<Halo2Loader<'a>>,
        snarks: &[SnarkWitness],
        as_proof: Value<&'_ [u8]>,
    ) -> KzgAccumulator<G1Affine, Rc<Halo2Loader<'a>>> {
        let assign_instances = |instances: &[Vec<Value<Fr>>]| {
            instances
                .iter()
                .map(|instances| {
                    instances.iter().map(|instance| loader.assign_scalar(*instance)).collect_vec()
                })
                .collect_vec()
        };

        let accumulators = snarks
            .iter()
            .flat_map(|snark| {
                let protocol = snark.protocol.loaded(loader);
                let instances = assign_instances(&snark.instances);
                let mut transcript =
                    PoseidonTranscript::<Rc<Halo2Loader>, _>::new(loader, snark.proof());
                let proof = Plonk::read_proof(svk, &protocol, &instances, &mut transcript);
                Plonk::succinct_verify(svk, &protocol, &instances, &proof)
            })
            .collect_vec();

        let acccumulator = {
            let mut transcript = PoseidonTranscript::<Rc<Halo2Loader>, _>::new(loader, as_proof);
            let proof =
                As::read_proof(&Default::default(), &accumulators, &mut transcript).unwrap();
            As::verify(&Default::default(), &accumulators, &proof).unwrap()
        };

        acccumulator
    }

    #[derive(serde::Serialize, serde::Deserialize)]
    pub struct AggregationConfigParams {
        pub strategy: halo2_ecc::fields::fp::FpStrategy,
        pub degree: u32,
        pub num_advice: usize,
        pub num_lookup_advice: usize,
        pub num_fixed: usize,
        pub lookup_bits: usize,
        pub limb_bits: usize,
        pub num_limbs: usize,
    }

    #[derive(Clone)]
    pub struct AggregationConfig {
        pub base_field_config: halo2_ecc::fields::fp::FpConfig<Fr, Fq>,
        pub instance: Column<Instance>,
    }

    impl AggregationConfig {
        pub fn configure(meta: &mut ConstraintSystem<Fr>, params: AggregationConfigParams) -> Self {
            assert!(
                params.limb_bits == BITS && params.num_limbs == LIMBS,
                "For now we fix limb_bits = {}, otherwise change code",
                BITS
            );
            let base_field_config = halo2_ecc::fields::fp::FpConfig::configure(
                meta,
                params.strategy,
                &[params.num_advice],
                &[params.num_lookup_advice],
                params.num_fixed,
                params.lookup_bits,
                params.limb_bits,
                params.num_limbs,
                halo2_base::utils::modulus::<Fq>(),
                0,
                params.degree as usize,
            );

            let instance = meta.instance_column();
            meta.enable_equality(instance);

            Self { base_field_config, instance }
        }

        pub fn range(&self) -> &halo2_base::gates::range::RangeConfig<Fr> {
            &self.base_field_config.range
        }

        pub fn ecc_chip(&self) -> halo2_ecc::ecc::BaseFieldEccChip<G1Affine> {
            EccChip::construct(self.base_field_config.clone())
        }
    }

    #[derive(Clone)]
    pub struct AggregationCircuit {
        svk: Svk,
        snarks: Vec<SnarkWitness>,
        instances: Vec<Fr>,
        as_proof: Value<Vec<u8>>,
    }

    impl AggregationCircuit {
        pub fn new(params: &ParamsKZG<Bn256>, snarks: impl IntoIterator<Item = Snark>) -> Self {
            let svk = params.get_g()[0].into();
            let snarks = snarks.into_iter().collect_vec();

            let accumulators = snarks
                .iter()
                .flat_map(|snark| {
                    let mut transcript =
                        PoseidonTranscript::<NativeLoader, _>::new(snark.proof.as_slice());
                    let proof =
                        Plonk::read_proof(&svk, &snark.protocol, &snark.instances, &mut transcript);
                    Plonk::succinct_verify(&svk, &snark.protocol, &snark.instances, &proof)
                })
                .collect_vec();

            let (accumulator, as_proof) = {
                let mut transcript = PoseidonTranscript::<NativeLoader, _>::new(Vec::new());
                let accumulator =
                    As::create_proof(&Default::default(), &accumulators, &mut transcript, OsRng)
                        .unwrap();
                (accumulator, transcript.finalize())
            };
            let KzgAccumulator { lhs, rhs } = accumulator;
            let instances =
                [lhs.x, lhs.y, rhs.x, rhs.y].map(fe_to_limbs::<_, _, LIMBS, BITS>).concat();

            Self {
                svk,
                snarks: snarks.into_iter().map_into().collect(),
                instances,
                as_proof: Value::known(as_proof),
            }
        }

        pub fn as_proof(&self) -> Value<&[u8]> {
            self.as_proof.as_ref().map(Vec::as_slice)
        }

        pub fn num_instance() -> Vec<usize> {
            // [..lhs, ..rhs]
            vec![4 * LIMBS]
        }

        pub fn instances(&self) -> Vec<Vec<Fr>> {
            vec![self.instances.clone()]
        }

        pub fn accumulator_indices() -> Vec<(usize, usize)> {
            (0..4 * LIMBS).map(|idx| (0, idx)).collect()
        }
    }

    impl Circuit<Fr> for AggregationCircuit {
        type Config = AggregationConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self {
                svk: self.svk,
                snarks: self.snarks.iter().map(SnarkWitness::without_witnesses).collect(),
                instances: Vec::new(),
                as_proof: Value::unknown(),
            }
        }

        fn configure(meta: &mut plonk::ConstraintSystem<Fr>) -> Self::Config {
            let path = std::env::var("VERIFY_CONFIG").unwrap();
            let params: AggregationConfigParams = AggregationConfigParams{
                // {"strategy":"Simple","degree":21,"num_advice":5,"num_lookup_advice":1,"num_fixed":1,"lookup_bits":20,"limb_bits":88,"num_limbs":3}

                strategy: halo2_ecc::fields::fp::FpStrategy::Simple,
                degree: 21,
                num_advice: 5,
                num_lookup_advice: 1,
                num_fixed: 1,
                lookup_bits: 20,
                limb_bits: 88,
                num_limbs: 3,
            };
            // serde_json::from_reader(
            //     File::open(path.as_str())
            //         .unwrap_or_else(|err| panic!("Path {path} does not exist: {err:?}")),
            // )
            // .unwrap();

            AggregationConfig::configure(meta, params)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), plonk::Error> {
            config.range().load_lookup_table(&mut layouter)?;
            let max_rows = config.range().gate.max_rows;

            let mut first_pass = halo2_base::SKIP_FIRST_PASS; // assume using simple floor planner
            let mut assigned_instances: Option<Vec<Cell>> = None;
            layouter.assign_region(
                || "",
                |region| {
                    if first_pass {
                        first_pass = false;
                        return Ok(());
                    }
                    let witness_time = start_timer!(|| "Witness Collection");
                    let ctx = Context::new(
                        region,
                        ContextParams {
                            max_rows,
                            num_context_ids: 1,
                            fixed_columns: config.base_field_config.range.gate.constants.clone(),
                        },
                    );

                    let ecc_chip = config.ecc_chip();
                    let loader = Halo2Loader::new(ecc_chip, ctx);
                    let KzgAccumulator { lhs, rhs } =
                        aggregate(&self.svk, &loader, &self.snarks, self.as_proof());

                    let lhs = lhs.assigned();
                    let rhs = rhs.assigned();

                    config.base_field_config.finalize(&mut loader.ctx_mut());
                    #[cfg(feature = "display")]
                    println!("Total advice cells: {}", loader.ctx().total_advice);
                    #[cfg(feature = "display")]
                    println!("Advice columns used: {}", loader.ctx().advice_alloc[0].0 + 1);

                    let instances: Vec<_> = lhs
                        .x
                        .truncation
                        .limbs
                        .iter()
                        .chain(lhs.y.truncation.limbs.iter())
                        .chain(rhs.x.truncation.limbs.iter())
                        .chain(rhs.y.truncation.limbs.iter())
                        .map(|assigned| assigned.cell().clone())
                        .collect();
                    assigned_instances = Some(instances);
                    end_timer!(witness_time);
                    Ok(())
                },
            )?;

            // Expose instances
            // TODO: use less instances by following Scroll's strategy of keeping only last bit of y coordinate
            let mut layouter = layouter.namespace(|| "expose");
            for (i, cell) in assigned_instances.unwrap().into_iter().enumerate() {
                layouter.constrain_instance(cell, config.instance, i)?;
            }
            Ok(())
        }
    }
}

fn gen_pk_local<C: Circuit<Fr>>(params: &ParamsKZG<Bn256>, circuit: &C) -> ProvingKey<G1Affine> {
    let vk = keygen_vk(params, circuit).unwrap();
    keygen_pk(params, vk, circuit).unwrap()
}

fn gen_proof_local<
    C: Circuit<Fr>,
    E: EncodedChallenge<G1Affine>,
    TR: TranscriptReadBuffer<Cursor<Vec<u8>>, G1Affine, E>,
    TW: TranscriptWriterBuffer<Vec<u8>, G1Affine, E>,
>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
) -> Vec<u8> {
    MockProver::run(params.k(), &circuit, instances.clone()).unwrap().assert_satisfied_par();

    let instances = instances.iter().map(|instances| instances.as_slice()).collect_vec();
    let proof = {
        let mut transcript = TW::init(Vec::new());
        create_proof::<KZGCommitmentScheme<Bn256>, ProverSHPLONK<_>, _, _, TW, _>(
            params,
            pk,
            &[circuit],
            &[instances.as_slice()],
            OsRng,
            &mut transcript,
        )
        .unwrap();
        transcript.finalize()
    };

    let accept = {
        let mut transcript = TR::init(Cursor::new(proof.clone()));
        VerificationStrategy::<_, VerifierSHPLONK<_>>::finalize(
            verify_proof::<_, VerifierSHPLONK<_>, _, TR, _>(
                params.verifier_params(),
                pk.get_vk(),
                AccumulatorStrategy::new(params.verifier_params()),
                &[instances.as_slice()],
                &mut transcript,
            )
            .unwrap(),
        )
    };
    assert!(accept);

    proof
}

#[test]
fn test_aggregation_circuit() {
    env_logger::init();

    let k = 20;

    // This set up requires one round of keccak for chunk's data hash
    let circuit = build_new_aggregation_circuit(1);
    println!("Instances len {:?}", circuit.instances().len()); 

    let params = snark_verifier::loader::halo2::halo2_ecc::halo2_base::utils::fs::gen_srs(21);
    // let params_app = {
    //     let mut params = params.clone();
    //     // params.downsize(14);
    //     params
    // };

    let pk = gen_pk_local(&params, &circuit);
    println!("Generated PK for aggregation circuit");

    let protocol = compile(
        &params,
        pk.get_vk(),
        Config::kzg().with_num_instance(vec![circuit.instances().len()]),
    );

    println!("Circuit protocol {:?}", protocol);
    println!("Circuit instances {:?}", circuit.instances());

    // let proof_agg_zkevm = gen_proof_local::<
    //     _,
    //     _,
    //     aggregation_zkevm::PoseidonTranscript<NativeLoader, _>,
    //     aggregation_zkevm::PoseidonTranscript<NativeLoader, _>,
    // >(&params, &pk, circuit.clone(), circuit.instances());

    // println!("Generated proof for aggregation circuit");
    // println!("Proof size: {}", proof_agg_zkevm.len());
    
    
    // let snarks = vec![aggregation_zkevm::Snark::new(protocol, circuit.instances(), proof_agg_zkevm)];

    let val1 = protocol.num_instance;
    let val2 = circuit.instances().iter().map(|instances| instances.len()).collect_vec();

    println!("Protocol instances {:?}", val1);
    println!("Circuit instances {:?}", val2);

    debug_assert_eq!(
        val1,
        val2,
        "Invalid Instances"
    );

    // let agg_circuit = aggregation_zkevm::AggregationCircuit::new(&params, snarks);
    // let pk = gen_pk_local(&params, &agg_circuit);
    // println!("Generated PK for aggregation circuit");

    // let proof_final = gen_proof_local::<_, _, EvmTranscript<G1Affine, _, _, _>, EvmTranscript<G1Affine, _, _, _>>(
    //     &params,
    //     &pk,
    //     agg_circuit.clone(),
    //     agg_circuit.instances(),
    // );

    // println!("Generated proof for BAC circuit");
    // println!("Proof size: {}", proof_final.len());

    // let mock_prover = MockProver::<Fr>::run(k, &circuit, instance).unwrap();
    // mock_prover.assert_satisfied_par();
}


pub fn build_new_aggregation_circuit(num_real_chunks: usize) -> AggregationCircuitZkEVM {
    // inner circuit: Mock circuit
    let k0 = 8;

    let mut rng = test_rng();
    let params = gen_srs(k0);
    dbg!("Generated SRS for aggregation circuit innner");

    let mut chunks_without_padding = (0..num_real_chunks)
        .map(|_| ChunkHash::mock_random_chunk_hash_for_testing(&mut rng))
        .collect_vec();
    for i in 0..num_real_chunks - 1 {
        chunks_without_padding[i + 1].prev_state_root = chunks_without_padding[i].post_state_root;
    }
    let padded_chunk =
        ChunkHash::mock_padded_chunk_hash_for_testing(&chunks_without_padding[num_real_chunks - 1]);
    let chunks_with_padding = [
        chunks_without_padding,
        vec![padded_chunk; MAX_AGG_SNARKS - num_real_chunks],
    ]
    .concat();

    // ==========================
    // real chunks
    // ==========================
    dbg!("Start generating snarks");
    let real_snarks = {
        let circuits = chunks_with_padding
            .iter()
            .take(num_real_chunks)
            .map(|&chunk| MockChunkCircuit::new(true, chunk))
            .collect_vec();
        circuits
            .iter()
            .map(|&circuit| layer_0!(circuit, MockChunkCircuit, params, k0, path))
            .collect_vec()
    };

    // ==========================
    // padded chunks
    // ==========================
    let padded_snarks =
        { vec![real_snarks.last().unwrap().clone(); MAX_AGG_SNARKS - num_real_chunks] };

    // ==========================
    // batch
    // ==========================
    let batch_hash = BatchHash::construct(&chunks_with_padding);

    dbg!("Inner aggregation circuit generation completed returning it");

    AggregationCircuitZkEVM::new(
        &params,
        [real_snarks, padded_snarks].concat().as_ref(),
        rng,
        batch_hash,
    )
    .unwrap()
}
