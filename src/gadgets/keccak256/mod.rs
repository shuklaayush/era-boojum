use super::*;
use crate::config::*;
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::Variable;
use crate::gadgets::u8::UInt8;
use std::mem::MaybeUninit;

pub mod round_function;

pub const LANE_WIDTH: usize = 5;
pub const BYTES_PER_WORD: usize = 8;
pub const KECCAK256_NUM_ROUNDS: usize = 24;
pub const KECCAK_RATE_BYTES: usize = 136;

pub const ROTATION_CONSTANTS: [[u32; LANE_WIDTH]; LANE_WIDTH] = [
    [0, 28, 61, 23, 46],  // x = 0
    [63, 20, 54, 19, 62], // x = 1
    [2, 58, 21, 49, 3],   // x = 2
    [36, 9, 39, 43, 8],   // x = 3
    [37, 44, 25, 56, 50], // x = 4
];

pub const KECCAK256_DIGEST_SIZE: usize = 32;

pub const ROUND_CONSTANTS: [u64; KECCAK256_NUM_ROUNDS] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

pub fn keccak256<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: &[UInt8<F>],
) -> [UInt8<F>; KECCAK256_DIGEST_SIZE] {
    use crate::cs::gates::ConstantAllocatableCS;

    assert!(input.len() <= u32::MAX as usize);

    let zero = cs.allocate_constant(F::ZERO);
    let mut state = [[[zero; BYTES_PER_WORD]; LANE_WIDTH]; LANE_WIDTH];

    let mut padded_message = Vec::with_capacity(input.len() + KECCAK_RATE_BYTES);
    padded_message.extend(input.iter().map(|el| el.variable));

    let block_size = KECCAK_RATE_BYTES;
    let last_block_size = input.len() % block_size;
    let padlen = block_size - last_block_size;
    if padlen == 1 {
        padded_message.push(cs.allocate_constant(F::from_u64_unchecked(0x81 as u64)));
    } else {
        padded_message.push(cs.allocate_constant(F::from_u64_unchecked(0x01 as u64)));
        padded_message.extend(std::iter::repeat(zero).take(padlen - 2));
        padded_message.push(cs.allocate_constant(F::from_u64_unchecked(0x80 as u64)));
    }

    assert_eq!(padded_message.len() % block_size, 0);

    use self::round_function::*;

    for block in padded_message.array_chunks::<KECCAK_RATE_BYTES>() {
        // absorb into state
        for i in 0..LANE_WIDTH {
            for j in 0..LANE_WIDTH {
                if i + LANE_WIDTH * j < (KECCAK_RATE_BYTES / BYTES_PER_WORD) {
                    let tmp = block
                        .array_chunks::<BYTES_PER_WORD>()
                        .skip(i + LANE_WIDTH * j)
                        .next()
                        .unwrap();
                    use crate::gadgets::blake2s::mixing_function::xor_many;
                    state[i][j] = xor_many(cs, &state[i][j], tmp);
                }
            }
        }
        keccak_256_round_function(cs, &mut state);
    }

    // copy back
    let mut result = [MaybeUninit::<UInt8<F>>::uninit(); KECCAK256_DIGEST_SIZE];
    for (i, dst) in result.array_chunks_mut::<8>().enumerate() {
        for (dst, src) in dst.iter_mut().zip(state[i][0].iter()) {
            let tmp = unsafe { UInt8::from_variable_unchecked(*src) };
            dst.write(tmp);
        }
    }

    unsafe { result.map(|el| el.assume_init()) }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        cs::{
            gates::{
                ConstantsAllocatorGate, FmaGateInBaseFieldWithoutConstant, NopGate, ReductionGate,
            },
            CSGeometry,
        },
        field::goldilocks::GoldilocksField,
        gadgets::tables::{
            and8::{create_and8_table, And8Table},
            byte_split::{create_byte_split_table, ByteSplitTable},
            xor8::{create_xor8_table, Xor8Table},
        },
    };
    use sha3::Digest;
    type F = GoldilocksField;
    use crate::cs::traits::gate::GatePlacementStrategy;
    use crate::gadgets::traits::witnessable::WitnessHookable;

    #[test]
    fn test_single_round() {
        test_keccak256(42);
    }
    #[test]
    fn test_single_round_exact() {
        test_keccak256(135);
    }
    #[test]
    fn test_two_rounds() {
        test_keccak256(136 + 42);
    }
    #[test]
    fn test_two_rounds_exact() {
        test_keccak256(136 + 135);
    }
    #[test]
    fn test_many_rounds() {
        test_keccak256(10 * 135 + 42);
    }
    #[test]
    fn test_many_rounds_exact() {
        test_keccak256(10 * 135 + 135);
    }

    fn test_keccak256(len: usize) {
        use rand::{Rng, SeedableRng};
        let mut rng = rand::rngs::StdRng::seed_from_u64(42 as u64);

        let mut input = vec![];
        for _ in 0..len {
            let byte: u8 = rng.gen();
            input.push(byte);
        }

        let mut hasher = sha3::Keccak256::new();
        hasher.update(&input);
        let reference_output = hasher.finalize();

        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 20,
            num_witness_columns: 0,
            num_constant_columns: 4,
            max_allowed_constraint_degree: 4,
        };

        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(geometry, 1 << 20, 1 << 18);
        use crate::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = builder.allow_lookup(
            crate::cs::LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                width: 3,
                num_repetitions: 5,
                share_table_id: true,
            },
        );

        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ReductionGate::<F, 4>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = builder.build(());

        // add tables
        let table = create_xor8_table();
        owned_cs.add_lookup_table::<Xor8Table, 3>(table);

        let table = create_and8_table();
        owned_cs.add_lookup_table::<And8Table, 3>(table);

        let table = create_byte_split_table::<F, 1>();
        owned_cs.add_lookup_table::<ByteSplitTable<1>, 3>(table);
        let table = create_byte_split_table::<F, 2>();
        owned_cs.add_lookup_table::<ByteSplitTable<2>, 3>(table);
        let table = create_byte_split_table::<F, 3>();
        owned_cs.add_lookup_table::<ByteSplitTable<3>, 3>(table);
        let table = create_byte_split_table::<F, 4>();
        owned_cs.add_lookup_table::<ByteSplitTable<4>, 3>(table);

        let mut circuit_input = vec![];

        let cs = &mut owned_cs;

        let mut it = input.array_chunks::<2>();
        for pair in &mut it {
            let pair = UInt8::allocate_pair(cs, *pair);
            circuit_input.extend(pair);
        }

        for el in it.remainder() {
            let el = UInt8::allocate_checked(cs, *el);
            circuit_input.push(el);
        }

        let output = keccak256(cs, &circuit_input);
        let output = hex::encode(&(output.witness_hook(&*cs))().unwrap());
        let reference_output = hex::encode(reference_output.as_slice());
        assert_eq!(output, reference_output);

        drop(cs);
        owned_cs.pad_and_shrink();
        let mut owned_cs = owned_cs.into_assembly();
        owned_cs.wait_for_witness();
        use crate::worker::Worker;
        let worker = Worker::new_with_num_threads(8);
        assert!(owned_cs.check_if_satisfied(&worker));
    }

    // Notes on benches:
    // - we ignore equality asserts because we are lazy, but those are negligible contribution compared to keccak256 itself
    // - we use random input (not zeroes), because constant propagation would not help much anyway, and it's more realistic case
    // - allocation (8-bit constraints on bytes) are included in the proof, but why not?
    // - PoW is turned off, because 2^20 bits for blake2s PoW is 30 ms anyway, negligible

    use crate::{
        cs::{
            implementations::{
                pow::NoPow,
                transcript::{Blake2sTranscript, Transcript},
            },
            oracle::TreeHasher,
        },
        log,
    };

    #[test]
    #[ignore]
    fn run_keccak256_prover_non_recursive() {
        use crate::blake2::Blake2s256;
        type TreeHash = Blake2s256;
        type Transcript = Blake2sTranscript;
        prove_keccak256::<TreeHash, Transcript>(8 * (1 << 10));
    }

    #[test]
    #[ignore]
    fn run_keccak256_prover_recursive_mode() {
        use crate::algebraic_props::round_function::AbsorptionModeOverwrite;
        use crate::algebraic_props::sponge::GoldilocksPoseidonSponge;
        use crate::cs::implementations::transcript::GoldilocksPoisedonTranscript;

        type TreeHash = GoldilocksPoseidonSponge<AbsorptionModeOverwrite>;
        type Transcript = GoldilocksPoisedonTranscript;
        prove_keccak256::<TreeHash, Transcript>(8 * (1 << 10));
    }

    #[test]
    #[ignore]
    fn run_keccak256_prover_recursive_mode_poseidon2() {
        use crate::algebraic_props::round_function::AbsorptionModeOverwrite;
        use crate::algebraic_props::sponge::GoldilocksPoseidon2Sponge;
        use crate::cs::implementations::transcript::GoldilocksPoisedonTranscript;

        type TreeHash = GoldilocksPoseidon2Sponge<AbsorptionModeOverwrite>;
        type Transcript = GoldilocksPoisedonTranscript;
        prove_keccak256::<TreeHash, Transcript>(8 * (1 << 10));
    }

    fn prove_keccak256<
        T: TreeHasher<GoldilocksField, Output = TR::CompatibleCap>,
        TR: Transcript<GoldilocksField, TransciptParameters = ()>,
    >(
        len: usize,
    ) {
        use crate::cs::implementations::prover::ProofConfig;
        use crate::field::goldilocks::GoldilocksExt2;
        use crate::worker::Worker;

        let worker = Worker::new_with_num_threads(8);

        let quotient_lde_degree = 8; // Setup params are not split yet, so it's should be equal to max(FRI lde degree, quotient degree)
        let fri_lde_degree = 8;
        let cap_size = 16;
        let mut prover_config = ProofConfig::default();
        prover_config.fri_lde_factor = fri_lde_degree;
        prover_config.pow_bits = 0; // not important in practice for anything. 2^20 Blake2s POW uses 30ms

        use rand::{Rng, SeedableRng};
        let mut rng = rand::rngs::StdRng::seed_from_u64(42 as u64);

        let mut input = vec![];
        for _ in 0..len {
            let byte: u8 = rng.gen();
            input.push(byte);
        }

        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 60,
            num_witness_columns: 0,
            num_constant_columns: 4,
            max_allowed_constraint_degree: 4,
        };

        let max_variables = 1 << 25;
        let max_trace_len = 1 << 19;

        use crate::cs::cs_builder::*;
        use crate::cs::GateConfigurationHolder;
        use crate::cs::StaticToolboxHolder;

        fn configure<
            T: CsBuilderImpl<F, T>,
            GC: GateConfigurationHolder<F>,
            TB: StaticToolboxHolder,
        >(
            builder: CsBuilder<T, F, GC, TB>,
        ) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
            let num_lookups = 8;
            let builder = builder.allow_lookup(
                crate::cs::LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                    width: 3,
                    num_repetitions: num_lookups,
                    share_table_id: true,
                },
            );
            let builder = ConstantsAllocatorGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = ReductionGate::<F, 4>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = NopGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );

            builder
        }

        {
            // satisfiability check
            let builder_impl = CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(
                geometry,
                max_variables,
                max_trace_len,
            );
            let builder = new_builder::<_, F>(builder_impl);

            let builder = configure(builder);
            let mut owned_cs = builder.build(());

            // add tables
            let table = create_xor8_table();
            owned_cs.add_lookup_table::<Xor8Table, 3>(table);

            let table = create_and8_table();
            owned_cs.add_lookup_table::<And8Table, 3>(table);

            let table = create_byte_split_table::<F, 1>();
            owned_cs.add_lookup_table::<ByteSplitTable<1>, 3>(table);
            let table = create_byte_split_table::<F, 2>();
            owned_cs.add_lookup_table::<ByteSplitTable<2>, 3>(table);
            let table = create_byte_split_table::<F, 3>();
            owned_cs.add_lookup_table::<ByteSplitTable<3>, 3>(table);
            let table = create_byte_split_table::<F, 4>();
            owned_cs.add_lookup_table::<ByteSplitTable<4>, 3>(table);

            let mut circuit_input = vec![];

            let cs = &mut owned_cs;

            let mut it = input.array_chunks::<2>();
            for pair in &mut it {
                let pair = UInt8::allocate_pair(cs, *pair);
                circuit_input.extend(pair);
            }

            for el in it.remainder() {
                let el = UInt8::allocate_checked(cs, *el);
                circuit_input.push(el);
            }

            let _output = keccak256(cs, &circuit_input);
            drop(cs);
            owned_cs.pad_and_shrink();
            let mut owned_cs = owned_cs.into_assembly();
            assert!(owned_cs.check_if_satisfied(&worker));
        }

        use crate::cs::cs_builder_reference::*;
        use crate::cs::cs_builder_verifier::*;

        let builder_impl = CsReferenceImplementationBuilder::<F, F, SetupCSConfig>::new(
            geometry,
            max_variables,
            max_trace_len,
        );
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let mut owned_cs = builder.build(());

        // add tables
        let table = create_xor8_table();
        owned_cs.add_lookup_table::<Xor8Table, 3>(table);

        let table = create_and8_table();
        owned_cs.add_lookup_table::<And8Table, 3>(table);

        let table = create_byte_split_table::<F, 1>();
        owned_cs.add_lookup_table::<ByteSplitTable<1>, 3>(table);

        let table = create_byte_split_table::<F, 2>();
        owned_cs.add_lookup_table::<ByteSplitTable<2>, 3>(table);

        let table = create_byte_split_table::<F, 3>();
        owned_cs.add_lookup_table::<ByteSplitTable<3>, 3>(table);

        let table = create_byte_split_table::<F, 4>();
        owned_cs.add_lookup_table::<ByteSplitTable<4>, 3>(table);

        let mut circuit_input = vec![];

        let cs = &mut owned_cs;

        let mut it = input.array_chunks::<2>();
        for pair in &mut it {
            let pair = UInt8::allocate_pair(cs, *pair);
            circuit_input.extend(pair);
        }

        for el in it.remainder() {
            let el = UInt8::allocate_checked(cs, *el);
            circuit_input.push(el);
        }

        let _output = keccak256(cs, &circuit_input);
        drop(cs);
        let (_, padding_hint) = owned_cs.pad_and_shrink();
        let owned_cs = owned_cs.into_assembly();
        owned_cs.print_gate_stats();

        let (base_setup, setup, vk, setup_tree, vars_hint, wits_hint) =
            owned_cs.get_full_setup::<T>(&worker, quotient_lde_degree, cap_size);

        let builder_impl = CsReferenceImplementationBuilder::<F, F, ProvingCSConfig>::new(
            geometry,
            max_variables,
            max_trace_len,
        );
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let mut owned_cs = builder.build(());

        // add tables
        let table = create_xor8_table();
        owned_cs.add_lookup_table::<Xor8Table, 3>(table);

        let table = create_and8_table();
        owned_cs.add_lookup_table::<And8Table, 3>(table);

        let table = create_byte_split_table::<F, 1>();
        owned_cs.add_lookup_table::<ByteSplitTable<1>, 3>(table);

        let table = create_byte_split_table::<F, 2>();
        owned_cs.add_lookup_table::<ByteSplitTable<2>, 3>(table);

        let table = create_byte_split_table::<F, 3>();
        owned_cs.add_lookup_table::<ByteSplitTable<3>, 3>(table);

        let table = create_byte_split_table::<F, 4>();
        owned_cs.add_lookup_table::<ByteSplitTable<4>, 3>(table);

        // create setup
        let now = std::time::Instant::now();
        log!("Start synthesis for proving");
        let mut circuit_input = vec![];

        let cs = &mut owned_cs;

        let mut it = input.array_chunks::<2>();
        for pair in &mut it {
            let pair = UInt8::allocate_pair(cs, *pair);
            circuit_input.extend(pair);
        }

        for el in it.remainder() {
            let el = UInt8::allocate_checked(cs, *el);
            circuit_input.push(el);
        }

        let _output = keccak256(cs, &circuit_input);
        dbg!(now.elapsed());
        log!("Synthesis for proving is done");
        owned_cs.pad_and_shrink_using_hint(&padding_hint);
        let mut owned_cs = owned_cs.into_assembly();

        log!("Proving");
        let witness_set = owned_cs.take_witness_using_hints(&worker, &vars_hint, &wits_hint);
        log!("Witness is resolved");

        let now = std::time::Instant::now();

        let proof = owned_cs.prove_cpu_basic::<GoldilocksExt2, TR, T, NoPow>(
            &worker,
            witness_set,
            &base_setup,
            &setup,
            &setup_tree,
            &vk,
            prover_config,
            (),
        );

        log!("Proving is done, taken {:?}", now.elapsed());

        let builder_impl = CsVerifierBuilder::<F, GoldilocksExt2>::new_from_parameters(geometry);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let verifier = builder.build(());

        let is_valid = verifier.verify::<T, TR, NoPow>((), &vk, &proof);

        assert!(is_valid);
    }
}
