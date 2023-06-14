use alloc::vec::Vec;

use crate::field::extension::Extendable;
use crate::gates::keccak256::{Keccak256Gate, STATE_SIZE, WIDTH};
use crate::gates::keccak_theta::Xor5Gate;
use crate::hash::hash_types::{HashOutTarget, RichField};
use crate::hash::u64_target::U64Target;
use crate::iop::ext_target::ExtensionTarget;
use crate::iop::target::{BoolTarget, Target};
use crate::plonk::circuit_builder::CircuitBuilder;
use crate::plonk::config::AlgebraicHasher;

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilder<F, D> {
    pub fn permute<H: AlgebraicHasher<F>>(
        &mut self,
        inputs: H::AlgebraicPermutation,
    ) -> H::AlgebraicPermutation {
        // We don't want to swap any inputs, so set that wire to 0.
        let _false = self._false();
        self.permute_swapped::<H>(inputs, _false)
    }

    /// Conditionally swap two chunks of the inputs (useful in verifying Merkle proofs), then apply
    /// a cryptographic permutation.
    pub(crate) fn permute_swapped<H: AlgebraicHasher<F>>(
        &mut self,
        inputs: H::AlgebraicPermutation,
        swap: BoolTarget,
    ) -> H::AlgebraicPermutation {
        H::permute_swapped(inputs, swap, self)
    }

    pub fn public_inputs_hash<H: AlgebraicHasher<F>>(
        &mut self,
        inputs: Vec<Target>,
    ) -> HashOutTarget {
        H::public_inputs_hash(inputs, self)
    }
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilder<F, D> {
    pub fn xor5(&mut self, inputs: [BoolTarget; WIDTH]) -> BoolTarget {
        let gate_type = Xor5Gate::<F, D>::new();
        let gate = self.add_gate(gate_type, vec![]);

        let zero = self.zero();

        // Route input wires.
        // let inputs = inputs.as_ref();
        for i in 0..WIDTH {
            let in_wire = ExtensionTarget::from_range(gate, Xor5Gate::<F, D>::wires_input(i));
            self.connect_extension(in_wire, inputs[i].target.to_ext_target(zero));
        }

        // Collect output wires.
        let out_wire = ExtensionTarget::from_range(gate, Xor5Gate::<F, D>::wires_output());

        let output = self.add_virtual_bool_target_safe();

        self.connect_extension(out_wire, output.target.to_ext_target(zero));

        output
    }

    pub fn keccak256(&mut self, inputs: [U64Target; STATE_SIZE]) -> [U64Target; WIDTH] {
        let gate_type = Keccak256Gate::<F, D>::new();
        let gate = self.add_gate(gate_type, vec![]);

        // Route input wires.
        // let inputs = inputs.as_ref();
        for i in 0..STATE_SIZE {
            let in_wire = U64Target {
                bits: Keccak256Gate::<F, D>::wires_input(i)
                    .map(|v| BoolTarget::new_unsafe(Target::wire(gate, v)))
                    .collect::<Vec<_>>(),
            };
            inputs[i].connect(&in_wire, self);
        }

        // Collect output wires.
        (0..5).map(|i| {
            U64Target {
                bits: Keccak256Gate::<F, D>::wires_output(i)
                    .map(|v| BoolTarget::new_unsafe(Target::wire(gate, v)))
                    .collect::<Vec<_>>(),
            }
        }).collect::<Vec<_>>().try_into().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use crate::{
        field::goldilocks_field::GoldilocksField,
        plonk::{circuit_data::CircuitConfig, circuit_builder::CircuitBuilder, config::PoseidonGoldilocksConfig},
        iop::witness::{PartialWitness, WitnessWrite},
        gates::keccak256::{STATE_SIZE},
        hash::u64_target::U64Target,
    };

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    fn test_keccak_circuit_builder() {
        let config = CircuitConfig::standard_keccak_config();
        // let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        
        let targets = (0..1).map(|_| {
            // let inputs = [(); WIDTH].map(|_| builder.add_virtual_bool_target_safe());
            // let outputs = builder.xor5(inputs);
            let inputs = [(); STATE_SIZE].map(|_| U64Target::new(&mut builder));
            let outputs = builder.keccak256(inputs.clone());

            (inputs, outputs)
        }).collect::<Vec<_>>();
        dbg!(builder.num_gates());
        let keccak_circuit_data = builder.build::<C>();

        let mut pw = PartialWitness::new();
        for (inputs, _outputs) in targets {
            // for i in 0..WIDTH {
            //     pw.set_bool_target(inputs[i], rand::random());
            // }
            for i in 0..STATE_SIZE {
                let bits: [bool; 64] = [(); 64].map(|_| rand::random());
                inputs[i].set_witness(bits.to_vec(), &mut pw);
            }
        }

        let now = Instant::now();
        let proof_with_pis = keccak_circuit_data.prove(pw).unwrap();

        println!("time = {} ms", now.elapsed().as_millis());
        println!(
            "degree = {}, degree_bits= {}",
            keccak_circuit_data.common.degree(),
            keccak_circuit_data.common.degree_bits()
        );

        keccak_circuit_data.verify(proof_with_pis.clone()).unwrap();

        let inner_circuit_data = keccak_circuit_data;
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let proof_with_pis_t = builder.add_virtual_proof_with_pis(&inner_circuit_data.common);
        let vd_target = builder.constant_verifier_data(&inner_circuit_data.verifier_only);
        // let vd_target = builder.add_virtual_verifier_data(inner_circuit_data.common.config.fri_config.cap_height);
        builder.verify_proof::<C>(&proof_with_pis_t, &vd_target, &inner_circuit_data.common);
        dbg!(builder.num_gates());
        let first_recursion_circuit_data = builder.build::<C>();

        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target::<C, D>(&proof_with_pis_t, &proof_with_pis);
        // pw.set_verifier_data_target(&vd_target, &inner_circuit_data.verifier_only);

        let now = Instant::now();
        let proof_with_pis = first_recursion_circuit_data.prove(pw).unwrap();

        println!("time = {} ms", now.elapsed().as_millis());
        println!(
            "degree = {}, degree_bits= {}",
            first_recursion_circuit_data.common.degree(),
            first_recursion_circuit_data.common.degree_bits()
        );

        let inner_circuit_data = first_recursion_circuit_data;
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let proof_with_pis_t = builder.add_virtual_proof_with_pis(&inner_circuit_data.common);
        let vd_target = builder.constant_verifier_data(&inner_circuit_data.verifier_only);
        // let vd_target = builder.add_virtual_verifier_data(inner_circuit_data.common.config.fri_config.cap_height);
        builder.verify_proof::<C>(&proof_with_pis_t, &vd_target, &inner_circuit_data.common);
        dbg!(builder.num_gates());
        let second_recursion_circuit_data = builder.build::<C>();

        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target::<C, D>(&proof_with_pis_t, &proof_with_pis);

        let now = Instant::now();
        let _proof_with_pis = second_recursion_circuit_data.prove(pw).unwrap();

        println!("time = {} ms", now.elapsed().as_millis());
        println!(
            "degree = {}, degree_bits= {}",
            second_recursion_circuit_data.common.degree(),
            second_recursion_circuit_data.common.degree_bits()
        );
    }
}