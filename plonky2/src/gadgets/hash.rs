use alloc::vec::Vec;

use crate::field::extension::Extendable;
use crate::gates::keccak256::{Keccak256RoundGate, ROUND_CONSTANTS, STATE_SIZE, WIDTH};
use crate::gates::keccak_chi::XorAndNotGate;
use crate::gates::keccak_theta::Xor5Gate;
use crate::hash::hash_types::{HashOutTarget, RichField};
use crate::hash::u64_target::{xor_circuit, U64Target};
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
    pub fn keccak_theta(&mut self, inputs: [BoolTarget; WIDTH]) -> BoolTarget {
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

    pub fn keccak_chi(&mut self, a: BoolTarget, b: BoolTarget, c: BoolTarget) -> BoolTarget {
        let gate_type = XorAndNotGate::<F, D>::new();
        let gate = self.add_gate(gate_type, vec![]);

        let zero = self.zero();

        // Route input wires.
        let in_wire = ExtensionTarget::from_range(gate, XorAndNotGate::<F, D>::wires_a());
        self.connect_extension(in_wire, a.target.to_ext_target(zero));
        let in_wire = ExtensionTarget::from_range(gate, XorAndNotGate::<F, D>::wires_b());
        self.connect_extension(in_wire, b.target.to_ext_target(zero));
        let in_wire = ExtensionTarget::from_range(gate, XorAndNotGate::<F, D>::wires_c());
        self.connect_extension(in_wire, c.target.to_ext_target(zero));

        // Collect output wires.
        let out_wire = ExtensionTarget::from_range(gate, XorAndNotGate::<F, D>::wires_output());

        let output = self.add_virtual_bool_target_safe();

        self.connect_extension(out_wire, output.target.to_ext_target(zero));

        output
    }

    pub fn keccak256_round(&mut self, inputs: [U64Target; STATE_SIZE]) -> [U64Target; STATE_SIZE] {
        let gate_type = Keccak256RoundGate::<F, D>::new();
        let gate = self.add_gate(gate_type, vec![]);

        // Route input wires.
        for i in 0..STATE_SIZE {
            let in_wire = U64Target {
                bits: Keccak256RoundGate::<F, D>::wires_input(i)
                    .map(|v| {
                        let t = BoolTarget::new_unsafe(Target::wire(gate, v));
                        self.assert_bool(t);

                        t
                    })
                    .collect::<Vec<_>>(),
            };
            inputs[i].connect(&in_wire, self);
        }

        // Collect output wires.
        (0..STATE_SIZE)
            .map(|i| U64Target {
                bits: Keccak256RoundGate::<F, D>::wires_output(i)
                    .map(|v| {
                        let t = BoolTarget::new_unsafe(Target::wire(gate, v));
                        self.assert_bool(t);

                        t
                    })
                    .collect::<Vec<_>>(),
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    pub fn keccak_f(&mut self, inputs: [U64Target; STATE_SIZE]) -> [U64Target; STATE_SIZE] {
        let mut state = inputs;
        for rc in ROUND_CONSTANTS.into_iter().take(24) {
            state = self.keccak256_round(state);
            state[0] = state[0].xor_const(rc, self);
        }

        state
    }

    pub fn keccak256(&mut self, input: Vec<BoolTarget>) -> Vec<BoolTarget>
    where
        F: RichField + Extendable<D>,
    {
        assert_eq!(input.len() % 8, 0); // input should be bytes.
        let block_size_in_bytes = 136; // in bytes
        let input_len_in_bytes = input.len() / 8;
        let num_blocks = input_len_in_bytes / block_size_in_bytes + 1;
        dbg!(num_blocks);

        let mut padded = vec![];
        for _ in 0..block_size_in_bytes * 8 * num_blocks {
            padded.push(self.add_virtual_bool_target_safe());
        }

        // register input
        for i in 0..input_len_in_bytes * 8 {
            self.connect(padded[i].target, input[i].target);
        }

        // append 0x01 = 1000 0000 after the last input
        let true_target = self.constant_bool(true);
        self.connect(padded[input_len_in_bytes * 8].target, true_target.target);

        // pad 0s
        let false_target = self.constant_bool(false);
        let last_index = padded.len() - 1;
        for i in input_len_in_bytes * 8 + 1..last_index {
            self.connect(padded[i].target, false_target.target);
        }

        // xor 0x80 = 0000 0001 with the last byte.
        // however the last bit is ensured to be 0, so just fill 1.
        self.connect(padded[last_index].target, true_target.target);

        let mut m = [(); 25].map(|_| U64Target::new(self));
        for i in 0..1600 {
            let word = i / 64;
            let bit = i % 64;
            self.connect(m[word].bits[bit].target, false_target.target);
        }

        for i in 0..num_blocks {
            for j in 0..block_size_in_bytes * 8 {
                let word = j / 64;
                let bit = j % 64;
                let xor_t = xor_circuit(
                    m[word].bits[bit],
                    padded[i * block_size_in_bytes * 8 + j],
                    self,
                );
                m[word].bits[bit] = xor_t;
            }
            m = self.keccak_f(m);
        }

        let mut z = Vec::new();
        for i in 0..256 {
            let new_target = self.add_virtual_bool_target_safe();
            let word = i / 64;
            let bit = i % 64;
            self.connect(new_target.target, m[word].bits[bit].target);
            z.push(new_target);
        }

        z
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use crate::field::goldilocks_field::GoldilocksField;
    use crate::iop::witness::{PartialWitness, WitnessWrite};
    use crate::plonk::circuit_builder::CircuitBuilder;
    use crate::plonk::circuit_data::CircuitConfig;
    use crate::plonk::config::PoseidonGoldilocksConfig;

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    fn test_keccak_chi_builder() {
        let config = CircuitConfig::standard_keccak_config();
        // let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let targets = (0..1)
            .map(|_| {
                // let inputs = [(); WIDTH].map(|_| builder.add_virtual_bool_target_safe());
                // let outputs = builder.keccak_theta(inputs);
                let a = builder.add_virtual_bool_target_safe();
                let b = builder.add_virtual_bool_target_safe();
                let c = builder.add_virtual_bool_target_safe();
                let outputs = builder.keccak_chi(a, b, c);

                (a, b, c, outputs)
            })
            .collect::<Vec<_>>();
        dbg!(builder.num_gates());
        let keccak_circuit_data = builder.build::<C>();

        let mut pw = PartialWitness::new();
        for (a, b, c, _outputs) in targets {
            // for i in 0..WIDTH {
            //     pw.set_bool_target(inputs[i], rand::random());
            // }

            pw.set_bool_target(a, rand::random());
            pw.set_bool_target(b, rand::random());
            pw.set_bool_target(c, rand::random());
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

    fn u8_to_bits(num: u8) -> Vec<bool> {
        let mut result = Vec::with_capacity(8);
        let mut n = num;
        for _ in 0..8 {
            result.push(n & 1 == 1);
            n >>= 1;
        }
        result
    }

    fn hex_str_to_bits(input: &str) -> anyhow::Result<Vec<bool>> {
        let input_u8 = hex::decode(input)?;
        let input_bits = input_u8
            .iter()
            .flat_map(|x| u8_to_bits(*x))
            .collect::<Vec<_>>();
        Ok(input_bits)
    }

    #[test]
    fn test_keccak_circuit_builder() {
        let input = "8f54f1c2d0eb5771cd5bf67a6689fcd6eed9444d91a39e5ef32a9b4ae5ca14ff8f54f1c2d0eb5771cd5bf67a6689fcd6eed9444d91a39e5ef32a9b4ae5ca14ff";
        let output = "c38d4cf2aeb3e65177c5d58e2afed87a17116190182829e59d3f8f8d801469c1";

        let config = CircuitConfig::standard_keccak_config();
        // let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let input_bits = hex_str_to_bits(input).unwrap();
        let output_bits = hex_str_to_bits(output).unwrap();
        let targets = (0..1)
            .map(|_| {
                let mut inputs_t = vec![];
                for b in input_bits.iter() {
                    inputs_t.push(builder.constant_bool(*b));
                }
                let outputs_t = builder.keccak256(inputs_t.clone());

                (inputs_t, outputs_t)
            })
            .collect::<Vec<_>>();
        dbg!(builder.num_gates());
        let keccak_circuit_data = builder.build::<C>();

        let mut pw = PartialWitness::new();
        for (_inputs_t, outputs_t) in targets {
            for i in 0..256 {
                pw.set_bool_target(outputs_t[i], output_bits[i]);
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
