use anyhow::Result;
use plonky2::field::types::Field;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

fn main() -> Result<()> {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    // The arithmetic circuit.
    let var0 = builder.add_virtual_target();
    let var1 = builder.add_virtual_target();
    let target = builder.add(var0, var1);

    // Public inputs are the initial value (provided below) and the result (which is generated).
    // builder.register_public_input(target);

    let mut pw = PartialWitness::new();
    pw.set_target(var0, F::ONE);
    pw.set_target(var1, F::ONE);
    pw.set_target(target, F::TWO);

    let data = builder.build::<C>();
    let proof = data.prove(pw)?;

    // println!(
    //     "Factorial starting at {} is {}",
    //     proof.public_inputs[0], proof.public_inputs[1]
    // );

    data.verify(proof)
}
