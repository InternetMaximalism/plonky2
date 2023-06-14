use alloc::string::String;
use alloc::vec::Vec;
use alloc::{format, vec};
use core::marker::PhantomData;
use core::ops::Range;

use crate::field::extension::Extendable;
use crate::field::types::Field;
use crate::gates::gate::Gate;
use crate::gates::util::StridedConstraintConsumer;
use crate::hash::hash_types::RichField;
use crate::hash::u64_target::U64AlgebraTarget;
use crate::iop::ext_target::ExtensionTarget;
use crate::iop::generator::{GeneratedValues, SimpleGenerator, WitnessGeneratorRef};
use crate::iop::target::Target;
use crate::iop::wire::Wire;
use crate::iop::witness::{PartitionWitness, Witness, WitnessWrite};
use crate::plonk::circuit_builder::CircuitBuilder;
use crate::plonk::vars::{EvaluationTargets, EvaluationVars, EvaluationVarsBase};
use crate::util::serialization::{Buffer, IoResult, Read, Write};

use super::keccak_theta::Xor5Gate;

pub const WIDTH: usize = 5;
pub const STATE_SIZE: usize = WIDTH * WIDTH;

fn xor<F: Field>(a: F, b: F) -> F {
    // a + b - 2ab
    let ab = a * b;

    a + b - ab.double()
}

/// Same as `mds_row_shf` for an extension algebra of `F`.
pub fn calc_keccak256_theta<F: Field>(input: &[[F; 64]; STATE_SIZE]) -> [[F; 64]; WIDTH] {
    let mut output = vec![];
    for x in 0..5 {
        let mut tmp = vec![];
        for i in 0..64 {
            let xor01 = xor(input[x][i], input[x + 5][i]);
            let xor012 = xor(xor01, input[x + 2 * 5][i]);
            let xor0123 = xor(xor012, input[x + 3 * 5][i]);
            let xor01234 = xor(xor0123, input[x + 4 * 5][i]);
            tmp.push(xor01234);
        }
        output.push(tmp.try_into().unwrap());
    }

    output.try_into().unwrap()
}

/// Keccak256 rho and pi Gate
/// 5 times xor
#[derive(Debug, Default)]
pub struct Keccak256Gate<F: RichField + Extendable<D>, const D: usize>(PhantomData<F>);

impl<F: RichField + Extendable<D>, const D: usize> Keccak256Gate<F, D> {
    pub fn new() -> Self {
        Self(PhantomData)
    }

    pub fn wires_input(i: usize) -> Range<usize> {
        assert!(i < STATE_SIZE);

        (i * 64)..((i + 1) * 64)
    }

    pub fn wires_output(i: usize) -> Range<usize> {
        assert!(i < WIDTH);

        ((i + STATE_SIZE) * 64)..((i + STATE_SIZE + 1) * 64)
    }

    // /// Same as `mds_row_shf_recursive` for an extension algebra of `F`.
    // fn calc_theta_circuit(
    //     builder: &mut CircuitBuilder<F, D>,
    //     input: &[U64ExtensionTarget<D>; WIDTH],
    // ) -> [U64ExtensionTarget<D>; WIDTH] {
    //     let mut output = vec![];
    //     for x in 0..5 {
    //         let xor01 = input[x].xor(&input[x + 5], builder);
    //         let xor012 = xor01.xor(&input[x + 2 * 5], builder);
    //         let xor0123 = xor012.xor(&input[x + 3 * 5], builder);
    //         let xor01234 = xor0123.xor(&input[x + 4 * 5], builder);
    //         output.push(xor01234); // bind, deg-3
    //     }

    //     output
    // }
}

impl<F: RichField + Extendable<D>, const D: usize> Gate<F, D> for Keccak256Gate<F, D> {
    fn id(&self) -> String {
        format!("{self:?}")
    }

    fn serialize(&self, _dst: &mut Vec<u8>) -> IoResult<()> {
        Ok(())
    }

    fn deserialize(_src: &mut Buffer) -> IoResult<Self> {
        Ok(Keccak256Gate::new())
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        let inputs = (0..STATE_SIZE)
            .map(|i| vars.local_wires[Self::wires_input(i)].to_vec())
            .collect::<Vec<_>>();

        let outputs = (0..WIDTH)
            .map(|i| vars.local_wires[Self::wires_output(i)].to_vec())
            .collect::<Vec<_>>();

        // let computed_outputs = calc_keccak256_theta(&inputs);

        let mut constraints = vec![];
        for x in 0..5 {
            for i in 0..64 {
                let xor01 = xor(inputs[x][i], inputs[x + 5][i]);
                let xor012 = xor(xor01, inputs[x + 2 * 5][i]);
                let xor0123 = xor(xor012, inputs[x + 3 * 5][i]);
                let xor01234 = xor(xor0123, inputs[x + 4 * 5][i]);
                constraints.push(xor01234 - outputs[x][i]);
            }
        }

        constraints
    }

    fn eval_unfiltered_base_one(
        &self,
        vars: EvaluationVarsBase<F>,
        mut yield_constr: StridedConstraintConsumer<F>,
    ) {
        let inputs = (0..STATE_SIZE)
            .map(|i| {
                Self::wires_input(i)
                    .map(|j| vars.local_wires[j])
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        let outputs = (0..WIDTH)
            .map(|i| {
                Self::wires_output(i)
                    .map(|j| vars.local_wires[j])
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        // let computed_outputs = calc_keccak256_theta(&inputs);

        for x in 0..5 {
            for i in 0..64 {
                let xor01 = xor(inputs[x][i], inputs[x + 5][i]);
                let xor012 = xor(xor01, inputs[x + 2 * 5][i]);
                let xor0123 = xor(xor012, inputs[x + 3 * 5][i]);
                let xor01234 = xor(xor0123, inputs[x + 4 * 5][i]);
                yield_constr.one(xor01234 - outputs[x][i]);
            }
        }
    }

    fn eval_unfiltered_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: EvaluationTargets<D>,
    ) -> Vec<ExtensionTarget<D>> {
        let inputs: [U64AlgebraTarget<D>; STATE_SIZE] = (0..STATE_SIZE)
            .map(|i| {
                U64AlgebraTarget(
                    Self::wires_input(i)
                        .map(|j| vars.local_wires[j])
                        .collect::<Vec<_>>()
                        .try_into()
                        .unwrap(),
                )
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let outputs: [U64AlgebraTarget<D>; WIDTH] = (0..WIDTH)
            .map(|i| {
                U64AlgebraTarget(
                    Self::wires_output(i)
                        .map(|j| vars.local_wires[j])
                        .collect::<Vec<_>>()
                        .try_into()
                        .unwrap(),
                )
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let mut constraints = vec![];
        for x in 0..WIDTH {
            // let xor01 = builder.xor_u64_algebra(inputs[x], inputs[x + 5]);
            // let xor012 = builder.xor_u64_algebra(xor01, inputs[x + 2 * 5]);

            // let xor34 = builder.xor_u64_algebra(inputs[x + 3 * 5], inputs[x + 4 * 5]);
            // let xor345 = builder.xor_u64_algebra(xor34, outputs[x]);

            // for (a, b) in xor012.into_iter().zip(xor345.into_iter()) {
            //     constraints.push(builder.sub_extension(a, b));
            // }

            for (((((i0, i1), i2), i3), i4), o) in inputs[x]
                .into_iter()
                .zip(inputs[x + 5].into_iter())
                .zip(inputs[x + 2 * 5].into_iter())
                .zip(inputs[x + 3 * 5].into_iter())
                .zip(inputs[x + 4 * 5].into_iter())
                .zip(outputs[x].into_iter())
            {
                // let xor01 = builder.xor_extension(i0, i1);
                // let xor012 = builder.xor_extension(xor01, i2);

                // let xor34 = builder.xor_extension(i3, i4);
                // let xor345 = builder.xor_extension(xor34, o);

                // constraints.push(builder.sub_extension(xor012, xor345));

                let gate_type = Xor5Gate::<F, D>::new();
                let gate = builder.add_gate(gate_type, vec![]);

                // Route input wires.
                let in_wire = ExtensionTarget::from_range(gate, Xor5Gate::<F, D>::wires_input(0));
                builder.connect_extension(in_wire, i0);
                let in_wire = ExtensionTarget::from_range(gate, Xor5Gate::<F, D>::wires_input(1));
                builder.connect_extension(in_wire, i1);
                let in_wire = ExtensionTarget::from_range(gate, Xor5Gate::<F, D>::wires_input(2));
                builder.connect_extension(in_wire, i2);
                let in_wire = ExtensionTarget::from_range(gate, Xor5Gate::<F, D>::wires_input(3));
                builder.connect_extension(in_wire, i3);
                let in_wire = ExtensionTarget::from_range(gate, Xor5Gate::<F, D>::wires_input(4));
                builder.connect_extension(in_wire, i4);

                // Collect output wires.
                let out_wire = ExtensionTarget::from_range(gate, Xor5Gate::<F, D>::wires_output());
                // builder.connect_extension(out_wire, o);
                constraints.push(builder.sub_extension(out_wire, o));
            }
        }

        constraints
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<WitnessGeneratorRef<F>> {
        let gen = Keccak256ThetaGenerator {
            row,
            _phantom: PhantomData,
        };
        vec![WitnessGeneratorRef::new(gen.adapter())]
    }

    fn num_wires(&self) -> usize {
        (WIDTH + STATE_SIZE) * 64
    }

    fn num_constants(&self) -> usize {
        0
    }

    fn degree(&self) -> usize {
        1
    }

    fn num_constraints(&self) -> usize {
        WIDTH * 64
    }
}

#[derive(Clone, Debug, Default)]
pub struct Keccak256ThetaGenerator<F: RichField + Extendable<D>, const D: usize> {
    row: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F>
    for Keccak256ThetaGenerator<F, D>
{
    fn id(&self) -> String {
        "Keccak256ThetaGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        (0..STATE_SIZE)
            .flat_map(|i| {
                Target::wires_from_range(self.row, Keccak256Gate::<F, D>::wires_input(i))
            })
            .collect()
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let local_wire = |column| Wire {
            row: self.row,
            column,
        };

        let inputs: [_; STATE_SIZE] = (0..STATE_SIZE)
            .map(|i| {
                Keccak256Gate::<F, D>::wires_input(i)
                    .map(|j| witness.get_wire(local_wire(j)))
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap()
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let computed_outputs = calc_keccak256_theta(&inputs);

        for (i, computed_out) in computed_outputs.into_iter().enumerate() {
            let out = Keccak256Gate::<F, D>::wires_output(i)
                .map(local_wire)
                .collect::<Vec<_>>();
            out_buffer.set_wires(out, &computed_out);
        }
    }

    fn serialize(&self, dst: &mut Vec<u8>) -> IoResult<()> {
        dst.write_usize(self.row)
    }

    fn deserialize(src: &mut Buffer) -> IoResult<Self> {
        let row = src.read_usize()?;
        Ok(Self {
            row,
            _phantom: PhantomData,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::Keccak256Gate;
    use crate::gates::gate_testing::{test_eval_fns, test_low_degree};
    use crate::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    #[test]
    fn low_degree() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let gate = Keccak256Gate::<F, D>::new();
        test_low_degree(gate)
    }

    #[test]
    fn eval_fns() -> anyhow::Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let gate = Keccak256Gate::<F, D>::new();
        test_eval_fns::<F, C, _, D>(gate)
    }
}
