use alloc::string::String;
use alloc::vec::Vec;
use alloc::{format, vec};
use core::marker::PhantomData;
use core::ops::Range;

use super::keccak_chi::{xor_and_not, XorAndNotGate};
use super::keccak_theta::Xor5Gate;
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

pub const WIDTH: usize = 5;
pub const STATE_SIZE: usize = WIDTH * WIDTH;

fn xor<F: Field>(a: F, b: F) -> F {
    // a + b - 2ab
    let ab = a * b;

    a + b - ab.double()
}

pub fn calc_keccak_theta<F: Field>(inputs: [[F; 64]; STATE_SIZE]) -> [[F; 64]; WIDTH] {
    let mut outputs = vec![];
    for x in 0..5 {
        let mut output = vec![];
        for i in 0..64 {
            let xor01 = xor(inputs[x][i], inputs[x + 5][i]);
            let xor012 = xor(xor01, inputs[x + 2 * 5][i]);
            let xor0123 = xor(xor012, inputs[x + 3 * 5][i]);
            let xor01234 = xor(xor0123, inputs[x + 4 * 5][i]);
            output.push(xor01234);
        }
        outputs.push(output.try_into().unwrap());
    }

    outputs.try_into().unwrap()
}

pub fn calc_keccak_chi<F: Field>(inputs: [[F; 64]; STATE_SIZE]) -> [[F; 64]; STATE_SIZE] {
    let mut outputs = vec![];
    for y in 0..5 {
        for x in 0..5 {
            let mut output = vec![];
            for i in 0..64 {
                output.push(xor_and_not(
                    inputs[x + y * 5][i],
                    inputs[(x + 2) % 5 + y * 5][i],
                    inputs[(x + 1) % 5 + y * 5][i],
                ));
            }
            outputs.push(output.try_into().unwrap()); // outputs[x + y * 5]
        }
    }

    outputs.try_into().unwrap()
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

    pub fn wires_tmp(i: usize) -> Range<usize> {
        assert!(i < STATE_SIZE);

        ((i + STATE_SIZE) * 64)..((i + STATE_SIZE + 1) * 64)
    }

    pub fn wires_output(i: usize) -> Range<usize> {
        assert!(i < WIDTH);

        ((i + 2 * STATE_SIZE) * 64)..((i + 2 * STATE_SIZE + 1) * 64)
    }

    pub fn end() -> usize {
        (2 * STATE_SIZE + WIDTH) * 64
        // (2 * STATE_SIZE) * 64
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Gate<F, D> for Keccak256Gate<F, D> {
    fn id(&self) -> String {
        format!("{self:?}")
    }

    fn serialize(&self, _dst: &mut Vec<u8>) -> IoResult<()> {
        Ok(())
    }

    fn deserialize(_src: &mut Buffer) -> IoResult<Self> {
        Ok(Self::new())
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        let inputs = (0..STATE_SIZE)
            .map(|i| vars.local_wires[Self::wires_input(i)].to_vec())
            .collect::<Vec<_>>();

        let mut tmps = (0..STATE_SIZE)
            .map(|i| vars.local_wires[Self::wires_input(i)].to_vec())
            .collect::<Vec<_>>();

        let outputs = (0..WIDTH)
            .map(|i| vars.local_wires[Self::wires_output(i)].to_vec())
            .collect::<Vec<_>>();

        let mut constraints = vec![];

        for y in 0..5 {
            for x in 0..5 {
                for i in 0..64 {
                    let chi = xor_and_not(
                        inputs[x + y * 5][i],
                        inputs[(x + 2) % 5 + y * 5][i],
                        inputs[(x + 1) % 5 + y * 5][i],
                    );
                    constraints.push(tmps[x + y * 5][i] - chi);
                    tmps[x + y * 5][i] = chi
                }
            }
        }

        for x in 0..5 {
            for i in 0..64 {
                let xor01 = xor(tmps[x][i], tmps[x + 5][i]);
                let xor012 = xor(xor01, tmps[x + 2 * 5][i]);
                let xor0123 = xor(xor012, tmps[x + 3 * 5][i]);
                let xor01234 = xor(xor0123, tmps[x + 4 * 5][i]);
                constraints.push(outputs[x][i] - xor01234);
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

        let mut tmps = (0..STATE_SIZE)
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

        for y in 0..5 {
            for x in 0..5 {
                for i in 0..64 {
                    let chi = xor_and_not(
                        inputs[x + y * 5][i],
                        inputs[(x + 2) % 5 + y * 5][i],
                        inputs[(x + 1) % 5 + y * 5][i],
                    );
                    yield_constr.one(tmps[x + y * 5][i] - chi);
                    tmps[x + y * 5][i] = chi;
                }
            }
        }

        for x in 0..5 {
            for i in 0..64 {
                let xor01 = xor(tmps[x][i], tmps[x + 5][i]);
                let xor012 = xor(xor01, tmps[x + 2 * 5][i]);
                let xor0123 = xor(xor012, tmps[x + 3 * 5][i]);
                let xor01234 = xor(xor0123, tmps[x + 4 * 5][i]);
                yield_constr.one(outputs[x][i] - xor01234);
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
        let mut tmps: [U64AlgebraTarget<D>; STATE_SIZE] = (0..STATE_SIZE)
            .map(|i| {
                U64AlgebraTarget(
                    Self::wires_tmp(i)
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

        for y in 0..WIDTH {
            for x in 0..WIDTH {
                for (((a, b), c), o) in inputs[x + y * 5]
                    .into_iter()
                    .zip(inputs[(x + 2) % 5 + y * 5].into_iter())
                    .zip(inputs[(x + 1) % 5 + y * 5].into_iter())
                    .zip(tmps[x + y * 5].0.iter_mut())
                {
                    let gate_type = XorAndNotGate::<F, D>::new();
                    let gate = builder.add_gate(gate_type, vec![]);

                    // Route input wires.
                    let a_wire =
                        ExtensionTarget::from_range(gate, XorAndNotGate::<F, D>::wires_a());
                    builder.connect_extension(a_wire, a);
                    let b_wire =
                        ExtensionTarget::from_range(gate, XorAndNotGate::<F, D>::wires_b());
                    builder.connect_extension(b_wire, b);
                    let c_wire =
                        ExtensionTarget::from_range(gate, XorAndNotGate::<F, D>::wires_c());
                    builder.connect_extension(c_wire, c);

                    // Collect output wires.
                    let out_wire =
                        ExtensionTarget::from_range(gate, XorAndNotGate::<F, D>::wires_output());
                    // builder.connect_extension(out_wire, o);
                    constraints.push(builder.sub_extension(*o, out_wire));
                    *o = out_wire;
                }
            }
        }

        for x in 0..WIDTH {
            for (((((i0, i1), i2), i3), i4), o) in tmps[x]
                .into_iter()
                .zip(tmps[x + 5].into_iter())
                .zip(tmps[x + 2 * 5].into_iter())
                .zip(tmps[x + 3 * 5].into_iter())
                .zip(tmps[x + 4 * 5].into_iter())
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
                constraints.push(builder.sub_extension(o, out_wire));
            }
        }

        constraints
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<WitnessGeneratorRef<F>> {
        let gen = Keccak256Generator {
            row,
            _phantom: PhantomData,
        };
        vec![WitnessGeneratorRef::new(gen.adapter())]
    }

    fn num_wires(&self) -> usize {
        Self::end()
    }

    fn num_constants(&self) -> usize {
        0
    }

    // XXX
    fn degree(&self) -> usize {
        8
    }

    fn num_constraints(&self) -> usize {
        (STATE_SIZE + WIDTH) * 64
    }
}

#[derive(Clone, Debug, Default)]
pub struct Keccak256Generator<F: RichField + Extendable<D>, const D: usize> {
    row: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F> for Keccak256Generator<F, D> {
    fn id(&self) -> String {
        "Keccak256Generator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        (0..STATE_SIZE)
            .flat_map(|i| Target::wires_from_range(self.row, Keccak256Gate::<F, D>::wires_input(i)))
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

        let computed_tmps = calc_keccak_chi(inputs);

        for (i, computed_tmp) in computed_tmps.into_iter().enumerate() {
            let tmp = Keccak256Gate::<F, D>::wires_tmp(i)
                .map(local_wire)
                .collect::<Vec<_>>();
            out_buffer.set_wires(tmp, &computed_tmp);
        }

        let computed_outputs = calc_keccak_theta(computed_tmps);

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
