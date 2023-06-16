use alloc::string::String;
use alloc::vec::Vec;
use alloc::{format, vec};
use core::marker::PhantomData;
use core::ops::Range;

use plonky2_field::extension::algebra::ExtensionAlgebra;
use plonky2_field::extension::{FieldExtension, OEF};

use super::keccak_theta::{xor, xor_ext_algebra};
use crate::field::extension::Extendable;
use crate::field::types::Field;
use crate::gates::gate::Gate;
use crate::gates::util::StridedConstraintConsumer;
use crate::hash::hash_types::RichField;
use crate::iop::ext_target::ExtensionTarget;
use crate::iop::generator::{GeneratedValues, SimpleGenerator, WitnessGeneratorRef};
use crate::iop::target::Target;
use crate::iop::witness::{PartitionWitness, Witness, WitnessWrite};
use crate::plonk::circuit_builder::CircuitBuilder;
use crate::plonk::vars::{EvaluationTargets, EvaluationVars, EvaluationVarsBase};
use crate::util::serialization::{Buffer, IoResult, Read, Write};

pub const WIDTH: usize = 5;
pub const STATE_SIZE: usize = WIDTH * WIDTH;

pub fn and_not<F: Field>(a: F, b: F) -> F {
    let not_b = F::ONE - b;

    a * not_b
}

fn xor_and_not<F: Field>(a: F, b: F, c: F) -> F {
    let b_and_not_c = and_not(b, c);

    xor(a, b_and_not_c)
}

fn xor_and_not_ext_algebra<F: OEF<D>, const D: usize>(
    a: ExtensionAlgebra<F, D>,
    b: ExtensionAlgebra<F, D>,
    c: ExtensionAlgebra<F, D>,
) -> ExtensionAlgebra<F, D> {
    let not_c = ExtensionAlgebra::one() - c;
    let b_and_not_c = b * not_c;

    xor_ext_algebra(a, b_and_not_c)
}

/// Keccak256 chi Gate
/// Calculate `a XOR (b AND (NOT c))`
#[derive(Debug, Default)]
pub struct XorAndNotGate<F: RichField + Extendable<D>, const D: usize>(PhantomData<F>);

impl<F: RichField + Extendable<D>, const D: usize> XorAndNotGate<F, D> {
    pub fn new() -> Self {
        Self(PhantomData)
    }

    pub fn wires_a() -> Range<usize> {
        0..D
    }

    pub fn wires_b() -> Range<usize> {
        D..2 * D
    }

    pub fn wires_c() -> Range<usize> {
        2 * D..3 * D
    }

    pub fn wires_output() -> Range<usize> {
        3 * D..4 * D
    }

    pub fn end() -> usize {
        4 * D
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Gate<F, D> for XorAndNotGate<F, D> {
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
        let a = vars.get_local_ext_algebra(Self::wires_a());
        let b = vars.get_local_ext_algebra(Self::wires_b());
        let c = vars.get_local_ext_algebra(Self::wires_c());
        let output = vars.get_local_ext_algebra(Self::wires_output());

        let a_xor_b_and_not_c = xor_and_not_ext_algebra(a, b, c);

        (a_xor_b_and_not_c - output).to_basefield_array().to_vec()
    }

    fn eval_unfiltered_base_one(
        &self,
        vars: EvaluationVarsBase<F>,
        mut yield_constr: StridedConstraintConsumer<F>,
    ) {
        let a = vars.get_local_ext(Self::wires_a());
        let b = vars.get_local_ext(Self::wires_b());
        let c = vars.get_local_ext(Self::wires_c());

        let output = vars.get_local_ext(Self::wires_output());

        let a_xor_b_and_not_c = xor_and_not(a, b, c);

        yield_constr.many((a_xor_b_and_not_c - output).to_basefield_array());
    }

    fn eval_unfiltered_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: EvaluationTargets<D>,
    ) -> Vec<ExtensionTarget<D>> {
        let a = vars.get_local_ext_algebra(Self::wires_a());
        let b = vars.get_local_ext_algebra(Self::wires_b());
        let c = vars.get_local_ext_algebra(Self::wires_c());
        let output = vars.get_local_ext_algebra(Self::wires_output());

        let a_xor_b_and_not_c = builder.xor_and_not_ext_algebra(a, b, c);

        builder
            .sub_ext_algebra(a_xor_b_and_not_c, output)
            .to_ext_target_array()
            .to_vec()
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<WitnessGeneratorRef<F>> {
        let gen = XorAndNotGenerator {
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

    fn degree(&self) -> usize {
        3
    }

    fn num_constraints(&self) -> usize {
        2
    }
}

#[derive(Clone, Debug, Default)]
pub struct XorAndNotGenerator<F: RichField + Extendable<D>, const D: usize> {
    row: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F> for XorAndNotGenerator<F, D> {
    fn id(&self) -> String {
        "XorAndNotGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        vec![
            Target::wires_from_range(self.row, XorAndNotGate::<F, D>::wires_a()),
            Target::wires_from_range(self.row, XorAndNotGate::<F, D>::wires_b()),
            Target::wires_from_range(self.row, XorAndNotGate::<F, D>::wires_c()),
        ]
        .concat()
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let get_local_get_target = |wire_range| ExtensionTarget::from_range(self.row, wire_range);
        let get_local_ext =
            |wire_range| witness.get_extension_target(get_local_get_target(wire_range));

        let a = get_local_ext(XorAndNotGate::<F, D>::wires_a());
        let b = get_local_ext(XorAndNotGate::<F, D>::wires_b());
        let c = get_local_ext(XorAndNotGate::<F, D>::wires_c());

        let computed_output = xor_and_not(a, b, c);

        out_buffer.set_extension_target(
            get_local_get_target(XorAndNotGate::<F, D>::wires_output()),
            computed_output,
        );
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
    use super::XorAndNotGate;
    use crate::gates::gate_testing::{test_eval_fns, test_low_degree};
    use crate::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    #[test]
    fn low_degree() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let gate = XorAndNotGate::<F, D>::new();
        test_low_degree(gate)
    }

    #[test]
    fn eval_fns() -> anyhow::Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let gate = XorAndNotGate::<F, D>::new();
        test_eval_fns::<F, C, _, D>(gate)
    }
}
