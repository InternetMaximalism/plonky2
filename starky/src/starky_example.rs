use core::marker::PhantomData;

use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;

use crate::stark::Stark;

#[derive(Copy, Clone)]
struct AddStark<F: RichField + Extendable<D>, const D: usize> {
    num_rows: usize,
    _phantom: PhantomData<F>,
}

// impl<F: RichField + Extendable<D>, const D: usize>

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for AddStark<F, D> {
    fn eval_packed_generic<FE, P, const D2: usize>(
        &self,
        vars: crate::vars::StarkEvaluationVars<FE, P>,
        yield_constr: &mut crate::constraint_consumer::ConstraintConsumer<P>,
    ) where
        FE: plonky2::field::extension::FieldExtension<D2, BaseField = F>,
        P: plonky2::field::packed::PackedField<Scalar = FE>,
    {
        todo!()
    }

    fn eval_ext_circuit(
        &self,
        builder: &mut plonky2::plonk::circuit_builder::CircuitBuilder<F, D>,
        vars: crate::vars::StarkEvaluationTargets<D>,
        yield_constr: &mut crate::constraint_consumer::RecursiveConstraintConsumer<F, D>,
    ) {
        todo!()
    }

    fn constraint_degree(&self) -> usize {
        todo!()
    }

    fn constants(&self) -> Vec<plonky2::field::polynomial::PolynomialValues<F>> {
        todo!()
    }
}
