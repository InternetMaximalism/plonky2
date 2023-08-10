#![allow(clippy::needless_range_loop)]
#![cfg_attr(not(test), no_std)]

extern crate alloc;

pub mod curve;
pub mod gadgets;

#[cfg(test)]
mod tests {
    use plonky2::field::secp256k1_base::Secp256K1Base;
    use plonky2::field::types::Field;
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    use crate::gadgets::nonnative::CircuitBuilderNonNative;

    #[test]
    fn test_overflow() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let config = CircuitConfig::standard_ecc_config();

        let pw = PartialWitness::<F>::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let a = Secp256K1Base::from_canonical_u32(1);
        let b = Secp256K1Base::from_canonical_u32(2);

        let a_t = builder.constant_nonnative(a);
        let b_t = builder.constant_nonnative(b);
        let _c_t = builder.mul_nonnative(&a_t, &b_t);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof).unwrap();
    }

    #[test]
    fn test_add_to_zero() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let config = CircuitConfig::standard_ecc_config();

        let pw = PartialWitness::<F>::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let a = Secp256K1Base::ONE;
        let b = Secp256K1Base::NEG_ONE;

        let a_t = builder.constant_nonnative(a);
        let b_t = builder.constant_nonnative(b);
        let c_t = builder.add_nonnative(&a_t, &b_t);

        let zero_t = builder.constant_nonnative(Secp256K1Base::ZERO);

        builder.connect_nonnative(&c_t, &zero_t);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof).unwrap();
    }
}
