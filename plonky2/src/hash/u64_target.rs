use plonky2_field::types::Field;

use crate::field::extension::Extendable;
use crate::hash::hash_types::RichField;
use crate::iop::ext_target::{ExtensionAlgebraTarget, ExtensionTarget};
use crate::iop::target::BoolTarget;
use crate::iop::witness::Witness;
use crate::plonk::circuit_builder::CircuitBuilder;

#[derive(Clone, Debug)]
pub struct U64Target {
    pub bits: Vec<BoolTarget>,
}

impl U64Target {
    pub fn new<F: RichField + Extendable<D>, const D: usize>(
        builder: &mut CircuitBuilder<F, D>,
    ) -> Self {
        let mut result = vec![];
        for _ in 0..64 {
            result.push(builder.add_virtual_bool_target_safe());
        }
        Self { bits: result }
    }

    pub fn from<F: RichField + Extendable<D>, const D: usize>(bits: Vec<BoolTarget>) -> Self {
        assert_eq!(bits.len(), 64);
        Self { bits }
    }

    pub fn set_witness<F: Field>(&self, bits: Vec<bool>, pw: &mut impl Witness<F>) {
        for i in 0..64 {
            pw.set_bool_target(self.bits[i], bits[i]);
        }
    }

    pub fn constant<F: RichField + Extendable<D>, const D: usize>(
        x: u64,
        builder: &mut CircuitBuilder<F, D>,
    ) -> Self {
        let mut result = vec![];
        let x_bits = u64_to_bits(x);
        for i in 0..64 {
            result.push(builder.constant_bool(x_bits[i]));
        }
        Self { bits: result }
    }

    pub fn connect<F: RichField + Extendable<D>, const D: usize>(
        &self,
        other: &Self,
        builder: &mut CircuitBuilder<F, D>,
    ) {
        for i in 0..64 {
            builder.connect(self.bits[i].target, other.bits[i].target);
        }
    }

    pub fn to_bits<F: RichField + Extendable<D>, const D: usize>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
    ) -> Vec<BoolTarget> {
        let output = Self::new(builder);
        self.connect(&output, builder);
        output.bits
    }

    pub fn xor<F: RichField + Extendable<D>, const D: usize>(
        &self,
        other: &Self,
        builder: &mut CircuitBuilder<F, D>,
    ) -> Self {
        let mut result = vec![];
        for i in 0..64 {
            let xor_target = xor_circuit(self.bits[i], other.bits[i], builder);
            result.push(xor_target);
        }
        Self { bits: result }
    }

    pub fn xor_const<F: RichField + Extendable<D>, const D: usize>(
        &self,
        other: u64,
        builder: &mut CircuitBuilder<F, D>,
    ) -> Self {
        let other_bits = u64_to_bits(other);
        let mut result = vec![];
        for i in 0..64 {
            let xor_target = xor_const_circuit(self.bits[i], other_bits[i], builder);
            result.push(xor_target);
        }
        Self { bits: result }
    }

    /* Rotate left by n
     * Note that the input parameter n is constant. It is not necessary to make n a constant target or public input,
     * because different n generates a different circuit.
     */
    pub fn rotl<F: RichField + Extendable<D>, const D: usize>(&self, n: usize) -> Self {
        let rotate = rotate_u64(n);
        let mut output = vec![];
        for i in 0..64 {
            output.push(self.bits[rotate[i]]);
        }

        Self { bits: output }
    }

    pub fn and<F: RichField + Extendable<D>, const D: usize>(
        &self,
        other: &Self,
        builder: &mut CircuitBuilder<F, D>,
    ) -> Self {
        let mut result = vec![];
        for i in 0..64 {
            result.push(builder.and(self.bits[i], other.bits[i]));
        }
        Self { bits: result }
    }

    pub fn not<F: RichField + Extendable<D>, const D: usize>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
    ) -> Self {
        let mut result = vec![];
        for i in 0..64 {
            result.push(builder.not(self.bits[i]));
        }
        Self { bits: result }
    }

    /// Calculate `self & !other`.
    pub fn and_not<F: RichField + Extendable<D>, const D: usize>(
        &self,
        other: &Self,
        builder: &mut CircuitBuilder<F, D>,
    ) -> Self {
        let mut result = vec![];
        for i in 0..64 {
            // x(1 - y) = x - xy
            result.push(BoolTarget::new_unsafe(builder.arithmetic(
                F::NEG_ONE,
                F::ONE,
                self.bits[i].target,
                other.bits[i].target,
                self.bits[i].target,
            )));
        }
        Self { bits: result }
    }
}

pub fn xor_circuit<F, const D: usize>(
    a: BoolTarget,
    b: BoolTarget,
    builder: &mut CircuitBuilder<F, D>,
) -> BoolTarget
where
    F: RichField + Extendable<D>,
{
    // a = 0, b = 0 => 0
    // a = 1, b = 0 => 1
    // a = 0, b = 1 => 1
    // a = 1, b = 1 => 0
    // xor(a, b) = a*(1-b) + (1-a)*b = a + b - 2*ab
    let b_minus_2ab = builder.arithmetic(-F::TWO, F::ONE, a.target, b.target, b.target);
    let a_plus_b_minus_2ab = builder.add(a.target, b_minus_2ab);
    // let c = builder.add_virtual_bool_target_safe();
    // builder.connect(c.target, a_plus_b_neg_two_ab);

    BoolTarget::new_unsafe(a_plus_b_minus_2ab)
}

pub fn xor_const_circuit<F, const D: usize>(
    a: BoolTarget,
    b: bool,
    builder: &mut CircuitBuilder<F, D>,
) -> BoolTarget
where
    F: RichField + Extendable<D>,
{
    // b = 0 => xor(a, b) = a
    // b = 1 => xor(a, b) = 1 - a = not(a)
    if b {
        builder.not(a)
    } else {
        a
    }
}

// reffered to https://github.com/polymerdao/plonky2-sha256
/// 0 -> [0, 1, 2, ..., 63]
/// 1 -> [63, 0, 1, ..., 62]
/// 63 -> [1, 2, ..., 63, 0]
fn rotate_u64(y: usize) -> Vec<usize> {
    let mut res = Vec::new();
    for i in 64 - y..64 {
        res.push(i);
    }
    for i in 0..64 - y {
        res.push(i);
    }
    res
}

pub fn from_bits_to_u64(bools: &[bool]) -> u64 {
    let mut result: u64 = 0;
    let mut shift = 0;
    for &bit in bools {
        if bit {
            result |= 1 << shift;
        }
        shift += 1;
        if shift == 64 {
            break;
        }
    }
    result
}

pub fn u64_to_bits(num: u64) -> Vec<bool> {
    let mut result = Vec::with_capacity(64);
    let mut n = num;
    for _ in 0..64 {
        result.push(n & 1 == 1);
        n >>= 1;
    }
    result
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct U64Algebra<F: Field + Extendable<D>, const D: usize>(pub [F::Extension; 64]);

impl<F: Field + Extendable<D>, const D: usize> std::ops::Deref for U64Algebra<F, D> {
    type Target = [F::Extension; 64];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<F: Field + Extendable<D>, const D: usize> From<u64> for U64Algebra<F, D> {
    fn from(c: u64) -> Self {
        let c_bits = u64_to_bits(c);

        let mut result = vec![];
        for i in 0..64 {
            result.push(if c_bits[i] {
                F::Extension::ONE
            } else {
                F::Extension::ZERO
            });
        }

        Self(result.try_into().unwrap())
    }
}

#[derive(Copy, Clone, Debug)]
pub struct U64AlgebraTarget<const D: usize>(pub [ExtensionTarget<D>; 64]);

impl<const D: usize> std::ops::Deref for U64AlgebraTarget<D> {
    type Target = [ExtensionTarget<D>; 64];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const D: usize> std::ops::DerefMut for U64AlgebraTarget<D> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<const D: usize> From<[ExtensionTarget<D>; 64]> for U64AlgebraTarget<D> {
    fn from(c: [ExtensionTarget<D>; 64]) -> Self {
        Self(c)
    }
}

impl<const D: usize> U64AlgebraTarget<D> {
    pub fn set_witness<F: RichField + Extendable<D>>(
        &self,
        witness: U64Algebra<F, D>,
        pw: &mut impl Witness<F>,
    ) {
        for i in 0..64 {
            pw.set_extension_target(self[i], witness[i]);
        }
    }
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilder<F, D> {
    pub fn add_virtual_u64_algebra_target_unsafe(&mut self) -> U64AlgebraTarget<D> {
        U64AlgebraTarget([(); 64].map(|_| self.add_virtual_extension_target()))
    }

    pub fn add_virtual_u64_algebra_target_safe(&mut self) -> U64AlgebraTarget<D> {
        U64AlgebraTarget([(); 64].map(|_| {
            let bool_target = self.add_virtual_extension_target();
            let tmp = self.mul_sub_extension(bool_target, bool_target, bool_target);
            let zero_ext = self.zero_extension();
            self.connect_extension(tmp, zero_ext);

            bool_target
        }))
    }

    pub fn constant_u64_algebra(&mut self, c: U64Algebra<F, D>) -> U64AlgebraTarget<D> {
        U64AlgebraTarget(c.map(|x| self.constant_extension(x)))
    }

    pub fn connect_u64_algebra(&mut self, a: U64AlgebraTarget<D>, b: U64AlgebraTarget<D>) {
        for (a_bit, b_bit) in a.into_iter().zip(b.into_iter()) {
            self.connect_extension(a_bit, b_bit);
        }
    }

    pub fn xor_extension(
        &mut self,
        a: ExtensionTarget<D>,
        b: ExtensionTarget<D>,
    ) -> ExtensionTarget<D> {
        let b_minus_2ab = self.arithmetic_extension(-F::TWO, F::ONE, a, b, b);

        self.add_extension(a, b_minus_2ab)
    }

    pub fn xor_ext_algebra(
        &mut self,
        a: ExtensionAlgebraTarget<D>,
        b: ExtensionAlgebraTarget<D>,
    ) -> ExtensionAlgebraTarget<D> {
        let ab = self.mul_ext_algebra(a, b);
        let a_plus_b = self.add_ext_algebra(a, b);
        let neg_two = self.constant_extension(F::Extension::from(-F::TWO));

        self.scalar_mul_add_ext_algebra(neg_two, ab, a_plus_b)
    }

    pub fn xor_and_not_ext_algebra(
        &mut self,
        a: ExtensionAlgebraTarget<D>,
        b: ExtensionAlgebraTarget<D>,
        c: ExtensionAlgebraTarget<D>,
    ) -> ExtensionAlgebraTarget<D> {
        let one = self.constant_ext_algebra(F::Extension::ONE.into());
        let not_c = self.sub_ext_algebra(one, c);
        let b_and_not_c = self.mul_ext_algebra(b, not_c);

        self.xor_ext_algebra(a, b_and_not_c)
    }

    pub fn xor_u64_algebra(
        &mut self,
        a: U64AlgebraTarget<D>,
        b: U64AlgebraTarget<D>,
    ) -> U64AlgebraTarget<D> {
        let mut result = vec![];
        for (a_bit, b_bit) in a.into_iter().zip(b.into_iter()) {
            result.push(self.xor_extension(a_bit, b_bit));
        }

        U64AlgebraTarget(result.try_into().unwrap())
    }

    pub fn xor_const_extension(&mut self, a: ExtensionTarget<D>, b: bool) -> ExtensionTarget<D> {
        // b = 0 => xor(a, b) = a
        // b = 1 => xor(a, b) = 1 - a = not(a)
        if b {
            let one_ext = self.one_extension();

            self.sub_extension(one_ext, a)
        } else {
            a
        }
    }

    pub fn xor_const_u64_algebra(&mut self, a: U64AlgebraTarget<D>, b: u64) -> U64AlgebraTarget<D> {
        let b_bits = u64_to_bits(b);

        let mut result = vec![];
        for i in 0..64 {
            let xor_target = self.xor_const_extension(a[i], b_bits[i]);
            result.push(xor_target);
        }

        U64AlgebraTarget(result.try_into().unwrap())
    }

    pub fn and_not_u64_algebra(
        &mut self,
        lhs: U64AlgebraTarget<D>,
        rhs: U64AlgebraTarget<D>,
    ) -> U64AlgebraTarget<D> {
        let result = lhs
            .into_iter()
            .zip(rhs.into_iter())
            .map(|(l, r)| self.arithmetic_extension(F::NEG_ONE, F::ONE, l, r, l))
            .collect::<Vec<_>>();

        U64AlgebraTarget(result.try_into().unwrap())
    }
}

#[cfg(test)]
mod tests {
    use crate::field::goldilocks_field::GoldilocksField;
    use crate::iop::witness::PartialWitness;
    use crate::plonk::circuit_data::CircuitConfig;
    use crate::plonk::config::PoseidonGoldilocksConfig;

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    use super::*;

    #[test]
    fn test_xor_u64_algebra() -> anyhow::Result<()> {
        let a: u64 = 29;
        let b: u64 = 14;
        let expected_output = a ^ b;
        dbg!(a, b, expected_output);

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let a_t = builder.constant_u64_algebra(a.into());
        let b_t = builder.constant_u64_algebra(b.into());
        let a_xor_b_t = builder.xor_u64_algebra(a_t, b_t);
        let data = builder.build::<C>();

        let mut pw = PartialWitness::<F>::new();
        a_xor_b_t.set_witness(expected_output.into(), &mut pw);

        let proof = data.prove(pw)?;
        data.verify(proof)?;

        Ok(())
    }
}
