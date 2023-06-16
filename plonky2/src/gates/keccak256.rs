use alloc::string::String;
use alloc::vec::Vec;
use alloc::{format, vec};
use core::marker::PhantomData;
use core::ops::Range;

use super::keccak_chi::and_not;
use super::keccak_theta::{xor, Xor5Gate};
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
use crate::plonk::plonk_common::{reduce_with_powers, reduce_with_powers_ext_circuit};
use crate::plonk::vars::{EvaluationTargets, EvaluationVars, EvaluationVarsBase};
use crate::util::serialization::{Buffer, IoResult, Read, Write};

pub const WIDTH: usize = 5;
pub const STATE_SIZE: usize = WIDTH * WIDTH;
pub const ROUND_CONSTANTS: [u64; 24] = [
    1u64,
    0x8082u64,
    0x800000000000808au64,
    0x8000000080008000u64,
    0x808bu64,
    0x80000001u64,
    0x8000000080008081u64,
    0x8000000000008009u64,
    0x8au64,
    0x88u64,
    0x80008009u64,
    0x8000000au64,
    0x8000808bu64,
    0x800000000000008bu64,
    0x8000000000008089u64,
    0x8000000000008003u64,
    0x8000000000008002u64,
    0x8000000000000080u64,
    0x800au64,
    0x800000008000000au64,
    0x8000000080008081u64,
    0x8000000000008080u64,
    0x80000001u64,
    0x8000000080008008u64,
];
pub const ROTR: [usize; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

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

fn rotl<T: Clone>(x: [T; 64], n: usize) -> [T; 64] {
    let rotate: [_; 64] = rotate_u64(n).try_into().unwrap();

    rotate.map(|r| x[r].clone())
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
                output.push(xor(
                    inputs[x + y * 5][i],
                    and_not(
                        inputs[(x + 2) % 5 + y * 5][i],
                        inputs[(x + 1) % 5 + y * 5][i],
                    ),
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
pub struct Keccak256RoundGate<F: RichField + Extendable<D>, const D: usize>(PhantomData<F>);

impl<F: RichField + Extendable<D>, const D: usize> Keccak256RoundGate<F, D> {
    pub fn new() -> Self {
        Self(PhantomData)
    }

    pub fn wires_input(i: usize) -> Range<usize> {
        assert!(i < STATE_SIZE);

        (i * 64)..((i + 1) * 64)
    }

    pub fn wires_tmp(i: usize) -> Range<usize> {
        assert!(i < WIDTH);

        ((STATE_SIZE + i) * 64)..((STATE_SIZE + i + 1) * 64)
    }

    pub fn wires_output(i: usize) -> Range<usize> {
        assert!(i < STATE_SIZE);

        // ((STATE_SIZE + WIDTH + i) * 64)..((STATE_SIZE + WIDTH + i + 1) * 64)
        ((STATE_SIZE + WIDTH + i) * 64)..((STATE_SIZE + WIDTH + i + 1) * 64)
    }

    pub fn end() -> usize {
        (2 * STATE_SIZE + WIDTH) * 64
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Gate<F, D> for Keccak256RoundGate<F, D> {
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

        let tmps = (0..WIDTH)
            .map(|i| vars.local_wires[Self::wires_tmp(i)].try_into().unwrap())
            .collect::<Vec<[_; 64]>>();

        // let tmps2 = (0..STATE_SIZE)
        //     .map(|i| vars.local_wires[Self::wires_tmp2(i)].to_vec())
        //     .collect::<Vec<_>>();

        let outputs = (0..STATE_SIZE)
            .map(|i| vars.local_wires[Self::wires_output(i)].to_vec())
            .collect::<Vec<_>>();

        let mut constraints = vec![];

        for x in 0..5 {
            let mut c = vec![];
            for i in 0..64 {
                let xor01 = xor(inputs[x][i], inputs[x + 5][i]);
                let xor012 = xor(xor01, inputs[x + 2 * 5][i]);
                let xor0123 = xor(xor012, inputs[x + 3 * 5][i]);
                let xor01234 = xor(xor0123, inputs[x + 4 * 5][i]);
                c.push(xor01234);
            }

            let c_lo = reduce_with_powers(&c[0..32], F::Extension::TWO);
            let c_hi = reduce_with_powers(&c[32..64], F::Extension::TWO);
            let tmps_x_lo = reduce_with_powers(&tmps[x][0..32], F::Extension::TWO);
            let tmps_x_hi = reduce_with_powers(&tmps[x][32..64], F::Extension::TWO);
            constraints.push(c_lo - tmps_x_lo);
            constraints.push(c_hi - tmps_x_hi);
        }

        let mut d = vec![];
        for x in 0..5 {
            let rot_c = rotl(tmps[(x + 1) % 5], 1);
            let mut d_bits = vec![];
            for i in 0..64 {
                d_bits.push(xor(tmps[(x + 4) % 5][i], rot_c[i]));
            }
            d.push(d_bits);
        }

        let mut theta: Vec<[_; 64]> = vec![];
        for y in 0..5 {
            for x in 0..5 {
                let mut theta_bits = vec![];
                for i in 0..64 {
                    theta_bits.push(xor(inputs[x + y * 5][i], d[x][i]));
                }
                theta.push(theta_bits.try_into().unwrap());
            }
        }

        // ρ and π steps
        let mut b_words: [Option<[_; 64]>; 25] = [(); 25].map(|_| None);
        for y in 0..5 {
            for x in 0..5 {
                let rot_theta = rotl(theta[x + y * 5], ROTR[x + y * 5]);

                b_words[y + ((2 * x + 3 * y) % 5) * 5] = Some(rot_theta);
            }
        }
        let bs = b_words.map(|x| x.unwrap());

        for y in 0..5 {
            for x in 0..5 {
                let mut b_and_not_c = vec![];
                let mut a_xor_o = vec![];
                for i in 0..64 {
                    b_and_not_c.push(
                        and_not(bs[(x + 2) % 5 + y * 5][i], bs[(x + 1) % 5 + y * 5][i]));
                    a_xor_o.push(xor(bs[x + y * 5][i], outputs[x + y * 5][i]));
                }

                let b_and_not_c_lo = reduce_with_powers(&b_and_not_c[0..32], F::Extension::TWO);
                let b_and_not_c_hi = reduce_with_powers(&b_and_not_c[32..64], F::Extension::TWO);
                let a_xor_o_lo = reduce_with_powers(&a_xor_o[0..32], F::Extension::TWO);
                let a_xor_o_hi = reduce_with_powers(&a_xor_o[32..64], F::Extension::TWO);
                constraints.push(b_and_not_c_lo - a_xor_o_lo);
                constraints.push(b_and_not_c_hi - a_xor_o_hi);
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

        let tmps = (0..WIDTH)
            .map(|i| {
                Self::wires_tmp(i)
                    .map(|j| vars.local_wires[j])
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap()
            })
            .collect::<Vec<[_; 64]>>();

        let outputs = (0..STATE_SIZE)
            .map(|i| {
                Self::wires_output(i)
                    .map(|j| vars.local_wires[j])
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        for x in 0..5 {
            let mut c = vec![];
            for i in 0..64 {
                let xor01 = xor(inputs[x][i], inputs[x + 5][i]);
                let xor012 = xor(xor01, inputs[x + 2 * 5][i]);
                let xor0123 = xor(xor012, inputs[x + 3 * 5][i]);
                let xor01234 = xor(xor0123, inputs[x + 4 * 5][i]);
                c.push(xor01234);
            }

            let c_lo = reduce_with_powers(&c[0..32], F::TWO);
            let c_hi = reduce_with_powers(&c[32..64], F::TWO);
            let tmps_x_lo = reduce_with_powers(&tmps[x][0..32], F::TWO);
            let tmps_x_hi = reduce_with_powers(&tmps[x][32..64], F::TWO);
            yield_constr.one(c_lo - tmps_x_lo);
            yield_constr.one(c_hi - tmps_x_hi);
        }

        let mut d = vec![];
        for x in 0..5 {
            let rot_c = rotl(tmps[(x + 1) % 5], 1);
            let mut d_bits = vec![];
            for i in 0..64 {
                d_bits.push(xor(tmps[(x + 4) % 5][i], rot_c[i]));
            }
            d.push(d_bits);
        }

        let mut theta: Vec<[_; 64]> = vec![];
        for y in 0..5 {
            for x in 0..5 {
                let mut theta_bits = vec![];
                for i in 0..64 {
                    theta_bits.push(xor(inputs[x + y * 5][i], d[x][i]));
                }
                theta.push(theta_bits.try_into().unwrap());
            }
        }

        // ρ and π steps
        let mut b_words: [Option<[_; 64]>; 25] = [(); 25].map(|_| None);
        for y in 0..5 {
            for x in 0..5 {
                let rot_theta = rotl(theta[x + y * 5], ROTR[x + y * 5]);

                b_words[y + ((2 * x + 3 * y) % 5) * 5] = Some(rot_theta);
            }
        }
        let bs = b_words.map(|x| x.unwrap());

        for y in 0..5 {
            for x in 0..5 {
                let mut b_and_not_c = vec![];
                let mut a_xor_o = vec![];
                for i in 0..64 {
                    b_and_not_c.push(and_not(bs[(x + 2) % 5 + y * 5][i], bs[(x + 1) % 5 + y * 5][i]));
                    a_xor_o.push(xor(bs[x + y * 5][i], outputs[x + y * 5][i]));
                }

                let b_and_not_c_lo = reduce_with_powers(&b_and_not_c[0..32], F::TWO);
                let b_and_not_c_hi = reduce_with_powers(&b_and_not_c[32..64], F::TWO);
                let a_xor_o_lo = reduce_with_powers(&a_xor_o[0..32], F::TWO);
                let a_xor_o_hi = reduce_with_powers(&a_xor_o[32..64], F::TWO);
                yield_constr.one(b_and_not_c_lo - a_xor_o_lo);
                yield_constr.one(b_and_not_c_hi - a_xor_o_hi);
            }
        }
    }

    fn eval_unfiltered_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: EvaluationTargets<D>,
    ) -> Vec<ExtensionTarget<D>> {
        let inputs: [_; STATE_SIZE] = (0..STATE_SIZE)
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
        let tmps: [_; WIDTH] = (0..WIDTH)
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
        let outputs: [_; STATE_SIZE] = (0..STATE_SIZE)
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

        let two = builder.constant(F::TWO);

        let mut constraints = vec![];

        for x in 0..WIDTH {
            let mut c = vec![];
            for ((((i0, i1), i2), i3), i4) in inputs[x]
                .into_iter()
                .zip(inputs[x + 5].into_iter())
                .zip(inputs[x + 2 * 5].into_iter())
                .zip(inputs[x + 3 * 5].into_iter())
                .zip(inputs[x + 4 * 5].into_iter())
            {
                // let out_wire = {
                //     let gate_type = Xor5Gate::<F, D>::new();
                //     let gate = builder.add_gate(gate_type, vec![]);

                //     // Route input wires.
                //     let in_wire = ExtensionTarget::from_range(gate, Xor5Gate::<F, D>::wires_input(0));
                //     builder.connect_extension(in_wire, i0);
                //     let in_wire = ExtensionTarget::from_range(gate, Xor5Gate::<F, D>::wires_input(1));
                //     builder.connect_extension(in_wire, i1);
                //     let in_wire = ExtensionTarget::from_range(gate, Xor5Gate::<F, D>::wires_input(2));
                //     builder.connect_extension(in_wire, i2);
                //     let in_wire = ExtensionTarget::from_range(gate, Xor5Gate::<F, D>::wires_input(3));
                //     builder.connect_extension(in_wire, i3);
                //     let in_wire = ExtensionTarget::from_range(gate, Xor5Gate::<F, D>::wires_input(4));
                //     builder.connect_extension(in_wire, i4);

                //     // Collect output wires.
                //     ExtensionTarget::from_range(gate, Xor5Gate::<F, D>::wires_output())
                // };

                let out_wire = {
                    let xor01 = builder.xor_extension(i0, i1);
                    let xor012 = builder.xor_extension(xor01, i2);
                    let xor0123 = builder.xor_extension(xor012, i3);
                    
                    builder.xor_extension(xor0123, i4)
                };

                c.push(out_wire);
            }

            let c_lo = reduce_with_powers_ext_circuit(builder, &c[0..32], two);
            let c_hi = reduce_with_powers_ext_circuit(builder, &c[32..64], two);
            let tmps_x_lo = reduce_with_powers_ext_circuit(builder, &tmps[x][0..32], two);
            let tmps_x_hi = reduce_with_powers_ext_circuit(builder, &tmps[x][32..64], two);
            constraints.push(builder.sub_extension(c_lo, tmps_x_lo));
            constraints.push(builder.sub_extension(c_hi, tmps_x_hi));
        }

        let mut d = vec![];
        for x in 0..5 {
            let rot_c = rotl(tmps[(x + 1) % 5].0, 1).into();
            d.push(builder.xor_u64_algebra(tmps[(x + 4) % 5], rot_c));
        }

        let mut theta = vec![];
        for y in 0..5 {
            for x in 0..5 {
                theta.push(builder.xor_u64_algebra(inputs[x + y * 5], d[x]));
            }
        }

        // ρ and π steps
        let mut b_words: [Option<U64AlgebraTarget<D>>; 25] = [(); 25].map(|_| None);
        for y in 0..5 {
            for x in 0..5 {
                let rot_self = rotl(theta[x + y * 5].0, ROTR[x + y * 5]).into();

                b_words[y + ((2 * x + 3 * y) % 5) * 5] = Some(rot_self);
            }
        }
        let bs = b_words.map(|x| x.unwrap());

        for y in 0..WIDTH {
            for x in 0..WIDTH {
                let mut b_and_not_c = vec![];
                let mut a_xor_o = vec![];
                for (((a, b), c), o) in bs[x + y * 5]
                    .into_iter()
                    .zip(bs[(x + 2) % 5 + y * 5].into_iter())
                    .zip(bs[(x + 1) % 5 + y * 5].into_iter())
                    .zip(outputs[x + y * 5].into_iter())
                {
                    // let out_wire = {
                    //     let gate_type = XorAndNotGate::<F, D>::new();
                    //     let gate = builder.add_gate(gate_type, vec![]);

                    //     // Route input wires.
                    //     let a_wire =
                    //         ExtensionTarget::from_range(gate, XorAndNotGate::<F, D>::wires_a());
                    //     builder.connect_extension(a_wire, a);
                    //     let b_wire =
                    //         ExtensionTarget::from_range(gate, XorAndNotGate::<F, D>::wires_b());
                    //     builder.connect_extension(b_wire, b);
                    //     let c_wire =
                    //         ExtensionTarget::from_range(gate, XorAndNotGate::<F, D>::wires_c());
                    //     builder.connect_extension(c_wire, c);

                    //     // Collect output wires.
                    //     ExtensionTarget::from_range(gate, XorAndNotGate::<F, D>::wires_output())
                    // };

                    b_and_not_c.push(builder.and_not_extension(b, c)); // deg 6
                    a_xor_o.push(builder.xor_extension(a, o)); // deg 4
                }

                let b_and_not_c_lo = reduce_with_powers_ext_circuit(builder, &b_and_not_c[0..32], two);
                let b_and_not_c_hi = reduce_with_powers_ext_circuit(builder, &b_and_not_c[32..64], two);
                let a_xor_o_lo = reduce_with_powers_ext_circuit(builder, &a_xor_o[0..32], two);
                let a_xor_o_hi = reduce_with_powers_ext_circuit(builder, &a_xor_o[32..64], two);
                constraints.push(builder.sub_extension(b_and_not_c_lo, a_xor_o_lo));
                constraints.push(builder.sub_extension(b_and_not_c_hi, a_xor_o_hi));
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

    fn degree(&self) -> usize {
        6
    }

    fn num_constraints(&self) -> usize {
        (STATE_SIZE + WIDTH) * 2
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
            .flat_map(|i| {
                Target::wires_from_range(self.row, Keccak256RoundGate::<F, D>::wires_input(i))
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
                Keccak256RoundGate::<F, D>::wires_input(i)
                    .map(|j| witness.get_wire(local_wire(j)))
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap()
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let c = calc_keccak_theta(inputs);

        for (i, tmp) in c.iter().enumerate() {
            let tmp_wires = Keccak256RoundGate::<F, D>::wires_tmp(i)
                .map(local_wire)
                .collect::<Vec<_>>();
            out_buffer.set_wires(tmp_wires, tmp);
        }

        let mut d = vec![];
        for x in 0..5 {
            let rot_c = rotl(c[(x + 1) % 5], 1);
            let mut d_bits = vec![];
            for i in 0..64 {
                d_bits.push(xor(c[(x + 4) % 5][i], rot_c[i]));
            }
            d.push(d_bits);
        }

        let mut theta: Vec<[_; 64]> = vec![];
        for y in 0..5 {
            for x in 0..5 {
                let mut theta_bits = vec![];
                for i in 0..64 {
                    theta_bits.push(xor(inputs[x + y * 5][i], d[x][i]));
                }
                theta.push(theta_bits.try_into().unwrap());
            }
        }

        // ρ and π steps
        let mut b_words: [Option<[_; 64]>; 25] = [(); 25].map(|_| None);
        for y in 0..5 {
            for x in 0..5 {
                let rot_theta = rotl(theta[x + y * 5], ROTR[x + y * 5]);

                b_words[y + ((2 * x + 3 * y) % 5) * 5] = Some(rot_theta);
            }
        }
        let bs = b_words.map(|x| x.unwrap());

        let outputs = calc_keccak_chi(bs);

        for (i, out) in outputs.iter().enumerate() {
            let out_wires = Keccak256RoundGate::<F, D>::wires_output(i)
                .map(local_wire)
                .collect::<Vec<_>>();
            out_buffer.set_wires(out_wires, out);
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
    use super::Keccak256RoundGate;
    use crate::gates::gate_testing::{test_eval_fns, test_low_degree};
    use crate::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    #[test]
    fn low_degree() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let gate = Keccak256RoundGate::<F, D>::new();
        test_low_degree(gate)
    }

    #[test]
    fn eval_fns() -> anyhow::Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let gate = Keccak256RoundGate::<F, D>::new();
        test_eval_fns::<F, C, _, D>(gate).unwrap();

        Ok(())
    }
}
