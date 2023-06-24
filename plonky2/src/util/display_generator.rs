use plonky2_field::types::Field;

use crate::iop::{target::Target, generator::{SimpleGenerator, GeneratedValues}, witness::{PartitionWitness, Witness}};

use super::serialization::{IoResult, Write, Buffer, Read};

#[derive(Clone, Debug)]
pub struct DisplayGenerator {
    pub caption: usize,
    pub targets: Vec<Target>,
}

impl<F: Field> SimpleGenerator<F> for DisplayGenerator {
    fn id(&self) -> String {
        "DisplayGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        self.targets.clone()
    }

    fn run_once(&self, witness: &PartitionWitness<F>, _out_buffer: &mut GeneratedValues<F>) {
        let values = self.targets.iter().map(|target| witness.get_target(*target)).collect::<Vec<_>>();
        dbg!(self.caption, self.targets.first(), values);
    }

    fn serialize(&self, dst: &mut Vec<u8>) -> IoResult<()> {
        dst.write_usize(self.caption)?;
        dst.write_usize(self.targets.len())?;
        for target in &self.targets {
            dst.write_target(*target)?;
        }
        

        Ok(())
    }

    fn deserialize(source: &mut Buffer) -> IoResult<Self> {
        let caption = source.read_usize()?;
        let mut targets = vec![];
        for _ in 0..source.read_usize()? {
            targets.push(source.read_target()?);
        }

          
        Ok(Self { caption, targets })
    }
}