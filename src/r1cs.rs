use pairing::{Engine, Field, PrimeField, PrimeFieldRepr};
use std::cmp::Ordering;
use std::io::{self, Read, Write};

use {Circuit, ConstraintSystem, Index, LinearCombination, SynthesisError, Variable};

fn read_varint_usize<R: Read>(reader: &mut R) -> io::Result<usize> {
    let mut n = 0;
    let mut buf = [0u8; 1];
    let mut shift = 0;
    reader.read_exact(&mut buf)?;
    while buf[0] >> 7 == 1 {
        n += ((buf[0] & 127) as usize) << shift;
        shift += 7;
        reader.read_exact(&mut buf)?;
    }
    n += ((buf[0] & 127) as usize) << shift;
    Ok(n)
}

fn write_varint_usize<W: Write>(writer: &mut W, mut n: usize) -> io::Result<()> {
    while n > 127 {
        writer.write(&[(1 << 7) | (n & 127) as u8])?;
        n >>= 7;
    }
    writer.write(&[(n & 127) as u8])?;
    Ok(())
}

fn read_varint_i64<R: Read>(reader: &mut R) -> io::Result<i64> {
    let res = read_varint_usize(reader)?;
    if res & 1 == 0 {
        Ok((res >> 1) as i64)
    } else {
        Ok(-1 * ((res >> 1) + 1) as i64)
    }
}

fn write_varint_i64<W: Write>(writer: &mut W, n: i64) -> io::Result<()> {
    let n = ((n << 1) ^ (n >> 63)) as usize;
    write_varint_usize(writer, n)
}

fn read_varint_fr<E: Engine, R: Read>(reader: &mut R) -> io::Result<E::Fr> {
    let mut repr = <E::Fr as PrimeField>::Repr::default();
    repr.read_signedvarint(reader)?;
    match E::Fr::from_repr(repr) {
        Ok(res) => Ok(res),
        Err(_) => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "varint is not in field",
        )),
    }
}

fn write_varint_fr<E: Engine, W: Write>(writer: &mut W, e: &E::Fr) -> io::Result<()> {
    e.into_repr().write_signedvarint(writer)?;
    Ok(())
}

fn write_varint_frrepr<E: Engine, W: Write>(
    writer: &mut W,
    e: &<E::Fr as PrimeField>::Repr,
) -> io::Result<()> {
    e.write_signedvarint(writer)?;
    Ok(())
}

struct Constraint<E: Engine> {
    a: LinearCombination<E>,
    b: LinearCombination<E>,
    c: LinearCombination<E>,
}

impl<E: Engine> Constraint<E> {
    fn write<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        // LinearCombination
        // | Sequence of (VariableIndex, Coefficient) |
        // - Coefficients must be non-zero
        // - Sorted by type, then index
        //    - [constant, rev_sorted([instance]), sorted([witness])]
        fn write_lc<E: Engine, W: Write>(
            lc: &LinearCombination<E>,
            writer: &mut W,
        ) -> io::Result<()> {
            write_varint_usize(writer, lc.0.len())?;
            let mut tmp = lc.0.clone();
            tmp.sort_by(|a, b| match (a, b) {
                ((Variable(Index::Input(_)), _),
                    (Variable(Index::Aux(_)), _)) => Ordering::Less,
                ((Variable(Index::Aux(_)), _),
                    (Variable(Index::Input(_)), _)) => Ordering::Greater,
                ((Variable(Index::Input(i)), _),
                    (Variable(Index::Input(j)), _)) => i.cmp(j),
                ((Variable(Index::Aux(i)), _),
                    (Variable(Index::Aux(j)), _)) => i.cmp(j),
            });
            for (v, c) in &tmp {
                if !c.is_zero() {
                    // Negative values: instance indices
                    // Zero: constant 1
                    // Positive values: witness indices
                    let v: i64 = match v {
                        Variable(Index::Input(0)) => 0,
                        Variable(Index::Input(i)) => -(*i as i64),
                        Variable(Index::Aux(i)) => *i as i64 + 1,
                    };
                    write_varint_i64(writer, v)?;
                    write_varint_fr::<E, W>(writer, c)?;
                }
            }
            Ok(())
        }

        write_lc(&self.a, writer)?;
        write_lc(&self.b, writer)?;
        write_lc(&self.c, writer)
    }
}

/// The in-memory representation of an (.r1cs, .assignments) file pair. Can be
/// used both as a ConstraintSystem (for serializing Circuits with their
/// assignments) and a Circuit (for creating Proofs).
pub struct R1CS<E: Engine> {
    input_assignment: Vec<E::Fr>,
    aux_assignment: Vec<E::Fr>,
    constraints: Vec<Constraint<E>>,
}

impl<E: Engine> ConstraintSystem<E> for R1CS<E> {
    type Root = Self;

    fn alloc<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.aux_assignment.push(f()?);

        Ok(Variable(Index::Aux(self.aux_assignment.len() - 1)))
    }

    fn alloc_input<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.input_assignment.push(f()?);

        Ok(Variable(Index::Input(self.input_assignment.len() - 1)))
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
    {
        let a = a(LinearCombination::zero());
        let b = b(LinearCombination::zero());
        let c = c(LinearCombination::zero());

        self.constraints.push(Constraint { a, b, c })
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self) {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}

impl<E: Engine> Circuit<E> for R1CS<E> {
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        for (i, a) in self.input_assignment.into_iter().enumerate() {
            cs.alloc_input(|| format!("R1CS input assignment {}", i), || Ok(a))?;
        }

        for (i, a) in self.aux_assignment.into_iter().enumerate() {
            cs.alloc(|| format!("R1CS aux assignment {}", i), || Ok(a))?;
        }

        for (i, c) in self.constraints.into_iter().enumerate() {
            let a = c.a;
            let b = c.b;
            let c = c.c;
            cs.enforce(|| format!("R1CS constraint {}", i), |_| a, |_| b, |_| c);
        }

        Ok(())
    }
}

// Header:
// - Magic bytes
// - Version (VarInt)
// - Number of SignedVarInts in the header (VarInt)
// - Field description
//   - Characteristic P
//   - Extension M
// - Number of instance variables N_X
// - Number of witness variables N_W
// - Further SignedVarInts are undefined in this spec, should be ignored
//
// | MAGICBYTES | VERSION | HEADER_LENGTH | P | M | N_X | N_W |( ... |)

fn serialize_header<E: Engine, W: Write>(
    magic: &[u8],
    nx: usize,
    nw: usize,
    writer: &mut W,
) -> io::Result<()> {
    writer.write(magic)?;
    write_varint_usize(writer, 0)?;
    write_varint_usize(writer, 4)?;
    write_varint_frrepr::<E, W>(writer, &E::Fr::char())?;
    write_varint_i64(writer, 2)?; // TODO
    write_varint_i64(writer, nx as i64)?;
    write_varint_i64(writer, nw as i64)
}

pub fn serialize_to_r1cs<E, C, W>(
    circuit: C,
    r1csfile: &mut W,
    assignments: &mut W,
) -> Result<(), SynthesisError>
where
    E: Engine,
    C: Circuit<E>,
    W: Write,
{
    let mut r1cs = R1CS {
        input_assignment: vec![],
        aux_assignment: vec![],
        constraints: vec![],
    };

    r1cs.alloc_input(|| "", || Ok(E::Fr::one()))?;

    circuit.synthesize(&mut r1cs)?;

    let nx = r1cs.input_assignment.len() - 1;
    let nw = r1cs.aux_assignment.len();

    serialize_header::<E, W>(&[82, 49, 67, 83], nx, nw, r1csfile)?;
    write_varint_usize(r1csfile, r1cs.constraints.len())?;
    for c in r1cs.constraints {
        c.write(r1csfile)?;
    }

    serialize_header::<E, W>(&[82, 49, 97, 115], nx, nw, assignments)?;
    write_varint_fr::<E, W>(assignments, &r1cs.input_assignment[0])?;
    for a in &r1cs.aux_assignment {
        write_varint_fr::<E, W>(assignments, a)?;
    }
    for a in &r1cs.input_assignment[1..] {
        write_varint_fr::<E, W>(assignments, a)?;
    }

    Ok(())
}

pub fn unserialize_from_r1cs<E, R>(
    r1cs: &mut R,
    assignments: &mut R,
) -> Result<R1CS<E>, SynthesisError>
where
    E: Engine,
    R: Read,
{
    let mut circuit = R1CS {
        input_assignment: vec![],
        aux_assignment: vec![],
        constraints: vec![],
    };

    // TODO: Unserialize

    Ok(circuit)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn varint_usize() {
        macro_rules! eval {
            ($value:expr, $expected:expr) => {
                let mut buf = Vec::new();
                write_varint_usize(&mut buf, $value).unwrap();
                assert_eq!(&buf, $expected);
                let mut slice: &[u8] = $expected;
                let mut read: &mut Read = &mut slice;
                let n = read_varint_usize(&mut read).unwrap();
                assert_eq!(n, $value);
            };
        }

        eval!(0, &[0]);
        eval!(1, &[1]);
        eval!(2, &[2]);
        eval!(3, &[3]);
        eval!(127, &[127]);
        eval!(128, &[128, 1]);
        eval!(129, &[129, 1]);
        eval!(255, &[255, 1]);
        eval!(256, &[128, 2]);
        eval!(383, &[255, 2]);
        eval!(384, &[128, 3]);
        eval!(16383, &[255, 127]);
        eval!(16384, &[128, 128, 1]);
        eval!(16385, &[129, 128, 1]);
        eval!(65535, &[255, 255, 3]);
        eval!(65536, &[128, 128, 4]);
        eval!(65537, &[129, 128, 4]);
        eval!(2097151, &[255, 255, 127]);
        eval!(2097152, &[128, 128, 128, 1]);
        eval!(2097153, &[129, 128, 128, 1]);
    }

    #[test]
    fn varint_i64() {
        macro_rules! eval {
            ($value:expr, $expected:expr) => {
                let mut buf = Vec::new();
                write_varint_i64(&mut buf, $value).unwrap();
                assert_eq!(&buf, $expected);
                let mut slice: &[u8] = $expected;
                let mut read: &mut Read = &mut slice;
                let n = read_varint_i64(&mut read).unwrap();
                assert_eq!(n, $value);
            };
        }

        eval!(0, &[0]);
        eval!(-1, &[1]);
        eval!(1, &[2]);
        eval!(-2, &[3]);
        eval!(2, &[4]);
        eval!(-63, &[125]);
        eval!(63, &[126]);
        eval!(-64, &[127]);
        eval!(64, &[128, 1]);
        eval!(-65, &[129, 1]);
        eval!(-128, &[255, 1]);
        eval!(128, &[128, 2]);
        eval!(-192, &[255, 2]);
        eval!(192, &[128, 3]);
        eval!(-8192, &[255, 127]);
        eval!(8192, &[128, 128, 1]);
        eval!(-8193, &[129, 128, 1]);
        eval!(-32768, &[255, 255, 3]);
        eval!(32768, &[128, 128, 4]);
        eval!(-32769, &[129, 128, 4]);
        eval!(-1048576, &[255, 255, 127]);
        eval!(1048576, &[128, 128, 128, 1]);
        eval!(-1048577, &[129, 128, 128, 1]);
    }

    #[test]
    fn varint_fr() {
        use pairing::bls12_381::Bls12;
        macro_rules! eval {
            ($value:expr, $expected:expr) => {
                let mut buf_tmp = Vec::new();
                $value.into_repr().write_le(&mut buf_tmp).unwrap();
                println!("le = {:?}", buf_tmp);
                let mut buf = Vec::new();
                write_varint_fr::<Bls12, Vec<u8>>(&mut buf, $value).unwrap();
                assert_eq!(&buf[..], &$expected[..]);
                let mut slice: &[u8] = $expected;
                let mut read: &mut Read = &mut slice;
                let n = read_varint_fr::<Bls12, &mut Read>(&mut read).unwrap();
                assert_eq!(n.into_repr().as_ref(), $value.into_repr().as_ref());
            };
        }

        let zero = <Bls12 as Engine>::Fr::zero();
        eval!(&zero, &[0]);

        let one = <Bls12 as Engine>::Fr::one();
        eval!(&one, &[1]);

        // n = -1
        let mut n = one;
        n.negate();
        eval!(
            &n,
            &[
                128, 128, 128, 128, 240, 255, 255, 255, 255, 253, 239, 242, 255, 223, 128, 210,
                189, 167, 149, 192, 157, 180, 130, 132, 216, 243, 204, 193, 212, 175, 231, 148,
                211, 206, 182, 159, 1,
            ]
        );

        // n = 2
        n.negate();
        n.double();
        eval!(&n, &[2]);

        // n = -2
        n.negate();
        eval!(
            &n,
            &[
                255, 255, 255, 255, 239, 255, 255, 255, 255, 253, 239, 242, 255, 223, 128, 210,
                189, 167, 149, 192, 157, 180, 130, 132, 216, 243, 204, 193, 212, 175, 231, 148,
                211, 206, 182, 159, 1,
            ]
        );

        // n = 3
        n.negate();
        n.add_assign(&one);
        eval!(&n, &[3]);

        // n = -3
        n.negate();
        eval!(
            &n,
            &[
                254, 255, 255, 255, 239, 255, 255, 255, 255, 253, 239, 242, 255, 223, 128, 210,
                189, 167, 149, 192, 157, 180, 130, 132, 216, 243, 204, 193, 212, 175, 231, 148,
                211, 206, 182, 159, 1,
            ]
        );

        // n = 4
        n.negate();
        n.add_assign(&one);
        eval!(&n, &[4]);

        // n = 128
        n.double();
        n.double();
        n.double();
        n.double();
        n.double();
        eval!(&n, &[128, 1]);

        // n = 127
        n.sub_assign(&one);
        eval!(&n, &[127]);

        // n = 129
        n.add_assign(&one);
        n.add_assign(&one);
        eval!(&n, &[129, 1]);
    }
}
