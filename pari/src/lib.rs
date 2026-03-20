use ark_ec::pairing::Pairing;

pub use ark_relations::gr1cs::ConstraintSystemRef;
use ark_std::marker::PhantomData;

mod batch_verify;
pub mod data_structures;
mod generator;
mod prover;
#[cfg(feature = "sol")]
mod solidity;
mod utils;
mod verifier;

#[cfg(test)]
mod test;

/// The SNARK of [[Pari]](https://eprint.iacr.org/2024/1245.pdf).
pub struct Pari<E: Pairing> {
    _p: PhantomData<E>,
}

impl<E: Pairing> Pari<E> {
    pub const SNARK_NAME: &'static [u8; 4] = b"Pari";
}
