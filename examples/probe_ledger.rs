use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};

#[allow(dead_code)]
fn g1_add_ufcs<E: Pairing>(a: &E::G1Affine, b: &E::G1Affine) -> E::G1Affine {
    // UFCS probe: does the generic env provide Add<&G1Affine> for G1?
    (<E::G1 as core::ops::Add<&E::G1Affine>>::add(a.into_group(), b)).into_affine()
}

#[allow(dead_code)]
fn g1_add_plain<E: Pairing>(a: &E::G1Affine, b: &E::G1Affine) -> E::G1Affine {
    (a.into_group() + b).into_affine()
}

fn main() {}
