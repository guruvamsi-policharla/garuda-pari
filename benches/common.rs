//! Shared benchmark support: the Rescue demo circuit and CSV result output.

use std::error::Error;
use std::fs::{create_dir_all, metadata, OpenOptions};
use std::str::FromStr;
use std::time::Duration;

use ark_crypto_primitives::{
    crh::{
        rescue::constraints::{CRHGadget, CRHParametersVar},
        CRHSchemeGadget,
    },
    sponge::rescue::RescueConfig,
};
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, fields::fp::FpVar};
use ark_relations::gr1cs::{ConstraintSynthesizer, SynthesisError};
use ark_relations::utils::IndexMap;
use ark_std::rand::Rng;
use csv::Writer;
use num_bigint::BigUint;
use zkpari::ConstraintSystemRef;

pub const RESCUE_ROUNDS: usize = 12;
pub const WIDTH: usize = 9;
const RESULT_FOLDER_PATH: &str = "results";

/// This is our demo circuit for proving knowledge of the
/// preimage of a Rescue hash invocation.
#[derive(Clone)]
pub struct RescueDemo<F: PrimeField> {
    pub input: Option<Vec<F>>,
    pub image: Option<F>,
    pub num_instances: usize,
    pub config: RescueConfig<F>,
    pub num_invocations: usize,
}

pub fn create_test_rescue_parameter<F: PrimeField>(rng: &mut impl Rng) -> RescueConfig<F> {
    let mut mds = vec![vec![]; 4];
    for i in 0..4 {
        for _ in 0..4 {
            mds[i].push(F::rand(rng));
        }
    }

    let mut ark = vec![vec![]; 25];
    for i in 0..(2 * RESCUE_ROUNDS + 1) {
        for _ in 0..4 {
            ark[i].push(F::rand(rng));
        }
    }
    let alpha_inv: BigUint = BigUint::from_str(
        "20974350070050476191779096203274386335076221000211055129041463479975432473805",
    )
    .unwrap();
    RescueConfig::<F>::new(RESCUE_ROUNDS, 5, alpha_inv, mds, ark, 3, 1)
}

impl<F: PrimeField + ark_crypto_primitives::sponge::Absorb> ConstraintSynthesizer<F>
    for RescueDemo<F>
{
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let params_g =
            CRHParametersVar::<F>::new_witness(cs.clone(), || Ok(self.config.clone())).unwrap();
        let mut input_g = Vec::new();

        for elem in self
            .input
            .clone()
            .ok_or(SynthesisError::AssignmentMissing)
            .unwrap()
        {
            input_g.push(FpVar::new_witness(cs.clone(), || Ok(elem)).unwrap());
        }

        let mut crh_a_g: Option<FpVar<F>> =
            Some(CRHGadget::<F>::evaluate(&params_g, &input_g).unwrap());

        for _ in 0..(self.num_invocations - 1) {
            crh_a_g =
                Some(CRHGadget::<F>::evaluate(&params_g, &vec![crh_a_g.unwrap(); WIDTH]).unwrap());
        }

        for _ in 0..self.num_instances - 1 {
            let image_instance: FpVar<F> = FpVar::new_input(cs.clone(), || {
                Ok(self.image.ok_or(SynthesisError::AssignmentMissing).unwrap())
            })
            .unwrap();

            if let Some(crh_a_g) = crh_a_g.clone() {
                let _ = crh_a_g.enforce_equal(&image_instance);
            }
        }

        Ok(())
    }
}

#[derive(Debug)]
pub struct BenchResult {
    pub curve: String,
    pub num_thread: usize,
    pub input_size: usize,
    pub num_invocations: usize,
    pub num_nonzero_entries: usize,
    pub num_keygen_iterations: usize,
    pub num_prover_iterations: usize,
    pub num_verifier_iterations: usize,
    pub predicate_constraints: IndexMap<String, usize>,
    pub num_constraints: usize,
    pub keygen_time: Duration,
    pub keygen_prep_time: Duration,
    pub keygen_corrected_time: Duration,
    pub pk_size: usize,
    pub vk_size: usize,
    pub prover_time: Duration,
    pub prover_prep_time: Duration,
    pub prover_corrected_time: Duration,
    pub proof_size: usize,
    pub verifier_time: Duration,
}

impl BenchResult {
    pub fn save_to_csv(&self, filename: &str) -> Result<(), Box<dyn Error>> {
        // Ensure the "results" directory exists
        create_dir_all(RESULT_FOLDER_PATH)?;

        // Construct full path to file
        let full_path = format!("{RESULT_FOLDER_PATH}/{filename}");

        // Check if file exists
        let file_exists = metadata(&full_path).is_ok();

        // Open the file in append mode
        let file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&full_path)?;

        // Create CSV writer
        let mut writer = Writer::from_writer(file);

        // If the file is newly created, write headers
        if !file_exists {
            writer.write_record([
                "Curve",
                "Num Threads",
                "Num Invocations",
                "Input Size",
                "Num Nonzero Entries",
                "Num Constraints",
                "Predicate Constraints",
                "Num KeyGen Iterations",
                "Setup Time (s)",
                "Setup Preparation Time (s)",
                "Setup Corrected Time (s)",
                "PK Size (bytes)",
                "VK Size (bytes)",
                "Num Prover Iterations",
                "Prover Time (s)",
                "Prover preparation Time (s)",
                "Prover Corrected Time (s)",
                "Proof Size (bytes)",
                "Num Verifier Iterations",
                "Verifier Time (ms)",
            ])?;
        }

        // Serialize data
        let predicate_constraints_str = serde_json::to_string(
            &self
                .predicate_constraints
                .iter()
                .map(|(k, v)| (k.clone(), *v))
                .collect::<Vec<_>>(),
        )?;
        let keygen_time_s = self.keygen_time.as_secs_f64();
        let prover_time_s = self.prover_time.as_secs_f64();
        let keygen_prep_time_s = self.keygen_prep_time.as_secs_f64();
        let prover_prep_time_s = self.prover_prep_time.as_secs_f64();
        let keygen_corrected_time_s = self.keygen_corrected_time.as_secs_f64();
        let prover_corrected_time_s = self.prover_corrected_time.as_secs_f64();
        let verifier_time_ms = self.verifier_time.as_secs_f64() * 1000.0;

        writer.write_record(&[
            Self::extract_curve_name(&self.curve).unwrap_or("-".to_string()),
            self.num_thread.to_string(),
            self.num_invocations.to_string(),
            self.input_size.to_string(),
            self.num_nonzero_entries.to_string(),
            self.num_constraints.to_string(),
            predicate_constraints_str,
            self.num_keygen_iterations.to_string(),
            keygen_time_s.to_string(),
            keygen_prep_time_s.to_string(),
            keygen_corrected_time_s.to_string(),
            match self.pk_size {
                0 => "-".to_string(),
                _ => self.pk_size.to_string(),
            },
            match self.vk_size {
                0 => "-".to_string(),
                _ => self.vk_size.to_string(),
            },
            self.num_prover_iterations.to_string(),
            prover_time_s.to_string(),
            prover_prep_time_s.to_string(),
            prover_corrected_time_s.to_string(),
            match self.proof_size {
                0 => "-".to_string(),
                _ => self.proof_size.to_string(),
            },
            self.num_verifier_iterations.to_string(),
            verifier_time_ms.to_string(),
        ])?;

        writer.flush()?;

        println!("Benchmark result saved to {filename}");
        Ok(())
    }

    fn extract_curve_name(input: &str) -> Option<String> {
        // Take the content inside the first angle bracket pair, e.g.
        // "Bls12<ark_bls12_381::Config>" -> "ark_bls12_381"
        let start = input.find('<')?;
        let end = input.find('>')?;
        let inside = &input[start + 1..end];
        let first_part = inside.split("::").next()?.to_string();
        Some(first_part)
    }
}
