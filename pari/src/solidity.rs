use crate::data_structures::Proof;
use crate::data_structures::VerifyingKey;
use ark_ec::pairing::Pairing;
use ark_ec::AffineRepr;
use ark_ff::Field;
use ark_ff::PrimeField;
use num_bigint::BigUint;
use regex::Regex;
use std::fs::File;
use std::io::Write;
pub const CONTRACT_PATH: &str = "./smart-contracts/";
pub struct Solidifier<E: Pairing> {
    pub p: Option<BigUint>,
    pub q: Option<BigUint>,
    pub coset_size: Option<usize>,
    pub coset_offset: Option<E::ScalarField>,
    pub minus_coset_offset_to_coset_size: Option<E::ScalarField>,
    pub coset_offset_to_coset_size_inverse: Option<E::ScalarField>,
    pub neg_h_gi: Option<Vec<E::ScalarField>>,
    pub nom_i: Option<Vec<E::ScalarField>>,
    pub vk: Option<VerifyingKey<E>>,
    pub proof: Option<Proof<E>>,
    pub input: Option<Vec<E::ScalarField>>,
}

impl<E: Pairing> Solidifier<E> {
    pub fn new() -> Self {
        Solidifier {
            p: Some(E::BaseField::MODULUS.into()),
            q: Some(E::ScalarField::MODULUS.into()),
            coset_size: None,
            coset_offset: None,
            minus_coset_offset_to_coset_size: None,
            coset_offset_to_coset_size_inverse: None,
            neg_h_gi: None,
            nom_i: None,
            vk: None,
            proof: None,
            input: None,
        }
    }

    fn extract_quad_ext_field_coordinates(input: &str) -> Option<(String, String)> {
        let re = Regex::new(r"QuadExtField\s*\(\s*([\d]+)\s*\+\s*([\d]+)\s*\*\s*u\s*\)").unwrap();

        re.captures(input).map(|caps| {
            let num1 = caps.get(1).unwrap().as_str().trim().to_string();
            let num2 = caps.get(2).unwrap().as_str().trim().to_string();
            (num1, num2)
        })
    }
    pub(crate) fn set_vk(&mut self, vk: &VerifyingKey<E>) {
        self.vk = Some(vk.clone());
    }

    pub(crate) fn set_proof(&mut self, proof: &Proof<E>) {
        self.proof = Some(proof.clone());
    }

    pub(crate) fn set_input(&mut self, input: &[E::ScalarField]) {
        let mut input_vec = vec![E::ScalarField::ONE];
        input_vec.extend_from_slice(input);
        self.input = Some(input_vec);
    }

    fn generate_input_static_code(input_size: usize) -> String {
        let i = input_size - 1;

        // Generate the Lagrange coefficient calculations
        let neg_lagrange_code = (0..=i)
            .map(|idx| {
                format!(
                    "uint256 neg_cur_elem{idx} = addmod(chall, NEG_H_Gi_{idx}, R); \n
                     uint256 neg_cur_elem{idx}_inv = invert_FR(neg_cur_elem{idx}); \n
                     uint256 lagrange_{idx} = mulmod(neg_cur_elem{idx}_inv, NOM_{idx}, R);\n"
                )
            })
            .collect::<Vec<_>>()
            .join(" ");

        // Generate Solidity code for binary tree addition
        let mut input_vars: Vec<String> = (0..=i)
            .map(|idx| format!("mulmod(lagrange_{}, input[{}], R)", idx, idx))
            .collect();

        while input_vars.len() > 1 {
            let mut new_input_vars = Vec::new();
            let len = input_vars.len();

            for j in (0..len).step_by(2) {
                if j + 1 < len {
                    // Pairwise addmod
                    new_input_vars.push(format!(
                        "addmod({}, {}, R)",
                        input_vars[j],
                        input_vars[j + 1]
                    ));
                } else {
                    // If odd number, carry last element
                    new_input_vars.push(input_vars[j].clone());
                }
            }
            input_vars = new_input_vars;
        }

        let x_a_code = format!("uint256 x_a = {};", input_vars[0]);

        format!("{}\n\n{}", neg_lagrange_code, x_a_code)
    }

    pub fn solidify(&self) {
        let input_size = self.input.as_ref().unwrap().len();

        let neg_h_gi_str = self
            .neg_h_gi
            .as_ref()
            .unwrap()
            .iter()
            .enumerate()
            .fold(String::new(), |acc, (i, x)| {
                acc + &format!("    uint256 constant NEG_H_Gi_{i} = {x};\n")
            });
        let nom_i_str = self
            .nom_i
            .as_ref()
            .unwrap()
            .iter()
            .enumerate()
            .fold(String::new(), |acc, (i, x)| {
                acc + &format!("    uint256 constant NOM_{i} = {x};\n")
            });

        let input_ref = self.input.as_ref().unwrap();
        let input_str = if input_ref.len() == 1 {
            format!("uint256({})", input_ref[0])
        } else {
            input_ref
                .iter()
                .map(|x| format!("{x}"))
                .collect::<Vec<_>>()
                .join(",\n ")
        };
        let input_refs_str = self
            .input
            .as_ref()
            .unwrap()
            .iter()
            .enumerate()
            .map(|(i, _)| format!("input[{}],\n", i))
            .collect::<Vec<_>>()
            .join("");
        let vk = self.vk.clone().unwrap();

        let h_x: (String, String) =
            Self::extract_quad_ext_field_coordinates(&format!("{}", vk.h.x().unwrap())).unwrap();
        let h_y: (String, String) =
            Self::extract_quad_ext_field_coordinates(&format!("{}", vk.h.y().unwrap())).unwrap();

        let delta_h_x: (String, String) =
            Self::extract_quad_ext_field_coordinates(&format!("{}", vk.delta_two_h.x().unwrap()))
                .unwrap();
        let delta_h_y: (String, String) =
            Self::extract_quad_ext_field_coordinates(&format!("{}", vk.delta_two_h.y().unwrap()))
                .unwrap();

        let tau_h_x: (String, String) = Self::extract_quad_ext_field_coordinates(&format!(
            "{}",
            self.vk.clone().unwrap().tau_h.x().unwrap()
        ))
        .unwrap();
        let tau_h_y: (String, String) = Self::extract_quad_ext_field_coordinates(&format!(
            "{}",
            self.vk.clone().unwrap().tau_h.y().unwrap()
        ))
        .unwrap();
        let denoms_init = (0..input_size)
            .map(|idx| format!("denoms[{idx}] = addmod(chall, NEG_H_Gi_{idx}, R);"))
            .collect::<Vec<_>>()
            .join("\n");

        // Step 2: Compute lagrange[i] = mulmod(denoms_inv[i], NOM_i, R);
        let nom_mul = (0..input_size)
            .map(|idx| {
                format!(
                    "        lag = mulmod(denoms[{idx}], NOM_{idx}, R);\n
        x_a = addmod(x_a, mulmod(lag, input[{idx}], R), R);"
                )
            })
            .collect::<Vec<_>>()
            .join("\n");

        let solidity_code = format!(
            r#"// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Pari verifier for input size {input_size}
contract Pari {{
    /// The proof is invalid.
    /// @dev This can mean that provided Groth16 proof points are not on their
    /// curves, that pairing equation fails, or that the proof is not for the
    /// provided public input.
    error ProofInvalid();

    // Addresses of precompiles
    uint256 constant PRECOMPILE_MODEXP = 0x05;
    uint256 constant PRECOMPILE_ADD = 0x06;
    uint256 constant PRECOMPILE_MUL = 0x07;
    uint256 constant PRECOMPILE_VERIFY = 0x08;

    // Base field Fp order P and scalar field Fr order R.
    // For BN254 these are computed as follows:
    //     t = 4965661367192848881
    //     P = 36⋅t⁴ + 36⋅t³ + 24⋅t² + 6⋅t + 1
    //     R = 36⋅t⁴ + 36⋅t³ + 18⋅t² + 6⋅t + 1
    uint256 constant P = {p};
    uint256 constant R = {q};

    // Exponents for inversions and square roots mod P
    uint256 constant EXP_INVERSE_FR = {exp_inv_r}; // R - 2

    //////////////////////////////// constants for processing the input //////////////////////////////

    // FFT Coset information
    uint256 constant COSET_SIZE = {coset_size};
    uint256 constant COSET_OFFSET = {coset_offset};

    // Preprocessed intermediate values for computing the lagrande polynomials
    // This computation is done according to https://o1-labs.github.io/proof-systems/plonk/lagrange.html
    uint256 constant MINUS_COSET_OFFSET_TO_COSET_SIZE = {minus_coset_offset_to_coset_size};
    uint256 constant COSET_OFFSET_TO_COSET_SIZE_INVERSE = {coset_offset_to_coset_size_inverse};

    {neg_h_gi_str}
    {nom_i_str}

    ////////////////////////////////////// Preprocessed verification key ////////////////////////////////

    uint256 constant G_X = {g_x};
    uint256 constant G_Y = {g_y};
    uint256 constant H_X_0 = {h_x_0};
    uint256 constant H_X_1 = {h_x_1};
    uint256 constant H_Y_0 = {h_y_0};
    uint256 constant H_Y_1 = {h_y_1};
    uint256 constant ALPHA_G_X = {alpha_g_x};
    uint256 constant ALPHA_G_Y = {alpha_g_y};
    uint256 constant BETA_G_X = {beta_g_x};
    uint256 constant BETA_G_Y = {beta_g_y};
    uint256 constant TAU_H_X_0 = {tau_h_x_0};
    uint256 constant TAU_H_X_1 = {tau_h_x_1};
    uint256 constant TAU_H_Y_0 = {tau_h_y_0};
    uint256 constant TAU_H_Y_1 = {tau_h_y_1};
    uint256 constant DELTA_TWO_H_X_0 = {delta_h_x_0};
    uint256 constant DELTA_TWO_H_X_1 = {delta_h_x_1};
    uint256 constant DELTA_TWO_H_Y_0 = {delta_h_y_0};
    uint256 constant DELTA_TWO_H_Y_1 = {delta_h_y_1};

    /////////////////////////////////////// Helper functions ////////////////////////////////

    /// Exponentiation in Fp.
    /// @notice Returns a number x such that a ^ e = x in Fp.
    /// @notice The input does not need to be reduced.
    /// @param a the base
    /// @param e the exponent
    /// @return x the result
    function exp(uint256 a, uint256 e) internal view returns (uint256 x) {{
        bool success;
        assembly ("memory-safe") {{
            let f := mload(0x40)
            mstore(f, 0x20)
            mstore(add(f, 0x20), 0x20)
            mstore(add(f, 0x40), 0x20)
            mstore(add(f, 0x60), a)
            mstore(add(f, 0x80), e)
            mstore(add(f, 0xa0), R)
            success := staticcall(gas(), PRECOMPILE_MODEXP, f, 0xc0, f, 0x20)
            x := mload(f)
        }}
        if (!success) {{
            // Exponentiation failed.
            // Should not happen.
            revert ProofInvalid();
        }}
    }}

    /// Invertsion in Fr.
    /// @notice Returns a number x such that a * x = 1 in Fr.
    /// @notice The input does not need to be reduced.
    /// @notice Reverts with ProofInvalid() if the inverse does not exist
    /// @param a the input
    /// @return x the solution
    function invert_FR(uint256 a) internal view returns (uint256 x) {{
        x = exp(a, EXP_INVERSE_FR);
        if (mulmod(a, x, R) != 1) {{
            // Inverse does not exist.
            // Can only happen during G2 point decompression.
            revert ProofInvalid();
        }}
    }}

    // Computes Z_H(challenge) as the vanishing polynomial for the coset
    // Z_H(x) = x^m-h^m
    // where m = COSET_SIZE and h = COSET_OFFSET
    function compute_vanishing_poly(
        uint256 chall
    ) internal view returns (uint256 result) {{
        // Exp uses 0x05 precompile internally
        uint256 tau_exp = exp(chall, COSET_SIZE);
        result = addmod(tau_exp, MINUS_COSET_OFFSET_TO_COSET_SIZE, R);
    }}

    function batch_invert(uint256[{input_size}] memory arr) internal view {{
        // 1) forward pass
        uint256 running = 1;
        // We'll store partial_prod products in a separate local array of the same length
        // so we can do the backward pass easily
        uint256[{input_size}] memory partial_prod;
        for (uint256 i = 0; i < {input_size}; i++) {{
            partial_prod[i] = running; // store partial_prod
            running = mulmod(running, arr[i], R);
        }}

        // 2) invert the running product once
        uint256 invRunning = exp(running, EXP_INVERSE_FR); // single exponentiation

        // 3) backward pass
        for (uint256 i = {input_size}; i > 0; ) {{
            // i goes from {input_size} down to 1
            // - 1 => i-1
            unchecked {{
                i--;
        }}
            // arr[i] = partial_prod[i] * invRunning
            uint256 orig = arr[i];
            arr[i] = mulmod(partial_prod[i], invRunning, R);
            // update invRunning *= orig
            invRunning = mulmod(invRunning, orig, R);
        }}
        }}


    // Computes v_q = (v_a^2-v_b)/Z_H(challenge)
    function comp_vq(
        uint256[{input_size}] calldata input,
        uint256[6] calldata proof,
        uint256 chall
    ) internal view returns (uint256 v_q) {{
        uint256[{input_size}] memory denoms;

        {denoms_init}

        batch_invert(denoms);

        uint256 x_a = 0;
        uint256 lag = 0;


        {nom_mul}



        // 4) We then do the usual steps: compute vanish, numerator, etc.
        // vanish = (chall^COSET_SIZE + constant)
        uint256 vanish = compute_vanishing_poly(chall);

        // numerator = ( (proof[0] + x_a)^2 ) - proof[1]
        uint256 numerator = addmod(proof[0], x_a, R);
        numerator = mulmod(numerator, numerator, R);
        numerator = addmod(numerator, R - proof[1], R);

        // vanishInv
        uint256 vanishInv = invert_FR(vanish);

        // v_q
        v_q = mulmod(numerator, vanishInv, R);



    }}

    function compute_A(
        uint256 v_a,
        uint256 v_b,
        uint256 v_q,
        uint256 chall,
        uint256 u_g_x,
        uint256 u_g_y
    ) internal view returns (uint256 A_x, uint256 A_y) {{

        bool success;
        uint256[2] memory P1;
        uint256[2] memory P2;
        uint256[2] memory P3;
        uint256[2] memory P4;
        uint256[2] memory P5;

        assembly ("memory-safe") {{
            let ptr := mload(0x40)
            mstore(ptr, ALPHA_G_X)
            mstore(add(ptr, 0x20), ALPHA_G_Y)
            mstore(add(ptr, 0x40), v_a)
            success := staticcall(gas(), PRECOMPILE_MUL, ptr, 0x60, P1, 0x40)
        }}

        assembly ("memory-safe") {{
            let ptr := mload(0x40)
            mstore(ptr, BETA_G_X)
            mstore(add(ptr, 0x20), BETA_G_Y)
            mstore(add(ptr, 0x40), v_b)
            success := staticcall(gas(), PRECOMPILE_MUL, ptr, 0x60, P2, 0x40)
        }}

        assembly ("memory-safe") {{
            let ptr := mload(0x40)
            mstore(ptr, G_X)
            mstore(add(ptr, 0x20), G_Y)
            mstore(add(ptr, 0x40), v_q)
            success := staticcall(gas(), PRECOMPILE_MUL, ptr, 0x60, P3, 0x40)
        }}

        assembly ("memory-safe") {{
            let ptr := mload(0x40)
            mstore(ptr, u_g_x)
            mstore(add(ptr, 0x20), u_g_y)
            mstore(add(ptr, 0x40), chall)
            success := staticcall(gas(), PRECOMPILE_MUL, ptr, 0x60, P4, 0x40)
        }}

        uint256[2] memory temp;
        assembly ("memory-safe") {{
            let ptr := mload(0x40)
            mstore(ptr, mload(P1))
            mstore(add(ptr, 0x20), mload(add(P1, 0x20)))
            mstore(add(ptr, 0x40), mload(P2))
            mstore(add(ptr, 0x60), mload(add(P2, 0x20)))
            success := staticcall(gas(), PRECOMPILE_ADD, ptr, 0x80, temp, 0x40)
        }}

        assembly ("memory-safe") {{
            let ptr := mload(0x40)
            mstore(ptr, mload(temp))
            mstore(add(ptr, 0x20), mload(add(temp, 0x20)))
            mstore(add(ptr, 0x40), mload(P3))
            mstore(add(ptr, 0x60), mload(add(P3, 0x20)))
            success := staticcall(gas(), PRECOMPILE_ADD, ptr, 0x80, temp, 0x40)
        }}

        assembly ("memory-safe") {{
            let ptr := mload(0x40)
            mstore(ptr, mload(temp))
            mstore(add(ptr, 0x20), mload(add(temp, 0x20)))
            mstore(add(ptr, 0x40), mload(P4))
            mstore(add(ptr, 0x60), sub(P, mload(add(P4, 0x20)))) // Negate Y-coordinate for subtraction
            success := staticcall(gas(), PRECOMPILE_ADD, ptr, 0x80, P5, 0x40)
        }}

        A_x = P5[0];
        A_y = P5[1];
    }}

    // Compute the RO challenge, this is done by hashing all the available public data up to the evaluation step of the verification process
    // This public data includes T_g (Which is the batch commitment and is a part of the proof, i.e. Proof[2:3]), the public input, and the verification key
    // Dues to stack limitation, the input to Keccak256 is split into two parts
    function comp_chall(
        uint256[2] memory t_g,
        uint256[{input_size}] memory input
    ) public pure returns (uint256) {{
        bytes32 hash = keccak256(
            abi.encodePacked(
                t_g[0],
                t_g[1],
                {input_refs_str}
                G_X,
                G_Y,
                ALPHA_G_X,
                ALPHA_G_Y,
                BETA_G_X,
                BETA_G_Y,
                H_X_0,
                H_X_1,
                H_Y_0,
                H_Y_1,
                DELTA_TWO_H_X_0,
                DELTA_TWO_H_X_1,
                DELTA_TWO_H_Y_0,
                DELTA_TWO_H_Y_1,
                TAU_H_X_0,
                TAU_H_X_1,
                TAU_H_Y_0,
                TAU_H_Y_1
            )
        );


        // Compute challenge
        uint256 chall = uint256(hash) % R;

        return chall;
    }}

    ///////////////////////// The main verification function of Pari ///////////////////////////

    // The verifier for `Circuit1` in `pari/test/Circuit1`
    function Verify(
        uint256[6] calldata proof,
        uint256[{input_size}] calldata input
    ) public view {{
        uint256 chall = comp_chall([proof[2], proof[3]], input);
        (uint256 A_x, uint256 A_y) = compute_A(
            proof[0],
            proof[1],
            comp_vq(input, proof, chall),
            chall,
            proof[4],
            proof[5]
        );

        //////////////////// Pairing  ////////////////////

        bool success;
        uint256 t_g_x = proof[2]; // Fix: Load calldata into memory first
        uint256 t_g_y = proof[3];
        uint256 u_g_x = proof[4]; // Fix: Load calldata into memory first
        uint256 u_g_y = proof[5];

        assembly ("memory-safe") {{
            let memPtr := mload(0x40) // Load free memory pointer

            mstore(add(memPtr, 0x00), t_g_x)
            mstore(add(memPtr, 0x20), t_g_y)
            mstore(add(memPtr, 0x40), DELTA_TWO_H_X_1)
            mstore(add(memPtr, 0x60), DELTA_TWO_H_X_0)
            mstore(add(memPtr, 0x80), DELTA_TWO_H_Y_1)
            mstore(add(memPtr, 0xa0), DELTA_TWO_H_Y_0)

            mstore(add(memPtr, 0xc0), u_g_x)
            mstore(add(memPtr, 0xe0), u_g_y)
            mstore(add(memPtr, 0x100), TAU_H_X_1)
            mstore(add(memPtr, 0x120), TAU_H_X_0)
            mstore(add(memPtr, 0x140), TAU_H_Y_1)
            mstore(add(memPtr, 0x160), TAU_H_Y_0)

            mstore(add(memPtr, 0x180), A_x)
            mstore(add(memPtr, 0x1a0), A_y)
            mstore(add(memPtr, 0x1c0), H_X_1)
            mstore(add(memPtr, 0x1e0), H_X_0)
            mstore(add(memPtr, 0x200), H_Y_1)
            mstore(add(memPtr, 0x220), H_Y_0)

            // Call the BN254 pairing precompile (0x08)
            success := staticcall(
                gas(), // Gas available
                PRECOMPILE_VERIFY, // Precompile address for pairing
                memPtr, // Input memory location
                0x240, // Input size (576 bytes for 3 pairings)
                memPtr, // Store output in the same memory
                0x20 // Output size (32 bytes)
            )
            success := and(success, mload(memPtr))
        }}
        if (!success) {{
            // Either proof or verification key invalid.
            // We assume the contract is correctly generated, so the verification key is valid.
            revert ProofInvalid();
        }}
    }}
}}

    "#,
            input_size = input_size,
            p = self.p.clone().unwrap(),
            q = self.q.clone().unwrap(),
            exp_inv_r = self.q.clone().unwrap() - BigUint::from(2u32),
            neg_h_gi_str = neg_h_gi_str,
            nom_i_str = nom_i_str,
            g_x = vk.g.x().unwrap(),
            g_y = vk.g.y().unwrap(),
            alpha_g_x = vk.alpha_g.x().unwrap(),
            alpha_g_y = vk.alpha_g.y().unwrap(),
            beta_g_x = vk.beta_g.x().unwrap(),
            beta_g_y = vk.beta_g.y().unwrap(),
            h_x_0 = h_x.0,
            h_x_1 = h_x.1,
            h_y_0 = h_y.0,
            h_y_1 = h_y.1,
            delta_h_x_0 = delta_h_x.0,
            delta_h_x_1 = delta_h_x.1,
            delta_h_y_0 = delta_h_y.0,
            delta_h_y_1 = delta_h_y.1,
            tau_h_x_0 = tau_h_x.0,
            tau_h_x_1 = tau_h_x.1,
            tau_h_y_0 = tau_h_y.0,
            tau_h_y_1 = tau_h_y.1,
            minus_coset_offset_to_coset_size =
                self.minus_coset_offset_to_coset_size.clone().unwrap(),
            coset_offset_to_coset_size_inverse =
                self.coset_offset_to_coset_size_inverse.clone().unwrap(),
            coset_size = self.coset_size.clone().unwrap(),
            coset_offset = self.coset_offset.clone().unwrap(),
            // input_processing_vars_str =
            // Self::generate_input_static_code(self.input.as_ref().unwrap().len()),
            input_refs_str = input_refs_str
        );

        let mut file =
            File::create(CONTRACT_PATH.to_owned() + &format!("pari-{}.sol", input_size)).unwrap();
        file.write_all(solidity_code.as_bytes()).unwrap();

        println!("pari.sol file has been generated successfully.");

        let solidity_test_code = format!(
            r#"// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../src/Pari.sol";

contract PariGasTest is Test {{
    Pari verifier;

    function setUp() public {{
        verifier = new Pari();
    }}

    function testGasVerify() public {{
        uint256[6] memory proof = [
            {v_a},
            {v_b},
            {t_g_x},
            {t_g_y},
            {u_g_x},
            {u_g_y}
        ];
        uint256[{input_size}] memory input = [
            {input_str}
        ];

        verifier.Verify(proof, input);
    }}
}}



    "#,
            v_a = self.proof.clone().unwrap().v_a,
            v_b = self.proof.clone().unwrap().v_b,
            t_g_x = self.proof.clone().unwrap().t_1.x().unwrap(),
            t_g_y = self.proof.clone().unwrap().t_1.y().unwrap(),
            u_g_x = self.proof.clone().unwrap().u_1.x().unwrap(),
            u_g_y = self.proof.clone().unwrap().u_1.y().unwrap(),
            input_str = input_str,
            input_size = input_size
        );

        let mut file =
            File::create(CONTRACT_PATH.to_owned() + &format!("pari-{}.t.sol", input_size)).unwrap();
        file.write_all(solidity_test_code.as_bytes()).unwrap();

        println!("pari.t.sol file has been generated successfully.");
    }
}
