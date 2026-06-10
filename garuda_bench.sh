#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT_DIR"

commands=(
  # "RAYON_NUM_THREADS=1 cargo bench --bench aadhaar-spartan --features \"r1cs\""
  # "RAYON_NUM_THREADS=1 cargo bench --bench aadhaar-groth16 --features \"r1cs\""
  # "RAYON_NUM_THREADS=1 cargo bench --bench aadhaar-garuda --features \"r1cs\""

  # "RAYON_NUM_THREADS=1 cargo bench --bench aptos-groth16 --features \"r1cs\""
  # "RAYON_NUM_THREADS=1 cargo bench --bench aptos-spartan --features \"r1cs\""
  # "RAYON_NUM_THREADS=1 cargo bench --bench aptos-garuda --features \"r1cs\""

  # "RAYON_NUM_THREADS=1 cargo bench --bench rescue-garuda  --features \"gr1cs\" -- --gr1cs"

  # "RAYON_NUM_THREADS=1 cargo bench --bench rescue-hyperplonk --features \"gr1cs\""


  # "RAYON_NUM_THREADS=1 cargo bench --bench rescue-groth16 --features \"r1cs\""
  # "RAYON_NUM_THREADS=1 cargo bench --bench rescue-garuda  --features \"r1cs\" -- --r1cs"


  "RAYON_NUM_THREADS=1 cargo bench --bench random-garuda --features \"r1cs\""
  # "RAYON_NUM_THREADS=1 cargo bench --bench random-garuda-gr1cs --features \"gr1cs\""
  # "RAYON_NUM_THREADS=1 cargo bench --bench random-garuda-addition --features \"r1cs\""
  # "RAYON_NUM_THREADS=1 cargo bench --bench random-garuda-gr1cs-addition --features \"gr1cs\""
  # "RAYON_NUM_THREADS=1 cargo bench --bench random-groth16-addition --features \"r1cs\""
  "RAYON_NUM_THREADS=1 cargo bench --bench random-groth16 --features \"r1cs\""
  # "RAYON_NUM_THREADS=1 cargo bench --bench rescue-spartan-nizk  --features \"gr1cs\" -- --gr1cs"
  # "RAYON_NUM_THREADS=1 cargo bench --bench rescue-spartan-nizk  --features \"r1cs\" -- --r1cs"
  "RAYON_NUM_THREADS=1 cargo bench --bench random-spartan --features \"r1cs\""
  # "RAYON_NUM_THREADS=1 cargo bench --bench random-spartan-ccs --features \"gr1cs\""
  # "RAYON_NUM_THREADS=1 cargo bench --bench random-spartan-ccs-addition --features \"gr1cs\""
  # "RAYON_NUM_THREADS=1 cargo bench --bench random-spartan-addition --features \"r1cs\""



)

for cmd in "${commands[@]}"; do
  echo "$cmd"
  eval "$cmd"
done
