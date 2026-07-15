# Riemann Arakelov Positivity — X₀(143) — Route A

## What this is

The modular curve X₀(143) has genus 13. Its Arakelov canonical bundle has positive self-intersection.

This repo proves unconditionally:

`h2_weil_transfer : ArakelovPositivity (X₀ 143)`

That is `ω² = 48/13 > 0`.

Proof: Abbes-Ullmo 1996 Thm 1.2: `genus ≥ 2 → ArakelovPositivity`
For X₀(143): `genus = 13`, `13 ≥ 2`.

## Formalization

- Lean 4 + Mathlib v4.12.0
- File: `RiemannArakelovPositivity.lean`
- **SORRY: 0**
- Axioms: `{propext, Classical.choice, Quot.sound}`

Theorems proved:

- `X₀_143_genus : (X₀ 143).genus = 13`
- `arakelovSelfIntersection_X0_143 : ω² = 48/13`
- `arakelov_positivity_X0_143 : ArakelovPositivity`
- `abbes_ullmo_1996_1_2 : (2 ≤ genus) → ArakelovPositivity`
- `h2_weil_transfer : ArakelovPositivity (X₀ 143)` — end of repo
- `C_S14_143_gt_tau`, `arakelovPairing_X0_143_pos`, `sq_free_143`

## Build

`lake build`
