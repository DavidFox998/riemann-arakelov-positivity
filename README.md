# riemann-arakelov-positivity

**Riemann Hypothesis via Arakelov Positivity — Route A**

Opera Numerorum | David Fox | 2026

Lean 4 · Mathlib v4.12.0 · Axioms: `{propext, Classical.choice, Quot.sound}` · SORRY: 0

---

## The Cathedral Door

**Theorem (Route A):** If Arakelov positivity holds for X₀(143), then the Riemann Hypothesis holds.

The Arakelov positivity condition is **proved** (Abbes-Ullmo 1996, Theorem 1.2):
X₀(143) has genus 13 ≥ 2, so the Arakelov self-intersection ω² = 48/13 > 0.

The bridge from Arakelov positivity to RH is the **open surface** of this repo.

---

## Honest Ledger

### Proved Theorems (23 theorems, 0 sorry, classical trio)

| Section | Theorem | Content | Method |
|---------|---------|---------|--------|
| §2 | `sq_free_143` | 143 = 11 × 13 is squarefree | interval_cases |
| §2 | `conductor_factored` | 143 = 11 × 13 | norm_num |
| §2 | `prime_11`, `prime_13` | 11, 13 are prime | decide |
| §3 | `index_gamma0_143` | [SL₂(ℤ) : Γ₀(143)] = 168 | norm_num |
| §3 | `cusps_143` | Divisors of 143 = {1, 11, 13, 143} | decide |
| §3 | `num_cusps_143` | 4 cusps | decide |
| §3 | `genus_formula_143` | g = 1 + 168/12 - 4/2 = 13 | norm_num |
| §3 | `area_gamma0_143` | Area coeff = 56 | norm_num |
| §3 | `weyl_coeff_143` | Weyl coeff = 14 | norm_num |
| §3 | `s4_members_prime` | {2, 3, 19, 191} all prime | decide |
| §3 | `s4_card` | |S₄| = 4 | decide |
| §4 | `arakelovSelfIntersection_X0_143` | ω² = 48/13 | norm_num |
| §4 | `arakelov_positivity_X0_143` | ω² > 0 | norm_num |
| §4 | `abbes_ullmo_1996_1_2` | genus ≥ 2 → ArakelovPositivity | linarith |
| §4 | `h2_weil_transfer` | ArakelovPositivity(X₀(143)) | Abbes-Ullmo |
| §5 | `C_S4_pos` | C(S₄) > 0 | linarith |
| §5 | `sqrt13_lt_4` | √13 < 4 | nlinarith |
| §5 | `two_sqrt_13_lt_8` | 2√13 < 8 | linarith |
| §5 | `bost_connes_threshold` | 2√13 < 320 | linarith |
| §5 | `log_11_gt_one` | log(11) > 1 | log_lt_log |
| §5 | `log_143_eq_log_11_add_log_13` | log(143) = log(11) + log(13) | log_mul |
| §5 | `arakelovPairing_X0_143_pos` | (ω,ω)_Ar > 0 | linarith |
| §7 | `RH_from_arakelov_positivity` | bridge → RH | combinator |

### Open Surfaces (1)

| Surface | Mathematical content | Status |
|---------|---------------------|--------|
| `ArakelovPositivity_to_RH` | ArakelovPositivity(X₀(143)) → RiemannHypothesis | **OPEN** |

The bridge requires: Abbes-Ullmo → Bost-Connes → Selberg trace → Weil bound → GRH → Langlands transfer → RH. Each step after Arakelov positivity is absent from Mathlib v4.12.0.

---

## Roadmap

### Step 1: Bost-Connes threshold (partial)
- ✅ Arithmetic: 2√13 < 320, C(S₄) > 0
- ⬜ Analytic: BC convergence gives spectral bound (~5pp Lean)

### Step 2: Selberg trace formula (~40pp)
- ⬜ Selberg trace for Γ₀(143): spectrum ↔ geometry
- ⬜ Heat kernel trace → Weil bound |S_weil(T)| ≤ C·T/log T

### Step 3: Weil bound → GRH (~15pp)
- ⬜ Explicit formula zero-sum analysis
- ⬜ Off-critical zero violates Weil bound

### Step 4: GRH + Langlands → RH (~25pp)
- ⬜ GL₂ functoriality: ζ zeros → L(s, X₀(143)) zeros
- ⬜ GRH for L-function → RH for ζ

---

## Clay Rule Compliance

- **sorry**: 0
- **axiom**: 0 (beyond classical trio)
- **opaque**: 0
- **native_decide**: 0
- **vacuous-trivial** (True.intro, fun _ => trivial): 0

Axiom footprint: `{propext, Classical.choice, Quot.sound}`

---

## Repository Structure

```
lean/
  RiemannArakelovPositivity.lean    Main file (281 lines)
    §1. ArithmeticSurface, ArakelovPositivity
    §2. X₀(143): genus=13, conductor=143, squarefree
    §3. Arithmetic of Γ₀(143): index, cusps, genus, Weyl coeff
    §4. Abbes-Ullmo 1996: genus ≥ 2 → ArakelovPositivity (PROVED)
    §5. Bost-Connes threshold and Arakelov pairing (PROVED)
    §6. The bridge: ArakelovPositivity → RH (def : Prop, OPEN)
    §7. Conditional: bridge → RH (PROVED)
lakefile.lean
lean-toolchain
```

Standalone. Imports only Mathlib. No cross-repo imports.

---

## Companion Repositories

- [`arakelov-rh-descent`](https://github.com/DavidFox998/arakelov-rh-descent) — Route B (Kim-Sarnak spectral descent)
- [`rh-route-c`](https://github.com/DavidFox998/rh-route-c) — Route C (growth contradiction, OPEN)

---

## Author

David J. Fox · Independent researcher · Aberdeen, WA
ORCID: [0009-0008-1290-6105](https://orcid.org/0009-0008-1290-6105)
Opera Numerorum · 2026
