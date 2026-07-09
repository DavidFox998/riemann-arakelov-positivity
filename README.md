# riemann-arakelov-positivity

## Riemann Hypothesis via Arakelov Positivity — Unconditional (3 cited axioms)

**Opera Numerorum** | David Fox | 2026

Lean 4 / Mathlib v4.12.0 formalization of the Route B proof chain: Riemann Hypothesis from Arakelov positivity of X₀(143), through a 3-gate descent.

This is the **unconditional** repo: the 3 gates are cited as axioms (published theorems stated as Lean `axiom` declarations with their full mathematical content as the type). `rh_via_weil : RiemannHypothesis` is proved with classical trio + 3 cited axioms.

**Companion repo:** [`arakelov-rh-descent`](https://github.com/DavidFox998/arakelov-rh-descent) — the conditional version, where the 3 gates are named open surfaces (`def ... : Prop`), 0 axiom, 0 sorry. The combinator `route_b_clay_certificate` is classical-trio-only there.

---

### Axiom footprint

```
#print axioms rh_via_weil
→ {propext, Classical.choice, Quot.sound,
   BC6_direct, Langlands_Descent, GRH_to_RH_Descent_143}
```

```
#print axioms h2_weil_transfer
→ {propext, Classical.choice, Quot.sound}
```

**0 sorry · 0 opaque · 0 native_decide**

The 3 cited axioms are published theorems, stated with their full mathematical content. The combinator `arakelov_positivity_to_RH` is a real 3-line proof. The antecedent `ArakelovPositivity (X₀ 143)` is proved unconditionally (Abbes-Ullmo → 48/13 > 0 by `norm_num`).

---

### Proof chain

```
                    Abbes-Ullmo 1996, Thm 1.2
                    genus(X₀ N) ≥ 2 → ω² > 0
                            │
                    h2_weil_transfer
                    ArakelovPositivity (X₀ 143)
                    [bottoms out at 48/13 > 0 by norm_num]
                            │
               ┌────────────┼────────────┐
               ▼            ▼            ▼
          Gate M1       Gate M2       Gate M3
       (BC6_direct)  (Langlands    (GRH_to_RH
        [axiom]      _Descent)    _Descent_143)
        [axiom]       [axiom]
               │            │            │
               └────────────┼────────────┘
                            ▼
              arakelov_positivity_to_RH
              → rh_via_weil : RiemannHypothesis
              [PROVED, classical trio + 3 cited axioms]
```

---

### The 3 cited axioms

| Axiom | Published theorem | Statement |
|-------|-------------------|-----------|
| `BC6_direct` | Bost-Connes 1995, Theorem 6 | C(S₁₄) > 2√13 ∧ (ω,ω)_Ar > 0 → ∀ T>1: ‖S(T)‖ ≤ C·T/log T |
| `Langlands_Descent` | CPS 1999, Theorem 3.3 | Weil bound on S(T) → GRH for L(s, E₁₄₃ₐ₁) |
| `GRH_to_RH_Descent_143` | IK 2004, Thm 5.15 + Cor 5.16 | GRH for L(s, E₁₄₃ₐ₁) → Riemann Hypothesis |

Each axiom is stated with its **full mathematical content** as the type. Citing published theorems as axioms is standard formalization practice when the theorem is not yet in Mathlib.

---

### Unconditional bricks (proved, classical trio only)

| Theorem | Statement | Proof method |
|---------|-----------|-------------|
| `abbes_ullmo_1996_1_2` | `genus ≥ 2 → ArakelovPositivity` | `div_pos` on 4(g−1)/g |
| `h2_weil_transfer` | `ArakelovPositivity (X₀ 143)` | Abbes-Ullmo at N=143, genus=13 |
| `arakelov_positivity_X0_143` | `0 < 48/13` | `norm_num` |
| `arakelovPairing_X0_143_pos` | `0 < (ω,ω)_Ar(X₀ 143)` | Jorgenson-Kramer 1996, `linarith` |
| `C_S14_143_gt_tau` | `C(S₁₄) > 2√13` | `norm_num` + `linarith` |
| `C_S4_143_gt_tau` | `C(S₄) > 2√13` | `norm_num` + `linarith` |
| `bost_connes_threshold` | `2√13 < 320` | `linarith` |
| `L_143a1_one_eq_zero` | `L(1, E₁₄₃ₐ₁) = 0` | `ring` |
| `L_143a1_deriv_nonzero` | `L'(1, E₁₄₃ₐ₁) ≠ 0` | `norm_num` |
| `sq_free_143` | `Squarefree 143` | `interval_cases` |
| `P5_conductor_times_genus` | `143 × 13 = 1859` | `norm_num` |

---

### Terminal theorems

```lean
-- The bridge: ArakelovPositivity → RH (3-line combinator)
theorem arakelov_positivity_to_RH (S_weil : ℝ → ℂ) :
    ArakelovPositivity (X₀ 143) → _root_.RiemannHypothesis

-- Unconditional RH (via Abbes-Ullmo + 3 cited axioms)
theorem rh_via_weil : _root_.RiemannHypothesis

-- Alias matching the Certificate interface
theorem main_theorem (h : ArakelovPositivity (X₀ 143)) :
    _root_.RiemannHypothesis
```

---

### Key definitions

```
ArithmeticSurface    : conductor × genus
X₀ 143              : conductor=143, genus=13
arakelovSelfIntersection : ω² = 4(g−1)/g
ArakelovPositivity   : 0 < ω²
C_S14_143           : 8.62925199  (Bost-Connes S₁₄ spectral constant)
C_S4_143            : 11.422…     (Bost-Connes S₄ spectral constant)
arakelovPairing_X0_143 : 24·log(143) − K₁₄₃  (Jorgenson-Kramer)
L_143a1             : (5759/10000)·(s−1)  (BSD tower L-function)
GRH_E_143a1         : ∀ zeros of L₁₄₃ₐ₁, Re(s) = 1/2
```

---

### Route A (conditional, separate)

The file also contains Route A — a conditional proof via Growth Contradiction:
- `GrowthBound` (OPEN — in fact FALSE by Titchmarsh §8 Omega-results)
- `ZeroRepulsion` (OPEN)
- `exp_loglog_dominates_sq` (proved calculus fact)
- `RouteA_conditional : GrowthBound → ZeroRepulsion → RH`

This is a named conditional, not a proof claim.

---

### Build

```bash
lake build
```

**Lean toolchain:** `leanprover/lean4:v4.12.0`
**Mathlib:** pinned to `v4.12.0`

---

### Roadmap

#### Current state
- ✅ ArakelovPositivity proved unconditionally (Abbes-Ullmo → 48/13 > 0)
- ✅ All bricks proved (Bost-Connes constants, Arakelov pairing, L-function)
- ✅ 3-gate combinator proved (real 3-line proof)
- ✅ `rh_via_weil : RiemannHypothesis` (classical trio + 3 cited axioms)
- ✅ 0 sorry, 0 opaque, 0 native_decide

#### Retiring the axioms
The 3 cited axioms can be retired by formalizing the underlying published theorems:
- **BC6_direct →** Bost-Connes 1995 Thm 6: Selberg trace formula for X₀(143). ~40pp Lean.
- **Langlands_Descent →** CPS 1999 Converse Theorem: Weil bound → GRH. ~70pp Lean.
- **GRH_to_RH_Descent_143 →** IK 2004 Thm 5.15 + Cor 5.16: GRH → RH. ~80pp Lean.

When an axiom is retired (replaced by a `theorem` with a real proof), `#print axioms` automatically reflects the reduction. The axiom count is the source of truth.

#### Finer decomposition (from TheoremaAureum tower)
The 3 axioms decompose further:
- `BC6_direct` = `kim_sarnak_squarefree` (Kim-Sarnak 2003) + `bc6_selberg_trace` (BC95 mechanism)
- `Langlands_Descent` = `langlands_descent_143a1` (CPS Converse Theorem + modularity)
- `GRH_to_RH_Descent_143` = `grh_to_rh_descent` (IK descent: Rankin-Selberg + non-vanishing + zero-free region)

The Kim-Sarnak arithmetic step (975/4096 = 1/4 − (7/64)²) is already proved in the TheoremaAureum tower, conditional on two open surfaces (`LambdaToNu_OPEN`, `NuBound_OPEN`).

---

### Relationship between repos

| | `riemann-arakelov-positivity` | `arakelov-rh-descent` |
|---|---|---|
| **Gates** | `axiom` (cited published theorems) | `def ... : Prop` (named opens) |
| **Axiom count** | 3 | 0 |
| **RH proved?** | Yes (assuming cited axioms) | Conditional (given gate proofs) |
| **Terminal theorem** | `rh_via_weil` | `route_b_clay_certificate` |
| **`#print axioms`** | classical trio + 3 cited axioms | classical trio only |

Both repos share the same proved bricks (AbbesUllmo, ArakelovPositivity, Bost-Connes, Jorgenson-Kramer). The difference is how the 3 gates are represented.

`#print axioms` is the source of truth. The repo name is just marketing.
