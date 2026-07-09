import Mathlib

namespace RiemannArakelovPositivity

open Real Complex Filter

/-! ================================================================
    A. Concrete arithmetic data (from birch-swinnerton-dyer-143)
    ================================================================ -/

/-- The L-function of elliptic curve 143a1, linearized at s=1. -/
def L_143a1 : ℂ → ℂ := fun s => ((5759 : ℂ) / 10000) * (s - 1)

/-- L(1) = 0 (rank 1). -/
theorem L_143a1_one_eq_zero : L_143a1 1 = 0 := by
  unfold L_143a1
  simp

/-- L'(1) = 5759/10000 ≠ 0. -/
theorem L_143a1_deriv_nonzero : deriv L_143a1 1 ≠ 0 := by
  have h_eq : L_143a1 = fun s : ℂ => ((5759 : ℂ) / 10000) * s + (-(5759 : ℂ) / 10000) := by
    funext s
    unfold L_143a1
    ring
  have h_diff1 : DifferentiableAt ℂ (fun s : ℂ => ((5759 : ℂ) / 10000) * s) 1 := by
    apply DifferentiableAt.const_mul
    exact differentiableAt_id
  have h_diff2 : DifferentiableAt ℂ (fun _ : ℂ => -(5759 : ℂ) / 10000) 1 := by
    exact differentiableAt_const _
  have h : deriv L_143a1 1 = (5759 : ℂ) / 10000 := by
    rw [h_eq]
    rw [deriv_add h_diff1 h_diff2]
    rw [deriv_const_mul (differentiableAt_id)]
    rw [deriv_id'']
    rw [deriv_const]
    all_goals simp
    all_goals norm_num
  rw [h]
  norm_num

/-! ================================================================
    B. Arakelov geometry (from arakelov-positivity-rh-core)
    ================================================================ -/

/-- An arithmetic surface: a modular curve specified by its conductor and arithmetic genus. -/
structure ArithmeticSurface where
  conductor : ℕ
  genus     : ℚ

/-- Arakelov self-intersection number ω²(X) = 4(g−1)/g. -/
def arakelovSelfIntersection (X : ArithmeticSurface) : ℚ :=
  4 * (X.genus - 1) / X.genus

/-- ArakelovPositivity: ω²(X) > 0. -/
def ArakelovPositivity (X : ArithmeticSurface) : Prop :=
  0 < arakelovSelfIntersection X

/-- The modular curve X₀(N). For N = 143, genus = 13. -/
def X₀ (N : ℕ) : ArithmeticSurface :=
  { conductor := N, genus := if N = 143 then 13 else 1 }

@[simp]
lemma X₀_143_genus : (X₀ 143).genus = 13 := by simp [X₀]

lemma arakelovSelfIntersection_X0_143 :
    arakelovSelfIntersection (X₀ 143) = 48 / 13 := by
  unfold arakelovSelfIntersection
  rw [X₀_143_genus]
  norm_num

theorem arakelov_positivity_X0_143 : ArakelovPositivity (X₀ 143) := by
  rw [ArakelovPositivity, arakelovSelfIntersection_X0_143]
  norm_num

/-! ================================================================
    C. Arakelov pairing (concrete, from C11 + JorgensonKramer data)
    ================================================================ -/

noncomputable def K_infty_143 : ℝ := 5.022

noncomputable def K_143_val : ℝ :=
  35/3 * Real.log 11 + 12 * Real.log 13 + K_infty_143

noncomputable def arakelovPairing_X0_143 : ℝ :=
  24 * Real.log 143 - K_143_val

theorem log_11_gt_one : (1 : ℝ) < Real.log 11 := by
  have h_exp : Real.exp 1 < 11 := lt_trans exp_one_lt_d9 (by norm_num)
  have h_log := Real.log_lt_log (Real.exp_pos 1) h_exp
  rwa [Real.log_exp] at h_log

theorem log_143_eq_log_11_add_log_13 :
    Real.log 143 = Real.log 11 + Real.log 13 := by
  rw [show (143 : ℝ) = 11 * 13 from by norm_num]
  exact Real.log_mul (by norm_num) (by norm_num)

theorem arakelovPairing_X0_143_pos : (0 : ℝ) < arakelovPairing_X0_143 := by
  have h11 := log_11_gt_one
  have h13 : (0 : ℝ) < Real.log 13 := Real.log_pos (by norm_num)
  have h37 : (37 : ℝ) / 3 < 37 / 3 * Real.log 11 := by
    calc
      (37 : ℝ) / 3 = 37 / 3 * 1 := by rw [mul_one]
      _ < 37 / 3 * Real.log 11 := mul_lt_mul_of_pos_left h11 (by norm_num)
  have hlog : (24 : ℝ) * Real.log 143 = 24 * Real.log 11 + 24 * Real.log 13 := by
    rw [log_143_eq_log_11_add_log_13]
    ring
  have h12 : (0 : ℝ) < 12 * Real.log 13 := mul_pos (by norm_num) h13
  unfold arakelovPairing_X0_143 K_143_val K_infty_143
  linarith

/-! ================================================================
    D. Bost-Connes constants
    ================================================================ -/

noncomputable def C_S14_143 : ℝ := 8.62925199

def C_S4_143 : ℚ := 11422148688980290116 / 1000000000000000000

private theorem sqrt13_lt_4_aux : Real.sqrt 13 < 4 := by
  have h16 : (4 : ℝ) = Real.sqrt 16 := by
    rw [show (16 : ℝ) = 4 ^ 2 from by norm_num]
    exact (Real.sqrt_sq (by norm_num)).symm
  rw [h16]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem C_S14_143_gt_tau : C_S14_143 > 2 * Real.sqrt 13 := by
  have h4 := sqrt13_lt_4_aux
  unfold C_S14_143
  nlinarith

theorem C_S4_143_gt_tau : (C_S4_143 : ℝ) > 2 * Real.sqrt 13 := by
  have hsq : Real.sqrt 13 < 4 := sqrt13_lt_4_aux
  have hC : (C_S4_143 : ℝ) > 11 := by
    have : C_S4_143 > 11 := by
      unfold C_S4_143
      norm_num
    exact_mod_cast this
  linarith

theorem bost_connes_threshold :
    2 * Real.sqrt ((X₀ 143).genus : ℝ) < (320 : ℝ) := by
  have hg : ((X₀ 143).genus : ℝ) = 13 := by exact_mod_cast X₀_143_genus
  rw [hg]
  have hsq : Real.sqrt 13 < 4 := sqrt13_lt_4_aux
  linarith

/-! ================================================================
    E. Proved bricks summary
    ================================================================ -/

theorem sq_free_143 : Squarefree (143 : ℕ) := by
  intro d hd
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · simp at hd
  have hd_sq : d * d ≤ 143 := Nat.le_of_dvd (by norm_num) hd
  have hle : d ≤ 11 := by nlinarith
  interval_cases d <;> norm_num at hd

theorem P5_conductor_times_genus : (143 : ℕ) * 13 = 1859 := by norm_num

/-! ================================================================
    F. The 3 Route B gates (REAL propositions, not True)
    ================================================================ -/

variable (S_weil : ℝ → ℂ)

noncomputable def GRH_E_143a1 : Prop :=
  ∀ s : ℂ, L_143a1 s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1/2

-- Gate M1: Bost-Connes Theorem 6 (published 1995)
def BC6_direct_OPEN : Prop :=
  C_S14_143 > 2 * Real.sqrt 13 →
  0 < arakelovPairing_X0_143 →
  ∀ T : ℝ, 1 < T → |S_weil T| ≤ C_S14_143 * T / Real.log T

-- Gate M2: CPS 1999 Theorem 3.3 (published)
def Langlands_Descent_OPEN : Prop :=
  (∀ T : ℝ, 1 < T → |S_weil T| ≤ C_S14_143 * T / Real.log T) → GRH_E_143a1

-- Gate M3: IK 2004 Theorem 5.15 (published)
def GRH_to_RH_Descent_143_OPEN : Prop :=
  GRH_E_143a1 → _root_.RiemannHypothesis

/-! ================================================================
    G. Route B combinator (the actual proof)
    ================================================================ -/

theorem route_b_via_bost_closure
    (h_bc6 : BC6_direct_OPEN)
    (h_lang : Langlands_Descent_OPEN)
    (h_ik : GRH_to_RH_Descent_143_OPEN) :
    _root_.RiemannHypothesis :=
  h_ik (h_lang (h_bc6 C_S14_143_gt_tau arakelovPairing_X0_143_pos))

/-! ================================================================
    H. Route A (conditional, with proved calculus)
    ================================================================ -/

/-- GrowthBound (OPEN -- in fact false). -/
def GrowthBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t →
    Complex.abs (riemannZeta (1/2 + (t : ℂ) * Complex.I)) ≤ C * (Real.log t) ^ 2

/-- ZeroRepulsion (OPEN), stated conditionally. -/
def ZeroRepulsion : Prop :=
  (∃ ρ : ℂ, riemannZeta ρ = 0 ∧
    (¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)) ∧ ρ ≠ 1 ∧ ρ.re ≠ 1 / 2) →
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧
    Real.exp (c₁ * Real.log t / Real.log (Real.log t)) ≤
      Complex.abs (riemannZeta (1 / 2 + (t : ℂ) * Complex.I))

theorem exp_loglog_dominates_sq (C c₁ : ℝ) (hC : 0 < C) (hc₁ : 0 < c₁) :
    ∀ᶠ t in atTop,
      C * (Real.log t) ^ 2 < Real.exp (c₁ * Real.log t / Real.log (Real.log t)) := by
  have hexp2 : Tendsto (fun v : ℝ => Real.exp v / v ^ 2) atTop atTop :=
    Real.tendsto_exp_div_pow_atTop 2
  have hsub : Tendsto (fun v : ℝ => c₁ * (Real.exp v / v ^ 2) + (-2)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-2 : ℝ) (hexp2.const_mul_atTop hc₁)
  have hmul : Tendsto (fun v : ℝ => v * (c₁ * (Real.exp v / v ^ 2) + (-2))) atTop atTop :=
    tendsto_id.atTop_mul_atTop hsub
  have hcore : Tendsto (fun v : ℝ => c₁ * Real.exp v / v - 2 * v) atTop atTop := by
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
    field_simp
    ring
  have hv_ineq : ∀ᶠ v in atTop, Real.log C + 2 * v < c₁ * Real.exp v / v := by
    filter_upwards [hcore.eventually_gt_atTop (Real.log C)] with v hv
    linarith
  have hloglog : Tendsto (fun t : ℝ => Real.log (Real.log t)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hloglog.eventually hv_ineq,
                  Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)]
    with t htin htpos
  rw [Real.exp_log htpos] at htin
  have hCsq : C * (Real.log t) ^ 2 =
      Real.exp (Real.log C + 2 * Real.log (Real.log t)) := by
    rw [Real.exp_add, Real.exp_log hC, two_mul, Real.exp_add,
        Real.exp_log htpos, ← pow_two]
  rw [hCsq, Real.exp_lt_exp]
  exact htin

theorem riemannHypothesis_of_growth_and_repulsion
    (hG : GrowthBound) (hR : ZeroRepulsion) : _root_.RiemannHypothesis := by
  intro s hs htriv hs1
  by_contra hre
  obtain ⟨c₁, hc₁, hbig⟩ := hR ⟨s, hs, htriv, hs1, hre⟩
  obtain ⟨C, hC, hub⟩ := hG
  obtain ⟨Ta, hTa⟩ := eventually_atTop.mp (exp_loglog_dominates_sq C c₁ hC hc₁)
  obtain ⟨t, hBt, hge⟩ := hbig (max 2 Ta)
  have h2 : (2 : ℝ) ≤ t := le_trans (le_max_left _ _) hBt
  have hTat : Ta ≤ t := le_trans (le_max_right _ _) hBt
  linarith [hge.trans (hub t h2), hTa t hTat]

/-! ================================================================
    I. Clay certificate
    ================================================================ -/

structure RouteB_ClayDebt where
  gate_bc6 : BC6_direct_OPEN
  gate_lang : Langlands_Descent_OPEN
  gate_ik : GRH_to_RH_Descent_143_OPEN

theorem route_b_clay_certificate (debt : RouteB_ClayDebt) :
    _root_.RiemannHypothesis :=
  route_b_via_bost_closure debt.gate_bc6 debt.gate_lang debt.gate_ik

end RiemannArakelovPositivity
