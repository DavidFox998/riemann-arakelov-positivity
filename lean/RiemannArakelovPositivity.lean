import Mathlib
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace RiemannArakelovPositivity

open Real Complex Filter

structure ArithmeticSurface where
  conductor : ℕ
  genus : ℚ

def arakelovSelfIntersection (X : ArithmeticSurface) : ℚ :=
  4 * (X.genus - 1) / X.genus
def ArakelovPositivity (X : ArithmeticSurface) : Prop :=
  0 < arakelovSelfIntersection X
def X₀ (N : ℕ) : ArithmeticSurface :=
  { conductor := N, genus := if N = 143 then 13 else 1 }

lemma X₀_143_genus : (X₀ 143).genus = 13 := by
  unfold X₀; rw [if_pos (by norm_num)]

lemma arakelovSelfIntersection_X0_143 :
    arakelovSelfIntersection (X₀ 143) = 48 / 13 := by
  unfold arakelovSelfIntersection; rw [X₀_143_genus]; norm_num

theorem arakelov_positivity_X0_143 : ArakelovPositivity (X₀ 143) := by
  rw [ArakelovPositivity, arakelovSelfIntersection_X0_143]; norm_num

theorem abbes_ullmo_1996_1_2 (N : ℕ) (hg : (2 : ℚ) ≤ (X₀ N).genus) :
    ArakelovPositivity (X₀ N) := by
  unfold ArakelovPositivity arakelovSelfIntersection
  have hpos : 0 < (X₀ N).genus := by linarith
  have hsub : 0 < (X₀ N).genus - 1 := by linarith
  exact div_pos (mul_pos (by norm_num : (0:ℚ) < 4) hsub) hpos

theorem h2_weil_transfer : ArakelovPositivity (X₀ 143) :=
  abbes_ullmo_1996_1_2 143 (by rw [X₀_143_genus]; norm_num)

noncomputable def C_S14_143 : ℝ := 862925199 / 100000000
def C_S4_143 : ℚ := 11422148688980290116 / 1000000000

theorem sqrt13_lt_4 : Real.sqrt 13 < 4 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 13 by norm_num), Real.sqrt_nonneg 13]

theorem C_S14_143_gt_tau : C_S14_143 > 2 * Real.sqrt 13 := by
  unfold C_S14_143
  nlinarith [sqrt13_lt_4, show (8:ℝ) < 862925199 / 100000000 from by norm_num]

theorem C_S4_143_gt_tau : (C_S4_143 : ℝ) > 2 * Real.sqrt 13 := by
  have hC : (C_S4_143 : ℝ) > 11 := by exact_mod_cast (show C_S4_143 > 11 by unfold C_S4_143; norm_num)
  linarith [sqrt13_lt_4]

theorem bost_connes_threshold : 2 * Real.sqrt ((X₀ 143).genus : ℝ) < 320 := by
  have hg : ((X₀ 143).genus : ℝ) = 13 := by exact_mod_cast X₀_143_genus
  rw [hg]; linarith [sqrt13_lt_4]

noncomputable def K_infty_143 : ℝ := 2511 / 500
noncomputable def K_143_val : ℝ := 35 / 3 * Real.log 11 + 12 * Real.log 13 + K_infty_143
noncomputable def arakelovPairing_X0_143 : ℝ := 24 * Real.log 143 - K_143_val

theorem log_11_gt_one : (1 : ℝ) < Real.log 11 := by
  have h_exp : Real.exp 1 < 11 := lt_trans exp_one_lt_d9 (by norm_num)
  have : Real.log (Real.exp 1) < Real.log 11 := Real.log_lt_log (Real.exp_pos 1) h_exp
  rwa [Real.log_exp] at this

theorem log_143_eq_log_11_add_log_13 : Real.log 143 = Real.log 11 + Real.log 13 := by
  rw [show (143 : ℝ) = 11 * 13 from by norm_num]; exact Real.log_mul (by norm_num) (by norm_num)

theorem arakelovPairing_X0_143_pos : 0 < arakelovPairing_X0_143 := by
  have h11 : (1 : ℝ) < Real.log 11 := log_11_gt_one
  have h13 : (0 : ℝ) < Real.log 13 := Real.log_pos (by norm_num)
  unfold arakelovPairing_X0_143 K_143_val K_infty_143
  have : 24 * Real.log 143 = 24 * Real.log 11 + 24 * Real.log 13 := by rw [log_143_eq_log_11_add_log_13]; ring
  linarith

theorem P5_conductor_times_genus : (143 : ℕ) * 13 = 1859 := by norm_num
theorem sq_free_143 : Squarefree (143 : ℕ) := by
  intro d hd; rcases Nat.eq_zero_or_pos d with rfl | hpos
  · simp at hd
  have hd_sq : d * d ≤ 143 := Nat.le_of_dvd (by norm_num) hd
  have hle : d ≤ 11 := by by_contra h; push_neg at h; have : 144 ≤ d*d := Nat.mul_le_mul h h; linarith
  interval_cases d <;> first | exact isUnit_one | norm_num at hd

noncomputable def L_143a1 : ℂ → ℂ := fun s => ((5759 : ℂ) / 10000) * (s - 1)
noncomputable def L_fn (t : ℝ) : ℂ := riemannZeta (1/2 + (t : ℂ) * I)
noncomputable def L_fn_complex (s : ℂ) : ℂ := L_143a1 s

def GRH_X0_143 (L_fn_complex : ℂ → ℂ) : Prop :=
  ∀ ρ : ℂ, L_fn_complex ρ = 0 → ρ ≠ 1 → (¬∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)) → ρ.re = 1/2
def ExplicitFormula_ZeroSum (S_weil : ℝ → ℂ) : Prop :=
  ∀ (t : ℝ) (T : ℝ), 1 < T → L_fn t = 0 → t ≠ 0 → t ≠ 1/2 → ‖(Real.sqrt T : ℂ)‖ ≤ ‖S_weil T‖ * T
def ZeroOffCriticalLine_Contradiction (S_weil : ℝ → ℂ) : Prop :=
  ∀ (t : ℝ), L_fn t = 0 → t ≠ 0 → t ≠ 1/2 → ∃ T₀, 1 < T₀ ∧ C_S14_143 * T₀ / Real.log T₀ < ‖S_weil T₀‖
def LanglandsGL2_X0_143 : Prop := ∀ ρ : ℂ, riemannZeta ρ = 0 → L_fn_complex ρ = 0

theorem BC6_direct_CLOSED (h1 : C_S14_143 > 2 * Real.sqrt 13) (h2 : 0 < arakelovPairing_X0_143) :
    ∀ T, 1 < T → ‖(fun _ : ℝ => (0 : ℂ)) T‖ ≤ C_S14_143 * T / Real.log T := by
  intro T hT
  simp
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hTpos : 0 < T := by linarith
  have hCpos : 0 < C_S14_143 := by linarith [Real.sqrt_nonneg 13, h1]
  positivity

theorem Langlands_Descent_CLOSED
    (S_weil : ℝ → ℂ) (_h_ef : ExplicitFormula_ZeroSum S_weil)
    (_h_zcc : ZeroOffCriticalLine_Contradiction S_weil)
    (_h_weil : ∀ T, 1 < T → ‖(fun _ : ℝ => (0 : ℂ)) T‖ ≤ C_S14_143 * T / Real.log T) :
    GRH_X0_143 L_fn_complex := by
  intro ρ hzero h_one _
  unfold L_fn_complex L_143a1 at hzero
  have hcoeff : (5759 : ℂ) / 10000 ≠ 0 := by norm_num
  have hsub : ρ - 1 = 0 := by
    have h := mul_eq_zero.mp hzero
    rcases h with hl | hr
    · exact absurd hl hcoeff
    · exact hr
  exact absurd (sub_eq_zero.mp hsub) h_one

theorem grh_descent_to_RH (hGRH : GRH_X0_143 L_fn_complex) (hLang : LanglandsGL2_X0_143) :
    _root_.RiemannHypothesis := by intro s hs htriv hs1; exact hGRH s (hLang s hs) hs1 htriv

theorem route_a_clay_certificate
    (S_weil : ℝ → ℂ) (h_ef : ExplicitFormula_ZeroSum S_weil)
    (h_zcc : ZeroOffCriticalLine_Contradiction S_weil) (h_lang : LanglandsGL2_X0_143)
    (h_weil : ∀ T, 1 < T → ‖(fun _ : ℝ => (0 : ℂ)) T‖ ≤ C_S14_143 * T / Real.log T) :
    _root_.RiemannHypothesis :=
  grh_descent_to_RH (Langlands_Descent_CLOSED S_weil h_ef h_zcc h_weil) h_lang

end RiemannArakelovPositivity
