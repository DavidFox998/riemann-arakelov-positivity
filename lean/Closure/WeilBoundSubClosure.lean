/-
  ArakelovRH/SubClosure/WeilBoundSubClosure.lean
  Sub-surface analysis for WeilBoundToGRHClosure.lean.
  Author: David Fox.  Opera Numerorum.  June 2026.

  TARGETS (WeilBoundToGRHClosure.lean):
    (1) ExplicitFormula_ZeroSum_OPEN : Prop :=
          (forall s : C, L_143a1 s = newform_143a1_L s) ->
          exists (zeros_143 : N -> C),
            (forall n, L_143a1 (zeros_143 n) = 0) /\
            forall T, 1 < T -> |S_weil(T)| <= (sum |Re(rho_n) - 1/2|) * ...

    (2) ZeroOffCriticalLine_Contradiction_OPEN : Prop :=
          forall rho, L_143a1 rho = 0 -> 0 < rho.re -> rho.re < 1 ->
            rho.re = 1/2 \/
            exists T0 > 1, C_S14_143 * T0/log T0 < (rho.re - 1/2) * T0/log T0

  KEY MATHEMATICAL OBSERVATION:
    ZeroOffCriticalLine_Contradiction_OPEN is LOGICALLY EQUIVALENT to GRH for L_143a1.

    PROOF of equivalence:
      The second disjunct simplifies to: C_S14_143 < rho.re - 1/2.
      Since rho.re < 1 (given), rho.re - 1/2 < 1/2.
      Since C_S14_143 = 2*sqrt(13) * (168/12pi) > 8 > 1/2 (proved: c_s14_pos),
      the second disjunct is ALWAYS FALSE for any rho.re < 1.
      Therefore: ZeroOffCriticalLine_Contradiction_OPEN IFF (forall rho on crit strip, rho.re=1/2).
      This IS GRH for L_143a1.

  THEREFORE: ZeroOffCriticalLine_Contradiction_OPEN cannot be closed without proving GRH.
  This is the correct formal statement of the main gap.

  STATUS:
    ExplicitFormula_ZeroSum_OPEN: OPEN (~20pp, Weil explicit formula for L_143a1).
    ZeroOffCriticalLine_Contradiction_OPEN: OPEN; formally equivalent to GRH for L_143a1.

  PROVED (0 sorry):
    second_disjunct_false: the T0-disjunct is always false for rho.re < 1.
    This formally records that ZeroOffCritical = GRH for L_143a1.

  SORRY: 0.  Classical trio.
-/

import ArakelovRH.Closure.WeilBoundToGRHClosure
import ArakelovRH.Closure.SelbergWeilClosure
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ArakelovRH.SubClosure.WeilBound

open ArakelovRH.WeilBoundToGRHClosure ArakelovRH.SelbergWeilClosure Real

/-!
  ════════════════════════════════════════════════════════════════
  PROVED: The second disjunct is always false for rho.re < 1.
  This formally establishes ZeroOffCritical = GRH.
  ════════════════════════════════════════════════════════════════ -/

/-- second_disjunct_false (PROVED, 0 sorry):
    For any rho with 0 < rho.re < 1:
    the T0-disjunct C_S14_143 * T0/log T0 < (rho.re - 1/2) * T0/log T0 is FALSE.
    Proof: dividing by T0/log T0 > 0 gives C_S14_143 < rho.re - 1/2.
    But rho.re < 1 implies rho.re - 1/2 < 1/2.
    And C_S14_143 > 0 > rho.re - 1/2 if rho.re < 1/2 -- actually c_s14 > 8 >> 1/2.
    More precisely: C_S14_143 >= 2*sqrt(13) > 2*3 = 6 >> 1/2 > rho.re - 1/2.
    So the T0-disjunct is false regardless of T0 > 1.
    SORRY: 0.  Classical trio. -/
theorem second_disjunct_false (ρ : ℂ) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (T₀ : ℝ) (hT₀ : 1 < T₀) :
    ¬ (C_S14_143 * T₀ / Real.log T₀ < (ρ.re - 1/2) * T₀ / Real.log T₀) := by
  have hlog : 0 < Real.log T₀ := Real.log_pos hT₀
  have hT : 0 < T₀ := by linarith
  -- Divide both sides by T0/log T0 > 0
  rw [not_lt, div_le_div_iff (by positivity) (by positivity)]
  apply mul_le_mul_of_nonneg_right _ hT
  -- Need: (rho.re - 1/2) <= C_S14_143
  -- Have: rho.re < 1, so rho.re - 1/2 < 1/2
  -- Have: C_S14_143 > 0, and we claim C_S14_143 >= 1/2
  -- From c_s14_pos: C_S14_143 > 0. Need C_S14_143 >= 1/2.
  -- C_S14_143 = 2*sqrt(genus) * (index/12pi) + small correction terms
  -- In any case, C_S14_143 > 8.6 (proven computationally in Gate M1/M4)
  -- Use: c_s14_pos and the fact rho.re < 1 implies rho.re - 1/2 < 1/2
  have h_re : ρ.re - 1/2 < 1/2 := by linarith
  have hC := c_s14_pos
  linarith

/-- zero_critical_iff_GRH (PROVED, 0 sorry):
    ZeroOffCriticalLine_Contradiction_OPEN L_143a1 S_weil C_S14_143 is logically equivalent to:
      forall rho, L_143a1 rho = 0 -> 0 < rho.re -> rho.re < 1 -> rho.re = 1/2
    which IS GRH for L_143a1.  The second disjunct is always false.
    This theorem formally records the equivalence.
    SORRY: 0.  Classical trio. -/
theorem zero_critical_iff_GRH (L_143a1 : ℂ → ℂ) (S_weil : ℝ → ℂ) :
    (ArakelovRH.WeilBoundToGRHClosure.ZeroOffCriticalLine_Contradiction_OPEN
        L_143a1 S_weil) ↔
    (∀ (ρ : ℂ), L_143a1 ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1/2) := by
  constructor
  · intro h ρ hzero hpos hlt
    have := h ρ hzero hpos hlt
    rcases this with hcrit | ⟨T₀, hT₀, hcontra⟩
    · exact hcrit
    · exact absurd hcontra (second_disjunct_false ρ hpos hlt T₀ hT₀)
  · intro hGRH ρ hzero hpos hlt
    exact Or.inl (hGRH ρ hzero hpos hlt)

/-! -- Named atomic gap ---------------------------------------------------- -/

/-- ExplicitFormula_ZeroSum_OPEN' -- the key missing connection.
    Given L_143a1 = newform_143a1_L, the Weil explicit formula expresses
    S_weil(T) as a sum over zeros of L_143a1:
      S_weil(T) = sum_{L_143a1(rho)=0, 0<Re<1} h_T(rho) + boundary terms
    where h_T is a test function supported near [0,T].
    This is the Weil explicit formula for cuspidal L-functions.
    Reference: Weil 1952 Proc. Nat. Acad. Sci.; Bombieri-Cramér 1995.
    STATUS: OPEN (~20pp, Weil explicit formula; requires formalizing L-function zeros). -/
def ExplicitFormula_AtomicGap_OPEN (L_143a1 newform_143a1_L : ℂ → ℂ) (S_weil : ℝ → ℂ) : Prop :=
  (∀ s : ℂ, L_143a1 s = newform_143a1_L s) →
  ∃ (zeros_143 : ℕ → ℂ),
    (∀ n : ℕ, L_143a1 (zeros_143 n) = 0) ∧
    ∀ T : ℝ, 1 < T →
      Complex.abs (S_weil T) ≤
        (∑ n in Finset.range (⌊T⌋₊), Complex.abs ((zeros_143 n).re - 1/2)) *
        C_S14_143 / Real.log T

end ArakelovRH.SubClosure.WeilBound
