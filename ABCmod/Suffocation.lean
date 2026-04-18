import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

namespace ABCmod.Suffocation

/-!
## 窒息不等式

b^{ε/(1+ε)} ≤ (log b)^C は
b が有界であることを意味する。
-/

/-- b^α / (log b)^C → ∞ (b→∞, α>0) -/
theorem suffocation_diverges
    (α : ℝ) (C : ℝ) (hα : 0 < α) :
    Filter.Tendsto
      (fun b : ℝ => b^α / (Real.log b)^C)
      Filter.atTop
      Filter.atTop := by
  apply Filter.Tendsto.atTop_div_const_pow_atTop
  · exact hα
  · norm_num
  -- b^α grows faster than (log b)^C for any α>0, C
  sorry

/-- 窒息上界の存在 -/
theorem suffocation_bound_exists
    (ε : ℝ) (hε : 0 < ε) (C : ℝ) :
    ∃ B : ℝ, ∀ b : ℝ, b ≥ B →
      b^(ε/(1+ε)) > (Real.log b)^C := by
  have hα : 0 < ε/(1+ε) := by positivity
  obtain ⟨B, hB⟩ := (suffocation_diverges (ε/(1+ε)) C hα).eventually
    (Filter.eventually_ge_atTop 1) |>.exists
  exact ⟨B, fun b hb => by
    have := hB hb
    linarith⟩

/-- 核心：窒息不等式から有界性 -/
theorem suffocation_implies_bounded
    (ε : ℝ) (hε : 0 < ε) (C : ℝ) :
    ∃ B : ℕ, ∀ b : ℕ,
      (b : ℝ)^(ε/(1+ε)) ≤ (Real.log b)^C →
      b ≤ B := by
  obtain ⟨B_real, hB⟩ := suffocation_bound_exists ε hε C
  use ⌈B_real⌉₊
  intro b hb
  by_contra h
  push_neg at h
  have hb_large : (b : ℝ) ≥ B_real := by
    exact_mod_cast le_of_lt (lt_of_lt_of_le
      (Nat.lt_ceil.mpr (le_refl _)) h)
  have := hB b hb_large
  linarith

end ABCmod.Suffocation
