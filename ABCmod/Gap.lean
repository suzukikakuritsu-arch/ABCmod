import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ContinuedFractions.Basic
import ABCmod.Basic

open Real

namespace ABCmod.Gap

/-!
## Gap Identity: gap = y × |Λ|

p^γ と最近の S-smooth 数 y の差は
y × |γ log p - log y| で表される。
-/

/-- gap と線形形式の関係（実数版）-/
lemma gap_eq_lambda (γ : ℕ) (y : ℕ) (hy : 0 < y) :
    let Λ := (γ : ℝ) * Real.log 2 - Real.log y
    |((2 : ℝ)^γ - y)| = y * |Real.exp Λ - 1| := by
  simp only
  rw [show (2 : ℝ)^γ = Real.exp (γ * Real.log 2) from by
    rw [← Real.rpow_natCast, Real.exp_log_eq_abs]
    simp [Real.rpow_natCast]]
  rw [show (y : ℝ) = Real.exp (Real.log y) from by
    rw [Real.exp_log (Nat.cast_pos.mpr hy)]]
  ring_nf
  rw [← Real.exp_sub]
  ring

/-- |e^x - 1| ≥ |x|/2 (|x| ≤ 1 のとき) -/
lemma exp_sub_one_ge (x : ℝ) (hx : |x| ≤ 1) :
    |Real.exp x - 1| ≥ |x| / 2 := by
  sorry
  -- Taylor 展開: e^x - 1 = x + x^2/2 + ...
  -- |x| ≤ 1 なら |e^x-1| ≥ |x| - x^2/2 ≥ |x|/2

/-- Smooth Gap の数値的確認（γ=7での直接計算）-/
theorem smooth_gap_reyssat :
    (2^7 : ℕ) - 5^3 = 3 ∧
    (3 : ℝ) / 2^7 ≥ 1 / (Real.log (2^7))^3 := by
  constructor
  · decide
  · norm_num
    rw [show Real.log (2^7 : ℝ) = 7 * Real.log 2 from by
      rw [Real.log_pow]]
    -- 3/128 ≥ 1/(7log2)^3
    -- (7log2)^3 ≈ (4.852)^3 ≈ 114
    -- 3/128 ≈ 0.0234, 1/114 ≈ 0.00877
    -- 0.0234 ≥ 0.00877 ✓
    sorry

end ABCmod.Gap
