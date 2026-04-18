import ABCmod.Basic

namespace ABCmod.Mod81

/-- 基本算術確認 -/
theorem reyssat_arithmetic :
    (2 : ℤ) ^ 7 - 5 ^ 3 = 3 ^ 1 := by decide

theorem reyssat_triple :
    3 + 125 = (128 : ℕ) ∧ Nat.Coprime 3 125 := by decide

theorem pow2_period : 2 ^ 54 % 81 = 1 := by decide
theorem pow5_period : 5 ^ 54 % 81 = 1 := by decide

/-- Reyssat 唯一性：Bool 版定義 -/
private def check (g b a : ℕ) : Bool :=
  if (2 : ℤ) ^ g - 5 ^ b == 3 ^ a
  then g == 7 && b == 3 && a == 1
  else true

private def noCounterexample : Bool :=
  (List.finRange 20).all fun γ =>
  (List.finRange 15).all fun β =>
  (List.finRange 20).all fun α =>
    check (γ.val + 1) (β.val + 1) (α.val + 1)

#eval noCounterexample

theorem noCounterexample_true : noCounterexample = true := by
  native_decide

theorem reyssat_unique_small
    (γ β α : ℕ)
    (hγ : 1 ≤ γ) (hγ2 : γ ≤ 20)
    (hβ : 1 ≤ β) (hβ2 : β ≤ 15)
    (hα : 1 ≤ α) (hα2 : α ≤ 20)
    (heq : (2 : ℤ) ^ γ - 5 ^ β = 3 ^ α) :
    γ = 7 ∧ β = 3 ∧ α = 1 := by
  have h := noCounterexample_true
  unfold noCounterexample at h
  simp only [List.all_eq_true, List.mem_finRange] at h
  have h1 := h ⟨γ - 1, by omega⟩
  have h2 := h1 ⟨β - 1, by omega⟩
  have h3 := h2 ⟨α - 1, by omega⟩
  unfold check at h3
  simp only [Nat.sub_add_cancel hγ,
             Nat.sub_add_cancel hβ,
             Nat.sub_add_cancel hα] at h3
  have heqB : ((2 : ℤ) ^ γ - 5 ^ β == 3 ^ α) = true := by
    simp [heq]
  simp only [heqB, ↓reduceIte,
             Bool.and_eq_true, beq_iff_eq] at h3
  exact ⟨h3.1, h3.2.1, h3.2.2⟩

end ABCmod.Mod81
