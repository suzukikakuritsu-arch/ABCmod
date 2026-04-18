import ABCmod.Basic

namespace ABCmod.Mod81

/-- 基本算術 -/
theorem reyssat_arithmetic :
    (2 : ℤ) ^ 7 - 5 ^ 3 = 3 ^ 1 := by decide

theorem reyssat_triple :
    3 + 125 = (128 : ℕ) ∧ Nat.Coprime 3 125 := by decide

theorem pow2_period : 2 ^ 54 % 81 = 1 := by decide
theorem pow5_period : 5 ^ 54 % 81 = 1 := by decide

/-!
### Reyssat 唯一性
Int の等式を Bool 関数で表現して decide
-/

private def check2pow (n : ℕ) : ℤ := 2 ^ n
private def check5pow (n : ℕ) : ℤ := 5 ^ n
private def check3pow (n : ℕ) : ℤ := 3 ^ n

private def isReyssat (g b a : ℕ) : Bool :=
  (check2pow g - check5pow b == check3pow a) &&
  (g != 7 || b != 3 || a != 1) == false

/-- 反例がないことを確認 -/
private def noCounterexample : Bool :=
  (List.finRange 20).all fun γ =>
  (List.finRange 15).all fun β =>
  (List.finRange 20).all fun α =>
    let g := γ.val + 1
    let b := β.val + 1
    let a := α.val + 1
    if check2pow g - check5pow b = check3pow a
    then g == 7 && b == 3 && a == 1
    else true

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
  simp only [Fin.val_mk,
             Nat.sub_add_cancel hγ,
             Nat.sub_add_cancel hβ,
             Nat.sub_add_cancel hα] at h3
  have heq' : check2pow γ - check5pow β = check3pow α := heq
  simp only [heq', ↓reduceIte,
             Bool.and_eq_true, beq_iff_eq] at h3
  exact ⟨h3.1, h3.2.1, h3.2.2⟩

end ABCmod.Mod81
