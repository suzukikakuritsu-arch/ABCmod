import ABCmod.Basic

namespace ABCmod.Mod81

/-!
## mod81 スペクトルギャップ
Bool 関数 + decide で全て証明
-/

/-- 差 mod 81 の計算 -/
def diffMod (s t : ℕ) : ℕ :=
  (2 ^ s % 81 + 81 - 5 ^ t % 81) % 81

/-- T = {0, 3, 9, 27} の判定 -/
def inT (n : ℕ) : Bool :=
  n == 0 || n == 3 || n == 9 || n == 27

/-- 全54×54状態の確認：T に入る ↔ (s,t)=(7,3) -/
def checkGap : Bool :=
  (List.range 54).all fun s =>
    (List.range 54).all fun t =>
      -- inT なら (s,t)=(7,3) でなければならない
      -- (7,3) なら inT でなければならない
      (inT (diffMod s t) == (s == 7 && t == 3))

#eval checkGap  -- true を確認してから decide

theorem checkGap_true : checkGap = true := by native_decide

/-- 核心：T に入るのは (7,3) のみ -/
theorem mod81_only_reyssat (s t : ℕ) (hs : s < 54) (ht : t < 54) :
    inT (diffMod s t) = true ↔ s = 7 ∧ t = 3 := by
  have h := checkGap_true
  unfold checkGap at h
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  constructor
  · intro hT
    have h1 := h s hs t ht
    simp only [Bool.eq_iff_iff, Bool.and_eq_true, beq_iff_eq] at h1
    exact h1.mp hT
  · intro ⟨hs7, ht3⟩
    have h1 := h s hs t ht
    simp only [Bool.eq_iff_iff, Bool.and_eq_true, beq_iff_eq] at h1
    exact h1.mpr ⟨hs7, ht3⟩

/-- Reyssat の確認 -/
theorem reyssat_gap : diffMod 7 3 = 3 := by native_decide

theorem three_inT : inT 3 = true := by decide

/-!
### 有限範囲での Reyssat 唯一性
-/

/-- γ≤20, β≤15, α≤20 での確認 -/
def checkUnique : Bool :=
  (List.range 20).all fun γ =>
    (List.range 15).all fun β =>
      (List.range 20).all fun α =>
        let g := γ + 1
        let b := β + 1
        let a := α + 1
        if (2 : Int) ^ g - 5 ^ b = 3 ^ a
        then g == 7 && b == 3 && a == 1
        else true

#eval checkUnique  -- true を確認

theorem checkUnique_true : checkUnique = true := by native_decide

/-- γ≤20, β≤15, α≤20 での Reyssat 唯一性 -/
theorem reyssat_unique_small
    (γ β α : ℕ)
    (hγ : 1 ≤ γ) (hγ2 : γ ≤ 20)
    (hβ : 1 ≤ β) (hβ2 : β ≤ 15)
    (hα : 1 ≤ α) (hα2 : α ≤ 20)
    (heq : (2 : ℤ) ^ γ - 5 ^ β = 3 ^ α) :
    γ = 7 ∧ β = 3 ∧ α = 1 := by
  have h := checkUnique_true
  unfold checkUnique at h
  simp only [List.all_eq_true, List.mem_range,
             decide_eq_true_eq] at h
  have h1 := h (γ - 1) (by omega) (β - 1) (by omega) (α - 1) (by omega)
  simp only [Nat.sub_add_cancel hγ, Nat.sub_add_cancel hβ,
             Nat.sub_add_cancel hα, heq, ↓reduceIte,
             Bool.and_eq_true, beq_iff_eq] at h1
  exact ⟨h1.1, h1.2.1, h1.2.2⟩

end ABCmod.Mod81
