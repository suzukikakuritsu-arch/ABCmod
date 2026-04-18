import Mathlib.Data.Nat.Prime.Basic
import ABCmod.Basic

namespace ABCmod.Mod81

/-!
## mod81 スペクトルギャップ

直接数値で証明する。
抽象的な命題は避けて
具体的な計算結果だけを述べる。
-/

/-- 基本確認 -/
theorem two_pow_7_mod81  : 2 ^ 7  % 81 = 47 := by decide
theorem five_pow_3_mod81 : 5 ^ 3  % 81 = 44 := by decide
theorem diff_reyssat_mod81 : (47 + 81 - 44) % 81 = 3 := by decide
theorem three_in_T81 : 3 ∈ ([0, 3, 9, 27] : List ℕ) := by decide

/-- ord₈₁(2) = 54 -/
theorem two_ord_81 : 2 ^ 54 % 81 = 1 := by decide

/-- ord₈₁(5) = 54 -/
theorem five_ord_81 : 5 ^ 54 % 81 = 1 := by decide

/-- Reyssat の差 mod 81 = 3 ∈ T -/
theorem reyssat_diff_mod81 :
    (2 ^ 7 + 81 - 5 ^ 3) % 81 = 3 := by decide

/-- 全状態確認：
    s ∈ Fin 54, t ∈ Fin 54 で
    (2^s + 81 - 5^t) % 81 = 3 になるのは
    (s, t) = (7, 3) のみ

    これを Bool 関数で表現して decide -/
def checkAllStates : Bool :=
  (List.range 54).all fun s =>
    (List.range 54).all fun t =>
      let diff := (2 ^ s % 81 + 81 - 5 ^ t % 81) % 81
      let inT := diff == 0 || diff == 3 || diff == 9 || diff == 27
      if inT then s == 7 && t == 3 else true

/-- 全状態確認が true -/
theorem checkAllStates_true : checkAllStates = true := by decide

/-- T81 に入る状態は (7,3) のみ -/
theorem mod81_only_reyssat
    (s t : ℕ) (hs : s < 54) (ht : t < 54)
    (hdiff : (2 ^ s % 81 + 81 - 5 ^ t % 81) % 81 ∈
             ([0, 3, 9, 27] : List ℕ)) :
    s = 7 ∧ t = 3 := by
  have h := checkAllStates_true
  unfold checkAllStates at h
  simp [List.all_iff_forall] at h
  have hs' := h s (by omega)
  have ht' := hs' t (by omega)
  simp only [Bool.and_eq_true, beq_iff_eq] at ht'
  by_contra hne
  push_neg at hne
  have : ¬ ((2 ^ s % 81 + 81 - 5 ^ t % 81) % 81 == 0 ||
             (2 ^ s % 81 + 81 - 5 ^ t % 81) % 81 == 3 ||
             (2 ^ s % 81 + 81 - 5 ^ t % 81) % 81 == 9 ||
             (2 ^ s % 81 + 81 - 5 ^ t % 81) % 81 == 27) := by
    intro hT
    simp only [Bool.or_eq_true, beq_iff_eq] at hT
    have hst : s = 7 ∧ t = 3 := ht' hT
    exact hne hst.1 hst.2
  simp only [Bool.not_or, Bool.not_eq_true, Bool.beq_eq_false_iff_ne] at this
  have hmem : (2 ^ s % 81 + 81 - 5 ^ t % 81) % 81 ∈
              ([0, 3, 9, 27] : List ℕ) := hdiff
  simp [List.mem_cons, List.mem_singleton] at hmem
  rcases hmem with h0 | h3 | h9 | h27
  · exact this.1 h0
  · exact this.2.1 h3
  · exact this.2.2.1 h9
  · exact this.2.2.2 h27

/-!
### 有限範囲での直接確認
γ≤20, β≤15 で Reyssat のみを確認
-/

/-- 直接確認用 Bool 関数 -/
def checkReyssatUnique : Bool :=
  (List.range 20).all fun γ =>
    (List.range 15).all fun β =>
      (List.range 20).all fun α =>
        if γ + 1 ≥ 1 && β + 1 ≥ 1 && α + 1 ≥ 1 then
          if (2 : Int) ^ (γ + 1) - 5 ^ (β + 1) = 3 ^ (α + 1) then
            (γ + 1) == 7 && (β + 1) == 3 && (α + 1) == 1
          else true
        else true

theorem checkReyssatUnique_true : checkReyssatUnique = true := by decide

/-- γ≤20, β≤15 での Reyssat 唯一性 -/
theorem reyssat_unique_small
    (γ β α : ℕ)
    (hγ : 1 ≤ γ) (hγ2 : γ ≤ 20)
    (hβ : 1 ≤ β) (hβ2 : β ≤ 15)
    (hα : 1 ≤ α) (hα2 : α ≤ 20)
    (heq : (2 : ℤ) ^ γ - 5 ^ β = 3 ^ α) :
    γ = 7 ∧ β = 3 ∧ α = 1 := by
  have h := checkReyssatUnique_true
  unfold checkReyssatUnique at h
  simp only [List.all_iff_forall, List.mem_range] at h
  have hγ' := h (γ - 1) (by omega)
  have hβ' := hγ' (β - 1) (by omega)
  have hα' := hβ' (α - 1) (by omega)
  simp only [Nat.sub_add_cancel hγ, Nat.sub_add_cancel hβ,
             Nat.sub_add_cancel hα] at hα'
  simp only [Bool.and_eq_true, beq_iff_eq, heq, decide_True,
             Bool.true_and] at hα'
  exact ⟨hα'.1, hα'.2.1, hα'.2.2⟩

end ABCmod.Mod81
