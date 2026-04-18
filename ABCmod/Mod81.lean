import ABCmod.Basic

namespace ABCmod.Mod81

/-!
## mod81 スペクトルギャップ
-/

/-- 差 mod 81 の計算 -/
def diffMod (s t : ℕ) : ℕ :=
  (2 ^ s % 81 + 81 - 5 ^ t % 81) % 81

/-- T = {3, 9, 27}（0を除外：差=0は2^s=5^t mod81で多数存在）-/
def inT (n : ℕ) : Bool :=
  n == 3 || n == 9 || n == 27

/-- Reyssat の確認 -/
theorem reyssat_diff : diffMod 7 3 = 3 := by native_decide
theorem reyssat_inT : inT 3 = true := by decide

/-- 全54×54状態の確認 -/
def checkGap : Bool :=
  (List.range 54).all fun s =>
    (List.range 54).all fun t =>
      if inT (diffMod s t)
      then s == 7 && t == 3
      else true

#eval checkGap

theorem checkGap_true : checkGap = true := by native_decide

/-- 核心：inT になるのは (7,3) のみ -/
theorem mod81_only_reyssat
    (s t : ℕ) (hs : s < 54) (ht : t < 54)
    (hT : inT (diffMod s t) = true) :
    s = 7 ∧ t = 3 := by
  have h := checkGap_true
  unfold checkGap at h
  rw [List.all_eq_true] at h
  have h1 : (fun s => (List.range 54).all fun t =>
      if inT (diffMod s t) then s == 7 && t == 3 else true) s := by
    apply h
    simp [List.mem_range, hs]
  rw [List.all_eq_true] at h1
  have h2 : (fun t => if inT (diffMod s t) then s == 7 && t == 3
      else true) t := by
    apply h1
    simp [List.mem_range, ht]
  simp only [hT, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h2
  exact ⟨h2.1, h2.2⟩

/-!
### Reyssat 唯一性（γ≤20）
-/

def checkUnique : Bool :=
  (List.range 20).all fun g =>
    (List.range 15).all fun b =>
      (List.range 20).all fun a =>
        let γ := g + 1; let β := b + 1; let α := a + 1
        if (2 : Int) ^ γ - 5 ^ β = 3 ^ α
        then γ == 7 && β == 3 && α == 1
        else true

#eval checkUnique

theorem checkUnique_true : checkUnique = true := by native_decide

theorem reyssat_unique_small
    (γ β α : ℕ)
    (hγ : 1 ≤ γ) (hγ2 : γ ≤ 20)
    (hβ : 1 ≤ β) (hβ2 : β ≤ 15)
    (hα : 1 ≤ α) (hα2 : α ≤ 20)
    (heq : (2 : ℤ) ^ γ - 5 ^ β = 3 ^ α) :
    γ = 7 ∧ β = 3 ∧ α = 1 := by
  have h := checkUnique_true
  unfold checkUnique at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h1 := h (γ - 1) (by omega)
  have h2 := h1 (β - 1) (by omega)
  have h3 := h2 (α - 1) (by omega)
  simp only [Nat.sub_add_cancel hγ, Nat.sub_add_cancel hβ,
             Nat.sub_add_cancel hα] at h3
  simp only [heq, ↓reduceIte, Bool.and_eq_true,
             beq_iff_eq] at h3
  exact ⟨h3.1, h3.2.1, h3.2.2⟩

end ABCmod.Mod81
