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
### Reyssat 唯一性（Fin を使って decide）
-/

/-- γ≤20, β≤15, α≤20 での唯一性 -/
theorem reyssat_unique_fin :
    ∀ (γ : Fin 20) (β : Fin 15) (α : Fin 20),
      (2 : ℤ) ^ (γ.val + 1) - 5 ^ (β.val + 1) = 3 ^ (α.val + 1) →
      γ.val + 1 = 7 ∧ β.val + 1 = 3 ∧ α.val + 1 = 1 := by
  decide

/-- 使いやすい形 -/
theorem reyssat_unique_small
    (γ β α : ℕ)
    (hγ : 1 ≤ γ) (hγ2 : γ ≤ 20)
    (hβ : 1 ≤ β) (hβ2 : β ≤ 15)
    (hα : 1 ≤ α) (hα2 : α ≤ 20)
    (heq : (2 : ℤ) ^ γ - 5 ^ β = 3 ^ α) :
    γ = 7 ∧ β = 3 ∧ α = 1 := by
  have h := reyssat_unique_fin
    ⟨γ - 1, by omega⟩
    ⟨β - 1, by omega⟩
    ⟨α - 1, by omega⟩
    (by simp [Nat.sub_add_cancel hγ,
              Nat.sub_add_cancel hβ,
              Nat.sub_add_cancel hα, heq])
  simp [Nat.sub_add_cancel hγ,
        Nat.sub_add_cancel hβ,
        Nat.sub_add_cancel hα] at h
  exact h

end ABCmod.Mod81
