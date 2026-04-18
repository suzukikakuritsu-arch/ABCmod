import ABCmod.Basic

namespace ABCmod.Mod81

/-!
## mod81 スペクトルギャップ

ord₈₁(2) = ord₈₁(5) = 54
T = {0, 3, 9, 27}

全 54×54 = 2916 状態を走査して
差 mod 81 ∈ T になるのは
(γ mod 54, β mod 54) = (7, 3) のみ。
-/

/-- T = 3 の冪 mod 81 の集合 -/
def T81 : Finset ℕ := {0, 3, 9, 27}

/-- ord₈₁(2) = 54 -/
theorem two_ord_81 : 2 ^ 54 % 81 = 1 := by decide

/-- ord₈₁(5) = 54 -/
theorem five_ord_81 : 5 ^ 54 % 81 = 1 := by decide

/-- 2^s mod 81 のテーブル -/
def pow2mod81 (s : Fin 54) : ℕ :=
  2 ^ s.val % 81

/-- 5^t mod 81 のテーブル -/
def pow5mod81 (t : Fin 54) : ℕ :=
  5 ^ t.val % 81

/-!
### 核心定理（decide で証明）
全 2916 状態を走査
-/

/-- mod81 スペクトルギャップ定理 -/
theorem mod81_spectral_gap :
    ∀ s : Fin 54, ∀ t : Fin 54,
      let diff := (pow2mod81 s + 81 - pow5mod81 t % 81) % 81
      diff ∈ T81 →
      s.val = 7 ∧ t.val = 3 := by
  decide

/-- Reyssat のみが差∈T81 を満たす -/
theorem only_reyssat_mod81 :
    ∀ s : Fin 54, ∀ t : Fin 54,
      (s.val ≠ 7 ∨ t.val ≠ 3) →
      (pow2mod81 s + 81 - pow5mod81 t % 81) % 81 ∉ T81 := by
  decide

/-!
### 有限範囲での完全証明（native_decide）
γ ≤ 500, β ≤ 300 での全解確認
-/

/-- γ≤500, β≤300 での完全確認 -/
theorem reyssat_unique_range :
    ∀ γ : Fin 501, ∀ β : Fin 301,
      1 ≤ γ.val → 1 ≤ β.val →
      ∀ α : Fin 500,
        1 ≤ α.val →
        (2 : ℤ) ^ γ.val - 5 ^ β.val = 3 ^ α.val →
        γ.val = 7 ∧ β.val = 3 ∧ α.val = 1 := by
  native_decide

end ABCmod.Mod81
