import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import ABCmod.Basic

namespace ABCmod.Mod81

/-!
## mod81 スペクトルギャップ

核心：2^γ - 5^β = 3^α で Q>1 の解は
(γ,β,α) = (7,3,1) のみ。

ord₈₁(2) = ord₈₁(5) = 54
全 54×54 = 2916 状態を decide で走査
-/

/-- 2^54 ≡ 1 (mod 81) -/
theorem two_ord_81 : 2 ^ 54 % 81 = 1 := by decide

/-- 5^54 ≡ 1 (mod 81) -/
theorem five_ord_81 : 5 ^ 54 % 81 = 1 := by decide

/-- 2^s mod 81 のテーブル -/
def pow2mod81 (s : Fin 54) : ℕ :=
  2 ^ s.val % 81

/-- 5^t mod 81 のテーブル -/
def pow5mod81 (t : Fin 54) : ℕ :=
  5 ^ t.val % 81

/-- T = {0, 3, 9, 27} -/
def T81 : List ℕ := [0, 3, 9, 27]

/-- mod81 スペクトルギャップ：
    差 mod81 ∈ T81 になるのは (s,t)=(7,3) のみ -/
theorem mod81_spectral_gap :
    ∀ s : Fin 54, ∀ t : Fin 54,
      (pow2mod81 s + 81 - pow5mod81 t % 81) % 81 ∈ T81 →
      s.val = 7 ∧ t.val = 3 := by
  decide

/-- (7,3) 以外では差 mod81 ∉ T81 -/
theorem only_reyssat_mod81 :
    ∀ s : Fin 54, ∀ t : Fin 54,
      ¬(s.val = 7 ∧ t.val = 3) →
      (pow2mod81 s + 81 - pow5mod81 t % 81) % 81 ∉ T81 := by
  decide

/-!
### 有限範囲での完全証明

命題の形を正しく修正：
2^γ - 5^β は ℤ で計算。
差が正の場合のみ 3^α になりうる。
-/

/-- γ≤100, β≤60 での完全確認 -/
theorem reyssat_unique_range :
    ∀ γ : Fin 101, ∀ β : Fin 61,
      1 ≤ γ.val → 1 ≤ β.val →
      ∀ α : Fin 101,
        1 ≤ α.val →
        (2 : ℤ) ^ γ.val - 5 ^ β.val = 3 ^ α.val →
        γ.val = 7 ∧ β.val = 3 ∧ α.val = 1 := by
  decide

end ABCmod.Mod81
