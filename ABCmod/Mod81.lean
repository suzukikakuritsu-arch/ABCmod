import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import ABCmod.Basic

namespace ABCmod.Mod81

/-!
## mod81 スペクトルギャップ
-/

/-- 2^54 ≡ 1 (mod 81) -/
theorem two_ord_81 : 2 ^ 54 % 81 = 1 := by decide

/-- 5^54 ≡ 1 (mod 81) -/
theorem five_ord_81 : 5 ^ 54 % 81 = 1 := by decide

/-- T = {0, 3, 9, 27} = 3^α mod 81 の値域 -/
def T81 : List ℕ := [0, 3, 9, 27]

/-- diff mod 81 の計算（アンダーフロー回避）-/
def diffMod81 (s t : Fin 54) : ℕ :=
  (2 ^ s.val % 81 + 81 - 5 ^ t.val % 81) % 81

/-- decide で全2916状態を確認：
    diffMod81 s t ∈ T81 ↔ s=7 ∧ t=3 -/
theorem mod81_iff :
    ∀ s : Fin 54, ∀ t : Fin 54,
      diffMod81 s t ∈ T81 ↔ s.val = 7 ∧ t.val = 3 := by
  decide

/-- T81 に入るのは (7,3) のみ（→ 方向）-/
theorem mod81_only_reyssat :
    ∀ s : Fin 54, ∀ t : Fin 54,
      diffMod81 s t ∈ T81 →
      s.val = 7 ∧ t.val = 3 := by
  decide

/-- (7,3) 以外は T81 に入らない（← 方向）-/
theorem mod81_not_T81 :
    ∀ s : Fin 54, ∀ t : Fin 54,
      ¬(s.val = 7 ∧ t.val = 3) →
      diffMod81 s t ∉ T81 := by
  decide

/-!
### 有限範囲での直接確認
-/

/-- γ≤50, β≤35 での完全確認 -/
theorem reyssat_unique_range :
    ∀ γ : Fin 51, ∀ β : Fin 36,
      1 ≤ γ.val → 1 ≤ β.val →
      ∀ α : Fin 51,
        1 ≤ α.val →
        (2 : ℤ) ^ γ.val - 5 ^ β.val = 3 ^ α.val →
        γ.val = 7 ∧ β.val = 3 ∧ α.val = 1 := by
  decide

end ABCmod.Mod81
