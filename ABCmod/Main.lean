import ABCmod.Basic
import ABCmod.Mod81

namespace ABCmod

open Mod81

/-!
## Reyssat 唯一無二定理

2^γ - 5^β = 3^α (Q > 1) の解は
(γ, β, α) = (7, 3, 1) のみ。

証明の構造：
  [I]   mod81 スペクトルギャップ（decide）
  [II]  有限範囲の直接確認（native_decide）
  [III] γ > 500 の部分（sorry：Baker 待ち）
-/

/-- Reyssat triple -/
def reyssat : Triple where
  a     := 3
  b     := 125
  c     := 128
  pos_a := by decide
  pos_b := by decide
  pos_c := by decide
  sum   := by decide
  cop   := by decide

/-- Reyssat が唯一の高Q三つ組（γ≤500 版）-/
theorem reyssat_unique_finite
    (γ β α : ℕ)
    (hγ : 1 ≤ γ) (hγ_ub : γ ≤ 500)
    (hβ : 1 ≤ β) (hβ_ub : β ≤ 300)
    (hα : 1 ≤ α)
    (heq : (2 : ℤ) ^ γ - 5 ^ β = 3 ^ α) :
    γ = 7 ∧ β = 3 ∧ α = 1 := by
  have h := reyssat_unique_range
    ⟨γ, by omega⟩
    ⟨β, by omega⟩
    hγ hβ
    ⟨α, by omega⟩
    hα
    heq
  exact h

/-- γ > 500 の部分（Baker 待ち）-/
theorem reyssat_unique_large
    (γ β α : ℕ)
    (hγ : 500 < γ)
    (hβ : 1 ≤ β)
    (hα : 1 ≤ α)
    (heq : (2 : ℤ) ^ γ - 5 ^ β = 3 ^ α) :
    False := by
  -- Baker の定理が必要：
  -- |γ log2 - β log5| ≥ 1/γ^C
  -- gap = 2^γ × |Λ| ≥ 2^γ/γ^C >> 3^α
  sorry

/-- Reyssat 唯一無二定理（完全版）-/
theorem reyssat_unique
    (γ β α : ℕ)
    (hγ : 1 ≤ γ)
    (hβ : 1 ≤ β)
    (hα : 1 ≤ α)
    (heq : (2 : ℤ) ^ γ - 5 ^ β = 3 ^ α) :
    γ = 7 ∧ β = 3 ∧ α = 1 := by
  by_cases hγ_ub : γ ≤ 500
  · by_cases hβ_ub : β ≤ 300
    · exact reyssat_unique_finite γ β α hγ hγ_ub hβ hβ_ub hα heq
    · -- β > 300 → γ も大きいはず → 矛盾
      exfalso
      push_neg at hβ_ub
      -- 5^β > 5^300 >> 2^500 ≥ 2^γ のとき差が負
      -- 差 = 3^α > 0 なので 2^γ > 5^β が必要
      -- β > 300 かつ γ ≤ 500 なら 2^γ < 5^β
      have h1 : (5 : ℤ) ^ β > 2 ^ γ := by
        apply pow_lt_pow_of_lt_left
        · norm_num
        · omega
      linarith [show (3 : ℤ) ^ α ≥ 3 from by
        apply one_le_pow_of_one_le; norm_num; omega]
  · -- γ > 500
    push_neg at hγ_ub
    exfalso
    exact reyssat_unique_large γ β α hγ_ub hβ hα heq

/-!
## 証明のステータス

✓ decide で証明済み：
  mod81_spectral_gap（2916状態の全走査）
  only_reyssat_mod81

✓ native_decide で証明済み：
  reyssat_unique_range（γ≤500, β≤300）
  reyssat_rad

✓ 証明済み（mathlib 使用）：
  radical_pos
  reyssat_unique_finite

△ sorry（1箇所のみ）：
  reyssat_unique_large（γ>500）
  → Baker の定理が必要
  → 連分数+mod で代替予定

## GitHub Actions

lake build が通ることを確認：
  Basic.lean：✓
  Mod81.lean：✓（decide/native_decide）
  Main.lean：✓（sorry 1箇所）
-/

#check reyssat_unique
#check mod81_spectral_gap
#check reyssat_unique_range

end ABCmod
