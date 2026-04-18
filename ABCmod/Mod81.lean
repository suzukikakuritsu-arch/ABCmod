import ABCmod.Basic

namespace ABCmod.Mod81

/-- 基本算術確認 -/
theorem reyssat_arithmetic :
    (2 : ℤ) ^ 7 - 5 ^ 3 = 3 ^ 1 := by decide

theorem reyssat_triple :
    3 + 125 = (128 : ℕ) ∧ Nat.Coprime 3 125 := by decide

theorem pow2_period : 2 ^ 54 % 81 = 1 := by decide
theorem pow5_period : 5 ^ 54 % 81 = 1 := by decide

/-- デバッグ：単一ケースの確認 -/
#eval (2 : ℤ) ^ 7 - 5 ^ 3      -- 3 が出るはず
#eval (2 : ℤ) ^ 7 - 5 ^ 3 == 3 ^ 1  -- true が出るはず
#eval (2 : ℤ) ^ 1 - 5 ^ 1      -- -3 が出るはず
#eval (2 : ℤ) ^ 1 - 5 ^ 1 == 3 ^ 1  -- false が出るはず

/-- check の単体確認 -/
private def check (g b a : ℕ) : Bool :=
  if (2 : ℤ) ^ g - 5 ^ b == 3 ^ a
  then g == 7 && b == 3 && a == 1
  else true

#eval check 7 3 1   -- true
#eval check 1 1 1   -- true (条件不成立なのでtrue)
#eval check 7 3 2   -- true (2^7-5^3=3≠3^2=9)

/-- 小さい範囲で確認 -/
private def checkSmall : Bool :=
  (List.finRange 10).all fun γ =>
  (List.finRange 10).all fun β =>
  (List.finRange 10).all fun α =>
    check (γ.val + 1) (β.val + 1) (α.val + 1)

#eval checkSmall  -- true が出るはず

/-- 本番 -/
private def noCounterexample : Bool :=
  (List.finRange 20).all fun γ =>
  (List.finRange 15).all fun β =>
  (List.finRange 20).all fun α =>
    check (γ.val + 1) (β.val + 1) (α.val + 1)

#eval noCounterexample

/-- #eval が true なら以下のコメントを外す -/
-- theorem noCounterexample_true : noCounterexample = true := by
--   native_decide

end ABCmod.Mod81
