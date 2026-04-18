import ABCmod.Basic

namespace ABCmod.Mod81

theorem reyssat_arithmetic :
    (2 : ℤ) ^ 7 - 5 ^ 3 = 3 ^ 1 := by decide

theorem reyssat_triple :
    3 + 125 = (128 : ℕ) ∧ Nat.Coprime 3 125 := by decide

theorem pow2_period : 2 ^ 54 % 81 = 1 := by decide
theorem pow5_period : 5 ^ 54 % 81 = 1 := by decide

private def check (g b a : ℕ) : Bool :=
  let lhs : ℤ := 2 ^ g - 5 ^ b
  let rhs : ℤ := 3 ^ a
  if lhs == rhs then
    g == 7 && b == 3 && a == 1
  else
    true

#eval check 7 3 1
#eval check 1 1 1
#eval check 5 2 1

private def checkSmall : Bool :=
  (List.finRange 10).all fun γ =>
  (List.finRange 10).all fun β =>
  (List.finRange 10).all fun α =>
    check (γ.val + 1) (β.val + 1) (α.val + 1)

#eval checkSmall

private def noCounterexample : Bool :=
  (List.finRange 20).all fun γ =>
  (List.finRange 15).all fun β =>
  (List.finRange 20).all fun α =>
    check (γ.val + 1) (β.val + 1) (α.val + 1)

#eval noCounterexample

end ABCmod.Mod81
