import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- Need to finish the nonprime definition
def Nonprime (n : ℕ) : Prop := ∃ m : ℕ, m ∣ n → m > 1 ∧ m ≠ n

example (M : ℕ) : ∃ n : ℕ, n > M ∧ Nonprime (2^n - 1) := by
  dsimp [Nonprime]
  use 2 * M + 4
  constructor
  . calc
    2 * M + 4 = M + M + 4 := by ring
    _ > M := by addarith[]
  use 2 ^ (M + 2) - 1
  intro ha --chat gpt
  constructor
  . calc
    2 ^ (M + 2) - 1 >  :=
