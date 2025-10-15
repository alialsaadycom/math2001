import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- Need to finish the nonprime definition
def Nonprime (n : ℕ) : Prop := ∃ m : ℕ, m ∣ n → m > 1 ∧ m ≠ n

example : ∀ M : ℕ, ∃ n : ℕ, n > M ∧ ¬ Prime (2^n - 1) := by
  intro M
  dsimp[Prime]
  push_neg
  use 2 * M + 4
  constructor
  . calc
    2 * M + 4 = M + M + 4 := by ring
    _ > M := by addarith[]
  . right
    use 2 ^ (M + 2) - 1
    . constructor
      use (2^(M + 2) + 1)
      have h1 := -- used ChatGPT to help derive this hypothesis, specifically casting to Z
        calc
          (2 : ℤ) ^ (2 * M + 4) - 1 = 2 ^ (M + 2) * 2 ^ (M + 2) - 1 := by ring
          _ = (2 ^ (M + 2)) ^ 2 - 1 := by ring_nf
          _ = (2 ^ (M + 2) - 1) * (2 ^ (M + 2) + 1) := by ring
      apply h1
