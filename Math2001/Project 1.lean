import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

example (M : ℕ) : ∃ n : ℕ, n > M ∧ ¬ Prime (2 ^ n - 1) := by
  use 2 * M + 4
  constructor
  . calc
    2 * M + 4 = M + M + 4 := by ring
    _ > M := by addarith[]
  . calc
    (2 ^ (2 * M + 4) - 1) = (2 ^ (2 * (M + 2)) - 1) := by ring
    _ = ((2 ^ (M + 2)) ^ 2 - 1) := by ring
    _ = (2 ^ (M + 2) - 1) * (2 ^ (M + 2) + 1) := by ring -- How to prove not prime?
