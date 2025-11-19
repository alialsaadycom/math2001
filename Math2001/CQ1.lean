import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


theorem C.Q1 : ∀ M : ℕ, ∃ n : ℕ, n > M ∧ ¬ Prime (2 ^ n - 1) := by
  intro M
  dsimp[Prime]
  zify
  push_neg

  use 2 * M + 4

  have hM := Nat.zero_le M

  have hM2 : 2 ^ (0 + 2) ≤ 2 ^ (M + 2) := Nat.pow_le_pow_of_le_right (by numbers) (by rel[hM]) -- ChatGPT provided the lemma
  zify at hM2

  have hM3 : 2 ^ (M) ≥ 2 ^ 0 := by refine Nat.pow_le_pow_of_le_right (by numbers) hM
  zify at hM3

  constructor
  . calc
    (2 * M + 4 : ℤ) = M + M + 4 := by ring
    _ > M := by addarith[] -- this proves that n > M ∀M.
  . right
    use 2 ^ (M + 2) - 1
    . constructor
      . use (2 ^ (M + 2) + 1 : ℤ)
        have hn :=
          calc
          ((2 : ℤ) ^ (2 * M + 4) - 1) = (2 ^ (2 * M + 4) - 1) := by ring
          _ = (2 ^ (M + 2) - 1) * (2 ^ (M + 2) + 1) := by ring -- proves difference of squares
        simpa using hn-- ChatGPT provided the function "simpa"
      . constructor
        . apply ne_of_gt
          have gt_one :=
            calc
              (2 : ℤ) ^ (M + 2) - 1 = 2 ^ (M + 2) - 1 := by ring
              _ = 2 ^ M * 2 ^ 2 - 1 := by ring
              _ = 2 ^ M * 4 - 1 := by ring
              _ ≥ 2 ^ 0 * 4 - 1 := by rel[hM3]
              _ = 4 - 1 := by numbers
              _ > 1 := by numbers
          simpa using gt_one -- prove that the factor is not 1

        . apply ne_of_lt
          have lt_n :=
            calc
              (2 : ℤ) ^ (2 * M + 4) - 1 = 2 ^ (2 * (M + 2)) - 1 := by ring
              _ = 2 ^ (M + 2) * 2 ^ (M + 2) - 1 := by ring
              _ ≥ 2 ^ (M + 2) * 2 ^ (0 + 2) - 1 := by rel[hM2]
              _ = 2 ^ (M + 2) * 4 - 1 := by ring
              _ = 2 ^ (M + 2) + 2 ^ (M + 2) * 3 - 1 := by ring
              _ ≥ 2 ^ (M + 2) + 2 ^ (0 + 2) * 3 - 1 := by rel[hM2]
              _ = 2 ^ (M + 2) + 12 - 1 := by ring
              _ > 2 ^ (M + 2) - 1 := by extra
          simpa using lt_n -- prove that the factor does not equal 2^n - 1
