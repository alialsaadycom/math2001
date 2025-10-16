import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


theorem C.Q1 : ∀ M : ℕ, ∃ n : ℕ, n > M ∧ ¬ Prime (2^n - 1) := by
  zify
  intro M
  dsimp[Prime]
  zify
  push_neg
  use 2 * M + 4

  have hM := Nat.zero_le M

  have hM2:
  M + 2 ≥ 0 + 2 := by rel[hM]

  have hM3 : 2 ^ (0 + 2) ≤ 2 ^ (M + 2) := Nat.pow_le_pow_of_le_right (by numbers) hM2 -- used "apply?" to get this
  zify at hM3

  have hM4 : 2 ^ (M) ≥ 2 ^ 0 := by refine Nat.pow_le_pow_of_le_right (by numbers) (by exact Nat.zero_le M)
  zify at hM4

  have hf :=
      calc
      (2 : ℤ) ^ (M + 2) - 1 = 2 ^ (M + 2) - 1 := by ring
      _ = 2 ^ M * 2 ^ 2 - 1 := by ring
      _ = 2 ^ M * 4 - 1 := by ring
      _ ≥ 2 ^ 0 * 4 - 1 := by rel[hM4]
      _ = 4 - 1 := by numbers
      _ > 1 := by numbers

  constructor
  . calc
    (2 * M + 4 :ℤ) = M + M + 4 := by ring
    _ > M := by addarith[]
  . right
    use 2 ^ (M + 2) - 1
    . constructor
      . use (2^(M + 2) + 1 : ℤ)
        have hn :=
          calc
          ((2 : ℤ) ^ (2 * M + 4) - 1) = (2 ^ (2 * M + 4) - 1) := by ring
          _ = (2 ^ (M + 2) - 1) * (2 ^ (M + 2) + 1) := by ring
          _ = (2 ^ (M + 2) - 1) * (2 ^ (M + 2) + 1) := by ring

        zify at hn -- ChatGPT provided the casting function "zify"
        simpa using hn-- ChatGPT provided the function "simpa"
      . constructor
        . apply ne_of_gt
          zify at hf
          simpa using hf
        . apply ne_of_lt
          have hn :=
            calc
              (2 : ℤ) ^ (2 * M + 4) - 1 = 2 ^ (2 * (M + 2)) -1 := by ring
              _ = 2 ^ (M + 2) * 2 ^ (M + 2) -1 := by ring
              _ ≥ 2 ^ (M + 2) * 2 ^ (0 + 2) - 1 := by rel[hM3]
              _ = 2 ^ (M + 2) * 4 - 1 := by ring
              _ = 2 ^ (M + 2) + 2 ^ (M + 2) * 3 - 1 := by ring
              _ ≥ 2 ^ (M + 2) + 2 ^ (0 + 2) * 3 - 1 := by rel[hM3]
              _ = 2 ^ (M + 2) + 12 - 1 := by ring
              _ > 2 ^ (M + 2) - 1 := by extra
          zify at hn
          simpa using hn
