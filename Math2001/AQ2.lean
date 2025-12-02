import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

open BigOperators


theorem A.Q2 (n : ℕ) : ∑ i in Finset.range (n + 1), (2 * i) ^ 2 = (2 * n + 2).choose 3 := by
  cases n with
  | zero =>
    rw [@Finset.sum_range_add]
    rw [@Finset.sum_range_zero]
    rw [@Finset.sum_range_one]
    dsimp[Nat.choose]
    numbers
  | succ n =>
  simple_induction n with k IH
  . -- base case
    rw [@Finset.sum_range_add]
    dsimp [Nat.succ]
    rw [@Finset.sum_singleton]
    rw [@Finset.sum_singleton]
    dsimp[Nat.choose]
    numbers
  . -- inductive step
    rw [@Finset.sum_range_add]
    rw [@Finset.sum_range_one]
    rw [IH]
    rw [Nat.succ_add_eq_succ_add]

    have succ_zero_eq_one : Nat.succ 0 = 1 := by rfl
    have succ_eq_plus_one (n : ℕ) : Nat.succ n = n + 1 := by rfl


    rw [show Nat.succ 0 = 1 by rfl]
    rw[show Nat.succ k = k + 1 by rfl]
    rw [show Nat.succ (k + 1) = k + 2 by rfl]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    rw [show Nat.factorial 3 = 6 by rfl]
    dsimp [Nat.descFactorial]

    rw [show (2 * (k + 1 + 1)) ^ 2 = 4 * (k + 2) ^ 2 by ring]
    rw [Nat.add_sub_cancel]
    rw [@add_sq]
    rw [Nat.add_succ_sub_one]
    rw?


    -- rw [show Nat.factorial (2 * (k + 1) + 2 - 3) = Nat.factorial (2 * k + 1) by rfl]


    -- dsimp [Nat.factorial]
    -- rw [show Nat.succ (2 * (k + 1) + 1) = 2 * (k + 1) + 2 by rfl]
    -- rw [show Nat.succ (2 * (k + 1)) = 2 * (k + 1) + 1 by rfl]
    -- rw [show Nat.succ (2 * k + 1) = 2 * k + 2 by rfl]
    -- rw [show Nat.succ (2 * k) = 2 * k + 1 by rfl]

    -- rw [Nat.div_eq]






    sorry
    -- but WHY???
    -- have : 3 ≤ 2 * (k + 1) + 2 := by
    --   calc
    --   2 * (k + 1) + 2 ≥ 2 * (0 + 1) + 2 := by rel[Nat.zero_le k]
    --   _ = 2 + 2 := by numbers
    --   _ ≥ 3 := by numbers
    -- apply this


theorem factorial_eq_succ_mul (n b : ℕ) : Nat.factorial (2 * Nat.succ (n) + b) = Nat.factorial (2 * (n + 1) + b - 1) * (2 * (n + 1) + b) := by
    have succ_zero_eq_one : Nat.succ 0 = 1 := by rfl
    have succ_eq_plus_one (n : ℕ) : Nat.succ n = n + 1 := by rfl
    simple_induction n with k IH
    . -- base case
       dsimp [Nat.factorial]
       rw [succ_zero_eq_one]
       simple_induction b with k IH
       . -- base case
        dsimp [Nat.factorial]
       . -- inductive step
        rw [Nat.succ_add_sub_one]
        dsimp [Nat.factorial]
        rw[IH]
        have : Nat.succ (2 * 1 + k) = 2 * 1 + (k + 1) := by rfl
        rw[this]
        rw [Nat.succ_add_sub_one]
        have :=
          calc
          Nat.succ (1 + k) = (1 + k + 1) := by rfl
          _ = 2 * 1 + k := by ring
        rw[this]
        ring
    . -- inductive step
       rw [succ_eq_plus_one]
       rw [Nat.two_mul]

       have : k + 1 + 1 + (k + 1 + 1) + b = k + 1 + 1 + 1 + b + (k + 1) := by ring
       rw[this]

       dsimp [Nat.factorial]
       rw[Nat.add_succ_sub_one]
       rw[Nat.succ_eq_one_add]

       ring

theorem factorial_eq_succ_mul' (n : ℕ): Nat.factorial (2 * Nat.succ (n)) = Nat.factorial (2 * (n + 1) - 1) * (2 * (n + 1)) := by
    have : Nat.factorial (2 * Nat.succ (n)) = Nat.factorial (2 * Nat.succ (n) + 0) := by ring
    rw [this]
    rw [factorial_eq_succ_mul]
    ring
