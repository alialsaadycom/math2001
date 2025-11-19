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
    rw [Nat.choose_eq_factorial_div_factorial]
    rw [Nat.choose_eq_factorial_div_factorial]

    have h1 (n : ℕ): Nat.factorial (2 * Nat.succ (n)) = Nat.factorial (2 * Nat.succ (n) - 1) * (2 * Nat.succ (n)) := by
      simple_induction n with k IH
      .
        dsimp [Nat.factorial]
      .
        rw [Nat.succ_mul]
        rw [Nat.add_succ_sub_one]
        rw [Nat.]
        sorry
    sorry














  -- have factorial_eq_prod (n : ℕ): Nat.factorial (n) = ∏ i in Finset.Ioc 0 n, i := by
      --   simple_induction n with k IH
      --   .
      --     rw [@Finset.Ioc_self]
      --     rw [@Finset.prod_empty]
      --     dsimp[Nat.factorial]
      --   .
      --     rw [@Nat.factorial_succ]
      --     rw [IH]
      --     rw [@Finset.prod_Ioc_succ_top]
      --     ring
      --     apply Nat.zero_le k



    -- rw [Nat.choose_eq_factorial_div_factorial]
    -- rw [Nat.factorial_succ]
    -- calc
    -- (2 * k + 1 + 1) * Nat.factorial (2 * k + 1) / (Nat.factorial 3 * Nat.factorial (2 * k + 2 - 3)) + (2 * (k + 1)) ^ 2 = (2 * k + 1 + 1) * ((2 * k + 1) * Nat.factorial (2 * k)) / (Nat.factorial 3 * Nat.factorial (2 * k + 2 - 3)) +
    -- (2 * (k + 1)) ^ 2 := by extra
