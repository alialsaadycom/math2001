import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Basic
import Library.Basic

math2001_init

open BigOperators

theorem A.Q2 (n : ℕ) : ∑ i in Finset.range (n + 1), (2 * i) ^ 2 = (2 * n + 2).choose 3 := by
  cases n with
  | zero =>
    -- show that sum to 0 and 2 choose 3 are both zero
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

    -- make it easier to read
    rw [show (2 * (k + 1 + 1)) ^ 2 = (2 * k + 4) ^ 2 by rfl]
    rw [show Nat.succ k = k + 1 by rfl]
    rw [show 2 * (k + 1) + 2 = 2 * k + 4 by rfl]
    rw [show Nat.succ (k + 1) = k + 2 by rfl]
    rw [show 2 * (k + 2) + 2 = 2 * k + 6 by rfl]

    -- show that the goal is equivalent with a term of 2k + 4 choose 3 on both sides (then we show the other terms are equal)
    rw [show Nat.choose (2 * k + 6) 3 = Nat.choose (2 * k + 5) 2 + Nat.choose (2 * k + 5) 3 by rw[Nat.choose_succ_succ]]
    rw [show Nat.choose (2 * k + 5) 3 = Nat.choose (2 * k + 4) 2 + Nat.choose (2 * k + 4) 3 by rw[Nat.choose_succ_succ]]

    rw [← Nat.add_assoc]

    -- expand the n choose 2 terms
    rw [Nat.choose_two_right]
    rw [Nat.choose_two_right]

    -- eliminate the denominator (left term)
    rw [show (2 * k + 5) * (2 * k + 5 - 1) = (2 * k + 5) * (2 * k + 4) by rfl]
    rw [show  (2 * k + 5) * (2 * k + 4) = 2 * (2 * k ^ 2 + 9 * k + 10) + 0 by ring]
    rw [Nat.mul_add_div]
    rw [Nat.zero_div]

    -- eliminate the denominator (right term)
    rw [show (2 * k + 4) * (2 * k + 4 - 1) = (2 * k + 4) * (2 * k + 3) by rfl]
    rw [show  (2 * k + 4) * (2 * k + 3) = 2 * (2 * k ^ 2 + 7 * k + 6) + 0 by ring]
    rw [Nat.mul_add_div]
    rw [Nat.zero_div]

    -- algebraic manipulation shows equality
    ring
    numbers
    numbers
