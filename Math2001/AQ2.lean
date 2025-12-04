import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Basic
import Library.Basic

math2001_init

open BigOperators

theorem A.Q2 (n : ℕ) : ∑ i in Finset.range (n + 1), (2 * i) ^ 2 = (2 * n + 2).choose 3 := by
  simple_induction n with k IH
  . -- base case
    rw [@Finset.sum_range_add]
    dsimp [Nat.succ]
    rw [@Finset.sum_singleton]
    dsimp[Nat.choose]
    numbers
  . -- inductive step

    -- identity (n + 1) choose (k + 1) = (n choose k) + (n choose (k + 1))
    rw [show Nat.choose (2 * (k + 1) + 2) 3 = Nat.choose (2 * (k + 1) + 1) 2 + Nat.choose (2 * (k + 1) + 1) 3 by rw[Nat.choose_succ_succ]]
    rw [show Nat.choose (2 * (k + 1) + 1) 3 = Nat.choose (2 * (k + 1)) 2 + Nat.choose (2 * (k + 1)) 3 by rw[Nat.choose_succ_succ]]

    -- identity n choose 2 = n(n - 1)/2
    rw [Nat.choose_two_right]
    rw [Nat.choose_two_right]

    -- eliminate the denominator in proof goal (first term)
    rw [show (2 * (k + 1) + 1) * (2 * (k + 1) + 1 - 1) = (2 * k + 3) * (2 * k + 2) by rfl]
    rw [show  (2 * k + 3) * (2 * k + 2) = 2 * (2 * k ^ 2 + 5 * k + 3) + 0 by ring]
    rw [Nat.mul_add_div]
    rw [Nat.zero_div]

    -- eliminate the denominator in proof goal (second term)
    rw [show 2 * (k + 1) * (2 * (k + 1) - 1) = (2 * k + 2) * (2 * k + 1) by rfl]
    rw [show  (2 * k + 2) * (2 * k + 1) = 2 * (2 * k ^ 2 + 3 * k + 1) + 0 by ring]
    rw [Nat.mul_add_div]
    rw [Nat.zero_div]

    -- substitute in the inductive hypothesis
    rw [@Finset.sum_range_add]
    rw [@Finset.sum_range_one]
    rw [IH]
    rw [show 2 * k + 2 = 2 * (k + 1) by rfl]

    -- algebraic manipulation shows equality
    ring
    numbers
    numbers
