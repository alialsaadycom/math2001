import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

open BigOperators

theorem A.Q2 (n : ℕ) : ∑ i in Finset.Ioc 0 n, (2 * i) ^ 2 = (2 * n + 2).choose 3 := by
  simple_induction n with k IH
  . -- base case
    rw [@Finset.Ioc_self]
    rw [@Finset.sum_empty]
    dsimp[Nat.choose]
  . -- inductive step
    rw [Finset.sum_Ioc_succ_top]
    rw [IH]


    -- rw [Nat.choose_eq_factorial_div_factorial]
    -- rw [Nat.factorial_succ]
    -- calc
    -- (2 * k + 1 + 1) * Nat.factorial (2 * k + 1) / (Nat.factorial 3 * Nat.factorial (2 * k + 2 - 3)) + (2 * (k + 1)) ^ 2 = (2 * k + 1 + 1) * ((2 * k + 1) * Nat.factorial (2 * k)) / (Nat.factorial 3 * Nat.factorial (2 * k + 2 - 3)) +
    -- (2 * (k + 1)) ^ 2 := by extra
