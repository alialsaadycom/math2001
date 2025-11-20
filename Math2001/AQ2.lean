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


    rw[succ_zero_eq_one]
    rw[succ_eq_plus_one]
    rw[succ_eq_plus_one]
    rw [Nat.choose_eq_factorial_div_factorial]

    have factorial_eq_succ_mul (n b : ℕ): Nat.factorial (2 * Nat.succ (n) + b) = Nat.factorial (2 * Nat.succ (n) + b - 1) * (2 * Nat.succ (n) + b) := by
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

    have factorial_eq_succ_mul' (n : ℕ): Nat.factorial (2 * Nat.succ (n)) = Nat.factorial (2 * Nat.succ (n) - 1) * (2 * Nat.succ (n)) := by
      have : Nat.factorial (2 * Nat.succ (n)) = Nat.factorial (2 * Nat.succ (n) + 0) := by ring
      rw [this]
      rw [factorial_eq_succ_mul]
      ring

    rw[factorial_eq_succ_mul]
    rw [Nat.succ_sub_one]
    rw[factorial_eq_succ_mul]
    rw [Nat.succ_sub_one]
    rw[factorial_eq_succ_mul']



    dsimp[Nat.factorial]

    sorry








    have : 3 ≤ 2 * (k + 1) + 2 := by
      calc
      2 * (k + 1) + 2 ≥ 2 * (0 + 1) + 2 := by rel[Nat.zero_le k]
      _ = 2 + 2 := by numbers
      _ ≥ 3 := by numbers
    apply this


    -- rw [Nat.choose_eq_factorial_div_factorial]


    -- have h1 (n : ℕ): Nat.factorial (2 * Nat.succ (n)) = Nat.factorial (2 * Nat.succ (n) - 1) * (2 * Nat.succ (n)) := by
    --   simple_induction n with k IH
    --   .
    --     dsimp [Nat.factorial]
    --   .
    --     rw [Nat.succ_mul]
    --     rw [Nat.add_succ_sub_one]

    --     sorry















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
