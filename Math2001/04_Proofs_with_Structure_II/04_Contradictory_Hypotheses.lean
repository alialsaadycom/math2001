/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init


example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!


example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h


example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  -- the case `1 < m`
  have h2 : m ≤ p := Nat.le_of_dvd hp' hmp
  obtain h2m | h2m_left : m = p ∨ m < p := eq_or_lt_of_le h2
  . --the case `m = p`
    right
    apply h2m
  . --the case `m < p`

    sorry -- how do I do this???











example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  have hcases : a ≤ 2 ∨ a ≥ 3 := le_or_succ_le a 2
  obtain hcase1 | hcase2 := hcases
  . have bcases : b ≤ 1 ∨ b ≥ 2 := le_or_succ_le b 1
    interval_cases a
    obtain bcase1 | bcase2 := bcases
    . interval_cases b
      sorry



  . apply hcase2

/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  sorry

example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  sorry

example : Prime 7 := by
  sorry

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  sorry

namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  sorry

example {n : ℕ} : n ≥ 2 → (∃ p, n = p ^ 2) → ¬ Prime n := by
intro q r
obtain ⟨s, u⟩ := r
have h1 : s > 1 := by
  have :=
    calc
      s ^ 2 = n := by addarith [u]
      _ > 1 := by addarith [q]
      _ = 1 ^ 2 := by numbers
  cancel 2 at this
apply not_prime s s
. exact Nat.ne_of_gt h1
. apply Nat.ne_of_lt
  rw [u]
  obtain t | t := le_or_gt s 1
  . interval_cases s
  . calc
      _ = s * 1 := by ring
      _ < s * s := by rel [t]
      _ = _ := by ring
. rw [u]
  ring

  example : ¬ (∃ p : ℕ, p > 2 ∧ p ^ 2 ∣ 15) := by
  intro h
  obtain ⟨n, hnl, hnr⟩ := h
  have h1 : n < 4 := by
    have h2 : n ^ 2 < 4 ^ 2 :=
      calc
        n ^ 2 ≤ 15 := by apply Nat.le_of_dvd
                         . numbers
                         . exact hnr
        _ < 4 ^ 2 := by numbers
    cancel 2 at h2
  interval_cases n
  obtain ⟨k, hk⟩ := hnr
  obtain h1 | h2 := le_or_succ_le k 1
  · have h :=
    calc 15 = 3 ^ 2 * k := hk
      _ ≤ 3 ^ 2 * 1 := by rel[h1]
    numbers at h
  · have h :=
    calc 15 = 3 ^ 2 * k := hk
      _ ≥ 3 ^ 2 * 2 := by rel[h2]
    numbers at h

example : ∃! a : ℕ, a ^ 2 + a = 2 := by
  use 1
  dsimp
  constructor
  . numbers
  intro a ha
    obtain h | h := le_or_gt a 1
      interval_cases a
      . numbers at ha
      . numbers
  . have :=
      calc
        a ^ 2 + a > 1 ^ 2 + 1 := by rel [h]
        _ = 2 := by numbers
    -- missing line 4
    -- missing line 5
