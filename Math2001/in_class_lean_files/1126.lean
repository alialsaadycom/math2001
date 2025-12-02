import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init

open Set


example : { n : ℤ | Int.Odd n}ᶜ = { n : ℤ | Int.Even n } := by
  ext n
  dsimp
  symm
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
      calc 0 ≡ n [ZMOD 2] := by rel [h1]
        _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction


example : ¬{ n : ℕ | 1800 ≤ n} ∈ { S : Set ℕ | ∀ a : ℕ, a ∈ S → 2 ∣ a} := by
  by_contra H
  dsimp at H
  have h1 : 1800 ≤ 1801 := by numbers
  have h2 := H 1801 h1
  have h3 : ¬2 ∣ 1801 := by
    apply Nat.not_dvd_of_exists_lt_and_lt
    use 900
    exact ⟨ by numbers, by numbers ⟩
  contradiction


def S : Set ℕ := {1, 2, 4}

def T : Set (Set ℕ) := { S, ∅ }

def U : Set (Set (Set ℕ)) := { T, {∅}, {S} }


-- 9.2.2
example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  constructor
  · intro h
    obtain (h | h) | (h | h) := h
    · left
      apply h
    · right
      left
      apply h
  -- and much, much more
    · sorry
    · sorry
  · sorry

-- alternate proof using the `exhaust` tactic
example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  exhaust
