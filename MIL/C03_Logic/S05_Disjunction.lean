import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg h]
  . rw [abs_of_neg h]; linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg h]; linarith
  . rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  . rw [abs_of_nonneg h]; exact add_le_add (le_abs_self x) (le_abs_self y)
  . rw [abs_of_neg h]
    rw [neg_add x y]
    exact add_le_add (neg_le_abs_self x) (neg_le_abs_self y)

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  . intro xltabsy
    rcases le_or_gt 0 y with h | h
    . rw [abs_of_nonneg h] at xltabsy; left; assumption
    . rw [abs_of_neg h] at xltabsy; right; assumption
  . rintro (xlty | xlt_negy)
    . exact lt_of_lt_of_le xlty (le_abs_self y)
    . exact lt_of_lt_of_le xlt_negy (neg_le_abs_self y)

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rw [neg_lt]
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg h]
    rw [and_comm, iff_self_and]
    intro; linarith
  . rw [abs_of_neg h]
    rw [iff_self_and]
    intro; linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x,y, (p | p)⟩ <;> (rw [p]; positivity)


example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  rw [←sub_eq_zero] at h
  have : x^2 - 1 = (x - 1) * (x + 1) := by ring
  rw [this] at h
  have : x - 1 = 0 ∨ x + 1 = 0 := mul_eq_zero.mp h
  rw [sub_eq_zero, ←eq_neg_iff_add_eq_zero] at this
  exact this

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  rw [←sub_eq_zero] at h
  have : x^2 - y^2 = (x - y) * (x + y) := by ring
  rw [this] at h
  have : x - y = 0 ∨ x + y = 0 := mul_eq_zero.mp h
  rw [sub_eq_zero, ←eq_neg_iff_add_eq_zero] at this
  exact this

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  rw [←sub_eq_zero] at h
  have : x^2 - 1 = (x - 1) * (x + 1) := by ring
  rw [this] at h
  have : x - 1 = 0 ∨ x + 1 = 0 := mul_eq_zero.mp h
  rw [sub_eq_zero, ←eq_neg_iff_add_eq_zero] at this
  exact this


example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  rw [←sub_eq_zero] at h
  have : x^2 - y^2 = (x - y) * (x + y) := by ring
  rw [this] at h
  have : x - y = 0 ∨ x + y = 0 := mul_eq_zero.mp h
  rw [sub_eq_zero, ←eq_neg_iff_add_eq_zero] at this
  exact this

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  . rintro h
    by_cases h' : P
    . right; exact h h'
    . left; assumption
  . rintro (hnotP | Q)
    . intro; contradiction
    . intro; assumption
