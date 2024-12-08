import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n ngtMax
  have ngtNs : n ≥ Ns := (le_max_left Ns Nt).trans ngtMax
  have ngtNt : n ≥ Nt := (le_max_right Ns Nt).trans ngtMax
  calc |s n + t n - (a + b)|
       _ = |(s n - a) + (t n  - b)| := by congr; abel
       _ ≤ |s n - a| + |t n - b| := abs_add_le _ _
       _ < ε := by linarith [hs n ngtNs, ht n ngtNt]

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε ε_pos
  rcases cs (ε / |c|) (by positivity) with ⟨N, hN⟩
  use N; intro n ngtN
  have sn_near_a : |s n - a| < ε / |c| := hN n ngtN
  dsimp
  calc |c * s n - c * a|
    _ = |c * (s n - a)| := by congr; ring
    _ = |c| * |s n - a| := abs_mul _ _
    _ < |c| * (ε / |c|) := (mul_lt_mul_left acpos).mpr sn_near_a
    _ = ε               := mul_div_cancel₀ _ (ne_of_lt acpos).symm


theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n nleN
  calc
        |s n|
        _ = |s n - a + a|   := by congr; abel
        _ ≤ |s n - a| + |a| := abs_add_le _ _
        _ < |a| + 1         := by linarith [h n nleN]

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos

  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  let N := max N₀ N₁
  use N; intro n ngtN
  have abs_sn_ltB : |s n| < B := h₀ n ((le_max_left _ _).trans ngtN)
  have abs_tn_εdivB : |t n| < ε / B := by
    convert h₁ n ((le_max_right _ _).trans ngtN)
    rw [sub_zero]
  rw [sub_zero]
  calc
    |s n * t n|
    _ = |s n| * |t n| := abs_mul _ _
    _ < B * (ε / B)  := by
      apply mul_lt_mul'
      . exact (le_of_lt abs_sn_ltB)
      . exact abs_tn_εdivB
      . apply abs_nonneg
      . exact Bpos
    _ = ε            := mul_div_cancel₀ ε (ne_of_lt Bpos).symm

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by exact abs_sub_pos.mpr abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := div_pos this (by norm_num)
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_max_left Na Nb)
  have absb : |s N - b| < ε := hNb N (le_max_right Na Nb)
  have : |a - b| < |a - b| :=
    calc |a - b|
         _ ≤ |s N - a| + |s N - b| := dist_triangle_left a b (s N)
         _ < ε + ε                 := add_lt_add absa absb
         _ = 2 * ε                 := by ring
         _ = |a - b|               := mul_div_cancel₀ |a - b| (by norm_num)
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
