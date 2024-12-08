import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  . rintro fs_in_v x xs
    exact fs_in_v ⟨x, xs, refl (f x)⟩
  . rintro s_in_fpbv
    rintro y ⟨x, xs, rfl⟩
    exact s_in_fpbv xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rw [preimage_subset_iff]
  rintro a ⟨a', a's, fa'eqfa⟩
  rw [←h fa'eqfa]; assumption

example : f '' (f ⁻¹' u) ⊆ u := by
  rw [image_subset_iff];

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, rfl⟩
  exact ⟨x, yu, refl (f x)⟩

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, xs, p⟩
  exact ⟨x, h xs, p⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  rintro x fx_in_u
  exact h fx_in_u

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  apply Subset.antisymm
  . rw [preimage_subset_iff]
    rintro a (fau | fav)
    . left; exact fau
    . right; exact fav
  . rintro a (fau | fav)
    . exact Or.inl fau
    . exact Or.inr fav

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rw [image_subset_iff, preimage_inter];
  rintro x ⟨xs, xt⟩
  exact ⟨⟨x, xs, refl _⟩, ⟨x, xt, refl _⟩⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x₁, x₁s, fx₁eqy⟩, ⟨x₂, x₂t, fx₂eqy⟩⟩
  have : x₁ = x₂ := h (fx₁eqy.trans fx₂eqy.symm)
  have x₁t : x₁ ∈ t := by convert x₂t
  exact ⟨x₁, ⟨x₁s, x₁t⟩, fx₁eqy⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x, xs, fxeqy⟩, ynotinft⟩
  exact ⟨x, ⟨xs, fun xt ↦ ynotinft ⟨x, xt, fxeqy⟩⟩, fxeqy⟩

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := refl _

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  apply Subset.antisymm
  . rintro y ⟨⟨x, xs, fxeqy⟩, yv⟩
    exact ⟨x, ⟨xs, fxeqy.symm.subst yv⟩, fxeqy⟩
  . rw [image_subset_iff]; simp only [preimage_inter]
    apply inter_subset_inter;
    . rw [←image_subset_iff]
    rfl

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rw [image_subset_iff, preimage_inter]
  apply inter_subset_inter
  . rw [←image_subset_iff]
  rfl

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rw [←image_subset_iff]
  exact (image_inter_preimage f s u).le

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rw [preimage_union]
  apply union_subset_union_left
  apply subset_preimage_image

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  apply Subset.antisymm
  . rw [image_subset_iff, iUnion_subset_iff]
    intro i; rw [←image_subset_iff]
    exact subset_iUnion (fun i ↦ f '' A i) i
  . rw [iUnion_subset_iff]; intro i
    apply image_mono
    apply subset_iUnion

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro y ⟨x, xiInter, fxeqy⟩
  simp; simp at xiInter
  intro i; exact ⟨x, xiInter i, fxeqy⟩

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  rintro y yiInter_fAi; simp at yiInter_fAi
  rcases yiInter_fAi i with ⟨x, _, fxeqy⟩
  use x; constructor
  . simp; intro i'
    rcases yiInter_fAi i' with ⟨x', x'iAi', fx'eqy⟩
    have : x = x' := injf (fxeqy.trans fx'eqy.symm)
    convert x'iAi'
  . exact fxeqy

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  apply Subset.antisymm
  . rw [preimage_subset_iff]; intro a; intro faiUnionB
    simp at *; exact faiUnionB
  . rw [iUnion_subset_iff]; intro i
    apply preimage_mono; apply subset_iUnion

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  apply Subset.antisymm
  . simp; intro i
    apply preimage_mono; apply iInter_subset
  . rw [←image_subset_iff, subset_iInter_iff]
    intro i; rw [image_subset_iff]
    apply iInter_subset

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x₁ x₁geq0 x₂ x₂geq0
  intro p
  simp at *
  rw [←sq_sqrt x₁geq0, ←sq_sqrt x₂geq0, p]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x₁ x₁geq0 x₂ x₂geq0
  intro p
  simp at *
  rw [←sqrt_sq x₁geq0, ←sqrt_sq x₂geq0, p]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; constructor
  . rintro ⟨x, _, rfl⟩
    apply sqrt_nonneg
  . intro ynonneg
    use y ^ 2
    simp at *
    constructor
    positivity
    rw [sqrt_sq ynonneg]

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y; constructor
  . rintro ⟨x, rfl⟩
    dsimp; apply sq_nonneg
  . rintro ynonneg
    use sqrt y; simp
    rw [sq_sqrt ynonneg]
end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  . intro injf
    intro x
    have : f (inverse f (f x)) = f x :=
      inverse_spec (f x) ⟨x, refl _⟩
    exact injf this
  . intro flinv
    intro x₁ x₂ p
    have : (inverse f) (f x₁) = (inverse f) (f x₂) :=
      congrArg (inverse f) p
    rw [flinv x₁, flinv x₂] at this
    exact this

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  . intro surjf
    intro y
    apply inverse_spec
    rcases surjf y with ⟨x, rfl⟩
    exact ⟨x, refl _⟩
  . rintro rinvf
    intro y
    use (inverse f) y
    rw [rinvf y]
end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by
    intro h'
    rw [←h] at h'
    contradiction
  contradiction

-- COMMENTS: TODO: improve this
end
