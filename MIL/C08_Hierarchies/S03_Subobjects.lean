import MIL.Common
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit true


@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' _ _ := Submonoid₁.ext



example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N


example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property


instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))


example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)


class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem

@[ext]
class Subgroup₁ (G : Type) [Group G] extends Submonoid₁ G where
  mem_inv : ∀ {a : G}, a ∈ carrier → a⁻¹ ∈ carrier

instance [Group G] : SetLike (Subgroup₁ G) G where
  coe H := H.toSubmonoid₁.carrier
  coe_injective' _ _ := Subgroup₁.ext

instance [Group G] : SubmonoidClass₁ (Subgroup₁ G) G where
  mul_mem s := s.toSubmonoid₁.mul_mem
  one_mem s := s.toSubmonoid₁.one_mem

instance [Monoid M] : Min (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩


example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P


def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      rintro x y z ⟨w₁, w₁n, z₁, z₁n, p⟩ ⟨w₂, w₂n, z₂, z₂n, q⟩
      use w₁ * w₂; constructor; exact N.mul_mem w₁n w₂n
      . use z₁ * z₂; constructor; exact N.mul_mem z₁n z₂n
        calc x * (w₁ * w₂) = y * (z₁ * w₂) := by rw [←mul_assoc x, p, mul_assoc]
            _              = y * (w₂ * z₁) := by rw [mul_comm z₁]
            _              = z * (z₁ * z₂) := by rw [←mul_assoc, q, mul_assoc, mul_comm z₂]
  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂' (· * ·) (by
      rintro x₁ x₂ ⟨wx, wxn, zx, zxn, p⟩ y₁ y₂ ⟨wy, wyn, zy, zyn, q⟩
      refine ⟨wx * wy, N.mul_mem wxn wyn, zx * zy, N.mul_mem zxn zyn, ?_⟩
      dsimp
      rw [mul_comm x₁, mul_assoc y₁, ← mul_assoc x₁, p, mul_comm y₁]
      rw [mul_assoc x₂, mul_assoc x₂, mul_assoc zx, mul_comm wy, q]
      rw [mul_comm zx, mul_assoc, mul_comm zy, mul_assoc]
        )
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; apply Quotient.eq.mpr; dsimp
    rw [mul_assoc]
  one := QuotientMonoid.mk N 1
  one_mul := by
      rintro ⟨a⟩; apply Quotient.eq.mpr; dsimp
      rw [one_mul]
  mul_one := by
      rintro ⟨a⟩; apply Quotient.eq.mpr; dsimp
      rw [mul_one]
