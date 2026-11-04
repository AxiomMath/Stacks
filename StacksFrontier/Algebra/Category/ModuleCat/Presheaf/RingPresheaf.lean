module

public import Mathlib.Algebra.Category.Ring.Basic

/-!
# The presheaf of rings underlying a presheaf of commutative rings

A presheaf of modules is indexed by a presheaf of rings, while the tensor product of two of its
sections needs the ring to be commutative. This file defines the presheaf of rings obtained by
composing a presheaf of commutative rings with the forgetful functor to rings, and records a
congruence lemma for scalar multiplication.

## Main definitions

* `Stacks.ringPresheaf`: the underlying presheaf of rings of a presheaf of commutative rings.
  It is also available as `Stacks.PresheafOfRings.ringPresheaf` and as
  `AlgebraicGeometry.SheafOfModules.ringPresheaf`.

## Main results

* `Stacks.smul_congr_left`: equal scalars act equally.
-/

@[expose] public section

open CategoryTheory

universe v u w

namespace Stacks

variable {C : Type u} [Category.{v} C]

/-- The underlying presheaf of rings of a presheaf of commutative rings. -/
abbrev ringPresheaf (O : Cᵒᵖ ⥤ CommRingCat.{w}) : Cᵒᵖ ⥤ RingCat.{w} :=
  O ⋙ forget₂ CommRingCat RingCat

/-- Equal scalars act equally. -/
theorem smul_congr_left {A : Type*} {N : Type*} [SMul A N] {a b : A} (h : a = b) (x : N) :
    a • x = b • x :=
  congrArg (fun c : A => c • x) h

end Stacks

namespace Stacks.PresheafOfRings

/-! `Stacks.PresheafOfRings.ringPresheaf` is an alias of `Stacks.ringPresheaf`. -/
export _root_.Stacks (ringPresheaf)

end Stacks.PresheafOfRings

namespace AlgebraicGeometry.SheafOfModules

/-! `AlgebraicGeometry.SheafOfModules.ringPresheaf` is an alias of `Stacks.ringPresheaf`. -/
export Stacks (ringPresheaf)

end AlgebraicGeometry.SheafOfModules
