module

public import Mathlib.AlgebraicGeometry.Artinian
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms from spectra of Artinian rings

Every morphism from the spectrum of an Artinian ring to an arbitrary scheme is an affine
morphism.

## Main results

* `AlgebraicGeometry.isAffineHom_of_isArtinianRing` states that a morphism whose source is the
  spectrum of an Artinian ring is affine.

## Implementation notes

Affineness of a morphism is expressed by the typeclass `AlgebraicGeometry.IsAffineHom`. The
proof uses that the spectrum of an Artinian ring is a finite discrete space, so the preimage of
any open is finite and hence affine.

## References

* [Stacks Project, Tag 01SI](https://stacks.math.columbia.edu/tag/01SI)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 01SI.** Every morphism from the spectrum of an
Artinian ring to a scheme is affine. -/
@[stacks 01SI]
lemma isAffineHom_of_isArtinianRing {A : CommRingCat.{u}} [IsArtinianRing A]
    {S : Scheme.{u}} (f : Spec A ⟶ S) : IsAffineHom f := by
  refine ⟨fun U _ ↦ ?_⟩
  have : Finite (f ⁻¹ᵁ U) := .of_injective Subtype.val Subtype.val_injective
  exact (inferInstance : IsAffine (f ⁻¹ᵁ U))

end AlgebraicGeometry
