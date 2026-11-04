module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffine

/-!
# Quasi-compact immersions are quasi-affine

A quasi-compact immersion of schemes is a quasi-affine morphism: the inverse image of an affine
open subscheme of the target is an open subscheme of a quasi-compact immersion into an affine
scheme, hence quasi-affine.

## Main results

* `AlgebraicGeometry.isQuasiAffineHom_of_isImmersion_of_quasiCompact`: every quasi-compact
  immersion of schemes is quasi-affine.

## Implementation notes

The result is registered as an instance, so quasi-affineness of a quasi-compact immersion is
available to typeclass inference.

## References

* [Stacks Project, Tag 02JR](https://stacks.math.columbia.edu/tag/02JR)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 02JR.** Every quasi-compact immersion of schemes is
quasi-affine. -/
@[stacks 02JR]
instance isQuasiAffineHom_of_isImmersion_of_quasiCompact
    {X S : Scheme.{u}} (f : X ⟶ S) [IsImmersion f] [QuasiCompact f] :
    IsQuasiAffineHom f := by
  refine ⟨fun U hU => ?_⟩
  have : IsAffine U.toScheme := hU
  have : CompactSpace (f ⁻¹ᵁ U).toScheme := QuasiCompact.compactSpace_of_compactSpace (f ∣_ U)
  exact Scheme.IsQuasiAffine.of_isImmersion (f ∣_ U)

end AlgebraicGeometry
