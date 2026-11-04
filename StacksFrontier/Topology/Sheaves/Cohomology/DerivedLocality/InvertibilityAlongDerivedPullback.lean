module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedLocality.InvertibilityOnAnOpenCover
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction

/-!
# Invertibility in the derived category is local for the derived pullback to opens

Let `X` be a ringed space and let `U : ι → Opens X` be a family of opens with `⨆ i, U i = ⊤`.  A
morphism of `D(𝒪_X)` whose *derived pullback* along the inclusion `j_{U i} : (U i, 𝒪_X|_{U i}) ⟶ X`
of each member is invertible is itself invertible.

## Main results

* `Stacks.Cohomology.isIso_of_isIso_derivedPullback_ofRestrict`: the statement above.

## Implementation notes

This is the `derivedPullback` spelling of
`Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map`, which is stated for the
restriction functor `ExtensionByZeroModules.jStar`.  The two agree: restriction is exact, so it is
its own left derived functor, and pullback along the inclusion of an open subspace *is*
restriction — that identification is
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso`, which also pays the
crossing between the two spellings `structureSheafRing (X.restrict U.isOpenEmbedding)` and
`ExtensionByZeroModules.resRing U (structureSheafRing X)` of the structure sheaf of the open
subspace.  Invertibility transports along an isomorphism of functors by
`CategoryTheory.NatIso.isIso_map_iff`, so nothing is reproved.

Everything is at `HasDerivedCategory.standard`, the model
`Stacks.Cohomology.DerivedOpenImmersion` and the derived pullback of [Stacks, Tag 079W] are
stated at.  The index type is arbitrary and no hypothesis is placed on `X` or on the two objects.

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard

/-- **Invertibility in `D(𝒪_X)` is local for the derived pullback to the members of an open
cover.**  If `⨆ i, U i = ⊤` and the derived pullback of `φ` along the inclusion of each `U i` is
invertible, then `φ` is invertible. -/
theorem isIso_of_isIso_derivedPullback_ofRestrict {X : AlgebraicGeometry.RingedSpace.{u, u}}
    {ι : Type*} (U : ι → Opens X.carrier) (hU : iSup U = ⊤)
    {E F : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (φ : E ⟶ F)
    (h : ∀ i, IsIso ((derivedPullback (X.ofRestrict (U i).isOpenEmbedding)).map φ)) :
    IsIso φ :=
  isIso_of_isIso_jStar_mapDerivedCategory_map (structureSheafRing X) U hU φ fun i =>
    (NatIso.isIso_map_iff
      (DerivedOpenImmersion.derivedPullbackOpenRestrictionIso X (U i)) φ).mp (h i)

end Stacks.Cohomology

end
