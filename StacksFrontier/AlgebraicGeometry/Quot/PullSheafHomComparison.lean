module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualSteps

/-!
# The canonical comparison of Stacks 08JF for algebraic spaces

Let `g : X ⟶ Y` be a morphism of algebraic spaces and `P`, `M` objects of `D(𝒪_Y)`.  Stacks 08JF
is the canonical map

`Lg^* R𝓗om(P, M) ⟶ R𝓗om(Lg^*P, Lg^*M)`,

the transpose, under the tensor–Hom adjunction of Stacks 08J8 on `X`, of

`Lg^* R𝓗om(P, M) ⊗^L Lg^*P ≅ Lg^*(R𝓗om(P, M) ⊗^L P) ⟶ Lg^*M`,

the inverse of the isomorphism of Stacks 07A4 followed by `Lg^*` of the evaluation map (the
counit of Stacks 08J8 on `Y`).  It is an isomorphism when `P` is perfect.

This file defines the map and names the invertibility as a proposition.

## Main definitions

* `AlgebraicGeometry.Space.pullSheafHomComparison`: the canonical map of Stacks 08JF, and
  `AlgebraicGeometry.Space.pullSheafHomComparisonTranspose` its transpose.
* `AlgebraicGeometry.Space.PullSheafHomComparisonIsIso`: **Stacks 08JF, the invertibility for a
  perfect source** (internal, pending), as a proposition.

## Main results

* `AlgebraicGeometry.Space.homEquiv_symm_pullSheafHomComparison`: the defining equation.

## References

* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The transpose of the map of Stacks 08JF under the tensor–Hom adjunction of Stacks 08J8:
`Lg^* R𝓗om(P, M) ⊗^L Lg^*P ≅ Lg^*(R𝓗om(P, M) ⊗^L P) ⟶ Lg^*M`, the inverse of the isomorphism of
Stacks 07A4 followed by `Lg^*` of the evaluation map. -/
def pullSheafHomComparisonTranspose {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    (P M : derivedModules B S hS Y) :
    ((smallEtaleDerivedTensor B S hS X).obj (((smallEtaleDerivedPullbackData B S hS).pull g).obj
        (((smallEtaleDerivedSheafHom B S hS Y).obj (Opposite.op P)).obj M))).obj
        (((smallEtaleDerivedPullbackData B S hS).pull g).obj P) ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull g).obj M :=
  (smallEtaleDerivedPullbackTensorIso g).inv.app
      (((smallEtaleDerivedSheafHom B S hS Y).obj (Opposite.op P)).obj M, P) ≫
    ((smallEtaleDerivedPullbackData B S hS).pull g).map
      ((smallEtaleDerivedTensorSheafHomAdjunction B S hS Y P).counit.app M)

/-- **The canonical map of Stacks 08JF** `Lg^* R𝓗om(P, M) ⟶ R𝓗om(Lg^*P, Lg^*M)` for a
morphism `g : X ⟶ Y` of algebraic spaces: the transpose, under the tensor–Hom adjunction of
Stacks 08J8 on `X`, of the inverse of the isomorphism of Stacks 07A4 followed by `Lg^*` of the
evaluation map `R𝓗om(P, M) ⊗^L P ⟶ M`
(`AlgebraicGeometry.Space.pullSheafHomComparisonTranspose`). -/
def pullSheafHomComparison {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    (P M : derivedModules B S hS Y) :
    ((smallEtaleDerivedPullbackData B S hS).pull g).obj
        (((smallEtaleDerivedSheafHom B S hS Y).obj (Opposite.op P)).obj M) ⟶
      ((smallEtaleDerivedSheafHom B S hS X).obj
          (Opposite.op (((smallEtaleDerivedPullbackData B S hS).pull g).obj P))).obj
        (((smallEtaleDerivedPullbackData B S hS).pull g).obj M) :=
  ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X
      (((smallEtaleDerivedPullbackData B S hS).pull g).obj P)).homEquiv _ _)
    (pullSheafHomComparisonTranspose g P M)

/-- **The defining equation of the map of Stacks 08JF**: its transpose under Stacks 08J8 is
`AlgebraicGeometry.Space.pullSheafHomComparisonTranspose`. -/
theorem homEquiv_symm_pullSheafHomComparison {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    (P M : derivedModules B S hS Y) :
    ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X
        (((smallEtaleDerivedPullbackData B S hS).pull g).obj P)).homEquiv _ _).symm
        (pullSheafHomComparison g P M) = pullSheafHomComparisonTranspose g P M := by
  unfold pullSheafHomComparison
  rw [Equiv.symm_apply_apply]

variable (B S hS)

/-- **Stacks 08JF, the invertibility for a perfect source** (internal, not yet proved here),
as a proposition: for every morphism `g : X ⟶ Y` of algebraic spaces, every
perfect `P` and every `M` in `D(𝒪_Y)`, the canonical map
`AlgebraicGeometry.Space.pullSheafHomComparison` `Lg^* R𝓗om(P, M) ⟶ R𝓗om(Lg^*P, Lg^*M)` is an
isomorphism. -/
def PullSheafHomComparisonIsIso : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) (P M : derivedModules B S hS Y),
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect P → IsIso (pullSheafHomComparison g P M)

end AlgebraicGeometry.Space

end
