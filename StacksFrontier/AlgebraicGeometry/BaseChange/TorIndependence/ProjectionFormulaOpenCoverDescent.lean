module

public import
StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ProjectionFormulaOpenImmersionBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenCoverInvertibility
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The projection formula is local on the base: the descent from an open cover

Let `f : X ⟶ Y` be a morphism of schemes and let `U : ι → Y.Opens` be a family of opens covering
`Y`.  This file closes the localization argument of [Stacks, Tag 08EU] and [Stacks, Tag 08I9]
over such a cover: the projection-formula morphism of [Stacks, Tag 0B53] for `f`, and the
canonical morphism of [Stacks, Tag 08I9], are invertible as soon as the corresponding morphisms
for the restricted morphisms `f|_{U_i} : f^{-1}U_i ⟶ U_i` are, at the restricted complexes.

* *From the base to the cover.*  For a Cartesian square whose horizontal arrows are open
  immersions, invertibility of the restricted projection-formula map implies invertibility of the
  derived pullback of the unrestricted one.  That is
  `isIso_derivedPullback_map_projectionFormulaMap_of_isOpenImmersion` of
  `Stacks.Cohomology.DerivedProjectionFormula`,
  proved from the square of [Stacks, Tag 0B6B] and invertibility of the base-change map of
  [Stacks, Tag 08HY] along an open immersion.  The square used here is Mathlib's
  `AlgebraicGeometry.isPullback_morphismRestrict`.
* *From the cover back to the base.*  Invertibility in `D(𝒪_Y)` is local on an open cover of
  `Y`, which is
  `Stacks.Cohomology.DerivedOpenImmersion.isIso_of_isIso_derivedPullback_ofRestrict`.

For the canonical morphism of [Stacks, Tag 08I9] the passage between
`Rf_*𝒪_X ⊗^𝐋 K ⟶ Rf_*Lf^*K` and the projection-formula map at the source complex `𝒪_X[0]` is
`Stacks.Cohomology.DerivedProjectionFormula.isIso_pullbackPushforwardTensorMap`, and the
identification `Lg'^*(𝒪_X[0]) ≅ 𝒪_{X'}[0]` that the restricted statement needs is
`Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso`.

## Main results

* `Stacks.Cohomology.DerivedProjectionFormula.isIso_of_isIso_derivedPullback_opens`:
  invertibility in `D(𝒪_Y)` is local on a cover of a scheme by opens.
* `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_openCover`:
  **the projection-formula map of [Stacks, Tag 0B53] is invertible if it is invertible after
  restricting to each member of an open cover of the base**, for arbitrary complexes and an
  arbitrary morphism of schemes.
* `Stacks.Cohomology.DerivedProjectionFormula.isIso_pullbackPushforwardTensorMap_of_openCover`:
  **the same for the canonical morphism `Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*Lf^*K` of
  [Stacks, Tag 08I9]**, for an arbitrary `K` in `D(𝒪_Y)`.

## Relation to [Stacks, Tag 08I9]

The proof of [Stacks, Tag 08I9] has two steps: the question is local on the base, so one may
assume the base, and hence also `X`, affine; and the affine case follows from the descriptions of
`D_QCoh` and of `Lf^*` given by [Stacks, Tag 06Z0] and [Stacks, Tag 08DW].  The first step is
`isIso_pullbackPushforwardTensorMap_of_openCover`: for `f` affine and `U` a cover of `Y` by
affine opens, each `f|_{U_i}` is a morphism of affine schemes.  The affine case is
`AlgebraicGeometry.AffineProjectionFormula.isIso_pullbackPushforwardTensorMap_of_isAffine`, and
the two together are
`AlgebraicGeometry.AffineProjectionFormula.isIso_pullbackPushforwardTensorMap_unconditional`.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08I9](https://stacks.math.columbia.edu/tag/08I9)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B6B](https://stacks.math.columbia.edu/tag/0B6B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

universe u

namespace Stacks.Cohomology.DerivedProjectionFormula

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Invertibility in `D(𝒪_Y)` is local on a cover of a scheme by opens.**  This is
`Stacks.Cohomology.DerivedOpenImmersion.isIso_of_isIso_derivedPullback_ofRestrict` read at the
scheme spelling: the inclusion `U.ι` of an open subscheme is, as a morphism of ringed spaces,
the inclusion of the open subspace. -/
theorem isIso_of_isIso_derivedPullback_opens {ι : Type*} (U : ι → Y.Opens)
    (hU : ∀ y : Y, ∃ i, y ∈ U i)
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))}
    (a : K ⟶ L)
    (h : ∀ i, IsIso ((derivedPullback (U i).ι.toLRSHom.toShHom).map a)) :
    IsIso a :=
  Stacks.Cohomology.DerivedOpenImmersion.isIso_of_isIso_derivedPullback_ofRestrict
    Y.toRingedSpace U hU a h

/-- **The projection-formula morphism of [Stacks, Tag 0B53] is invertible as soon as it is after
restriction to the members of an open cover of the base.**

For an arbitrary morphism of schemes `f : X ⟶ Y`, arbitrary `E ∈ D(𝒪_X)` and `K ∈ D(𝒪_Y)`, and a
family of opens `U i` covering `Y`: if the projection-formula map for the restricted morphism
`f|_{U_i} : f^{-1}U_i ⟶ U_i` at the restricted complexes `Lg_i'^*E` and `Lg_i^*K` is invertible
for every `i`, then the projection-formula map for `f` at `E` and `K` is invertible.

This is the localization argument of the proof of [Stacks, Tag 08EU], over an open cover of the
base. -/
@[stacks 08EU "the localization argument of the source's proof, closed over an open cover: for \
an arbitrary morphism of schemes and arbitrary complexes, invertibility of the \
projection-formula map for f|_U at the restricted complexes, for U running through an open \
cover of the base, implies invertibility of the map for f; the affine case of the tag is NOT \
proved here, so the tag is not closed"]
theorem isIso_projectionFormulaMap_of_openCover {ι : Type*} (U : ι → Y.Opens)
    (hU : ∀ y : Y, ∃ i, y ∈ U i)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (h : ∀ i, IsIso (projectionFormulaMap (f ∣_ U i).toLRSHom.toShHom
      ((derivedPullback (f ⁻¹ᵁ U i).ι.toLRSHom.toShHom).obj E)
      ((derivedPullback (U i).ι.toLRSHom.toShHom).obj K))) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom E K) := by
  refine isIso_of_isIso_derivedPullback_opens U hU _ fun i => ?_
  exact isIso_derivedPullback_map_projectionFormulaMap_of_isOpenImmersion
    (f ⁻¹ᵁ U i).ι (f ∣_ U i) f (U i).ι (isPullback_morphismRestrict f (U i)).flip E K (h i)

/-- **The canonical morphism of [Stacks, Tag 08I9] is invertible as soon as it is after
restriction to the members of an open cover of the base.**

For an arbitrary morphism of schemes `f : X ⟶ Y`, an arbitrary `K ∈ D(𝒪_Y)` and a family of
opens `U i` covering `Y`: if

`R(f|_{U_i})_*𝒪_{f^{-1}U_i} ⊗^𝐋_{𝒪_{U_i}} Lg_i^*K ⟶ R(f|_{U_i})_*L(f|_{U_i})^*Lg_i^*K`

is invertible for every `i`, then `Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*Lf^*K` is invertible.

This is the first of the two steps of the proof of [Stacks, Tag 08I9]; with the affine case
`AlgebraicGeometry.AffineProjectionFormula.isIso_pullbackPushforwardTensorMap_of_isAffine` it
gives `AlgebraicGeometry.AffineProjectionFormula.isIso_pullbackPushforwardTensorMap_unconditional`.
-/
theorem isIso_pullbackPushforwardTensorMap_of_openCover {ι : Type*} (U : ι → Y.Opens)
    (hU : ∀ y : Y, ∃ i, y ∈ U i)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (h : ∀ i, IsIso (pullbackPushforwardTensorMap' (f ∣_ U i).toLRSHom.toShHom
      ((derivedPullback (U i).ι.toLRSHom.toShHom).obj K))) :
    IsIso (pullbackPushforwardTensorMap' f.toLRSHom.toShHom K) := by
  refine (isIso_pullbackPushforwardTensorMap f.toLRSHom.toShHom K).2 ?_
  refine isIso_projectionFormulaMap_of_openCover f U hU _ K fun i => ?_
  refine isIso_projectionFormulaMap_of_iso_left (f ∣_ U i).toLRSHom.toShHom
    (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso
      (f ⁻¹ᵁ U i).ι.toLRSHom.toShHom).symm _ ?_
  exact (isIso_pullbackPushforwardTensorMap (f ∣_ U i).toLRSHom.toShHom
    ((derivedPullback (U i).ι.toLRSHom.toShHom).obj K)).1 (h i)

end Stacks.Cohomology.DerivedProjectionFormula

end
