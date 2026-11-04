module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.CompactPerfect
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AnyModel.RestrictAndPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.StructureSheafCompactObject
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedDirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPerfectHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.PerfectSheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.RestrictionPerfectSupport
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineSheafPerfectHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.RestrictionOfPerfectObjects
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCohomologyComparisonSupplement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.PerfectObjectsAreCompact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DirectSumsOnARingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDualGlobalFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualityPairing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSiteComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSiteComparisonSupplement

/-!
# A perfect object of `D_QCoh(𝒪_X)` is compact, at an arbitrary model

Let `X` be a quasi-compact quasi-separated scheme. [Stacks, Tag 09M1] asserts that an object of
`D_QCoh(𝒪_X)` is compact if and only if it is perfect as an object of `D(𝒪_X)`. That statement
is `Stacks.Duality.isCompactObject_iff_isPerfect` (with its directions
`Stacks.Duality.isPerfect_of_isCompactObject` and `Stacks.Duality.isCompactObject_of_isPerfect`),
read at the locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` of the
derived category.

This file transports the implication from perfectness to compactness to an arbitrary chosen
model of `D(𝒪_X)`, which is where the supported compact-generation results of this directory use
it.

## Main results

* `AlgebraicGeometry.isCompactObject_of_isPerfect`: a perfect object of `D_QCoh(𝒪_X)` is compact,
  at an arbitrary chosen model.

## Implementation notes

Compactness travels along the comparison equivalence
`StacksDraft.DerivedModel.derivedCategoryBModelEquiv` of the two readings of `D_QCoh(𝒪_X)`, by
`CategoryTheory.isCompactObject_iff_isCompactObject_obj`, and perfectness travels along the
comparison equivalence of the two readings of `D(𝒪_X)`, by
`Stacks.DerivedQCoh.AnyModel.isPerfect_modelEquiv_iff`.

## References

* [Stacks Project, Proposition 36.17.1 (09M1)](https://stacks.math.columbia.edu/tag/09M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u w

namespace AlgebraicGeometry

section AnyModel

variable (X : Scheme.{u}) [hX : HasDerivedCategory.{u} (SheafOfModules.{u} X.ringCatSheaf)]

/-- The chosen derived category of `SheafOfModules X.ringCatSheaf`, read at the
`StrictlyPerfect.OXMod` spelling in which perfectness is stated. -/
local instance hasDerivedCategoryOxModAnyModel : HasDerivedCategory.{u}
    (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) :=
  Stacks.DerivedQCoh.hasDerivedCategoryOxMod X hX

/-- The chosen derived category of `SheafOfModules X.ringCatSheaf`, read at the
`AlgebraicGeometry.Scheme.Modules` spelling, at which the comparison equivalence of two models
of `D_QCoh(𝒪_X)` is formed. -/
local instance hasDerivedCategoryModulesAnyModel : HasDerivedCategory.{u} X.Modules := hX

/-- Quasi-coherence is closed under isomorphism, at the `X.Modules` spelling of the
`𝒪_X`-modules. Reinstated here because the comparison equivalence of two models of
`D_QCoh(𝒪_X)` is formed at that spelling. -/
local instance isClosedUnderIsomorphisms_isQuasicoherentAnyModel :
    (show ObjectProperty X.Modules from
      SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderIsomorphisms where
  of_iso {_ _} e h := ObjectProperty.prop_of_iso
    (show ObjectProperty (SheafOfModules.{u} X.ringCatSheaf) from
      SheafOfModules.isQuasicoherent X.ringCatSheaf) e h

/-- The comparison equivalence between two readings of `D_QCoh(𝒪_X)` is additive
(`StacksDraft.DerivedModel.derivedCategoryBModelEquiv_functor_additive`), as an instance at the
`X.Modules` spelling at which it is formed here. -/
instance derivedCategoryBModelEquiv_isQuasicoherent_functor_additive
    (h₁ : HasDerivedCategory.{w} X.Modules) (h₂ : HasDerivedCategory.{u} X.Modules) :
    (StacksDraft.DerivedModel.derivedCategoryBModelEquiv (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) h₁ h₂).functor.Additive :=
  StacksDraft.DerivedModel.derivedCategoryBModelEquiv_functor_additive _ h₁ h₂

/-- **A perfect object of `D_QCoh(𝒪_X)` is compact, at an arbitrary model.** Let `X` be a
quasi-compact quasi-separated scheme and let `K` be an object of `D_QCoh(𝒪_X)` which is perfect as
an object of `D(𝒪_X)`. Then `K` is a compact object of `D_QCoh(𝒪_X)`.

This is [Stacks, Tag 09M1], `Stacks.Duality.isCompactObject_of_isPerfect` at the locally small
model, transported to the chosen model: compactness travels along the comparison equivalence of
the two readings of `D_QCoh(𝒪_X)`, by `CategoryTheory.isCompactObject_iff_isCompactObject_obj`,
and perfectness travels along the comparison equivalence of the two readings of `D(𝒪_X)`, by
`Stacks.DerivedQCoh.AnyModel.isPerfect_modelEquiv_iff`. -/
theorem isCompactObject_of_isPerfect [CompactSpace X] [QuasiSeparatedSpace X]
    (K : (Stacks.Duality.derivedQuasiCoherent X).FullSubcategory)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K.obj) :
    IsCompactObject.{u} K := by
  let E := StacksDraft.DerivedModel.derivedCategoryBModelEquiv (A := X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf) (hasDerivedCategoryModulesAnyModel X)
    (Scheme.Modules.hasDerivedCategory X)
  have hperf := (Stacks.DerivedQCoh.AnyModel.isPerfect_modelEquiv_iff
      (Stacks.DerivedQCoh.hasDerivedCategoryOxMod X hX)
      (Stacks.DerivedQCoh.hasDerivedCategoryOxMod X (Scheme.Modules.hasDerivedCategory X))
      K.obj).1 hK
  exact (isCompactObject_iff_isCompactObject_obj E.functor K).2
    (Stacks.Duality.isCompactObject_of_isPerfect (h := Scheme.Modules.hasDerivedCategory X)
      (E.functor.obj K) hperf)

end AnyModel

end AlgebraicGeometry

end
