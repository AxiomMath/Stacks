module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.QuasicoherentSupportedComplexes

/-!
# Quasi-coherence of the local cohomology sheaves, degree by degree

Let `X` be a scheme, `T ⊆ X` a closed subset whose open complement is retrocompact, and
`i : T → X` the inclusion.  [Stacks, Tag 0G7G] (1) says that `i_*R𝓗_T` carries `D_QCoh(𝒪_X)`
into itself;
`Stacks.Perfect.SupportedQuasicoherent.derivedQuasiCoherent_derivedSupportedPushforward` is that
statement.  This file reads it in a single degree, at a module rather than a complex:

`i_*ℋⁿ_T(ℱ)` is a quasi-coherent `𝒪_X`-module, for every quasi-coherent `ℱ` and every `n`.

## Main definitions

* `Stacks.Perfect.SupportedQuasicoherent.supportedPushforwardHomologyIso` —
  `Hⁿ(i_*R𝓗_T(ℱ[0])) ≅ i_*ℋⁿ_T(ℱ)`, naturally in `ℱ`.

## Main results

* `Stacks.Perfect.SupportedQuasicoherent.isQuasicoherent_rightDerived_supportedSectionsFunctor_obj`
  — **[Stacks, Tag 0G7G] (1), degreewise.**

## Implementation notes

Two things separate the derived statement from the degreewise one, and both are already in the
library.  A module placed in degree zero lies in `D_QCoh(𝒪_X)` as soon as it is quasi-coherent,
because its cohomology is itself in degree zero and vanishes elsewhere and quasi-coherent
modules form a weak Serre subcategory
(`DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj` at
`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre`).  And the
cohomology of the *total* derived functor at such an object is Mathlib's `ℕ`-indexed
`CategoryTheory.Functor.rightDerived`, by
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`; its hypotheses are that
`i_*R𝓗_T` is a right derived functor of `ℱ ↦ i_*ℋ_T(ℱ)` with the unit
`Stacks.Perfect.SupportedQuasicoherent.derivedSupportedPushforwardUnit`, which is the instance
`derivedSupportedPushforward_isRightDerivedFunctor`, and that K-injective resolutions exist,
which is `Stacks.Cohomology.Localization.enoughKInjectives`.  Quasi-coherence is closed under
isomorphism, being a weak Serre subcategory, so it transports across that comparison.

No `@[stacks 0G7G]` attribute is attached: the tag is already carried by
`Stacks.Perfect.SupportedQuasicoherent.quasiCoherentSupported_derivedSupportedPushforward`
(part (1)) and `…derivedSupportedPushforwardAdjunction` (part (2)), and this file states no
part of the tag that those do not, only a specialization of part (1).

## References

* [Stacks Project, Tag 0G7G](https://stacks.math.columbia.edu/tag/0G7G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.SupportedSections

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Perfect.SupportedQuasicoherent

variable (X : Scheme.{u}) (T : Set X) (hT : IsClosed T)

/-- **`Hⁿ(i_*R𝓗_T(ℱ[0])) ≅ i_*ℋⁿ_T(ℱ)`.**  The degree-`n` cohomology of `i_*R𝓗_T` applied to a
module placed in degree zero is Mathlib's `ℕ`-indexed right derived functor of
`ℱ ↦ i_*ℋ_T(ℱ)`, because `i_*R𝓗_T` is a right derived functor of that functor
(`derivedSupportedPushforward_isRightDerivedFunctor`) and K-injective resolutions exist. -/
public def supportedPushforwardHomologyIso (n : ℕ) :
    DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0 ⋙
        derivedSupportedPushforward X.toRingedSpace T hT ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (n : ℤ) ≅
      (supportedSectionsFunctor X.toRingedSpace T).rightDerived n :=
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (supportedSectionsFunctor X.toRingedSpace T)
    (derivedSupportedPushforward X.toRingedSpace T hT)
    (derivedSupportedPushforwardUnit X.toRingedSpace T hT)
    Stacks.Cohomology.Localization.enoughKInjectives n

/-- **[Stacks, Tag 0G7G] (1), degree by degree.**  For a quasi-coherent module `ℱ` on a scheme
`X` and a closed subset `T` whose open complement is retrocompact, the module `i_*ℋⁿ_T(ℱ)` of
sections supported on `T` in degree `n` is quasi-coherent. -/
public theorem isQuasicoherent_rightDerived_supportedSectionsFunctor_obj (hT : IsClosed T)
    (hTc : IsRetrocompact Tᶜ)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hF : SheafOfModules.isQuasicoherent X.ringCatSheaf F) (n : ℕ) :
    SheafOfModules.isQuasicoherent X.ringCatSheaf
      (((supportedSectionsFunctor X.toRingedSpace T).rightDerived n).obj F) := by
  have hwS := Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X
  have hE : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((DerivedCategory.singleFunctor _ 0).obj F) :=
    (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj _ hwS F hF).2
  exact hwS.isClosedUnderIsomorphisms.of_iso
    ((supportedPushforwardHomologyIso X T hT n).app F)
    (derivedQuasiCoherent_derivedSupportedPushforward X T hT hTc _ hE (n : ℤ))

end Stacks.Perfect.SupportedQuasicoherent

end
