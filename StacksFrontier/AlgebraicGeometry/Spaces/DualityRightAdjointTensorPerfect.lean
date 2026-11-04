module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPushforwardTraceCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedDualExactPairing

/-!
# Direct images of perfect objects tensored with `a(𝒪_Y)`

Let `f : X ⟶ Y` be a proper, flat morphism of finite presentation of quasi-compact and
quasi-separated algebraic spaces and `ω = a(𝒪_Y)` for the right adjoint `a` of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` (Stacks 0E55). For a perfect object `E` of `D(𝒪_X)`,
`Rf_*(E ⊗^L ω) ≅ Rf_* R𝓗om(E^∨, ω) ≅ R𝓗om(Rf_* E^∨, 𝒪_Y) = (Rf_* E^∨)^∨` by Stacks 08JJ,
Stacks 0E58 with Stacks 0GG4, and Stacks 0CTM; in particular it is perfect.

## Main definitions

* `AlgebraicGeometry.Space.derivedModulePushforwardTensorRightAdjointIso`: the isomorphism
  `Rf_*(E ⊗^L a(𝒪_Y)) ≅ (Rf_* E^∨)^∨` for a perfect `E`.

## Main results

* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_tensor_rightAdjoint`:
  `Rf_*(E ⊗^L a(𝒪_Y))` is perfect for every perfect `E`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) (hYqc : IsQuasiCompactSpace B S hS Y.1)
  (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
  (hfp : IsFinitePresentation B S hS f.hom)

include hYqc hf hfl hfp in
/-- **`Rf_*(E ⊗^L a(𝒪_Y)) ≅ (Rf_* E^∨)^∨`** for a perfect `E`: the direct image of
`E ⊗^L ω ≅ R𝓗om(E^∨, ω)` (Stacks 08JJ), followed by the trace map
`Rf_* R𝓗om(E^∨, ω) ⟶ R𝓗om(Rf_* E^∨, 𝒪_Y)` of Stacks 0E58, which is invertible (Stacks 0GG4). -/
def derivedModulePushforwardTensorRightAdjointIso
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    (derivedModulePushforward B S hS f).obj (((smallEtaleDerivedTensor B S hS X).obj E).obj
        ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
          (derivedStructureSheaf B S hS Y.1 Y.2)).obj) ≅
      smallEtaleDerivedDual B S hS Y ((derivedModulePushforward B S hS f).obj
        (smallEtaleDerivedDual B S hS X E)) :=
  (derivedModulePushforward B S hS f).mapIso
      (((smallEtaleDerivedTensor B S hS X).mapIso
          (smallEtaleDerivedBidualIso B S hS X E hE).symm).app
          ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
            (derivedStructureSheaf B S hS Y.1 Y.2)).obj ≪≫
        (smallEtaleDerivedSheafHomIsoTensorDual B S hS X _ _
          (isPerfect_smallEtaleDerivedDual B S hS X E hE)).symm) ≪≫
    @asIso _ _ _ _ (smallEtalePushforwardTrace hZ f hXqc hXqs hYqs
      (quasicoherentDerivedDual X ⟨E, derivedCategoryB_of_isPerfect B S hS X E hE⟩ hE)
      (derivedStructureSheaf B S hS Y.1 Y.2))
      (isIso_smallEtalePushforwardTrace_of_isPerfect hZ f hXqc hXqs hYqs
        (quasicoherentDerivedDual X ⟨E, derivedCategoryB_of_isPerfect B S hS X E hE⟩ hE)
        (derivedStructureSheaf B S hS Y.1 Y.2) hYqc (isPerfect_smallEtaleDerivedDual B S hS X E hE)
        (isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat f hf hfl hfp _
          (isPerfect_smallEtaleDerivedDual B S hS X E hE)).1)

include hYqc hf hfl hfp in
/-- **`Rf_*(E ⊗^L a(𝒪_Y))` is perfect for every perfect `E`.** -/
theorem isPerfect_derivedModulePushforward_tensor_rightAdjoint
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((derivedModulePushforward B S hS f).obj (((smallEtaleDerivedTensor B S hS X).obj E).obj
        ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
          (derivedStructureSheaf B S hS Y.1 Y.2)).obj)) := by
  obtain ⟨P, hP, ⟨i⟩⟩ := isPerfect_smallEtaleDerivedDual B S hS Y _
    (isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat f hf hfl hfp _
      (isPerfect_smallEtaleDerivedDual B S hS X E hE)).1
  exact ⟨P, hP, ⟨i ≪≫ (derivedModulePushforwardTensorRightAdjointIso hZ f hXqc hXqs hYqs hYqc hf
    hfl hfp E hE).symm⟩⟩

end AlgebraicGeometry.Space

end
