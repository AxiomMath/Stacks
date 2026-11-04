module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentDerivedUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentWeakSerreOfExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpacesEtaleAffineVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CoarseningDerivedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.DerivedUnitSingleOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnboundedEquivalenceOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom

/-!
# Derived descent of quasi-coherent modules along an fppf hypercovering

Let `a : U → X` be an augmentation of a simplicial algebraic space which is an fppf hypercovering,
and `a : (Sh(U_{étale}), 𝒪_U) ⟶ (Sh(X_{étale}), 𝒪_X)` the morphism of ringed topoi of
Stacks 0DE7. Stacks 0DHF asserts that `QCoh(𝒪_U)` is a weak Serre subcategory of `Mod(𝒪_U)` and
that `a^* : D_{QCoh}(𝒪_X) ⟶ D_{QCoh}(𝒪_U)` is an equivalence with quasi-inverse `Ra_*`.

This file proves the equivalence once the pullback of modules `a^*` is known to be exact, by
checking the hypotheses of Stacks 0D7V in the form
`Stacks.Cohomology.CohomologicalDescent.equivalenceUnboundedAdjunctionUnboundedEquivalence`:
`a^*` induces an equivalence `QCoh(𝒪_X) ≌ QCoh(𝒪_U)` (Stacks 0DHD), the unit `ℱ ⟶ Ra_*a^*ℱ` is
invertible on quasi-coherent `ℱ` (Stacks 0DHE), and both sites satisfy Stacks 0D6R with the
affine objects, `d = 0` and the coverings by affine objects (Stacks 0DH2, 071Y, 01XB).

All names below are in the namespace `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite`.

## Main definitions

* `derivedQuasicoherentDescentEquivalenceOfPreservesFiniteLimits`: the equivalence
  `D_{QCoh}(𝒪_X) ≌ D_{QCoh}(𝒪_U)`, for an exact `a^*`.

## Main results

* `bijective_derivedPullback_map_of_preservesFiniteLimits` and
  `exists_derivedPullback_obj_iso_of_preservesFiniteLimits`: `La^*` is fully faithful and
  essentially surjective between the two `D_{QCoh}`'s.

## References

* [Stacks Project, Tag 0DHF](https://stacks.math.columbia.edu/tag/0DHF)
* [Stacks Project, Tag 0D7V](https://stacks.math.columbia.edu/tag/0D7V)
* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CategoryTheory.Hypercovering
open Stacks.Cohomology.DerivedPushforward

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {U : SimplicialObject T.Spaces} {X : T.Spaces}
  {a : U ⟶ (SimplicialObject.const T.Spaces).obj X}

attribute [local instance] enoughInjectives_ringedToposModules
  enoughInjectives_spacesEtaleRingedToposModules

section Exact

variable (h : IsHypercoveringAugmentation T.pretopologyBigFppfPretopology U a)
  [hex : PreservesFiniteLimits
    (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
      u + 1, u + 1, u + 1} (augmentationRingedToposHom a).toModulesHom)]

include h in
/-- The unit `ℱ[0] ⟶ Ra_*La^*(ℱ[0])` is invertible for quasi-coherent `ℱ`, once `a^*` is exact:
Stacks 0DHE through the derived unit at an object placed in degree zero. -/
theorem isIso_derivedUnit_app_singleFunctor_obj_of_preservesFiniteLimits
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (SpacesEtale.topology T.schemeSite S T.scheme_mem X))
      (SpacesEtale.structureSheaf T.schemeSite S T.scheme_mem X)))
    (hF : F.IsQuasicoherentOnSite) :
    IsIso ((derivedPullbackPushforwardAdjunctionOfToposHom (augmentationRingedToposHom a)).unit.app
      ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard
        (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))) 0).obj F)) :=
  have H := @isIso_unit_and_isZero_rightDerived_of_isHypercoveringAugmentation _ _ _ _ _ h F hF
  open Stacks.Cohomology.CohomologicalDescent in
  OfRingedToposHom.isIso_derivedUnit_app_singleFunctor_obj_of_isZero_rightDerived
    (augmentationRingedToposHom a) F H.1 H.2

include h in
/-- **Stacks 0DHF, once `a^*` is exact.** For an fppf hypercovering `a : U → X` with exact
pullback of modules `a^*`, the derived pullback restricts to an equivalence
`D_{QCoh}(𝒪_X) ≌ D_{QCoh}(𝒪_U)`, with quasi-inverse the restriction of `Ra_*`. -/
def derivedQuasicoherentDescentEquivalenceOfPreservesFiniteLimits :
    (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))).FullSubcategory ≌
      (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U).O))).FullSubcategory :=
  haveI := RingedToposHom.pullbackModules_preservesFiniteColimits (augmentationRingedToposHom a)
  haveI := RingedToposHom.pullbackModules_additive (augmentationRingedToposHom a)
  haveI := Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
    (augmentationRingedToposHom a)
  letI := Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback_commShift
    (augmentationRingedToposHom a)
  haveI := Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback_isTriangulated_general
    (augmentationRingedToposHom a)
  haveI : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U).O)).IsWeakSerreClass :=
    isWeakSerreClass_isQuasicoherentOnSite_ringedSite_of_preservesFiniteLimits h
  Stacks.Cohomology.CohomologicalDescent.equivalenceUnboundedAdjunctionUnboundedEquivalence
    (augmentationRingedToposHom a).toModulesHom.pullbackModules
    (derivedPullbackPushforwardAdjunctionOfToposHom (augmentationRingedToposHom a))
    (Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom.derivedPullbackNatIso
      (augmentationRingedToposHom a))
    _ _ (fun F hF ↦ @isQuasicoherentOnSite_augmentationRingedToposHom_pullbackModules_obj _ _ _
      _ _ a F hF)
    (quasicoherentDescentEquivalence h).isEquivalence_functor
    (isIso_derivedUnit_app_singleFunctor_obj_of_preservesFiniteLimits h)
    (IsAffineScheme U) (exists_preZeroHypercover_isAffineScheme_spacesEtaleAffineVanishing U)
    (fun _ _ ↦ 0)
    (fun V _ ↦ Stacks.Cohomology.cofinalCoveringSystemOfBasis _ (IsAffineScheme U)
      (exists_preZeroHypercover_isAffineScheme_spacesEtaleAffineVanishing U) V)
    (fun _ _ 𝒰 h𝒰 i p hp G hG ↦
      isZero_moduleCohomology_of_isAffineScheme_spacesEtaleAffineVanishing U G hG (𝒰.X i)
        (h𝒰.2 i) p (by exact_mod_cast hp))
    {V | SpacesEtale.IsAffineScheme T.schemeSite S T.scheme_mem X V}
    (BigFppfSpaceSite.exists_preZeroHypercover_isAffineScheme_spacesEtaleAffineVanishing T X)
    (fun _ _ ↦ 0)
    (fun V _ ↦ Stacks.Cohomology.cofinalCoveringSystemOfBasis _
      {V | SpacesEtale.IsAffineScheme T.schemeSite S T.scheme_mem X V}
      (BigFppfSpaceSite.exists_preZeroHypercover_isAffineScheme_spacesEtaleAffineVanishing T X) V)
    (fun _ _ 𝒰 h𝒰 i p hp F hF ↦
      BigFppfSpaceSite.isZero_moduleCohomology_of_isAffineScheme_spacesEtaleAffineVanishing T X
        F hF (𝒰.X i) (h𝒰.2 i) p (by exact_mod_cast hp))

include h in
/-- **`La^*` is fully faithful on `D_{QCoh}(𝒪_X)`, once `a^*` is exact** (part of Stacks 0DHF):
for `K, E` with quasi-coherent cohomology, `Hom(K, E) ⟶ Hom(La^*K, La^*E)` is bijective. -/
theorem bijective_derivedPullback_map_of_preservesFiniteLimits
    {K E : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) _ _
      (HasDerivedCategory.standard _)}
    (hK : @DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) K)
    (hE : @DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) E) :
    haveI := Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
      (augmentationRingedToposHom a)
    Function.Bijective (fun g : K ⟶ E ↦
      (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
        (augmentationRingedToposHom a)).map g) := by
  have := Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
    (augmentationRingedToposHom a)
  let e := derivedQuasicoherentDescentEquivalenceOfPreservesFiniteLimits h
  have h₁ := (ObjectProperty.fullyFaithfulι _).map_bijective
    (X := (⟨K, hK⟩ : (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))).FullSubcategory))
    (Y := ⟨E, hE⟩)
  have h₂ := e.fullyFaithfulFunctor.map_bijective (X := ⟨K, hK⟩) (Y := ⟨E, hE⟩)
  have h₃ := (ObjectProperty.fullyFaithfulι _).map_bijective
    (X := e.functor.obj ⟨K, hK⟩) (Y := e.functor.obj ⟨E, hE⟩)
  exact (Function.Bijective.of_comp_iff _ h₁).mp (h₃.comp h₂)

include h in
/-- **`La^*` is essentially surjective onto `D_{QCoh}(𝒪_U)`, once `a^*` is exact** (part of
Stacks 0DHF): every `L` with quasi-coherent cohomology is `La^*K` for some `K` with
quasi-coherent cohomology. -/
theorem exists_derivedPullback_obj_iso_of_preservesFiniteLimits
    (L : @DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U).O)) _ _
      (HasDerivedCategory.standard _))
    (hL : @DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U).O)) L) :
    haveI := Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
      (augmentationRingedToposHom a)
    ∃ K, @DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) K ∧
      Nonempty ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
        (augmentationRingedToposHom a)).obj K ≅ L) := by
  have := Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
    (augmentationRingedToposHom a)
  let e := derivedQuasicoherentDescentEquivalenceOfPreservesFiniteLimits h
  exact ⟨(e.inverse.obj ⟨L, hL⟩).obj, (e.inverse.obj ⟨L, hL⟩).property,
    ⟨(ObjectProperty.ι _).mapIso (e.counitIso.app ⟨L, hL⟩)⟩⟩

end Exact

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
