module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialAugmentationPullbackExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentDerivedDescent

/-!
# Stacks 0DHF: derived descent of quasi-coherent modules along an fppf hypercovering

Let `a : U → X` be an augmentation of a simplicial algebraic space which is an fppf
hypercovering of `X`, and `a : (Sh(U_{étale}), 𝒪_U) ⟶ (Sh(X_{étale}), 𝒪_X)` the morphism of
ringed topoi of Stacks 0DE7. Then `QCoh(𝒪_U)` is a weak Serre subcategory of `Mod(𝒪_U)` and
`a^* : D_{QCoh}(𝒪_X) ⟶ D_{QCoh}(𝒪_U)` is an equivalence with quasi-inverse `Ra_*`.

The equivalence was constructed for an exact `a^*`
(`derivedQuasicoherentDescentEquivalenceOfPreservesFiniteLimits`); exactness of `a^*` for an fppf
hypercovering is `preservesFiniteLimits_augmentationRingedToposHom_pullbackModules`.

## Main results

All in the namespace `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite`.

* `derivedQuasicoherentDescentEquivalence`, with
  `derivedQuasicoherentDescentEquivalence_functor_comp_ι` and
  `derivedQuasicoherentDescentEquivalence_inverse_comp_ι` identifying its functor with `La^*` and
  its inverse with `Ra_*`.
* `bijective_derivedPullback_map` and `exists_derivedPullback_obj_iso`.
* `isWeakSerreClass_and_derivedPullback_equivalence`: **Stacks 0DHF.** `QCoh(𝒪_U)` is a weak
  Serre subcategory of `Mod(𝒪_U)` and `a^*` is an equivalence `D_{QCoh}(𝒪_X) ⟶ D_{QCoh}(𝒪_U)`.

## References

* [Stacks Project, Tag 0DHF](https://stacks.math.columbia.edu/tag/0DHF)
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

variable (h : IsHypercoveringAugmentation T.pretopologyBigFppfPretopology U a)

include h in
/-- **The derived pullback along an fppf hypercovering is an equivalence on quasi-coherent
complexes** (Stacks 0DHF): `D_{QCoh}(𝒪_X) ≌ D_{QCoh}(𝒪_U)`. -/
def derivedQuasicoherentDescentEquivalence :
    (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))).FullSubcategory ≌
      (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U).O))).FullSubcategory :=
  haveI := preservesFiniteLimits_augmentationRingedToposHom_pullbackModules h
  derivedQuasicoherentDescentEquivalenceOfPreservesFiniteLimits h

include h in
/-- The functor of `derivedQuasicoherentDescentEquivalence` is the restriction of `La^*`. -/
theorem derivedQuasicoherentDescentEquivalence_functor_comp_ι :
    haveI := Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
      (augmentationRingedToposHom a)
    (derivedQuasicoherentDescentEquivalence h).functor ⋙
        (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U).O))).ι =
      (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))).ι ⋙
        Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback (X := ringedTopos U)
          (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (augmentationRingedToposHom a) :=
  rfl

include h in
/-- The quasi-inverse of `derivedQuasicoherentDescentEquivalence` is the restriction of
`Ra_*`. -/
theorem derivedQuasicoherentDescentEquivalence_inverse_comp_ι :
    (derivedQuasicoherentDescentEquivalence h).inverse ⋙
        (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))).ι =
      (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U).O))).ι ⋙
        derivedPushforward (X := ringedTopos U)
          (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (augmentationRingedToposHom a) :=
  rfl

include h in
/-- **`La^*` is fully faithful on `D_{QCoh}(𝒪_X)`** for an fppf hypercovering (part of
Stacks 0DHF): for `K, E` with quasi-coherent cohomology, `Hom(K, E) ⟶ Hom(La^*K, La^*E)` is
bijective. -/
theorem bijective_derivedPullback_map
    {K E : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) _ _
      (HasDerivedCategory.standard _)}
    (hK : (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))) K)
    (hE : (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))) E) :
    haveI := Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
      (augmentationRingedToposHom a)
    Function.Bijective (fun g : K ⟶ E ↦
      (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
        (augmentationRingedToposHom a)).map g) :=
  have := preservesFiniteLimits_augmentationRingedToposHom_pullbackModules h
  bijective_derivedPullback_map_of_preservesFiniteLimits h hK hE

include h in
/-- **`La^*` is essentially surjective onto `D_{QCoh}(𝒪_U)`** for an fppf hypercovering (part
of Stacks 0DHF). -/
theorem exists_derivedPullback_obj_iso
    (L : @DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U).O)) _ _
      (HasDerivedCategory.standard _))
    (hL : (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U).O))) L) :
    haveI := Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
      (augmentationRingedToposHom a)
    ∃ K, (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))) K ∧
      Nonempty ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
        (augmentationRingedToposHom a)).obj K ≅ L) :=
  have := preservesFiniteLimits_augmentationRingedToposHom_pullbackModules h
  exists_derivedPullback_obj_iso_of_preservesFiniteLimits h L hL

include h in
/-- **Stacks 0DHF.** Let `a : U → X` be an augmentation of a simplicial algebraic space which is
an fppf hypercovering of `X`. Then `QCoh(𝒪_U)` is a weak Serre subcategory of `Mod(𝒪_U)`, and
`a^* : D_{QCoh}(𝒪_X) ⟶ D_{QCoh}(𝒪_U)` is an equivalence of categories with quasi-inverse
`Ra_*`: there is an equivalence whose functor is the restriction of the derived pullback `La^*`
and whose inverse is the restriction of the derived pushforward `Ra_*`. -/
theorem isWeakSerreClass_and_derivedPullback_equivalence :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (J := (ringedSite U).J)
        (ringedSite U).O)).IsWeakSerreClass ∧
    haveI := Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
      (augmentationRingedToposHom a)
    ∃ e : (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))).FullSubcategory ≌
      (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U).O))).FullSubcategory,
      e.functor ⋙ (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U).O))).ι =
        (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))).ι ⋙
          Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback (X := ringedTopos U)
            (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
            (augmentationRingedToposHom a) ∧
      e.inverse ⋙ (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O))).ι =
        (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U).O))).ι ⋙
          derivedPushforward (X := ringedTopos U)
            (Y := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
            (augmentationRingedToposHom a) :=
  ⟨isWeakSerreClass_isQuasicoherentOnSite_ringedSite h,
    ⟨derivedQuasicoherentDescentEquivalence h,
      derivedQuasicoherentDescentEquivalence_functor_comp_ι h,
      derivedQuasicoherentDescentEquivalence_inverse_comp_ι h⟩⟩

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
