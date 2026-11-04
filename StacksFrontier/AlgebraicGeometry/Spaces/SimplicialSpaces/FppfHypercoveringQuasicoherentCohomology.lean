module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleAugmentationComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentDerivedDescentEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleAffineKFlatModel
public import StacksFrontier.CategoryTheory.Adjunction.UnitIsoMapBijective
public import StacksFrontier.CategoryTheory.Adjunction.UnitIsoOfIntertwining
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOfToposHomTwoIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayGlobalSectionsOfInvertibleUnit

/-!
# Cohomology of quasi-coherent complexes along an fppf hypercovering

Let `S` be a scheme, `X` an algebraic space over `S`, `U` a simplicial algebraic space over `S` and
`a : U → X` an augmentation which is an fppf hypercovering of `X`, and let
`a : (Sh(U_étale), 𝒪_U) → (Sh(X_étale), 𝒪_X)` be the morphism of ringed topoi of Section 0DE7.
For every object `K` of `D_QCoh(𝒪_X)` the derived unit `K → Ra_*La^*K` is an isomorphism, and
consequently

`RΓ(X_étale, K) = RΓ(U_étale, La^*K)`.

The unit is invertible because `La^* : D_QCoh(𝒪_X) → D_QCoh(𝒪_U)` is an equivalence with
quasi-inverse `Ra_*` (Stacks 0DHF). That equivalence is available for the augmentation of the
spaces-étale site of `U` of `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite`; through the
2-isomorphism `AlgebraicGeometry.Space.etaleAugmentationTwoIso` it is carried to the augmentation
of the strict model of `U_étale` of Section 0DE7: the derived pullbacks along the two
augmentations differ by the derived pullback along an equivalence of ringed topoi, which is fully
faithful, and the unit at `K` is invertible exactly when `La^*` is bijective on morphisms into `K`.
Finally `RΓ(U_étale, -) = RΓ(X_étale, -) ∘ Ra_*` (Cohomology on Sites, Remark 08J6) identifies
`RΓ(U_étale, La^*K)` with `RΓ(X_étale, Ra_*La^*K)`, which is `RΓ(X_étale, K)` by the unit.

## Main results

* `AlgebraicGeometry.Space.IsFppfHypercovering.isIso_derivedAdjunction_unit_app`: the derived
  unit `K → Ra_*La^*K` is invertible for `K` in `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.Space.IsFppfHypercovering.isIso_derivedGlobalSectionsSemilinearMap`:
  **Stacks 0DHG**, the canonical map `RΓ(X_étale, K) ⟶ RΓ(U_étale, La^*K)` is an isomorphism.

## Implementation notes

The derived categories of sheaves of modules are those of the model `HasDerivedCategory.standard`,
in which the derived pullback, the derived pushforward and their adjunction along a morphism of
ringed topoi are constructed; the coefficient rings of `RΓ` carry arbitrary models.

## References

* [Stacks Project, Tag 0DHG](https://stacks.math.columbia.edu/tag/0DHG)
* [Stacks Project, Tag 0DHF](https://stacks.math.columbia.edu/tag/0DHF)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CategoryTheory.Hypercovering

universe u r r'

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

section Derived

open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.Cohomology.DerivedPushforward
open SimplicialSpacesEtaleSite

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable (A) in
/-- The objects of `D_QCoh(𝒪_X)`: the complexes of `𝒪_X`-modules on `X_{spaces, étale}` whose
cohomology sheaves are quasi-coherent. -/
abbrev etaleQuasicoherentComplexes :
    ObjectProperty (@DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS A.right).O)) _ _
      (HasDerivedCategory.standard _)) :=
  @DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS A.right).O))

/-- **The derived unit along the augmentation of `SimplicialSpacesEtaleSite` is invertible on
`D_QCoh(𝒪_X)`** for an fppf hypercovering: `La^*` restricts to an equivalence
`D_QCoh(𝒪_X) ≌ D_QCoh(𝒪_U)` whose quasi-inverse is the restriction of `Ra_*` (Stacks 0DHF). -/
theorem IsFppfHypercovering.isIso_derivedAdjunction_unit_app_simplicialSpacesEtaleSite
    (hA : IsFppfHypercovering A)
    (K : @DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS A.right).O)) _ _
      (HasDerivedCategory.standard _))
    (hK : etaleQuasicoherentComplexes A K) :
    IsIso ((derivedAdjunction (augmentationRingedToposHom (augmentationToConst A))).unit.app K) :=
  have h := BigFppfSpaceSite.isHypercoveringAugmentation_pretopology_of_isFppfHypercovering
    (bigFppfSpaceSiteOfSchemeSite B S hS) hA
  let e := derivedQuasicoherentDescentEquivalence h
  Adjunction.isIso_unit_app_of_fullyFaithful_lift
    (derivedAdjunction (augmentationRingedToposHom (augmentationToConst A)))
    (etaleQuasicoherentComplexes A)
    (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (SimplicialSpacesEtaleSite.ringedTopos A.left).O)))
    (fun K hK ↦ (e.functor.obj ⟨K, hK⟩).property)
    (fun L hL ↦ (e.inverse.obj ⟨L, hL⟩).property)
    e.fullyFaithfulFunctor K hK

/-- **The derived unit along the augmentation of `U_étale` is invertible on `D_QCoh(𝒪_X)`** for
an fppf hypercovering `a : U → X`: `K → Ra_*La^*K` is an isomorphism for every `K` whose
cohomology sheaves are quasi-coherent. -/
theorem IsFppfHypercovering.isIso_derivedAdjunction_unit_app (hA : IsFppfHypercovering A)
    (K : @DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS A.right).O)) _ _
      (HasDerivedCategory.standard _))
    (hK : etaleQuasicoherentComplexes A K) :
    IsIso ((derivedAdjunction (etaleAugmentationRingedHom A)).unit.app K) := by
  have := isEquivalence_derivedPullback_etaleSiteComparisonRingedToposHom A
  refine ((derivedAdjunction (etaleAugmentationRingedHom A)).isIso_unit_app_iff_bijective_map
    K).2 fun P => ?_
  have hg := (Adjunction.isIso_unit_app_iff_bijective_map
    (derivedAdjunction (augmentationRingedToposHom (augmentationToConst A)))
    K).1 (hA.isIso_derivedAdjunction_unit_app_simplicialSpacesEtaleSite K hK) P
  have e₁ := Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackIsoOfTwoIso.{u + 1, u + 1,
    u + 1, u + 1, u + 1, u + 1} (etaleAugmentationTwoIso A)
  have hg₁ := (Functor.bijective_map_iff_of_natIso_unitIsoMapBijective e₁ P K).1 hg
  have e₂ := Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.derivedPullbackCompIso.{u + 1,
    u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} (etaleSiteComparisonRingedToposHom A)
      (etaleAugmentationRingedHom A)
  have hg₂ := (Functor.bijective_map_iff_of_natIso_unitIsoMapBijective e₂.symm P K).1 hg₁
  have hc := (Functor.FullyFaithful.ofFullyFaithful
    (derivedPullback.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (etaleSiteComparisonRingedToposHom A))).map_bijective
      ((derivedPullback (etaleAugmentationRingedHom A)).obj P)
      ((derivedPullback (etaleAugmentationRingedHom A)).obj K)
  exact (Functor.bijective_comp_map_iff_unitIsoMapBijective hc).1 hg₂

section GlobalSections

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open AlgebraicGeometry.RingedToposHom Stacks.Cohomology.SiteModules
  Stacks.Cohomology.LerayOfToposHom

/-- **Stacks Project, Tag 0DHG.** Let `S` be a scheme, `X` an algebraic space over `S`, `U` a
simplicial algebraic space over `S` and `a : U → X` an augmentation. If `a : U → X` is an fppf
hypercovering of `X`, then

`RΓ(X_étale, K) = RΓ(U_étale, a^*K)`

for `K ∈ D_QCoh(𝒪_X)`, where `a : (Sh(U_étale), 𝒪_U) → (Sh(X_étale), 𝒪_X)` is the morphism of
ringed topoi of Section 0DE7 (`AlgebraicGeometry.Space.etaleAugmentationRingedHom`) and `a^*` its
derived pullback: the canonical map `RΓ(X_étale, K) ⟶ RΓ(U_étale, a^*K)` is an isomorphism.

Here `RΓ(X_étale, -)` and `RΓ(U_étale, -)` are the total right derived functors of global
sections, with values in the derived categories of modules over coefficient rings `R'` and `R`
mapping to `Γ(X, 𝒪_X)` and to `Γ(U, 𝒪_U)` through `ψ'` and `ψ`, compatibly (`h`) with
`ρ : R' → R` and the map `Γ(X, 𝒪_X) → Γ(U, 𝒪_U)` of `a`; the right hand side is read in `D(R')`
through restriction of scalars along `ρ`. For instance `R = R' = ℤ`. The canonical map
(`Stacks.Cohomology.LerayOfToposHom.derivedGlobalSectionsSemilinearMap`) is `RΓ(X_étale, -)` of the
derived unit `K → Ra_*a^*K`, invertible on `D_QCoh(𝒪_X)` by
`AlgebraicGeometry.Space.IsFppfHypercovering.isIso_derivedAdjunction_unit_app`, followed by the
identification `RΓ(X_étale, -) ∘ Ra_* = RΓ(U_étale, -)` of Cohomology on Sites, Remark 08J6. -/
@[stacks 0DHG]
theorem IsFppfHypercovering.isIso_derivedGlobalSectionsSemilinearMap (hA : IsFppfHypercovering A)
    {R : Type r} [Ring R] [HasDerivedCategory (ModuleCat.{u + 1} R)]
    {R' : Type r'} [Ring R'] [HasDerivedCategory (ModuleCat.{u + 1} R')]
    (ψ : R →+* RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := ((etaleSituation A).totalRingedTopos (etaleStructureSheaf A)).J))
        ((etaleSituation A).totalRingedTopos (etaleStructureSheaf A)).O).obj)
    (ψ' : R' →+* RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (etaleRingedAugmentation A).augmentationRingedTopos.J))
        (etaleRingedAugmentation A).augmentationRingedTopos.O).obj)
    (ρ : R' →+* R)
    (h : (toposGlobalSectionsRingHom (etaleAugmentationRingedHom A)).comp ψ' = ψ.comp ρ)
    (K : @DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS A.right).O)) _ _
      (HasDerivedCategory.standard _))
    (hK : etaleQuasicoherentComplexes A K) :
    IsIso (derivedGlobalSectionsSemilinearMap.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, r, r',
      _, _}
      (etaleAugmentationRingedHom A) ψ ψ' ρ h K) :=
  isIso_derivedGlobalSectionsSemilinearMap_of_isIso_unit.{u + 1, u + 1, u + 1, u + 1, u + 1,
    u + 1, r, r', _, _} (etaleAugmentationRingedHom A) ψ ψ' ρ h K
    (hA.isIso_derivedAdjunction_unit_app K hK)

end GlobalSections

end Derived

end AlgebraicGeometry.Space

end
