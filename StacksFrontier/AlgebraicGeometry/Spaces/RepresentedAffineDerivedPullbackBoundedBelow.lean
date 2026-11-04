module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LocallyBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePushforwardStructureFiniteTorDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelPseudoCoherent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowTensor

/-!
# Derived pullback along a morphism of affines of finite Tor dimension preserves boundedness below

Let `g : U' ⟶ U` be a morphism of affine objects of the big fppf site, with rings `R ⟶ R'`.
If `R'` has finite Tor dimension over `R`, then `Lg^*K` is bounded below for every bounded below
`K ∈ D_QCoh(𝒪_U)`: by the projection formula (Stacks 08IN) `Rg_*Lg^*K ≅ Rg_*𝒪_{U'} ⊗^L K`, which
is bounded below because `Rg_*𝒪_{U'}` has finite Tor dimension, and `Rg_*` reflects the vanishing
of the cohomology sheaves of objects of `D_QCoh(𝒪_{U'})` (`Rg_*Φ_{R'}M ≅ Φ_R(M|_R)`).

## Main results

* `isZero_homology_of_isZero_homology_derivedModulePushforward_representedSpaceMap`: for
  `F ∈ D_QCoh(𝒪_{U'})`, if `H^i(Rg_*F) = 0` then `H^i(F) = 0`.
* `isBoundedBelow_of_isBoundedBelow_smallEtaleModelDerivedEquivalence_functor_obj`: the derived
  equivalence with the small étale model reflects boundedness below.
* `isBoundedBelow_smallEtaleDerivedModulePullback_representedSpaceMap`: `Lg^*K` is bounded below
  for every bounded below `K ∈ D_QCoh(𝒪_U)` when `R'` has finite Tor dimension over `R`.
-/

/- Instances that come into scope here only through the base versions of imported modules,
and that would change the elaboration below (universe joins, the small model of `D(R)`). -/
attribute [-instance] SheafOfModules.hasBinBiprod

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  (g : U' ⟶ U)

/-- The morphism of spaces represented by a morphism of affine objects is affine. -/
private theorem isAffineHom_representedSpaceMap :
    IsAffineHom B S hS (representedSpaceMap B S hS g).hom :=
  isAffineHom_of_isAffineSpace B S hS _ (isAffineSpace_yoneda B S hS U' inferInstance)
    (isAffineSpace_yoneda B S hS U inferInstance)

/-- **`Rg_*` reflects the vanishing of cohomology sheaves on `D_QCoh` along a morphism of affine
representables.** For `F ∈ D_QCoh(𝒪_{U'})`, if `H^i(Rg_*F) = 0` then `H^i(F) = 0`:
`F ≅ Φ_{R'}M` and `Rg_*Φ_{R'}M ≅ Φ_R(M|_R)`. -/
theorem isZero_homology_of_isZero_homology_derivedModulePushforward_representedSpaceMap
    (F : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U')
      (isAlgebraicSpace_yoneda B S hS U')))
    (hF : QcohDerived B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ F) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((derivedModulePushforward B S hS (representedSpaceMap B S hS g)).obj F))) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj F) := by
  have hg := isAffineHom_representedSpaceMap B S hS g
  let M := (representedAffineDerivedSections B S hS U').obj F
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS U' F hF
  let c : (representedAffineDerivedAssociated B S hS U').obj M ≅ F :=
    asIso ((representedAffineDerivedAdjunction B S hS U').counit.app F)
  have hT := isIso_representedAffineTransportUnit B S hS g hg M
  let t := @asIso _ _ _ _ (representedAffineTransportUnit B S hS g M) hT
  -- `H^i(Φ_R(M|_R)) = 0`
  have h₁ : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((representedAffineDerivedAssociated B S hS U).obj
        ((ModuleCat.restrictScalars
          (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory.obj M))) :=
    h.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      (t ≪≫ (derivedModulePushforward B S hS (representedSpaceMap B S hS g)).mapIso c))
  have h₂ := (isZero_representedAffineAssociated_obj_iff B S hS U _).1
    (h₁.of_iso (((representedAffineAssociated B S hS U).mapDerivedCategoryHomologyIso i).app
      _).symm)
  have h₃ : IsZero ((ModuleCat.restrictScalars (representedAffineCommRingCatHom B S hS g).hom).obj
      ((DerivedCategory.homologyFunctor _ i).obj M)) :=
    h₂.of_iso (((ModuleCat.restrictScalars
      (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategoryCompHomologyFunctorIso
        i).app M).symm
  have h₄ : IsZero ((DerivedCategory.homologyFunctor _ i).obj M) := by
    rw [IsZero.iff_id_eq_zero] at h₃ ⊢
    apply (ModuleCat.restrictScalars (representedAffineCommRingCatHom B S hS g).hom).map_injective
    rwa [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (isZero_homology_iff_representedAffineDerivedSections U' F hF i).2 h₄

/-- **The derived equivalence with the model reflects boundedness below**: it commutes with the
cohomology sheaves and the equivalence of module categories reflects zero objects. -/
theorem isBoundedBelow_of_isBoundedBelow_smallEtaleModelDerivedEquivalence_functor_obj
    (X : AlgebraicSpaces B S hS)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : DerivedCategoryB.IsBoundedBelow
      ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj K)) :
    DerivedCategoryB.IsBoundedBelow K := by
  obtain ⟨n₀, hn₀⟩ := hK
  refine ⟨n₀, fun n hn => ?_⟩
  have h := ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
    (smallEtaleModelModulesEquivalence B S hS X).functor n).app K).isZero_iff.mp (hn₀ n hn)
  exact (((smallEtaleModelModulesEquivalence B S hS X).inverse.map_isZero h)).of_iso
    ((smallEtaleModelModulesEquivalence B S hS X).unitIso.app _)

/-- **Derived pullback along a morphism of affines of finite Tor dimension preserves boundedness
below.** For `g : U' ⟶ U` a morphism of affine objects with rings `R ⟶ R'` of finite Tor
dimension and `K ∈ D_QCoh(𝒪_U)` bounded below, `Lg^*K` is bounded below. -/
theorem isBoundedBelow_smallEtaleDerivedModulePullback_representedSpaceMap
    (hR : HasFiniteTorDimensionRingHom (representedAffineCommRingCatHom B S hS g).hom)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)))
    (hK : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ K)
    (hKb : DerivedCategoryB.IsBoundedBelow K) :
    DerivedCategoryB.IsBoundedBelow
      ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj K) := by
  have hg := isAffineHom_representedSpaceMap B S hS g
  have hfin := hasFiniteTorDimension_derivedPushforward_structureDerived_representedSpaceMap
    B S hS g hR
  have hfinM := hasFiniteTorDimension_smallEtaleModelDerivedEquivalence_functor_obj B S hS
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ _
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (smallEtaleModelRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))) _ hfin
  have hbM :=
    Stacks.SheafOfModules.DerivedTensorProduct.isBoundedBelow_tensor_of_hasFiniteTorDimension
      _ _ _ hfinM (isBoundedBelow_smallEtaleModelDerivedEquivalence_functor_obj B S hS _ K hKb)
  have hb := isBoundedBelow_of_isBoundedBelow_smallEtaleModelDerivedEquivalence_functor_obj B S hS
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ _ (DerivedCategoryB.isBoundedBelow_of_iso
      ((smallEtaleModelDerivedTensorIso B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).app
        ((derivedModulePushforward B S hS (representedSpaceMap B S hS g)).obj
          (structureDerived ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩), K)).symm hbM)
  have hPF := isIso_smallEtaleProjectionFormulaMap B S hS (f := representedSpaceMap B S hS g)
    (isQuasiCompact_of_isAffineHom_hom _ hg) (isQuasiSeparated_of_isAffineHom_hom _ hg)
    (structureDerived ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)
    (qcohDerived_singleFunctor_structureModule (X := yoneda.obj U')
      (hX := isAlgebraicSpace_yoneda B S hS U')) K hK
  obtain ⟨n, hn⟩ := DerivedCategoryB.isBoundedBelow_of_iso
    (@asIso _ _ _ _ _ hPF ≪≫ (derivedModulePushforward B S hS (representedSpaceMap B S hS g)).mapIso
      ((smallEtaleDerivedTensorLeftUnitor _).app _)) hb
  exact ⟨n, fun i hi =>
    isZero_homology_of_isZero_homology_derivedModulePushforward_representedSpaceMap B S hS g _
      (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ _ K hK) i (hn i hi)⟩

end AlgebraicGeometry.Space

end
