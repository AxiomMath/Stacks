module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.GeneralConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BoundednessUnbounded
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusRestriction
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationLevelHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle

/-!
# Stacks 0GKY, 0GKZ and 0GL0 at the source's hypotheses, from Stacks 0GKV and Stacks 09YU

This file states Stacks 0GKY, 0GKZ and the `D⁺_{tors,c}` case of Stacks 0GL0 at the hypotheses
of the source, with Stacks 0GKV (`h0GKV`) and Stacks 09YU (`h09YU`, essential surjectivity for the
colimit of the categories of constructible sheaves at the stages of an inverse system) as the only
further hypotheses; both are proved elsewhere, and the registered statements discharge them.

The statements are made in the standard model of the derived category
(`HasDerivedCategory.standard`), in which `Rf_!` and
`Stacks.EtaleCohomology.LowerShriekConstructibilityInput` are stated.

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_plus_of_stages`:
  Stacks 0GL0 for `K ∈ D⁺_{tors,c}(X_étale, Λ)`.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_affineLine_of_stages`:
  Stacks 0GKZ.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_openAffineLine_of_stages`:
  Stacks 0GKY.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriekUnbounded_of_stages`:
  Stacks 0GL0 for `K ∈ D_c(X_étale, Λ)`, `Λ` torsion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

/-- The cohomology sheaves of a torsion sheaf placed in degree `0` are torsion. -/
theorem isTorsionEtaleModule_homology_singleFunctor {Λ : Type} [Ring Λ] {X : Scheme.{u}}
    {F : EtaleModules.{u, 0} Λ X} (ht : IsTorsionEtaleModule Λ X F) (q : ℤ) :
    IsTorsionEtaleModule Λ X ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · exact isTorsionEtaleModule_of_isZero Λ X
      (DerivedCategory.Plus.isZero_homology_of_isGE _ 0 q hq)
  · exact IsTorsionEtaleModule.of_iso Λ X
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).app F).symm ht
  · exact isTorsionEtaleModule_of_isZero Λ X
      (DerivedCategory.Plus.isZero_homology_of_isLE _ 0 q hq)

variable (B : BigEtaleSite.{u})

/-- **Stacks 0GL0 for sheaves over a Noetherian ring, from Stacks 0GKV and Stacks 09YU.** Let
`f : X ⟶ Y` be a separated, locally finitely presented, quasi-compact morphism of schemes of `B`
with `X` quasi-compact and quasi-separated, `j` a compactification of `f`, `Λ` a Noetherian ring
and `F` a constructible torsion sheaf of `Λ`-modules on `X`. Then every cohomology sheaf of
`Rf_! F` is constructible: `F` is annihilated by an integer `N > 0`, so `Λ` may be replaced by
`Λ/NΛ`
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_quotient`), and
then `Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_torsion`
applies. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_isTorsion_of_stages
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (h09YU : ∀ (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] {I : Type u} [Preorder I] [Nonempty I]
      [IsDirected I (· ≤ ·)] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
      (hX : B.Contains c.pt), IsLimit c →
      (∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e))) →
      (∀ p : I, CompactSpace (Dg.obj (op p)).obj) →
      (∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) →
      SmallEtaleStagesEssSurj B (ModuleCat.{u + 1} Λ) Dg c hX
        (fun Z => IsConstructibleModuleSheaf B Z Λ))
    {X Y : B.Scheme} [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (f : X.obj ⟶ Y.obj)
    [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    (j : CompactificationOf (Over.mk f)) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]
    (F : EtaleModules.{u, 0} Λ X.obj) (hF : IsBigSiteConstructibleEtaleModule B X Λ F)
    (ht : IsTorsionEtaleModule Λ X.obj F) (n : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ n).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
  isConstructibleEtaleModule_homology_derivedLowerShriek_of_quotient B f j
    (fun Λ' _ _ m hm hΛ' G hG p => isConstructibleEtaleModule_homology_derivedLowerShriek_of_torsion
      B Λ' m hm hΛ' h0GKV (h09YU Λ') f j G hG p) Λ F hF ht n

/-- **Stacks 0GL0 for `D⁺_{tors,c}`, from Stacks 0GKV and Stacks 09YU.** Let `f : X ⟶ Y` be a
separated morphism of finite presentation of schemes of `B`, with `Y` quasi-compact and
quasi-separated, `j` a compactification of `f`, `Λ` a Noetherian ring, and `K` an object of
`D⁺(X_étale, Λ)` whose cohomology sheaves are constructible and torsion. Then every cohomology
sheaf of `Rf_! K` is constructible: the dévissage of Stacks 015J reduces it to sheaves,
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_isTorsion_of_stages`. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_plus_of_stages
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (h09YU : ∀ (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] {I : Type u} [Preorder I] [Nonempty I]
      [IsDirected I (· ≤ ·)] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
      (hX : B.Contains c.pt), IsLimit c →
      (∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e))) →
      (∀ p : I, CompactSpace (Dg.obj (op p)).obj) →
      (∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) →
      SmallEtaleStagesEssSurj B (ModuleCat.{u + 1} Λ) Dg c hX
        (fun Z => IsConstructibleModuleSheaf B Z Λ))
    {X Y : B.Scheme} [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj] (f : X.obj ⟶ Y.obj)
    [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    (j : CompactificationOf (Over.mk f)) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X.obj))
    (hK : ∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
        ((DerivedCategory.Plus.homologyFunctor _ q).obj K) ∧
      IsTorsionEtaleModule Λ X.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K))
    (n : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ
      ((DerivedCategory.Plus.homologyFunctor _ n).obj ((derivedLowerShriek.{u, 0} f j Λ).obj
          K)) := by
  have : QuasiSeparated f := IsSeparated.instQuasiSeparated f
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X.obj := quasiSeparatedSpace_of_quasiSeparated f
  exact isConstructibleEtaleModule_homology_derivedLowerShriek_of_forall_sheaf B f j Λ
    (fun G hG hGt p => isConstructibleEtaleModule_homology_derivedLowerShriek_of_isTorsion_of_stages
      B h0GKV h09YU f j Λ G hG hGt p) K hK n

/-- **Stacks 0GKZ, from Stacks 0GKV and Stacks 09YU.** Let `Y` be an affine scheme of `B`, `Λ` a
Noetherian ring, `ι : X ≅ 𝔸¹_Y` (so `X` is `𝔸¹_Y`), `f = ι ≫ (𝔸¹_Y ⟶ Y)` the structure morphism,
`j` a compactification of `f`, and `F` a constructible sheaf of `Λ`-modules on `X` which is
torsion. Then every cohomology sheaf of `Rf_! F` is constructible. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_affineLine_of_stages
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (h09YU : ∀ (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] {I : Type u} [Preorder I] [Nonempty I]
      [IsDirected I (· ≤ ·)] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
      (hX : B.Contains c.pt), IsLimit c →
      (∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e))) →
      (∀ p : I, CompactSpace (Dg.obj (op p)).obj) →
      (∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) →
      SmallEtaleStagesEssSurj B (ModuleCat.{u + 1} Λ) Dg c hX
        (fun Z => IsConstructibleModuleSheaf B Z Λ))
    (Y : B.Scheme) [IsAffine Y.obj] (X : B.Scheme)
    (ι : X.obj ⟶ AffineSpace (ULift.{u} (Fin 1)) Y.obj) [IsIso ι]
    (j : CompactificationOf (Over.mk (ι ≫ AffineSpace (ULift.{u} (Fin 1)) Y.obj ↘ Y.obj)))
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (F : EtaleModules.{u, 0} Λ X.obj)
    (hF : IsBigSiteConstructibleEtaleModule B X Λ F) (ht : IsTorsionEtaleModule Λ X.obj F) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} _ j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          F))) := by
  let π := AffineSpace (ULift.{u} (Fin 1)) Y.obj ↘ Y.obj
  exact isConstructibleEtaleModule_homology_derivedLowerShriek_plus_of_stages B h0GKV h09YU
    (ι ≫ π) j Λ _ (fun q => ⟨isConstructibleEtaleModule_homology_singleFunctor hF q,
      isTorsionEtaleModule_homology_singleFunctor ht q⟩) k

/-- **Stacks 0GKY, from Stacks 0GKV and Stacks 09YU.** Let `Y` be a Noetherian affine scheme of
`B`, `Λ` a Noetherian ring with `m = 0` in `Λ` for some `m > 0`, `ι : U ⟶ 𝔸¹_Y` an open
immersion, `f = ι ≫ (𝔸¹_Y ⟶ Y)` the structure morphism of `U`, `j` a compactification of `f`, and
`F` a finite type locally constant sheaf of `Λ`-modules on `U`. Then every cohomology sheaf of
`Rf_! F` is constructible. The source also assumes `Y` of finite dimension, which is not needed. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_openAffineLine_of_stages
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (h09YU : ∀ (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] {I : Type u} [Preorder I] [Nonempty I]
      [IsDirected I (· ≤ ·)] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
      (hX : B.Contains c.pt), IsLimit c →
      (∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e))) →
      (∀ p : I, CompactSpace (Dg.obj (op p)).obj) →
      (∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) →
      SmallEtaleStagesEssSurj B (ModuleCat.{u + 1} Λ) Dg c hX
        (fun Z => IsConstructibleModuleSheaf B Z Λ))
    (Y : B.Scheme) [IsNoetherian Y.obj] [IsAffine Y.obj] (U : B.Scheme)
    (ι : U.obj ⟶ AffineSpace (ULift.{u} (Fin 1)) Y.obj) [IsOpenImmersion ι]
    (j : CompactificationOf (Over.mk (ι ≫ AffineSpace (ULift.{u} (Fin 1)) Y.obj ↘ Y.obj)))
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (F : EtaleModules.{u, 0} Λ U.obj)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ U.obj.smallEtaleTopology F) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} _ j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          F))) := by
  let π := AffineSpace (ULift.{u} (Fin 1)) Y.obj ↘ Y.obj
  have : IsLocallyNoetherian Y.obj := IsNoetherian.toIsLocallyNoetherian
  have : IsLocallyNoetherian (AffineSpace (ULift.{u} (Fin 1)) Y.obj) :=
    LocallyOfFiniteType.isLocallyNoetherian π
  have hc : IsBigSiteConstructibleEtaleModule B U Λ F := by
    letI := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B U Λ
    exact isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant B U Λ _
      ((SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff B U Λ F).mpr hF)
  exact isConstructibleEtaleModule_homology_derivedLowerShriek_of_torsion B Λ m hm hΛ h0GKV
    (h09YU Λ) (ι ≫ π) j F hc k

/-! ### The unbounded case -/

/-- **On bounded below complexes `Rf_!` on `D(X_étale)` is `Rf_!` on `D⁺(X_étale)`**: the
extension by zero `j_!` is exact on both sides, and the derived direct image on `D⁺` is the
restriction of the one on `D` (`CategoryTheory.Functor.boundedDerivedIso`). -/
theorem nonempty_ι_obj_derivedLowerShriek_iso (Λ : Type) [Ring Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (j : CompactificationOf (Over.mk f))
    (E : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) :
    Nonempty (DerivedCategory.Plus.ι.obj ((derivedLowerShriek.{u, 0} f j Λ).obj E) ≅
      (derivedLowerShriekUnbounded.{u, 0} f j Λ).obj (DerivedCategory.Plus.ι.obj E)) := by
  let F := etaleModuleDirectImage.{u, 0} Λ j.toBase
  let RF := etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ j.toBase
  let α := Stacks.Injectives.KInjectiveResolution.homotopyCategoryUnit F RF
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ j.toBase)
  let J := etaleModuleExtensionByZero.{u, 0} Λ j.immersion
  let e₁ := (Functor.boundedDerivedIso F RF α
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _)).app
      ((etaleModuleDerivedExtensionByZero.{u, 0} Λ j.immersion).obj E)
  let e₂ : DerivedCategory.Plus.ι.obj
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ j.immersion).obj E) ≅
      (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ j.immersion).obj
        (DerivedCategory.Plus.ι.obj E) :=
    DerivedCategory.Plus.ι.mapIso (J.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app E) ≪≫
      ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ j.immersion).app
        (DerivedCategory.Plus.ι.obj E)).symm
  exact ⟨e₁ ≪≫ RF.mapIso e₂⟩

/-- **Stacks 0GL0 for `D_c` over a torsion ring, from Stacks 0GKV and Stacks 09YU.** Let
`f : X ⟶ Y` be a separated morphism of finite presentation of schemes of `B`, with `Y`
quasi-compact and quasi-separated, `j` a compactification of `f`, `Λ` a Noetherian ring with
`m = 0` in `Λ` for some `m > 0`, and `K` an object of `D(X_étale, Λ)` whose cohomology sheaves are
constructible. Then every cohomology sheaf of `Rf_! K` is constructible. By Stacks 0G2A,
`H^n(Rf_! K) = H^n(Rf_!(τ_{≥ n - N} τ_{≤ n} K))`, and the bounded complex
`τ_{≥ n - N} τ_{≤ n} K` is handled by
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_plus_of_stages`. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriekUnbounded_of_stages
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (h09YU : ∀ (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] {I : Type u} [Preorder I] [Nonempty I]
      [IsDirected I (· ≤ ·)] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
      (hX : B.Contains c.pt), IsLimit c →
      (∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e))) →
      (∀ p : I, CompactSpace (Dg.obj (op p)).obj) →
      (∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) →
      SmallEtaleStagesEssSurj B (ModuleCat.{u + 1} Λ) Dg c hX
        (fun Z => IsConstructibleModuleSheaf B Z Λ))
    {X Y : B.Scheme} [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj] (f : X.obj ⟶ Y.obj)
    [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    (j : CompactificationOf (Over.mk f)) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]
    (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0) (K : DerivedCategory (EtaleModules.{u, 0} Λ X.obj))
    (hK : ∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ ((DerivedCategory.homologyFunctor _ q).obj K))
    (n : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.homologyFunctor _ n).obj
      ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj K)) := by
  have : CompactSpace j.space := QuasiCompact.compactSpace_of_compactSpace j.toBase
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_fiber_le j.toBase
  let N : ℤ := (2 * d : ℕ)
  let t := DerivedCategory.TStructure.t (C := EtaleModules.{u, 0} Λ X.obj)
  let H := DerivedCategory.homologyFunctor (EtaleModules.{u, 0} Λ Y.obj) n
  let R := derivedLowerShriekUnbounded.{u, 0} f j Λ
  let K₁ := (t.truncLE n).obj K
  let K₂ := (t.truncGE (n - N)).obj K₁
  have h₁ := (bounded_derivedLowerShriekUnbounded Λ f j m hm hΛ d hd K).1 n n le_rfl
  have h₂ := (bounded_derivedLowerShriekUnbounded Λ f j m hm hΛ d hd K₁).2.1 n n le_rfl
  let e : H.obj (R.obj K) ≅ H.obj (R.obj K₂) :=
    (asIso (H.map (R.map ((t.truncLEι n).app K)))).symm ≪≫
      asIso (H.map (R.map ((t.truncGEπ (n - N)).app K₁)))
  -- the bounded complex `K₂` as an object of `D⁺`
  have : K₂.IsGE (n - N) := t.isGE_truncGE_obj K₁ (n - N) (n - N)
  let E : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X.obj) := ⟨K₂, ⟨n - N, inferInstance⟩⟩
  have hE : ∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
      ((DerivedCategory.Plus.homologyFunctor _ q).obj E) ∧
      IsTorsionEtaleModule Λ X.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj E) := by
    intro q
    refine ⟨?_, isTorsionEtaleModule_of_natCast_eq_zero Λ m hm hΛ _⟩
    change IsBigSiteConstructibleEtaleModule B X Λ ((DerivedCategory.homologyFunctor _ q).obj K₂)
    by_cases hq : q < n - N
    · exact isConstructibleEtaleModule_of_isZero B Λ X
        (DerivedCategory.isZero_of_isGE K₂ (n - N) q hq)
    have := DerivedCategory.isIso_homologyMap_truncGEπ_app (n - N) q (by omega) K₁
    refine IsBigSiteConstructibleEtaleModule.of_iso B Λ
      (asIso ((DerivedCategory.homologyFunctor _ q).map ((t.truncGEπ (n - N)).app K₁))) ?_
    by_cases hqn : n < q
    · have : K₁.IsLE n := t.isLE_truncLE_obj K n n
      exact isConstructibleEtaleModule_of_isZero B Λ X
        (DerivedCategory.isZero_of_isLE K₁ n q hqn)
    have := Stacks.TruncationLevel.isIso_homologyMap_truncLEι_app n q (by omega) K
    exact IsBigSiteConstructibleEtaleModule.of_iso B Λ
      (asIso ((DerivedCategory.homologyFunctor _ q).map ((t.truncLEι n).app K))).symm (hK q)
  have hc := isConstructibleEtaleModule_homology_derivedLowerShriek_plus_of_stages B h0GKV h09YU f j
    Λ E hE n
  obtain ⟨e'⟩ := nonempty_ι_obj_derivedLowerShriek_iso Λ f j E
  exact IsBigSiteConstructibleEtaleModule.of_iso B Λ ((H.mapIso e') ≪≫ e.symm) hc

end Stacks.EtaleCohomology

end
