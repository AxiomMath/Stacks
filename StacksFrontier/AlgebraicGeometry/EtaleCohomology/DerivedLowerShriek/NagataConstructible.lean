module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.AffineLineNagata
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.FiniteDirectImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersectionAffine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence

/-!
# Constructibility of `Rf_!` over a Nagata base

Let `Y` be a Noetherian Nagata scheme, `f : X ⟶ Y` separated of finite type, `Λ` a torsion
Noetherian ring and `F` a constructible sheaf of `Λ`-modules on `X`. Then every cohomology sheaf
of `Rf_! F` is constructible. This is Stacks 0GL0 over a Nagata base; the general case passes to
a base of finite type over `ℤ` by Stacks 09YU.

The proof is the source's. The question is local on `Y`, so `Y` may be taken affine; by Noetherian
induction on `X` and the triangle of Stacks 0GKP, `X` may be taken affine; a closed immersion
`X ⟶ 𝔸ⁿ_Y` and Stacks 0F7J for it reduce to `X = 𝔸ⁿ_Y`; and `𝔸ⁿ⁺¹_Y ⟶ 𝔸¹_Y ⟶ Y` with Stacks 0F7J
and the dévissage of Stacks 015J reduce to Stacks 0GKZ over a Nagata base
(`isConstructibleEtaleModule_homology_derivedLowerShriek_affineLine_of_isNagataScheme`).

Stacks 0GKV enters as the hypothesis `h0GKV` until it lands.

## Main results

* `Stacks.EtaleCohomology.nonempty_rightDerived_iso_homology_derivedLowerShriek_singleFunctor`:
  `R^p f̄_*(j_! F) = H^p(Rf_! F)`.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_forall_sheaf`:
  the dévissage from sheaves to bounded below complexes.
* `isConstructibleEtaleModule_homology_derivedLowerShriek_affineSpace_of_isNagataScheme`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Topology TopologicalSpace

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

-- instances of `Stacks.Models.RegularModelSituation` whose conclusions (`QuasiCompact ?f`, ...)
-- match every goal and send instance search into a loop; they are irrelevant here
attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

/-- **`R^p f̄_*(j_! F) = H^p(Rf_! F)`** for a sheaf `F` placed in degree `0`: `Rf_! = Rf̄_* ∘ Rj_!`
and `Rj_!(F[0]) = (j_! F)[0]`, extension by zero being exact. -/
theorem nonempty_rightDerived_iso_homology_derivedLowerShriek_singleFunctor {X Y : Scheme.{u}}
    (f : X ⟶ Y) (j : CompactificationOf (Over.mk f)) (Λ : Type) [Ring Λ]
    (F : EtaleModules.{u, 0} Λ X) (p : ℕ) :
    Nonempty (((etaleModuleDirectImage.{u, 0} Λ j.toBase).rightDerived p).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F) ≅
      (DerivedCategory.Plus.homologyFunctor _ p).obj
        ((derivedLowerShriek.{u, 0} f j Λ).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  let E := etaleModuleExtensionByZero.{u, 0} Λ j.immersion
  let e₁ : (etaleModuleDerivedExtensionByZero.{u, 0} Λ j.immersion).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj (E.obj F) :=
    E.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app _ ≪≫
      DerivedCategory.Plus.ι.preimageIso ((E.mapDerivedCategorySingleFunctor 0).app F)
  exact ⟨(rightDerivedPlusObjIso (etaleModuleDirectImage.{u, 0} Λ j.toBase) (E.obj F) p).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ j.toBase).mapIso e₁.symm)⟩

/-- **The dévissage of Stacks 015J for `Rf_!`, in terms of `Rf_!` on sheaves.** If every
cohomology sheaf of `Rf_! G` is constructible for every constructible torsion sheaf `G`, then so
is every cohomology sheaf of `Rf_! K` for every bounded below `K` with constructible torsion
cohomology sheaves. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_forall_sheaf
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X.obj ⟶ Y.obj)
    (j : CompactificationOf (Over.mk f)) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]
    (h : ∀ G : EtaleModules.{u, 0} Λ X.obj, IsBigSiteConstructibleEtaleModule B X Λ G →
      IsTorsionEtaleModule Λ X.obj G → ∀ p : ℕ,
        IsBigSiteConstructibleEtaleModule B Y Λ
          ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
          ((derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G))))
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X.obj))
    (hK : ∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
        ((DerivedCategory.Plus.homologyFunctor _ q).obj K) ∧
      IsTorsionEtaleModule Λ X.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K))
    (n : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ
      ((DerivedCategory.Plus.homologyFunctor _ n).obj ((derivedLowerShriek.{u, 0} f j Λ).obj K)) :=
  isConstructibleEtaleModule_homology_derivedLowerShriek_of_sheaf B f j Λ
    (fun G hG ht p => IsBigSiteConstructibleEtaleModule.of_iso B Λ
      (nonempty_rightDerived_iso_homology_derivedLowerShriek_singleFunctor f j Λ G p).some.symm
      (h G hG ht p)) K hK n


variable (B : BigEtaleSite.{u})

/-- If `m > 0` is zero in `Λ`, every object of `D⁺(X_étale, Λ)` has torsion cohomology sheaves. -/
private theorem isTorsionPlus_of_natCast_eq_zero {X : Scheme.{u}} {Λ : Type} [Ring Λ] {m : ℕ}
    (hm : 0 < m) (hΛ : (m : Λ) = 0) {K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)} :
    isTorsionPlus.{u, 0} Λ X K :=
  fun _ => isTorsionEtaleModule_of_natCast_eq_zero Λ m hm hΛ _

/-- Constructibility of the `k`-th cohomology sheaf is transported along isomorphisms in `D⁺`. -/
private theorem isConstructibleEtaleModule_homology_of_iso {Y : B.Scheme} {Λ : Type} [CommRing Λ]
    [IsNoetherianRing Λ] {K L : DerivedCategory.Plus (EtaleModules.{u, 0} Λ Y.obj)} (e : K ≅ L)
    {k : ℤ} (h : IsBigSiteConstructibleEtaleModule B Y Λ
      ((DerivedCategory.Plus.homologyFunctor _ k).obj K)) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj L) :=
  IsBigSiteConstructibleEtaleModule.of_iso B Λ
    ((DerivedCategory.Plus.homologyFunctor _ k).mapIso e) h

/-- **Stacks 0GL0 for affine space over a Nagata base, from Stacks 0GKV.** Let `Y` be a Noetherian
Nagata scheme of `B`, `X ≅ 𝔸ʳ_Y`, `j` a compactification of `X ⟶ Y`, `Λ` a Noetherian ring with
`m = 0` in `Λ` for some `m > 0`, and `F` a constructible sheaf of `Λ`-modules on `X`. Then every
cohomology sheaf of `Rf_! F` is constructible. By induction on `r`: `𝔸ʳ⁺¹_Y = 𝔸ʳ_{𝔸¹_Y}`, so by
Stacks 0F7J `Rf_! = R(𝔸¹_Y → Y)_! ∘ R(𝔸ʳ⁺¹_Y → 𝔸¹_Y)_!`; the inner functor is handled by
induction over the Nagata scheme `𝔸¹_Y`, and the outer one by Stacks 0GKZ over a Nagata base and
the dévissage of Stacks 015J. For `r = 0` the morphism is an isomorphism, so Stacks 0GK3 applies.
`h0GKV` is Stacks 0GKV. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_affineSpace_of_isNagataScheme
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (r : ℕ) :
    ∀ (Y : B.Scheme) [IsNoetherian Y.obj], IsNagataScheme Y.obj → ∀ (X : B.Scheme)
      (e : X.obj ≅ AffineSpace (ULift.{u} (Fin r)) Y.obj)
      (j : CompactificationOf (Over.mk (e.hom ≫ AffineSpace (ULift.{u} (Fin r)) Y.obj ↘ Y.obj)))
      (F : EtaleModules.{u, 0} Λ X.obj), IsBigSiteConstructibleEtaleModule B X Λ F → ∀ k : ℤ,
        IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
          ((derivedLowerShriek.{u, 0} _ j Λ).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  induction r with
  | zero =>
    intro Y _ hY X e j F hF k
    have : IsLocallyNoetherian Y.obj := IsNoetherian.toIsLocallyNoetherian
    let g := e.hom ≫ AffineSpace (ULift.{u} (Fin 0)) Y.obj ↘ Y.obj
    have : IsIso g := inferInstance
    have : IsSeparated g := inferInstance
    have : LocallyQuasiFinite g := inferInstance
    have : QuasiCompact g := inferInstance
    have : LocallyOfFinitePresentation g := inferInstance
    exact isConstructibleEtaleModule_homology_derivedLowerShriek_of_quasiFinite B (X := X)
      (Y := Y) g Λ j _ (fun q => ⟨isConstructibleEtaleModule_homology_singleFunctor hF q,
        isTorsionEtaleModule_of_natCast_eq_zero Λ m hm hΛ _⟩) k
  | succ r ih =>
    intro Y _ hY X e j F hF k
    have : IsLocallyNoetherian Y.obj := IsNoetherian.toIsLocallyNoetherian
    let T := Y.obj
    let A1 := AffineSpace (ULift.{u} (Fin 1)) T
    let Ar := AffineSpace (ULift.{u} (Fin r)) A1
    let a : Ar ⟶ A1 := Ar ↘ A1
    let b : A1 ⟶ T := A1 ↘ T
    let s := e ≪≫ Stacks.Chow.affineSpaceSuccIso T r
    let f₁ : X.obj ⟶ A1 := s.hom ≫ a
    have hab : f₁ ≫ b = e.hom ≫ AffineSpace (ULift.{u} (Fin (r + 1))) T ↘ T := by
      simp only [f₁, s, a, b, Iso.trans_hom, Category.assoc]
      rw [Stacks.Chow.affineSpaceSuccIso_hom_over]
    -- the scheme `𝔸¹_Y` of `B`, Noetherian and Nagata
    have : LocallyOfFinitePresentation b := inferInstance
    have : LocallyOfFiniteType b := inferInstance
    have : QuasiCompact b := inferInstance
    have : IsSeparated b := inferInstance
    have hA1 : B.Contains A1 := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact b Y.property
    let A1B : B.Scheme := B.obj A1 hA1
    have : IsLocallyNoetherian A1 := LocallyOfFiniteType.isLocallyNoetherian b
    have : CompactSpace A1 := QuasiCompact.compactSpace_of_compactSpace b
    have : IsNoetherian A1B.obj := ⟨⟩
    have : QuasiSeparatedSpace A1 := inferInstance
    have hA1N : IsNagataScheme A1B.obj := isNagataScheme_of_locallyOfFiniteType b hY
    have : LocallyOfFiniteType a := inferInstance
    have : QuasiCompact a := inferInstance
    have : IsSeparated a := inferInstance
    have : LocallyOfFiniteType f₁ := inferInstance
    have : QuasiCompact f₁ := inferInstance
    have : IsSeparated f₁ := inferInstance
    have : QuasiSeparated f₁ := IsSeparated.instQuasiSeparated f₁
    have : QuasiSeparated b := IsSeparated.instQuasiSeparated b
    have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f₁
    have : QuasiSeparatedSpace X.obj := quasiSeparatedSpace_of_quasiSeparated f₁
    obtain ⟨j₁⟩ : Nonempty (CompactificationOf (Over.mk f₁)) := IsCofiltered.nonempty
    obtain ⟨jb⟩ : Nonempty (CompactificationOf (Over.mk b)) := IsCofiltered.nonempty
    obtain ⟨jb'⟩ : Nonempty (CompactificationOf (Over.mk (𝟙 A1 ≫ b))) := IsCofiltered.nonempty
    obtain ⟨jc⟩ : Nonempty (CompactificationOf (Over.mk (f₁ ≫ b))) := IsCofiltered.nonempty
    -- the inner step, by induction over `𝔸¹_Y`
    have hin : ∀ q : ℤ, IsBigSiteConstructibleEtaleModule B A1B Λ
        ((DerivedCategory.Plus.homologyFunctor _ q).obj ((derivedLowerShriek.{u, 0} f₁ j₁ Λ).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
      ih A1B hA1N X s j₁ F hF
    -- the outer step, Stacks 0GKZ over a Nagata base and the dévissage
    have hout : ∀ G : EtaleModules.{u, 0} Λ A1B.obj, IsBigSiteConstructibleEtaleModule B A1B Λ G →
        IsTorsionEtaleModule Λ A1B.obj G → ∀ p : ℕ,
          IsBigSiteConstructibleEtaleModule B Y Λ
            ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
            ((derivedLowerShriek.{u, 0} b jb Λ).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) := fun G hG _ p =>
      isConstructibleEtaleModule_homology_derivedLowerShriek_of_eq B (Category.id_comp b) jb' jb Λ
        _ (isTorsionPlus_of_natCast_eq_zero hm hΛ) _
        (isConstructibleEtaleModule_homology_derivedLowerShriek_affineLine_of_isNagataScheme B Y hY
          A1B (𝟙 A1) jb' Λ m hm hΛ h0GKV G hG p)
    let K := (derivedLowerShriek.{u, 0} f₁ j₁ Λ).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
    have hK := isConstructibleEtaleModule_homology_derivedLowerShriek_of_forall_sheaf B (X := A1B)
      (Y := Y) b jb Λ hout K
      (fun q => ⟨hin q, isTorsionEtaleModule_of_natCast_eq_zero Λ m hm hΛ _⟩) k
    -- Stacks 0F7J for `f₁ ≫ b`, then the change of compactification
    have hF0 : isTorsionPlus.{u, 0} Λ X.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F) :=
      isTorsionPlus_of_natCast_eq_zero hm hΛ
    let eC := (derivedLowerShriekCompIso Λ f₁ b j₁ jb jc).app
      ⟨(DerivedCategory.Plus.singleFunctor _ 0).obj F, hF0⟩
    exact isConstructibleEtaleModule_homology_derivedLowerShriek_of_eq B hab jc j Λ _ hF0 k
      (isConstructibleEtaleModule_homology_of_iso B eC.symm hK)


/-- **Stacks 0GL0 for an affine source over an affine Nagata base, from Stacks 0GKV.** A closed
immersion `h : U ⟶ 𝔸ⁿ_Y` over `Y` and Stacks 0F7J for the finite `h` give
`R(U → Y)_! G = R(𝔸ⁿ_Y → Y)_!(h_* G)`, with `h_* G` constructible (Stacks 095R). `h0GKV` is
Stacks 0GKV. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_isAffine_of_isNagataScheme
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (Y : B.Scheme) [IsNoetherian Y.obj] [IsAffine Y.obj] (hY : IsNagataScheme Y.obj)
    (U : B.Scheme) [IsAffine U.obj] (g : U.obj ⟶ Y.obj) [IsSeparated g] [LocallyOfFiniteType g]
    (j : CompactificationOf (Over.mk g)) (G : EtaleModules.{u, 0} Λ U.obj)
    (hG : IsBigSiteConstructibleEtaleModule B U Λ G) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} g j Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) := by
  have : IsLocallyNoetherian Y.obj := IsNoetherian.toIsLocallyNoetherian
  have : LocallyOfFinitePresentation g := inferInstance
  obtain ⟨n, h, hh, hfac⟩ := exists_closedImmersion_affineSpace_of_lfp g
  have : IsClosedImmersion h := hh
  let An := AffineSpace (ULift.{u} (Fin n)) Y.obj
  let π : An ⟶ Y.obj := An ↘ Y.obj
  have : LocallyOfFinitePresentation π := inferInstance
  have : LocallyOfFiniteType π := inferInstance
  have : QuasiCompact π := inferInstance
  have : IsSeparated π := inferInstance
  have : QuasiSeparated π := IsSeparated.instQuasiSeparated π
  have hAn : B.Contains An := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact π Y.property
  let AnB : B.Scheme := B.obj An hAn
  let hB : U ⟶ AnB := ObjectProperty.homMk h
  have : IsLocallyNoetherian An := LocallyOfFiniteType.isLocallyNoetherian π
  have : CompactSpace An := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace An := inferInstance
  have : IsFinite h := inferInstance
  have : LocallyOfFinitePresentation h := inferInstance
  have : IsFinite (B.inclusion.map hB) := inferInstanceAs (IsFinite h)
  have : LocallyOfFinitePresentation (B.inclusion.map hB) :=
    inferInstanceAs (LocallyOfFinitePresentation h)
  have hhG := isConstructibleEtaleModule_directImage_of_isFinite B Λ hB hG
  have : IsSeparated (h ≫ π) := inferInstance
  have : LocallyOfFiniteType (h ≫ π) := inferInstance
  have : QuasiCompact (h ≫ π) := inferInstance
  obtain ⟨jπ⟩ : Nonempty (CompactificationOf (Over.mk π)) := IsCofiltered.nonempty
  obtain ⟨jπ'⟩ : Nonempty (CompactificationOf (Over.mk ((Iso.refl An).hom ≫ π))) :=
    IsCofiltered.nonempty
  obtain ⟨jh⟩ : Nonempty (CompactificationOf (Over.mk (h ≫ π))) := IsCofiltered.nonempty
  have hE := isConstructibleEtaleModule_homology_derivedLowerShriek_affineSpace_of_isNagataScheme
    B Λ m hm hΛ h0GKV n Y hY AnB (Iso.refl An) jπ' _ hhG k
  have hE' := isConstructibleEtaleModule_homology_derivedLowerShriek_of_eq B
    (Category.id_comp π) jπ' jπ Λ _ (isTorsionPlus_of_natCast_eq_zero hm hΛ)
    k hE
  have : CompactSpace U.obj := QuasiCompact.compactSpace_of_compactSpace (h ≫ π)
  have : QuasiSeparatedSpace U.obj := quasiSeparatedSpace_of_quasiSeparated (h ≫ π)
  have hG0 : isTorsionPlus.{u, 0} Λ U.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G) :=
    isTorsionPlus_of_natCast_eq_zero hm hΛ
  obtain ⟨e₀⟩ := nonempty_derivedDirectImage_singleFunctor_iso_of_isIntegralHom h Λ G
  let eC := (derivedLowerShriekCompDirectImageIsoOfIsFinite Λ h π jπ jh).app
    ⟨(DerivedCategory.Plus.singleFunctor _ 0).obj G, hG0⟩
  refine isConstructibleEtaleModule_homology_derivedLowerShriek_of_eq B hfac jh j Λ _ hG0 k ?_
  exact isConstructibleEtaleModule_homology_of_iso B
    (eC ≪≫ (derivedLowerShriek.{u, 0} π jπ Λ).mapIso e₀).symm hE'

/-- **Stacks 0GL0 over an affine Nagata base, from Stacks 0GKV.** Let `Y` be an affine Noetherian
Nagata scheme of `B`, `f : X ⟶ Y` separated of finite type and `F` a constructible sheaf of
`Λ`-modules on `X`, over a Noetherian ring with `m = 0` for some `m > 0`. Then every cohomology
sheaf of `Rf_! F` is constructible. By Noetherian induction on the closed subschemes of `X`: for a
nonempty one `Z`, an affine open `U ⊆ Z` and the triangle of Stacks 0GKP reduce to the affine case
for `U` and to the induction hypothesis for the complement of `U`. `h0GKV` is Stacks 0GKV. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_isAffine_base_of_isNagataScheme
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (Y : B.Scheme) [IsNoetherian Y.obj] [IsAffine Y.obj] (hY : IsNagataScheme Y.obj)
    (X : B.Scheme) (f : X.obj ⟶ Y.obj) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j : CompactificationOf (Over.mk f)) (F : EtaleModules.{u, 0} Λ X.obj)
    (hF : IsBigSiteConstructibleEtaleModule B X Λ F) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  have : IsLocallyNoetherian Y.obj := IsNoetherian.toIsLocallyNoetherian
  have : IsLocallyNoetherian X.obj := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X.obj := ⟨⟩
  have : QuasiSeparated f := IsSeparated.instQuasiSeparated f
  suffices H : ∀ C : Closeds X.obj, ∀ (Z : B.Scheme) (i : Z ⟶ X),
      IsClosedImmersion (B.inclusion.map i) → Set.range (B.inclusion.map i).base ⊆ (C : Set X.obj) →
      ∀ (j : CompactificationOf (Over.mk (B.inclusion.map i ≫ f)))
        (G : EtaleModules.{u, 0} Λ Z.obj), IsBigSiteConstructibleEtaleModule B Z Λ G → ∀ k : ℤ,
        IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
          ((derivedLowerShriek.{u, 0} _ j Λ).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) by
    obtain ⟨j'⟩ : Nonempty (CompactificationOf (Over.mk (B.inclusion.map (𝟙 X) ≫ f))) :=
      IsCofiltered.nonempty
    exact isConstructibleEtaleModule_homology_derivedLowerShriek_of_eq B
      (by simp : B.inclusion.map (𝟙 X) ≫ f = f) j' j Λ _
      (isTorsionPlus_of_natCast_eq_zero hm hΛ) k
      (H ⊤ X (𝟙 X) (inferInstanceAs (IsClosedImmersion (𝟙 X.obj))) (fun _ _ => trivial) j' F hF k)
  intro C
  induction C using WellFoundedLT.induction with
  | _ C ih =>
  intro Z i hi hC j G hG k
  let i' : Z.obj ⟶ X.obj := B.inclusion.map i
  have : IsClosedImmersion i' := hi
  have : IsFinite i' := inferInstance
  have : LocallyOfFiniteType i' := inferInstance
  have : QuasiCompact i' := inferInstance
  have : IsLocallyNoetherian Z.obj := LocallyOfFiniteType.isLocallyNoetherian i'
  have : CompactSpace Z.obj := QuasiCompact.compactSpace_of_compactSpace i'
  have : IsNoetherian Z.obj := ⟨⟩
  have : QuasiSeparatedSpace Z.obj := inferInstance
  by_cases hZ : Nonempty Z.obj
  swap
  · rw [not_nonempty_iff] at hZ
    exact isConstructibleEtaleModule_of_isZero B Λ Y (Functor.map_isZero _ (Functor.map_isZero _
      (Functor.map_isZero _ (isZero_etaleModulesUniv_of_isEmpty Λ Z.obj G))))
  obtain ⟨z⟩ := hZ
  obtain ⟨_, ⟨U₀, hU, rfl⟩, hzU, -⟩ :=
    Z.obj.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  let U : Z.obj.Opens := U₀
  have : IsAffine U.toScheme := hU
  have : QuasiCompact U.ι := inferInstance
  have hUB : B.Contains U.toScheme :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact U.ι Z.property
  let UB : B.Scheme := B.obj U.toScheme hUB
  let uB : UB ⟶ Z := ObjectProperty.homMk U.ι
  let ci := closedComplementι U.ι
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ Z.obj) 0).obj G
  obtain ⟨a, b, c, hT⟩ := exists_distTriang_derivedLowerShriek_openClosed_plus Λ j U.ι ci
    (range_eq_compl_range_closedComplementι U.ι) K
  have hQ := isWeakSerreClass_isBigSiteConstructibleEtaleModule B Y Λ
  -- the affine open part
  have hGU := isConstructibleEtaleModule_inverseImage B Λ uB hG
  obtain ⟨eU⟩ := nonempty_restriction_singleFunctor_iso U.ι G
  have h₁ : ∀ q : ℤ, IsBigSiteConstructibleEtaleModule B Y Λ
      ((DerivedCategory.Plus.homologyFunctor _ q).obj (Triangle.mk a b c).obj₁) := fun q =>
    isConstructibleEtaleModule_homology_of_iso B ((derivedLowerShriek.{u, 0} _ _ Λ).mapIso eU.symm)
      (isConstructibleEtaleModule_homology_derivedLowerShriek_of_isAffine_of_isNagataScheme B Λ m
        hm hΛ h0GKV Y hY UB (U.ι ≫ i' ≫ f) (j.restrictOpen U.ι) _ hGU q)
  -- the closed complement, by induction
  have : IsClosedImmersion ci := inferInstance
  have : LocallyOfFiniteType ci := inferInstance
  have : QuasiCompact ci := inferInstance
  have hZ'B : B.Contains (closedComplement U.ι) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact ci Z.property
  let Z'B : B.Scheme := B.obj (closedComplement U.ι) hZ'B
  let ciB : Z'B ⟶ Z := ObjectProperty.homMk ci
  have hci : IsClosedImmersion (B.inclusion.map (ciB ≫ i)) :=
    inferInstanceAs (IsClosedImmersion (ci ≫ i'))
  let C' : Closeds X.obj := ⟨Set.range (ci ≫ i').base, (ci ≫ i').isClosedEmbedding.isClosed_range⟩
  have hC'C : C' < C := by
    refine lt_of_le_of_ne (fun x ⟨y, hy⟩ => hC ⟨ci y, hy⟩) fun hEq => ?_
    have hzC : i' z ∈ (C : Set X.obj) := hC ⟨z, rfl⟩
    rw [← hEq] at hzC
    obtain ⟨y, hy⟩ := hzC
    have hyz : ci y = z := i'.isClosedEmbedding.injective hy
    have hr : Set.range U.ι.base = (Set.range ci.base)ᶜ :=
      range_eq_compl_range_closedComplementι U.ι
    have hzU' : z ∈ Set.range U.ι.base := by rw [Scheme.Opens.range_ι]; exact hzU
    rw [hr] at hzU'
    exact hzU' ⟨y, hyz⟩
  have hGZ' := isConstructibleEtaleModule_inverseImage B Λ ciB hG
  obtain ⟨eZ⟩ := nonempty_inverseImage_singleFunctor_iso ci G
  have : IsSeparated (ci ≫ i' ≫ f) := inferInstance
  have : LocallyOfFiniteType (ci ≫ i' ≫ f) := inferInstance
  have : QuasiCompact (ci ≫ i' ≫ f) := inferInstance
  obtain ⟨jZ⟩ : Nonempty (CompactificationOf (Over.mk (B.inclusion.map (ciB ≫ i) ≫ f))) :=
    IsCofiltered.nonempty
  have h₃ : ∀ q : ℤ, IsBigSiteConstructibleEtaleModule B Y Λ
      ((DerivedCategory.Plus.homologyFunctor _ q).obj (Triangle.mk a b c).obj₃) := fun q =>
    isConstructibleEtaleModule_homology_of_iso B ((derivedLowerShriek.{u, 0} _ _ Λ).mapIso eZ.symm)
      (isConstructibleEtaleModule_homology_derivedLowerShriek_of_eq B
        (by simp; rfl : B.inclusion.map (ciB ≫ i) ≫ f = ci ≫ i' ≫ f) jZ
        (j.restrictClosed ci) Λ _ (isTorsionPlus_of_natCast_eq_zero hm hΛ) q
        (ih C' hC'C Z'B (ciB ≫ i) hci (fun _ hx => hx) jZ _ hGZ' q))
  exact prop_homology_obj₂_of_distTriang_plus (IsBigSiteConstructibleEtaleModule B Y Λ) _ hT h₁ h₃ k


/-- **Stacks 0GL0 over a Nagata base, for sheaves, from Stacks 0GKV.** Let `Y` be a Noetherian
Nagata scheme of `B`, `f : X ⟶ Y` separated of finite type, `j` a compactification of `f`, `Λ` a
Noetherian ring with `m = 0` in `Λ` for some `m > 0`, and `F` a constructible sheaf of
`Λ`-modules on `X`. Then every cohomology sheaf of `Rf_! F` is constructible. The question is
local on `Y` (Noetherian induction,
`Stacks.EtaleCohomology.isConstructibleEtaleModule_of_forall_isIntegral_isNormal`,
and base change, Stacks 0F7L, to an affine open), which reduces it to
`isConstructibleEtaleModule_homology_derivedLowerShriek_of_isAffine_base_of_isNagataScheme`.
`h0GKV` is Stacks 0GKV. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_isNagataScheme
    (Y : B.Scheme) [IsNoetherian Y.obj] (hY : IsNagataScheme Y.obj) (X : B.Scheme)
    (f : X.obj ⟶ Y.obj) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j : CompactificationOf (Over.mk f)) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]
    (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (F : EtaleModules.{u, 0} Λ X.obj) (hF : IsBigSiteConstructibleEtaleModule B X Λ F) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  refine isConstructibleEtaleModule_of_forall_isIntegral_isNormal B Λ Y hY _
    (fun T w hw hwq _ _ => ?_)
  let w' : T.obj ⟶ Y.obj := B.inclusion.map w
  have : LocallyOfFiniteType w' := hw
  have : QuasiCompact w' := hwq
  have : IsLocallyNoetherian Y.obj := IsNoetherian.toIsLocallyNoetherian
  have : IsLocallyNoetherian T.obj := LocallyOfFiniteType.isLocallyNoetherian w'
  have : CompactSpace T.obj := QuasiCompact.compactSpace_of_compactSpace w'
  have : IsNoetherian T.obj := ⟨⟩
  -- a nonempty affine open `W` of `T`
  obtain ⟨t⟩ : Nonempty T.obj := inferInstance
  obtain ⟨_, ⟨W₀, hW, rfl⟩, htW, -⟩ :=
    T.obj.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ t) isOpen_univ
  let W : T.obj.Opens := W₀
  have : IsAffine W.toScheme := hW
  have : QuasiCompact W.ι := inferInstance
  have hWB : B.Contains W.toScheme :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact W.ι T.property
  let WB : B.Scheme := B.obj W.toScheme hWB
  let wB : WB ⟶ T := ObjectProperty.homMk W.ι
  let v : W.toScheme ⟶ Y.obj := W.ι ≫ w'
  have : LocallyOfFiniteType v := inferInstance
  have : QuasiCompact v := inferInstance
  have : IsLocallyNoetherian W.toScheme := inferInstance
  have : CompactSpace W.toScheme := QuasiCompact.compactSpace_of_compactSpace v
  have : IsNoetherian WB.obj := ⟨⟩
  have : IsAffine WB.obj := inferInstanceAs (IsAffine W.toScheme)
  have hWN : IsNagataScheme WB.obj := isNagataScheme_of_locallyOfFiniteType v hY
  -- the base change of `f` to `W`
  have sq := IsPullback.of_hasPullback f v
  let fW := pullback.snd f v
  have : IsSeparated fW := MorphismProperty.of_isPullback sq ‹IsSeparated f›
  have : LocallyOfFiniteType fW := MorphismProperty.of_isPullback sq ‹_›
  have : QuasiCompact fW := MorphismProperty.of_isPullback sq ‹_›
  have : LocallyOfFiniteType (pullback.fst f v) := MorphismProperty.of_isPullback sq.flip ‹_›
  have : QuasiCompact (pullback.fst f v) := MorphismProperty.of_isPullback sq.flip ‹_›
  have hXW : B.Contains (pullback f v) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (pullback.fst f v) X.property
  let XW : B.Scheme := B.obj (pullback f v) hXW
  let gB : XW ⟶ X := ObjectProperty.homMk (pullback.fst f v)
  have hFW := isConstructibleEtaleModule_inverseImage B Λ gB hF
  have hc :=
    isConstructibleEtaleModule_homology_derivedLowerShriek_of_isAffine_base_of_isNagataScheme
      B Λ m hm hΛ h0GKV WB hWN XW fW (j.baseChange sq) _ hFW k
  -- base change (Stacks 0F7L)
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X.obj) 0).obj F
  have hKt : isTorsionPlus.{u, 0} Λ X.obj K := isTorsionPlus_of_natCast_eq_zero hm hΛ
  have := isIso_derivedLowerShriekBaseChange_app Λ sq j K hKt
  let eBC := asIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq j).app K)
  obtain ⟨e₁⟩ := nonempty_homology_etaleModuleDerivedInverseImagePlus_iso Λ v
    ((derivedLowerShriek.{u, 0} f j Λ).obj K) k
  obtain ⟨e₂⟩ := nonempty_inverseImage_singleFunctor_iso (Λ := Λ) (pullback.fst f v) F
  refine ⟨WB, wB, inferInstanceAs (IsOpenImmersion W.ι), ⟨⟨t, htW⟩⟩, ?_⟩
  exact IsBigSiteConstructibleEtaleModule.of_iso B Λ
    (((DerivedCategory.Plus.homologyFunctor _ k).mapIso
      (eBC ≪≫ (derivedLowerShriek.{u, 0} fW (j.baseChange sq) Λ).mapIso e₂)).symm ≪≫ e₁) hc

/-- **Stacks 0GL0 over a Nagata base, for bounded below complexes, from Stacks 0GKV.** As
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_isNagataScheme`,
for `K` in `D⁺(X_étale, Λ)` with constructible cohomology sheaves (torsion, `Λ` being torsion):
the dévissage of Stacks 015J. `h0GKV` is Stacks 0GKV. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_plus_of_isNagataScheme
    (Y : B.Scheme) [IsNoetherian Y.obj] (hY : IsNagataScheme Y.obj) (X : B.Scheme)
    (f : X.obj ⟶ Y.obj) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j : CompactificationOf (Over.mk f)) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]
    (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X.obj))
    (hK : ∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
      ((DerivedCategory.Plus.homologyFunctor _ q).obj K)) (n : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ
      ((DerivedCategory.Plus.homologyFunctor _ n).obj ((derivedLowerShriek.{u, 0} f j Λ).obj K)) :=
  isConstructibleEtaleModule_homology_derivedLowerShriek_of_forall_sheaf B f j Λ
    (fun G hG _ p => isConstructibleEtaleModule_homology_derivedLowerShriek_of_isNagataScheme B Y hY
      X f j Λ m hm hΛ h0GKV G hG p) K
    (fun q => ⟨hK q, isTorsionEtaleModule_of_natCast_eq_zero Λ m hm hΛ _⟩) n

end Stacks.EtaleCohomology

end
