module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LocallyConstantUnibranch
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.NormalizationInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.GenericTrivializationFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SmallEtaleSitePresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerre.FiniteTypeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.DenseOpenComplement
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineSpaceBundleSmooth
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SurjectiveClosedImmersionWeights

/-!
# `Rf_!` of a constructible sheaf on an open of `𝔸¹` over a Nagata base

Let `Y` be a Noetherian Nagata scheme, `X ⊆ 𝔸¹_Y` open with structure morphism `f : X ⟶ Y`, `Λ`
a torsion Noetherian ring and `F` a constructible sheaf of `Λ`-modules on `X`. Then every
cohomology sheaf of `Rf_! F` is constructible. For `X = 𝔸¹_Y` this is Stacks 0GKZ, and for `F`
finite type locally constant it is Stacks 0GKY, both over a Nagata base; the general case of
these tags (an arbitrary affine base) passes to a base of finite type over `ℤ` by Stacks 09YU.
Stacks 0GKV is taken as the hypothesis `h0GKV`.

## Main results

All in the namespace `Stacks.EtaleCohomology`:

* `exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule`:
  a constructible sheaf on Mathlib's small étale site is finite type locally constant on an open
  neighbourhood of a generic point.
* `isConstructibleEtaleModule_homology_derivedLowerShriek_of_dense_isFiniteTypeLocallyConstant`.
* `isConstructibleEtaleModule_homology_derivedLowerShriek_affineLine_of_isNagataScheme`.

## Implementation notes

The proof follows [Stacks, Tag 0GKZ], with one change. By Noetherian induction through
normalizations (`Stacks.EtaleCohomology.isConstructibleEtaleModule_of_forall_isIntegral_isNormal`,
which uses that normalizations of integral opens of `Y` are finite, `Y` being Nagata) one may
assume `Y` integral and normal, and must find a nonempty open of `Y` over which `Rf_! F` is
constructible. Then `X` is normal and irreducible, `F` is finite type locally constant on a
nonempty open `O ⊆ X`, and over the open image `W` of `O` the open `O` is dense in every fibre,
so its closed complement is quasi-finite over `W`. The triangle of Stacks 0GKP reduces to Stacks
0GK3 for the complement and to Stacks 0GKY for `O`, which is irreducible and normal, hence
geometrically unibranch, so Stacks 0GJ0 applies to it. Stacks 0GKZ applies 0GJ0 to an open that
is only connected, where it is not available; the normalization is what supplies unibranchness.
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

section Helpers

variable (B : BigEtaleSite.{u}) {Λ : Type} [CommRing Λ] [IsNoetherianRing Λ]

omit [IsNoetherianRing Λ] in
/-- **A constructible sheaf is finite type locally constant near a generic point**, on Mathlib's
small étale site: the transport of
`exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleModuleSheaf'` (in
`AlgebraicGeometry`) along the identification of the two small étale sites. -/
theorem exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule
    (X : B.Scheme) [IsReduced X.obj] (F : EtaleModules.{u, 0} Λ X.obj)
    (hF : IsBigSiteConstructibleEtaleModule B X Λ F) {η : X.obj} (hη : η ∈ genericPoints X.obj) :
    ∃ (O : B.Scheme) (o : O ⟶ X), IsOpenImmersion (B.inclusion.map o) ∧
      η ∈ Set.range (B.inclusion.map o).base ∧
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ O.obj.smallEtaleTopology
        ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map o)).obj F) := by
  obtain ⟨O, o, ho, hηO, hc⟩ :=
    exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleModuleSheaf' B Λ X
      ((etaleModulesToSmallEtale B X Λ).obj F) hF hη
  refine ⟨O, o, ho, hηO, ?_⟩
  refine (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff B O Λ _).mp ?_
  exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ
    (etaleModulesToSmallEtalePullbackIso B Λ o F).symm hc

variable {B}

/-- The cohomology sheaves of a constructible sheaf placed in degree `0` are constructible. -/
theorem isConstructibleEtaleModule_homology_singleFunctor {X : B.Scheme}
    {F : EtaleModules.{u, 0} Λ X.obj} (hF : IsBigSiteConstructibleEtaleModule B X Λ F) (q : ℤ) :
    IsBigSiteConstructibleEtaleModule B X Λ ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · exact isConstructibleEtaleModule_of_isZero B Λ X
      (DerivedCategory.Plus.isZero_homology_of_isGE _ 0 q hq)
  · exact IsBigSiteConstructibleEtaleModule.of_iso B Λ
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).app F).symm hF
  · exact isConstructibleEtaleModule_of_isZero B Λ X
      (DerivedCategory.Plus.isZero_homology_of_isLE _ 0 q hq)

omit [IsNoetherianRing Λ] in
/-- The restriction along an étale morphism of a sheaf placed in degree `0` is its inverse image
placed in degree `0`. -/
theorem nonempty_restriction_singleFunctor_iso {X U : Scheme.{u}} (o : U ⟶ X) [Etale o]
    (F : EtaleModules.{u, 0} Λ X) :
    Nonempty ((etaleModuleRestriction.{u, 0} Λ o).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} Λ o).obj F)) := by
  let e₁ : DerivedCategory.Plus.ι.obj
        ((etaleModuleRestriction.{u, 0} Λ o).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≅
      DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleRestriction.{u, 0} Λ o).obj F)) :=
    ((etaleModuleRestriction.{u, 0} Λ o).mapDerivedCategorySingleFunctor 0).app F
  exact ⟨DerivedCategory.Plus.ι.preimageIso e₁ ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso
      ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ o).symm.app _)⟩

/-- The cohomology sheaves of the inverse image along a morphism of `B` of a constructible sheaf
placed in degree `0` are constructible and, over a torsion ring, torsion. -/
theorem isConstructibleEtaleModule_homology_inverseImage_singleFunctor {X Z : B.Scheme}
    (g : Z ⟶ X) {F : EtaleModules.{u, 0} Λ X.obj} (hF : IsBigSiteConstructibleEtaleModule B X Λ F)
    (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0) (q : ℤ) :
    IsBigSiteConstructibleEtaleModule B Z Λ ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map g)).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ∧
      IsTorsionEtaleModule Λ Z.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map g)).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  obtain ⟨e⟩ := nonempty_homology_etaleModuleDerivedInverseImagePlus_iso Λ (B.inclusion.map g)
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F) q
  exact ⟨IsBigSiteConstructibleEtaleModule.of_iso B Λ e.symm
      (isConstructibleEtaleModule_inverseImage B Λ g
        (isConstructibleEtaleModule_homology_singleFunctor hF q)),
    isTorsionEtaleModule_of_natCast_eq_zero Λ m hm hΛ _⟩

/-- **Density in the fibres from preirreducibility.** If the fibre of `f` over `s`, as a subset
of the source, is preirreducible and meets the open `O` as soon as it is nonempty, then `O` is
dense in the fibre. -/
theorem dense_fiberι_preimage_of_isPreirreducible {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    {O : Set X} (hO : IsOpen O) (hirr : IsPreirreducible (f.base ⁻¹' {s}))
    (hmeet : (f.base ⁻¹' {s}).Nonempty → (f.base ⁻¹' {s} ∩ O).Nonempty) :
    Dense ((f.fiberι s) ⁻¹' O) := by
  have hrange : Set.range (f.fiberι s) = f.base ⁻¹' {s} := Scheme.Hom.range_fiberι f s
  have hmem : ∀ c : f.fiber s, f.fiberι s c ∈ f.base ⁻¹' {s} := fun c => by
    rw [← hrange]; exact ⟨c, rfl⟩
  have hpre : IsPreirreducible (Set.univ : Set (f.fiber s)) := by
    rintro u v hu hv ⟨a, -, ha⟩ ⟨b, -, hb⟩
    obtain ⟨U', hU', rfl⟩ := (f.fiberι s).isEmbedding.isInducing.isOpen_iff.mp hu
    obtain ⟨V', hV', rfl⟩ := (f.fiberι s).isEmbedding.isInducing.isOpen_iff.mp hv
    obtain ⟨x, hx, hxU, hxV⟩ := hirr U' V' hU' hV' ⟨_, hmem a, ha⟩ ⟨_, hmem b, hb⟩
    rw [← hrange] at hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨y, Set.mem_univ _, hxU, hxV⟩
  have : PreirreducibleSpace (f.fiber s) := ⟨hpre⟩
  by_cases hne : Nonempty (f.fiber s)
  · obtain ⟨z⟩ := hne
    obtain ⟨x, hx, hxO⟩ := hmeet ⟨_, hmem z⟩
    rw [← hrange] at hx
    obtain ⟨y, rfl⟩ := hx
    exact (hO.preimage (f.fiberι s).continuous).dense ⟨y, hxO⟩
  · rw [not_nonempty_iff] at hne
    exact fun x => isEmptyElim x

omit [IsNoetherianRing Λ] in
/-- Inverse image of a sheaf placed in degree `0` is the inverse image sheaf placed in degree
`0`. -/
theorem nonempty_inverseImage_singleFunctor_iso {X U : Scheme.{u}} (g : U ⟶ X)
    (F : EtaleModules.{u, 0} Λ X) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ g).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} Λ g).obj F)) :=
  ⟨DerivedCategory.Plus.ι.preimageIso
    (((etaleModuleInverseImage.{u, 0} Λ g).mapDerivedCategorySingleFunctor 0).app F)⟩

end Helpers

variable (B : BigEtaleSite.{u})

/-- **`Rf_! F` when `F` is finite type locally constant on a fibrewise dense, irreducible,
geometrically unibranch open.** Let `f : X ⟶ T` be separated of finite presentation with fibres
of dimension at most `1`, `T` Noetherian, `F` a constructible sheaf of `Λ`-modules on `X` over a
torsion Noetherian ring, and `o : O ⟶ X` an open immersion, dense in every fibre of `f`, with `O`
irreducible and geometrically unibranch and `F|_O` finite type locally constant. Then every
cohomology sheaf of `Rf_! F` is constructible: by the triangle of Stacks 0GKP for `O ⊆ X`, from
Stacks 0GK3 for the closed complement, which is quasi-finite over `T`, and Stacks 0GKY for `O`.
`h0GKV` is Stacks 0GKV. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_dense_isFiniteTypeLocallyConstant
    (T : B.Scheme) [IsNoetherian T.obj] (X : B.Scheme) (f : X.obj ⟶ T.obj) [IsSeparated f]
    (hf : FinitePresentation f) (hdim : ∀ s, topologicalKrullDim (f.fiber s) ≤ 1)
    (j : CompactificationOf (Over.mk f)) (O : B.Scheme) (o : O ⟶ X)
    (ho : IsOpenImmersion (B.inclusion.map o))
    (hd : ∀ s, Dense ((f.fiberι s) ⁻¹' Set.range (B.inclusion.map o).base))
    [IrreducibleSpace O.obj] (hO : IsGeometricallyUnibranch O.obj)
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (F : EtaleModules.{u, 0} Λ X.obj) (hF : IsBigSiteConstructibleEtaleModule B X Λ F)
    (hFO : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ O.obj.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map o)).obj F)) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B T Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  let o' : O.obj ⟶ X.obj := B.inclusion.map o
  have : IsOpenImmersion o' := ho
  have : LocallyOfFinitePresentation f := hf.1
  have : QuasiCompact f := hf.2.1
  have : QuasiSeparated f := hf.2.2
  have : LocallyOfFiniteType f := inferInstance
  have : IsLocallyNoetherian T.obj := IsNoetherian.toIsLocallyNoetherian
  have : IsLocallyNoetherian X.obj := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X.obj := ⟨⟩
  have : QuasiCompact o' := inferInstance
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X.obj) 0).obj F
  let i := closedComplementι o'
  obtain ⟨a, b, c, hT⟩ := exists_distTriang_derivedLowerShriek_openClosed_plus Λ j o' i
    (range_eq_compl_range_closedComplementι o') K
  have hQ := isWeakSerreClass_isBigSiteConstructibleEtaleModule B T Λ
  -- the closed part, through Stacks 0GK3
  have : IsClosedImmersion i := inferInstance
  have : IsFinite i := inferInstance
  have : IsProper i := inferInstance
  have : LocallyOfFiniteType i := IsProper.toLocallyOfFiniteType
  have : QuasiCompact i := inferInstance
  have hZB : B.Contains (closedComplement o') :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact i X.property
  let ZB : B.Scheme := B.obj (closedComplement o') hZB
  let iB : ZB ⟶ X := ObjectProperty.homMk i
  have : IsLocallyNoetherian (closedComplement o') := LocallyOfFiniteType.isLocallyNoetherian i
  have : CompactSpace ZB.obj := QuasiCompact.compactSpace_of_compactSpace i
  have : QuasiSeparatedSpace ZB.obj := inferInstanceAs (QuasiSeparatedSpace (closedComplement o'))
  have : LocallyQuasiFinite (i ≫ f) :=
    locallyQuasiFinite_comp_of_dense_fiber_of_isClosedImmersion f hdim
      o'.isOpenEmbedding.isOpen_range hd i (by
        rintro _ ⟨z, rfl⟩ hz
        have hr : Set.range o'.base = (Set.range i.base)ᶜ :=
          range_eq_compl_range_closedComplementι o'
        exact (hr ▸ hz : _) ⟨z, rfl⟩)
  have : IsSeparated (i ≫ f) := inferInstance
  have : QuasiCompact (i ≫ f) := inferInstance
  have : LocallyOfFiniteType (i ≫ f) := inferInstance
  have : LocallyOfFinitePresentation (i ≫ f) := inferInstance
  have h₃ : ∀ q : ℤ, IsBigSiteConstructibleEtaleModule B T Λ
      ((DerivedCategory.Plus.homologyFunctor _ q).obj (Triangle.mk a b c).obj₃) := fun q =>
    isConstructibleEtaleModule_homology_derivedLowerShriek_of_quasiFinite B (X := ZB) (Y := T)
      (i ≫ f) Λ _ _
      (fun q' => isConstructibleEtaleModule_homology_inverseImage_singleFunctor iB hF m hm hΛ q') q
  -- the open part, through Stacks 0GKY over a unibranch source
  have : LocallyQuasiFinite o' := inferInstance
  have hfO : FinitePresentation (o' ≫ f) :=
    ⟨inferInstance, inferInstance, MorphismProperty.comp_mem @QuasiSeparated _ _ inferInstance ‹_›⟩
  have hdimO := topologicalKrullDim_fiber_comp_le_of_locallyQuasiFinite o' f (d := 1) hdim
  have : IsSeparated (o' ≫ f) := inferInstance
  obtain ⟨e⟩ := nonempty_restriction_singleFunctor_iso o' F
  have h₁ : ∀ q : ℤ, IsBigSiteConstructibleEtaleModule B T Λ
      ((DerivedCategory.Plus.homologyFunctor _ q).obj (Triangle.mk a b c).obj₁) := fun q =>
    IsBigSiteConstructibleEtaleModule.of_iso B Λ ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((derivedLowerShriek.{u, 0} _ _ Λ).mapIso e.symm))
      (isConstructible_homology_derivedLowerShriek_of_isFiniteTypeLocallyConstant_of_geomUnibranch
        B T hO (o' ≫ f) hfO hdimO (j.restrictOpen o') Λ m hm hΛ h0GKV _ hFO q)
  exact prop_homology_obj₂_of_distTriang_plus (IsBigSiteConstructibleEtaleModule B T Λ) _ hT h₁ h₃ k


/-- **The normal step of Stacks 0GKY/0GKZ.** Let `T` be an integral normal Noetherian scheme of
`B`, `ι : X ⟶ 𝔸¹_T` an open immersion, `f : X ⟶ T` the structure morphism, `F` a constructible
sheaf of `Λ`-modules on `X` over a torsion Noetherian ring. Then `Rf_! F` has constructible
cohomology sheaves over a nonempty open `W ⊆ T`. `X` is irreducible and normal; `F` is finite
type locally constant on an open `O ∋` the generic point of `X`; take `W = f(O)`, over which `O`
is dense in every fibre, the fibres of `f` being open in those of `𝔸¹_T`, which are irreducible;
then base change (Stacks 0F7L) to `W` and
`isConstructibleEtaleModule_homology_derivedLowerShriek_of_dense_isFiniteTypeLocallyConstant`.
`h0GKV` is Stacks 0GKV. -/
theorem exists_isConstructibleEtaleModule_homology_derivedLowerShriek_affineLine_of_isNormal
    (T : B.Scheme) [IsNoetherian T.obj] [IsIntegral T.obj] [IsNormal T.obj] (X : B.Scheme)
    (ι : X.obj ⟶ AffineSpace (ULift.{u} (Fin 1)) T.obj) [IsOpenImmersion ι]
    (j : CompactificationOf (Over.mk (ι ≫ AffineSpace (ULift.{u} (Fin 1)) T.obj ↘ T.obj)))
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (F : EtaleModules.{u, 0} Λ X.obj) (hF : IsBigSiteConstructibleEtaleModule B X Λ F) :
    ∃ (W : B.Scheme) (w : W ⟶ T), IsOpenImmersion (B.inclusion.map w) ∧ Nonempty W.obj ∧
      ∀ k : ℤ, IsBigSiteConstructibleEtaleModule B W Λ
        ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map w)).obj
          ((DerivedCategory.Plus.homologyFunctor _ k).obj
            ((derivedLowerShriek.{u, 0} _ j Λ).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
  let A := AffineSpace (ULift.{u} (Fin 1)) T.obj
  let π : A ⟶ T.obj := A ↘ T.obj
  let f : X.obj ⟶ T.obj := ι ≫ π
  have : SmoothOfRelativeDimension 1 π :=
    Stacks.Chow.smoothOfRelativeDimension_affineSpaceOver T.obj 1
  have : Smooth π := smooth_affineSpace_over _ _
  have : IsAffineHom π := inferInstance
  have : IsSeparated π := inferInstance
  have : LocallyOfFinitePresentation π := inferInstance
  have : LocallyOfFiniteType π := inferInstance
  have : QuasiCompact π := inferInstance
  have : IsNoetherian A := isNoetherian_of_locallyOfFiniteType π
  have : QuasiCompact ι := inferInstance
  have : IsNoetherian X.obj := isNoetherian_of_locallyOfFiniteType (ι ≫ π)
  have : Smooth f := inferInstance
  have : IsSeparated f := inferInstance
  have hf : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  have hdimπ : ∀ s, topologicalKrullDim (π.fiber s) ≤ 1 := fun s => by
    rw [topologicalKrullDim_eq_iSup_localKrullDim]
    refine iSup_le fun z => ?_
    rw [← topologicalKrullDimAt_eq_localKrullDim,
      topologicalKrullDimAt_fiber_eq_of_smoothOfRelativeDimension π 1 s z]
    simp
  have hdim : ∀ s, topologicalKrullDim (f.fiber s) ≤ 1 :=
    topologicalKrullDim_fiber_comp_le_of_locallyQuasiFinite ι π (d := 1) hdimπ
  have hirrf : ∀ s, IsPreirreducible (f.base ⁻¹' {s}) := fun s => by
    have hπ : IsPreirreducible (π.base ⁻¹' {s}) := by
      rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
      exact (PreirreducibleSpace.isPreirreducible_univ).image _ (π.fiberι s).continuous.continuousOn
    exact hπ.preimage ι.isOpenEmbedding
  by_cases hX : Nonempty X.obj
  swap
  · rw [not_nonempty_iff] at hX
    have hz : IsZero F := isZero_etaleModulesUniv_of_isEmpty Λ X.obj F
    refine ⟨T, 𝟙 T, inferInstanceAs (IsOpenImmersion (𝟙 T.obj)), inferInstance, fun k => ?_⟩
    exact isConstructibleEtaleModule_of_isZero B Λ T (Functor.map_isZero _ (Functor.map_isZero _
      (Functor.map_isZero _ (Functor.map_isZero _ hz))))
  -- `X` is irreducible and normal; `F` is locally constant near its generic point
  have : IrreducibleSpace X.obj := ι.isOpenEmbedding.irreducibleSpace
  have : IsReduced X.obj := isReduced_of_isOpenImmersion ι
  have : IsNormal A := isNormal_of_smooth π
  have : IsNormal X.obj := isNormal_of_etale ι
  have hξ : genericPoint X.obj ∈ genericPoints X.obj := by
    rw [genericPoints_eq_singleton]; rfl
  obtain ⟨O, o, ho, ⟨z₀, -⟩, hFO⟩ :=
    exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule B X F hF hξ
  let o' : O.obj ⟶ X.obj := B.inclusion.map o
  have : IsOpenImmersion o' := ho
  have : Nonempty O.obj := ⟨z₀⟩
  have : IrreducibleSpace O.obj := o'.isOpenEmbedding.irreducibleSpace
  have : IsNormal O.obj := isNormal_of_etale o'
  -- the open image `W = f(O)` and the base change to it
  let W : T.obj.Opens :=
    ⟨f.base '' Set.range o'.base, f.isOpenMap _ o'.isOpenEmbedding.isOpen_range⟩
  have : QuasiCompact W.ι := inferInstance
  have hWB : B.Contains W.toScheme :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact W.ι T.property
  let WB : B.Scheme := B.obj W.toScheme hWB
  let wB : WB ⟶ T := ObjectProperty.homMk W.ι
  let P : X.obj.Opens := f ⁻¹ᵁ W
  let f' : P.toScheme ⟶ W.toScheme := f ∣_ W
  have sq : IsPullback P.ι f' f W.ι := (isPullback_morphismRestrict f W).flip
  have : QuasiCompact P.ι := inferInstance
  have hPB : B.Contains P.toScheme :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact P.ι X.property
  let PB : B.Scheme := B.obj P.toScheme hPB
  let pB : PB ⟶ X := ObjectProperty.homMk P.ι
  have : IsSeparated f' := MorphismProperty.of_isPullback sq ‹IsSeparated f›
  have hf' : FinitePresentation f' := FinitePresentation.of_isPullback sq hf
  have hdim' : ∀ s, topologicalKrullDim (f'.fiber s) ≤ 1 := fun s => by
    change f'.fiberDimension s ≤ 1
    rw [Scheme.Hom.fiberDimension_eq_of_isPullback sq]
    exact hdim _
  have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
  have : IsLocallyNoetherian W.toScheme := inferInstance
  have : IsNoetherian WB.obj := ⟨⟩
  -- `O ⊆ P`
  have hOP : Set.range o'.base ⊆ Set.range P.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ⟨_, ⟨y, rfl⟩, rfl⟩
  let κ : O.obj ⟶ P.toScheme := IsOpenImmersion.lift P.ι o' hOP
  have hκ : κ ≫ P.ι = o' := IsOpenImmersion.lift_fac P.ι o' hOP
  have : IsOpenImmersion (κ ≫ P.ι) := by rw [hκ]; infer_instance
  have : IsOpenImmersion κ := IsOpenImmersion.of_comp κ P.ι
  let κB : O ⟶ PB := ObjectProperty.homMk κ
  have hFP := isConstructibleEtaleModule_inverseImage B Λ pB hF
  have hFO' : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ O.obj.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ κ).obj ((etaleModuleInverseImage.{u, 0} Λ P.ι).obj F)) :=
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ
      (eqToIso (congrArg (fun g => (etaleModuleInverseImage.{u, 0} Λ g).obj F) hκ.symm) ≪≫
        (etaleModuleInverseImageCompIso.{u, 0} Λ κ P.ι).app F) hFO
  -- `O` is dense in the fibres of `f'`
  have hd : ∀ s, Dense ((f'.fiberι s) ⁻¹' Set.range κ.base) := fun s => by
    refine dense_fiberι_preimage_of_isPreirreducible f' s κ.isOpenEmbedding.isOpen_range ?_ ?_
    · have h := (hirrf s.1).preimage P.ι.isOpenEmbedding
      convert h using 1
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      have hc : (f'.base x).1 = f.base (P.ι.base x) := morphismRestrict_base_coe f W x
      exact ⟨fun h => by rw [← hc, h], fun h => Subtype.ext (hc.trans h)⟩
    · rintro -
      obtain ⟨_, ⟨y, rfl⟩, hy⟩ := s.2
      refine ⟨κ y, ?_, ⟨y, rfl⟩⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      apply Subtype.ext
      have h2 : P.ι.base (κ.base y) = o'.base y := by rw [← Scheme.Hom.comp_apply, hκ]
      have hc : (f'.base (κ.base y)).1 = f.base (P.ι.base (κ.base y)) :=
        morphismRestrict_base_coe f W _
      rw [hc, h2]
      exact hy
  have hKX :=
    isConstructibleEtaleModule_homology_derivedLowerShriek_of_dense_isFiniteTypeLocallyConstant
      B WB PB f' hf' hdim' (j.baseChange sq) O κB (inferInstanceAs (IsOpenImmersion κ)) hd
      isGeometricallyUnibranch_of_isNormal Λ m hm hΛ h0GKV _ hFP hFO'
  -- base change along `W ⊆ T` (Stacks 0F7L)
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X.obj) 0).obj F
  have hKt : isTorsionPlus.{u, 0} Λ X.obj K := fun _ =>
    isTorsionEtaleModule_of_natCast_eq_zero Λ m hm hΛ _
  have := isIso_derivedLowerShriekBaseChange_app Λ sq j K hKt
  let eBC := asIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq j).app K)
  obtain ⟨e₂⟩ := nonempty_inverseImage_singleFunctor_iso (Λ := Λ) P.ι F
  have hWne : Nonempty WB.obj := ⟨⟨f.base (o'.base z₀), o'.base z₀, ⟨z₀, rfl⟩, rfl⟩⟩
  refine ⟨WB, wB, inferInstanceAs (IsOpenImmersion W.ι), hWne, fun k => ?_⟩
  obtain ⟨e₁⟩ := nonempty_homology_etaleModuleDerivedInverseImagePlus_iso Λ W.ι
    ((derivedLowerShriek.{u, 0} f j Λ).obj K) k
  exact IsBigSiteConstructibleEtaleModule.of_iso B Λ
    (((DerivedCategory.Plus.homologyFunctor _ k).mapIso
      (eBC ≪≫ (derivedLowerShriek.{u, 0} f' (j.baseChange sq) Λ).mapIso e₂)).symm ≪≫ e₁)
    (hKX k)

/-- **Stacks 0GKY and 0GKZ over a Nagata base, from Stacks 0GKV.** Let `Y` be a Noetherian Nagata
scheme of `B`, `ι : X ⟶ 𝔸¹_Y` an open immersion (for `ι` an isomorphism this is `𝔸¹_Y` itself),
`f = ι ≫ (𝔸¹_Y ⟶ Y)`, `j` a compactification of `f`, `Λ` a Noetherian ring with `m = 0` in `Λ`
for some `m > 0`, and `F` a constructible sheaf of `Λ`-modules on `X` (for instance finite type
locally constant). Then every cohomology sheaf of `Rf_! F` is constructible.

By Noetherian induction through normalizations
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_of_forall_isIntegral_isNormal`) and base change
(Stacks 0F7L) one reduces to
`exists_isConstructibleEtaleModule_homology_derivedLowerShriek_affineLine_of_isNormal`.
`h0GKV` is Stacks 0GKV. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_affineLine_of_isNagataScheme
    (Y : B.Scheme) [IsNoetherian Y.obj] (hY : IsNagataScheme Y.obj) (X : B.Scheme)
    (ι : X.obj ⟶ AffineSpace (ULift.{u} (Fin 1)) Y.obj) [IsOpenImmersion ι]
    (j : CompactificationOf (Over.mk (ι ≫ AffineSpace (ULift.{u} (Fin 1)) Y.obj ↘ Y.obj)))
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (F : EtaleModules.{u, 0} Λ X.obj) (hF : IsBigSiteConstructibleEtaleModule B X Λ F) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} _ j Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  refine isConstructibleEtaleModule_of_forall_isIntegral_isNormal B Λ Y hY _
    (fun T w hw hwq _ _ => ?_)
  let w' : T.obj ⟶ Y.obj := B.inclusion.map w
  have : LocallyOfFiniteType w' := hw
  have : QuasiCompact w' := hwq
  have : IsNoetherian T.obj := isNoetherian_of_locallyOfFiniteType w'
  let AY := AffineSpace (ULift.{u} (Fin 1)) Y.obj
  let AT := AffineSpace (ULift.{u} (Fin 1)) T.obj
  let a : AT ⟶ AY := AffineSpace.map (ULift.{u} (Fin 1)) w'
  have hsqA : IsPullback a (AT ↘ T.obj) (AY ↘ Y.obj) w' := AffineSpace.isPullback_map w'
  have hsqι := IsPullback.of_hasPullback ι a
  have sq := hsqι.paste_vert hsqA
  have : LocallyOfFiniteType a := MorphismProperty.of_isPullback hsqA.flip ‹_›
  have : QuasiCompact a := MorphismProperty.of_isPullback hsqA.flip ‹_›
  have : LocallyOfFiniteType (pullback.fst ι a) := MorphismProperty.of_isPullback hsqι.flip ‹_›
  have : QuasiCompact (pullback.fst ι a) := MorphismProperty.of_isPullback hsqι.flip ‹_›
  have hXT : B.Contains (pullback ι a) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (pullback.fst ι a) X.property
  let XT : B.Scheme := B.obj (pullback ι a) hXT
  let gB : XT ⟶ X := ObjectProperty.homMk (pullback.fst ι a)
  have : IsOpenImmersion (pullback.snd ι a) := inferInstance
  have hFT := isConstructibleEtaleModule_inverseImage B Λ gB hF
  obtain ⟨W, o, ho, hW, hc⟩ :=
    exists_isConstructibleEtaleModule_homology_derivedLowerShriek_affineLine_of_isNormal B T XT
      (pullback.snd ι a) (j.baseChange sq) Λ m hm hΛ h0GKV _ hFT
  refine ⟨W, o, ho, hW, ?_⟩
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X.obj) 0).obj F
  have hKt : isTorsionPlus.{u, 0} Λ X.obj K := fun _ =>
    isTorsionEtaleModule_of_natCast_eq_zero Λ m hm hΛ _
  have := isIso_derivedLowerShriekBaseChange_app Λ sq j K hKt
  let eBC := asIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq j).app K)
  obtain ⟨e₁⟩ := nonempty_homology_etaleModuleDerivedInverseImagePlus_iso Λ w'
    ((derivedLowerShriek.{u, 0} _ j Λ).obj K) k
  obtain ⟨e₂⟩ := nonempty_inverseImage_singleFunctor_iso (Λ := Λ) (pullback.fst ι a) F
  exact IsBigSiteConstructibleEtaleModule.of_iso B Λ
    ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map o)).mapIso
        (((DerivedCategory.Plus.homologyFunctor _ k).mapIso
          (eBC ≪≫ (derivedLowerShriek.{u, 0} _ (j.baseChange sq) Λ).mapIso e₂)).symm ≪≫ e₁) ≪≫
      ((etaleModuleInverseImageCompIso.{u, 0} Λ (B.inclusion.map o) w').app _).symm) (hc k)

end Stacks.EtaleCohomology

end
