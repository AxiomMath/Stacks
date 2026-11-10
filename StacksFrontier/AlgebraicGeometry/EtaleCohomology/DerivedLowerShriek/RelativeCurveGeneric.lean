module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProperFiniteComposite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.OpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ThickeningInvariance
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.DenseOpenComplement
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeDimensionOne.CurveDiagram

/-!
# `Rf_! M` near a generic point of the base, for a family of curves

This is the generic step of the proof of Stacks 0GKX. Let `f : X ⟶ S` be separated and of finite
presentation with fibres of dimension at most `1`, `S` Noetherian, and `η` a generic point of an
irreducible component of `S`. For a finite module `M` over a torsion Noetherian ring there is an
open neighbourhood `U` of `η` over which every cohomology sheaf of `Rf_! M` is constructible.

The proof is the source's. Stacks 0GK7 gives, over a neighbourhood `U` of `η`, a finite surjective
universally injective `V ⟶ U`, an open `W ⊆ X_V` dense in the fibres, a finite surjective
`ν : ∐ Yᵢ ⟶ X_V` which is a thickening over `W`, and smooth proper families of curves
`q̄ᵢ : Ȳᵢ ⟶ Tᵢ` compactifying `Yᵢ`, with `Tᵢ ⟶ V` finite étale. Then:

* constructibility over `U` follows from constructibility over `V` (Stacks 095Q), and over `V` the
  complex is `R(X_V → V)_! M` by base change (Stacks 0F7L);
* the triangle of Stacks 0GKP for `W ⊆ X_V` and the quasi-finiteness of the complement `Z → V`
  (Stacks 0GK3) reduce to `R(W → V)_! M`;
* Stacks 0GKQ for the thickening `ν⁻¹(W) ⟶ W` replaces `W` by `ν⁻¹(W)`, an open of `∐ Ȳᵢ`;
* the triangle of Stacks 0GKP for `ν⁻¹(W) ⊆ ∐ Ȳᵢ` and the quasi-finiteness of its complement
  reduce to `R(∐ Ȳᵢ → V)_! M = R(∐ Tᵢ → V)_* R(∐ q̄ᵢ)_* M`, constructible by Stacks 0GKW and 0GK3
  (`isConstructible_homology_derivedLowerShriek_ofProper_comp_isFinite_of_hasConstantCohomology`).

The independence of `Rf_!` of the compactification (Stacks 0F7I) is used throughout to compare the
compactifications that the steps produce.

The constructibility of Stacks 0GKV enters as the hypothesis `h0GKV`.
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

/-- **Constructibility of `Rf_!` does not see the compactification, nor the spelling of `f`.** If
`f₁ = f₂`, then for torsion `K` the cohomology sheaves of `Rf₁_! K` and `Rf₂_! K`, computed through
any two compactifications, agree (Stacks 0F7I), so one is constructible when the other is. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_eq (B : BigEtaleSite.{u})
    {X : Scheme.{u}} {Y : B.Scheme} [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj]
    {f₁ f₂ : X ⟶ Y.obj} (h : f₁ = f₂) [IsSeparated f₁] [LocallyOfFiniteType f₁] [QuasiCompact f₁]
    (j₁ : CompactificationOf (Over.mk f₁)) (j₂ : CompactificationOf (Over.mk f₂))
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (hK : isTorsionPlus.{u, 0} Λ X K)
    (n : ℤ)
    (h₁ : IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ n).obj
      ((derivedLowerShriek.{u, 0} f₁ j₁ Λ).obj K))) :
    IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ n).obj
      ((derivedLowerShriek.{u, 0} f₂ j₂ Λ).obj K)) := by
  subst h
  exact IsBigSiteConstructibleEtaleModule.of_iso B Λ
    ((DerivedCategory.Plus.homologyFunctor _ n).mapIso
      ((derivedLowerShriekCompactificationIso f₁ j₁ j₂ Λ).app ⟨K, hK⟩)) h₁

/-- **The complement of the open part of the compactified curves is quasi-finite.** Let
`q̄ᵢ : Ȳᵢ ⟶ Tᵢ` be smooth with geometrically connected fibres of dimension at most `1`, let
`jᵢ : Yᵢ ⟶ Ȳᵢ` be open immersions with `qᵢ = jᵢ ≫ q̄ᵢ` surjective, and let `o : O ⟶ ∐ Ȳᵢ` be an
open immersion whose image contains `jᵢ(Dᵢ)` for subsets `Dᵢ ⊆ Yᵢ` dense in every fibre of `qᵢ`.
Then the closed complement of `O` is locally quasi-finite over `∐ Tᵢ`: over `Tₖ` it is the
complement in `Ȳₖ` of an open dense in every fibre of `q̄ₖ`. -/
theorem locallyQuasiFinite_closedComplementι_comp_sigmaMap {ι : Type} [Finite ι]
    {T Y Ybar : ι → Scheme.{u}} (q : ∀ i, Y i ⟶ T i) (qbar : ∀ i, Ybar i ⟶ T i)
    (j : ∀ i, Y i ⟶ Ybar i) (hjq : ∀ i, j i ≫ qbar i = q i) (hj : ∀ i, IsOpenImmersion (j i))
    (hq : ∀ i, Surjective (q i))
    (hqbar : ∀ i, Smooth (qbar i) ∧
      (∀ s, GeometricallyConnected ((qbar i).fiberToSpecResidueField s)) ∧
      ∀ s, topologicalKrullDim ((qbar i).fiber s) ≤ 1)
    {O : Scheme.{u}} (o : O ⟶ ∐ Ybar) [IsOpenImmersion o] (D : ∀ i, Set (Y i))
    (hD : ∀ i s, Dense (((q i).fiberι s) ⁻¹' D i))
    (hDo : ∀ i, ∀ y ∈ D i, Sigma.ι Ybar i (j i y) ∈ Set.range o) :
    LocallyQuasiFinite (closedComplementι o ≫ Limits.Sigma.map qbar) := by
  have hloc : IsZariskiLocalAtTarget @LocallyQuasiFinite.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyQuasiFinite)
  refine IsZariskiLocalAtTarget.of_openCover (P := @LocallyQuasiFinite) (sigmaOpenCover T)
    fun k₀ => ?_
  let k : ι := k₀
  change LocallyQuasiFinite (pullback.snd _ (Sigma.ι T k))
  let i' := closedComplementι o
  have hP := (IsPullback.of_hasPullback i' (Sigma.ι Ybar k)).paste_vert
    (isPullback_sigmaMap qbar k)
  rw [← MorphismProperty.cancel_left_of_respectsIso @LocallyQuasiFinite hP.isoPullback.hom,
    hP.isoPullback_hom_snd]
  have := hj k
  have := (hqbar k).1
  have : Surjective (j k ≫ qbar k) := by rw [hjq k]; exact hq k
  have hO : IsOpen ((Sigma.ι Ybar k) ⁻¹' Set.range o) :=
    o.isOpenEmbedding.isOpen_range.preimage (Sigma.ι Ybar k).continuous
  refine locallyQuasiFinite_comp_of_dense_fiber_of_isClosedImmersion (qbar k) (hqbar k).2.2 hO
    (fun s => ?_) (pullback.snd i' (Sigma.ι Ybar k)) ?_
  · refine (dense_fiber_image_of_isOpenImmersion (j k) (qbar k) (hqbar k).2.1 (D := D k)
      (fun s => by rw [hjq k]; exact hD k s) s).mono ?_
    rintro x ⟨y, hy, hyx⟩
    exact (hyx ▸ hDo k y hy : _)
  · rintro _ ⟨p, rfl⟩ hp
    have hc : i' (pullback.fst i' (Sigma.ι Ybar k) p) =
        Sigma.ι Ybar k (pullback.snd i' (Sigma.ι Ybar k) p) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    have hr : Set.range o.base = (Set.range i'.base)ᶜ := range_eq_compl_range_closedComplementι o
    have hp' : Sigma.ι Ybar k (pullback.snd i' (Sigma.ι Ybar k) p) ∈ Set.range o.base := hp
    rw [hr, ← hc] at hp'
    exact hp' ⟨_, rfl⟩

/-- **`Rg_! M` for an open `g : O ⟶ ∐ Ȳᵢ` of a coproduct of compactified curves.** Let
`q̄ᵢ : Ȳᵢ ⟶ Tᵢ` be proper and smooth with geometrically connected fibres of dimension at most
`1`, and `tᵢ : Tᵢ ⟶ V` finite étale, `V` Noetherian. Let `o : O ⟶ ∐ Ȳᵢ` be an open immersion
whose closed complement is locally quasi-finite over `∐ Tᵢ`. Then for `L` isomorphic to the
constant sheaf on a finite module `M` over a torsion Noetherian ring, in degree `0`, every
cohomology sheaf of `R(O → V)_! L` is constructible. By the triangle of Stacks 0GKP for
`O ⊆ ∐ Ȳᵢ`, this follows from Stacks 0GK3 for the complement and from Stacks 0GKW and 0GK3 for
`∐ Ȳᵢ ⟶ ∐ Tᵢ ⟶ V`. `h0GKV` is Stacks 0GKV. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_sigmaCurve_open
    (B : BigEtaleSite.{u}) (V : B.Scheme) [IsNoetherian V.obj] {ι : Type} [Finite ι]
    {T Ybar : ι → Scheme.{u}} (t : ∀ i, T i ⟶ V.obj) (qbar : ∀ i, Ybar i ⟶ T i)
    (ht : ∀ i, IsFinite (t i) ∧ Etale (t i))
    (hqbar : ∀ i, IsProper (qbar i) ∧ Smooth (qbar i) ∧
      (∀ s, GeometricallyConnected ((qbar i).fiberToSpecResidueField s)) ∧
      ∀ s, topologicalKrullDim ((qbar i).fiber s) ≤ 1)
    {O : Scheme.{u}} (o : O ⟶ ∐ Ybar) [IsOpenImmersion o]
    (hZ : LocallyQuasiFinite (closedComplementι o ≫ Limits.Sigma.map qbar))
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (M : ModuleCat.{u + 1} Λ) (hM : Module.Finite Λ M)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (jO : CompactificationOf (Over.mk (o ≫ Limits.Sigma.map qbar ≫ Sigma.desc t)))
    (L : DerivedCategory.Plus (EtaleModules.{u, 0} Λ O))
    (hL : Nonempty (L ≅ (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((constantSheaf O.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B V Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} (o ≫ Limits.Sigma.map qbar ≫ Sigma.desc t) jO Λ).obj L)) := by
  obtain ⟨hp, hs, hgc, hd⟩ := sigmaMap_curveFamily qbar hqbar
  let F₁ := Limits.Sigma.map qbar
  let F₂ := Sigma.desc t
  have : ∀ i, IsFinite (t i) := fun i => (ht i).1
  have : ∀ i, Etale (t i) := fun i => (ht i).2
  have hF₂f : IsFinite F₂ := isFinite_sigmaDesc
  have hloc : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  have hF₂e : Etale F₂ := IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun i => (ht i).2
  have : IsProper F₁ := hp
  have : UniversallyClosed F₁ := IsProper.toUniversallyClosed
  have : QuasiCompact F₁ := instQuasiCompactOfUniversallyClosed F₁
  have : LocallyOfFiniteType F₁ := IsProper.toLocallyOfFiniteType
  have : IsProper F₂ := inferInstance
  have : QuasiCompact F₂ := inferInstance
  have : LocallyOfFiniteType F₂ := IsProper.toLocallyOfFiniteType
  have : IsLocallyNoetherian V.obj := IsNoetherian.toIsLocallyNoetherian
  have hT : B.Contains (∐ T) := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact F₂ V.property
  have hY : B.Contains (∐ Ybar) := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact F₁ hT
  let TT : B.Scheme := B.obj (∐ T) hT
  let YY : B.Scheme := B.obj (∐ Ybar) hY
  let qB : YY ⟶ TT := ObjectProperty.homMk F₁
  let tB : TT ⟶ V := ObjectProperty.homMk F₂
  have : IsProper (B.inclusion.map qB) := hp
  have : IsFinite (B.inclusion.map tB) := hF₂f
  have : LocallyOfFinitePresentation (B.inclusion.map tB) :=
    inferInstanceAs (LocallyOfFinitePresentation F₂)
  have : IsLocallyNoetherian (∐ T : Scheme.{u}) := LocallyOfFiniteType.isLocallyNoetherian F₂
  have : CompactSpace (∐ T : Scheme.{u}) := QuasiCompact.compactSpace_of_compactSpace F₂
  have : AlgebraicGeometry.IsNoetherian TT.obj := ⟨⟩
  have : IsLocallyNoetherian (∐ Ybar : Scheme.{u}) := LocallyOfFiniteType.isLocallyNoetherian F₁
  have : CompactSpace (∐ Ybar : Scheme.{u}) := QuasiCompact.compactSpace_of_compactSpace F₁
  have : Smooth (B.inclusion.map qB) := hs
  have : GeometricallyConnected (B.inclusion.map qB) := hgc
  have hℓ : ∀ ℓ : ℕ, ℓ.Prime → ∀ q : ℕ, IsBigSiteConstructibleEtaleModule B TT (ZMod ℓ)
      (rightDerivedConstantUnit (B.inclusion.map qB) q (ZMod ℓ)) := fun ℓ hℓ q =>
    have : Fact ℓ.Prime := ⟨hℓ⟩
    h0GKV YY TT (B.inclusion.map qB) hd ℓ q
  have hmM : ∀ x : M, m • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]
  -- the open-closed triangle on `∐ Ȳᵢ`
  let cM := (constantSheaf (∐ Ybar).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ (∐ Ybar)) 0).obj cM
  let i := closedComplementι o
  have : QuasiCompact (F₁ ≫ F₂) := inferInstance
  obtain ⟨a, b, c, hT⟩ := exists_distTriang_derivedLowerShriek_openClosed_plus Λ
    (CompactificationOf.ofProper (F₁ ≫ F₂)) o i (range_eq_compl_range_closedComplementι o) K
  have hQ := isWeakSerreClass_isBigSiteConstructibleEtaleModule B V Λ
  -- the closed part, through Stacks 0GK3
  have hZB : B.Contains (closedComplement o) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact i hY
  let ZB : B.Scheme := B.obj (closedComplement o) hZB
  have : IsLocallyNoetherian (closedComplement o) := LocallyOfFiniteType.isLocallyNoetherian i
  have : CompactSpace ZB.obj := QuasiCompact.compactSpace_of_compactSpace i
  have : QuasiSeparatedSpace ZB.obj := inferInstanceAs (QuasiSeparatedSpace (closedComplement o))
  have : IsSeparated F₁ := IsProper.toIsSeparated
  have : IsSeparated (i ≫ F₁ ≫ F₂) := inferInstance
  have : LocallyQuasiFinite F₂ := inferInstance
  have : LocallyQuasiFinite (i ≫ F₁ ≫ F₂) := by
    rw [← Category.assoc]
    exact MorphismProperty.comp_mem @LocallyQuasiFinite _ _ hZ inferInstance
  have : QuasiCompact (i ≫ F₁ ≫ F₂) := inferInstance
  have : LocallyOfFiniteType (i ≫ F₁ ≫ F₂) := inferInstance
  have : LocallyOfFinitePresentation (i ≫ F₁ ≫ F₂) := inferInstance
  have h₃ : ∀ q : ℤ, IsBigSiteConstructibleEtaleModule B V Λ
      ((DerivedCategory.Plus.homologyFunctor _ q).obj (Triangle.mk a b c).obj₃) := fun q =>
    isConstructibleEtaleModule_homology_derivedLowerShriek_of_quasiFinite B (X := ZB) (Y := V)
      (i ≫ F₁ ≫ F₂) Λ _ _
      (fun q' => HasConstantCohomologyPlus.isConstructible_and_isTorsion B m hm hΛ (X := ZB) hM
        ((hasConstantCohomologyPlus_singleFunctor Λ M).inverseImage i) q') q
  -- the proper part, through Stacks 0GKW and 0GK3
  have h₂ : ∀ q : ℤ, IsBigSiteConstructibleEtaleModule B V Λ
      ((DerivedCategory.Plus.homologyFunctor _ q).obj (Triangle.mk a b c).obj₂) := fun q =>
    isConstructible_homology_derivedLowerShriek_ofProper_comp_isFinite_of_hasConstantCohomology
      B qB tB Λ hℓ m hm M hM hmM K (hasConstantCohomologyPlus_singleFunctor Λ M) q
  -- the open part, and the comparison of `L` with the restriction of `K`
  have h₁ :=
    prop_homology_obj₁_of_distTriang_plus (IsBigSiteConstructibleEtaleModule B V Λ) _ hT h₂ h₃ k
  obtain ⟨e₁⟩ := hL
  obtain ⟨e₂⟩ := nonempty_restriction_singleFunctor_constantSheaf_iso (Λ := Λ) (M := M) o
    ⟨Iso.refl K⟩
  have h₁' := IsBigSiteConstructibleEtaleModule.of_iso B Λ
    ((DerivedCategory.Plus.homologyFunctor _ k).mapIso
      ((derivedLowerShriek.{u, 0} _ _ Λ).mapIso (e₂ ≪≫ e₁.symm))) h₁
  -- move to the compactification `jO` (Stacks 0F7I)
  have : CompactSpace V.obj := inferInstance
  have : IsSeparated (o ≫ F₁ ≫ F₂) := inferInstance
  have : QuasiCompact (o ≫ F₁ ≫ F₂) := inferInstance
  have : LocallyOfFiniteType (o ≫ F₁ ≫ F₂) := inferInstance
  exact isConstructibleEtaleModule_homology_derivedLowerShriek_of_eq B rfl _ jO Λ L
    (fun q => isTorsionEtaleModule_of_natCast_eq_zero Λ m hm hΛ _) k h₁'

/-- **`R(X_V → V)_! M` from a curve diagram over `V`** (the core of the generic step of Stacks
0GKX). Let `p : X_V ⟶ V` be separated of finite presentation with fibres of dimension at most
`1`, `V` Noetherian, and suppose given the data of Stacks 0GK7 over `V`: an open `W ⊆ X_V` dense
in the fibres, `ν : ∐ Yᵢ ⟶ X_V` with `ν⁻¹(W) ⟶ W` a thickening, `ν⁻¹(W) ∩ Yᵢ` dense in the fibres
of `qᵢ : Yᵢ ⟶ Tᵢ`, open immersions `jᵢ : Yᵢ ⟶ Ȳᵢ` into proper smooth families of curves
`q̄ᵢ : Ȳᵢ ⟶ Tᵢ`, and finite étale `tᵢ : Tᵢ ⟶ V` with `ν ∘ p = t ∘ q` on `Yᵢ`. Then for `K`
isomorphic to the constant sheaf on a finite module over a torsion Noetherian ring, in degree
`0`, every cohomology sheaf of `Rp_! K` is constructible. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_curveDiagram
    (B : BigEtaleSite.{u}) (V : B.Scheme) [IsNoetherian V.obj] {XV : Scheme.{u}}
    (pV : XV ⟶ V.obj) [IsSeparated pV] (hpV : FinitePresentation pV)
    (hdim : ∀ s, topologicalKrullDim (pV.fiber s) ≤ 1) {n : ℕ}
    {T Y Ybar : Fin n → Scheme.{u}} (t : ∀ i, T i ⟶ V.obj) (q : ∀ i, Y i ⟶ T i)
    (qbar : ∀ i, Ybar i ⟶ T i) (j : ∀ i, Y i ⟶ Ybar i) (ν : (∐ Y) ⟶ XV) (W : XV.Opens)
    (hjq : ∀ i, j i ≫ qbar i = q i) (hν : ∀ i, Sigma.ι Y i ≫ ν ≫ pV = q i ≫ t i)
    (hWd : ∀ s : V.obj, Dense ((pV.fiberι s) ⁻¹' (W : Set XV)))
    (hWY : ∀ i (s : T i), Dense (((q i).fiberι s) ⁻¹' ((Sigma.ι Y i ≫ ν) ⁻¹' (W : Set XV))))
    (hth : Stacks.Thickenings.IsThickening (ν ∣_ W)) (hj : ∀ i, IsOpenImmersion (j i))
    (ht : ∀ i, IsFinite (t i) ∧ Etale (t i)) (hq : ∀ i, Surjective (q i) ∧ Smooth (q i))
    (hqbar : ∀ i, IsProper (qbar i) ∧ Smooth (qbar i) ∧
      (∀ s, GeometricallyConnected ((qbar i).fiberToSpecResidueField s)) ∧
      ∀ s, topologicalKrullDim ((qbar i).fiber s) ≤ 1)
    (jc : CompactificationOf (Over.mk pV))
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (M : ModuleCat.{u + 1} Λ) (hM : Module.Finite Λ M)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ XV))
    (hK : Nonempty (K ≅ (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((constantSheaf XV.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B V Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} pV jc Λ).obj K)) := by
  have : IsLocallyNoetherian V.obj := IsNoetherian.toIsLocallyNoetherian
  have : LocallyOfFinitePresentation pV := hpV.1
  have : QuasiCompact pV := hpV.2.1
  have : LocallyOfFiniteType pV := inferInstance
  have : IsLocallyNoetherian XV := LocallyOfFiniteType.isLocallyNoetherian pV
  have : CompactSpace XV := QuasiCompact.compactSpace_of_compactSpace pV
  have hXV : B.Contains XV := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact pV V.property
  have hQ := isWeakSerreClass_isBigSiteConstructibleEtaleModule B V Λ
  -- the open-closed triangle for `W ⊆ X_V`
  let iZ := closedComplementι W.ι
  obtain ⟨a, b, c, hT⟩ := exists_distTriang_derivedLowerShriek_openClosed_plus Λ jc W.ι iZ
    (range_eq_compl_range_closedComplementι W.ι) K
  refine prop_homology_obj₂_of_distTriang_plus (IsBigSiteConstructibleEtaleModule B V Λ) _ hT
    (fun k' => ?_) (fun k' => ?_) k
  · -- the open part `W`: Stacks 0GKQ for the thickening `ν⁻¹(W) ⟶ W`, then `∐ Ȳᵢ`
    let th := ν ∣_ W
    have : IsClosedImmersion th := hth.1
    have : Surjective th := ⟨hth.2⟩
    have : QuasiCompact (W.ι ≫ pV) := inferInstance
    let KW := (etaleModuleRestriction.{u, 0} Λ W.ι).mapDerivedCategoryPlus.obj K
    have hKW := nonempty_restriction_singleFunctor_constantSheaf_iso W.ι hK
    let e :=
      (derivedLowerShriekInverseImageIsoOfThickening.{u, 0} Λ (jc.restrictOpen W.ι) th).app KW
    refine IsBigSiteConstructibleEtaleModule.of_iso B Λ
      ((DerivedCategory.Plus.homologyFunctor _ k').mapIso e) ?_
    -- the open `ν⁻¹(W)` of `∐ Ȳᵢ`
    let o : (ν ⁻¹ᵁ W : Scheme.{u}) ⟶ ∐ Ybar := (ν ⁻¹ᵁ W).ι ≫ Limits.Sigma.map j
    have : IsOpenImmersion (Limits.Sigma.map j) :=
      IsZariskiLocalAtTarget.sigmaMap (P := @IsOpenImmersion) j hj
    have : IsOpenImmersion o := inferInstance
    have hF : Limits.Sigma.map j ≫ Limits.Sigma.map qbar ≫ Sigma.desc t = ν ≫ pV := by
      refine Sigma.hom_ext _ _ fun i => ?_
      rw [Sigma.ι_map_assoc, Sigma.ι_map_assoc, Sigma.ι_comp_desc, reassoc_of% (hjq i), hν i]
    have heq : o ≫ Limits.Sigma.map qbar ≫ Sigma.desc t = th ≫ W.ι ≫ pV := by
      rw [Category.assoc, hF, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    have hZ' : LocallyQuasiFinite (closedComplementι o ≫ Limits.Sigma.map qbar) :=
      locallyQuasiFinite_closedComplementι_comp_sigmaMap q qbar j hjq hj (fun i => (hq i).1)
        (fun i => ⟨(hqbar i).2.1, (hqbar i).2.2⟩) o
        (fun i => (Sigma.ι Y i ≫ ν) ⁻¹' (W : Set XV)) hWY (fun i y hy => by
          refine ⟨⟨Sigma.ι Y i y, ?_⟩, ?_⟩
          · change ν (Sigma.ι Y i y) ∈ W
            rw [← Scheme.Hom.comp_apply]
            exact hy
          · change Limits.Sigma.map j (Sigma.ι Y i y) = Sigma.ι Ybar i (j i y)
            rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Sigma.ι_map])
    obtain ⟨hp, -, -, -⟩ := sigmaMap_curveFamily qbar hqbar
    have : ∀ i, IsFinite (t i) := fun i => (ht i).1
    have : IsProper (Limits.Sigma.map qbar) := hp
    have : IsFinite (Sigma.desc t) := isFinite_sigmaDesc
    have : IsProper (Sigma.desc t) := inferInstance
    have : IsSeparated (Limits.Sigma.map qbar) := IsProper.toIsSeparated
    have : UniversallyClosed (Limits.Sigma.map qbar) := IsProper.toUniversallyClosed
    have : QuasiCompact (Limits.Sigma.map qbar) :=
      instQuasiCompactOfUniversallyClosed (Limits.Sigma.map qbar)
    have : LocallyOfFiniteType (Limits.Sigma.map qbar) := IsProper.toLocallyOfFiniteType
    have : LocallyOfFiniteType (Sigma.desc t) := IsProper.toLocallyOfFiniteType
    have : IsLocallyNoetherian (∐ Ybar : Scheme.{u}) := LocallyOfFiniteType.isLocallyNoetherian
      (Limits.Sigma.map qbar ≫ Sigma.desc t)
    have : IsSeparated (o ≫ Limits.Sigma.map qbar ≫ Sigma.desc t) := inferInstance
    have : QuasiCompact (o ≫ Limits.Sigma.map qbar ≫ Sigma.desc t) := by
      rw [heq]
      exact MorphismProperty.comp_mem @QuasiCompact _ _ inferInstance ‹QuasiCompact (W.ι ≫ pV)›
    have : LocallyOfFiniteType (o ≫ Limits.Sigma.map qbar ≫ Sigma.desc t) := inferInstance
    have : IsProper (Limits.Sigma.map qbar ≫ Sigma.desc t) := inferInstance
    exact isConstructibleEtaleModule_homology_derivedLowerShriek_of_eq B heq
      ((CompactificationOf.ofProper (Limits.Sigma.map qbar ≫ Sigma.desc t)).restrictOpen o) _ Λ _
      (fun q' => isTorsionEtaleModule_of_natCast_eq_zero Λ m hm hΛ _) k'
      (isConstructibleEtaleModule_homology_derivedLowerShriek_sigmaCurve_open B V t qbar ht hqbar
        o hZ' Λ m hm hΛ M hM h0GKV _ _
        (nonempty_inverseImage_singleFunctor_constantSheaf_iso th hKW) k')
  · -- the closed part `Z`: quasi-finite over `V` (Stacks 0GK3)
    have hZB : B.Contains (closedComplement W.ι) :=
      Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact iZ hXV
    let ZB : B.Scheme := B.obj (closedComplement W.ι) hZB
    have : IsLocallyNoetherian (closedComplement W.ι) := LocallyOfFiniteType.isLocallyNoetherian iZ
    have : CompactSpace ZB.obj := QuasiCompact.compactSpace_of_compactSpace iZ
    have : QuasiSeparatedSpace ZB.obj :=
      inferInstanceAs (QuasiSeparatedSpace (closedComplement W.ι))
    have : LocallyQuasiFinite (iZ ≫ pV) :=
      locallyQuasiFinite_comp_of_dense_fiber_of_isClosedImmersion pV hdim W.isOpen hWd iZ (by
        rintro _ ⟨z, rfl⟩ hz
        have hr : Set.range W.ι.base = (Set.range iZ.base)ᶜ :=
          range_eq_compl_range_closedComplementι W.ι
        have hz' : iZ z ∈ Set.range W.ι.base := by rw [Scheme.Opens.range_ι]; exact hz
        rw [hr] at hz'
        exact hz' ⟨z, rfl⟩)
    have : IsSeparated (iZ ≫ pV) := inferInstance
    have : QuasiCompact (iZ ≫ pV) := inferInstance
    have : LocallyOfFiniteType (iZ ≫ pV) := inferInstance
    have : LocallyOfFinitePresentation (iZ ≫ pV) := inferInstance
    exact isConstructibleEtaleModule_homology_derivedLowerShriek_of_quasiFinite B (X := ZB) (Y := V)
      (iZ ≫ pV) Λ _ _
      (fun q' => HasConstantCohomologyPlus.isConstructible_and_isTorsion B m hm hΛ (X := ZB) hM
        ((hasConstantCohomologyPlus_of_iso_singleFunctor hK).inverseImage iZ) q') k'

/-- A base change of a separated finitely presented morphism with fibres of dimension at most `1`
is again of this kind. -/
private theorem base_change_separated_finitePresentation_fiber_dim_le {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)
    [IsSeparated f] (hf : FinitePresentation f) (hdim : ∀ s, topologicalKrullDim (f.fiber s) ≤ 1) :
    IsSeparated f' ∧ FinitePresentation f' ∧ ∀ s, topologicalKrullDim (f'.fiber s) ≤ 1 := by
  have : LocallyOfFiniteType f := by have := hf.1; infer_instance
  refine ⟨MorphismProperty.of_isPullback sq ‹_›, FinitePresentation.of_isPullback sq hf,
    fun s => ?_⟩
  change f'.fiberDimension s ≤ 1
  rw [Scheme.Hom.fiberDimension_eq_of_isPullback sq]
  exact hdim _

/-- **Stacks 0F7L on cohomology sheaves.** For a cartesian square and `K` killed by `m`, the
pullback of `Hᵏ(Rf_! K)` is `Hᵏ` of `Rf'_!` of the pullback of `K`. -/
private theorem nonempty_iso_homology_derivedLowerShriek_baseChange {Λ : Type} [CommRing Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g) (j : CompactificationOf (Over.mk f))
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (k : ℤ) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor _ k).obj
        ((derivedLowerShriek.{u, 0} f' (j.baseChange sq) Λ).obj
          ((etaleModuleInverseImage.{u, 0} Λ g').mapDerivedCategoryPlus.obj K)) ≅
      (etaleModuleInverseImage.{u, 0} Λ g).obj ((DerivedCategory.Plus.homologyFunctor _ k).obj
        ((derivedLowerShriek.{u, 0} f j Λ).obj K))) := by
  have := isIso_derivedLowerShriekBaseChange_app Λ sq j K fun _ =>
    isTorsionEtaleModule_of_natCast_eq_zero Λ m hm hΛ _
  obtain ⟨e⟩ := nonempty_homology_etaleModuleDerivedInverseImagePlus_iso Λ g
    ((derivedLowerShriek.{u, 0} f j Λ).obj K) k
  exact ⟨(DerivedCategory.Plus.homologyFunctor _ k).mapIso
    (asIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq j).app K)).symm ≪≫ e⟩

/-- **The generic step of Stacks 0GKX.** Let `S` be a Noetherian scheme of `B`, `f : X ⟶ S`
separated and of finite presentation with fibres of dimension at most `1`, `j` a compactification
of `f`, and `K` isomorphic to the constant sheaf on a finite module `M` over a torsion Noetherian
ring, in degree `0`. For every generic point `η` of an irreducible component of `S` there is an
open neighbourhood `u : U ⟶ S` of `η` over which every cohomology sheaf of `Rf_! K` is
constructible, using the base change isomorphism of Stacks 0F7L. `h0GKV` is Stacks 0GKV. -/
theorem exists_isConstructibleEtaleModule_homology_derivedLowerShriek_near_genericPoint
    (B : BigEtaleSite.{u}) (S : B.Scheme) [IsNoetherian S.obj] {X : Scheme.{u}}
    (f : X ⟶ S.obj) [IsSeparated f] (hf : FinitePresentation f)
    (hdim : ∀ s, topologicalKrullDim (f.fiber s) ≤ 1) (j : CompactificationOf (Over.mk f))
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (M : ModuleCat.{u + 1} Λ) (hM : Module.Finite Λ M)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hK : Nonempty (K ≅ (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))
    (η : S.obj) (hη : η ∈ genericPoints S.obj) :
    ∃ (U : B.Scheme) (u : U ⟶ S), IsOpenImmersion (B.inclusion.map u) ∧
      η ∈ Set.range (B.inclusion.map u).base ∧ ∀ k : ℤ,
        IsBigSiteConstructibleEtaleModule B U Λ
          ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map u)).obj
            ((DerivedCategory.Plus.homologyFunctor _ k).obj
              ((derivedLowerShriek.{u, 0} f j Λ).obj K))) := by
  obtain ⟨U, hηU, V, v, hvf, hvs, hvi, XV, a, pV, hsq, n, T, Y, Ybar, t, q, qbar, jY, ν, W, hjq,
    hν, -, -, hWd, hWY, hth, hj, ht, hq, hqbar⟩ :=
    exists_curveDiagram_near_genericPoint f hf η hη (hdim η)
  have : IsLocallyNoetherian S.obj := IsNoetherian.toIsLocallyNoetherian
  have : QuasiCompact U.ι := inferInstance
  have hU : B.Contains U.toScheme :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact U.ι S.property
  let UB : B.Scheme := B.obj U.toScheme hU
  let uB : UB ⟶ S := ObjectProperty.homMk U.ι
  have : IsFinite v := hvf
  have : IsProper v := inferInstance
  have : LocallyOfFiniteType v := IsProper.toLocallyOfFiniteType
  have : QuasiCompact v := inferInstance
  have hV : B.Contains V := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact v hU
  let VB : B.Scheme := B.obj V hV
  let vB : VB ⟶ UB := ObjectProperty.homMk v
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian v
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace v
  have : IsNoetherian VB.obj := ⟨⟩
  have : CompactSpace UB.obj := inferInstanceAs (CompactSpace U.toScheme)
  have : QuasiSeparatedSpace UB.obj := inferInstanceAs (QuasiSeparatedSpace U.toScheme)
  have : CompactSpace VB.obj := inferInstanceAs (CompactSpace V)
  have : QuasiSeparatedSpace VB.obj := inferInstanceAs (QuasiSeparatedSpace V)
  -- the base change `p : X_V ⟶ V`
  obtain ⟨_, hpV, hdimV⟩ := base_change_separated_finitePresentation_fiber_dim_le hsq hf hdim
  let KV := (etaleModuleInverseImage.{u, 0} Λ a).mapDerivedCategoryPlus.obj K
  have hcore := isConstructibleEtaleModule_homology_derivedLowerShriek_of_curveDiagram B VB pV
    hpV hdimV t q qbar jY ν W hjq hν hWd hWY hth hj ht hq hqbar (j.baseChange hsq) Λ m hm hΛ M hM
    h0GKV KV (nonempty_inverseImage_singleFunctor_constantSheaf_iso a hK)
  -- base change (Stacks 0F7L) and descent along `V ⟶ U` (Stacks 095Q)
  refine ⟨UB, uB, inferInstanceAs (IsOpenImmersion U.ι), ⟨⟨η, hηU⟩, rfl⟩, fun k => ?_⟩
  refine isConstructibleEtaleModule_of_inverseImage B Λ vB hvs.surj ?_
  obtain ⟨e⟩ := nonempty_iso_homology_derivedLowerShriek_baseChange hsq j K m hm hΛ k
  exact IsBigSiteConstructibleEtaleModule.of_iso B Λ
    (e ≪≫ (etaleModuleInverseImageCompIso.{u, 0} Λ v U.ι).app _) (hcore k)

/-- **Stacks 0GKX, from Stacks 0GKV.** Let `S` be a Noetherian scheme of `B` and
`f : X ⟶ S` separated and of finite presentation with fibres of dimension at most `1` (for
instance separated, affine and smooth of relative dimension `1`), let `j` be a compactification of
`f`, `Λ` a Noetherian ring with `m = 0` in `Λ` for some `m > 0`, and `M` a finite `Λ`-module.
Then every cohomology sheaf of `Rf_! M` is constructible.

The source's induction on `dim S` is a Noetherian induction here
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_of_forall_isClosedImmersion`): for a nonempty
reduced closed subscheme `Z ⟶ S`, base change (Stacks 0F7L) identifies the restriction of
`Rf_! M` to `Z` with `R(X_Z → Z)_! M`, which is constructible near a generic point of `Z` by
`exists_isConstructibleEtaleModule_homology_derivedLowerShriek_near_genericPoint`.
`h0GKV` is Stacks 0GKV. -/
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_of_fiberDimension_le_one
    (B : BigEtaleSite.{u}) (S : B.Scheme) [IsNoetherian S.obj] {X : Scheme.{u}}
    (f : X ⟶ S.obj) [IsSeparated f] (hf : FinitePresentation f)
    (hdim : ∀ s, topologicalKrullDim (f.fiber s) ≤ 1) (j : CompactificationOf (Over.mk f))
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (M : ModuleCat.{u + 1} Λ) (hM : Module.Finite Λ M)
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hK : Nonempty (K ≅ (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B S Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj K)) := by
  refine isConstructibleEtaleModule_of_forall_isClosedImmersion B Λ S _
    (fun Z i hi _ hne => ?_)
  let i' : Z.obj ⟶ S.obj := B.inclusion.map i
  have : IsLocallyNoetherian S.obj := IsNoetherian.toIsLocallyNoetherian
  have : IsClosedImmersion i' := hi
  have : IsFinite i' := inferInstance
  have : IsProper i' := inferInstance
  have : LocallyOfFiniteType i' := IsProper.toLocallyOfFiniteType
  have : QuasiCompact i' := inferInstance
  have : IsLocallyNoetherian Z.obj := LocallyOfFiniteType.isLocallyNoetherian i'
  have : CompactSpace Z.obj := QuasiCompact.compactSpace_of_compactSpace i'
  have : IsNoetherian Z.obj := ⟨⟩
  -- a generic point of `Z`
  obtain ⟨z⟩ := hne
  let η : Z.obj := (genericPoints.ofComponent
    ⟨_, irreducibleComponent_mem_irreducibleComponents z⟩ : genericPoints Z.obj)
  have hη : η ∈ genericPoints Z.obj := Subtype.prop _
  -- the base change of `f` to `Z`
  have sq := IsPullback.of_hasPullback f i'
  let fZ := pullback.snd f i'
  obtain ⟨_, hfZ, hdimZ⟩ := base_change_separated_finitePresentation_fiber_dim_le sq hf hdim
  let KZ := (etaleModuleInverseImage.{u, 0} Λ (pullback.fst f i')).mapDerivedCategoryPlus.obj K
  obtain ⟨U, u', hu, ⟨x, -⟩, hc⟩ :=
    exists_isConstructibleEtaleModule_homology_derivedLowerShriek_near_genericPoint B Z fZ hfZ
      hdimZ (j.baseChange sq) Λ m hm hΛ M hM h0GKV KZ
      (nonempty_inverseImage_singleFunctor_constantSheaf_iso _ hK) η hη
  obtain ⟨e⟩ := nonempty_iso_homology_derivedLowerShriek_baseChange sq j K m hm hΛ k
  refine ⟨U, u', hu, ⟨x⟩, IsBigSiteConstructibleEtaleModule.of_iso B Λ
    ((etaleModuleInverseImageCompIso.{u, 0} Λ (B.inclusion.map u') i').app _ ≪≫
      (etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map u')).mapIso e.symm).symm (hc k)⟩

end Stacks.EtaleCohomology

end
