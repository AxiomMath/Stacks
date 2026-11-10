module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.SchemeBaseSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupExtensionFromOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceSquareGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquarePushout
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChowDiagram
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# Dominating a proper modification across an elementary distinguished square

Say that an algebraic space `Y` *dominates modifications* when every proper morphism `f : X ⟶ Y`
which is an isomorphism over a quasi-compact open subspace `U ⊆ Y` is dominated by a `U`-admissible
blowup of `Y`: there are a `U`-admissible blowup `b : Y' ⟶ Y` and `g : Y' ⟶ X` with `f ∘ g = b`.
This is the conclusion of Stacks 087G.

This file proves that the property crosses an elementary distinguished square `(U ⊆ W, φ : V ⟶ W)`
with `V` affine and `W` quasi-compact and quasi-separated: if `U` dominates modifications, so does
`W`. Together with the case of an affine scheme and the induction principle of Stacks 08GP this
proves Stacks 087G.

## The argument

Let `f : X ⟶ W` be proper and an isomorphism over a quasi-compact open `U₀ ⊆ W`.

* Over `U` the base change `X_U ⟶ U` is dominated by a `U₀ ∩ U`-admissible blowup `U' ⟶ U`; by
  Stacks 086D it is the restriction of a `U₀`-admissible blowup `b₁ : W₁ ⟶ W`.
* `V₁ = V ×_W W₁` is a quasi-compact quasi-separated scheme (Stacks 085R on the affine chart `V`).
  Over the inverse image `O ⊆ V₁` of `U₀ ∪ U` the morphism `X ×_W V₁ ⟶ V₁` has a section: over `U₀`
  the inverse of `f`, over `U` the domination of `X_U` by `U'`; the two agree on the overlap
  because `f` is an isomorphism over `U₀`. A scheme dominates sections
  (`AlgebraicGeometry.Space.DominatesSections`, the proof of Stacks 0CPI), so there is an
  `O`-admissible blowup `b₂ : V₂ ⟶ V₁` with a morphism `V₂ ⟶ X` extending that section.
* The centre `Z₂` of `b₂` avoids `O`, so it lies over the complement of `U` where `V₁ ⟶ W₁` is an
  isomorphism; glued with the empty closed subspace of `b₁⁻¹(U)` it is the restriction of a
  finitely presented closed subspace `Z ⊆ W₁` avoiding `b₁⁻¹(U₀)`
  (`AlgebraicGeometry.Space.squareGlue`). The blowup `c : Y' ⟶ W₁` in `Z` makes `c ≫ b₁` a
  `U₀`-admissible blowup (Stacks 086C).
* `Y'` is the pushout of its parts over `b₁⁻¹(U)` and over `V₁` (Stacks 0DVI): over the first it
  maps to `X` through `U'`, over the second through `V₂ ≅ Y' ×_{W₁} V₁` (Stacks 085S), and the two
  agree on the overlap by the extension property of `V₂ ⟶ X`.

## Main definitions

* `AlgebraicGeometry.Space.DominatesModifications`: every proper morphism to the space which is an
  isomorphism over a quasi-compact open subspace `U` is dominated by a `U`-admissible blowup.

## Main results

* `AlgebraicGeometry.Space.DominatesSections.dominatesModifications`: a space which dominates
  sections dominates modifications.
* `AlgebraicGeometry.Space.dominatesSections_pullback_of_isAffineSpace`: the base change of an
  admissible blowup along an affine étale morphism dominates sections.
* `AlgebraicGeometry.Space.dominatesModifications_of_isElementaryDistinguishedSquare`: dominating
  modifications crosses an elementary distinguished square `(U ⊆ W, φ : V ⟶ W)` with `V` affine,
  `U` quasi-compact and `W` quasi-compact and quasi-separated.

## References

* [Stacks Project, Tag 087G](https://stacks.math.columbia.edu/tag/087G)
* [Stacks Project, Tag 0CPI](https://stacks.math.columbia.edu/tag/0CPI)
* [Stacks Project, Tag 086D](https://stacks.math.columbia.edu/tag/086D)
* [Stacks Project, Tag 086C](https://stacks.math.columbia.edu/tag/086C)
* [Stacks Project, Tag 0DVI](https://stacks.math.columbia.edu/tag/0DVI)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An algebraic space `Y` **dominates modifications** when every proper morphism `f : X ⟶ Y` which
is an isomorphism over a quasi-compact open subspace `U ⊆ Y` is dominated by a `U`-admissible
blowup: there are a `U`-admissible blowup `b : Y' ⟶ Y` and a morphism `g : Y' ⟶ X` with
`g ≫ f = b`. -/
def DominatesModifications (Y : AlgebraicSpaces B S hS) : Prop :=
  ∀ (U : OpenSubspaces B S hS Y.1), IsQuasiCompactSpace B S hS U.1.toFunctor →
    ∀ (X : AlgebraicSpaces B S hS) (f : X ⟶ Y), IsProper B S hS f.hom →
      IsIso (pullback.snd f.hom U.1.ι) →
        ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y), IsAdmissibleBlowup B S hS U b ∧
          ∃ g : Y' ⟶ X, g ≫ f = b

/-- A space which dominates sections dominates modifications: a morphism which is an isomorphism
over `U` has the section `f⁻¹` there. -/
theorem DominatesSections.dominatesModifications {Y : AlgebraicSpaces B S hS}
    (h : DominatesSections Y) : DominatesModifications Y := by
  intro U hUqc X f hf hiso
  obtain ⟨Y', b, hb, g, hg, -⟩ := h U hUqc X f hf
    (inv (pullback.snd f.hom U.1.ι) ≫ pullback.fst f.hom U.1.ι)
    (by rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc])
  exact ⟨Y', b, hb, g, hg⟩

/-- In a cartesian square over `j ≫ i`, the projection to the source of `j` is an isomorphism when
the base change of `f` along `i` is an isomorphism. -/
theorem isIso_snd_of_isPullback_comp {C : Type*} [Category C] [HasPullbacks C] {X W U A P : C}
    (f : X ⟶ W) (i : U ⟶ W) (j : A ⟶ U) [IsIso (pullback.snd f i)] {fst : P ⟶ X} {snd : P ⟶ A}
    (h : IsPullback fst snd f (j ≫ i)) : IsIso snd :=
  (IsPullback.of_right' h (IsPullback.of_hasPullback f i)).isIso_snd_of_isIso

/-- The projection to the source of the base change of a proper morphism `b` along `φ` is proper. -/
private theorem isProper_fst_pullback_of_isProper {W W₁ : AlgebraicSpaces B S hS}
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V) (φ : V ⟶ W.1)
    {b : W₁ ⟶ W} (hb : IsProper B S hS b.hom) : IsProper B S hS (pullback.fst φ b.hom) :=
  isProper_of_isPullback B S hS (isAlgebraicSpace_pullback B S hS φ b.hom hV W₁.2 W.2) W₁.2 hV W.2
    (IsPullback.of_hasPullback φ b.hom).flip hb

/-- **The base change of an admissible blowup along an affine étale morphism dominates sections**:
it is a quasi-compact quasi-separated scheme. -/
theorem dominatesSections_pullback_of_isAffineSpace {W W₁ : AlgebraicSpaces B S hS}
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (hVaff : IsAffineSpace B S hS V) (φ : V ⟶ W.1) (hφ : IsEtale B S hS φ)
    {U₀ : OpenSubspaces B S hS W.1} {b₁ : W₁ ⟶ W} (hb₁ : IsAdmissibleBlowup B S hS U₀ b₁) :
    DominatesSections (⟨pullback φ b₁.hom, isAlgebraicSpace_pullback B S hS φ b₁.hom hV W₁.2 W.2⟩ :
      AlgebraicSpaces B S hS) := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    AlgebraicGeometry.hasSheafify_bigFppfOver B S hS
  have hZ := B.contains_terminal
  have hb₁p : IsProper B S hS b₁.hom := IsAdmissibleBlowup.isProper B S hS hb₁
  obtain ⟨T, hTaff, ⟨eV⟩⟩ := hVaff
  obtain ⟨Z₁, hZ₁fp, -, hZ₁bl⟩ := hb₁
  have hV₁ : IsAlgebraicSpace B S hS (pullback φ b₁.hom) :=
    isAlgebraicSpace_pullback B S hS φ b₁.hom hV W₁.2 W.2
  let a : schemeSpace T ⟶ W := ObjectProperty.homMk (eV.inv ≫ φ)
  have ha : IsEtale B S hS a.hom := isEtale_comp B S hS (isEtale_of_iso B S hS eV.symm) hφ
  have hsqp : IsPullback (pullback.fst φ b₁.hom ≫ eV.hom) (pullback.snd φ b₁.hom)
      (eV.inv ≫ φ) b₁.hom :=
    (IsPullback.of_hasPullback φ b₁.hom).of_iso (Iso.refl _) eV (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  have hsq := isPullback_homMk B S hS (isAlgebraicSpace_yoneda B S hS T) W₁.2 W.2 hV₁ hsqp
  have hpfp : IsFinitePresentation B S hS (preimageClosedSubspace a Z₁).1.ι :=
    isFinitePresentation_of_isPullback B S hS (preimageClosedSubspace a Z₁).2.1 Z₁.2.1
      (isAlgebraicSpace_yoneda B S hS T) W.2 (Subfunctor.isPullback_preimage a.hom Z₁.1) hZ₁fp
  have hcU := contains_reesChartSituation_centreIdeal _ hpfp (selfPresentation B S hS T)
  have hcR := contains_reesRelationSituation_centreIdeal _ hpfp (selfPresentation B S hS T)
  have hcRR := contains_reesDoubleSituation_centreIdeal _ hpfp (selfPresentation B S hS T)
  obtain ⟨e, -⟩ := exists_iso_schemeSpace_reesProjChart_of_isEtale hZ₁bl T ha hcU hcR hcRR hsq
  set R := reesProjChart (centreIdeal (preimageClosedSubspace a Z₁))
    (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS T) hcU
  have hVqc : IsQuasiCompactSpace B S hS V :=
    IsAffineSpace.isQuasiCompactSpace ⟨T, hTaff, ⟨eV⟩⟩
  have hfstp := isProper_fst_pullback_of_isProper hV φ hb₁p
  have hV₁qc : IsQuasiCompactSpace B S hS (pullback φ b₁.hom) :=
    isQuasiCompactSpace_of_isQuasiCompact B S hS hV hVqc _ hfstp.2.1.2
  have hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V :=
    isAbsolutelyQuasiSeparated_of_iso B S hS hZ hV eV
      (isAbsolutelyQuasiSeparated_yoneda_obj B S hS hZ T inferInstance)
  have hV₁qs : IsAbsolutelyQuasiSeparated B S hS hZ (pullback φ b₁.hom) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hV₁ hVqs
      (isQuasiSeparated_of_isSeparated B S hS hfstp.1)
  have eR : pullback φ b₁.hom ≅ yoneda.obj R := (ObjectProperty.ι _).mapIso e
  have hRqc : IsQuasiCompactSpace B S hS (yoneda.obj R) :=
    IsQuasiCompactSpace.of_iso B S hS hV₁qc eR
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj R) := by
    have := compactSpace_points_of_isQuasiCompactSpace B S hS (isAlgebraicSpace_yoneda B S hS R)
      hRqc
    exact (schemePointsHomeomorph B S hS R).compactSpace
  have : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj R) :=
    quasiSeparatedSpace_of_isAbsolutelyQuasiSeparated_yoneda B S hS hZ R
      (isAbsolutelyQuasiSeparated_of_iso B S hS hZ (isAlgebraicSpace_yoneda B S hS R) eR.symm hV₁qs)
  exact DominatesSections.of_iso e (dominatesSections_schemeSpace hZ R)

/-- **Dominating modifications crosses an elementary distinguished square.** Let
`(U ⊆ W, φ : V ⟶ W)` be an elementary distinguished square with `W` quasi-compact and
quasi-separated, `U` quasi-compact and `V` affine. If `U` dominates modifications, so does `W`. -/
theorem dominatesModifications_of_isElementaryDistinguishedSquare {W : AlgebraicSpaces B S hS}
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : Subfunctor W.1) (φ : V ⟶ W.1)
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 U φ)
    (hWqc : IsQuasiCompactSpace B S hS W.1)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W.1)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) (hVaff : IsAffineSpace B S hS V)
    (hPU : DominatesModifications
      (⟨U.toFunctor, hsq.isOpenSubspace.1⟩ : AlgebraicSpaces B S hS)) :
    DominatesModifications W := by
  intro U₀ hU₀qc X f hf hiso
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    AlgebraicGeometry.hasSheafify_bigFppfOver B S hS
  have hZ := B.contains_terminal
  have hUo : IsOpenSubspace B S hS U := hsq.isOpenSubspace
  have hV : IsAlgebraicSpace B S hS V := hsq.isAlgebraicSpace
  let A : OpenSubspaces B S hS U.toFunctor :=
    ⟨U₀.1.preimage U.ι, isOpenSubspace_preimage B S hS U.ι U₀.1 W.2 hUo.1 U₀.2⟩
  have hAqc : IsQuasiCompactSpace B S hS A.1.toFunctor :=
    isQuasiCompactSpace_preimage_toFunctor B S hS hZ W.2 hWqs hUo.1 hUqc U₀.1 hU₀qc U.ι
  let XU : AlgebraicSpaces B S hS :=
    ⟨pullback f.hom U.ι, isAlgebraicSpace_pullback B S hS f.hom U.ι X.2 hUo.1 W.2⟩
  let fU : XU ⟶ (⟨U.toFunctor, hUo.1⟩ : AlgebraicSpaces B S hS) :=
    ObjectProperty.homMk (pullback.snd f.hom U.ι)
  have hfU : IsProper B S hS fU.hom :=
    isProper_of_isPullback B S hS XU.2 X.2 hUo.1 W.2 (IsPullback.of_hasPullback f.hom U.ι) hf
  have hisoU : IsIso (pullback.snd fU.hom A.1.ι) := by
    have h := (IsPullback.of_hasPullback (pullback.snd f.hom U.ι) A.1.ι).paste_horiz
      (IsPullback.of_hasPullback f.hom U.ι)
    rw [← Subfunctor.fromPreimage_ι] at h
    exact isIso_snd_of_isPullback_comp f.hom U₀.1.ι _ h
  obtain ⟨U', bU, hbU, gU, hgU⟩ := hPU A hAqc XU fU hfU hisoU
  /- Extend the blowup of `U` to `W` (Stacks 086D). -/
  obtain ⟨W₁, b₁, hb₁, e₁, he₁⟩ := exists_isAdmissibleBlowup_isPullback' hZ hWqc hWqs U₀
    ⟨U, hUo⟩ hU₀qc hUqc bU hbU
  have hφ : IsEtale B S hS φ := hsq.isEtale
  let V₁ : AlgebraicSpaces B S hS :=
    ⟨pullback φ b₁.hom, isAlgebraicSpace_pullback B S hS φ b₁.hom hV W₁.2 W.2⟩
  have hDV₁ : DominatesSections V₁ := dominatesSections_pullback_of_isAffineSpace hV hVaff φ hφ hb₁
  let p : V₁.1 ⟶ W.1 := pullback.fst φ b₁.hom ≫ φ
  have hp : p = pullback.snd φ b₁.hom ≫ b₁.hom := pullback.condition
  have hVqc : IsQuasiCompactSpace B S hS V := IsAffineSpace.isQuasiCompactSpace hVaff
  have hfstp := isProper_fst_pullback_of_isProper hV φ (IsAdmissibleBlowup.isProper B S hS hb₁)
  have hV₁qc : IsQuasiCompactSpace B S hS V₁.1 :=
    isQuasiCompactSpace_of_isQuasiCompact B S hS hV hVqc _ hfstp.2.1.2
  let O₀ : OpenSubspaces B S hS W.1 := openSubspaceUnion B S hS W U₀ ⟨U, hUo⟩
  have hO₀qc : IsQuasiCompactSpace B S hS O₀.1.toFunctor := by
    refine isQuasiCompactSpace_of_isCompact_range B S hS W.2 O₀.2 ?_
    change IsCompact (subspacePointSet B S hS W.1 O₀.1)
    rw [subspacePointSet_openSubspaceUnion]
    refine IsCompact.union ?_ ?_
    · have := compactSpace_points_of_isQuasiCompactSpace B S hS U₀.2.1 hU₀qc
      exact isCompact_range (continuous_pointsMap B S hS U₀.1.ι)
    · have := compactSpace_points_of_isQuasiCompactSpace B S hS hUo.1 hUqc
      exact isCompact_range (continuous_pointsMap B S hS U.ι)
  let O : OpenSubspaces B S hS V₁.1 :=
    ⟨O₀.1.preimage p, isOpenSubspace_preimage B S hS p O₀.1 W.2 V₁.2 O₀.2⟩
  have hOqc : IsQuasiCompactSpace B S hS O.1.toFunctor :=
    isQuasiCompactSpace_preimage_toFunctor B S hS hZ W.2 hWqs V₁.2 hV₁qc O₀.1 hO₀qc p
  let Pa : Subfunctor O.1.toFunctor := U₀.1.preimage (O.1.ι ≫ p)
  let Pb : Subfunctor O.1.toFunctor := U.preimage (O.1.ι ≫ p)
  have hPa : IsOpenSubspace B S hS Pa :=
    isOpenSubspace_preimage B S hS (O.1.ι ≫ p) U₀.1 W.2 O.2.1 U₀.2
  have hPb : IsOpenSubspace B S hS Pb :=
    isOpenSubspace_preimage B S hS (O.1.ι ≫ p) U W.2 O.2.1 hUo
  have hcovE : IsEtaleCovering B S hS (fun | false => Pa.toFunctor | true => Pb.toFunctor)
      (fun | false => Pa.ι | true => Pb.ι) := by
    refine ⟨O.2.1, ?_, ?_, ?_⟩
    · rintro (_ | _)
      · exact hPa.1
      · exact hPb.1
    · rintro (_ | _)
      · exact isEtale_of_presheaf_etale B S hS (presheaf_etale_of_isOpenImmersion B S hS hPa.2)
      · exact isEtale_of_presheaf_etale B S hS (presheaf_etale_of_isOpenImmersion B S hS hPb.2)
    · refine Set.eq_univ_iff_forall.mpr fun x => ?_
      have hx : pointsMap B S hS _ (O.1.ι ≫ p) x ∈ subspacePointSet B S hS W.1 O₀.1 := by
        have h : pointsMap B S hS _ O.1.ι x ∈ subspacePointSet B S hS V₁.1 O.1 := ⟨x, rfl⟩
        rw [subspacePointSet_preimage B S hS] at h
        rwa [pointsMap_comp_apply]
      rw [subspacePointSet_openSubspaceUnion] at hx
      rcases hx with hx | hx
      · have h : x ∈ subspacePointSet B S hS O.1.toFunctor Pa := by
          rwa [subspacePointSet_preimage B S hS]
        exact Set.mem_iUnion.mpr ⟨false, h⟩
      · have h : x ∈ subspacePointSet B S hS O.1.toFunctor Pb := by
          rwa [subspacePointSet_preimage B S hS]
        exact Set.mem_iUnion.mpr ⟨true, h⟩
  have hcov := isFppfCovering_of_isEtaleCovering B S hS hcovE
  have : IsIso (pullback.snd f.hom U₀.1.ι) := hiso
  have he₁' : IsPullback bU.hom e₁.hom U.ι b₁.hom := AlgebraicSpaces.isPullback_hom B S hS he₁
  have hgU' : gU.hom ≫ pullback.snd f.hom U.ι = bU.hom := congrArg (fun m => m.hom) hgU
  have hgUf : gU.hom ≫ pullback.fst f.hom U.ι ≫ f.hom = bU.hom ≫ U.ι := by
    rw [pullback.condition, ← Category.assoc, hgU']
  let ga : Pa.toFunctor ⟶ X.1 := U₀.1.fromPreimage (O.1.ι ≫ p) ≫
    inv (pullback.snd f.hom U₀.1.ι) ≫ pullback.fst f.hom U₀.1.ι
  have hga : ga ≫ f.hom = U₀.1.fromPreimage (O.1.ι ≫ p) ≫ U₀.1.ι := by
    simp only [ga, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  let ℓb : Pb.toFunctor ⟶ U'.1 := he₁'.lift (U.fromPreimage (O.1.ι ≫ p))
    (Pb.ι ≫ O.1.ι ≫ pullback.snd φ b₁.hom)
    (by rw [Subfunctor.fromPreimage_ι, Category.assoc, Category.assoc, ← hp])
  let gb : Pb.toFunctor ⟶ X.1 := ℓb ≫ gU.hom ≫ pullback.fst f.hom U.ι
  have hgb : gb ≫ f.hom = U.fromPreimage (O.1.ι ≫ p) ≫ U.ι := by
    simp only [gb, Category.assoc]
    rw [hgUf, ← Category.assoc, he₁'.lift_fst]
  have hPaa : pullback.fst Pa.ι Pa.ι = pullback.snd Pa.ι Pa.ι :=
    (cancel_mono Pa.ι).1 pullback.condition
  have hPbb : pullback.fst Pb.ι Pb.ι = pullback.snd Pb.ι Pb.ι :=
    (cancel_mono Pb.ι).1 pullback.condition
  have hab : pullback.fst Pa.ι Pb.ι ≫ ga = pullback.snd Pa.ι Pb.ι ≫ gb := by
    refine eq_of_comp_eq_of_isIso_pullback_snd f.hom U₀.1
      (pullback.fst Pa.ι Pb.ι ≫ U₀.1.fromPreimage (O.1.ι ≫ p)) ?_ ?_
    · rw [Category.assoc, hga, Category.assoc]
    · rw [Category.assoc, hgb, Subfunctor.fromPreimage_ι, ← Category.assoc,
        ← pullback.condition, Category.assoc, Category.assoc, Subfunctor.fromPreimage_ι]
  obtain ⟨σ, hσ, -⟩ := existsUnique_desc_of_isFppfCovering B S hS
    (fun | false => Pa.toFunctor | true => Pb.toFunctor) (fun | false => Pa.ι | true => Pb.ι)
    hcov X.2.isSheaf (fun | false => ga | true => gb) (by
      rintro (_ | _) (_ | _)
      · exact hPaa ▸ rfl
      · exact hab
      · rw [← pullbackSymmetry_hom_comp_snd, Category.assoc, ← hab, ← Category.assoc,
          pullbackSymmetry_hom_comp_fst]
      · exact hPbb ▸ rfl)
  have hσf : σ ≫ f.hom = O.1.ι ≫ p := by
    obtain ⟨d, -, hd⟩ := existsUnique_desc_of_isFppfCovering B S hS
      (fun | false => Pa.toFunctor | true => Pb.toFunctor) (fun | false => Pa.ι | true => Pb.ι)
      hcov W.2.isSheaf (fun | false => Pa.ι ≫ O.1.ι ≫ p | true => Pb.ι ≫ O.1.ι ≫ p) (by
        rintro (_ | _) (_ | _) <;> simp only [← Category.assoc, pullback.condition])
    have h1 := hd (σ ≫ f.hom) (by
      rintro (_ | _)
      · change Pa.ι ≫ σ ≫ f.hom = _
        rw [← Category.assoc, hσ false]
        change ga ≫ f.hom = _
        rw [hga, Subfunctor.fromPreimage_ι]
      · change Pb.ι ≫ σ ≫ f.hom = _
        rw [← Category.assoc, hσ true]
        change gb ≫ f.hom = _
        rw [hgb, Subfunctor.fromPreimage_ι])
    have h2 := hd (O.1.ι ≫ p) (by rintro (_ | _) <;> rfl)
    exact h1.trans h2.symm
  let X₁ : AlgebraicSpaces B S hS :=
    ⟨pullback f.hom p, isAlgebraicSpace_pullback B S hS f.hom p X.2 V₁.2 W.2⟩
  let f₁ : X₁ ⟶ V₁ := ObjectProperty.homMk (pullback.snd f.hom p)
  have hf₁ : IsProper B S hS f₁.hom :=
    isProper_of_isPullback B S hS X₁.2 X.2 V₁.2 W.2 (IsPullback.of_hasPullback f.hom p) hf
  let σ₁ : O.1.toFunctor ⟶ X₁.1 := pullback.lift σ O.1.ι hσf
  have hσ₁ : σ₁ ≫ f₁.hom = O.1.ι := pullback.lift_snd _ _ _
  obtain ⟨V₂, b₂, hb₂, g₂, hg₂, hext₂⟩ := hDV₁ O hOqc X₁ f₁ hf₁ σ₁ hσ₁
  obtain ⟨Z₂, hZ₂fp, hZ₂disj, hZ₂bl⟩ := hb₂
  have sq₁ := isElementaryDistinguishedSquare_preimage B S hS W.2 W₁.2 U φ hsq b₁.hom
  let UW₁ : AlgebraicSpaces B S hS := ⟨(U.preimage b₁.hom).toFunctor, sq₁.isOpenSubspace.1⟩
  let E := emptyClosedSubspace UW₁
  have hptsUO : subspacePointSet B S hS V₁.1 (U.preimage p) ⊆ subspacePointSet B S hS V₁.1 O.1 := by
    change subspacePointSet B S hS V₁.1 (U.preimage p) ⊆
      subspacePointSet B S hS V₁.1 (O₀.1.preimage p)
    rw [subspacePointSet_preimage B S hS, subspacePointSet_preimage B S hS,
      subspacePointSet_openSubspaceUnion]
    exact Set.preimage_mono Set.subset_union_right
  have hcompat : ∀ (Y : BigFppfOver B S hS) (a : (U.preimage b₁.hom).toFunctor.obj (Opposite.op Y))
      (b : V₁.1.obj (Opposite.op Y)),
      (U.preimage b₁.hom).ι.app (Opposite.op Y) a = (pullback.snd φ b₁.hom).app (Opposite.op Y) b →
        (a ∈ E.1.obj (Opposite.op Y) ↔ b ∈ Z₂.1.obj (Opposite.op Y)) := by
    intro Y a b hab
    have hEZ : (⊥ : Subfunctor V₁.1).sheafify (BigFppfOver.topology B S hS) ≤ Z₂.1 :=
      Subfunctor.sheafify_le (G := ⊥) (G' := Z₂.1) bot_le
        ((isSheaf_iff_isSheaf_of_type _ _).1 V₁.2.isSheaf)
        ((isSheaf_iff_isSheaf_of_type _ _).1 Z₂.2.1.isSheaf)
    constructor
    · intro ha
      exact hEZ _ (show b ∈ ((⊥ : Subfunctor V₁.1).sheafify
        (BigFppfOver.topology B S hS)).obj (Opposite.op Y) from ha)
    · intro hb
      have hAE : Z₂.1 ⊓ U.preimage p ≤
          (⊥ : Subfunctor V₁.1).sheafify (BigFppfOver.topology B S hS) := by
        refine le_of_range_pointsMap_ι_subset B S hS
          (isOpenSubspace_sheafify_bot B S hS V₁.1 V₁.2) ?_
        rintro _ ⟨x, rfl⟩
        exfalso
        have hmem : ∀ {G : Subfunctor V₁.1} (hG : Z₂.1 ⊓ U.preimage p ≤ G),
            pointsMap B S hS _ (Z₂.1 ⊓ U.preimage p).ι x ∈ subspacePointSet B S hS V₁.1 G :=
          fun hG => ⟨pointsMap B S hS _ (Subfunctor.homOfLe hG) x, by
            rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]⟩
        exact Set.disjoint_left.1 hZ₂disj (hptsUO (hmem inf_le_right)) (hmem inf_le_left)
      have hbU : b ∈ (U.preimage p).obj (Opposite.op Y) := by
        change p.app (Opposite.op Y) b ∈ U.obj (Opposite.op Y)
        rw [hp]
        change b₁.hom.app (Opposite.op Y) ((pullback.snd φ b₁.hom).app (Opposite.op Y) b) ∈ _
        rw [← hab]
        exact a.2
      exact hAE _ ⟨hb, hbU⟩
  have hEc : IsClosedSubspace B S hS E.1 := E.2
  let Z := squareGlue B S hS (U.preimage b₁.hom) (pullback.snd φ b₁.hom) E.1 Z₂.1
  have hZc : IsClosedSubspace B S hS Z := isClosedSubspace_squareGlue W₁.2 sq₁ hEc Z₂.2 hcompat
  have hZfp : IsFinitePresentation B S hS Z.ι := isFinitePresentation_squareGlue W₁.2 sq₁ hEc Z₂.2
    hcompat (isFinitePresentation_ι_emptyClosedSubspace UW₁) hZ₂fp
  have hZU : Z.preimage (U.preimage b₁.hom).ι = E.1 := preimage_ι_squareGlue W₁.2 sq₁ Z₂.2 hcompat
  have hZV : Z.preimage (pullback.snd φ b₁.hom) = Z₂.1 := preimage_squareGlue W₁.2 sq₁ Z₂.2 hcompat
  obtain ⟨Y', c, hc⟩ := exists_isBlowupAlong_of_isFinitePresentation (X := W₁) ⟨Z, hZc⟩ hZfp
  have hcdisj : Disjoint (subspacePointSet B S hS W₁.1 (U₀.1.preimage b₁.hom))
      (subspacePointSet B S hS W₁.1 Z) := by
    refine Set.disjoint_left.2 fun x hx₀ hxZ => ?_
    rcases mem_range_or_mem_range_of_isElementaryDistinguishedSquare B S hS W₁.2 _ _ sq₁ x with
      ⟨y, rfl⟩ | ⟨v, rfl⟩
    · have hy : y ∈ subspacePointSet B S hS UW₁.1 (Z.preimage (U.preimage b₁.hom).ι) := by
        rwa [subspacePointSet_preimage B S hS]
      rwa [hZU, subspacePointSet_emptyClosedSubspace] at hy
    · have hv₂ : v ∈ subspacePointSet B S hS V₁.1 Z₂.1 := by
        rwa [← hZV, subspacePointSet_preimage B S hS]
      have hv₀ : v ∈ subspacePointSet B S hS V₁.1 O.1 := by
        change v ∈ subspacePointSet B S hS V₁.1 (O₀.1.preimage p)
        rw [subspacePointSet_preimage B S hS, subspacePointSet_openSubspaceUnion]
        left
        rw [subspacePointSet_preimage B S hS] at hx₀
        rwa [hp, pointsMap_comp_apply]
      exact Set.disjoint_left.1 hZ₂disj hv₀ hv₂
  have hcadm : IsAdmissibleBlowup B S hS
      ⟨U₀.1.preimage b₁.hom, isOpenSubspace_preimage B S hS b₁.hom U₀.1 W.2 W₁.2 U₀.2⟩ c :=
    ⟨⟨Z, hZc⟩, hZfp, hcdisj, hc⟩
  have hbadm := isAdmissibleBlowup_comp_of_isQuasiCompactSpace hZ hWqc hWqs U₀ hb₁ hcadm
  refine ⟨Y', c ≫ b₁, hbadm, ?_⟩
  have sq₂ := isElementaryDistinguishedSquare_preimage B S hS W₁.2 Y'.2 (U.preimage b₁.hom)
    (pullback.snd φ b₁.hom) sq₁ c.hom
  have hpo := isPushout_elementaryDistinguishedSquare B S hS Y'.2 _ _ sq₂
  let Aset : Subfunctor Y'.1 := (U.preimage b₁.hom).preimage c.hom
  let sndC := pullback.snd (pullback.snd φ b₁.hom) c.hom
  let fstC := pullback.fst (pullback.snd φ b₁.hom) c.hom
  have hCalg := sq₂.isAlgebraicSpace
  let ℓ₁ : (U.preimage b₁.hom).toFunctor ⟶ U'.1 :=
    he₁'.lift (U.fromPreimage b₁.hom) (U.preimage b₁.hom).ι (Subfunctor.fromPreimage_ι _ _)
  let gA : Aset.toFunctor ⟶ X.1 :=
    (U.preimage b₁.hom).fromPreimage c.hom ≫ ℓ₁ ≫ gU.hom ≫ pullback.fst f.hom U.ι
  have hφ₁flat : IsFlat B S hS (pullback.snd φ b₁.hom) := isFlat_of_isEtale B S hS sq₁.isEtale
  let Ca : AlgebraicSpaces B S hS := ⟨pullback (pullback.snd φ b₁.hom) c.hom, hCalg⟩
  let φ₁a : V₁ ⟶ W₁ := ObjectProperty.homMk (pullback.snd φ b₁.hom)
  have hsqC := isPullback_homMk B S hS V₁.2 Y'.2 W₁.2 hCalg
    (IsPullback.of_hasPullback (pullback.snd φ b₁.hom) c.hom)
  have hbC := isBlowupAlong_preimage_of_isPullback_of_isFlat (g := φ₁a) hφ₁flat hc hsqC
  have hpreZ : preimageClosedSubspace φ₁a ⟨Z, hZc⟩ = Z₂ := Subtype.ext hZV
  rw [hpreZ] at hbC
  obtain ⟨e₂, he₂⟩ := hbC.exists_iso hZ₂bl
  have he₂' : e₂.hom.hom ≫ b₂.hom = fstC := congrArg (fun m => m.hom) he₂
  let gC : Ca.1 ⟶ X.1 := e₂.hom.hom ≫ g₂.hom ≫ pullback.fst f.hom p
  have hg₂' : g₂.hom ≫ pullback.snd f.hom p = b₂.hom := congrArg (fun m => m.hom) hg₂
  have hUO₀ : U ≤ O₀.1 := by
    calc U = openSubspaceOfPoints B S hS W.1 (Set.range (pointsMap B S hS U.toFunctor U.ι)) :=
          eq_openSubspaceOfPoints_range_pointsMap B S hS W.2 U hUo
      _ ≤ O₀.1 := openSubspaceOfPoints_mono B S hS Set.subset_union_right
  have he₁mono : Mono e₁.hom := he₁'.mono_snd_of_mono
  have hagree : pullback.snd Aset.ι sndC ≫ gC = pullback.fst Aset.ι sndC ≫ gA := by
    let t₁ := pullback.fst Aset.ι sndC
    let t₂ := pullback.snd Aset.ι sndC
    let m : pullback Aset.ι sndC ⟶ V₂.1 := t₂ ≫ e₂.hom.hom
    have hmb : m ≫ b₂.hom ≫ p = t₁ ≫ Aset.ι ≫ c.hom ≫ b₁.hom := by
      simp only [m, Category.assoc]
      rw [← Category.assoc e₂.hom.hom, he₂', hp, ← Category.assoc fstC,
        pullback.condition, Category.assoc, ← Category.assoc t₂, ← pullback.condition,
        Category.assoc]
    have hmemU : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ) (x : (pullback Aset.ι sndC).obj Y),
        (m ≫ b₂.hom ≫ p).app Y x ∈ U.obj Y := by
      intro Y x
      rw [hmb]
      exact (t₁.app Y x).2
    let kO : pullback Aset.ι sndC ⟶ O.1.toFunctor := Subfunctor.lift (m ≫ b₂.hom) (by
      rintro Y _ ⟨x, rfl⟩
      exact hUO₀ Y (by simpa [Category.assoc] using hmemU Y x))
    have hkO : kO ≫ O.1.ι = m ≫ b₂.hom := Subfunctor.lift_ι _ _
    let kb : pullback Aset.ι sndC ⟶ Pb.toFunctor := Subfunctor.lift kO (by
      rintro Y _ ⟨x, rfl⟩
      change (O.1.ι ≫ p).app Y (kO.app Y x) ∈ U.obj Y
      rw [← NatTrans.comp_app_apply, ← Category.assoc, hkO]
      simpa [Category.assoc] using hmemU Y x)
    have hkb : kb ≫ Pb.ι = kO := Subfunctor.lift_ι _ _
    let kpre : pullback Aset.ι sndC ⟶ (O.1.preimage b₂.hom).toFunctor :=
      (Subfunctor.isPullback_preimage b₂.hom O.1).lift kO m hkO
    have hkpre₁ : kpre ≫ (O.1.preimage b₂.hom).ι = m := IsPullback.lift_snd _ _ _ _
    have hkpre₂ : kpre ≫ O.1.fromPreimage b₂.hom = kO := IsPullback.lift_fst _ _ _ _
    have hC : t₂ ≫ gC = kb ≫ ℓb ≫ gU.hom ≫ pullback.fst f.hom U.ι := by
      have h1 : t₂ ≫ gC = kO ≫ σ := by
        change m ≫ g₂.hom ≫ pullback.fst f.hom p = _
        rw [← hkpre₁, Category.assoc, ← Category.assoc _ g₂.hom, hext₂, Category.assoc,
          (show σ₁ ≫ pullback.fst f.hom p = σ from pullback.lift_fst _ _ _),
          ← Category.assoc, hkpre₂]
      rw [h1, ← hkb, Category.assoc]
      exact congrArg (kb ≫ ·) (hσ true)
    have hℓ : kb ≫ ℓb = t₁ ≫ (U.preimage b₁.hom).fromPreimage c.hom ≫ ℓ₁ := by
      rw [← cancel_mono e₁.hom]
      simp only [Category.assoc]
      rw [he₁'.lift_snd, he₁'.lift_snd, Subfunctor.fromPreimage_ι, ← Category.assoc kb,
        hkb, ← Category.assoc kO, hkO]
      change ((t₂ ≫ e₂.hom.hom) ≫ b₂.hom) ≫ pullback.snd φ b₁.hom = _
      rw [Category.assoc, Category.assoc, ← Category.assoc e₂.hom.hom, he₂', pullback.condition,
        ← Category.assoc, ← pullback.condition, Category.assoc]
    rw [hC, ← Category.assoc kb, hℓ]
    simp only [Category.assoc]
    rfl
  let gCa : Ca ⟶ X := ObjectProperty.homMk gC
  let gAa : (⟨Aset.toFunctor, sq₂.isOpenSubspace.1⟩ : AlgebraicSpaces B S hS) ⟶ X :=
    ObjectProperty.homMk gA
  have hw : (ObjectProperty.homMk (pullback.snd Aset.ι sndC) :
      AlgebraicSpaces.fiberProduct B S hS
        (ObjectProperty.homMk Aset.ι :
          (⟨Aset.toFunctor, sq₂.isOpenSubspace.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y'.1, Y'.2⟩)
        (ObjectProperty.homMk sndC : (⟨Ca.1, hCalg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y'.1, Y'.2⟩) ⟶
          ⟨Ca.1, hCalg⟩) ≫ gCa =
      (ObjectProperty.homMk (pullback.fst Aset.ι sndC) : _ ⟶
        (⟨Aset.toFunctor, sq₂.isOpenSubspace.1⟩ : AlgebraicSpaces B S hS)) ≫ gAa :=
    ObjectProperty.hom_ext _ hagree
  refine ⟨hpo.desc gCa gAa hw, ?_⟩
  refine hpo.hom_ext ?_ ?_
  · rw [← Category.assoc, hpo.inl_desc]
    refine ObjectProperty.hom_ext _ ?_
    change (e₂.hom.hom ≫ g₂.hom ≫ pullback.fst f.hom p) ≫ f.hom = sndC ≫ c.hom ≫ b₁.hom
    simp only [Category.assoc]
    rw [pullback.condition, ← Category.assoc g₂.hom, hg₂', ← Category.assoc, he₂', hp,
      ← Category.assoc, pullback.condition, Category.assoc]
  · rw [← Category.assoc, hpo.inr_desc]
    refine ObjectProperty.hom_ext _ ?_
    change ((U.preimage b₁.hom).fromPreimage c.hom ≫ ℓ₁ ≫ gU.hom ≫ pullback.fst f.hom U.ι) ≫
      f.hom = Aset.ι ≫ c.hom ≫ b₁.hom
    simp only [Category.assoc]
    rw [hgUf, ← Category.assoc ℓ₁, he₁'.lift_fst,
      Subfunctor.fromPreimage_ι, ← Category.assoc, Subfunctor.fromPreimage_ι, Category.assoc]

end AlgebraicGeometry.Space

end
