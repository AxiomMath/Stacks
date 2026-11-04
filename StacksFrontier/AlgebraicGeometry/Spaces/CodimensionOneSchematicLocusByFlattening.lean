module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtCompactSet
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FiniteLocallyFreePushPull
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionOneChartInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.GenericPointsAndDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableDenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZariskiLocallyQuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartProperImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoverCodimensionOneSchematicNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSurjectiveAffineSource
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Reduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae

/-!
# Separated algebraic spaces are schemes in codimension one, by flattening (Stacks 0ADE)

Stacks 0ADE is a remark giving "a sketch of a proof of Lemma 0ADD which avoids using More on
Groupoids, Lemma 0ABI".  Lemma 0ADD says:

> Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `x ∈ |X|`. If `X` is
> separated, locally Noetherian, and the dimension of the local ring of `X` at `x` is `≤ 1`
> (Properties of Spaces, Definition 04NA), then there exists an open subspace of `X` containing
> `x` which is a scheme.

This file proves that statement along the remark's route, and registers it under Stacks 0ADE.
No result about invariant affine opens of groupoids (Stacks 0ABI) is used, nor imported: the
groupoid argument of the base proof of 0ADD,
`AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_localRingDimension_le_one`, is
replaced by the five steps of the remark.

* **Step 1.** "We may assume `X` is a reduced Noetherian separated algebraic space (by
  Cohomology of Spaces, Lemma 07VP or Limits of Spaces, Lemma 07VU) and we may choose a finite
  surjective morphism `Y ⟶ X` where `Y` is a Noetherian scheme."  The reduction is
  `AlgebraicGeometry.Space.exists_isOpenSubspace_isAffineSpace_of_reduction` (the thickening
  case of Stacks 07VT, as in 07VU).  The finite surjective cover by a scheme near `x` is produced
  by the induction on the degree of an étale chart of the base proof of 0ADD
  (`Space.exists_isOpenSubspace_isRepresentable_of_chart_rank_le_of_fittingBlowups`), in
  place of Stacks 09YC: at each stage the scheme-theoretic image of the chart is a scheme finite
  and surjective over a neighbourhood `Z₂` of `x`.
* **Step 2.** After shrinking `X`, a finite morphism `X' ⟶ X`, isomorphic over a dense open, and
  a closed subscheme `Y'` of `X' ×_X Y` finite locally free and surjective over `X'`.  The
  flattening blowup is the blowup in the Fitting ideal of the stratum
  (`AlgebraicGeometry.Space.exists_blowup_fittingStratum`, through Stacks 0D0Q, 0866, 0864);
  one is taken for each Fitting stratum of `Y ⟶ X` meeting the closure of `x`, so `X'` is a
  finite family, finite over a neighbourhood of `x` by Stacks 0AD2.
* **Step 3.** After shrinking, `X'` is a scheme near the fibre over `x`: Stacks 07S6 and 09NN
  (`AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_isFiniteLocallyFree_cover`).
* **Step 4.** An affine open `W' ⊆ X'` containing the fibre over `x` which is the inverse image
  of an open subspace `W ⊆ X`: Stacks 0ADC and 09NN, and the principal open `D(f')`.
* **Step 5.** `W' ⟶ W` is finite surjective and `W` is a scheme by Stacks 07VP; indeed `W` is
  affine, so the open subspace produced is an affine scheme.

Steps 3 to 5 are `AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_finite_family`
and Steps 2 to 5 for a given cover are
`AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_isFinite_isSurjective_cover`.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenSubspace_isAffineSpace_of_reduction`: Step 1.
* `Space.exists_isOpenSubspace_isRepresentable_of_chart_rank_le_of_fittingBlowups`:
  the induction on the degree of an étale chart, with Steps 1 to 5 at each stage.
* `Space.exists_isOpenSubspace_isRepresentable_of_localRingDimension_le_one_of_fittingBlowups`:
  **Stacks 0ADE**.

## References

* [Stacks Project, Tag 0ADE](https://stacks.math.columbia.edu/tag/0ADE)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 07VU](https://stacks.math.columbia.edu/tag/07VU)
* [Stacks Project, Tag 0D0Q](https://stacks.math.columbia.edu/tag/0D0Q)
* [Stacks Project, Tag 0AD2](https://stacks.math.columbia.edu/tag/0AD2)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
* [Stacks Project, Tag 09NN](https://stacks.math.columbia.edu/tag/09NN)
* [Stacks Project, Tag 0ADC](https://stacks.math.columbia.edu/tag/0ADC)
* [Stacks Project, Tag 07VP](https://stacks.math.columbia.edu/tag/07VP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A base change of a morphism which is surjective on points is surjective on points. -/
private theorem isSurjective_of_isPullback_of_presheaf
    {W Z F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : W ⟶ Z} {q : W ⟶ F} {g : Z ⟶ G}
    {h : F ⟶ G} (sq : IsPullback p q g h) (hh : IsSurjective B S hS h) :
    IsSurjective B S hS p := by
  intro z
  obtain ⟨x, hx⟩ := hh (pointsMap B S hS Z g z)
  obtain ⟨w, hw, -⟩ := exists_point_of_isPullback_presheaf B S hS sq z x hx.symm
  exact ⟨w, hw⟩

/-- **Step 1 of Stacks 0ADE: one may assume `X` reduced.**  If a point of the reduction `X_red`
of an algebraic space lies in an open subspace of `X_red` which is an affine scheme, then its
image lies in an open subspace of `X` which is an affine scheme.

The open subspace `G ⊆ X` with the same points receives the surjective closed immersion
`G ×_X X_red ⟶ G` from an affine scheme, so it is affine by the thickening case of Stacks 07VT
(`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective`), which is the
argument of Limits of Spaces, Lemma 07VU. -/
theorem exists_isOpenSubspace_isAffineSpace_of_reduction {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (xr : points B S hS (reduction B S hS X hX).toFunctor)
    (h : ∃ G : Subfunctor (reduction B S hS X hX).toFunctor, IsOpenSubspace B S hS G ∧
      IsAffineSpace B S hS G.toFunctor ∧ xr ∈ Set.range (pointsMap B S hS G.toFunctor G.ι)) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ IsAffineSpace B S hS G.toFunctor ∧
      pointsMap B S hS _ (reduction B S hS X hX).ι xr ∈
        Set.range (pointsMap B S hS G.toFunctor G.ι) := by
  classical
  obtain ⟨G, hG, hGaff, hxG⟩ := h
  have hR : IsClosedSubspace B S hS (reduction B S hS X hX) :=
    isClosedSubspace_reducedClosedSubspace B S hS X hX _ _
  have hRinj := pointsMap_injective_of_mono B S hS (reduction B S hS X hX).ι
  have hRsurj := surjective_pointsMap_ι_reduction B S hS X hX
  have hRclosed : IsClosedMap (pointsMap B S hS _ (reduction B S hS X hX).ι) :=
    isClosed_of_universallyClosed B S hS hX (reduction B S hS X hX).ι
      (universallyClosed_of_isClosedImmersion B S hS hR.1 hX (reduction B S hS X hX).ι hR.2)
  -- the open subspace of `X` with the points of `G`
  set Gset := pointsMap B S hS _ (reduction B S hS X hX).ι ''
    Set.range (pointsMap B S hS G.toFunctor G.ι) with hGset
  have hGopen : IsOpen Gset := by
    have : Gset = (pointsMap B S hS _ (reduction B S hS X hX).ι ''
        (Set.range (pointsMap B S hS G.toFunctor G.ι))ᶜ)ᶜ := by
      rw [hGset, Set.image_compl_eq ⟨hRinj, hRsurj⟩, compl_compl]
    rw [this]
    exact (hRclosed _
      (isOpen_range_pointsMap_of_isOpenImmersion B S hS _ hG.2).isClosed_compl).isOpen_compl
  obtain ⟨G', hG', hG'range⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hX Gset hGopen
  have hpre : G'.preimage (reduction B S hS X hX).ι = G := by
    refine eq_of_isOpenSubspace_of_range_eq B S hS
      (isOpenSubspace_preimage B S hS (reduction B S hS X hX).ι G' hX hR.1 hG') hG ?_
    rw [pointsRange_preimage, hG'range, hGset, hRinj.preimage_image]
  -- `G' ×_X X_red ⟶ G'` is a surjective closed immersion from an affine scheme
  have sq : IsPullback (G'.fromPreimage (reduction B S hS X hX).ι)
      (G'.preimage (reduction B S hS X hX).ι).ι G'.ι (reduction B S hS X hX).ι :=
    Subfunctor.isPullback_preimage (reduction B S hS X hX).ι G'
  have hci : IsClosedImmersion B S hS (G'.fromPreimage (reduction B S hS X hX).ι) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sq.flip hR.2
  have hsrc : IsAffineSpace B S hS (G'.preimage (reduction B S hS X hX).ι).toFunctor :=
    hpre ▸ hGaff
  refine ⟨G', hG', isAffineSpace_of_isClosedImmersion_of_isSurjective B S hS _
    (isOpenSubspace_preimage B S hS (reduction B S hS X hX).ι G' hX hR.1 hG').1 hG'.1 hci
      (isSurjective_of_isPullback_of_presheaf B S hS sq hRsurj) hsrc, ?_⟩
  rw [hG'range]
  exact ⟨xr, hxG, rfl⟩

/-- An open subspace of an absolutely separated, locally Noetherian algebraic space is again
absolutely separated and locally Noetherian. -/
private theorem isAbsolutelySeparated_and_hasEtaleLocalProperty_of_isOpenImmersion
    {F Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hZ : IsAlgebraicSpace B S hS Z) (f : F ⟶ Z) (hf : IsOpenImmersion B S hS f)
    (hsep : IsAbsolutelySeparated B S hS B.contains_terminal Z)
    (hnoeth : HasEtaleLocalProperty B S hS Z (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    IsAbsolutelySeparated B S hS B.contains_terminal F ∧
      HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  ⟨isAbsolutelySeparated_of_isSeparated B S hS B.contains_terminal hsep
      (isSeparated_of_mono f (mono_of_presheaf_isOpenImmersion hf)),
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hF hZ f
      (isLocallyOfFiniteType_of_isEtale B S hS hZ (isEtale_of_isOpenImmersion B S hS hf))
      hnoeth⟩

/-- **The induction on the degree of the chart in the proof of Stacks 0ADD, along Stacks 0ADE.**
This is the induction of the base proof of Stacks 0ADD,
`AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_chart_rank_le`, with its last
step changed: once the scheme-theoretic image of the chart is a scheme finite and surjective over
an open `Z₂ ∋ z` (the finite surjective cover by a scheme of Step 1 of Stacks 0ADE), the open
subspace of `Z₂` around `z` which is an affine scheme is produced by Steps 1 to 5 of Stacks 0ADE
— the reduction `AlgebraicGeometry.Space.exists_isOpenSubspace_isAffineSpace_of_reduction`
followed by `exists_isOpenSubspace_isRepresentable_of_isFinite_isSurjective_cover` — instead
of Stacks 0ABI and 07VP.  The inductive hypothesis is this statement itself, so Stacks 0ABI is
used at no level of the induction.  The open subspace produced is affine. -/
theorem exists_isOpenSubspace_isRepresentable_of_chart_rank_le_of_fittingBlowups (d : ℕ) :
    ∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_ : IsAlgebraicSpace B S hS Z)
      (_ : IsAbsolutelySeparated B S hS B.contains_terminal Z)
      (_ : HasEtaleLocalProperty B S hS Z (fun T : Scheme.{u} => IsLocallyNoetherian T))
      (z : points B S hS Z) (_ : localRingDimension B S hS z ≤ 1)
      (V : BigFppfOver B S hS) (_ : CompactSpace ((BigFppfOver.toScheme B S hS).obj V))
      (v : yoneda.obj V ⟶ Z) (_ : IsEtale B S hS v)
      (_ : z ∈ Set.range (pointsMap B S hS _ v))
      {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_ : IsAlgebraicSpace B S hS Q)
      (q : Q ⟶ Z) (_ : IsProper B S hS q) (_ : yoneda.relativelyRepresentable q)
      (i : yoneda.obj V ⟶ Q) (_ : IsImmersion B S hS i) (_ : i ≫ q = v)
      (_ : ChartRankAtCodimZeroLE B S hS V v d),
      ∃ G : Subfunctor Z, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
        IsAffineSpace B S hS G.toFunctor ∧ z ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) := by
  have hpre : ∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_ : IsAlgebraicSpace B S hS Z)
      (U : Subfunctor Z) (_ : IsOpenSubspace B S hS U) (G : Subfunctor Z)
      (_ : IsOpenSubspace B S hS G) (_ : G.toFunctor.IsRepresentable),
      (G.preimage U.ι).toFunctor.IsRepresentable := by
    intro Z hZ U hU G hG hGrep
    have hP : IsOpenSubspace B S hS (G.preimage U.ι) :=
      isOpenSubspace_preimage B S hS U.ι G hZ hU.1 hG
    have hle : Subfunctor.range ((G.preimage U.ι).ι ≫ U.ι) ≤ G := by
      rintro T _ ⟨a, rfl⟩
      exact a.2
    have := isRepresentable_of_le_of_isRepresentable B S hS
      (isOpenSubspace_range_ι_comp B S hS U hU _ hP) hle hGrep
    exact isRepresentable_of_natIso _ (asIso (Subfunctor.toRange ((G.preimage U.ι).ι ≫ U.ι))).symm
  -- Steps 1 to 5 of Stacks 0ADE for a space with a finite surjective cover by a scheme
  have hstep : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_ : IsAlgebraicSpace B S hS Y)
      (_ : IsAbsolutelySeparated B S hS B.contains_terminal Y)
      (_ : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
      (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ Y) (_ : IsFinite B S hS g)
      (_ : IsSurjective B S hS g) (y : points B S hS Y) (_ : localRingDimension B S hS y ≤ 1),
      ∃ G : Subfunctor Y, IsOpenSubspace B S hS G ∧ IsAffineSpace B S hS G.toFunctor ∧
        y ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) := by
    intro Y hY hsepY hnoethY U g hgfin hgsurj y hdimy
    -- Step 1: the reduction `Y_red`, with the base change of the cover
    have hR : IsClosedSubspace B S hS (reduction B S hS Y hY) :=
      isClosedSubspace_reducedClosedSubspace B S hS Y hY _ _
    obtain ⟨yr, hyr⟩ := surjective_pointsMap_ι_reduction B S hS Y hY y
    have hRsep : IsAbsolutelySeparated B S hS B.contains_terminal
        (reduction B S hS Y hY).toFunctor :=
      isAbsolutelySeparated_of_isSeparated B S hS B.contains_terminal hsepY
        (isSeparated_of_mono (reduction B S hS Y hY).ι inferInstance)
    have hRnoeth : HasEtaleLocalProperty B S hS (reduction B S hS Y hY).toFunctor
        (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
      isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hR.1 hY (reduction B S hS Y hY).ι
        (isLocallyOfFiniteType_of_isImmersion B S hS _
          (isImmersion_of_isClosedImmersion B S hS hR.2)) hnoethY
    have hdimR : localRingDimension B S hS yr ≤ 1 := by
      have h := localRingDimension_le_of_isLocallyQuasiFinite B S hS hR.1 hY
        (reduction B S hS Y hY).ι
        (isLocallyQuasiFinite_of_isImmersion B S hS _
          (isImmersion_of_isClosedImmersion B S hS hR.2)) yr
      rw [hyr] at h
      exact h.trans hdimy
    have sq : IsPullback (hR.2.rep.fst g) (yoneda.map (hR.2.rep.snd g))
        (reduction B S hS Y hY).ι g := hR.2.rep.isPullback g
    have hgrfin : IsFinite B S hS (hR.2.rep.fst g) := isFinite_of_isPullback B S hS sq.flip hgfin
    -- Steps 2 to 5 on `Y_red`, and back to `Y`
    rw [← hyr]
    exact exists_isOpenSubspace_isAffineSpace_of_reduction B S hS hY yr
      (exists_isOpenSubspace_isRepresentable_of_isFinite_isSurjective_cover B S hS hR.1 hRsep
        hRnoeth _ _ hgrfin (isSurjective_of_isPullback_of_presheaf B S hS sq hgsurj) yr hdimR)
  have hrep : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAffineSpace B S hS F →
      F.IsRepresentable :=
    fun ⟨_, _, ⟨e⟩⟩ => isRepresentable_of_natIso _ e.symm
  induction d with
  | zero =>
    intro Z hZ _ _ z _ V _ v hv hzv _ _ _ _ _ _ _ _ hrank
    exact absurd hzv
      (notMem_range_pointsMap_of_chartRankAtCodimZeroLE_zero B S hS hZ V v hv hrank z)
  | succ d ih =>
    intro Z hZ hsep hnoeth z hdim V hVc v hv hzv Q hQ q hq hqr i hi hiq hrank
    set Vb := schemeTheoreticImageSubfunctor B S hS i with hVb
    set j := toSchemeTheoreticImage B S hS i with hj
    set p := Vb.ι ≫ q with hpdef
    have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
    have hVbcl : IsClosedSubspace B S hS Vb :=
      isClosedSubspace_schemeTheoreticImageSubfunctor B S hS i hQ
    have hY : IsAlgebraicSpace B S hS Vb.toFunctor := hVbcl.1
    have hp : IsProper B S hS p :=
      isProper_comp B S hS hVbcl.1 hQ hZ _ _
        (isProper_of_isClosedImmersion B S hS hVbcl.1 hQ _ hVbcl.2) hq
    have hYsep : IsAbsolutelySeparated B S hS B.contains_terminal Vb.toFunctor :=
      isAbsolutelySeparated_of_isSeparated B S hS B.contains_terminal hsep hp.1
    have hYnoeth :=
      isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hY hZ p hp.2.1.1 hnoeth
    have hQsep : IsAbsolutelySeparated B S hS B.contains_terminal Q :=
      isAbsolutelySeparated_of_isSeparated B S hS B.contains_terminal hsep hq.1
    have hiqc : IsQuasiCompact B S hS i :=
      isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal hQ
        (isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS B.contains_terminal Q hQsep)
        (isQuasiCompactSpace_yoneda B S hS V hVc) i
    obtain ⟨-, hiso, hrange, -, -⟩ :=
      isOpenImmersion_and_dense_toSchemeTheoreticImage_of_qc_or_reduced B S hS hV hQ i hi
        (Or.inl hiqc)
    have hjp : j ≫ p = v := by
      rw [hpdef, ← Category.assoc, hj, toSchemeTheoreticImage_ι B S hS i, hiq]
    -- `Y` is finite over an open `Z₁ ∋ z`, which we shrink into the image of `v`
    obtain ⟨Z₁, hZ₁, hzZ₁, hfin₁⟩ :=
      exists_isOpenSubspace_isFinite_schemeTheoreticImage B S hS hZ hsep hnoeth z hdim V hVc v hv
        hQ q hq i hi hiq
    obtain ⟨Z₁', hZ₁', hZ₁'range⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hZ
      (Set.range (pointsMap B S hS _ Z₁.ι) ∩ Set.range (pointsMap B S hS _ v))
      ((isOpen_range_pointsMap_of_isOpenImmersion B S hS Z₁.ι hZ₁.2).inter
        (isOpen_range_pointsMap_of_isEtale B S hS v hV hZ hv))
    have hle : Z₁' ≤ Z₁ :=
      le_of_range_pointsMap_ι_subset B S hS hZ₁ (hZ₁'range ▸ Set.inter_subset_left)
    obtain ⟨z₁, hz₁⟩ : z ∈ Set.range (pointsMap B S hS _ Z₁'.ι) := by
      rw [hZ₁'range]
      exact ⟨hzZ₁, hzv⟩
    set Y₁ := Z₁'.preimage p with hY₁def
    set p₁ := Z₁'.fromPreimage p with hp₁def
    have hsq : IsPullback p₁ Y₁.ι Z₁'.ι p := Subfunctor.isPullback_preimage p Z₁'
    have hY₁ : IsOpenSubspace B S hS Y₁ := isOpenSubspace_preimage B S hS p Z₁' hZ hY hZ₁'
    have hp₁fin : IsFinite B S hS p₁ := by
      have hk : IsPullback (pullback.lift Y₁.ι (p₁ ≫ Subfunctor.homOfLe hle)
          (by rw [Category.assoc, Subfunctor.homOfLe_ι, hsq.w]))
          p₁ (pullback.snd p Z₁.ι) (Subfunctor.homOfLe hle) :=
        IsPullback.of_right (by rw [pullback.lift_fst, Subfunctor.homOfLe_ι]; exact hsq.flip)
          (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p Z₁.ι)
      exact isFinite_of_isPullback B S hS hk hfin₁
    have hp₁surj : IsSurjective B S hS p₁ := by
      intro z'
      have hmem : pointsMap B S hS _ Z₁'.ι z' ∈
          Set.range (pointsMap B S hS _ Z₁.ι) ∩ Set.range (pointsMap B S hS _ v) := by
        rw [← hZ₁'range]
        exact ⟨z', rfl⟩
      obtain ⟨a, ha⟩ := hmem.2
      obtain ⟨y₁, hy₁, -⟩ := exists_point_of_isPullback_presheaf B S hS hsq z'
        (pointsMap B S hS _ j a) (by rw [← pointsMap_comp_apply, hjp, ha])
      exact ⟨y₁, hy₁⟩
    -- every point of `Y` over `z` lies in a representable open subspace
    obtain ⟨Z₂, hZ₂, hz₁Z₂, hrep₂⟩ :=
      exists_isOpenSubspace_isRepresentable_pullback_of_isFinite B S hS hY₁.1 hZ₁'.1 p₁ hp₁fin
        z₁ (by
          intro y₁ hy₁
          have hpy : pointsMap B S hS _ p (pointsMap B S hS _ Y₁.ι y₁) = z := by
            rw [← pointsMap_comp_apply, ← hsq.w, pointsMap_comp_apply, hy₁, hz₁]
          suffices h : ∃ G : Subfunctor Vb.toFunctor, IsOpenSubspace B S hS G ∧
              G.toFunctor.IsRepresentable ∧
                pointsMap B S hS _ Y₁.ι y₁ ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) by
            obtain ⟨G, hG, hGrep, hyG⟩ := h
            refine ⟨G.preimage Y₁.ι, isOpenSubspace_preimage B S hS Y₁.ι G hY hY₁.1 hG,
              hpre hY Y₁ hY₁ G hG hGrep, ?_⟩
            rw [pointsRange_preimage]
            exact hyG
          by_cases hyj : pointsMap B S hS _ Y₁.ι y₁ ∈ Set.range (pointsMap B S hS _ j)
          · obtain ⟨a, ha⟩ := hyj
            have : IsIso (Subfunctor.toRange j) := hiso
            refine ⟨Subfunctor.range j, hrange,
              isRepresentable_of_natIso _ (asIso (Subfunctor.toRange j)),
              pointsMap B S hS _ (Subfunctor.toRange j) a, ?_⟩
            rw [← pointsMap_comp_apply, Subfunctor.toRange_ι, ha]
          · -- the chart of one lower degree on the scheme-theoretic image `Y` of `V` in `Q`
            obtain ⟨W, hWc, w, Q', hQ', q', i', hw, hq', hq'r, hi', hi'q, hcov, hdrop⟩ :=
              exists_chart_of_complement_graph B S hS hZ hsep V hVc v hv hQ q hq hqr i hi hiq
            have hyw := hcov _ hyj (hpy ▸ hzv)
            have hdimy : localRingDimension B S hS (pointsMap B S hS _ Y₁.ι y₁) ≤ 1 := by
              have h1 := localRingDimension_le_of_isLocallyQuasiFinite B S hS hY₁.1 hZ₁'.1 p₁
                (isLocallyQuasiFinite_of_isFinite B S hS hY₁.1 hZ₁'.1 hp₁fin) y₁
              have h2 := localRingDimension_pointsMap_of_etale B S hS hY₁.1 hY Y₁.ι
                (isEtale_of_isOpenImmersion B S hS hY₁.2) y₁
              have h3 := localRingDimension_pointsMap_of_etale B S hS hZ₁'.1 hZ Z₁'.ι
                (isEtale_of_isOpenImmersion B S hS hZ₁'.2) z₁
              rw [hz₁] at h3
              rw [hy₁] at h1
              rw [h2]
              exact h1.trans (h3 ▸ hdim)
            obtain ⟨G, hG, hGrep, -, hyG⟩ := ih hY hYsep hYnoeth _ hdimy W hWc w hw hyw hQ' q'
              hq' hq'r i' hi' hi'q (hdrop d hrank)
            exact ⟨G, hG, hGrep, hyG⟩)
    -- over `Z₂`, a finite surjective morphism from a scheme
    set ι₂ := Z₂.ι ≫ Z₁'.ι with hι₂def
    have hι₂ : IsOpenImmersion B S hS ι₂ := isOpenImmersion_comp B S hS _ _ hZ₂.2 hZ₁'.2
    obtain ⟨hsep₂, hnoeth₂⟩ :=
      isAbsolutelySeparated_and_hasEtaleLocalProperty_of_isOpenImmersion B S hS hZ₂.1 hZ ι₂
        hι₂ hsep hnoeth
    obtain ⟨z₂, hz₂⟩ := hz₁Z₂
    have hdim₂ : localRingDimension B S hS z₂ ≤ 1 := by
      rw [← localRingDimension_pointsMap_of_etale B S hS hZ₂.1 hZ ι₂
        (isEtale_of_isOpenImmersion B S hS hι₂) z₂, hι₂def, pointsMap_comp_apply, hz₂, hz₁]
      exact hdim
    have := hrep₂
    set e := (pullback p₁ Z₂.ι).reprW with he
    have hgpb : IsPullback (e.hom ≫ pullback.fst p₁ Z₂.ι) (e.hom ≫ pullback.snd p₁ Z₂.ι)
        p₁ Z₂.ι :=
      IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ e rfl rfl
    have hgfin : IsFinite B S hS (e.hom ≫ pullback.snd p₁ Z₂.ι) :=
      isFinite_of_isPullback B S hS hgpb hp₁fin
    have hgsurj : IsSurjective B S hS (e.hom ≫ pullback.snd p₁ Z₂.ι) :=
      isSurjective_comp B S hS (isSurjective_of_isIso B S hS e.hom)
        (isSurjective_pullback_snd B S hS hY₁.1 hZ₁'.1 hZ₂.1 p₁ Z₂.ι hp₁surj)
    -- Stacks 0ADE, Steps 1 to 5: `z₂` lies in an open subspace `H` of `Z₂` which is affine
    obtain ⟨H, hH, hHaff, hz₂H⟩ := hstep hZ₂.1 hsep₂ hnoeth₂ _ _ hgfin hgsurj z₂ hdim₂
    -- back to `Z`
    obtain ⟨K₁, hK₁, hK₁aff, hK₁range⟩ :=
      exists_isOpenSubspace_isAffineSpace_of_isOpenSubspace B S hS hZ₂ hH hHaff
    obtain ⟨K₀, hK₀, hK₀aff, hK₀range⟩ :=
      exists_isOpenSubspace_isAffineSpace_of_isOpenSubspace B S hS hZ₁' hK₁ hK₁aff
    refine ⟨K₀, hK₀, hrep hK₀aff, hK₀aff, ?_⟩
    obtain ⟨h₀, hh₀⟩ := hz₂H
    have hz₁K₁ : z₁ ∈ Set.range (pointsMap B S hS K₁.toFunctor K₁.ι) := by
      rw [hK₁range, ← hz₂, ← hh₀]
      exact ⟨h₀, pointsMap_comp_apply B S hS _ _ _⟩
    obtain ⟨k₁, hk₁⟩ := hz₁K₁
    rw [hK₀range, ← hz₁, ← hk₁]
    exact ⟨k₁, pointsMap_comp_apply B S hS _ _ _⟩

/-- **Stacks 0ADE.**  Let `X` be an algebraic space over `S` which is separated and locally
Noetherian, and let `x ∈ |X|` be a point whose local ring has dimension at most one
(Stacks 04NA).  Then there is an open subspace of `X` containing `x` which is a scheme, that is,
whose functor of points is representable; the route of the remark makes it an affine scheme,
which is recorded as well.

This is the statement of Stacks 0ADD, proved along the route of the remark Stacks 0ADE, which
avoids More on Groupoids, Lemma 0ABI: the finite surjective cover by a scheme near `x` comes
from the induction on the degree of an affine étale chart through `x`
(`exists_isOpenSubspace_isRepresentable_of_chart_rank_le_of_fittingBlowups`), and the
remark's Steps 1 to 5 — reduction, flattening by blowing up Fitting ideals (Stacks 0D0Q), the
finite flat quotient of Stacks 07S6 with Stacks 09NN, the affine open with saturated principal
trace via Stacks 0ADC and 09NN, and Stacks 07VP — turn it into an open subspace which is a scheme.
-/
@[stacks 0ADE "Lemma 0ADD proved along the route of the remark, avoiding Stacks 0ABI"]
theorem exists_isOpenSubspace_isRepresentable_of_localRingDimension_le_one_of_fittingBlowups
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsAbsolutelySeparated B S hS B.contains_terminal X)
    (hnoeth : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (x : points B S hS X) (hdim : localRingDimension B S hS x ≤ 1) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      IsAffineSpace B S hS G.toFunctor ∧ x ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) := by
  -- an affine étale chart through `x`, and its open image `Z₀`
  obtain ⟨V, c, hVaff, hcEt, hxc⟩ :=
    exists_affine_etale_chart_of_isCompact B S hS X hX (isCompact_singleton (x := x))
  have hc : IsEtale B S hS c := (isEtale_iff_presheaf_of_yoneda B S hS c).2 hcEt
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  obtain ⟨Z₀, hZ₀, hZ₀range⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hX _
    (isOpen_range_pointsMap_of_isEtale B S hS c hV hX hc)
  obtain ⟨c₀, hc₀⟩ :=
    (factorsThrough_openSubspace_iff_points B S hS hX hV Z₀ hZ₀ c).2 hZ₀range.symm.subset
  have hc₀et : IsEtale B S hS c₀ := isEtale_of_comp_mono B S hS c₀ Z₀.ι (hc₀ ▸ hc)
  obtain ⟨hsep₀, hnoeth₀⟩ :=
    isAbsolutelySeparated_and_hasEtaleLocalProperty_of_isOpenImmersion B S hS hZ₀.1 hX Z₀.ι
      hZ₀.2 hsep hnoeth
  have hc₀surj : IsSurjective B S hS c₀ := by
    intro z'
    have hmem : pointsMap B S hS _ Z₀.ι z' ∈ Set.range (pointsMap B S hS _ c) := by
      rw [← hZ₀range]
      exact ⟨z', rfl⟩
    obtain ⟨a, ha⟩ := hmem
    refine ⟨a, pointsMap_injective_of_mono B S hS Z₀.ι ?_⟩
    rw [← pointsMap_comp_apply, hc₀, ha]
  have hVc : CompactSpace ((BigFppfOver.toScheme B S hS).obj V) := inferInstance
  have hqc₀ : IsQuasiCompactSpace B S hS Z₀.toFunctor :=
    isQuasiCompactSpace_of_isSurjective B S hS hV hZ₀.1 c₀ hc₀surj
      (isQuasiCompactSpace_yoneda B S hS V hVc)
  obtain ⟨x₀, hx₀⟩ : x ∈ Set.range (pointsMap B S hS _ Z₀.ι) := by
    rw [hZ₀range]
    exact hxc (Set.mem_singleton x)
  have hdim₀ : localRingDimension B S hS x₀ ≤ 1 := by
    rw [← localRingDimension_pointsMap_of_etale B S hS hZ₀.1 hX Z₀.ι
      (isEtale_of_isOpenImmersion B S hS hZ₀.2) x₀, hx₀]
    exact hdim
  -- the embedding in a proper representable morphism, and the bound on the degree
  obtain ⟨Q, hQ, q, i, hq, hqr, hi, hiq⟩ :=
    exists_isImmersion_isProper_of_isEtale_of_isAffine B S hS hZ₀.1 hqc₀ hsep₀ V hVaff c₀ hc₀et
  have hR : IsReasonableSpace B S hS Z₀.toFunctor :=
    isReasonableSpace_of_isVeryReasonableSpace B S hS _ hZ₀.1
      (isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated B S hS
        B.contains_terminal _ hZ₀.1
        (isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated B S hS _
          B.contains_terminal hZ₀.1
          (isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS B.contains_terminal _
            hsep₀)))
  obtain ⟨d, -, -, -, -, -, hfib⟩ := exists_minimalDegreeOpen_and_fibre_le_degree B S hS
    Z₀.toFunctor V c₀ hZ₀.1 hR hVaff hc₀et
    (isSeparated_of_isEtale_of_scheme_isSeparated B S hS _ hZ₀.1 V inferInstance c₀ hc₀et) ⟨x₀⟩
  obtain ⟨a, ha⟩ := hc₀surj x₀
  obtain ⟨G₀, hG₀, -, hG₀aff, g₀, hg₀⟩ :=
    exists_isOpenSubspace_isRepresentable_of_chart_rank_le_of_fittingBlowups B S hS d hZ₀.1 hsep₀
      hnoeth₀ x₀ hdim₀ V hVc c₀ hc₀et ⟨a, ha⟩ hQ q hq hqr i hi hiq
      (fun K hK T eT ξ Vf q' i' hpb _ => hfib K hK T eT ξ Vf q' i' hpb)
  obtain ⟨K, hK, hKaff, hKrange⟩ :=
    exists_isOpenSubspace_isAffineSpace_of_isOpenSubspace B S hS hZ₀ hG₀ hG₀aff
  obtain ⟨T, hTaff, ⟨eT⟩⟩ := hKaff
  refine ⟨K, hK, isRepresentable_of_natIso _ eT.symm, ⟨T, hTaff, ⟨eT⟩⟩, ?_⟩
  rw [hKrange, ← hx₀, ← hg₀]
  exact ⟨g₀, pointsMap_comp_apply B S hS _ _ _⟩

end AlgebraicGeometry.Space

end
