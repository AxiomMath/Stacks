module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtCompactSet
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FiniteLocallyFreePushPull
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionOneChartInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionOneFiniteAffineNeighbourhood
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
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSurjectiveAffineSource
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae

/-!
# Separated algebraic spaces are schemes in codimension one

This file proves [Stacks, Tag 0ADD]:

> Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `x ∈ |X|`. If `X` is
> separated, locally Noetherian, and the dimension of the local ring of `X` at `x` is `≤ 1`
> (Properties of Spaces, Definition 04NA), then there exists an open subspace of `X` containing
> `x` which is a scheme.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_chart_rank_le`: the
  induction on the degree of an étale chart which produces the scheme neighbourhood.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_localRingDimension_le_one`:
  **Stacks 0ADD**.

## The route

The source shrinks `X` to a quasi-compact neighbourhood of `x`, takes a finite surjective
morphism `U ⟶ X` from a scheme ([Stacks, Tag 09YC]), uses [Stacks, Tag 0ABI] on the groupoid
`U ×_X U` to find an open `H ∋ x` with a finite surjective morphism from an affine scheme, and
concludes by [Stacks, Tag 07VP] that `H` is affine.

Here the finite surjective cover is produced only near `x`, and by a different argument. Shrink
`X` to the image `Z` of an affine étale chart `v : V ⟶ Z` through `x`; `Z` is quasi-compact, and
`V` is immersed over `Z` in a proper representable `Q ⟶ Z` (the product with a projective space,
`AlgebraicGeometry.Space.exists_isImmersion_isProper_of_isEtale_of_isAffine`). The fibres of `v`
at the field-valued points have degree bounded by some `d`
(`AlgebraicGeometry.Space.exists_minimalDegreeOpen_and_fibre_le_degree`). One then proves, by
induction on `d`, that the point `z` lies in an open subspace which is a scheme:

* For `d = 0` the chart has empty image
  (`AlgebraicGeometry.Space.notMem_range_pointsMap_of_chartRankAtCodimZeroLE_zero`).
* For `d + 1`, let `Y` be the scheme-theoretic image of `V` in `Q`, a proper space over `Z` in
  which `V` is a dense open (Stacks 088G). By [Stacks, Tag 0AD2] `Y` is finite over an open
  `Z₁ ∋ z`, which we take inside the image of `v`. A point of `Y` over `z` either lies in `V`, or
  lies on the boundary; a boundary point is reached by an étale chart `W` of `Y` immersed in a
  proper representable `Q' ⟶ Y` and of degree at most `d`
  (`AlgebraicGeometry.Space.exists_chart_of_complement_graph`), and its local ring has dimension
  at most one because `Y` is finite over `Z₁`; by induction it lies in a scheme open subspace of
  `Y`. Hence `Y` is a scheme over an open `Z₂ ∋ z`
  (`AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_pullback_of_isFinite`), finite
  and surjective over `Z₂`. Now [Stacks, Tag 0ABI] (in the namespace `AlgebraicGeometry.Space`,
  `exists_isOpenSubspace_isFinite_isSurjective_affine_of_localRingDimension_le_one`) gives an
  open `H ∋ z` with a finite surjective morphism from an affine scheme, and `H` is
  Noetherian, so affine by [Stacks, Tag 07VP]
  (`AlgebraicGeometry.Space.isAffineSpace_of_isFinite_of_isSurjective`).

## References

* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 0AD2](https://stacks.math.columbia.edu/tag/0AD2)
* [Stacks Project, Tag 0ABI](https://stacks.math.columbia.edu/tag/0ABI)
* [Stacks Project, Tag 07VP](https://stacks.math.columbia.edu/tag/07VP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The source of an open immersion into a separated, locally Noetherian algebraic space is
separated and locally Noetherian. -/
private theorem isAbsolutelySeparated_and_isLocallyNoetherian_of_isOpenImmersion
    {F Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hZ : IsAlgebraicSpace B S hS Z) (f : F ⟶ Z) (hf : IsOpenImmersion B S hS f)
    (hsep : IsAbsolutelySeparated B S hS B.contains_terminal Z)
    (hnoeth : HasEtaleLocalProperty B S hS Z (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    IsAbsolutelySeparated B S hS B.contains_terminal F ∧
      HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  ⟨isAbsolutelySeparated_of_isSeparated B S hS B.contains_terminal hsep
      (isSeparated_of_mono f (mono_of_presheaf_isOpenImmersion hf)),
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hF hZ f
      (isLocallyOfFiniteType_of_isEtale B S hS hZ (isEtale_of_isOpenImmersion B S hS hf)) hnoeth⟩

/-- The trace of a representable open subspace of `Z` on an open subspace `U ⊆ Z` is
representable. -/
private theorem isRepresentable_preimage_ι_of_isOpenSubspace
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (U : Subfunctor Z) (hU : IsOpenSubspace B S hS U)
    (G : Subfunctor Z) (hG : IsOpenSubspace B S hS G) (hGrep : G.toFunctor.IsRepresentable) :
    (G.preimage U.ι).toFunctor.IsRepresentable := by
  have hP : IsOpenSubspace B S hS (G.preimage U.ι) :=
    isOpenSubspace_preimage B S hS U.ι G hZ hU.1 hG
  have hle : Subfunctor.range ((G.preimage U.ι).ι ≫ U.ι) ≤ G := by
    rintro T _ ⟨a, rfl⟩
    exact a.2
  have := isRepresentable_of_le_of_isRepresentable B S hS
    (isOpenSubspace_range_ι_comp B S hS U hU _ hP) hle hGrep
  exact isRepresentable_of_natIso _ (asIso (Subfunctor.toRange ((G.preimage U.ι).ι ≫ U.ι))).symm

/-- The local ring dimension bound `≤ 1` descends along an open immersion. -/
private theorem localRingDimension_le_one_of_isOpenImmersion
    {F Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hZ : IsAlgebraicSpace B S hS Z) (f : F ⟶ Z) (hf : IsOpenImmersion B S hS f)
    {x : points B S hS F} {z : points B S hS Z} (hxz : pointsMap B S hS _ f x = z)
    (hdim : localRingDimension B S hS z ≤ 1) : localRingDimension B S hS x ≤ 1 := by
  rw [← localRingDimension_pointsMap_of_etale B S hS hF hZ f (isEtale_of_isOpenImmersion B S hS hf)
    x, hxz]
  exact hdim

/-- A point lying over a point in the image of `α` lies in the image of `α ≫ β`. -/
private theorem mem_range_pointsMap_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (α : F ⟶ G) (β : G ⟶ H)
    {x : points B S hS F} {y : points B S hS G} {z : points B S hS H}
    (hxy : pointsMap B S hS _ α x = y) (hyz : pointsMap B S hS _ β y = z) :
    z ∈ Set.range (pointsMap B S hS _ (α ≫ β)) :=
  ⟨x, by rw [pointsMap_comp_apply, hxy, hyz]⟩

/-- **The induction on the degree of the chart in the proof of Stacks 0ADD.** Let `Z` be a
separated, locally Noetherian algebraic space over `S` and `z ∈ |Z|` a point whose local ring
has dimension at most one. Let `v : V ⟶ Z` be an étale chart with quasi-compact source whose
image contains `z`, immersed by `i` over `Z` in a proper representable morphism `q : Q ⟶ Z`, and
whose fibres at the codimension-zero field-valued points have degree at most `d`. Then `z` lies
in an open subspace of `Z` which is a scheme.

For `d = 0` the image of `v` is empty. For `d + 1`, the scheme-theoretic image `Y` of `V` in `Q`
is finite over an open `Z₁ ∋ z` inside the image of `v` (Stacks 0AD2); the points of `Y` over
`z` lie in the open `V ⊆ Y` or are reached by the complement-of-the-graph chart of degree `d`,
to which the induction hypothesis applies; so `Y` is a scheme over an open `Z₂ ∋ z`, finite and
surjective over it. Stacks 0ABI then gives an open `H ∋ z` and a finite surjective morphism to
`H` from an affine scheme, and `H` is affine by Stacks 07VP. -/
theorem exists_isOpenSubspace_isRepresentable_of_chart_rank_le (d : ℕ) :
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
        z ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) := by
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
              isRepresentable_preimage_ι_of_isOpenSubspace B S hS hY Y₁ hY₁ G hG hGrep, ?_⟩
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
              have hdim₁ := localRingDimension_le_one_of_isOpenImmersion B S hS hZ₁'.1 hZ Z₁'.ι
                hZ₁'.2 hz₁ hdim
              have h1 := localRingDimension_le_of_isLocallyQuasiFinite B S hS hY₁.1 hZ₁'.1 p₁
                (isLocallyQuasiFinite_of_isFinite B S hS hY₁.1 hZ₁'.1 hp₁fin) y₁
              have h2 := localRingDimension_pointsMap_of_etale B S hS hY₁.1 hY Y₁.ι
                (isEtale_of_isOpenImmersion B S hS hY₁.2) y₁
              rw [hy₁] at h1
              rw [h2]
              exact h1.trans hdim₁
            exact ih hY hYsep hYnoeth _ hdimy W hWc w hw hyw hQ' q' hq' hq'r i' hi' hi'q
              (hdrop d hrank))
    -- over `Z₂`, a finite surjective morphism from a scheme
    set ι₂ := Z₂.ι ≫ Z₁'.ι with hι₂def
    have hι₂ : IsOpenImmersion B S hS ι₂ := isOpenImmersion_comp B S hS _ _ hZ₂.2 hZ₁'.2
    obtain ⟨hsep₂, hnoeth₂⟩ :=
      isAbsolutelySeparated_and_isLocallyNoetherian_of_isOpenImmersion B S hS hZ₂.1 hZ ι₂ hι₂
        hsep hnoeth
    obtain ⟨z₂, hz₂⟩ := hz₁Z₂
    have hdim₂ : localRingDimension B S hS z₂ ≤ 1 :=
      localRingDimension_le_one_of_isOpenImmersion B S hS hZ₂.1 hZ ι₂ hι₂
        (by rw [hι₂def, pointsMap_comp_apply, hz₂, hz₁]) hdim
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
    -- Stacks 0ABI: an open `H ∋ z` with a finite surjective morphism from an affine scheme
    obtain ⟨H, W', t, hH, hz₂H, hW'aff, htfin, htsurj⟩ :=
      exists_isOpenSubspace_isFinite_isSurjective_affine_of_localRingDimension_le_one B S hS
        hZ₂.1 hsep₂ hnoeth₂ _ _ hgfin hgsurj z₂ hdim₂
    -- Stacks 07VP: `H` is Noetherian, hence affine
    have hι₃ : IsOpenImmersion B S hS (H.ι ≫ ι₂) := isOpenImmersion_comp B S hS _ _ hH.2 hι₂
    obtain ⟨hsep₃, hnoeth₃⟩ :=
      isAbsolutelySeparated_and_isLocallyNoetherian_of_isOpenImmersion B S hS hH.1 hZ _ hι₃
        hsep hnoeth
    have hW' : IsAlgebraicSpace B S hS (yoneda.obj W') := isAlgebraicSpace_yoneda B S hS W'
    have hqc₃ : IsQuasiCompactSpace B S hS H.toFunctor :=
      isQuasiCompactSpace_of_isSurjective B S hS hW' hH.1 t htsurj
        (isQuasiCompactSpace_yoneda B S hS W' inferInstance)
    obtain ⟨T, -, ⟨eT⟩⟩ := isAffineSpace_of_isFinite_of_isSurjective B S hS B.contains_terminal
      ⟨H.toFunctor, hH.1⟩ ⟨yoneda.obj W', hW'⟩ (ObjectProperty.homMk t) htfin htsurj
      (isAffineSpace_yoneda B S hS W' hW'aff)
      ⟨hqc₃, isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS B.contains_terminal _
        hsep₃, hnoeth₃⟩
    have hHrep : H.toFunctor.IsRepresentable := isRepresentable_of_natIso _ eT.symm
    -- back to `Z`
    obtain ⟨K₁, hK₁, hK₁rep, hK₁range⟩ :=
      exists_isOpenSubspace_isRepresentable_of_isOpenSubspace B S hS hZ₁'.1 hZ₂ hH hHrep
    obtain ⟨K₀, hK₀, hK₀rep, hK₀range⟩ :=
      exists_isOpenSubspace_isRepresentable_of_isOpenSubspace B S hS hZ hZ₁' hK₁ hK₁rep
    refine ⟨K₀, hK₀, hK₀rep, ?_⟩
    obtain ⟨h₀, hh₀⟩ := hz₂H
    obtain ⟨k₁, hk₁⟩ : z₁ ∈ Set.range (pointsMap B S hS K₁.toFunctor K₁.ι) := by
      rw [hK₁range]
      exact mem_range_pointsMap_comp B S hS _ _ hh₀ hz₂
    rw [hK₀range]
    exact mem_range_pointsMap_comp B S hS _ _ hk₁ hz₁

/-- **Stacks 0ADD.** Let `X` be an algebraic space over `S` which is separated and locally
Noetherian, and let `x ∈ |X|` be a point whose local ring has dimension at most one
(Stacks 04NA). Then there is an open subspace of `X` containing `x` which is a scheme, that
is, whose functor of points is representable.

An affine étale chart `V ⟶ X` through `x` has open image `Z₀`, which is quasi-compact,
separated and locally Noetherian; `V` is immersed over `Z₀` in a proper representable morphism,
the fibres of `V ⟶ Z₀` at field-valued points have bounded degree, and
`AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_chart_rank_le` applies. -/
@[stacks 0ADD]
theorem exists_isOpenSubspace_isRepresentable_of_localRingDimension_le_one
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsAbsolutelySeparated B S hS B.contains_terminal X)
    (hnoeth : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (x : points B S hS X) (hdim : localRingDimension B S hS x ≤ 1) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      x ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) := by
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
    isAbsolutelySeparated_and_isLocallyNoetherian_of_isOpenImmersion B S hS hZ₀.1 hX Z₀.ι hZ₀.2
      hsep hnoeth
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
  have hdim₀ : localRingDimension B S hS x₀ ≤ 1 :=
    localRingDimension_le_one_of_isOpenImmersion B S hS hZ₀.1 hX Z₀.ι hZ₀.2 hx₀ hdim
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
  obtain ⟨G₀, hG₀, hG₀rep, g₀, hg₀⟩ :=
    exists_isOpenSubspace_isRepresentable_of_chart_rank_le B S hS d hZ₀.1 hsep₀ hnoeth₀ x₀
      hdim₀ V hVc c₀ hc₀et ⟨a, ha⟩ hQ q hq hqr i hi hiq
      (fun K hK T eT ξ Vf q' i' hpb _ => hfib K hK T eT ξ Vf q' i' hpb)
  obtain ⟨K, hK, hKrep, hKrange⟩ :=
    exists_isOpenSubspace_isRepresentable_of_isOpenSubspace B S hS hX hZ₀ hG₀ hG₀rep
  refine ⟨K, hK, hKrep, ?_⟩
  rw [hKrange]
  exact mem_range_pointsMap_comp B S hS _ _ hg₀ hx₀

end AlgebraicGeometry.Space
