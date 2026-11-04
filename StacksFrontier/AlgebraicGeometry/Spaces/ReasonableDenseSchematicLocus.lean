module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ImageRepresentableInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Reasonable
public import StacksFrontier.CategoryTheory.PullbackCancelMono

/-!
# The reasonable case of the density of the schematic locus

Tag 03JI, Proposition 68.10.1, says that a *reasonable* algebraic space over a scheme `S`
contains a dense open subspace which is a scheme. This file reduces that proposition to the
degree induction which is the whole content of the source's proof, and proves everything
around that induction.

Three things are proved here, none of which was available.

* Reasonableness passes to open subspaces. This is not an instance of Tag 03JX — it is
  proved directly from the formulation `AlgebraicGeometry.Space.IsReasonableSpace` the
  library uses, condition (2) of Tag 03JT, and it is what lets the source's reduction "the
  question is local on `X`" be carried out.
* An open-subspace-and-representable-and-nonempty subspace of an open subspace of `X` is
  transported to one of `X` itself, below the given open subspace. This is the bookkeeping
  the two localization steps need.
* The localization steps themselves: from the *absolute* statement that every nonempty
  reasonable algebraic space has a nonempty representable open subspace, the hypothesis
  `hnonempty` of
  `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_isAlgebraicSpace`
  follows and Tag 03JI's conclusion follows; and that absolute statement in turn follows from
  the same statement for a space carrying *one affine étale chart surjective on points with
  universally bounded fibres*, which is the situation the source's induction starts from.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isReasonableSpace_of_isOpenSubspace`: an open subspace of a
  reasonable algebraic space over `S` is reasonable.
* `AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_le_of_isOpenSubspace`: a
  nonempty representable open subspace of an open subspace `G` of `X` is the point set of a
  nonempty representable open subspace of `X` contained in `G`.
* `AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_le_of_core`: the hypothesis
  `hnonempty` of Tag 086U's reduction, for a reasonable algebraic space, from the absolute
  core statement.
* `AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_of_chartCore`: the absolute
  core statement from the affine-chart core statement.
* `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_core` and
  `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_chartCore`:
  the conclusion of Tag 03JI for a reasonable algebraic space over `S`, from the absolute
  core statement and from the affine-chart core statement respectively.

## Implementation notes

**Why Tag 03JI is not proved through Tag 086U.** Tag 086U, Rydh's theorem, says the same
thing for a *decent* space, and reasonable implies decent, so it is tempting to derive this
proposition from that theorem. That derivation is circular: the source's proof of Tag 086U
invokes Proposition 68.10.1 — this very tag — on the open subspace swept out by a chart whose
fibre degrees are bounded. The source proves Tag 03JI independently, by induction on a bound
for the fibre degrees of one affine chart, and the reduction here is to that induction.

**What is left.** The one hypothesis carried, in the style of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`, is `hchart`: a nonempty
algebraic space over `S` with an affine étale chart surjective on points and with universally
bounded fibres has a nonempty representable open subspace. That is the conclusion of the
source's induction on the bound.

**That induction is now proved, modulo Tag 07S8 alone**, in
`StacksFrontier.AlgebraicGeometry.Spaces.DegreeInductionSchematicLocus`: with `X_n` the open
complement of the `(n-1)`-st closed subspace of the stratification of Tag 07S8, either `X_n`
has a point, and then the chart is finite locally free of degree `n` over it so Tag 07S6 and
Tag 01ZY make `X_n` a scheme; or `X_n` has no point, and then the bound drops to `n - 1`. The
first branch is
`AlgebraicGeometry.Space.isRepresentable_of_surjectiveEtale_finiteLocallyFree_of_isImmersion`
in `StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatChartRepresentable`, and the induction is
`AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_of_bound_of_h07S8`. The only
result still owed is Tag 07S8, the degree stratification of a flat, locally finitely
presented, separated, locally quasi-finite morphism *from a scheme to an algebraic space* with
universally bounded fibres, whose own scheme-level input is Tag 07RY.

Tag 07S6 — a scheme with a finite locally free equivalence relation has a quotient scheme — is
proved, with the glueing of the local quotients, with the bare attribute as
`AlgebraicGeometry.Space.nonempty_finiteFlatQuotient_of_affineOrbits`
(`StacksFrontier/AlgebraicGeometry/Spaces/FiniteFlatQuotientCharts.lean`), under the source's own
conditions (1), (2) and (3) and with no site hypothesis.

**The density step is not the source's.** The source finishes by checking that
`X'' ∪ X_n` is dense. Here that is unnecessary: the reduction
`AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_isAlgebraicSpace`
in `StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus` already turns *local*
nonemptiness into global density through the schematic locus of Tag 03JH, so only the
nonemptiness statement is needed. That reduction carries no decency hypothesis, which is
exactly what makes it usable here.

**Transferring the fibre bound.** `AlgebraicGeometry.Space.HasUniversallyBoundedFibers`
specifies each fibre by a cartesian square of presheaves, so transferring it from `X` to an
open subspace `G` is the observation that a square over `X` whose two legs factor through the
monomorphism `G.ι` is already cartesian over `G`; that is
`AlgebraicGeometry.Space.hasUniversallyBoundedFibers_of_comp_mono`, and it is the only step
of the permanence of reasonableness which is not formal.

**Transporting an open subspace upwards.** An open subspace of an open subspace is *not*
literally a subfunctor of the ambient space, so it is transported by its point set: the image
of its point set is open, and the subspace
`AlgebraicGeometry.Space.openSubspaceOfPoints` cut out by that image is isomorphic to it by
`AlgebraicGeometry.Space.isIso_lift_range_pointsMap_of_isOpenImmersion`, hence
representable, and lies below the given open subspace by part (1) of Tag 03BZ in the form
`AlgebraicGeometry.Space.le_of_range_pointsMap_ι_subset`.

**Nothing here carries a Stacks attribute.** Every statement below either is a reduction
carrying `hchart`, or is an auxiliary permanence statement for which the source has no tag of
its own; Tag 03JI is not proved.

## References

* [Stacks Project, Tag 03JI](https://stacks.math.columbia.edu/tag/03JI)
* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 03JT](https://stacks.math.columbia.edu/tag/03JT)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 07S8](https://stacks.math.columbia.edu/tag/07S8)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Reasonableness of an open subspace -/

/-- A chart of a subfunctor `G` of `X` whose composite with the inclusion of `G` has
universally bounded fibres over `X`, in the sense of Tag 03JL, has universally bounded fibres
over `G`, with the same bound.

Each fibre over a field-valued point of `G` is computed by the same cartesian square as the
fibre over the corresponding field-valued point of `X`, because both legs of that square
factor through the monomorphism `G.ι`. -/
theorem hasUniversallyBoundedFibers_of_comp_mono
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {G : Subfunctor X} {U : BigFppfOver B S hS}
    {φ : yoneda.obj U ⟶ G.toFunctor}
    (h : HasUniversallyBoundedFibers B S hS U (φ ≫ G.ι)) :
    HasUniversallyBoundedFibers B S hS U φ := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, fun k _ T e ξ => ?_⟩
  obtain ⟨V, p, i, r, hr, hflf, hpb⟩ := hn k T e (ξ ≫ G.ι)
  exact ⟨V, p, i, r, hr, hflf, isPullback_of_comp_mono G.ι hpb⟩

/-- An open subspace of a reasonable algebraic space over `S` is reasonable.

An affine étale chart of the open subspace becomes an affine étale chart of the ambient space
after composition with the inclusion, since an open immersion is étale and étale charts
compose; the resulting bound on its fibres over the ambient space is a bound on its fibres
over the open subspace by
`AlgebraicGeometry.Space.hasUniversallyBoundedFibers_of_comp_mono`.

This is the permanence which licenses the source's reduction of Tag 03JI to the case of a
space with one affine chart. It is *not* obtained from Tag 03JX: it is proved directly from
condition (2) of Tag 03JT, which is the formulation
`AlgebraicGeometry.Space.IsReasonableSpace` uses. -/
theorem isReasonableSpace_of_isOpenSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsReasonableSpace B S hS X)
    {G : Subfunctor X} (hG : IsOpenSubspace B S hS G) :
    IsReasonableSpace B S hS G.toFunctor := by
  have hmul := isMultiplicative_presheaf_etale B S hS
  intro U hU φ hφ
  refine hasUniversallyBoundedFibers_of_comp_mono B S hS (hX U hU (φ ≫ G.ι) ?_)
  exact MorphismProperty.comp_mem _ φ G.ι hφ (presheaf_etale_of_isOpenImmersion B S hS hG.2)

/-! ### Transporting a representable open subspace upwards -/

/-- A nonempty representable open subspace `H'` of an open subspace `G` of an algebraic space
`X` over `S` gives a nonempty representable open subspace of `X` contained in `G`.

The subspace of `X` is the one cut out by the image of the point set of `H'`, which is open
because `H'.ι ≫ G.ι` is an open immersion. It is isomorphic to `H'` by
`AlgebraicGeometry.Space.isIso_lift_range_pointsMap_of_isOpenImmersion`, hence
representable; its point set is that image, hence nonempty; and it lies below `G` because its
point set is contained in the point set of `G`, which is part (1) of Tag 03BZ in the form
`AlgebraicGeometry.Space.le_of_range_pointsMap_ι_subset`. -/
theorem exists_isRepresentable_isOpenSubspace_le_of_isOpenSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {G : Subfunctor X} (hG : IsOpenSubspace B S hS G)
    {H' : Subfunctor G.toFunctor} (hH'open : IsOpenSubspace B S hS H')
    (hH'rep : H'.toFunctor.IsRepresentable)
    (hH'ne : (Set.range (pointsMap B S hS H'.toFunctor H'.ι)).Nonempty) :
    ∃ H : Subfunctor X, H ≤ G ∧ IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
      (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty := by
  set P := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS) with hP
  have _hP1 : P.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage (BigFppfOver.toScheme B S hS)
  have _hP2 : P.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition P
  have hcomp : IsOpenImmersion B S hS (H'.ι ≫ G.ι) :=
    MorphismProperty.comp_mem _ _ _ hH'open.2 hG.2
  set W := Set.range (pointsMap B S hS H'.toFunctor (H'.ι ≫ G.ι)) with hW
  have hWopen : IsOpen W := isOpen_range_pointsMap_of_isOpenImmersion B S hS _ hcomp
  refine ⟨openSubspaceOfPoints B S hS X W, ?_,
    isOpenSubspace_openSubspaceOfPoints B S hS hX W hWopen, ?_, ?_⟩
  · refine le_of_range_pointsMap_ι_subset B S hS hG ?_
    rw [range_pointsMap_ι_openSubspaceOfPoints B S hS W, hW, pointsMap_comp]
    exact Set.range_comp_subset_range _ _
  · have := isIso_lift_range_pointsMap_of_isOpenImmersion B S hS hG.2 hH'open
    exact CategoryTheory.isRepresentable_of_natIso _
      (asIso (Subfunctor.lift (H'.ι ≫ G.ι)
        (range_le_openSubspaceOfPoints_range_pointsMap (H'.ι ≫ G.ι))))
  · rw [range_pointsMap_ι_openSubspaceOfPoints B S hS W, hW]
    exact Set.range_nonempty_iff_nonempty.mpr (Set.range_nonempty_iff_nonempty.mp hH'ne)

/-! ### From the absolute core statement to Tag 03JI -/

/-- **The hypothesis `hnonempty` of Tag 086U's reduction, for a reasonable algebraic space.**

Assume the absolute statement `hcore` that every nonempty reasonable algebraic space over `S`
has a nonempty representable open subspace. Then every nonempty open subspace of a reasonable
algebraic space over `S` contains a nonempty representable open subspace.

An open subspace is itself a reasonable algebraic space by
`AlgebraicGeometry.Space.isReasonableSpace_of_isOpenSubspace`, so `hcore` applies to it, and
the resulting subspace is transported upwards by
`AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_le_of_isOpenSubspace`. -/
theorem exists_isRepresentable_isOpenSubspace_le_of_core
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hr : IsReasonableSpace B S hS X)
    (hcore : ∀ Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS Y →
      IsReasonableSpace B S hS Y → Nonempty (points B S hS Y) →
      ∃ H : Subfunctor Y, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty)
    (G : Subfunctor X) (hG : IsOpenSubspace B S hS G)
    (hGne : (Set.range (pointsMap B S hS G.toFunctor G.ι)).Nonempty) :
    ∃ H : Subfunctor X, H ≤ G ∧ IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
      (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty := by
  obtain ⟨H', hH'open, hH'rep, hH'ne⟩ := hcore G.toFunctor hG.1
    (isReasonableSpace_of_isOpenSubspace B S hS hr hG)
    (Set.range_nonempty_iff_nonempty.mp hGne)
  exact exists_isRepresentable_isOpenSubspace_le_of_isOpenSubspace B S hS hX hG hH'open
    hH'rep hH'ne

/-- **Tag 03JI from the absolute core statement.** A reasonable algebraic space over `S` has
a representable open subspace whose point set is dense, as soon as every nonempty reasonable
algebraic space over `S` has a nonempty representable open subspace.

The passage from local nonemptiness to global density is
`AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_isAlgebraicSpace`,
which realizes the dense open subspace as the schematic locus of Tag 03JH and assumes no
decency; the open subspace produced here is therefore the schematic locus of `X`. -/
theorem exists_denseRange_isRepresentable_isOpenSubspace_of_core
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hr : IsReasonableSpace B S hS X)
    (hcore : ∀ Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS Y →
      IsReasonableSpace B S hS Y → Nonempty (points B S hS Y) →
      ∃ H : Subfunctor Y, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      DenseRange (pointsMap B S hS G.toFunctor G.ι) :=
  exists_denseRange_isRepresentable_isOpenSubspace_of_isAlgebraicSpace B S hS hX
    (exists_isRepresentable_isOpenSubspace_le_of_core B S hS hX hr hcore)

/-! ### From the affine-chart core statement to the absolute one -/

/-- **The absolute core statement from the affine-chart core statement.**

Assume `hchart`: a nonempty algebraic space over `S` carrying an affine étale chart which is
surjective on points and has universally bounded fibres has a nonempty representable open
subspace. Then every nonempty reasonable algebraic space over `S` has a nonempty
representable open subspace.

This is the source's reduction "the question is local on `X`, so we may assume there is an
affine scheme `U` with a surjective étale map `U → X`". An affine étale chart through a chosen
point exists by Tag 03FX in the form
`AlgebraicGeometry.Space.exists_affine_etale_chart_at_point`; the open subspace `X'` of `X`
cut out by the image of its point set — open by Tag 03IR — receives that chart surjectively on
points, is reasonable by
`AlgebraicGeometry.Space.isReasonableSpace_of_isOpenSubspace`, and therefore bounds the fibres
of the lifted chart, the chart's source being affine. So `hchart` applies to `X'` and the
resulting subspace is transported upwards by
`AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_le_of_isOpenSubspace`. -/
theorem exists_isRepresentable_isOpenSubspace_of_chartCore
    (hchart : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (V : BigFppfOver B S hS)
      (b : yoneda.obj V ⟶ Y), IsAlgebraicSpace B S hS Y →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b →
      Function.Surjective (pointsMap B S hS (yoneda.obj V) b) →
      HasUniversallyBoundedFibers B S hS V b → Nonempty (points B S hS Y) →
      ∃ H : Subfunctor Y, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hr : IsReasonableSpace B S hS X) (hne : Nonempty (points B S hS X)) :
    ∃ H : Subfunctor X, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
      (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty := by
  obtain ⟨x⟩ := hne
  obtain ⟨V, b, hVaffine, hbetale, v, hv⟩ :=
    exists_affine_etale_chart_at_point B S hS X hX x
  -- The open subspace of `X` swept out by the chart.
  have _hE : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := (@Etale.{u} : MorphismProperty Scheme.{u}))
  have _hQ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hbEtale : IsEtale B S hS b := isEtale_of_presheaf_etale B S hS hbetale
  have hWopen : IsOpen (Set.range (pointsMap B S hS (yoneda.obj V) b)) :=
    isOpen_range_pointsMap_of_isEtale B S hS b (isAlgebraicSpace_yoneda B S hS V) hX hbEtale
  set G := openSubspaceOfPoints B S hS X (Set.range (pointsMap B S hS (yoneda.obj V) b))
    with hGdef
  have hG : IsOpenSubspace B S hS G :=
    isOpenSubspace_openSubspaceOfPoints B S hS hX _ hWopen
  have hGrange : Set.range (pointsMap B S hS G.toFunctor G.ι) =
      Set.range (pointsMap B S hS (yoneda.obj V) b) :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  -- The chart lifts to `G` and is surjective on its points.
  set b' := Subfunctor.lift b (range_le_openSubspaceOfPoints_range_pointsMap b) with hb'def
  have hb'ι : b' ≫ G.ι = b := Subfunctor.lift_ι _ _
  have hb'etale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b' :=
    MorphismProperty.presheaf_of_comp_mono _ (m := G.ι) (by rw [hb'ι]; exact hbetale)
  have hιinj : Function.Injective (pointsMap B S hS G.toFunctor G.ι) :=
    pointsMap_injective_of_mono B S hS G.ι
  have hb'surj : Function.Surjective (pointsMap B S hS (yoneda.obj V) b') := by
    intro y
    have hmem : pointsMap B S hS G.toFunctor G.ι y ∈
        Set.range (pointsMap B S hS (yoneda.obj V) b) := by
      rw [← hGrange]; exact ⟨y, rfl⟩
    obtain ⟨w, hw⟩ := hmem
    refine ⟨w, hιinj ?_⟩
    rw [← pointsMap_comp_apply, hb'ι]
    exact hw
  -- `G` is reasonable, which bounds the fibres of the lifted affine chart.
  have hGreasonable : IsReasonableSpace B S hS G.toFunctor :=
    isReasonableSpace_of_isOpenSubspace B S hS hr hG
  obtain ⟨H', hH'open, hH'rep, hH'ne⟩ := hchart G.toFunctor V b' hG.1 hVaffine hb'etale
    hb'surj (hGreasonable V hVaffine b' hb'etale)
    ⟨pointsMap B S hS (yoneda.obj V) b' v⟩
  obtain ⟨H, -, hHopen, hHrep, hHne⟩ :=
    exists_isRepresentable_isOpenSubspace_le_of_isOpenSubspace B S hS hX hG hH'open hH'rep
      hH'ne
  exact ⟨H, hHopen, hHrep, hHne⟩

/-- **Tag 03JI from the affine-chart core statement.** A reasonable algebraic space over `S`
has a representable open subspace whose point set is dense, as soon as every nonempty
algebraic space over `S` carrying an affine étale chart surjective on points with universally
bounded fibres has a nonempty representable open subspace.

The hypothesis `hchart` is the conclusion of the source's induction on a bound for the fibre
degrees of the chart; it is discharged, modulo Tag 07S8 alone, by
`AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_of_h07S8` of
`StacksFrontier.AlgebraicGeometry.Spaces.DegreeInductionSchematicLocus`. Everything else in the
proof of Tag 03JI is proved. See the implementation notes of this file. -/
theorem exists_denseRange_isRepresentable_isOpenSubspace_of_chartCore
    (hchart : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (V : BigFppfOver B S hS)
      (b : yoneda.obj V ⟶ Y), IsAlgebraicSpace B S hS Y →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b →
      Function.Surjective (pointsMap B S hS (yoneda.obj V) b) →
      HasUniversallyBoundedFibers B S hS V b → Nonempty (points B S hS Y) →
      ∃ H : Subfunctor Y, IsOpenSubspace B S hS H ∧ H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hr : IsReasonableSpace B S hS X) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      DenseRange (pointsMap B S hS G.toFunctor G.ι) :=
  exists_denseRange_isRepresentable_isOpenSubspace_of_core B S hS hX hr
    fun _Y hY hYr hYne =>
      exists_isRepresentable_isOpenSubspace_of_chartCore B S hS hchart hY hYr hYne

end AlgebraicGeometry.Space

end
