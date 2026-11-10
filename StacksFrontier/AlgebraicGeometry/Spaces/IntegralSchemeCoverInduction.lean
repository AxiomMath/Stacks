module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.MinimalDegreeFibreBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ExtendIntegralMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverDenseCompactification
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverGraphOmittedFibrePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverReductions
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimensionDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCoverRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremGeneral

/-!
# The induction of Stacks 09YB on the fibre degree of a chart

This file performs the induction of [Stacks, Tag 09YB] and discharges clause (1) of that tag:
a quasi-compact quasi-separated algebraic space over a scheme `S` admits a surjective integral
morphism from the presheaf represented by an object of the big fppf site — that is, **from a
scheme**.

The induction is on an integer `d` bounding the degrees of the field-valued fibres of a
surjective étale chart `p : h_U ⟶ X`, and its step is the source's:

* `p` is quasi-finite and separated, so Tag 0ABS factors it as a quasi-compact open immersion
  `h_U ⟶ Y₀` followed by an integral `Y₀ ⟶ X`, and the scheme-theoretic closure of the image
  replaces `Y₀` by a `Y` in which `U` is dense
  (`AlgebraicGeometry.Space.exists_isSchemeTheoreticallyDense_isIntegralHom_factorization`);
* the complementary summand `W` of the splitting `h_U ×_X Y = h_U ⨿ W` is a surjective étale
  chart of an open subspace `V ⊆ Y` with every field-valued fibre of degree `< d`, and `Y ∖ V`
  is contained in `j(U)`
  (`AlgebraicGeometry.Space.exists_isOpenSubspace_chart_isFiniteLocallyFreeOfRank_lt`);
* `V` is again quasi-separated and is quasi-compact, and its chart is again separated with
  quasi-compact source, so the induction hypothesis at the smaller bound covers `V`; and
* that cover is extended over `Y` by Tag 0G2D, glued with the reduced induced structure on
  `Y ∖ V`, and pushed to `X` along the integral `Y ⟶ X`
  (`AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_openSubspace_cover` and
  `AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_comp`).

The recursion bottoms out at `d = 0`: no field-valued fibre can have degree below `0`, so `V`
has no points at all, `j(U)` is the whole of `Y` and `j` is a surjective open immersion, hence
an isomorphism; the chart `p = j ≫ π` is then itself integral and surjective.

## Main results

* `AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_openSubspace_cover`: **the
  last step of the inductive step.** If an open subspace `V` of a quasi-separated algebraic
  space `Y` is quasi-compact, has an integral surjective scheme cover, and together with the
  image of a representable open immersion `j : h_U ⟶ Y` covers `|Y|`, then `Y` has an integral
  surjective scheme cover.
* `AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_isEmpty_points`: an algebraic
  space with no points has one, namely its own chart.
* `AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_chart_fibre_le`: **the
  induction.** A quasi-separated algebraic space carrying a separated surjective étale chart
  with quasi-compact source all of whose field-valued fibres have degree at most `d` has an
  integral surjective scheme cover.
* `AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_isQuasiCompactSpace`:
  **clause (1) of [Stacks, Tag 09YB], unconditionally.**

## Implementation notes

**What the induction carries, and why.** The hypotheses on the chart are étaleness,
surjectivity, separatedness and quasi-compactness *of the source as a space* — not affineness.
Affineness is not available at the recursive call: the new chart `W` is produced as a site
object with no finiteness property attached. What is available is the factorization
`φ : h_W ⟶ h_U` of the drop through the old chart, and that factorization is **integral**, which
is exactly enough: it makes `h_W` quasi-compact over the quasi-compact `h_U`, and it makes
`φ ≫ p` separated, whence the new chart is separated by the cancellation of Stacks 0AGC.
Affineness is needed only to *start* the induction, where it supplies both the chart and —
through Stacks 03JX and the degree stratification of Stacks 07S8 — the initial bound.

**Why quasi-separatedness is carried and quasi-compactness of the space is not.** The space is
quasi-compact automatically, being the surjective image of a quasi-compact chart. Quasi-
separatedness, by contrast, is used twice: to see that the chart is a quasi-compact *morphism*,
which Tag 0ABS needs for quasi-finiteness, and to see that the inclusion of `V` is a
quasi-compact morphism, which Tag 0G2D needs. Both are
`AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace`, Stacks 073B part (1). It passes
to `Y` because `Y ⟶ X` is integral, hence separated, and to `V` because `V ⊆ Y` is a
subfunctor.

**Why `Y'` of Tag 0G2D is a scheme.** Tag 0G2D extends the integral cover `Z ⟶ V` to an
integral `ν : Y' ⟶ Y` with `Y' ×_Y V ≅ Z`, and `Y'` is only asserted to be an algebraic space.
It is covered by two open subspaces: `Y' ×_Y V`, which is `Z` and so a scheme, and
`Y' ×_Y h_U`, which is integral over the scheme `U` and so a scheme by Tag 03KC. They cover
because `V` and `j(U)` cover `Y`, the points of a fibre product over matching points existing
by Tag 03H4. Tag 01JJ in the form
`AlgebraicGeometry.Space.isRepresentable_of_isOpenImmersion_cover` then makes `Y'` a scheme.

**The reduced closed complement is a scheme** because it is a closed subspace of `Y` whose
point set lies in `j(U)`: `AlgebraicGeometry.Space.isRepresentable_of_le_of_isClosedSubspace`.

## References

* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 0ABS](https://stacks.math.columbia.edu/tag/0ABS)
* [Stacks Project, Tag 0G2D](https://stacks.math.columbia.edu/tag/0G2D)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 07S8](https://stacks.math.columbia.edu/tag/07S8)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
* [Stacks Project, Tag 0AGC](https://stacks.math.columbia.edu/tag/0AGC)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The last step of the inductive step -/

/-- Precomposing with an isomorphism does not change the integrality of a morphism. -/
private theorem isIntegralHom_comp_of_isIso {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ⟶ G) [IsIso e] {f : G ⟶ H} (hf : IsIntegralHom B S hS f) :
    IsIntegralHom B S hS (e ≫ f) :=
  isIntegralHom_comp B S hS
    (isIntegralHom_of_isClosedImmersion B S hS e (isClosedImmersion_of_isIso B S hS e)) hf

/-- Precomposing with an isomorphism does not change the set of points in the range. -/
private theorem range_pointsMap_comp_of_isIso {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ⟶ G) [IsIso e] (f : G ⟶ H) :
    Set.range (pointsMap B S hS F (e ≫ f)) = Set.range (pointsMap B S hS G f) := by
  rw [pointsMap_comp]
  exact (pointsMap_surjective_of_isIso B S hS e).range_comp _

/-- **The last step of the inductive step of [Stacks, Tag 09YB].** Let `Y` be a quasi-separated
algebraic space over `S`, let `j : h_U ⟶ Y` be an open immersion from an object of the site and
let `V ⊆ Y` be a quasi-compact open subspace whose point set together with that of `j` covers
`|Y|`. If `V` has a surjective integral scheme cover then so does `Y`.

Tag 0G2D extends the cover of `V` to an integral `ν : Y' ⟶ Y`; `Y'` is a scheme because it is
covered by the two open subspaces `Y' ×_Y V ≅ Z` and `Y' ×_Y h_U`, the second being integral
over the scheme `U`; the reduced induced structure on `|Y| ∖ |V|` is a scheme because it is a
closed subspace of `Y` lying inside `j(U)`; and the two are glued by
`AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_isIntegralHom_pair`. -/
theorem existsIntegralSurjectiveSchemeCover_of_openSubspace_cover
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (U : BigFppfOver B S hS) (j : yoneda.obj U ⟶ Y) (hj : IsOpenImmersion B S hS j)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hVqc : IsQuasiCompactSpace B S hS V.toFunctor)
    (hcov : Set.range (pointsMap B S hS (yoneda.obj U) j) ∪
      Set.range (pointsMap B S hS V.toFunctor V.ι) = Set.univ)
    (hVcover : ExistsIntegralSurjectiveSchemeCover B S hS V.toFunctor) :
    ExistsIntegralSurjectiveSchemeCover B S hS Y := by
  classical
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have _ : Functor.IsRepresentable (yoneda.obj U) := inferInstance
  obtain ⟨Zc, ζ, hζsurj, hζint⟩ := hVcover
  have hZcalg : IsAlgebraicSpace B S hS (yoneda.obj Zc) := isAlgebraicSpace_yoneda B S hS Zc
  -- the inclusion of `V` is a quasi-compact morphism, which Tag 0G2D needs
  have hViqc : IsQuasiCompact B S hS V.ι :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hY hYqs hVqc V.ι
  -- Tag 0G2D: extend the integral cover of `V` to an integral morphism to `Y`
  obtain ⟨Y', ν, f', hY', hνint, hsq⟩ :=
    exists_isIntegralHom_isPullback_of_isOpenImmersion hZcalg hV.1 hY V.ι hV.2 hViqc ζ hζint
  -- the two charts of `Y'`
  have _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hf'oi : IsOpenImmersion B S hS f' :=
    MorphismProperty.of_isPullback hsq.flip hV.2
  have hPalg : IsAlgebraicSpace B S hS (pullback ν j) :=
    isAlgebraicSpace_pullback B S hS ν j hY' hUalg hY
  have hfstoi : IsOpenImmersion B S hS (pullback.fst ν j) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback ν j).flip hj
  have hsndint : IsIntegralHom B S hS (pullback.snd ν j) :=
    isIntegralHom_of_isPullback B S hS (IsPullback.of_hasPullback ν j) hνint
  have hPrep : (pullback ν j).IsRepresentable := by
    obtain ⟨hrep, -⟩ :=
      (isIntegralHom_iff_representable B S hS (pullback.snd ν j) hPalg hUalg).1 hsndint
    exact Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable _ hrep
  have _ := hPrep
  set eP : yoneda.obj (pullback ν j).reprX ≅ pullback ν j := (pullback ν j).reprW with hePdef
  -- `Y'` is a scheme: the two charts are open immersions and cover its points
  set Wfam : ULift.{u} Bool → BigFppfOver B S hS := fun b =>
    match b with
    | ⟨false⟩ => Zc
    | ⟨true⟩ => (pullback ν j).reprX
  set kfam : ∀ b, yoneda.obj (Wfam b) ⟶ Y' := fun b =>
    match b with
    | ⟨false⟩ => f'
    | ⟨true⟩ => eP.hom ≫ pullback.fst ν j
  have hkoi : ∀ b, IsOpenImmersion B S hS (kfam b) := by
    intro b
    rcases b with ⟨_ | _⟩
    · exact hf'oi
    · exact isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS eP.hom) hfstoi
  have hkcov : (⋃ b, Set.range (pointsMap B S hS (yoneda.obj (Wfam b)) (kfam b))) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun y' => ?_
    rcases Set.eq_univ_iff_forall.1 hcov (pointsMap B S hS Y' ν y') with ⟨uu, hu⟩ | ⟨vv, hv⟩
    · obtain ⟨w, hw, -⟩ :=
        exists_points_of_isPullback B S hS (IsPullback.of_hasPullback ν j) y' uu hu.symm
      refine Set.mem_iUnion.2 ⟨⟨true⟩,
        pointsMap B S hS (pullback ν j) eP.inv w, ?_⟩
      change pointsMap B S hS (yoneda.obj (pullback ν j).reprX) (eP.hom ≫ pullback.fst ν j)
        (pointsMap B S hS (pullback ν j) eP.inv w) = y'
      rw [← pointsMap_comp_apply, eP.inv_hom_id_assoc]
      exact hw
    · obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS hsq y' vv hv.symm
      exact Set.mem_iUnion.2 ⟨⟨false⟩, w, hw⟩
  have hY'rep : Y'.IsRepresentable := by
    refine isRepresentable_of_isOpenImmersion_cover B S hS hY'.isSheaf
      (ι := ULift.{u} Bool) ((Cardinal.lt_aleph0_of_finite _).trans B.aleph0_lt_cutoff)
      (μ := max ((BigFppfOver.toScheme B S hS).obj Zc).size
        ((BigFppfOver.toScheme B S hS).obj (pullback ν j).reprX).size)
      (max_lt Zc.left.property (pullback ν j).reprX.left.property)
      (W := Wfam) ?_ kfam hkoi hkcov
    intro b
    rcases b with ⟨_ | _⟩
    · exact le_max_left _ _
    · exact le_max_right _ _
  have _ := hY'rep
  set eY' : yoneda.obj Y'.reprX ≅ Y' := Y'.reprW with heY'def
  -- the reduced closed complement of `V`, a scheme because it lies inside `j(U)`
  have hVopenPts : IsOpen (Set.range (pointsMap B S hS V.toFunctor V.ι)) :=
    isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hY V hV
  set Tset : Set (points B S hS Y) := (Set.range (pointsMap B S hS V.toFunctor V.ι))ᶜ
    with hTsetdef
  have hTcl : _root_.IsClosed Tset := hVopenPts.isClosed_compl
  set T : Subfunctor Y := reducedClosedSubspace B S hS Y hY Tset hTcl with hTdef
  have hTrange : Set.range (pointsMap B S hS T.toFunctor T.ι) = Tset :=
    range_pointsMap_ι_reducedClosedSubspace B S hS Y hY Tset hTcl
  have hTcs : IsClosedSubspace B S hS T :=
    isClosedSubspace_reducedClosedSubspace' B S hS hY Tset hTcl
  have hjopen : IsOpenSubspace B S hS (Subfunctor.range j) :=
    isOpenSubspace_range_of_isOpenImmersion U j hj
  have _ : Mono j := mono_of_isOpenImmersion B S hS j hj
  have hjrange : Set.range (pointsMap B S hS (Subfunctor.range j).toFunctor
      (Subfunctor.range j).ι) = Set.range (pointsMap B S hS (yoneda.obj U) j) :=
    range_pointsMap_ι_range B S hS j
  have hle : T ≤ Subfunctor.range j := by
    refine le_of_range_pointsMap_ι_subset B S hS hjopen ?_
    rw [hTrange, hjrange]
    intro y hy
    rcases Set.eq_univ_iff_forall.1 hcov y with h | h
    · exact h
    · exact absurd h hy
  have hTrep : T.toFunctor.IsRepresentable :=
    isRepresentable_of_le_of_isClosedSubspace B S hS hTcs hle
      (isRepresentable_range_of_isOpenImmersion U j hj)
  have _ := hTrep
  set eT : yoneda.obj T.toFunctor.reprX ≅ T.toFunctor := T.toFunctor.reprW with heTdef
  -- glue the two integral covers
  refine existsIntegralSurjectiveSchemeCover_of_isIntegralHom_pair B S hS hY
    Y'.reprX T.toFunctor.reprX (eY'.hom ≫ ν) (eT.hom ≫ T.ι) ?_ ?_ ?_
  · exact isIntegralHom_comp_of_isIso B S hS eY'.hom hνint
  · exact isIntegralHom_comp_of_isIso B S hS eT.hom
      (isIntegralHom_of_isClosedImmersion B S hS _ hTcs.2)
  · have hrange1 : Set.range (pointsMap B S hS (yoneda.obj Y'.reprX) (eY'.hom ≫ ν)) =
        Set.range (pointsMap B S hS Y' ν) := by
      rw [pointsMap_comp]
      exact (pointsMap_surjective_of_isIso B S hS eY'.hom).range_comp _
    have hrange2 : Set.range (pointsMap B S hS (yoneda.obj T.toFunctor.reprX)
          (eT.hom ≫ T.ι)) = Set.range (pointsMap B S hS T.toFunctor T.ι) := by
      rw [pointsMap_comp]
      exact (pointsMap_surjective_of_isIso B S hS eT.hom).range_comp _
    intro y
    rw [hrange1, hrange2]
    by_cases hy : y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι)
    · -- over `V` the cover of `V` lifts into `Y'`
      obtain ⟨v, hv⟩ := hy
      obtain ⟨z, hz⟩ := hζsurj v
      refine Or.inl ⟨pointsMap B S hS (yoneda.obj Zc) f' z, ?_⟩
      rw [← pointsMap_comp_apply, hsq.w, pointsMap_comp_apply, hz, hv]
    · -- off `V` the reduced closed complement covers
      refine Or.inr ?_
      rw [hTrange]
      exact hy

/-! ### The base of the induction -/

/-- **An algebraic space over `S` with no points has a surjective integral scheme cover: its own
étale chart.** The chart has no points either, so it is universally injective — every base change
of it has a point set mapping into the empty point set of the chart — and an étale, universally
injective, surjective morphism of algebraic spaces is an isomorphism by Stacks 05W5. An
isomorphism is a closed immersion, hence integral. -/
theorem existsIntegralSurjectiveSchemeCover_of_isEmpty_points
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (c : yoneda.obj U ⟶ X) (hc : IsEtale B S hS c)
    (hcs : IsSurjective B S hS c) (hempty : IsEmpty (points B S hS X)) :
    ExistsIntegralSurjectiveSchemeCover B S hS X := by
  have hUempty : IsEmpty (points B S hS (yoneda.obj U)) :=
    ⟨fun w ↦ hempty.elim (pointsMap B S hS (yoneda.obj U) c w)⟩
  have hui : UniversallyInjective B S hS c := by
    intro Y' _ g a _ _
    exact hUempty.elim (pointsMap B S hS (pullback g c) (pullback.snd g c) a)
  have hiso : IsIso c :=
    isIso_of_isEtale_of_universallyInjective_of_isSurjective B S hS
      (isAlgebraicSpace_yoneda B S hS U) hX c hc hui hcs
  have _ := hiso
  exact ⟨U, c, hcs,
    isIntegralHom_of_isClosedImmersion B S hS c (isClosedImmersion_of_isIso B S hS c)⟩

/-! ### The induction on the fibre degree -/

/-- **The induction of [Stacks, Tag 09YB] on the fibre degree of a chart.**

Let `X` be a quasi-separated algebraic space over `S` and let `p : h_U ⟶ X` be a separated
surjective étale chart whose source is quasi-compact and every field-valued fibre of which is
finite locally free of degree at most `d`. Then `X` has a surjective integral scheme cover.

The induction is strong induction on `d`. At each stage Tag 0ABS factors `p` as a quasi-compact
open immersion `j : h_U ⟶ Y` followed by an integral `π : Y ⟶ X`, with `j(U)` dense in `Y`
after replacing `Y` by the scheme-theoretic closure of that image; the complementary summand of
the splitting `h_U ×_X Y = h_U ⨿ W` is a surjective étale chart of an open subspace `V ⊆ Y`,
with every field-valued fibre of degree strictly below `d` and with `Y ∖ V ⊆ j(U)`.

If `d = 0` there is no degree below `d`, so `V` has no points and `j` is a surjective open
immersion, hence an isomorphism; then `p = j ≫ π` is itself integral and surjective. Otherwise
`V` is a quasi-separated algebraic space, quasi-compact because it is the surjective image of
the quasi-compact `h_W`, and its chart is separated with quasi-compact source because the
factorization of the drop through `h_U` is integral; so the induction hypothesis at `d - 1`
covers `V`, and
`AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_openSubspace_cover` together
with `AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_comp` carries that cover to
`Y` and then to `X`. -/
theorem existsIntegralSurjectiveSchemeCover_of_chart_fibre_le
    (hZ : B.Contains (⊤_ Scheme.{u})) (d : ℕ) :
    ∀ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS X →
      IsAbsolutelyQuasiSeparated B S hS hZ X →
      ∀ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
        IsEtale B S hS p → IsSurjective B S hS p → IsSeparated B S hS p →
        IsQuasiCompactSpace B S hS (yoneda.obj U) →
        (∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
          (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
          (ζ : yoneda.obj T ⟶ X) (Q : BigFppfOver B S hS) (q : Q ⟶ T)
          (c : yoneda.obj Q ⟶ yoneda.obj U),
          IsPullback c (yoneda.map q) p ζ →
            ∃ r : ℕ, r ≤ d ∧
              IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r) →
        ExistsIntegralSurjectiveSchemeCover B S hS X := by
  classical
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro X hX hXqs U p hpet hpsurj hpsep hUqc hd
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  -- the chart is a quasi-compact morphism, hence quasi-finite
  have hpqc : IsQuasiCompact B S hS p :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hX hXqs hUqc p
  have hpqf : IsQuasiFinite B S hS p :=
    ⟨isLocallyQuasiFinite_of_isEtale' B S hS hpet, hpqc⟩
  -- Tag 0ABS, then the dense replacement
  obtain ⟨-, N₀, hfac₀, hj₀, hj₀qc, hπ₀⟩ := zariskiMainTheorem B S hS p hUalg hX hpqf hpsep
  have hY₀ := N₀.isAlgebraicSpace
  set j₀ := N₀.toNorm
  set π₀ := N₀.fromNorm
  obtain ⟨Y, j, π, hY, hj, hjqc, hπ, hfac, -, -, -, hdense⟩ :=
    exists_isSchemeTheoreticallyDense_isIntegralHom_factorization B S hS hUalg hY₀ j₀ hj₀
      hj₀qc π₀ hπ₀
  have hjπ : j ≫ π = p := hfac.trans hfac₀
  -- the fibre-degree drop
  obtain ⟨Wc, V, g', φ, hVopen, hg'et, hg'surj, hφint, hgfac, hcov, hdrop⟩ :=
    exists_isOpenSubspace_chart_isFiniteLocallyFreeOfRank_lt B S hS hX hY U j π hj hπ
      (by rw [hjπ]; exact hpet) (by rw [hjπ]; exact hpsep) (by rw [hjπ]; exact hpsurj)
      hdense d (by rw [hjπ]; exact hd)
  have hWcalg : IsAlgebraicSpace B S hS (yoneda.obj Wc) := isAlgebraicSpace_yoneda B S hS Wc
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- the base: no fibre can have degree below zero, so `V` has no points and `j` is an iso
    subst hd0
    have hVempty : IsEmpty (points B S hS V.toFunctor) := by
      refine ⟨fun x => ?_⟩
      obtain ⟨pt, -⟩ := Quot.exists_rep x
      have hg'p := (isEtale_iff_presheaf_of_yoneda B S hS g').1 hg'et
      obtain ⟨r, hr, -⟩ := hdrop pt.carrier pt.field pt.siteObject (Iso.refl _)
        (yonedaEquiv.symm pt.value) (hg'p.rep.pullback (yonedaEquiv.symm pt.value))
        (hg'p.rep.snd (yonedaEquiv.symm pt.value))
        (yoneda.map (hg'p.rep.fst' (yonedaEquiv.symm pt.value)))
        (hg'p.rep.isPullback' (yonedaEquiv.symm pt.value))
      exact absurd hr (Nat.not_lt_zero r)
    have hVrange : Set.range (pointsMap B S hS V.toFunctor V.ι) = ∅ := Set.range_eq_empty _
    have hjsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) j) := by
      intro y
      rcases Set.eq_univ_iff_forall.1 hcov y with h | h
      · exact h
      · rw [hVrange] at h; exact absurd h (Set.notMem_empty y)
    have _ : IsIso j := isIso_of_isOpenImmersion_of_surjective_pointsMap B S hS j hj hjsurj
    refine ⟨U, p, hpsurj, ?_⟩
    rw [← hjπ]
    exact isIntegralHom_comp_of_isIso B S hS j hπ
  · -- the step: recurse into `V` at the strictly smaller bound
    have hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y :=
      isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hY hXqs
        (isQuasiSeparated_of_isSeparated B S hS
          (isSeparated_of_isIntegralHom B S hS π hY hX hπ))
    have hφqc : IsQuasiCompact B S hS φ :=
      isQuasiCompact_of_isAffineHom' B S hS φ hWcalg hUalg
        (isAffineHom_of_isIntegralHom φ hφint)
    have hWcqc : IsQuasiCompactSpace B S hS (yoneda.obj Wc) :=
      isQuasiCompactSpace_source_of_isQuasiCompact B S hS hUalg hUqc hφqc
    have hVqc : IsQuasiCompactSpace B S hS V.toFunctor :=
      isQuasiCompactSpace_of_isSurjective B S hS hWcalg hVopen.1 g' hg'surj hWcqc
    have hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V.toFunctor :=
      isAbsolutelyQuasiSeparated_subfunctor B S hS hZ hYqs V hVopen.1
    have hg'sep : IsSeparated B S hS g' := by
      refine isSeparated_of_comp B S hS g' (V.ι ≫ π) ?_
      have hcomp : g' ≫ V.ι ≫ π = φ ≫ p := by rw [← Category.assoc, hgfac, hjπ]
      rw [hcomp]
      exact isSeparated_comp B S hS φ p
        (isSeparated_of_isIntegralHom B S hS φ hWcalg hUalg hφint) hpsep
    have hVcover : ExistsIntegralSurjectiveSchemeCover B S hS V.toFunctor :=
      ih (d - 1) (by omega) V.toFunctor hVopen.1 hVqs Wc g' hg'et hg'surj hg'sep hWcqc
        (fun K hK T eT ξ Q q c hsqc => by
          obtain ⟨r, hlt, hrank⟩ := hdrop K hK T eT ξ Q q c hsqc
          exact ⟨r, by omega, hrank⟩)
    refine existsIntegralSurjectiveSchemeCover_comp B S hS π hπ ?_ ?_
    · intro y
      obtain ⟨x, hx⟩ := hpsurj y
      exact ⟨pointsMap B S hS (yoneda.obj U) j x, by rw [← pointsMap_comp_apply, hjπ]; exact hx⟩
    · exact existsIntegralSurjectiveSchemeCover_of_openSubspace_cover B S hS hZ hY hYqs U j hj
        V hVopen hVqc hcov hVcover

/-! ### Clause (1) of the tag -/

/-- **Clause (1) of [Stacks, Tag 09YB], unconditionally.** A quasi-compact quasi-separated
algebraic space over a scheme `S` admits a surjective integral morphism from the presheaf
represented by an object of the big fppf site, that is from a scheme over `S`.

An affine surjective étale chart exists because the space is quasi-compact (Stacks 03E3 in the
form `AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover`); a
quasi-separated algebraic space is reasonable by Stacks 03JX, so the fibre degrees of that
chart are bounded, by the degree stratification of Stacks 07S8
(`AlgebraicGeometry.Space.exists_minimalDegreeOpen_and_fibre_le_degree`); and
`AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_chart_fibre_le` performs the
induction on that bound. The space with no points is treated separately, its chart then being
an isomorphism. -/
theorem existsIntegralSurjectiveSchemeCover_of_isQuasiCompactSpace
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X) :
    ExistsIntegralSurjectiveSchemeCover B S hS X := by
  classical
  obtain ⟨U, c, hUaff, hcsurj, hcet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X hX).1 hXqc
  have hcs : IsSurjective B S hS c := isSurjective_of_presheafSurjective B S hS c hcsurj
  rcases isEmpty_or_nonempty (points B S hS X) with hemp | hne
  · exact existsIntegralSurjectiveSchemeCover_of_isEmpty_points B S hS hX U c hcet hcs hemp
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hUaff
  have hUsep : Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj U) := inferInstance
  have hUqc : IsQuasiCompactSpace B S hS (yoneda.obj U) :=
    isQuasiCompact_yoneda_of_compact B S hS U inferInstance
  have hcsep : IsSeparated B S hS c :=
    isSeparated_of_isEtale_of_scheme_isSeparated B S hS X hX U hUsep c hcet
  have hR : IsReasonableSpace B S hS X :=
    isReasonableSpace_of_isAbsolutelyQuasiSeparated B S hS hZ X hX hXqs
  obtain ⟨d, -, -, -, -, -, hbd⟩ :=
    exists_minimalDegreeOpen_and_fibre_le_degree B S hS X U c hX hR hUaff hcet hcsep hne
  exact existsIntegralSurjectiveSchemeCover_of_chart_fibre_le B S hS hZ d X hX hXqs U c hcet
    hcs hcsep hUqc hbd

end AlgebraicGeometry.Space

end
