module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv

/-!
# The inverse image of the centre along the blowup of an algebraic space

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `Z ⊆ X` be a closed
subspace.  Tag 085U says that the blowing up `b : X' ⟶ X` of `Z` in `X` is a final object of the
category `𝒞` of those `Y ⟶ X` whose inverse image of `Z` is an effective Cartier divisor on `Y`.
Finality has two independent halves: that `b` is an *object* of `𝒞`, and that every object of
`𝒞` admits a unique morphism to `b` over `X`.  This file is about the first half, membership:
the inverse image `b⁻¹(Z)` of the centre along the blowup
`AlgebraicGeometry.Space.blowUpAlongHom'` of Tag 085Q is an effective Cartier divisor on the
blowup.

The route is étale descent for effective Cartier divisors.  The blowup is glued from the
relative `Proj` `P_U` of the Rees algebra of the induced sheaf of ideals on the presenting
scheme `U` of an étale presentation, and `P_U ⟶ X'` is a surjective étale scheme chart
(`AlgebraicGeometry.Space.RelativeProjGlueingData.chart`), so part (2) of Tag 083C — available
here as `AlgebraicGeometry.Space.isEffectiveCartierDivisor_of_hasEffectiveCartierEtaleCover` —
reduces the assertion to a statement about one ideal sheaf of the *scheme* `P_U`.  That ideal
sheaf is identified below with the inverse image along `P_U ⟶ U` of the sheaf of ideals the
construction of the blowup starts from, so the residue is the scheme-level assertion of Tag
02OS part (2) for the relative `Proj` of a Rees algebra.

## Main definitions

* `AlgebraicGeometry.Space.blowUpGlueingData` is the glueing datum of Tag 084C out of which
  `AlgebraicGeometry.Space.blowUpAlong'` is built, named so that its chart `P_U ⟶ X'` and the
  structure morphism `P_U ⟶ U` can be referred to.

## Main results

* `AlgebraicGeometry.Space.ker_rep_snd_eq_reesChartIdeal`: **the identification the blowup
  needs on its chart.**  It applies
  `AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart` -- the sheaf of ideals a
  closed subspace induces on an étale scheme chart is the ideal sheaf of its inverse image
  there, proved in `StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage` -- at the
  chart of the presentation.
* `AlgebraicGeometry.Space.ker_rep_snd_blowUpChart`: **the inverse image of the centre along the
  chart of the blowup is the exceptional ideal of the scheme-level relative `Proj`.**  The ideal
  sheaf of the inverse image of `Z` along `P_U ⟶ U ⟶ X`, which the chart square identifies with
  the inverse image of `b⁻¹(Z)` on `P_U`, is the inverse image of the Rees chart ideal along the
  structure morphism `P_U ⟶ U`.
* `AlgebraicGeometry.Space.isPullbackDefined_blowUpAlongHom'`: **the membership half of Tag
  085U**, from the scheme-level statement of Tag 02OS part (2) for the relative `Proj` of the
  Rees algebra of the chart ideal.
* `AlgebraicGeometry.Space.isPullbackDefined_blowUpAlongHom'_of_iso`: the same, from the
  comparison of that relative `Proj` with the blowup of a scheme as the library builds it.
* `Stacks.Blowup.isEffectiveCartierDivisor_comap_relativeProjToBase_of_iso` is the transport
  which derives the scheme-level input from that comparison.
* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_exceptionalDivisor'`: **the membership half
  of Tag 085U with nothing assumed**, the scheme-level divisor statement being supplied by
  `Stacks.Blowup.isCartierOver_relativeProjToBase_reesSituation`.

## Implementation notes

**Why the chart identification is the whole space-level content.**  The chart condition of Tag
083C is a condition on the single ideal sheaf `(D ×_{X'} P_U ⟶ P_U).ker` by
`AlgebraicGeometry.Space.isSchemeEffectiveCartierPullback_iff_ker`, and the chart square
`AlgebraicGeometry.Space.RelativeProjGlueingData.chart_comp_toBase` turns the inverse image of
`b⁻¹(Z)` on `P_U` into the inverse image of `Z` along `P_U ⟶ U ⟶ X`.  Inverse images on charts
compose — `AlgebraicGeometry.Space.schemeKer_snd_comp` — so everything reduces to the
ideal sheaf of `Z ×_X U` on `U`, which `ker_rep_snd_eq_idealSheafDataOfChart` identifies with
the sheaf of ideals `AlgebraicGeometry.Space.reesChartIdeal` whose Rees algebra the blowup is
the relative `Proj` of.  That identification is proved affine-open by affine open in
`StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage`, which this file imports.

**Where the scheme-level divisor statement comes from.**  The input `hE` below is Tag 02OS part
(2) — the exceptional divisor of the blowup of a scheme is an effective Cartier divisor — for the
relative `Proj` of `Stacks.Blowup.reesSituation`, the Rees algebra *sheaf* of the chart ideal.
The library proves Tag 02OS part (2) twice, for `AlgebraicGeometry.blowUp` in
`Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal` and for `Stacks.Blowup.blowUp` in
`Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal_reesData`, and neither is the relative
`Proj` the blowup of an algebraic space is glued from:
`AlgebraicGeometry.reesSituation` takes its graded algebra from a chosen witness of
`Stacks.Blowup.exists_reesAlgebraData` rather than from the explicit sheaf, and
`Stacks.Blowup.reesData` glues the ordinary Rees algebras `Γ(X, U)[I(U)t]` instead.  What was
missing was therefore a comparison of constructions and not a divisor statement, and that
comparison is `Stacks.Blowup.reesSituationBlowUpIso` in
`StacksFrontier/AlgebraicGeometry/Blowup/ReesSituationComparison.lean`, an isomorphism over the
base along which Tag 02OS part (2) is already transported there:
`Stacks.Blowup.isCartierOver_relativeProjToBase_reesSituation` is exactly `hE`.  So
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_exceptionalDivisor'` assumes nothing beyond
the three `B.Contains` side conditions on the relative
`Proj`s, which are the set-theoretic conditions
`AlgebraicGeometry.Space.relativeProjChartOfSituation` already takes.

**The finality half, for whoever takes it.**  Finality is the mapping-in property of relative
`Proj` for algebraic spaces.  Its scheme analogue is
`Stacks.RelativeProj.Situation.exists_hom_relativeProj_of_sectionRingHom`, and transporting it
needs a morphism into the blowup to be descended to the quotient sheaf; the handle for that is
`AlgebraicGeometry.Space.RelativeProjGlueingData.existsUnique_desc_toSpace`.  The entry point
assembling the two halves into Tag 085U is
`AlgebraicGeometry.Space.isBlowupAlong_of_existsUnique_lift`, which consumes exactly the
membership statement proved here together with the unique lift.

## References

* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 083Y](https://stacks.math.columbia.edu/tag/083Y)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Blowup

/-- **The exceptional ideal of the relative `Proj` of the Rees algebra sheaf is an effective
Cartier divisor, given the comparison with the blowup.**  If the relative `Proj` of
`Stacks.Blowup.reesSituation I` is isomorphic over the base to the blowup
`Stacks.Blowup.blowUp I`, then the inverse image of `I` along its structure morphism is an
effective Cartier divisor.

The inverse image along an isomorphism of the exceptional ideal of `Stacks.Blowup.blowUp I` is
the ideal in question, and an isomorphism is flat, so Tag 02OS part (2) in the form
`Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal_reesData` transports along it. -/
theorem isEffectiveCartierDivisor_comap_relativeProjToBase_of_iso {X : Scheme.{u}}
    (I : X.IdealSheafData) (e : (reesSituation I).relativeProj ≅ blowUp I)
    (he : e.hom ≫ blowUpToBase I = (reesSituation I).relativeProjToBase) :
    Stacks.Divisors.IsEffectiveCartierDivisor (I.comap (reesSituation I).relativeProjToBase) := by
  rw [← he, Scheme.IdealSheafData.comap_comp]
  exact Stacks.Divisors.isPullbackDefined_of_flat e.hom _
    (isEffectiveCartierDivisor_exceptionalIdeal_reesData I)

end Stacks.Blowup

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The sheaf of ideals a closed subspace induces on an étale scheme chart -/

/-- **On an affine chart the chartwise sheaf of ideals is the ideal sheaf of the defining
ideal.**  The sheaf of ideals that the defining ideal sheaf of a closed subspace `Z ⊆ X`
induces on an *affine* étale scheme chart `A` is the ideal sheaf of the single ideal
`AlgebraicGeometry.Space.definingIdealAt` of sections over `A`.

An ideal sheaf on an affine scheme is determined by its ideal of global sections, and that
ideal is computed by `AlgebraicGeometry.Space.ker_appTop_subschemeι_idealSheafDataOfChart`. -/
theorem idealSheafDataOfChart_eq_ofIdealTop (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (A : SmallEtale B S hS X.1)
    [IsAffine (chartScheme A)] :
    idealSheafDataOfChart B S hS X (definingIdealSheaf B S hS X Z)
        (definingIdealSheaf_isCartesianOnAffineCharts B S hS X Z) A =
      Scheme.IdealSheafData.ofIdealTop (X := chartScheme A)
        (definingIdealAt B S hS X Z (op A)) :=
  Scheme.IdealSheafData.ext_of_isAffine
    (((Scheme.IdealSheafData.ker_subschemeι_app _ ⟨⊤, isAffineOpen_top _⟩).symm.trans
      (ker_appTop_subschemeι_idealSheafDataOfChart B S hS X (definingIdealSheaf B S hS X Z)
        (definingIdealSheaf_isCartesianOnAffineCharts B S hS X Z) A inferInstance)).trans
      (Stacks.Divisors.ideal_ofIdealTop_top (isAffineOpen_top (chartScheme A)) _).symm)

/-- **The ideal sheaf of the inverse image of the centre on the presenting scheme of a
presentation is the Rees chart ideal.**  This is
`AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart` at the chart
`AlgebraicGeometry.Space.presentationChart` of an étale presentation: the sheaf of ideals whose
Rees algebra the blowup of `X` along `Z` is the relative `Proj` of is the ideal sheaf of
`Z ×_X U` on `U`. -/
theorem ker_rep_snd_eq_reesChartIdeal (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.obj) (P : Presentation B S hS X.obj X.property) :
    ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd P.toSpace)).ker =
      reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P :=
  ker_rep_snd_eq_idealSheafDataOfChart B S hS X Z (presentationChart P)

/-! ### The inverse image of the centre along the blowup -/

variable {B S hS} {X : AlgebraicSpaces B S hS}
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  (Z : ClosedSubspaces B S hS X.obj) (P : Presentation B S hS X.obj X.property)
  (hcU : B.Contains (reesChartSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (hcR : B.Contains (reesRelationSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (hcRR : B.Contains (reesDoubleSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)

/-- The glueing datum of Tag 084C out of which the blowup
`AlgebraicGeometry.Space.blowUpAlong'` of `X` along `Z` is built: the Rees glueing datum of the
defining ideal sheaf of the centre, with the equivalence-relation condition on the two
projections discharged by
`AlgebraicGeometry.Space.isEquivalenceRelation_post_reesProj`.

The blowup, its structure morphism and its exceptional divisor are this datum's relative `Proj`,
structure morphism and inverse image of the centre; naming the datum is what gives access to its
chart `P_U ⟶ X'`. -/
def blowUpGlueingData : RelativeProjGlueingData B S hS X.obj X.property :=
  reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR
    (isEquivalenceRelation_post_reesProj (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR hcRR)

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **The inverse image of the centre along the chart of the blowup is the exceptional ideal of
the scheme-level relative `Proj`.**  On the étale scheme chart `P_U` of the blowup, the ideal
sheaf of the inverse image of the exceptional divisor `b⁻¹(Z)` is the inverse image of the Rees
chart ideal along the structure morphism `P_U ⟶ U`.

The chart square `AlgebraicGeometry.Space.RelativeProjGlueingData.chart_comp_toBase` identifies
the restriction of `b` to the chart with `P_U ⟶ U ⟶ X`, inverse images of a closed subspace on
charts compose, and the ideal sheaf of `Z ×_X U` on `U` is the Rees chart ideal. -/
theorem ker_rep_snd_blowUpChart :
    ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd
        (yoneda.map (blowUpGlueingData Z P hcU hcR hcRR).projChartHom ≫ P.toSpace))).ker =
      (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P).comap
        ((BigFppfOver.toScheme B S hS).map
          (blowUpGlueingData Z P hcU hcR hcRR).projChartHom) :=
  (schemeKer_snd_comp B S hS Z P.toSpace
      (blowUpGlueingData Z P hcU hcR hcRR).projChartHom).trans
    (congrArg (fun J => J.comap ((BigFppfOver.toScheme B S hS).map
        (blowUpGlueingData Z P hcU hcR hcRR).projChartHom))
      (ker_rep_snd_eq_reesChartIdeal B S hS X Z P))

/-- **The membership half of Stacks 085U.**  The inverse image of the centre `Z` along the
blowing up `b : X' ⟶ X` of `X` along `Z` is an effective Cartier divisor on `X'`; equivalently,
`b` is an object of the category `𝒞` of Tag 085U.

The blowup has `P_U` for a surjective étale scheme chart, so part (2) of Tag 083C reduces the
assertion to one ideal sheaf of the scheme `P_U`, and
`AlgebraicGeometry.Space.ker_rep_snd_blowUpChart` identifies that ideal sheaf with the inverse
image of the Rees chart ideal along `P_U ⟶ U`.  The hypothesis `hE` is the scheme-level
assertion of Tag 02OS part (2) for the relative `Proj` of the Rees algebra of that ideal; see
`AlgebraicGeometry.Space.isPullbackDefined_blowUpAlongHom'_of_iso` for the form in which only a
comparison of the two constructions of the blowup of a scheme is needed. -/
theorem isPullbackDefined_blowUpAlongHom'
    (hE : Stacks.Divisors.IsEffectiveCartierDivisor
      ((reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P).comap
        (reesChartSituation (centreIdeal Z)
          (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProjToBase)) :
    IsPullbackDefined B S hS (blowUpAlongHom' Z P hcU hcR hcRR) Z := by
  have hcomp : (blowUpGlueingData Z P hcU hcR hcRR).chart ≫
      (blowUpGlueingData Z P hcU hcR hcRR).toBase =
      yoneda.map (blowUpGlueingData Z P hcU hcR hcRR).projChartHom ≫ P.toSpace :=
    (blowUpGlueingData Z P hcU hcR hcRR).chart_comp_toBase
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      (Z.2.2.rep.snd (yoneda.map (blowUpGlueingData Z P hcU hcR hcRR).projChartHom ≫
        P.toSpace))) := Z.2.2.property_snd _
  refine isEffectiveCartierDivisor_of_hasEffectiveCartierEtaleCover B S hS _ _
    ⟨(blowUpGlueingData Z P hcU hcR hcRR).projChart, (blowUpGlueingData Z P hcU hcR hcRR).chart,
      isEtale_of_presheaf_etale B S hS (blowUpGlueingData Z P hcU hcR hcRR).chart_etale,
      isSurjective_of_presheafSurjective B S hS _
        (blowUpGlueingData Z P hcU hcR hcRR).chart_surjective, ?_⟩
  have hj : (Z.1.preimage (blowUpAlongHom' Z P hcU hcR hcRR).hom).preimage
        (blowUpGlueingData Z P hcU hcR hcRR).chart =
      Subfunctor.range (yoneda.map (Z.2.2.rep.snd
        (yoneda.map (blowUpGlueingData Z P hcU hcR hcRR).projChartHom ≫ P.toSpace))) := by
    change Z.1.preimage ((blowUpGlueingData Z P hcU hcR hcRR).chart ≫
      (blowUpGlueingData Z P hcU hcR hcRR).toBase) = _
    rw [hcomp]
    exact preimage_eq_range_rep_snd B S hS X Z _
      (yoneda.map (blowUpGlueingData Z P hcU hcR hcRR).projChartHom ≫ P.toSpace)
  exact (isSchemeEffectiveCartierPullback_iff_ker B S hS _ _ _ _ _ _ hj).2
    (ker_rep_snd_blowUpChart Z P hcU hcR hcRR ▸ hE)

/-- **The membership half of Stacks 085U, from the comparison of the two constructions of the
blowup of a scheme.**  If the relative `Proj` of the Rees algebra sheaf of the chart ideal is
isomorphic, over the presenting scheme, to the blowup `Stacks.Blowup.blowUp` of that ideal as
the library builds it, then the inverse image of the centre along the blowing up of `X` along
`Z` is an effective Cartier divisor.

The comparison is the analogue for `Stacks.Blowup.reesSituation` of
`AlgebraicGeometry.reesDataIso`; it carries no divisor content, and Tag 02OS part (2) for the
blowup of a scheme supplies the rest through
`Stacks.Blowup.isEffectiveCartierDivisor_comap_relativeProjToBase_of_iso`. -/
theorem isPullbackDefined_blowUpAlongHom'_of_iso
    (e : (reesChartSituation (centreIdeal Z)
          (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj ≅
        Stacks.Blowup.blowUp
          (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P))
    (he : e.hom ≫ Stacks.Blowup.blowUpToBase
          (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P) =
        (reesChartSituation (centreIdeal Z)
          (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProjToBase) :
    IsPullbackDefined B S hS (blowUpAlongHom' Z P hcU hcR hcRR) Z :=
  isPullbackDefined_blowUpAlongHom' Z P hcU hcR hcRR
    (Stacks.Blowup.isEffectiveCartierDivisor_comap_relativeProjToBase_of_iso _ e he)

/-- **The membership half of Stacks 085U.**  The exceptional divisor `b⁻¹(Z)` of the blowing up
`b : X' ⟶ X` of an algebraic space `X` along a closed subspace `Z ⊆ X` is an effective Cartier
divisor on `X'`; equivalently, `b` is an object of the category `𝒞` of Tag 085U.

The scheme-level input `hE` of `AlgebraicGeometry.Space.isPullbackDefined_blowUpAlongHom'` is
`Stacks.Blowup.isCartierOver_relativeProjToBase_reesSituation`, so nothing is left to assume:
the divisor content is Tag 02OS part (2) for the blowup of the *scheme* `U` in the Rees chart
ideal, and étale descent along the chart `P_U ⟶ X'` carries it to the algebraic space.
Finality, the other half of Tag 085U, is
`AlgebraicGeometry.Space.existsUnique_lift_blowUpAlongHom'`, and the two halves are assembled by
`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'`, which is where Tag 085U is registered:
this statement is `AlgebraicGeometry.Space.IsBlowupAlong.isPullbackDefined` of it, so it carries
no tag of its own. -/
theorem isEffectiveCartierDivisor_exceptionalDivisor' :
    IsEffectiveCartierDivisor B S hS (blowUpAlong' Z P hcU hcR hcRR)
      (exceptionalDivisor' Z P hcU hcR hcRR) :=
  isPullbackDefined_blowUpAlongHom' Z P hcU hcR hcRR
    (Stacks.Blowup.isCartierOver_relativeProjToBase_reesSituation _)

end AlgebraicGeometry.Space

end
