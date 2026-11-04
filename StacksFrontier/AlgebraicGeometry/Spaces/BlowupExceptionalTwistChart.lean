module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneExceptionalIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupExceptionalCartier

/-!
# The twisting sheaf and the exceptional divisor on a chart of the blowup of an algebraic space

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S`, let
`Z ⊆ X` be a closed subspace and let `b : X' ⟶ X` be the blowing up of `X` along `Z` of Stacks
085Q, the relative `Proj` of the Rees algebra of the defining ideal sheaf of `Z` constructed in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupRelativeProj.lean`.  Part (3) of Stacks 085T says
that there is a canonical isomorphism `𝒪_{X'}(-1) = 𝒪_{X'}(E)` between the inverse of the first
twisting sheaf of that relative `Proj` and the invertible sheaf of the exceptional divisor
`E = b⁻¹(Z)`.

The source proves all three parts of Stacks 085T by base change to a surjective étale scheme
chart, which reduces each of them to the case of schemes, Stacks 02OS.  This file carries out
that reduction for part (3): the chart `P_U ⟶ X'` that the construction of Stacks 085Q supplies
is the blowup of the presenting scheme `U` of the étale presentation in the induced sheaf of
ideals `ℐ|_U`, the canonical base change of `E` to it is the exceptional divisor of that scheme
blowup, and so the twisting sheaf `𝒪(1)` there is its ideal sheaf.  Dualising, `𝒪(-1)` on the
chart is the invertible sheaf of the base change of `E`, which is part (3) read on the chart.

**Part (3) itself is not stated**, because `𝒪_{X'}(n)` does not exist in this library for the
algebraic space `X'`.  The section "Where this stops" below says exactly what is missing and
names each missing input by tag number.

## Main results

* `AlgebraicGeometry.Space.ker_rep_snd_chart_exceptionalDivisor`: **the exceptional divisor of
  the blowup of an algebraic space is, on the chart, the exceptional divisor of the blowup of the
  chart.**  The ideal sheaf of the canonical base change of `E = b⁻¹(Z)` to `P_U` is the inverse
  image `ℐ|_U · 𝒪_{P_U}` of the centre along the structure morphism of `P_U` over `U`.
* `AlgebraicGeometry.Space.ker_rep_snd_chart_exceptionalDivisor_comap` and
  `AlgebraicGeometry.Space.comap_ker_rep_snd_chart_exceptionalDivisor`: the same identification
  carried across the comparison of the two Rees constructions of this repository, in each
  direction.
* `AlgebraicGeometry.Space.comap_hom_comap_inv`: taking the inverse image of a sheaf of ideals
  along an isomorphism of schemes and then along its inverse changes nothing.
* `AlgebraicGeometry.Space.chartTwistOneIsoExceptionalDivisorIdealSheaf`: **part (3) of Stacks
  085T, read on the chart `P_U`.**  The twisting sheaf `𝒪(1)` of the blowup of `U` in `ℐ|_U` is
  the ideal sheaf of the canonical base change of the exceptional divisor of the blowup of the
  algebraic space, carried along that comparison.

## The shape of the proof

Three inputs meet here.

1. **The chart identification.**  The exceptional divisor is `b⁻¹(Z)`, so its base change to
   `P_U` is the base change of `Z` along `P_U ⟶ U ⟶ X`, which is the inverse image along
   `P_U ⟶ U` of the base change of `Z` to `U`; and the ideal sheaf of the latter is the sheaf of
   ideals `ℐ|_U` that the construction forms the Rees algebra of.  That is
   `AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart` together with
   `AlgebraicGeometry.Space.schemeKer_snd_preimage` and
   `AlgebraicGeometry.Space.schemeKer_snd_comp`, exactly as in the proof of part (2) in
   `StacksFrontier/AlgebraicGeometry/Spaces/BlowupExceptionalCartier.lean`.  It is factored out
   here as a statement in its own right, since part (3) needs it as an equality of sheaves of
   ideals and not only inside a proof.
2. **The comparison of the two Rees constructions.**  This repository builds the Rees algebra of
   a quasi-coherent sheaf of ideals twice.  `Stacks.Blowup.reesSituation` is assembled from the
   explicitly given `Stacks.Blowup.reesAlgebraData`, and `AlgebraicGeometry.Space.reesChartSituation`
   — the situation whose relative `Proj` is the chart `P_U` — is that one.
   `AlgebraicGeometry.reesSituation` is assembled from `AlgebraicGeometry.reesAlgebraData`, which
   is `Classical.choice` of an existence statement, and its relative `Proj` is
   `AlgebraicGeometry.blowUp`, which every geometric fact about blowups of schemes in this
   repository — including Stacks 02OS part (3) — is proved for.  The two are *not*
   definitionally equal, and the identification is
   `Stacks.Blowup.reesSituationBlowUpIso`, an isomorphism over the base
   (`Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase`).  Everything below is transported
   along it, the same device by which part (2) of Stacks 02OS is made available for
   `Stacks.Blowup.reesSituation` in
   `Stacks.Blowup.isCartierOver_relativeProjToBase_reesSituation`.
3. **For a scheme it is Stacks 02OS (3).**  `AlgebraicGeometry.twistOneIsoExceptionalIdealModule`
   says that the twisting sheaf `𝒪(1)` of the blowup of a scheme in a quasi-coherent sheaf of
   ideals is the ideal sheaf of its exceptional divisor, for an arbitrary scheme and an arbitrary
   quasi-coherent sheaf of ideals.

## Where this stops, and what is missing

Part (3) is an isomorphism of sheaves of modules **on `X'`**, and only one of its two sides
exists for an algebraic space in this library.

* `𝒪_{X'}(E)` does exist.  `AlgebraicGeometry.Space.associatedInvertibleSheaf` is `𝓘_E^{⊗ -1}`
  for an effective Cartier divisor on an algebraic space, which is Stacks 0841 part (1), and
  part (2) of Stacks 085T —
  `AlgebraicGeometry.Space.isEffectiveCartierDivisor_exceptionalDivisor_blowUpAlong` — supplies
  the hypothesis it takes.  So the right-hand side of part (3) is available.
* `𝒪_{X'}(-1)` does **not**.  The twisting sheaves of the relative `Proj` of an algebraic space
  are **Stacks 084D**, and the only form of 084D in this library is
  `AlgebraicGeometry.Space.RelativeProjSheafGlueingData.exists_twist` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjTwists.lean`, which
  - is an *existence* statement — a family of quasi-coherent modules on `Proj_X(𝒜)` whose chart
    restrictions are the chart twists — and so names no particular `𝒪_{X'}(n)` that part (3)
    could be an isomorphism out of;
  - carries as hypotheses a descent datum for the chart twists and the essential-surjectivity
    half of Stacks 03M3; and
  - is stated over the `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`
    formalization of Situation 01NN, whereas the blowup of Stacks 085Q is built over
    `Stacks.RelativeProj.Situation`.  The two share no declarations and the only bridge between
    them runs from the sheaf-level datum to the affine-open one, which is the direction that
    does not help; this is recorded in the implementation notes of `RelativeProjTwists.lean`.

**What is *not* missing is the descent theorem.**  Stacks 03M3 is proved here for an
algebraic-space target, both halves and at the hypotheses of the source:
`AlgebraicGeometry.Space.isEquivalence_quasicoherentFromSpaceBase` and
`AlgebraicGeometry.Space.equivalenceQuasicoherentFromSpaceBase` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasicoherentFromSpaceBaseEquivalence.lean` say
that `ℱ ↦ (φ^*ℱ, α)` is an equivalence from the quasi-coherent `𝒪_X`-modules to the
quasi-coherent modules on the groupoid of a presentation, for `φ` étale, surjective, relatively
representable and with the arrow space its kernel pair.  The chart of the blowup satisfies all
four — `AlgebraicGeometry.Space.RelativeProjGlueingData.chart_etale`, `…chart_surjective` and
`…chart_isKernelPair`.  So neither half of 03M3 is an obstruction, and the
`IsEffectiveEtaleDescent` binder of `exists_twist` is in principle dischargeable; what stands in
the way of using one for the other is only that the two state "quasi-coherent module on a
groupoid" in different formalizations — `AlgebraicGeometry.Space.QuasicoherentModule` for a
groupoid in algebraic spaces against `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule` for a
groupoid scheme — which needs a comparison of the two.

Closing the gap needs, by tag number:

* **Stacks 01O3** at the chart: the pullbacks of the twisting sheaves `𝒪_{P_U}(n)` along the two
  legs of the relation `P_R ⇉ P_U` are the twisting sheaves `𝒪_{P_R}(n)`, and the resulting
  comparison satisfies the cocycle law and the normalisation along the identity.  That is what
  makes `𝒪_{P_U}(1)` a quasi-coherent module on the groupoid of the presentation, and with it
  **Stacks 084D** for the blowup follows from the essential-surjectivity half of Stacks 03M3
  above.  Stacks 01O3 has one registration in the tree,
  `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.relativeProj_baseChange_twist`, and it
  is not enough for two reasons: it supplies the base-change isomorphism `r` and the comparison
  `θ` of the twisting algebras, but not their cocycle law over `R ×_U R` nor their normalisation
  along the diagonal of `R` — exactly the two conditions whose absence the
  `projIsEquivalenceRelation` field of the glueing datum of Stacks 085Q records for the relative
  `Proj`s themselves — and it is stated for a
  `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, not for a
  `Stacks.RelativeProj.Situation`, so it does not even type against the chart of the blowup.  No
  declaration assembles the descent datum; `RelativeProjTwists.lean` carries it as the
  hypothesis
  `AlgebraicGeometry.Space.RelativeProjSheafGlueingData.HasTwistDescentDatum`.
* **Stacks 03M4**, via **Stacks 03DW**, for quasi-coherence of the defining ideal sheaf of a
  closed subspace on the small étale site.  `AlgebraicGeometry.Space.definingIdealSheaf` does not
  assert it, and its own module documentation records the obstruction.  Without it `𝓘_E` is not
  an object of `AlgebraicGeometry.Space.QuasicoherentSheaves` at all, so it is not in the source
  of the equivalence of Stacks 03M3; and the restriction of `𝓘_E` to the chart cannot be
  compared with the scheme-level ideal sheaf of its base change, so not even the chart form of
  part (3) can be stated with the restriction of `𝓘_E` itself on the right-hand side.  What
  appears below is the scheme-level ideal sheaf of the base change, which is what the chart
  identification produces.
* The compatibility of the isomorphism of **Stacks 02OS** (3) with those two descent data — that
  is, that the chart isomorphism proved below is a morphism of quasi-coherent modules on the
  groupoid of the presentation.  This is the content of the word "canonical" in part (3), and it
  is what the full-faithfulness half of Stacks 03M3 then turns into an isomorphism on `X'`; the
  chart isomorphism on its own does not descend, since two quasi-coherent `𝒪_{X'}`-modules with
  isomorphic chart restrictions need not be isomorphic.  Nothing in this library proves it.
* **Stacks 084B**, relative `Proj` base change for algebraic spaces, which the glueing datum of
  Stacks 085Q carries as a hypothesis rather than proves — it is the parameter `heq` together
  with the two cartesian fields.  It has no registration in the tree.

No `@[stacks 085T]` attribute is attached to anything in this file.  The declarations below
state the chart form of part (3), not part (3), and part (3) is an assertion about sheaves of
modules on `X'`.  Parts (1) and (2) of Stacks 085T are registered elsewhere:
`AlgebraicGeometry.Space.isIso_fromPreimage_openComplement` in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupIsomorphismOffCentre.lean` states part (1), that the
blowup is an isomorphism over the open complement of the centre, and
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_exceptionalDivisor_blowUpAlong` in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupExceptionalCartier.lean` states part (2), that the
exceptional divisor is an effective Cartier divisor on the blowup.

## References

* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 03M4](https://stacks.math.columbia.edu/tag/03M4)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  (Z : ClosedSubspaces B S hS X.obj) (P : Presentation B S hS X.obj X.property)
  (hcU : B.Contains (reesChartSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (hcR : B.Contains (reesRelationSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (heq : CategoryTheory.IsEquivalenceRelation
      ((Over.post B.inclusion).map (reesProjTarget (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR)))

/-- **The exceptional divisor of the blowup of an algebraic space is, on the chart, the
exceptional divisor of the blowup of the chart.**  Let `b : X' ⟶ X` be the blowing up of an
algebraic space `X` along a closed subspace `Z` of Stacks 085Q and let `P_U ⟶ X'` be the
surjective étale scheme chart the construction supplies, the relative `Proj` of the Rees algebra
of the sheaf of ideals `ℐ|_U` induced on the presenting scheme `U` of the étale presentation.
Then the ideal sheaf of the canonical base change of the exceptional divisor `b⁻¹(Z)` to `P_U` is
the inverse image `ℐ|_U · 𝒪_{P_U}` of the centre along the structure morphism of `P_U` over `U`.

The base change of `b⁻¹(Z)` to `P_U` is the base change of `Z` along `P_U ⟶ U ⟶ X`, hence the
inverse image along `P_U ⟶ U` of the base change of `Z` to `U`, whose ideal sheaf is `ℐ|_U`.
This is the computation inside the proof of part (2) of Stacks 085T in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupExceptionalCartier.lean`, stated on its own. -/
theorem ker_rep_snd_chart_exceptionalDivisor :
    ((BigFppfOver.toScheme B S hS).map
        ((exceptionalDivisor Z P hcU hcR heq).2.2.rep.snd
          (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
            P hcU hcR heq).chart)).ker =
      (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P).comap
        (Stacks.RelativeProj.Situation.relativeProjToBase
          (Stacks.Blowup.reesSituation
            (reesChartIdeal (centreIdeal Z)
              (isCartesianOnAffineCharts_centreIdeal Z) P))) := by
  set d := reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
    P hcU hcR heq with hd
  have hchartE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) d.chart := d.chart_etale
  have hproj : (BigFppfOver.toScheme B S hS).map d.projChartHom =
      Stacks.RelativeProj.Situation.relativeProjToBase
        (Stacks.Blowup.reesSituation
          (reesChartIdeal (centreIdeal Z)
            (isCartesianOnAffineCharts_centreIdeal Z) P)) := rfl
  have hker : ((BigFppfOver.toScheme B S hS).map
        ((exceptionalDivisor Z P hcU hcR heq).2.2.rep.snd d.chart)).ker =
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd (d.chart ≫ d.toBase))).ker :=
    schemeKer_snd_preimage B S hS (blowUpAlongHom Z P hcU hcR heq) Z
      ⟨CostructuredArrow.mk d.chart, hchartE⟩
  rw [d.chart_comp_toBase, schemeKer_snd_comp B S hS Z d.presentation.toSpace d.projChartHom,
    hproj] at hker
  have hchartIdeal :
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd d.presentation.toSpace)).ker =
      reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P :=
    ker_rep_snd_eq_idealSheafDataOfChart B S hS X Z (presentationChart P)
  rw [hchartIdeal] at hker
  exact hker

/-- **The exceptional divisor on the chart, read through the comparison of the two Rees
constructions.**  The ideal sheaf of the canonical base change of the exceptional divisor
`b⁻¹(Z)` to the chart `P_U` is the inverse image along
`Stacks.Blowup.reesSituationBlowUpIso` of the exceptional ideal of
`AlgebraicGeometry.blowUp (ℐ|_U)`.

The comparison is an isomorphism over the base, so composing it with the blowup morphism of
`AlgebraicGeometry.blowUp (ℐ|_U)` gives the structure morphism of `P_U` over `U`. -/
theorem ker_rep_snd_chart_exceptionalDivisor_comap :
    ((BigFppfOver.toScheme B S hS).map
        ((exceptionalDivisor Z P hcU hcR heq).2.2.rep.snd
          (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
            P hcU hcR heq).chart)).ker =
      (AlgebraicGeometry.exceptionalIdeal
          (reesChartIdeal (centreIdeal Z)
            (isCartesianOnAffineCharts_centreIdeal Z) P)).comap
        (Stacks.Blowup.reesSituationBlowUpIso
          (reesChartIdeal (centreIdeal Z)
            (isCartesianOnAffineCharts_centreIdeal Z) P)).hom := by
  rw [ker_rep_snd_chart_exceptionalDivisor Z P hcU hcR heq,
    ← Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase
      (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P),
    Scheme.IdealSheafData.comap_comp]

/-- **Taking the inverse image of a sheaf of ideals along an isomorphism and then along its
inverse changes nothing.** -/
theorem comap_hom_comap_inv {Y W : Scheme.{u}} (e : Y ≅ W) (I : W.IdealSheafData) :
    (I.comap e.hom).comap e.inv = I := by
  rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

/-- **The exceptional divisor of the blowup of the chart, read from the algebraic space.**  The
exceptional ideal of `AlgebraicGeometry.blowUp (ℐ|_U)` is the inverse image along the inverse of
`Stacks.Blowup.reesSituationBlowUpIso` of the ideal sheaf of the canonical base change of the
exceptional divisor `b⁻¹(Z)` to the chart `P_U`.  This is
`AlgebraicGeometry.Space.ker_rep_snd_chart_exceptionalDivisor_comap` read in the other
direction. -/
theorem comap_ker_rep_snd_chart_exceptionalDivisor :
    (((BigFppfOver.toScheme B S hS).map
        ((exceptionalDivisor Z P hcU hcR heq).2.2.rep.snd
          (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
            P hcU hcR heq).chart)).ker).comap
        (Stacks.Blowup.reesSituationBlowUpIso
          (reesChartIdeal (centreIdeal Z)
            (isCartesianOnAffineCharts_centreIdeal Z) P)).inv =
      AlgebraicGeometry.exceptionalIdeal
        (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P) := by
  exact (congrArg
      (fun I : ((BigFppfOver.toScheme B S hS).obj
          (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
            P hcU hcR heq).projChart).IdealSheafData =>
        I.comap (Stacks.Blowup.reesSituationBlowUpIso
          (reesChartIdeal (centreIdeal Z)
            (isCartesianOnAffineCharts_centreIdeal Z) P)).inv)
      (ker_rep_snd_chart_exceptionalDivisor_comap Z P hcU hcR heq)).trans
    (comap_hom_comap_inv _ _)

/-- **Stacks 085T part (3), read on the étale chart of the blowup.**  Let `b : X' ⟶ X` be the
blowing up of an algebraic space `X` along a closed subspace `Z` of Stacks 085Q, with exceptional
divisor `E = b⁻¹(Z)`, and let `P_U ⟶ X'` be the surjective étale scheme chart the construction
supplies, the blowup of the presenting scheme `U` of the étale presentation in the induced sheaf
of ideals `ℐ|_U`.  Then the twisting sheaf `𝒪(1)` of that scheme blowup is the ideal sheaf of the
canonical base change of `E` to the chart, carried along the comparison
`Stacks.Blowup.reesSituationBlowUpIso` of the two Rees constructions of this repository.
Dualising, `𝒪(-1)` there is the invertible sheaf of that base change, an effective Cartier
divisor by part (2).

This is the reduction to the case of schemes by which the source proves part (3): the chart is
the blowup of `U` in `ℐ|_U`, the base change of `E` there is its exceptional divisor
(`AlgebraicGeometry.Space.comap_ker_rep_snd_chart_exceptionalDivisor`), and for a scheme the
statement is Stacks 02OS part (3), `AlgebraicGeometry.twistOneIsoExceptionalIdealModule`, with no
hypothesis on the scheme or on the sheaf of ideals.

Part (3) itself — an isomorphism of sheaves of modules on `X'` — is not this statement: it is
`AlgebraicGeometry.Space.blowUpTwistSpaceNegOneIsoAssociatedInvertibleSheaf`, obtained by descending
the scheme-level isomorphism from `P_U` to `X'` along Stacks 03M3
(`StacksFrontier/AlgebraicGeometry/Spaces/BlowupTwistDescent.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupTwistDescentCanonical.lean`). -/
def chartTwistOneIsoExceptionalDivisorIdealSheaf :
    AlgebraicGeometry.blowUpTwist
        (reesChartIdeal (centreIdeal Z)
          (isCartesianOnAffineCharts_centreIdeal Z) P) 1 ≅
      Stacks.ClosedImmersion.idealSheaf
        ((((BigFppfOver.toScheme B S hS).map
            ((exceptionalDivisor Z P hcU hcR heq).2.2.rep.snd
              (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
                P hcU hcR heq).chart)).ker).comap
          (Stacks.Blowup.reesSituationBlowUpIso
            (reesChartIdeal (centreIdeal Z)
              (isCartesianOnAffineCharts_centreIdeal Z) P)).inv).subschemeι.toLRSHom.toShHom := by
  rw [comap_ker_rep_snd_chart_exceptionalDivisor Z P hcU hcR heq]
  exact AlgebraicGeometry.twistOneIsoExceptionalIdealModule _

end AlgebraicGeometry.Space

end
