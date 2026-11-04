module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFinality
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase

/-!
# Reducedness of a blowup of an algebraic space, with the chart hypothesis discharged

`StacksFrontier/AlgebraicGeometry/Spaces/BlowupReduced.lean` proves reducedness of a blowup of a
reduced algebraic space from an étale chart on which the blowup is representable by a scheme
blowup.  This file produces that chart from the construction of Stacks 085Q and so states
Stacks 085W on the source's own hypotheses alone.

## Main results

* `AlgebraicGeometry.Space.isReduced_of_isBlowupAlong_of_presentation` is **Stacks 085W**: the
  blowup of a reduced algebraic space in a closed subspace is reduced.

## Implementation notes

The chart is the one the construction of Stacks 085Q supplies.  That construction is
`AlgebraicGeometry.Space.blowUpAlong'` and `AlgebraicGeometry.Space.blowUpAlongHom'` of
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupEquivalenceRelationClosed.lean`, and it comes with a
surjective étale *scheme* chart `P_U ⟶ X'`,
`AlgebraicGeometry.Space.RelativeProjGlueingData.chart` for the datum
`AlgebraicGeometry.Space.blowUpGlueingData`, where `P_U` is the relative `Proj` of the Rees
algebra of the chart ideal on the presenting scheme `U`.  So no base change is needed: `U` is
reduced because it is an étale chart of the reduced `X`
(`AlgebraicGeometry.Space.exists_atlas_iff_forall_etale`), `P_U` is the blowup of the scheme `U`
by `Stacks.Blowup.reesSituationBlowUpIso` and hence reduced by Stacks 0808, and the chart
`P_U ⟶ X'` exhibits the constructed blowup as reduced directly from the definition of
`AlgebraicGeometry.Space.HasEtaleLocalProperty`.  An arbitrary blowup `b` of `X` in `Z` is
isomorphic over `X` to the constructed one, because the construction is a final object of the
category of Stacks 085U (`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'`), and an
isomorphism is surjective and flat, so Stacks 06MI transports reducedness to it.

Besides `Z`, the blowup `b` and reducedness of `X` the statement takes only the data the
construction of Stacks 085Q itself takes: an étale presentation `P` of `X`, the universe choice
`HasSheafify` for the quotient presheaf, and the three `B.Contains` side conditions on the
relative `Proj`s which `AlgebraicGeometry.Space.relativeProjChartOfSituation` already asks for.
None of it appears in the conclusion, and nothing is assumed about `Z` or `b` beyond the
source's own hypotheses.

## References

* [Stacks Project, Tag 085W](https://stacks.math.columbia.edu/tag/085W)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 0808](https://stacks.math.columbia.edu/tag/0808)
* [Stacks Project, Tag 06MI](https://stacks.math.columbia.edu/tag/06MI)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 085W.**  Let `X` be an algebraic space over `S` and let `Z ⊆ X` be the closed
subspace cut out by a quasi-coherent sheaf of ideals.  If `X` is reduced then so is the blowup
`b : X' ⟶ X` of `X` in `Z`.

Nothing about the blowup is assumed beyond its universal property, Stacks 085U: the étale chart
of `X'` the proof runs on is the one the construction of Stacks 085Q supplies, namely the
relative `Proj` `P_U` of the Rees algebra of the chart ideal on the presenting scheme `U` of the
presentation `P`.  That scheme is the blowup of the *scheme* `U`, by
`Stacks.Blowup.reesSituationBlowUpIso`, so it is reduced by Stacks 0808; `P_U ⟶ X'` is
surjective étale, so Stacks 06MI carries reducedness to the constructed blowup, and from there
to `b` along the isomorphism of any two blowups in the same centre.

Besides `Z`, the blowup `b` and reducedness of `X` the statement takes only the data the
construction of Stacks 085Q itself takes: the presentation `P`, the universe choice
`HasSheafify` for the quotient presheaf, and the three `B.Contains` side conditions on the
relative `Proj`s which `AlgebraicGeometry.Space.relativeProjChartOfSituation` already asks for.
None of that appears in the conclusion. -/
@[stacks 085W "the blowup of a reduced algebraic space in a closed subspace is reduced, with \
no assumed inputs beyond the Stacks 085Q construction data — the étale presentation P of the \
space, the HasSheafify universe choice for the quotient presheaf, and the three B.Contains size \
conditions on the relative Projs of the chart, relation and double situations — none of which \
occurs in the conclusion"]
theorem isReduced_of_isBlowupAlong_of_presentation
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.obj)
    (P : Presentation B S hS X.obj X.property)
    (hcU : B.Contains (reesChartSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
    (hcR : B.Contains (reesRelationSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
    (hcRR : B.Contains (reesDoubleSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
    {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsReduced T)) :
    HasEtaleLocalProperty B S hS X'.1 (fun T : Scheme.{u} => IsReduced T) := by
  have hUred : IsReduced ((BigFppfOver.toScheme B S hS).obj P.U) :=
    (exists_atlas_iff_forall_etale B S hS X.1 (fun T : Scheme.{u} => IsReduced T) X.2).mp hX
      P.U P.toSpace P.etale
  have hblowUpRed : IsReduced (AlgebraicGeometry.blowUp
      (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P)) :=
    isReduced_blowUp _
  have hprojRed : IsReduced (reesChartSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj :=
    isReduced_of_isOpenImmersion (Stacks.Blowup.reesSituationBlowUpIso _).hom
  have hchartSituationRed :
      IsReduced (blowUpGlueingData Z P hcU hcR hcRR).chartSituation.relativeProj := hprojRed
  have hchartRed : IsReduced ((BigFppfOver.toScheme B S hS).obj
      (blowUpGlueingData Z P hcU hcR hcRR).projChart) :=
    isReduced_of_isOpenImmersion (blowUpGlueingData Z P hcU hcR hcRR).projChartIso.hom
  have hblow : HasEtaleLocalProperty B S hS (blowUpAlong' Z P hcU hcR hcRR).1
      (fun T : Scheme.{u} => IsReduced T) :=
    ⟨(blowUpGlueingData Z P hcU hcR hcRR).projChart,
      (blowUpGlueingData Z P hcU hcR hcRR).chart,
      (blowUpGlueingData Z P hcU hcR hcRR).chart_surjective,
      (blowUpGlueingData Z P hcU hcR hcRR).chart_etale, hchartRed⟩
  obtain ⟨e, -⟩ := (isBlowupAlong_blowUpAlongHom' Z P hcU hcR hcRR).exists_iso hb
  have : IsIso e.hom.hom :=
    Iso.isIso_hom ((ObjectProperty.ι
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)).mapIso e)
  exact isReduced_of_flat_of_surjective B S hS (blowUpAlong' Z P hcU hcR hcRR).2 X'.2 e.hom.hom
    (isFlat_of_isEtale B S hS (isEtale_of_isIso B S hS e.hom.hom))
    (isSurjective_of_isIso B S hS e.hom.hom) hblow

end AlgebraicGeometry.Space

end
