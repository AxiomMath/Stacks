module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupRelativeProj
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv

/-!
# The exceptional divisor of the blowup of an algebraic space is an effective Cartier divisor

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S`, let
`Z ⊆ X` be a closed subspace and let `b : X' ⟶ X` be the blowing up of `X` along `Z` of Stacks
085Q, the relative `Proj` of the Rees algebra of the defining ideal sheaf of `Z` constructed in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupRelativeProj.lean`.  Stacks 085T part (2) says that
the exceptional divisor `b⁻¹(Z) ⊆ X'` is an effective Cartier divisor on `X'`.  This file proves
it, `AlgebraicGeometry.Space.isEffectiveCartierDivisor_exceptionalDivisor_blowUpAlong`.

## Main results

* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_exceptionalDivisor_blowUpAlong` is **Stacks
  085T part (2)** for the blowup of Stacks 085Q.

## The shape of the proof

Four inputs meet here.

1. **One surjective étale chart suffices.** Stacks 083C (2) ⟹ (1),
   `AlgebraicGeometry.Space.isEffectiveCartierDivisor_of_hasEffectiveCartierEtaleCover`, reduces
   effective Cartier-ness of a closed subspace of `X'` to effective Cartier-ness of its inverse
   image on a single surjective étale scheme chart of `X'`.
2. **The construction provides such a chart.** The blowup is glued from the relative `Proj` `P_U`
   of the Rees algebra on the presenting scheme `U` of an étale presentation of `X`, and
   `AlgebraicGeometry.Space.RelativeProjGlueingData.chart` is a surjective étale chart
   `P_U ⟶ X'` whose composite with `b` is `P_U ⟶ U ⟶ X`
   (`AlgebraicGeometry.Space.RelativeProjGlueingData.chart_comp_toBase`).
3. **The inverse image of `Z` on that chart is the inverse image of the centre of the scheme
   blowup.** The exceptional divisor is `b⁻¹(Z)`, so its base change to `P_U` is the base change
   of `Z` along `P_U ⟶ U ⟶ X`, which is the inverse image along `P_U ⟶ U` of the base change of
   `Z` to `U`; and the ideal sheaf of the latter is the sheaf of ideals `𝓘_Z|_U` that the
   construction forms the Rees algebra of.  That identification is
   `AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart` together with
   `AlgebraicGeometry.Space.schemeKer_snd_preimage` and
   `AlgebraicGeometry.Space.schemeKer_snd_comp`.
4. **For a scheme it is Stacks 02OS (2).**
   `Stacks.Blowup.isCartierOver_relativeProjToBase_reesSituation` says that the inverse image of
   an ideal sheaf `I` of a scheme along the structure morphism of the relative `Proj` of its Rees
   algebra is an effective Cartier divisor — exactly for the model
   `Stacks.Blowup.reesSituation` that the space blowup is built from.

## Implementation notes

The closed-subscheme presentation that Stacks 083C (2) asks for — an object of the site, a
morphism from it to the chart and an identification with the subscheme cut out by the ideal
sheaf — is supplied by
`AlgebraicGeometry.Space.ker_eq_iff_exists_closedSubschemePresentation` applied to the ideal
sheaf of the canonical base change of the exceptional divisor to the chart, which is an object of
the site because the inclusion of a closed subspace is relatively representable.  So no further
containment assumption on the big fppf site is made: the three parameters `hcU`, `hcR` and `heq`
are those of the construction of Stacks 085Q itself.

The étaleness and surjectivity that `AlgebraicGeometry.Space.HasEffectiveCartierEtaleCover` wants
are the notions of Stacks 03FR and 03ME for a morphism of algebraic spaces, while the chart of
the glueing datum comes with the relatively representable forms; the two are bridged by
`AlgebraicGeometry.Space.isEtale_of_presheaf_etale` and
`AlgebraicGeometry.Space.isSurjective_of_presheafSurjective`.

`AlgebraicGeometry.Space.isEffectiveCartierDivisor_exceptionalDivisor` in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupIsomorphismOffCentre.lean` is a different statement
with the same mathematical content: it reads off the effective Cartier condition from
`AlgebraicGeometry.Space.IsBlowupAlong`, the universal property of Stacks 085U, where it is one
half of the definition.  The theorem here is about the *constructed* blowup of Stacks 085Q, for
which nothing is assumed about the inverse image of the centre.

## References

* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

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

/-- **Stacks 085T part (2).** Let `X` be an algebraic space over a scheme `S`, let `Z ⊆ X` be a
closed subspace and let `b : X' ⟶ X` be the blowing up of `X` along `Z` of Stacks 085Q, the
relative `Proj` of the Rees algebra `⨁_{n ≥ 0} 𝓘_Zⁿ`.  Then the exceptional divisor `b⁻¹(Z)` is
an effective Cartier divisor on `X'`.

By Stacks 083C (2) ⟹ (1) it is enough to see this on one surjective étale scheme chart of `X'`,
and the construction supplies one: the relative `Proj` `P_U` of the Rees algebra on the
presenting scheme `U` of the étale presentation, whose composite with `b` is `P_U ⟶ U ⟶ X`.  The
inverse image of `b⁻¹(Z)` there is therefore the inverse image along `P_U ⟶ U` of the closed
subscheme `Z ×_X U` of `U`, whose ideal sheaf is the sheaf of ideals `𝓘_Z|_U` the Rees algebra is
formed from, and for a scheme that inverse image is an effective Cartier divisor by Stacks 02OS
(2).

The parameters `hcU`, `hcR` and `heq` are the ones the blowup of Stacks 085Q is built from: two
containment conditions on the big fppf site and the normalisation and cocycle conditions making
the two projections of the relative `Proj`s an internal equivalence relation. -/
@[stacks 085T "part (2), the exceptional divisor b⁻¹(Z) of the blowup of an algebraic space \
along a closed subspace is an effective Cartier divisor on the blowup"]
theorem isEffectiveCartierDivisor_exceptionalDivisor_blowUpAlong :
    IsEffectiveCartierDivisor B S hS (blowUpAlong Z P hcU hcR heq)
      (exceptionalDivisor Z P hcU hcR heq) := by
  set d := reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
    P hcU hcR heq
  have hchartE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) d.chart := d.chart_etale
  have hchartS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) d.chart := d.chart_surjective
  have hproj : (BigFppfOver.toScheme B S hS).map d.projChartHom =
      (reesChartSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProjToBase := rfl
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
  refine isEffectiveCartierDivisor_of_hasEffectiveCartierEtaleCover B S hS _ _
    ⟨d.projChart, d.chart, isEtale_of_presheaf_etale B S hS hchartE,
      isSurjective_of_presheafSurjective B S hS d.chart hchartS, ?_⟩
  obtain ⟨R, j, e, hmap, hran⟩ :=
    (ker_eq_iff_exists_closedSubschemePresentation B S hS (blowUpAlong Z P hcU hcR heq)
      (exceptionalDivisor Z P hcU hcR heq) d.projChart d.chart _).1 rfl
  exact ⟨_, R, j, e, by
    rw [hker]
    exact Stacks.Blowup.isCartierOver_relativeProjToBase_reesSituation _, hmap, hran⟩

end AlgebraicGeometry.Space

end
