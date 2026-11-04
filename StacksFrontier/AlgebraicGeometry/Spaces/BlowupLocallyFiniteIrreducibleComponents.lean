module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFinality
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationComparison
import StacksFrontier.AlgebraicGeometry.Blowup.Transform.GenericPoints
import StacksFrontier.AlgebraicGeometry.Properties.FiniteIrreducibleComponents
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Local finiteness of the irreducible components of a blowup of an algebraic space

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `Z ⊆ X` be the closed
subspace cut out by a quasi-coherent sheaf of ideals.  Stacks 0BH1 says that if `X` satisfies
the equivalent conditions of Stacks 0BB1 then so does the blowup `b : X' ⟶ X` of `X` in `Z`.

The equivalent conditions of Stacks 0BB1 are spelled in this library by its condition (2),
`AlgebraicGeometry.Space.HasLocallyFiniteIrreducibleComponents`: every quasi-compact open of
every étale scheme chart of the space has finitely many irreducible components.  The four
conditions are proved equivalent in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Normalization.lean`, where the tag of the
source lemma sits.

## Main results

* `AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_of_isBlowupAlong_of_presentation`
  is **Stacks 0BH1**, with no assumed inputs.

## Implementation notes

The proof is the source's, routed exactly as
`AlgebraicGeometry.Space.isReduced_of_isBlowupAlong_of_presentation` (Stacks 085W) routes the
analogous statement for reducedness.  The construction of Stacks 085Q builds the blowup as the
relative `Proj` of the Rees algebra, and it comes with a surjective étale *scheme* chart of the
blowup: `AlgebraicGeometry.Space.RelativeProjGlueingData.chart` for the glueing datum
`AlgebraicGeometry.Space.blowUpGlueingData`, whose chart scheme is isomorphic to the relative
`Proj` of the Rees algebra of the chart ideal on the presenting scheme `U` of a presentation of
`X`.  So:

* `U` has finitely many irreducible components over each of its quasi-compact opens, being an
  étale scheme chart of `X`;
* the scheme blowup of `U` in the chart ideal then has that property, which is
  `AlgebraicGeometry.finite_irreducibleComponents_of_isCompact_blowUp` — the scheme-level case,
  proved from Stacks 0BFM;
* the relative `Proj` of the Rees algebra of the chart ideal *is* that scheme blowup, by
  `Stacks.Blowup.reesSituationBlowUpIso`, and the chart scheme is isomorphic to it, so both
  inherit the property through
  `AlgebraicGeometry.finiteIrreducibleComponents_of_etale` (Stacks 0BAL, an isomorphism being
  étale);
* one surjective étale scheme chart suffices, by conditions (1) and (2) of Stacks 0BB1, which is
  `AlgebraicGeometry.Space.exists_surjective_etale_chart_iff_hasLocallyFiniteIrreducibleComponents`
  — so the constructed blowup satisfies the conditions;
* an arbitrary blowup `b` of `X` in `Z` is isomorphic over `X` to the constructed one, because
  the construction is a final object of the category of Stacks 085U
  (`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'` and
  `AlgebraicGeometry.Space.IsBlowupAlong.exists_iso`), and the conditions transfer along an
  isomorphism of presheaves because an isomorphism is étale.

## What the statement carries

Besides `Z`, the blowup `b` and the hypothesis on `X`, only the data the construction of
Stacks 085Q itself takes: an étale presentation `P` of `X`, the universe choice `HasSheafify`
for the quotient presheaf, and the three `B.Contains` side conditions on the relative `Proj`s
which `AlgebraicGeometry.Space.relativeProjChartOfSituation` already asks for.  None of it
appears in the conclusion, and no hypothesis's conclusion is part of the content.

## References

* [Stacks Project, Tag 0BH1](https://stacks.math.columbia.edu/tag/0BH1)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 0BFM](https://stacks.math.columbia.edu/tag/0BFM)
* [Stacks Project, Tag 0BAL](https://stacks.math.columbia.edu/tag/0BAL)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The condition of Stacks 0BB1 transfers along an isomorphism of presheaves on the big fppf
site: an étale scheme chart of the target becomes an étale scheme chart of the source after
composing with the inverse, an isomorphism being étale. -/
theorem hasLocallyFiniteIrreducibleComponents_of_iso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (hF : HasLocallyFiniteIrreducibleComponents B S hS F) :
    HasLocallyFiniteIrreducibleComponents B S hS G := fun U f hf =>
  hF U (f ≫ e.inv) (isEtale_comp B S hS hf (isEtale_of_isIso B S hS e.inv))

/-- **Stacks 0BH1.**  Let `X` be an algebraic space over `S` and let `Z ⊆ X` be the closed
subspace cut out by a quasi-coherent sheaf of ideals.  If `X` satisfies the equivalent
conditions of Stacks 0BB1 — here its condition (2),
`AlgebraicGeometry.Space.HasLocallyFiniteIrreducibleComponents` — then so does the blowup
`b : X' ⟶ X` of `X` in `Z`.

Nothing about the blowup is assumed beyond its universal property, Stacks 085U: the étale
chart of `X'` the proof runs on is the one the construction of Stacks 085Q supplies, namely the
relative `Proj` `P_U` of the Rees algebra of the chart ideal on the presenting scheme `U` of
the presentation `P`.  That scheme is the blowup of the *scheme* `U`, by
`Stacks.Blowup.reesSituationBlowUpIso`, so every quasi-compact open of it has finitely many
irreducible components by
`AlgebraicGeometry.finite_irreducibleComponents_of_isCompact_blowUp`; `P_U ⟶ X'` is surjective
étale, so conditions (1) and (2) of Stacks 0BB1 carry the condition to the constructed blowup,
and from there to `b` along the isomorphism of any two blowups in the same centre.

Besides `Z`, the blowup `b` and the hypothesis on `X` the statement takes only the data the
construction of Stacks 085Q itself takes: the presentation `P`, the universe choice
`HasSheafify` for the quotient presheaf, and the three `B.Contains` side conditions on the
relative `Proj`s which `AlgebraicGeometry.Space.relativeProjChartOfSituation` already asks for.
None of that appears in the conclusion. -/
@[stacks 0BH1 "the blowup of an algebraic space satisfying the equivalent conditions of \
Stacks 0BB1 in a closed subspace satisfies them too, with no assumed inputs beyond the Stacks \
085Q construction data for the centre -- a presentation P, the HasSheafify universe choice, and \
the three B.Contains side conditions hcU, hcR and hcRR on the relative Projs -- none of which \
occurs in the conclusion"]
theorem hasLocallyFiniteIrreducibleComponents_of_isBlowupAlong_of_presentation
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
    (hX : HasLocallyFiniteIrreducibleComponents B S hS X.1) :
    HasLocallyFiniteIrreducibleComponents B S hS X'.1 := by
  have hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj P.U).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj P.U)) →
        (irreducibleComponents V).Finite :=
    hX P.U P.toSpace ((isEtale_iff_presheaf_of_yoneda B S hS P.toSpace).mpr P.etale)
  have hblowUp := AlgebraicGeometry.finite_irreducibleComponents_of_isCompact_blowUp
    (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P) hU
  have hproj : ∀ V : (reesChartSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj.Opens,
      IsCompact (V : Set (reesChartSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj) →
        (irreducibleComponents V).Finite :=
    finiteIrreducibleComponents_of_etale (Stacks.Blowup.reesSituationBlowUpIso _).hom hblowUp
  have hchart : ∀ V : ((BigFppfOver.toScheme B S hS).obj
        (blowUpGlueingData Z P hcU hcR hcRR).projChart).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj
        (blowUpGlueingData Z P hcU hcR hcRR).projChart)) →
        (irreducibleComponents V).Finite :=
    finiteIrreducibleComponents_of_etale
      (blowUpGlueingData Z P hcU hcR hcRR).projChartIso.hom hproj
  have hblow : HasLocallyFiniteIrreducibleComponents B S hS
      (blowUpAlong' Z P hcU hcR hcRR).1 :=
    (exists_surjective_etale_chart_iff_hasLocallyFiniteIrreducibleComponents B S hS
      (blowUpAlong' Z P hcU hcR hcRR).2).mp
      ⟨(blowUpGlueingData Z P hcU hcR hcRR).projChart,
        (blowUpGlueingData Z P hcU hcR hcRR).chart,
        (surjective_iff_surjective_pointsMap B S hS (blowUpAlong' Z P hcU hcR hcRR).1
          (blowUpAlong' Z P hcU hcR hcRR).2 _ _).mp
          (blowUpGlueingData Z P hcU hcR hcRR).chart_surjective,
        (isEtale_iff_presheaf_of_yoneda B S hS _).mpr
          (blowUpGlueingData Z P hcU hcR hcRR).chart_etale,
        hchart⟩
  obtain ⟨e, -⟩ := (isBlowupAlong_blowUpAlongHom' Z P hcU hcR hcRR).exists_iso hb
  exact hasLocallyFiniteIrreducibleComponents_of_iso B S hS
    ((ObjectProperty.ι
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)).mapIso e) hblow

end AlgebraicGeometry.Space

end
