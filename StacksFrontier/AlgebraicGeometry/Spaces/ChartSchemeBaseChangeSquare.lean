module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeChartFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartLocalizationBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartLocalRestrictionIdentification

/-!
# Chart base change read on the small étale sites of the two chart schemes

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S`, let `V` be an
étale scheme chart of `Y` and let `U = V ×_Y X` be the base-changed chart of `X`, with
`ψ : U ⟶ V` the cartesian projection.  Base change of charts along `f` localizes at `V` to a
functor `Over V ⥤ Over U` of slices of the two small étale sites; the chart-scheme
identification of Stacks 04M0 after Stacks 03ED, `AlgebraicGeometry.Space.chartSchemeEquivalence`,
reads each slice as the small étale site of the *scheme* of the chart.  This file shows that the
localized base change becomes, under that identification, base change of small étale sites of
schemes along the morphism of schemes underlying `ψ`: the square

```
 chartSchemeSite V --- base change along ψ ---> chartSchemeSite U
        |                                              |
 chartSchemeEquivalence                    chartSchemeEquivalence
        v                                              v
     Over V -------- Over.post (smallBaseChange f) -> Over U
```

commutes up to a canonical natural isomorphism.

Nothing new is proved here: the square is the two known halves of the chart-scheme
identification, pasted.  `AlgebraicGeometry.Space.chartSchemeEquivalence` is the composite of
the comparison of the small étale site of a scheme with that of the algebraic space it
represents and the localization of Stacks 04M0 at the chart, and each half already carries its
own base-change square —
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso` for the first and
`AlgebraicGeometry.Space.chartLocalizationBaseChangeIso` for the second.  What this file
contributes is the bookkeeping that puts them together, which is not free: the comparison of
the small étale sites appears in `AlgebraicGeometry.Space.chartSchemeEquivalence` through its
*inverse*, and the two existing squares are both stated for its functor.

## Main definitions

* `AlgebraicGeometry.Space.chartSchemeBaseChange`: base change of the small étale sites of the
  two chart schemes along the morphism of schemes underlying `ψ`.
* `AlgebraicGeometry.Space.chartSchemeBaseChangeInnerIso`: the square after precomposition with
  the comparison functor of `V`, where both sides are free of inverses and the two existing
  squares apply directly.
* `AlgebraicGeometry.Space.chartSchemeBaseChangeIso`: **the natural isomorphism filling the
  square above**, with the chart-scheme identifications written out as composites.
* `AlgebraicGeometry.Space.chartSchemeEquivalenceBaseChangeIso`: the same isomorphism with the
  chart-scheme identifications named, which is the form in which it is used.

## Implementation notes

The comparison of the small étale sites of the chart scheme and of the chart space enters
`AlgebraicGeometry.Space.chartSchemeEquivalence` as an inverse, so neither existing square can be
whiskered into the statement directly.  The construction therefore goes through
`AlgebraicGeometry.Space.chartSchemeBaseChangeInnerIso`, the square precomposed with the
*functor* of that comparison: there `CategoryTheory.Equivalence.funInvIdAssoc` cancels the
inverse on both sides and the two existing squares are the only content.  Cancelling the
precomposition again, by `CategoryTheory.Equivalence.invFunIdAssoc`, returns the square itself.

Every composite is written out and every whiskering is given its functor explicitly, with the
reassociations named as `CategoryTheory.Functor.associator`.  This is not decoration: the
functors here are long composites of comparison functors, and leaving a grouping or a whiskered
functor to be inferred makes the elaborator unify two such composites, which exhausts the
heartbeat budget.  For the same reason the statement of
`AlgebraicGeometry.Space.chartSchemeBaseChangeIso` spells the chart-scheme identification as the
composite it is defined to be, rather than naming
`AlgebraicGeometry.Space.chartSchemeEquivalence`; the two are equal by `rfl`, and
`AlgebraicGeometry.Space.chartSchemeEquivalenceBaseChangeIso` records the named form.

## References

* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison of the small étale site of the scheme of an étale chart with the small étale
site of the algebraic space that chart represents, at the spelling
`AlgebraicGeometry.Space.chartSchemeEquivalence` is built from. -/
noncomputable abbrev chartReprEquivalence {Z : AlgebraicSpaces B S hS}
    (A : SmallEtale B S hS Z.1) :=
  representedSmallEtaleEquivalence B S hS (chartOverObject B S hS Z A)

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (hrep : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)

/-- **Base change of the small étale sites of the two chart schemes**, along the morphism of
schemes underlying the cartesian projection `ψ : V ×_Y X ⟶ V`. -/
noncomputable abbrev chartSchemeBaseChange :=
  smallEtaleBaseChange (associatedBigEtaleSite B) (baseChangeChartHom B S hS f hrep V).left

/-- Base change of charts along the morphism of algebraic spaces represented by `ψ`, which is
the common middle term of the two existing squares. -/
noncomputable abbrev chartReprBaseChange :=
  smallBaseChange B S hS (representedSpaceMap B S hS (baseChangeChartHom B S hS f hrep V))
    (chartProjectionRepresentable B S hS f hrep V)

/-- **The square after precomposition with the comparison functor of `V`.**  Both sides are
then free of the inverse comparison, and the isomorphism is the localized base-change square of
Stacks 04CF followed by the represented base-change square, with the comparison of the
base-changed chart cancelled between them. -/
noncomputable def chartSchemeBaseChangeInnerIso :
    (chartReprEquivalence B S hS V).functor ⋙
        ((chartReprEquivalence B S hS V).inverse ⋙
          ((SmallEtale.chartLocalizationEquivalence B S hS Y.1 V).functor ⋙
            Over.post (smallBaseChange B S hS f hrep))) ≅
      (chartReprEquivalence B S hS V).functor ⋙
        (chartSchemeBaseChange B S hS f hrep V ⋙
          ((chartReprEquivalence B S hS (baseChangeChart B S hS f hrep V)).inverse ⋙
            (SmallEtale.chartLocalizationEquivalence B S hS X.1
              (baseChangeChart B S hS f hrep V)).functor)) :=
  (chartReprEquivalence B S hS V).funInvIdAssoc
      ((SmallEtale.chartLocalizationEquivalence B S hS Y.1 V).functor ⋙
        Over.post (smallBaseChange B S hS f hrep)) ≪≫
    chartLocalizationBaseChangeIso B S hS f hrep V ≪≫
    (Functor.isoWhiskerLeft (chartReprBaseChange B S hS f hrep V)
      ((chartReprEquivalence B S hS (baseChangeChart B S hS f hrep V)).funInvIdAssoc
        (SmallEtale.chartLocalizationEquivalence B S hS X.1
          (baseChangeChart B S hS f hrep V)).functor)).symm ≪≫
    (Functor.associator (chartReprBaseChange B S hS f hrep V)
      (chartReprEquivalence B S hS (baseChangeChart B S hS f hrep V)).functor
      ((chartReprEquivalence B S hS (baseChangeChart B S hS f hrep V)).inverse ⋙
        (SmallEtale.chartLocalizationEquivalence B S hS X.1
          (baseChangeChart B S hS f hrep V)).functor)).symm ≪≫
    Functor.isoWhiskerRight
      (representedSmallEtaleBaseChangeIso B S hS (baseChangeChartHom B S hS f hrep V)
        (chartProjectionRepresentable B S hS f hrep V))
      ((chartReprEquivalence B S hS (baseChangeChart B S hS f hrep V)).inverse ⋙
        (SmallEtale.chartLocalizationEquivalence B S hS X.1
          (baseChangeChart B S hS f hrep V)).functor) ≪≫
    Functor.associator (chartReprEquivalence B S hS V).functor
      (chartSchemeBaseChange B S hS f hrep V)
      ((chartReprEquivalence B S hS (baseChangeChart B S hS f hrep V)).inverse ⋙
        (SmallEtale.chartLocalizationEquivalence B S hS X.1
          (baseChangeChart B S hS f hrep V)).functor)

/-- **The localized chart base change is base change of the small étale sites of the two chart
schemes.**  For a representable morphism `f : X ⟶ Y` of algebraic spaces over `S` and an étale
scheme chart `V` of `Y`, the localization at `V` of base change of charts along `f`, read
through the chart-scheme identification at both ends, is base change along the morphism of
schemes underlying the cartesian projection `ψ : V ×_Y X ⟶ V`.

The chart-scheme identification is spelled as the composite it is defined to be; see
`AlgebraicGeometry.Space.chartSchemeEquivalenceBaseChangeIso` for the named form. -/
noncomputable def chartSchemeBaseChangeIso :
    (chartReprEquivalence B S hS V).inverse ⋙
        ((SmallEtale.chartLocalizationEquivalence B S hS Y.1 V).functor ⋙
          Over.post (smallBaseChange B S hS f hrep)) ≅
      chartSchemeBaseChange B S hS f hrep V ⋙
        ((chartReprEquivalence B S hS (baseChangeChart B S hS f hrep V)).inverse ⋙
          (SmallEtale.chartLocalizationEquivalence B S hS X.1
            (baseChangeChart B S hS f hrep V)).functor) :=
  ((chartReprEquivalence B S hS V).invFunIdAssoc
      ((chartReprEquivalence B S hS V).inverse ⋙
        ((SmallEtale.chartLocalizationEquivalence B S hS Y.1 V).functor ⋙
          Over.post (smallBaseChange B S hS f hrep)))).symm ≪≫
    Functor.isoWhiskerLeft (chartReprEquivalence B S hS V).inverse
      (chartSchemeBaseChangeInnerIso B S hS f hrep V) ≪≫
    (chartReprEquivalence B S hS V).invFunIdAssoc
      (chartSchemeBaseChange B S hS f hrep V ⋙
        ((chartReprEquivalence B S hS (baseChangeChart B S hS f hrep V)).inverse ⋙
          (SmallEtale.chartLocalizationEquivalence B S hS X.1
            (baseChangeChart B S hS f hrep V)).functor))

/-- **The square of `AlgebraicGeometry.Space.chartSchemeBaseChangeIso` with the chart-scheme
identifications named.**  This is the form the comparison is used in; the functor of
`AlgebraicGeometry.Space.chartSchemeEquivalence` is the composite appearing there by `rfl`. -/
noncomputable def chartSchemeEquivalenceBaseChangeIso :
    (chartSchemeEquivalence B S hS Y V).functor ⋙
        Over.post (smallBaseChange B S hS f hrep) ≅
      chartSchemeBaseChange B S hS f hrep V ⋙
        (chartSchemeEquivalence B S hS X (baseChangeChart B S hS f hrep V)).functor :=
  chartSchemeBaseChangeIso B S hS f hrep V

end AlgebraicGeometry.Space

end
