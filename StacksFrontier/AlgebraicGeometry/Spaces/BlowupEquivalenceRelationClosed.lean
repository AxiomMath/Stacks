module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationTransitivity

/-!
# The blowing up of an algebraic space, with the descent datum discharged

`StacksFrontier/AlgebraicGeometry/Spaces/BlowupRelativeProj.lean` builds the blowup of an algebraic
space `X` along a closed subspace `Z` as the relative Proj of the Rees algebra of the defining
ideal sheaf of `Z`, and carries the equivalence-relation condition on the two projections
`P_R ⇉ P_U` of its descent datum as a parameter `heq`. That condition is now a theorem:
`AlgebraicGeometry.Space.isEquivalenceRelation_post_reesProj`. This file restates the three
declarations of Tag 085Q without it.

The restated declarations are *the same objects*: each is the corresponding declaration of
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupRelativeProj.lean` applied to the proof of the
equivalence-relation condition rather than to an assumption of it. What remains carried is the
set-theoretic side condition that the three relative Projs `P_U`, `P_R` and `P_{R ×_U R}` be
objects of the big fppf site — `hcU`, `hcR` and `hcRR`. That is the same condition that
`AlgebraicGeometry.Space.relativeProjChartOfSituation` takes, it is what the source's
set-theoretic conventions provide, and carrying it is not a weakening of Tag 085Q.

## Main definitions

* `AlgebraicGeometry.Space.blowUpAlong'`: **Stacks 085Q**, the blowup of `X` along `Z`, with the
  equivalence-relation field of the descent datum discharged.
* `AlgebraicGeometry.Space.blowUpAlongHom'`: **Stacks 085Q**, its structure morphism `b`.
* `AlgebraicGeometry.Space.exceptionalDivisor'`: **Stacks 085Q**, the exceptional divisor
  `b⁻¹(Z)`.

## Implementation notes

The three declarations are definitionally the primed-free ones at the discharged hypothesis, so
every statement already proved about `AlgebraicGeometry.Space.blowUpAlong` and its companions
applies to them with no transport; in particular the type of
`AlgebraicGeometry.Space.exceptionalDivisor'` is stated over `blowUpAlong'` and is accepted
because the two agree by definition.

`StacksFrontier/AlgebraicGeometry/Spaces/BlowupRelativeProj.lean` is not edited: its three
declarations are the general form, taking the condition as a parameter, and they remain correct
and useful for a consumer who has the condition by other means.

## References

* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  (Z : ClosedSubspaces B S hS X.obj) (P : Presentation B S hS X.obj X.property)
  (hcU : B.Contains (reesChartSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (hcR : B.Contains (reesRelationSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (hcRR : B.Contains (reesDoubleSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)

/-- **Stacks 085Q.** The blowing up of an algebraic space `X` along a closed subspace `Z ⊆ X`:
the relative Proj `Proj_X(⨁_{n ≥ 0} 𝓘_Zⁿ)` of the Rees algebra of the defining ideal sheaf of
`Z`, as an algebraic space over `S`.

This is `AlgebraicGeometry.Space.blowUpAlong` with its equivalence-relation parameter supplied by
`AlgebraicGeometry.Space.isEquivalenceRelation_post_reesProj` rather than assumed. -/
@[stacks 085Q "the blowup of X along Z as the relative Proj of the Rees algebra, the same object \
as blowUpAlong with the descent datum's equivalence-relation field discharged rather than \
assumed; the three B.Contains side conditions on the relative Projs remain"]
def blowUpAlong' : AlgebraicSpaces B S hS :=
  blowUpAlong Z P hcU hcR
    (isEquivalenceRelation_post_reesProj (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR hcRR)

/-- **Stacks 085Q.** The blowing up `b : Proj_X(⨁_{n ≥ 0} 𝓘_Zⁿ) ⟶ X` of an algebraic space `X`
along a closed subspace `Z ⊆ X`, as a morphism of algebraic spaces over `S`, with the
equivalence-relation field of the descent datum discharged. -/
@[stacks 085Q "the morphism b of the blowup, with the descent datum's equivalence-relation field \
discharged rather than assumed; the three B.Contains side conditions on the relative Projs \
remain"]
def blowUpAlongHom' : blowUpAlong' Z P hcU hcR hcRR ⟶ X :=
  blowUpAlongHom Z P hcU hcR
    (isEquivalenceRelation_post_reesProj (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR hcRR)

/-- **Stacks 085Q.** The exceptional divisor `b⁻¹(Z)` of the blowing up of `X` along `Z`: the
inverse image of the centre along the structure morphism of the blowup, as a closed subspace of
the blowup, with the equivalence-relation field of the descent datum discharged. -/
@[stacks 085Q "the exceptional divisor b⁻¹(Z) of the blowup and the centre Z, with the descent \
datum's equivalence-relation field discharged rather than assumed; the three B.Contains side \
conditions on the relative Projs remain"]
def exceptionalDivisor' : ClosedSubspaces B S hS (blowUpAlong' Z P hcU hcR hcRR).obj :=
  exceptionalDivisor Z P hcU hcR
    (isEquivalenceRelation_post_reesProj (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR hcRR)

end AlgebraicGeometry.Space

end
