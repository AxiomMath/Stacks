module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjChartSituation

/-!
# The quasi-coherence hypothesis of the chart restriction is dischargeable

`AlgebraicGeometry.Space.relativeProjChartAlgebra` restricts a graded algebra `𝒜` on an algebraic
space `X` to an étale scheme chart `V` of `X`, landing in Situation 01NN on the chart
(`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`), and it takes as a hypothesis
`hqc` the quasi-coherence of the Zariski restrictions of the homogeneous pieces.  Its siblings
`AlgebraicGeometry.Space.relativeProjChartSituation` and
`AlgebraicGeometry.Space.relativeProjChartSheafAlgebra` carry the same hypothesis, and the
structure `AlgebraicGeometry.Space.RelativeProjSituationChart` carries it as a field.

The hypothesis is **not needed**: quasi-coherence of a module on the small étale site of `X` gives
quasi-coherence of its Zariski restriction to a chart, with no further assumption, by
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme` — the étale-to-Zariski direction
of Descent, Stacks 03DX.  This file spends that, so that the restriction of Situation 0849's
algebra to a chart needs nothing beyond Situation 0849 itself.

The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/GradedAlgebraChartRestriction.lean` state that the
étale-to-Zariski direction of Descent 03DX "is not in this library"; that is no longer so, and
was already not so when those notes were written —
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionQuasicoherent.lean` is that direction,
proved, and the same notes' claim that the two available clauses of Stacks 03DX "neither of which
compares the two" sites overlooks it.  The hypothesis-carrying forms are left in place, since they
are consumed elsewhere; what is added here is the discharged form.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme_piece`: the hypothesis `hqc` of
  `AlgebraicGeometry.Space.relativeProjChartAlgebra`, discharged for a graded algebra whose
  homogeneous pieces are quasi-coherent on the small étale site of `X`.
* `AlgebraicGeometry.Space.relativeProjChartAlgebraOfQc`: the restriction of such a graded algebra
  to an étale scheme chart, with no quasi-coherence hypothesis.
* `AlgebraicGeometry.Space.relativeProjChartSheafAlgebraOfSituation` and
  `AlgebraicGeometry.Space.relativeProjChartSituationOfSituation`: the restriction of Situation
  0849's algebra to an étale scheme chart, under Situation 0849 alone.

## Implementation notes

Nothing below carries a Stacks attribute.  The tag 01NN sits on the hypothesis-carrying
`AlgebraicGeometry.Space.relativeProjChartAlgebra` and
`AlgebraicGeometry.Space.relativeProjChartSituation`, and these are the same constructions with
one hypothesis supplied, so they state no new tag; the attribute on the originals describes the
construction, not the hypothesis.

The homogeneous pieces are unchanged, so every `piece` identity of the originals transports by
`rfl`, and the statements below are definitionally the originals at the supplied hypothesis.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory

open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The hypothesis, discharged -/

/-- **The Zariski restriction to an étale scheme chart of a homogeneous piece which is
quasi-coherent on the small étale site is quasi-coherent.**

This is the hypothesis `hqc` of `AlgebraicGeometry.Space.relativeProjChartAlgebra`, supplied from
quasi-coherence of the pieces of `𝒜` on the small étale site of `X` — which is the form
Situation 0849 carries it in — by the étale-to-Zariski direction of Descent, Stacks 03DX, that is
by `AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme`. -/
theorem isQuasicoherent_restrictToChartScheme_piece {X : AlgebraicSpaces B S hS}
    (A : SheafOfModules.GradedAlgebra (structureRingSheaf B S hS X))
    (hA : ∀ n : ℤ, (A.piece n).IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) (n : ℤ) :
    (restrictToChartScheme B S hS X.1 X.2 (A.piece n) V).IsQuasicoherent :=
  isQuasicoherent_restrictToChartScheme B S hS X (A.piece n) (hA n) V

/-! ### The chart restriction without a quasi-coherence hypothesis -/

/-- **The restriction of a graded algebra on an algebraic space to an étale scheme chart**, for a
graded algebra whose homogeneous pieces are quasi-coherent on the small étale site: Situation
01NN on the chart, with no quasi-coherence hypothesis on the Zariski restrictions.

This is `AlgebraicGeometry.Space.relativeProjChartAlgebra` with its `hqc` supplied by
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme_piece`. -/
def relativeProjChartAlgebraOfQc {X : AlgebraicSpaces B S hS}
    (A : SheafOfModules.GradedAlgebra (structureRingSheaf B S hS X))
    (V : SmallEtale B S hS X.1)
    (hcomm : ∀ (i j : ℤ) (W : (SmallEtale B S hS X.1)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (hneg : ∀ (n : ℤ), n < 0 → ∀ (W : (SmallEtale B S hS X.1)ᵒᵖ)
      (y : (A.piece n).val.obj W), y = 0)
    (hA : ∀ n : ℤ, (A.piece n).IsQuasicoherentOnSite) :
    SheafGradedAlgebra (chartScheme V) :=
  relativeProjChartAlgebra A V hcomm hneg
    (isQuasicoherent_restrictToChartScheme_piece B S hS A hA V)

/-- The homogeneous pieces of the chart restriction are the module restrictions of the pieces of
`𝒜`, as for the hypothesis-carrying form. -/
theorem relativeProjChartAlgebraOfQc_piece {X : AlgebraicSpaces B S hS}
    (A : SheafOfModules.GradedAlgebra (structureRingSheaf B S hS X))
    (V : SmallEtale B S hS X.1)
    (hcomm : ∀ (i j : ℤ) (W : (SmallEtale B S hS X.1)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (hneg : ∀ (n : ℤ), n < 0 → ∀ (W : (SmallEtale B S hS X.1)ᵒᵖ)
      (y : (A.piece n).val.obj W), y = 0)
    (hA : ∀ n : ℤ, (A.piece n).IsQuasicoherentOnSite) (n : ℤ) :
    (relativeProjChartAlgebraOfQc B S hS A V hcomm hneg hA).piece n =
      restrictToChartScheme B S hS X.1 X.2 (A.piece n) V :=
  rfl

/-! ### The chart restriction of Situation 0849 -/

variable (s : RelativeProjSituation.{u, u}) (V : SmallEtale s.site s.base s.containsBase s.space.1)

/-- **The restriction of Situation 0849's graded algebra to an étale scheme chart**, under
Situation 0849 alone: Situation 01NN on the chart, with no hypothesis beyond the situation.

This is `AlgebraicGeometry.Space.relativeProjChartSheafAlgebra` with its `hqc` supplied from the
situation's own `isQuasicoherent` field. -/
def relativeProjChartSheafAlgebraOfSituation : SheafGradedAlgebra (chartScheme V) :=
  relativeProjChartSheafAlgebra s V
    (isQuasicoherent_restrictToChartScheme_piece s.site s.base s.containsBase s.algebra
      s.isQuasicoherent V)

/-- The homogeneous pieces of that restriction are the module restrictions of the pieces of
`𝒜`. -/
theorem relativeProjChartSheafAlgebraOfSituation_piece (n : ℤ) :
    (relativeProjChartSheafAlgebraOfSituation s V).piece n =
      restrictToChartScheme s.site s.base s.containsBase s.space.1 s.space.2
        (s.algebra.piece n) V :=
  rfl

/-- **The relative Proj situation of Stacks 01NN carried on an étale scheme chart by the
restriction of Situation 0849's algebra**, under Situation 0849 alone.

This is `AlgebraicGeometry.Space.relativeProjChartSituation` with its `hqc` supplied from the
situation's own `isQuasicoherent` field. -/
def relativeProjChartSituationOfSituation : Stacks.RelativeProj.Situation.{u} :=
  relativeProjChartSituation s V
    (isQuasicoherent_restrictToChartScheme_piece s.site s.base s.containsBase s.algebra
      s.isQuasicoherent V)

/-- The base of that situation is the scheme underlying the chart. -/
theorem relativeProjChartSituationOfSituation_base :
    (relativeProjChartSituationOfSituation s V).base = chartScheme V :=
  rfl

/-- The homogeneous pieces of that situation are the module restrictions of the pieces of `𝒜`. -/
theorem relativeProjChartSituationOfSituation_algebra_piece (n : ℤ) :
    (relativeProjChartSituationOfSituation s V).algebra.piece n =
      restrictToChartScheme s.site s.base s.containsBase s.space.1 s.space.2
        (s.algebra.piece n) V :=
  rfl

end AlgebraicGeometry.Space

end
