module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjChartSituation

/-!
# The chart restriction of a graded algebra, in the forms its consumers use

`AlgebraicGeometry.Space.relativeProjChartAlgebra` restricts a graded algebra `𝒜` on an algebraic
space `X` whose homogeneous pieces are quasi-coherent on the small étale site to an étale scheme
chart `V` of `X`, landing in Situation 01NN on the chart
(`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`); quasi-coherence of the Zariski
restrictions of the pieces is supplied there by the étale-to-Zariski direction of Descent,
Stacks 03DX, `AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme`.

This file records that step for a single piece, and the names under which the restriction of
Situation 0849's algebra is consumed elsewhere.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme_piece`: the Zariski restriction
  of a homogeneous piece which is quasi-coherent on the small étale site of `X` is quasi-coherent.
* `AlgebraicGeometry.Space.relativeProjChartAlgebraOfQc`: the restriction of such a graded algebra
  to an étale scheme chart.
* `AlgebraicGeometry.Space.relativeProjChartSheafAlgebraOfSituation` and
  `AlgebraicGeometry.Space.relativeProjChartSituationOfSituation`: the restriction of Situation
  0849's algebra to an étale scheme chart.

## Implementation notes

Nothing below carries a Stacks attribute: these are the constructions
`AlgebraicGeometry.Space.relativeProjChartAlgebra`,
`AlgebraicGeometry.Space.relativeProjChartSheafAlgebra` and
`AlgebraicGeometry.Space.relativeProjChartSituation`, which carry the tag 01NN, under the names
their consumers use.  The homogeneous pieces are unchanged, so every `piece` identity transports
by `rfl`.

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

This is the étale-to-Zariski direction of Descent, Stacks 03DX, in the form
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme`, read for a homogeneous piece. -/
theorem isQuasicoherent_restrictToChartScheme_piece {X : AlgebraicSpaces B S hS}
    (A : SheafOfModules.GradedAlgebra (structureRingSheaf B S hS X))
    (hA : ∀ n : ℤ, (A.piece n).IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) (n : ℤ) :
    (restrictToChartScheme B S hS X.1 X.2 (A.piece n) V).IsQuasicoherent :=
  isQuasicoherent_restrictToChartScheme B S hS X (A.piece n) (hA n) V

/-! ### The chart restriction -/

/-- **The restriction of a graded algebra on an algebraic space to an étale scheme chart**, for a
graded algebra whose homogeneous pieces are quasi-coherent on the small étale site: Situation
01NN on the chart.  This is `AlgebraicGeometry.Space.relativeProjChartAlgebra`. -/
def relativeProjChartAlgebraOfQc {X : AlgebraicSpaces B S hS}
    (A : SheafOfModules.GradedAlgebra (structureRingSheaf B S hS X))
    (V : SmallEtale B S hS X.1)
    (hcomm : ∀ (i j : ℤ) (W : (SmallEtale B S hS X.1)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (hneg : ∀ (n : ℤ), n < 0 → ∀ (W : (SmallEtale B S hS X.1)ᵒᵖ)
      (y : (A.piece n).val.obj W), y = 0)
    (hA : ∀ n : ℤ, (A.piece n).IsQuasicoherentOnSite) :
    SheafGradedAlgebra (chartScheme V) :=
  relativeProjChartAlgebra A V hcomm hneg hA

/-- The homogeneous pieces of the chart restriction are the module restrictions of the pieces of
`𝒜`. -/
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

This is `AlgebraicGeometry.Space.relativeProjChartSheafAlgebra`. -/
def relativeProjChartSheafAlgebraOfSituation : SheafGradedAlgebra (chartScheme V) :=
  relativeProjChartSheafAlgebra s V

/-- The homogeneous pieces of that restriction are the module restrictions of the pieces of
`𝒜`. -/
theorem relativeProjChartSheafAlgebraOfSituation_piece (n : ℤ) :
    (relativeProjChartSheafAlgebraOfSituation s V).piece n =
      restrictToChartScheme s.site s.base s.containsBase s.space.1 s.space.2
        (s.algebra.piece n) V :=
  rfl

/-- **The relative Proj situation of Stacks 01NN carried on an étale scheme chart by the
restriction of Situation 0849's algebra**, under Situation 0849 alone.

This is `AlgebraicGeometry.Space.relativeProjChartSituation`. -/
def relativeProjChartSituationOfSituation : Stacks.RelativeProj.Situation.{u} :=
  relativeProjChartSituation s V

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
