module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFinality
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence

/-!
# The blowing up of an algebraic space at a closed point exists

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `z ∈ |X|` be a closed point.
The blowing up of `X` at `z` in the sense of Stacks 0BHE,
`AlgebraicGeometry.Space.IsBlowupAtClosedPoint`, exists: it is the blowup of Stacks 085Q of `X`
along the reduced closed subspace supported on `{z}`, provided the big fppf site contains the
relative `Proj`s out of which that blowup is glued.

## Main results

* `AlgebraicGeometry.Space.isBlowupAtClosedPoint_blowUpAlongHom'`: the blowing up of `X` along
  the reduced closed subspace on a closed point is the blowing up of `X` at that point.
* `AlgebraicGeometry.Space.exists_isBlowupAtClosedPoint`: the blowing up of an algebraic space
  at a closed point exists, the presentation being the canonical one built from the atlas.

## References

* [Stacks Project, Tag 0BHE](https://stacks.math.columbia.edu/tag/0BHE)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)] {X : AlgebraicSpaces B S hS}

/-- **The blowing up of `X` along the reduced closed subspace on a closed point `z` is the
blowing up of `X` at `z`.**  Here the reduced closed subspace on `z` is
`AlgebraicGeometry.Space.closedPointSubspace`, and the blowing up at `z` is in the sense of
`AlgebraicGeometry.Space.IsBlowupAtClosedPoint`. -/
theorem isBlowupAtClosedPoint_blowUpAlongHom' (z : points B S hS X.obj)
    (hz : IsClosed ({z} : Set (points B S hS X.obj)))
    (P : Presentation B S hS X.obj X.property)
    (hcU : B.Contains (reesChartSituation (centreIdeal (closedPointSubspace B S hS z hz))
      (isCartesianOnAffineCharts_centreIdeal (closedPointSubspace B S hS z hz))
      P).relativeProj)
    (hcR : B.Contains (reesRelationSituation (centreIdeal (closedPointSubspace B S hS z hz))
      (isCartesianOnAffineCharts_centreIdeal (closedPointSubspace B S hS z hz))
      P).relativeProj)
    (hcRR : B.Contains (reesDoubleSituation (centreIdeal (closedPointSubspace B S hS z hz))
      (isCartesianOnAffineCharts_centreIdeal (closedPointSubspace B S hS z hz))
      P).relativeProj) :
    IsBlowupAtClosedPoint B S hS z hz
      (blowUpAlongHom' (closedPointSubspace B S hS z hz) P hcU hcR hcRR) :=
  isBlowupAtClosedPoint_of_isBlowupAlong
    (isBlowupAlong_blowUpAlongHom' (closedPointSubspace B S hS z hz) P hcU hcR hcRR)

/-- **The blowing up of an algebraic space at a closed point exists**, given the three size side
conditions of the construction of Stacks 085Q along the canonical étale presentation
`AlgebraicGeometry.Space.presentationOfIsAlgebraicSpace` of `X`. -/
theorem exists_isBlowupAtClosedPoint (z : points B S hS X.obj)
    (hz : IsClosed ({z} : Set (points B S hS X.obj)))
    (hcU : B.Contains (reesChartSituation (centreIdeal (closedPointSubspace B S hS z hz))
      (isCartesianOnAffineCharts_centreIdeal (closedPointSubspace B S hS z hz))
      (presentationOfIsAlgebraicSpace B S hS X.obj X.property)).relativeProj)
    (hcR : B.Contains (reesRelationSituation (centreIdeal (closedPointSubspace B S hS z hz))
      (isCartesianOnAffineCharts_centreIdeal (closedPointSubspace B S hS z hz))
      (presentationOfIsAlgebraicSpace B S hS X.obj X.property)).relativeProj)
    (hcRR : B.Contains (reesDoubleSituation (centreIdeal (closedPointSubspace B S hS z hz))
      (isCartesianOnAffineCharts_centreIdeal (closedPointSubspace B S hS z hz))
      (presentationOfIsAlgebraicSpace B S hS X.obj X.property)).relativeProj) :
    ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X), IsBlowupAtClosedPoint B S hS z hz b :=
  ⟨_, _, isBlowupAtClosedPoint_blowUpAlongHom' z hz
    (presentationOfIsAlgebraicSpace B S hS X.obj X.property) hcU hcR hcRR⟩

end AlgebraicGeometry.Space

end
