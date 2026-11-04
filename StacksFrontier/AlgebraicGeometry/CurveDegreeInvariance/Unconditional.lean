module

public import StacksFrontier.AlgebraicGeometry.CurveDegreeInvariance.Morphism
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0AYU] with no hypothesis

**The prefix `AlgebraicGeometry.` is elided from every declaration name below.**

`curveDegree_pullback_eq_of_bijOn_genericPointsOne`
(`StacksFrontier/AlgebraicGeometry/CurveDegreeInvariance/Morphism.lean`) proves
[Stacks, Tag 0AYU]'s "more generally" statement — for `g : X' ⟶ X` over a field `k` between
schemes proper over `k` of dimension at most one, inducing a bijection on the generic points of
the one-dimensional components and isomorphisms on the local rings there,

`deg(g^*ℰ) = deg(ℰ)`

for `ℰ` finite locally free of constant rank, with no hypothesis beyond the tag's own: [Stacks,
Tag 02O6] over a field and the projection formula [Stacks, Tag 01E8] at `g` are proved there.
This file keeps the name `curveDegree_pullback_eq_of_bijOn_genericPointsOne_of_isProper` for
that statement, which an earlier form of `Morphism.lean` proved only with those two inputs
carried as hypotheses.

## Main results

* `curveDegree_pullback_eq_of_bijOn_genericPointsOne_of_isProper`: **[Stacks, Tag 0AYU], the
  "more generally" statement, with no hypothesis beyond the tag's own.**

## References

* [Stacks Project, Tag 0AYU](https://stacks.math.columbia.edu/tag/0AYU)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.BirationalCurveFinite
open Stacks.AlgebraicGeometry.ComponentDegrees
open Stacks.AlgebraicGeometry.CurveEulerBridge
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0AYU], the "more generally" statement, with no hypothesis beyond the tag's
own.** Let `k` be a field and let `g : X' ⟶ X` be a morphism over `k` between schemes proper
over `k` and of dimension at most one which induces a bijection between the generic points of
the one-dimensional irreducible components of `X'` and those of `X`, and isomorphisms of the
local rings at the points of `X'` involved. Let `ℰ` be finite locally free of constant rank `n`
on `X`. Then

`deg(g^*ℰ) = deg(ℰ)`.

`hbij` and `hstalk` are the tag's own hypotheses, and they are all that
`curveDegree_pullback_eq_of_bijOn_genericPointsOne` takes: [Stacks, Tag 02O6] over a field and
the projection formula at `g` are proved there rather than carried. -/
@[stacks 0AYU "the 'more generally' statement, with no hypothesis beyond the tag's own",
  sga "6 X 4.4" "special case"]
theorem curveDegree_pullback_eq_of_bijOn_genericPointsOne_of_isProper (k : Type u) [Field k]
    {X' X : Scheme.{u}} (p' : X' ⟶ Spec (.of k)) (p : X ⟶ Spec (.of k))
    [IsProper p'] [IsProper p]
    (hdimX' : topologicalKrullDim (X' : Type u) ≤ 1)
    (hdimX : topologicalKrullDim (X : Type u) ≤ 1)
    (g : X' ⟶ X) (hgOver : g ≫ p = p')
    (hbij : Set.BijOn g (genericPointsOne X') (genericPointsOne X))
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (hstalk : ∀ z ∈ genericPointsOne X', IsIso (g.stalkMap z)) :
    @curveDegree k _ X' p' _ hdimX' ((Scheme.Modules.pullback g).obj E) n
        (isFiniteLocallyFreeOfRank_pullback g E n) =
      curveDegree k p hdimX E n :=
  curveDegree_pullback_eq_of_bijOn_genericPointsOne k p' p hdimX' hdimX g hgOver hbij E n hstalk

end AlgebraicGeometry

end
