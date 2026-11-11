module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionArtinTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionGRingHypothesis

/-!
# The G-ring hypothesis of Stacks 0GH9 gives Artin's contraction (Stacks 0GIB)

Remark Stacks 0GH9 announces that, to prove the desired result for Situation 0GH8, the local
rings of `S` will be assumed to be G-rings. This file records that the announced hypothesis
does what it is needed for: it implies the hypothesis of Stacks 0GIB (G-rings at the finite type
points of `S`), so under it the desired result holds whenever `X'` and `W` are separated over
`S`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.isGRing_of_localRingsAreGRings`: the hypothesis
  of Stacks 0GH9 gives G-rings at finite type points.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_solution_of_localRingsAreGRings`: under
  the hypothesis of Stacks 0GH9, Situation 0GH8 with `X'` and `W` separated over `S` has a
  solution.

## References

* [Stacks Project, Tag 0GH9](https://stacks.math.columbia.edu/tag/0GH9)
* [Stacks Project, Tag 0GIB](https://stacks.math.columbia.edu/tag/0GIB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Under the hypothesis of Stacks 0GH9, the local ring of `S` at a finite type point is a G-ring,
which is the form of the hypothesis that Stacks 0GIB uses. -/
theorem isGRing_of_localRingsAreGRings {c : ContractionSituation B S hS}
    (hc : c.LocalRingsAreGRings) (s : S) (_hs : IsFiniteTypePoint s) :
    IsGRing (S.presheaf.stalk s) :=
  hc s

/-- **The hypothesis of Stacks 0GH9 gives the desired result.** In Situation 0GH8, if the local
rings of `S` are G-rings and `X'` and `W` are separated over `S`, there is a solution
`(f : X' ⟶ X, T, a)` with `|U| = |X| ∖ T` (Stacks 0GIB). -/
theorem exists_solution_of_localRingsAreGRings (c : ContractionSituation B S hS)
    (hc : c.LocalRingsAreGRings)
    (hX' : Space.IsSeparated B S hS (terminal.from c.X'))
    (hW : FormalSpace.IsSeparatedMorphism B S hS (terminal.from c.W)) :
    ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (s : Solution c X),
      Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ :=
  exists_solution_of_isSeparated c (fun s hs => isGRing_of_localRingsAreGRings hc s hs) hX' hW

end AlgebraicGeometry.Artin.ContractionSituation

end
