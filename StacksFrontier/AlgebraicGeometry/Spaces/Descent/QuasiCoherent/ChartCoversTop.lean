module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ChartRefinement

/-!
# The charts of the members of an étale covering cover the final object

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be an étale covering of
`X` in the sense of Stacks 041E, for instance a Zariski covering.  Every chart of the small étale
site of `X` is refined by charts of the members, by
`AlgebraicGeometry.Space.exists_refinement_of_isEtaleCovering`; so the family of *all* charts of
`X` of the form `V ≫ f i`, indexed by a member `i` of the covering and a chart `V` of that
member, covers the final object of the small étale site of `X` in the sense of
`CategoryTheory.GrothendieckTopology.CoversTop`.

That is the shape in which a gluing principle on the small étale site of `X` — for instance
`existsUnique_hom_of_isCompatible`, the gluing form of Stacks 03EM — consumes the covering: the
small étale site of an algebraic space has no final object, so a covering of it can only be
expressed as a family of objects covering every object.

## Main results

* `AlgebraicGeometry.Space.memberChart` is the chart of `X` attached to a member of the family
  and a chart of that member.
* `AlgebraicGeometry.Space.coversTop_of_isEtaleCovering` and
  `AlgebraicGeometry.Space.coversTop_of_isZariskiCovering`: those charts cover the final object.

## Implementation notes

The index type is the sigma type of the index type of the covering and the charts of its members,
so the family is one object for each pair; it is not the index type of the covering itself,
because the chart of a member that refines a given chart of `X` depends on that chart.

## References

* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
* [Stacks Project, Tag 041G](https://stacks.math.columbia.edu/tag/041G)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-- The chart of the small étale site of `X` attached to a member `i` of a family of algebraic
spaces étale over `X` together with a chart of that member: the chart postcomposed with
`f i`. -/
def memberChart (p : Σ i : I, SmallEtale B S hS (Yi i).1) : SmallEtale B S hS X.1 :=
  (smallEtalePostcomp B S hS (f p.1) (hf p.1)).obj p.2

/-- **The charts of the members of an étale covering cover the final object of the small étale
site of `X`.**  Every chart of `X` is refined by charts of the members, so every arrow into it
whose source lies in the refining family — a fortiori the sieve of objects of the family — is
covering. -/
theorem coversTop_of_isEtaleCovering
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (f i).hom)) :
    (SmallEtale.topology B S hS X.1).CoversTop
      (memberChart B S hS Yi f hcov.etale) := by
  intro W
  obtain ⟨V, q, hcover⟩ := exists_refinement_of_isEtaleCovering B S hS Yi f hcov W
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_ hcover
  rintro Z r ⟨_, b, _, ⟨i⟩, rfl⟩
  exact ⟨⟨i, V i⟩, ⟨b⟩⟩

/-- **The charts of the members of a Zariski covering cover the final object of the small étale
site of `X`**, a Zariski covering being an étale covering by Stacks 0DF1. -/
theorem coversTop_of_isZariskiCovering
    (hcov : IsZariskiCovering B S hS I (fun i => (Yi i).1) (fun i => (f i).hom)) :
    (SmallEtale.topology B S hS X.1).CoversTop
      (memberChart B S hS Yi f
        (isEtaleCovering_of_isZariskiCovering B S hS X.2 (fun i => (Yi i).2) hcov).etale) :=
  coversTop_of_isEtaleCovering B S hS Yi f
    (isEtaleCovering_of_isZariskiCovering B S hS X.2 (fun i => (Yi i).2) hcov)

end AlgebraicGeometry.Space

end
