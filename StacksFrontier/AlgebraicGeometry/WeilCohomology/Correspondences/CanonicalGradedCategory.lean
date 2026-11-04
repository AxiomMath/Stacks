module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalFlat
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalProperIntersection
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveGraphFunctor

/-!
# The graded category of correspondences and the graph functor

Let `k` be a field. Correspondences between smooth projective schemes over `k`, composed with the
canonical family of diagonal classes — the Gysin classes `Δ^!` of Stacks 0FBR — form a graded
category over `ℚ` (Stacks 0FG2), and sending a morphism to the class of its graph is a
contravariant functor into it (Stacks 0FG3).

## Main definitions

* `Stacks.WeilCohomology.canonicalCorrespondenceCompositionData`: composition of
  correspondences between smooth projective schemes over `k`, for the canonical diagonal classes.
* `Stacks.WeilCohomology.canonicalCorrespondences_gradedCategory`: the graded category of
  correspondences.
* `Stacks.WeilCohomology.canonicalGraphFunctor`: the graph functor.

## References

* [Stacks Project, Tag 0FG2](https://stacks.math.columbia.edu/tag/0FG2)
* [Stacks Project, Tag 0FG3](https://stacks.math.columbia.edu/tag/0FG3)
* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k]

/-- Composition of correspondences between smooth projective schemes over `k`, formed with the
canonical family of diagonal classes. -/
noncomputable abbrev canonicalCorrespondenceCompositionData :=
  correspondenceCompositionData k (canonicalDiagonalClassFamily k)
    (canonicalDiagonalClassFamily_compositionAssoc k)
    (canonicalDiagonalClassFamily_properIntersectionFormula k)

/-- Correspondences between smooth projective schemes over `k` form a graded category over `ℚ`:
the morphisms from `X` to `Y` are `⨁ᵣ Corrʳ(X, Y)`, the identity is the class of the diagonal, of
degree zero, and the composite of correspondences of degrees `r` and `s`, formed with the
canonical diagonal classes, has degree `r + s`. -/
@[stacks 0FG2]
instance canonicalCorrespondences_gradedCategory :
    GradedCategory ℚ (canonicalCorrespondenceCompositionData k).Obj :=
  GradedCompositionData.gradedCategory _

/-- The contravariant functor from smooth projective schemes over `k` to the category of
correspondences which is the identity on objects and sends `f : X ⟶ Y` to the class
`[Γ_f] ∈ Corr⁰(Y, X)` of its graph. -/
@[stacks 0FG3]
noncomputable def canonicalGraphFunctor :
    ((SmoothProjectiveScheme k).FullSubcategory)ᵒᵖ ⥤
      (canonicalCorrespondenceCompositionData k).Obj :=
  graphFunctor k (canonicalDiagonalClassFamily k)
    (canonicalDiagonalClassFamily_compositionAssoc k)
    (canonicalDiagonalClassFamily_properIntersectionFormula k)

end Stacks.WeilCohomology

end
