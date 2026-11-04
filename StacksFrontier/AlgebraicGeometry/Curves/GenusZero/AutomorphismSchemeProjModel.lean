module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusZero.AutomorphismSchemeDimension
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineProjModel

/-!
# The automorphism group scheme of a `k`-scheme isomorphic to `Proj k[T₀, T₁]`

Let `k` be a field and `X` a `k`-scheme isomorphic over `k` to the projective line
`ℙ¹_k = ℙ¹_{Spec k}`, in its model as the base change of `Proj ℤ[T₀, T₁]`. Then the automorphism
functor of `X` is representable, and every scheme representing it has dimension three. This is
the genus zero clause of [Stacks, Tag 0DSV] for a `k`-scheme given with an isomorphism to the
base-change model of `ℙ¹_k` (the clause itself is
`AlgebraicGeometry.GenusZero.autScheme_topologicalKrullDim_eq_three_of_genus_eq_zero`): the glued
projective line is isomorphic to this model over `Spec k`
(`AlgebraicGeometry.projectiveLineOverIsoProjectiveSpaceOver`), so the statement reduces to
`AlgebraicGeometry.GenusZero.autScheme_topologicalKrullDim_eq_three_of_iso_projectiveLine`.

## Main results

* `AlgebraicGeometry.GenusZero.autScheme_topologicalKrullDim_eq_three_of_iso_projectiveSpaceOver`:
  **for `X ≅ ℙ¹_{Spec k}` the automorphism group scheme of `X` exists and has dimension three.**

## References

* [Stacks Project, Tag 0DSV](https://stacks.math.columbia.edu/tag/0DSV)
* [Stacks Project, Tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GenusZero

variable (k : Type u) [Field k]

/-- **The automorphism group scheme of a `k`-scheme isomorphic to `ℙ¹_{Spec k}` has dimension
three**, `ℙ¹_{Spec k}` being projective space over `Spec k` by base change from the integers:
the automorphism functor of `X` is representable, and every scheme representing it has
dimension three. -/
theorem autScheme_topologicalKrullDim_eq_three_of_iso_projectiveSpaceOver {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k))
    (e : Over.mk f ≅ Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))) :
    (∃ G : Over (Spec (.of k)), Nonempty ((Scheme.autFunctor (Over.mk f)).RepresentableBy G)) ∧
      ∀ G : Over (Spec (.of k)), (Scheme.autFunctor (Over.mk f)).RepresentableBy G →
        topologicalKrullDim G.left = 3 :=
  autScheme_topologicalKrullDim_eq_three_of_iso_projectiveLine k f
    (e ≪≫ (projectiveLineOverIsoProjectiveSpaceOver k).symm)

end AlgebraicGeometry.GenusZero
