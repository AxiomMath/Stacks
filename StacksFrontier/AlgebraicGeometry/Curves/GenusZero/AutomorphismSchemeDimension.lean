module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.ProjectiveGeneralLinearTwoDimension
public import StacksFrontier.AlgebraicGeometry.Scheme.ProjectiveLineAutomorphismFunctor

/-!
# The automorphism group scheme of a curve of genus zero

Let `k` be a field. The automorphism functor `T ↦ Aut_T(ℙ¹_T)` of the projective line is the
functor of points of `PGL_{2,k}`: the scheme `AlgebraicGeometry.projectiveGeneralLinearTwoScheme`
represents it, and the identification sends the `T`-point of `PGL_{2,k}` given by an invertible
matrix `M` over `Γ(T)` to the Möbius automorphism `[s : t] ↦ [a s + b t : c s + d t]` of `M`. The
scheme `PGL_{2,k}` has dimension three. Consequently, for every `k`-scheme `X` isomorphic to
`ℙ¹_k`, the automorphism functor of `X` is representable and every scheme representing it has
dimension three.

These are the two steps of the genus zero clause of [Stacks, Tag 0DSV], which is
`AlgebraicGeometry.GenusZero.autScheme_topologicalKrullDim_eq_three_of_genus_eq_zero`; the genus
one clause is `AlgebraicGeometry.GenusOne.autScheme_topologicalKrullDim_eq_one_of_genus_eq_one`.

## Main results

* [Stacks, Tag 0DSV], genus zero,
`AlgebraicGeometry.GenusZero.autFunctor_projectiveLine_representableBy_projectiveGeneralLinearTwo`:
  **`Aut(ℙ¹_k) = PGL_{2,k}` as functors, by Möbius maps, and `PGL_{2,k}` has dimension three.**
* `AlgebraicGeometry.GenusZero.autScheme_topologicalKrullDim_eq_three_of_iso_projectiveLine`:
  **for `X ≅ ℙ¹_k` the automorphism group scheme of `X` exists and has dimension three.**

## Implementation notes

The projective line is the glued model `AlgebraicGeometry.projectiveLine` of [Stacks, Tag 01JE].
The source deduces `X ≅ ℙ¹_k` for a smooth curve of genus zero over an algebraically closed field
from [Stacks, Tag 0C6U]; the second theorem is stated for every `k`-scheme isomorphic to `ℙ¹_k`,
and is applied to such a curve in
`AlgebraicGeometry.GenusZero.autScheme_topologicalKrullDim_eq_three_of_genus_eq_zero`. As in the
genus one clause, the automorphism group scheme is a representing object of
`AlgebraicGeometry.Scheme.autFunctor`, and since representing objects are unique up to
isomorphism the dimension statement is made for every representing object.

## References

* [Stacks Project, Tag 0DSV](https://stacks.math.columbia.edu/tag/0DSV)
* [Stacks Project, Tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GenusZero

variable (k : Type u) [Field k]

/-- **Stacks Project, Tag 0DSV**, genus zero. **`Aut(ℙ¹_k) = PGL_{2,k}` as functors.** The scheme
`PGL_{2,k}` represents the automorphism functor of the projective line over `k`, the point of
`PGL_{2,k}` given by an invertible matrix `M` over a `k`-algebra `A` corresponding to the Möbius
automorphism of `M`; and `PGL_{2,k}` has dimension three. -/
@[stacks 0DSV "genus zero: Aut(P^1_k) = PGL_{2,k} as functors, an invertible matrix acting by its \
Moebius map, and PGL_{2,k} has dimension three"]
theorem autFunctor_projectiveLine_representableBy_projectiveGeneralLinearTwo :
    (∃ R : (Scheme.autFunctor (projectiveLineOver k)).RepresentableBy
        (projectiveGeneralLinearTwoScheme k),
      ∀ {A : Type u} [CommRing A] (h : Spec (.of A) ⟶ Spec (.of k))
        (M : Matrix (Fin 2) (Fin 2) A) (hM : IsUnit M.det),
        R.homEquiv (evaluationOver h M hM) = mobiusAutFunctor h M hM) ∧
      topologicalKrullDim (projectiveGeneralLinearTwoScheme k).left = 3 :=
  ⟨⟨projectiveLineAutFunctorRepresentableBy k, fun h M hM ↦
    projectiveLineAutFunctorRepresentableBy_homEquiv_evaluationOver h M hM⟩,
    topologicalKrullDim_projectiveGeneralLinearTwoScheme k⟩

/-- **The automorphism group scheme of a `k`-scheme isomorphic to the projective line has
dimension three**: its automorphism functor is representable, and every scheme representing it
has dimension three. -/
theorem autScheme_topologicalKrullDim_eq_three_of_iso_projectiveLine {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (e : Over.mk f ≅ projectiveLineOver k) :
    (∃ G : Over (Spec (.of k)), Nonempty ((Scheme.autFunctor (Over.mk f)).RepresentableBy G)) ∧
      ∀ G : Over (Spec (.of k)), (Scheme.autFunctor (Over.mk f)).RepresentableBy G →
        topologicalKrullDim G.left = 3 := by
  let R := (projectiveLineAutFunctorRepresentableBy k).ofIso (Scheme.autFunctorIsoOfIso e).symm
  refine ⟨⟨_, ⟨R⟩⟩, fun G R' ↦ ?_⟩
  rw [Scheme.topologicalKrullDim_left_eq_of_representableBy R' R,
    topologicalKrullDim_projectiveGeneralLinearTwoScheme]

end AlgebraicGeometry.GenusZero
