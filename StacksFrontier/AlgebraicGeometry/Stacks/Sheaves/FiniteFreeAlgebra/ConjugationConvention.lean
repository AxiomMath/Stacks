module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.ConjugationActionOnSite

/-!
# The two matrix conventions of the conjugation action, and their composite

Two different conventions for the matrix of an arrow meet when the presheaf `FA_d` of free
rank-`d` algebra structures is compared with the evaluated action groupoid of the conjugation
action, and each of them inverts the matrix. This file records that the two inversions cancel, so
that the comparison is matrix-*preserving* and no stray inverse is left in the identification.

The two conventions are these.

* `AlgebraicGeometry.FiniteFreeAlgebra.ActionGroupoidPresheaf.arrowEquiv` puts an arrow `x ⟶ y`
  of the action-groupoid presheaf of Stacks 05YP in bijection with the matrices `g` satisfying
  `conjugationOnPoints laws T g x = y`: an arrow with matrix `g` out of `x` has target `a(g, x)`,
  for the *right* action `a` named in Stacks 05YQ.
* The action groupoid in algebraic spaces is formed from
  `AlgebraicGeometry.Space.conjugationModObj`, whose action is the *left* action
  `g • x = a(g⁻¹, x)` of `AlgebraicGeometry.FiniteFreeAlgebra.leftConjugationOnPoints`; by
  `AlgebraicGeometry.Space.groupoidOfAction_target` and
  `AlgebraicGeometry.Space.groupoidOfAction_evaluationArrowEquiv` an arrow of its evaluation with
  matrix `h` out of `x` therefore has target `h • x = a(h⁻¹, x)`.

So an arrow of the evaluated action groupoid has the matrix of the corresponding arrow of the
action-groupoid presheaf *inverted*:
`AlgebraicGeometry.FiniteFreeAlgebra.leftConjugationOnPoints_inv` below is that statement.
Meanwhile the natural isomorphism supplied by
`AlgebraicGeometry.FiniteFreeAlgebra.presheaf_actionGroupoid` inverts too — its second clause
reads `(P.arrowEquiv … ((η.hom.app T).map e)).1.1 = (F.arrowEquiv … e).matrix⁻¹`. Composing the
two, a morphism of free structures with matrix `M` corresponds to an arrow of the evaluated
action groupoid with matrix `(M⁻¹)⁻¹ = M`.

That last step is `inv_inv`, and it is the only place the cancellation happens; it is recorded
here as `AlgebraicGeometry.FiniteFreeAlgebra.leftConjugationOnPoints_inv_inv` rather than left to
be re-derived at the point of use, because getting it wrong is invisible to the type checker: both
conventions have the same type, and a spurious `symm` or a missing inverse produces a
well-typed identification of the wrong arrow.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.leftConjugationOnPoints_inv`: the left action at `g⁻¹` is
  the right action at `g`, which is the change of convention between the two groupoids.
* `AlgebraicGeometry.FiniteFreeAlgebra.conjugationOnPoints_inv`: the same read in the other
  direction.
* `AlgebraicGeometry.FiniteFreeAlgebra.leftConjugationOnPoints_inv_inv`: the two inversions
  cancel.

## References

* [Stacks Project, Tag 05YP](https://stacks.math.columbia.edu/tag/05YP)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable {d : ℕ} [NeZero d] (laws : ConjugationPreservesAlgebraLaws.{u} d) (T : Scheme.{u})

/-- **The change of convention between the two groupoids.** The left action at the inverse matrix
is the right action at the matrix itself, so an arrow of the evaluated action groupoid with matrix
`g⁻¹` has the same target as an arrow of the action-groupoid presheaf with matrix `g`. -/
theorem leftConjugationOnPoints_inv (g : UnitFixingMatrix Γ(T, ⊤) d) (x : T ⟶ scheme.{u} d) :
    leftConjugationOnPoints laws T g⁻¹ x = conjugationOnPoints laws T g x := by
  rw [leftConjugationOnPoints, inv_inv]

/-- The change of convention, read in the other direction. -/
theorem conjugationOnPoints_inv (g : UnitFixingMatrix Γ(T, ⊤) d) (x : T ⟶ scheme.{u} d) :
    conjugationOnPoints laws T g⁻¹ x = leftConjugationOnPoints laws T g x := rfl

/-- **The two inversions cancel.** Inverting the matrix to pass from the action-groupoid presheaf
of Stacks 05YP to the evaluated action groupoid, and inverting it again as
`AlgebraicGeometry.FiniteFreeAlgebra.presheaf_actionGroupoid` does to pass from `FA_d` to that
presheaf, restores the original matrix: the composite identification is matrix-preserving. -/
theorem leftConjugationOnPoints_inv_inv (g : UnitFixingMatrix Γ(T, ⊤) d)
    (x : T ⟶ scheme.{u} d) :
    leftConjugationOnPoints laws T (g⁻¹)⁻¹ x = leftConjugationOnPoints laws T g x := by
  rw [inv_inv]

end AlgebraicGeometry.FiniteFreeAlgebra

end
