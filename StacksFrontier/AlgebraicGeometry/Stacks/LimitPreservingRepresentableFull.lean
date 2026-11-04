module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingDiagonalCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRepresentableEssSurj

/-!
# Fullness of the comparison of Stacks 0CMR from descent of objects along the diagonal

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of a
scheme `S`. Fullness of the comparison functor

`colim 𝒳_{Uᵢ} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{Uᵢ}`

out of the canonical square of Stacks 0CMR is the last of its three properties needed for the
converse direction of Stacks 0CMV, the other two being
`AlgebraicGeometry.Stack.faithful_toCategoricalPullbackFunctor_canonicalSquare` and
`AlgebraicGeometry.Stack.essSurj_toCategoricalPullbackFunctor_canonicalSquare`. This file carries
it, from descent of objects along the *relative diagonal* `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳`.

## Main results

* `AlgebraicGeometry.Stack.full_toCategoricalPullbackFunctor_canonicalSquare`: the comparison out
  of `AlgebraicGeometry.Stack.canonicalSquare` is full as soon as the objects of `𝒳` descend along
  the cone relative to `Δ_f`.

## Implementation notes

The route is the one the machinery of Stacks 0CMW is built for, and it avoids the circularity the
statement invites: essential surjectivity of the comparison of `Δ_f`'s own square of Stacks 0CMR
is enough for fullness of `f`'s comparison, so nothing is asked of limit preservation of `Δ_f` —
which is the property Stacks 0CMW identifies *with* the conclusion.

Two steps. Essential surjectivity of `Δ_f`'s comparison is
`AlgebraicGeometry.Stack.essSurj_toCategoricalPullbackFunctor_canonicalSquare` applied to `Δ_f`,
and it transports to the comparison of the square of relative diagonals of `f`'s square by
`AlgebraicGeometry.Stack.full_toCategoricalPullbackFunctor_canonicalSquare_of_essSurj_diagonal`,
over the identification of the two squares that Stacks 0CMW supplies. Essential surjectivity of
the comparison of a square of relative diagonals already forces fullness of the original
comparison, since under
`CategoryTheory.Limits.CategoricalPullback.diagonalTargetEquivalence` that comparison is the
diagonal of the original one.

The index category is cofiltered, as everywhere in Stacks 0CMR; the transfer needs its opposite to
be filtered, which is the same condition.

## References

* [Stacks Project, Tag 0CMV](https://stacks.math.columbia.edu/tag/0CMV)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS))
  (f : 𝒳 ⟶ 𝒴) {I : Type v} [Category.{w} I]

/-- **Fullness of the comparison out of the canonical square of Stacks 0CMR**, for a 1-morphism
whose objects descend along the cofiltered limit *relative to its diagonal*. Together with
`AlgebraicGeometry.Stack.faithful_toCategoricalPullbackFunctor_canonicalSquare` and
`AlgebraicGeometry.Stack.essSurj_toCategoricalPullbackFunctor_canonicalSquare` this is the third
and last property the converse direction of Stacks 0CMV asks of the comparison.

The hypothesis is the condition of Stacks 06CU for `Δ_f`, read at the cone; it gives essential
surjectivity of the comparison of `Δ_f`'s square of Stacks 0CMR, and that is what the criterion
of Stacks 0CMW turns into fullness here. -/
theorem full_toCategoricalPullbackFunctor_canonicalSquare [IsCofiltered I]
    (E : I ⥤ BigFppfOver B S hS) (d : Cone E)
    (hd : RelativeDescentObj.{u, v, w, max (u + 1) v w, max u v} B S hS
      (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E d) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    (Cat.toCategoricalPullbackFunctor
      (canonicalSquare.{u, v, w, max (u + 1) v w, max u v} B S hS f E d)).Full := by
  have : IsFiltered Iᵒᵖ := (isFiltered_op_iff_isCofiltered I).2 inferInstance
  exact full_toCategoricalPullbackFunctor_canonicalSquare_of_essSurj_diagonal B S hS 𝒳 𝒴 f E d
    (essSurj_toCategoricalPullbackFunctor_canonicalSquare.{u, v, w, max (u + 1) v w, max u v}
      B S hS (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E d hd)

end AlgebraicGeometry.Stack

end
