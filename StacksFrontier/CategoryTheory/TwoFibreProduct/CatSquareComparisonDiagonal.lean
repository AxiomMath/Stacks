module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatCategoricalPullback
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CategoricalPullbackSquareDiagonal

/-!
# The comparison of a square of `Cat` is the comparison of its underlying functors

`CategoryTheory.Cat.toCategoricalPullbackFunctor` compares the apex of a 2-commutative square
of `Cat` with the explicit 2-fibre product of its two legs, and
`CategoryTheory.Limits.CategoricalPullback.squareComparison` does the same for a 2-commutative
square of plain categories. A square of `Cat` is a square of categories whose filler is a
2-isomorphism of `Cat`, and the two comparison functors agree once that 2-isomorphism is read as a
natural isomorphism of functors. Consequently the criterion of Stacks 0CMW
(`CategoryTheory.Limits.CategoricalPullback.fullyFaithful_squareComparison_iff`) holds for squares
of `Cat`.

## Main definitions

* `CategoryTheory.Cat.squareDiagonalComparison`: the comparison functor of the square of relative
  diagonals of a 2-commutative square of `Cat`.

## Main results

* `CategoryTheory.Cat.toCategoricalPullbackFunctor_eq_squareComparison`: the two comparison
  functors agree.
* `CategoryTheory.Cat.full_toCategoricalPullbackFunctor_of_essSurj_squareDiagonalComparison`: that
  comparison is full as soon as the comparison of the square of relative diagonals is essentially
  surjective.
* `CategoryTheory.Cat.fullyFaithful_toCategoricalPullbackFunctor_iff`: for a 2-commutative square
  of `Cat` whose two upper and left corners are groupoids, the comparison out of the apex is fully
  faithful if and only if the comparison of the square of relative diagonals is an equivalence.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 003R](https://stacks.math.columbia.edu/tag/003R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

namespace CategoryTheory.Cat

universe v u

variable {A B C : Cat.{v, max u v}} {F : A ⟶ C} {G : B ⟶ C}

/-- **The comparison functor of a square of `Cat` is the comparison functor of the underlying
square of categories.** Both send an object `x` of the apex to the triple
`(fst x, snd x, φ_x)`. -/
lemma toCategoricalPullbackFunctor_eq_squareComparison (P : TwoCommSq F G) :
    toCategoricalPullbackFunctor P =
      CategoricalPullback.squareComparison P.fst.toFunctor P.snd.toFunctor F.toFunctor
        G.toFunctor (Cat.Hom.toNatIso P.iso) :=
  rfl

/-- **The comparison `B` of the square of relative diagonals of a 2-commutative square of
`Cat`**: the functor `P.pt ⥤ A ×_{Δ_F, A ×_C A} (P.pt ×_B P.pt)`. -/
noncomputable abbrev squareDiagonalComparison (P : TwoCommSq F G) :=
  CategoricalPullback.diagonalComparison P.fst.toFunctor P.snd.toFunctor F.toFunctor
    G.toFunctor (Cat.Hom.toNatIso P.iso)

/-- **The fullness half of Stacks 0CMW for a 2-commutative square of `Cat`.** If the codomains of
the two legs out of the apex are groupoids then the comparison out of the apex into the explicit
2-fibre product is full as soon as the comparison of the square of relative diagonals is
essentially surjective. -/
theorem full_toCategoricalPullbackFunctor_of_essSurj_squareDiagonalComparison (P : TwoCommSq F G)
    [IsGroupoid (A : Type (max u v))] [IsGroupoid (B : Type (max u v))]
    (h : (squareDiagonalComparison P).EssSurj) :
    (toCategoricalPullbackFunctor P).Full := by
  rw [toCategoricalPullbackFunctor_eq_squareComparison]
  exact CategoricalPullback.full_squareComparison_of_essSurj_diagonalComparison _ _ _ _ _ h

/-- **Stacks 0CMW for a 2-commutative square of `Cat`.** If the codomains of the two legs out of
the apex are groupoids then the comparison out of the apex into the explicit 2-fibre product is
fully faithful exactly when the comparison of the square of relative diagonals is an
equivalence. -/
theorem fullyFaithful_toCategoricalPullbackFunctor_iff (P : TwoCommSq F G)
    [IsGroupoid (A : Type (max u v))] [IsGroupoid (B : Type (max u v))] :
    ((toCategoricalPullbackFunctor P).Full ∧ (toCategoricalPullbackFunctor P).Faithful) ↔
      (squareDiagonalComparison P).IsEquivalence := by
  rw [toCategoricalPullbackFunctor_eq_squareComparison]
  exact CategoricalPullback.fullyFaithful_squareComparison_iff _ _ _ _ _

end CategoryTheory.Cat

end
