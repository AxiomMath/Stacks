module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatCategoricalPullback
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# A square of `Cat` whose comparison is an equivalence is a 2-fibre product

`CategoryTheory.Cat.isEquivalence_toCategoricalPullbackFunctor` says that the comparison functor
out of a 2-fibre product of a cospan of `Cat` into the explicit 2-fibre product of Stacks 003R is
an equivalence. This file proves the converse: a 2-commutative square of `Cat` whose comparison
functor is an equivalence of categories *is* a 2-fibre product (**Stacks 003Q**).

## Main results

* `CategoryTheory.Cat.isTwoFibreProduct_of_isEquivalence_toCategoricalPullbackFunctor`: a
  2-commutative square of `Cat` whose comparison functor into the explicit 2-fibre product is an
  equivalence is a 2-fibre product.
* `CategoryTheory.Cat.nonempty_isTwoFibreProduct_of_isEquivalence_toCategoricalPullbackFunctor`:
  the same conclusion as a `Nonempty`.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 003R](https://stacks.math.columbia.edu/tag/003R)
* [Stacks Project, Tag 02X9](https://stacks.math.columbia.edu/tag/02X9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

namespace CategoryTheory.Cat

universe v u

variable {A B C : Cat.{v, max u v}} {F : A ⟶ C} {G : B ⟶ C}

/-- **The converse of `CategoryTheory.Cat.isEquivalence_toCategoricalPullbackFunctor`.** A
2-commutative square of `Cat` whose comparison functor into the explicit 2-fibre product of
Stacks 003R is an equivalence of categories is itself a 2-fibre product of the cospan. -/
noncomputable def isTwoFibreProduct_of_isEquivalence_toCategoricalPullbackFunctor
    (P : TwoCommSq F G) (h : (toCategoricalPullbackFunctor P).IsEquivalence) :
    IsTwoFibreProduct P :=
  letI := h
  let e := (toCategoricalPullbackFunctor P).asEquivalence
  isTwoFibreProduct_of_section (isTwoFibreProduct_categoricalPullbackSq F G)
    ((preHomCategoricalPullback P).ofSection e.inverse.toCatHom (Cat.Hom.isoMk e.counitIso))
    (toCategoricalPullback P) (Cat.Hom.isoMk e.unitIso.symm)

/-- A 2-commutative square of `Cat` whose comparison functor into the explicit 2-fibre product is
an equivalence of categories admits a structure of 2-fibre product. -/
theorem nonempty_isTwoFibreProduct_of_isEquivalence_toCategoricalPullbackFunctor
    (P : TwoCommSq F G) (h : (toCategoricalPullbackFunctor P).IsEquivalence) :
    Nonempty (IsTwoFibreProduct P) :=
  ⟨isTwoFibreProduct_of_isEquivalence_toCategoricalPullbackFunctor P h⟩

end CategoryTheory.Cat

end
