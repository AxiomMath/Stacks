module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Exactness of a short complex of functors on a discrete category

A functor category `Discrete α ⥤ D` over an abelian category `D` is abelian, and its homology is
computed componentwise. So a short complex of such functors is exact as soon as each of its
components is, with no finiteness or smallness assumption on the index type `α`.

This is the form in which the exactness of a product of complexes enters the Čech theory: a term
of a Čech complex is a product over the tuples of members of a covering, and that product is a
limit over a discrete index category.

## Main results

* `CategoryTheory.ShortComplex.exact_of_app_discrete`: a short complex of functors on a discrete
  category is exact as soon as it is exact in each component.
-/

@[expose] public section

namespace CategoryTheory

open Limits

namespace ShortComplex

/-- **A short complex of functors on a discrete category is exact as soon as it is exact in each
component.** Evaluation preserves homology, and a functor on a discrete category is zero as soon
as all its values are. -/
lemma exact_of_app_discrete {α : Type*} {D : Type*} [Category* D] [Abelian D]
    (S : ShortComplex (Discrete α ⥤ D))
    (h : ∀ x, (S.map ((evaluation (Discrete α) D).obj x)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  refine Functor.isZero _ fun x ↦ ?_
  exact IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).1 (h x))
    (S.mapHomologyIso ((evaluation (Discrete α) D).obj x)).symm

end ShortComplex

end CategoryTheory

end
