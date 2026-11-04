module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPolynomialSquareDescent
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPolynomialTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.PolynomialPresheafMap

/-!
# Descending a square membership on the polynomial model of a presentation

Let `α₁ : E₁ ⟶ B` and `α₂ : E₂ ⟶ B` be two families of generators of a sheaf of commutative
rings `B` over `A` on a site and let `h : E₁ ⟶ E₂` be a morphism of families with
`h ≫ α₂ = α₁`.  The injective half of the degree `-1` comparison of the two naive cotangent
complexes has to turn a square membership on the second polynomial model into one on the
first: a polynomial `q` over an object of the site, lying in the kernel of the first model and
with all of its partial derivatives there, whose image under the induced map lies in the
square of the kernel of the second model, should have `q` itself in the square of the kernel
of the first.

That is false over the object where `q` lives and true over a covering of it, because the
ring-level descent
`Stacks.Sites.Conormal.mem_ker_sq_of_rename_lift` consumes a lift through the first
presentation of each of the finitely many variables of the witness, and such a lift exists only
locally.  This file interposes that covering: the finite set of variables is computed where `q`
lives, the covering is the one on which their images in `B` lift, and the conclusion is about
the restriction of `q`.

## Main results

* `Stacks.Sites.FreeAlgebra.exists_covering_mem_ker_sq_polynomialPresheafMap`: **the covering
  on which a square membership descends.**

## Implementation notes

The hypothesis on the partial derivatives is read only over the object where `q` lives, not
over every further arrow: the ring-level descent truncates `q` to its own variables there, and
the covering enters afterwards, through the lifts alone.  That is the opposite of the
surjective half, where the polynomial is restricted first and its partial derivatives have to
be controlled after each restriction.

## References

* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1), part (2), the homotopy
  behind the descent.
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU), the free algebra
  sheaf, whose presheaf model carries these polynomials.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the independence of
  the naive cotangent complex from the presentation, whose degree `-1` comparison this serves.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w

namespace Stacks.Sites.FreeAlgebra

open Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
  (E₁ E₂ : Functor Cᵒᵖ (Type w)) (h : E₁ ⟶ E₂)
  (α₁ : E₁ ⟶ underlyingPresheaf J B) (α₂ : E₂ ⟶ underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (freeAlgebraSheafDesc J A B E₁ a α₁).hom]
  [Presheaf.IsLocallySurjective J (freeAlgebraSheafDesc J A B E₂ a α₂).hom]
  (hα : h ≫ α₂ = α₁)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Presheaf.IsLocallySurjective J (freeAlgebraSheafDesc J A B E₂ a α₂).hom] in
include hα in
/-- **A square membership on the second polynomial model descends, on a covering, to the
first.**  Let `q` lie in the kernel of the polynomial model of the first presentation and have
all of its partial derivatives there, that is let its conormal class be killed by the conormal
map, and let its image under the map of polynomial models lie in the square of the kernel of
the second.  Then on a covering sieve of the object where `q` lives every restriction of `q`
lies in the square of the kernel of the first model.

The covering is the one on which the images in `B` of the finitely many variables carrying the
witness of the square membership lift through the first presentation; over each of its arrows
the ring-level descent `Stacks.Sites.Conormal.mem_ker_sq_of_rename_lift` applies. -/
theorem exists_covering_mem_ker_sq_polynomialPresheafMap {W : C}
    (q : (polynomialPresheaf J A E₁).obj (op W))
    (hq : q ∈ kernelIdeal (polynomialEvaluation J A B E₁ a α₁) (op W))
    (hpd : ∀ i, MvPolynomial.pderiv i q ∈
      kernelIdeal (polynomialEvaluation J A B E₁ a α₁) (op W))
    (hsq : (polynomialPresheafMap J A h).app (op W) q ∈
      kernelIdeal (polynomialEvaluation J A B E₂ a α₂) (op W) ^ 2) :
    ∃ S : Sieve W, S ∈ J W ∧ ∀ (V : C) (m : V ⟶ W), S m →
      (polynomialPresheaf J A E₁).map m.op q ∈
        kernelIdeal (polynomialEvaluation J A B E₁ a α₁) (op V) ^ 2 := by
  classical
  obtain ⟨s, p, hvars, hp, hpsq⟩ := exists_finset_rename_mem_ker_sq_vars_subset
    ((polynomialEvaluation J A B E₂ a α₂).app (op W))
    ((polynomialPresheafMap J A h).app (op W)) q hsq
  obtain ⟨S, hS, hlift⟩ := exists_covering_forall_exists_lift
    (polynomialEvaluation J A B E₁ a α₁) J
    (s.image fun j ↦ (polynomialEvaluation J A B E₂ a α₂).app (op W) (MvPolynomial.X j))
  refine ⟨S, hS, fun V m hm ↦ ?_⟩
  refine mem_ker_sq_of_rename_lift
    ((polynomialEvaluation J A B E₁ a α₁).app (op W))
    ((polynomialEvaluation J A B E₂ a α₂).app (op W))
    ((polynomialPresheafMap J A h).app (op W))
    ((polynomialEvaluation J A B E₁ a α₁).app (op V))
    (B.obj.map m.op)
    ((polynomialPresheaf J A E₁).map m.op)
    ((polynomialCoefficientMap J A E₁).app (op W) ≫ (polynomialPresheaf J A E₁).map m.op)
    (congrArg (fun t : polynomialPresheaf J A E₁ ⟶ B.obj ↦ t.app (op W))
      (polynomialPresheafMap_comp_polynomialEvaluation J A h B a α₁ α₂ hα))
    (congrArg (fun t : A.obj ⟶ polynomialPresheaf J A E₂ ↦ t.app (op W))
      (polynomialCoefficientMap_comp_polynomialPresheafMap J A h))
    ((polynomialEvaluation J A B E₁ a α₁).naturality m.op) rfl
    q hq hpd s p hvars hp hpsq (fun j hj ↦ ?_)
  obtain ⟨t, ht⟩ := hlift V m hm
    ((polynomialEvaluation J A B E₂ a α₂).app (op W) (MvPolynomial.X j))
    (Finset.mem_image_of_mem _ hj)
  exact ⟨t, ht⟩

end Stacks.Sites.FreeAlgebra

end
