module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPolynomialModel

/-!
# The presheaf of polynomial rings is functorial in the family of variables

The free algebra sheaf `A[E]` is functorial in the presheaf of sets `E`, by
`Stacks.SheafOfModules.freeAlgebraMap`.  Before sheafification the same is true of the presheaf
of polynomial rings `U ↦ A(U)[E(U)]`, and this file records that morphism: a morphism
`h : E₁ ⟶ E₂` of presheaves of sets renames the variables.

The point of having it is that the degree `-1` comparison of two presentations is studied on
sections of the polynomial model, where a section is an honest polynomial, and the comparison
of the two presentations there is this morphism.  The sheaf-level `freeAlgebraMap` is of no use
for that: its sections are not polynomials.

## Main definitions

* `Stacks.Sites.FreeAlgebra.polynomialPresheafMap`: the morphism of presheaves of commutative
  rings `A(-)[E₁(-)] ⟶ A(-)[E₂(-)]` renaming the variables along `h : E₁ ⟶ E₂`.

## Main results

* `Stacks.Sites.FreeAlgebra.polynomialCoefficientMap_comp_polynomialPresheafMap`: it is a
  morphism of `A`-algebras.
* `Stacks.Sites.FreeAlgebra.polynomialPresheafMap_comp_polynomialEvaluation`: a morphism of
  families of generators makes it a factorisation of one polynomial presentation through the
  other.
* `Stacks.Sites.FreeAlgebra.polynomialPresheafMap_comp_polynomialUnit`: it is compatible with
  the sheafification units, the sheaf-level morphism being `freeAlgebraMap`.

## Implementation notes

The morphism is written as `MvPolynomial.eval₂Hom MvPolynomial.C (fun x ↦ MvPolynomial.X (h x))`
rather than as `MvPolynomial.rename (h x)`, which it equals: the restriction maps of
`polynomialPresheaf` are themselves `eval₂Hom`s, and only at that spelling do the `eval₂Hom_C`
and `eval₂Hom_X'` equations match the goals.  Against `rename` they do not: its coercion to a
ring homomorphism carries `AddMonoidAlgebra.nonAssocSemiring` where the presheaf's object
carries the `CommRingCat.of` instance, and the two, though definitionally equal, are not
syntactically equal, so no rewrite fires.

## References

* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU), the free algebra
  sheaf.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), whose degree `-1`
  comparison is read along this morphism on the polynomial model.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w

namespace Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Sheaf J CommRingCat.{w}) {E₁ E₂ : Functor Cᵒᵖ (Type w)} (h : E₁ ⟶ E₂)

/-- The morphism of presheaves of commutative rings `A(U)[E₁(U)] ⟶ A(U)[E₂(U)]` renaming the
variables along a morphism `h : E₁ ⟶ E₂` of presheaves of sets.  It is the identity on
coefficients and sends the variable `x` to the variable `h x`. -/
noncomputable def polynomialPresheafMap :
    polynomialPresheaf J A E₁ ⟶ polynomialPresheaf J A E₂ where
  app U := CommRingCat.ofHom
    (MvPolynomial.eval₂Hom MvPolynomial.C (fun x ↦ MvPolynomial.X (h.app U x)))
  naturality := by
    intro U V f
    dsimp only [polynomialPresheaf]
    ext <;> simp [NatTrans.naturality_apply h f]

/-- The renaming morphism, on a coefficient. -/
theorem polynomialPresheafMap_app_C (U : Cᵒᵖ) (r : A.obj.obj U) :
    (polynomialPresheafMap J A h).app U (MvPolynomial.C r) =
      (MvPolynomial.C r : MvPolynomial (E₂.obj U) (A.obj.obj U)) :=
  MvPolynomial.eval₂Hom_C _ _ r

/-- The renaming morphism, on a variable. -/
theorem polynomialPresheafMap_app_X (U : Cᵒᵖ) (x : E₁.obj U) :
    (polynomialPresheafMap J A h).app U (MvPolynomial.X x) =
      (MvPolynomial.X (h.app U x) : MvPolynomial (E₂.obj U) (A.obj.obj U)) :=
  MvPolynomial.eval₂Hom_X' _ _ x

/-- The renaming morphism is a morphism of `A`-algebras. -/
theorem polynomialCoefficientMap_comp_polynomialPresheafMap :
    polynomialCoefficientMap J A E₁ ≫ polynomialPresheafMap J A h =
      polynomialCoefficientMap J A E₂ := by
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  refine RingHom.ext fun r ↦ ?_
  exact polynomialPresheafMap_app_C J A h U r

variable (B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
  (α₁ : E₁ ⟶ underlyingPresheaf J B) (α₂ : E₂ ⟶ underlyingPresheaf J B)

/-- A morphism of families of generators makes the renaming morphism a factorisation of one
polynomial presentation through the other. -/
theorem polynomialPresheafMap_comp_polynomialEvaluation (hα : h ≫ α₂ = α₁) :
    polynomialPresheafMap J A h ≫ polynomialEvaluation J A B E₂ a α₂ =
      polynomialEvaluation J A B E₁ a α₁ := by
  subst hα
  apply NatTrans.ext
  funext U
  dsimp only [polynomialPresheaf, polynomialEvaluation, polynomialPresheafMap]
  ext <;> simp

variable [HasWeakSheafify J CommRingCat.{w}]

/-- The renaming morphism is compatible with the sheafification units: followed by the unit of
`A[E₂]` it is the unit of `A[E₁]` followed by the morphism `A[E₁] ⟶ A[E₂]` of free algebra
sheaves, which is `Stacks.SheafOfModules.freeAlgebraMap`. -/
theorem polynomialPresheafMap_comp_polynomialUnit :
    polynomialPresheafMap J A h ≫ polynomialUnit J A E₂ =
      polynomialUnit J A E₁ ≫ (freeAlgebraSheafDesc J A (freeAlgebraSheaf J A E₂) E₁
        (freeAlgebraSheafCoefficientMap J A E₂)
        (h ≫ freeAlgebraSheafVariable J A E₂)).hom := by
  rw [polynomialUnit_comp_desc J A (freeAlgebraSheaf J A E₂) E₁
    (freeAlgebraSheafCoefficientMap J A E₂) (h ≫ freeAlgebraSheafVariable J A E₂)]
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    refine Eq.trans ?_ (MvPolynomial.eval₂Hom_C
      ((freeAlgebraSheafCoefficientMap J A E₂).hom.app U).hom
      ((h ≫ freeAlgebraSheafVariable J A E₂).app U) r).symm
    refine Eq.trans (congrArg ((polynomialUnit J A E₂).app U)
      (polynomialPresheafMap_app_C J A h U r)) ?_
    exact congrArg (fun k : A.obj ⟶ (freeAlgebraSheaf J A E₂).obj ↦ k.app U r)
      (coefficientMap_comp_polynomialUnit J A E₂)
  · intro x
    refine Eq.trans ?_ (MvPolynomial.eval₂Hom_X'
      ((freeAlgebraSheafCoefficientMap J A E₂).hom.app U).hom
      ((h ≫ freeAlgebraSheafVariable J A E₂).app U) x).symm
    exact congrArg ((polynomialUnit J A E₂).app U) (polynomialPresheafMap_app_X J A h U x)

end Stacks.Sites.FreeAlgebra

end
