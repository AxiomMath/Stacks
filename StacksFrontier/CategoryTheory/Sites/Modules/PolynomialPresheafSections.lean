module

public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheaf

/-!
# Sections of the presheaf of polynomial rings

A section of the presheaf `U ↦ A(U)[E(U)]` over `U` is an honest polynomial, and this file
records how the structure of such a section is read: the restriction maps and the evaluation
morphisms on a coefficient `C r` and on a variable `X x`, and — the point of the file — that
restricting a polynomial can only produce variables that are restrictions of its variables.

The last statement is what makes a finite set of variables of a section survive restriction: a
section of `A(-)[E(-)]` over `U` involves finitely many variables, and over any `V → U` the
restricted section involves only their restrictions.  The degree `-1` comparison of two
presentations is computed on the polynomial model, where it needs exactly this.

## Main results

* `Stacks.Sites.FreeAlgebra.polynomialPresheaf_map_C` and
  `Stacks.Sites.FreeAlgebra.polynomialPresheaf_map_X`: restriction in `A(-)[E(-)]` restricts a
  coefficient along `A` and a variable along `E`.
* `Stacks.Sites.FreeAlgebra.polynomialEvaluation_app_C` and
  `Stacks.Sites.FreeAlgebra.polynomialEvaluation_app_X`: evaluation along `(a, e)` sends a
  coefficient through `a` and the variable `x` to `e(x)`.
* `Stacks.Sites.FreeAlgebra.polynomialPresheaf_map_eq_rename_comp_map`: the restriction
  homomorphism is renaming the variables along `E.map f` after mapping the coefficients along
  `A.obj.map f`.
* `Stacks.Sites.FreeAlgebra.exists_vars_of_mem_vars_polynomialPresheaf_map`: every variable of a
  restricted polynomial is the restriction of a variable of the polynomial.

## Implementation notes

The conclusion of `exists_vars_of_mem_vars_polynomialPresheaf_map` is stated as
`∃ x ∈ p.vars, E.map f x = i` rather than as a membership in `p.vars.image (E.map f)`, so that
no `DecidableEq (E.obj V)` instance is required; `MvPolynomial.mem_vars_rename` is Mathlib's
`vars_rename` already packaged in that form.

`polynomialPresheaf_map_eq_rename_comp_map` is used only to transport a `vars` membership across
an equality of ring homomorphisms.  It is not a licence to spell the restriction maps of
`polynomialPresheaf` as `MvPolynomial.rename`: the coercion of `rename` to a ring homomorphism
carries `AddMonoidAlgebra.nonAssocSemiring` where the presheaf's object carries the
`CommRingCat.of` instance, and the two, though definitionally equal, are not syntactically
equal, so `MvPolynomial.eval₂Hom_C` and `MvPolynomial.eval₂Hom_X'` no longer fire against it.
That is why the lemmas on `C` and `X` above are proved against the `eval₂Hom` spelling.

## References

* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU), the free algebra
  sheaf, whose presheaf model is `polynomialPresheaf`.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), whose degree `-1`
  comparison is computed on sections of that model.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w

namespace Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Sheaf J CommRingCat.{w}) (E : Functor Cᵒᵖ (Type w))

/-- Restriction in `A(-)[E(-)]` sends the coefficient `C r` to the coefficient `C` of the
restriction of `r`. -/
theorem polynomialPresheaf_map_C {U V : Cᵒᵖ} (f : U ⟶ V) (r : A.obj.obj U) :
    (polynomialPresheaf J A E).map f (MvPolynomial.C r) =
      MvPolynomial.C (A.obj.map f r) :=
  MvPolynomial.eval₂Hom_C _ _ r

/-- Restriction in `A(-)[E(-)]` sends the variable `X x` to the variable `X` of the restriction
of `x`. -/
theorem polynomialPresheaf_map_X {U V : Cᵒᵖ} (f : U ⟶ V) (x : E.obj U) :
    (polynomialPresheaf J A E).map f (MvPolynomial.X x) =
      MvPolynomial.X (E.map f x) :=
  MvPolynomial.eval₂Hom_X' _ _ x

/-- The restriction homomorphism of `A(-)[E(-)]` along `f` factors as mapping the coefficients
along `A.obj.map f` followed by renaming the variables along `E.map f`. -/
theorem polynomialPresheaf_map_eq_rename_comp_map {U V : Cᵒᵖ} (f : U ⟶ V) :
    (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A.obj.map f).hom)
        (fun x ↦ MvPolynomial.X (E.map f x)) :
        MvPolynomial (E.obj U) (A.obj.obj U) →+* MvPolynomial (E.obj V) (A.obj.obj V)) =
      (MvPolynomial.rename (E.map f)).toRingHom.comp
        (MvPolynomial.map (A.obj.map f).hom) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro x
    simp

/-- Every variable of the restriction of a polynomial `p` is the restriction of a variable of
`p`.  In particular a section of `A(-)[E(-)]` over `U` restricts, over any `V → U`, to a
polynomial in the restrictions of its own finitely many variables. -/
theorem exists_vars_of_mem_vars_polynomialPresheaf_map {U V : Cᵒᵖ} (f : U ⟶ V)
    (p : (polynomialPresheaf J A E).obj U) {i : E.obj V}
    (hi : i ∈ ((polynomialPresheaf J A E).map f p).vars) :
    ∃ x ∈ p.vars, E.map f x = i := by
  have hp : ((polynomialPresheaf J A E).map f p :
      MvPolynomial (E.obj V) (A.obj.obj V)) =
      MvPolynomial.rename (E.map f) (MvPolynomial.map (A.obj.map f).hom p) :=
    RingHom.congr_fun (polynomialPresheaf_map_eq_rename_comp_map J A E f) p
  have hi' : i ∈ (MvPolynomial.rename (E.map f)
      (MvPolynomial.map (A.obj.map f).hom p)).vars := by
    rw [← hp]
    exact hi
  obtain ⟨x, hx, hxi⟩ := MvPolynomial.mem_vars_rename (E.map f)
    (MvPolynomial.map (A.obj.map f).hom p) hi'
  exact ⟨x, MvPolynomial.vars_map p (A.obj.map f).hom hx, hxi⟩

variable (B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) (e : E ⟶ underlyingPresheaf J B)

/-- Evaluation `A(U)[E(U)] → B(U)` along `(a, e)` sends the coefficient `C r` to `a(r)`. -/
theorem polynomialEvaluation_app_C (U : Cᵒᵖ) (r : A.obj.obj U) :
    (polynomialEvaluation J A B E a e).app U (MvPolynomial.C r) = a.hom.app U r :=
  MvPolynomial.eval₂Hom_C _ _ r

/-- Evaluation `A(U)[E(U)] → B(U)` along `(a, e)` sends the variable `X x` to `e(x)`. -/
theorem polynomialEvaluation_app_X (U : Cᵒᵖ) (x : E.obj U) :
    (polynomialEvaluation J A B E a e).app U (MvPolynomial.X x) = e.app U x :=
  MvPolynomial.eval₂Hom_X' _ _ x

end Stacks.Sites.FreeAlgebra

end
