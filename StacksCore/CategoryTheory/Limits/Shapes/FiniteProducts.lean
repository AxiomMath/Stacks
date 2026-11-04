module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.Data.Set.Finite.Basic

/-! ## Coproducts of families with finitely many nonzero terms

A family of objects that is zero outside a finite set of indices has a coproduct as soon as the
category has finite coproducts: take the coproduct of the finitely many possibly nonzero members,
with the unique map out of each zero member as the remaining inclusion. No zero morphisms are
needed, since a zero object has a unique morphism to anything.

This is the "for each `n` at most finitely many `A^{p, n - p}` are nonzero" half of the existence
remark after Stacks 012Z. Its graded-object and total-complex readings are
`CategoryTheory.GradedObject.hasMap_of_finite` and `HomologicalComplex₂.hasTotal_of_finite`.
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C]

/-- A family that is zero outside a finite set of indices has a coproduct when finite coproducts
exist. -/
theorem hasCoproduct_of_finite_not_isZero {J : Type*} [HasFiniteCoproducts C] (f : J → C)
    (hf : {j | ¬ IsZero (f j)}.Finite) : HasCoproduct f :=
  HasColimit.mk
    { cocone := Cofan.mk (∐ fun j : hf.toFinset => f j) fun j =>
        open scoped Classical in
        if h : IsZero (f j) then h.to_ _
        else Sigma.ι (fun j : hf.toFinset => f j) ⟨j, hf.mem_toFinset.2 h⟩
      isColimit := Cofan.IsColimit.mk _ (fun t => Sigma.desc fun j : hf.toFinset => t.inj j)
        (fun t j => by
          by_cases h : IsZero (f j)
          · exact h.eq_of_src _ _
          · simp [h])
        (fun t m hm => Sigma.hom_ext (f := fun j : hf.toFinset => f j) _ _ fun j => by
          have hj : ¬ IsZero (f j) := hf.mem_toFinset.1 j.2
          simpa [hj] using hm j) }

end CategoryTheory.Limits
