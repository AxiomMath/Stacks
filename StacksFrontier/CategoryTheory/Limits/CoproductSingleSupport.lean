module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# A coproduct with a single nonvanishing summand

A coproduct `∐ A` in a preadditive category all but one of whose summands are zero objects is
that one summand.

## Main definitions

* `CategoryTheory.Limits.coprodIsoOfSingleSupport`: the isomorphism `∐ A ≅ A i₀`, for a family
  `A : ι → D` with `IsZero (A i)` for every `i ≠ i₀`.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Limits

/-- A coproduct all but one of whose summands vanish is that summand. -/
public def coprodIsoOfSingleSupport {D : Type*} [Category D] [Preadditive D] {ι : Type*}
    (A : ι → D) [HasCoproduct A] (i₀ : ι) (h : ∀ i, i ≠ i₀ → IsZero (A i)) :
    ∐ A ≅ A i₀ := by
  classical
  refine ⟨Sigma.desc (fun i => if hi : i = i₀ then eqToHom (congrArg A hi) else 0),
    Sigma.ι A i₀, ?_, by simp⟩
  refine Sigma.hom_ext _ _ fun i => ?_
  by_cases hi : i = i₀
  · subst hi
    simp
  · exact (h i hi).eq_of_src _ _

end CategoryTheory.Limits

end
