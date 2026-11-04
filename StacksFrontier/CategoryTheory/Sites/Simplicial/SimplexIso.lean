module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Isomorphisms in the opposite of the simplex category

An isomorphism of the simplex category is an identity, so an isomorphism in the opposite
category is the transport along an equality of its endpoints. This is the form in which the
simplicial-site constructions use it: an isomorphism of the index category of a simplicial
diagram can be eliminated by `cases`.

## Main results

* `SimplexCategory.exists_eq_eqToHom_of_isIso`: an isomorphism in `SimplexCategoryᵒᵖ` is
  `eqToHom` for an equality of its endpoints.

## References

* [Stacks Project, Tag 09WC](https://stacks.math.columbia.edu/tag/09WC)
* [Stacks Project, Tag 09WD](https://stacks.math.columbia.edu/tag/09WD)
-/

@[expose] public section

open CategoryTheory

namespace SimplexCategory

/-- An isomorphism in the opposite of the simplex category is the transport along an equality
of its endpoints. -/
theorem exists_eq_eqToHom_of_isIso {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) [IsIso f] :
    ∃ h : a = b, f = eqToHom h := by
  cases a with
  | op a =>
    cases b with
    | op b =>
      have hlen : b.len = a.len := SimplexCategory.len_eq_of_isIso f.unop
      have hab : a = b := by cases a; cases b; simp_all
      subst b
      refine ⟨rfl, ?_⟩
      have hf : f.unop = 𝟙 a := SimplexCategory.eq_id_of_isIso f.unop
      simpa using congrArg Quiver.Hom.op hf

end SimplexCategory

end
