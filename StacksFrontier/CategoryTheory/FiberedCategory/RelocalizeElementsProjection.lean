module

public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsMap
public import StacksFrontier.CategoryTheory.FiberedCategory.RelocalizeAsElements

/-!
# The structural morphism of a lower-shriek extension, on categories of elements

Let `a : A ⟶ X` be a morphism of a category `C` and let `H` be a presheaf of sets on `C/A`. The
lower-shriek extension `Λ_a H` of Stacks 03I5 part (2) comes with a structural morphism
`Λ_a H ⟶ h_{A/X}` to the presheaf represented by `A/X`
(`CategoryTheory.OverShriek.relocalizeToYoneda`), reading off the factorization that a section
carries. This file records what that morphism does on categories of elements: composing the
identification `El_{C/A} H ≅ El_{C/X} (Λ_a H)` of
`CategoryTheory.PresheafOfCategories.relocalizeToElements` with the induced functor of categories
of elements gives the projection of `El_{C/A} H` to `C/A` followed by
`CategoryTheory.PresheafOfCategories.overMapToElements`, on the nose.

That identity is the commuting square which, through
`CategoryTheory.PresheafOfCategories.natTrans_app_sectionOfObj_of_comp_eq`, identifies the
morphism of representing presheaves induced by the first projection of a base change with the
structural morphism of the extension.

## Main results

* `CategoryTheory.PresheafOfCategories.relocalizeToElements_comp_elementsMap`: the identity
  above.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.PresheafOfCategories

universe v u

variable {C : Type u} [Category.{v} C] {X A : C} (a : A ⟶ X) (H : (Over A)ᵒᵖ ⥤ Type v)

/-- **The structural morphism of a lower-shriek extension, read on categories of elements.** A
section of `H` over `V : C/A`, carried into `El (Λ_a H)` and then pushed along the structural
morphism `Λ_a H ⟶ h_{A/X}`, is the relocalization of `V` read as an element of the presheaf
represented by `A/X`: both name the structure morphism of `V`. -/
lemma relocalizeToElements_comp_elementsMap :
    relocalizeToElements a H ⋙ elementsMap (OverShriek.relocalizeToYoneda a H) =
      (presheafOfCategories (H ⋙ typeToCat)).p ⋙ overMapToElements a :=
  rfl

end CategoryTheory.PresheafOfCategories

end
