module

public import Mathlib.CategoryTheory.Adjunction.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The adjunct of a morphism out of a composite left adjoint

Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be composable adjunctions, so that
`CategoryTheory.Adjunction.comp` makes `L₁ ⋙ L₂` a left adjoint of `R₂ ⋙ R₁`.  A morphism out of
`(L₁ ⋙ L₂).obj X` which is given as `L₂` of a morphism followed by another morphism — the shape
the left-hand side of a composition law for the two left adjoints has — has an adjunct along the
composite adjunction, and this file computes it: it is the adjunct of the first morphism followed
by `R₁` of the adjunct of the second.

This is the step every composition law for a pair of left adjoints is proved by.  Such a law
cannot be checked on elements, a left adjoint having no formula; its adjunct is a morphism into a
composite right adjoint, where the two factors are available separately and the law can be
proved there.

## Main results

* `Stacks.CategoryTheory.homEquiv_comp_map_comp`: the computation.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u₃} [Category.{v₃} C]

/-- **The adjunct, along a composite of two adjunctions, of the second left adjoint applied to
one morphism followed by another**: it is the two adjuncts, the second read through the first
right adjoint.

This is `CategoryTheory.Adjunction.comp_homEquiv`, which splits a transpose along a composite
adjunction into the two one-step transposes, together with the two naturality statements for the
hom-set bijection. -/
@[ega "0 4.4.8" "more general"]
theorem homEquiv_comp_map_comp {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {X : A} {Y : B} {Z : C}
    (f : L₁.obj X ⟶ Y) (g : L₂.obj Y ⟶ Z) :
    (adj₁.comp adj₂).homEquiv X Z (L₂.map f ≫ g) =
      adj₁.homEquiv X Y f ≫ R₁.map (adj₂.homEquiv Y Z g) := by
  rw [Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]

universe v₄ u₄

variable {D : Type u₄} [Category.{v₄} D]

/-- **Transposing along a composite of three adjunctions, innermost factor first.** The transpose
of `L₃.map f ≫ g` along `adj₁.comp (adj₂.comp adj₃)` is the transpose along `adj₁` of the
transpose along `adj₂` of `f` followed by the transpose of `g` along `adj₃`: the innermost
transpose is taken first, and `f` leaves it by naturality of the hom-set bijection in its left
argument.

This is the threefold counterpart of `Stacks.CategoryTheory.homEquiv_comp_map_comp`, which it is
*not* an instance of: see the implementation notes. It is the step that splits the transposition
along `CategoryTheory.CocontinuousSimplicialSite.transitionModulePullbackAdjunctionB` --
restriction of presheaves of modules along the transition functor, extension of scalars along the
transition ring map, sheafification -- into its three concrete factors. -/
theorem homEquiv_comp_comp_map_comp {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₃ : C ⥤ D} {R₃ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (X : A) {Y : C} {Z : D} (f : L₂.obj (L₁.obj X) ⟶ Y) (g : L₃.obj Y ⟶ Z) :
    (adj₁.comp (adj₂.comp adj₃)).homEquiv X Z (L₃.map f ≫ g) =
      adj₁.homEquiv X (R₂.obj (R₃.obj Z))
        (adj₂.homEquiv (L₁.obj X) (R₃.obj Z) (f ≫ adj₃.homEquiv Y Z g)) := by
  rw [Adjunction.comp_homEquiv]
  refine congrArg (adj₁.homEquiv X (R₂.obj (R₃.obj Z))) ?_
  rw [Adjunction.comp_homEquiv]
  exact congrArg (adj₂.homEquiv (L₁.obj X) (R₃.obj Z))
    (adj₃.homEquiv_naturality_left f g)

end Stacks.CategoryTheory

end
