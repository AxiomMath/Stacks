module

public import Mathlib.CategoryTheory.Filtered.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Cofiltered diagrams (Stacks 04AZ)

Stacks 04AZ is the formal dual of Stacks 002V. A **diagram** `M : I ⥤ C` is
*cofiltered* (or *codirected*) when `I` is nonempty, any two objects of `I`
admit morphisms from a common object, and any two parallel morphisms
`a, b : x ⟶ y` of `I` become equal after precomposing with some `c : w ⟶ x`
**and applying `M`**: `M.map (c ≫ a) = M.map (c ≫ b)`. An **index category**
`I` is then cofiltered when the identity diagram `𝟭 I` is.

Only the diagram version is new content here: the index-category version is
Mathlib's `CategoryTheory.IsCofiltered`, which already carries this tag. So this
file defines `CategoryTheory.Functor.IsCofiltered` for a diagram and then
records the comparison `(𝟭 I).IsCofiltered ↔ IsCofiltered I`, rather than
introducing a second constant for cofiltered index categories.

The condition on objects is phrased as `∃ z (_ : z ⟶ x) (_ : z ⟶ y), True`,
matching `CategoryTheory.IsCofilteredOrEmpty.cone_objs`, so that the comparison
lemma is a pure repackaging. The index and target categories are implicit: both
are determined by `M`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

/-- **Stacks 04AZ.** A diagram `M : I ⥤ C` is *cofiltered* (or *codirected*) if
`I` is nonempty, every pair of objects of `I` admits morphisms from a common
object, and every pair of parallel morphisms of `I` is equalized, after applying
`M`, by precomposition with a further morphism. -/
@[stacks_fixed 04AZ, sga "4 I 2.7" "cofiltered"]
structure Functor.IsCofiltered {I : Type u₁} [Category.{v₁} I] {C : Type u₂} [Category.{v₂} C]
    (M : I ⥤ C) : Prop where
  /-- The category `I` has at least one object. -/
  nonempty : Nonempty I
  /-- For every pair of objects `x, y` of `I` there exist an object `z` and
  morphisms `z ⟶ x`, `z ⟶ y`. -/
  cone_objs : ∀ x y : I, ∃ (z : I) (_ : z ⟶ x) (_ : z ⟶ y), True
  /-- For every pair of parallel morphisms `a, b : x ⟶ y` of `I` there exist an
  object `w` and a morphism `c : w ⟶ x` with `M.map (c ≫ a) = M.map (c ≫ b)`. -/
  cone_maps : ∀ ⦃x y : I⦄ (a b : x ⟶ y),
    ∃ (w : I) (c : w ⟶ x), M.map (c ≫ a) = M.map (c ≫ b)

/-- **Stacks 04AZ.** An index category `I` is cofiltered in the sense of Stacks —
the identity diagram `𝟭 I` is a cofiltered diagram — exactly when it is
cofiltered in the sense of Mathlib's `CategoryTheory.IsCofiltered`. Since
`(𝟭 I).map f = f`, condition (3) for `𝟭 I` reads `c ≫ a = c ≫ b` in `I`, so both
directions are a repackaging of the same data. -/
@[stacks 04AZ]
theorem Functor.isCofiltered_id_iff (I : Type u₁) [Category.{v₁} I] :
    (𝟭 I).IsCofiltered ↔ _root_.CategoryTheory.IsCofiltered I :=
  ⟨fun h =>
      @_root_.CategoryTheory.IsCofiltered.mk _ _ ⟨h.cone_objs, h.cone_maps⟩ h.nonempty,
    fun h => ⟨h.nonempty, h.cone_objs, h.cone_maps⟩⟩

end CategoryTheory
