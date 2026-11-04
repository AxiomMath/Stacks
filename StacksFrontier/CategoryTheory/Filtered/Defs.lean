module

public import Mathlib.CategoryTheory.Filtered.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Filtered diagrams (Stacks 002V)

Stacks 002V defines *filtered* (or *directed*) in two stages. A **diagram**
`M : I ⥤ C` is filtered when `I` is nonempty, any two objects of `I` admit
morphisms into a common object, and any two parallel morphisms `a, b : x ⟶ y`
of `I` become equal after composing with some `c : y ⟶ z` **and applying `M`**:
`M.map (a ≫ c) = M.map (b ≫ c)`. An **index category** `I` is then filtered
when the identity diagram `𝟭 I` is.

Only the diagram version is new content here: the index-category version is
Mathlib's `CategoryTheory.IsFiltered`, which already carries this tag (with the
remark "They also define a diagram being filtered"). Accordingly this file
defines `CategoryTheory.Functor.IsFiltered` for a diagram and then records the
comparison `(𝟭 I).IsFiltered ↔ IsFiltered I`, rather than introducing a second
constant for filtered index categories.

The condition on objects is phrased as `∃ z (_ : x ⟶ z) (_ : y ⟶ z), True`,
matching `CategoryTheory.IsFilteredOrEmpty.cocone_objs`, so that the comparison
lemma is a pure repackaging. The index and target categories are implicit: both
are determined by `M`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

/-- **Stacks 002V.** A diagram `M : I ⥤ C` is *filtered* (or *directed*) if
`I` is nonempty, every pair of objects of `I` admits morphisms into a common
object, and every pair of parallel morphisms of `I` is equalized, after
applying `M`, by composition with a further morphism. -/
@[stacks_fixed 002V]
structure Functor.IsFiltered {I : Type u₁} [Category.{v₁} I] {C : Type u₂} [Category.{v₂} C]
    (M : I ⥤ C) : Prop where
  /-- The category `I` has at least one object. -/
  nonempty : Nonempty I
  /-- For every pair of objects `x, y` of `I` there exist an object `z` and
  morphisms `x ⟶ z`, `y ⟶ z`. -/
  cocone_objs : ∀ x y : I, ∃ (z : I) (_ : x ⟶ z) (_ : y ⟶ z), True
  /-- For every pair of parallel morphisms `a, b : x ⟶ y` of `I` there exist an
  object `z` and a morphism `c : y ⟶ z` with `M.map (a ≫ c) = M.map (b ≫ c)`. -/
  cocone_maps : ∀ ⦃x y : I⦄ (a b : x ⟶ y),
    ∃ (z : I) (c : y ⟶ z), M.map (a ≫ c) = M.map (b ≫ c)

/-- **Stacks 002V.** An index category `I` is filtered in the sense of Stacks —
the identity diagram `𝟭 I` is a filtered diagram — exactly when it is filtered
in the sense of Mathlib's `CategoryTheory.IsFiltered`. Since `(𝟭 I).map f = f`,
condition (3) for `𝟭 I` reads `a ≫ c = b ≫ c` in `I`, so both directions are a
repackaging of the same data. -/
@[stacks 002V]
theorem Functor.isFiltered_id_iff (I : Type u₁) [Category.{v₁} I] :
    (𝟭 I).IsFiltered ↔ _root_.CategoryTheory.IsFiltered I :=
  ⟨fun h =>
      @_root_.CategoryTheory.IsFiltered.mk _ _ ⟨h.cocone_objs, h.cocone_maps⟩ h.nonempty,
    fun h => ⟨h.nonempty, h.cocone_objs, h.cocone_maps⟩⟩

end CategoryTheory
