module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Noetherian
import StacksCore.Tactic.StacksAttribute

/-!
# Artinian abelian categories

Stacks 0FCF has two parts. Part (1), an object of an abelian category is Artinian if it
satisfies the descending chain condition on subobjects, is mathlib's `IsArtinianObject`
(`WellFoundedLT (Subobject X)`), which carries the tag upstream. Part (2), an abelian category
is Artinian if every object is Artinian, is `CategoryTheory.IsArtinianCategory` below.

Mathlib's `CategoryTheory.Artinian` additionally asks the category to be essentially small,
so it is a strictly stronger notion; `CategoryTheory.artinian_iff_essentiallySmall_and` makes
the comparison precise.

## Main definitions

* `CategoryTheory.IsArtinianCategory`: Stacks 0FCF (2).
-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- An abelian category is *Artinian* if every object is Artinian, i.e. satisfies the
descending chain condition on subobjects. Unlike mathlib's `Artinian`, no smallness
condition is imposed. -/
@[stacks 0FCF "part (2): an abelian category is Artinian if every object is Artinian; part (1) is
mathlib's `IsArtinianObject`"]
class IsArtinianCategory [Abelian C] : Prop where
  isArtinianObject : ∀ X : C, IsArtinianObject X

attribute [instance] IsArtinianCategory.isArtinianObject

/-- Mathlib's `Artinian` is Stacks' Artinian abelian category together with essential
smallness. -/
lemma artinian_iff_essentiallySmall_and [Abelian C] :
    Artinian.{v, u, w} C ↔ EssentiallySmall.{w} C ∧ IsArtinianCategory C :=
  ⟨fun h => ⟨h.toEssentiallySmall, ⟨h.isArtinianObject⟩⟩,
    fun ⟨h₁, h₂⟩ => { toEssentiallySmall := h₁, isArtinianObject := h₂.isArtinianObject }⟩

end CategoryTheory
