module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Noetherian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Noetherian abelian categories

Stacks tag 0FCG, part (2): an abelian category is Noetherian if every object of it is Noetherian,
that is, satisfies the ascending chain condition on subobjects (part (1), which is Mathlib's
`CategoryTheory.IsNoetherianObject`).

Mathlib's `CategoryTheory.Noetherian` additionally requires the category to be essentially small,
which Stacks does not; the two notions agree on essentially small categories
(`isNoetherianAbelianCategory_iff_noetherian`).

## Main definitions

* `CategoryTheory.IsNoetherianAbelianCategory`: every object of the abelian category is
  Noetherian.
-/

@[expose] public section

namespace CategoryTheory

universe w v u

variable (C : Type u) [Category.{v} C]

/-- An abelian category is Noetherian if every object of it is Noetherian, i.e. satisfies the
ascending chain condition on subobjects. Unlike Mathlib's `CategoryTheory.Noetherian`, no
smallness of the category is required. -/
@[stacks 0FCG "(2): an abelian category is Noetherian if every object is Noetherian."]
class IsNoetherianAbelianCategory [Abelian C] : Prop where
  isNoetherianObject : ∀ X : C, IsNoetherianObject X

attribute [instance] IsNoetherianAbelianCategory.isNoetherianObject

variable [Abelian C]

/-- A Noetherian category in Mathlib's sense (essentially small, every object Noetherian) is a
Noetherian abelian category. -/
instance (priority := 100) isNoetherianAbelianCategory_of_noetherian [Noetherian.{v, u, w} C] :
    IsNoetherianAbelianCategory C :=
  ⟨Noetherian.isNoetherianObject⟩

/-- For an essentially small abelian category, being Noetherian in the sense of Stacks agrees
with Mathlib's `CategoryTheory.Noetherian`. -/
lemma isNoetherianAbelianCategory_iff_noetherian [EssentiallySmall.{w} C] :
    IsNoetherianAbelianCategory C ↔ Noetherian.{v, u, w} C :=
  ⟨fun h ↦ { toEssentiallySmall := ‹_›, isNoetherianObject := h.isNoetherianObject },
    fun _ ↦ inferInstance⟩

end CategoryTheory
