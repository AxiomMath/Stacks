module

public import StacksCore.CategoryTheory.Subobject.ArtinianObject
import StacksCore.Tactic.StacksAttribute

/-! ## Noetherian Objects

Stacks tag 0FCI: for a short exact sequence `0 ⟶ A₁ ⟶ A₂ ⟶ A₃ ⟶ 0` in an abelian
category, `A₂` is Noetherian if and only if `A₁` and `A₃` are Noetherian.

This is the exact dual of tag 0FCH, and is deduced from it in `Cᵒᵖ`: taking kernels and
cokernels identifies `Subobject X` with the order dual of `Subobject (op X)`, so `X` is
Noetherian exactly when `op X` is Artinian, and `S.op` is short exact whenever `S` is,
with `S.op.X₁ = op S.X₃` and `S.op.X₃ = op S.X₁`.
-/

add_to_stacks 0FCI "=>" CategoryTheory.instIsClosedUnderSubobjectsIsNoetherianObject

@[expose] public section

variable {C : Type*} [Category* C] [CategoryTheory.Abelian C] {X Y : C} (f : X ⟶ Y)

namespace CategoryTheory

omit [Abelian C] in
/-- `IsNoetherianObject` is invariant under equivalences of categories. -/
lemma isNoetherianObject_congr {D : Type*} [Category* D] (e : C ≌ D) (X : C) :
    IsNoetherianObject X ↔ IsNoetherianObject (e.functor.obj X) := by
  rw [isNoetherianObject_iff_not_strictMono, isNoetherianObject_iff_not_strictMono]
  exact ⟨fun h g hg ↦ h _ ((Subobject.orderIsoCongr e X).symm.strictMono.comp hg),
    fun h g hg ↦ h _ ((Subobject.orderIsoCongr e X).strictMono.comp hg)⟩

lemma isNoetherianObject_iff_isArtinianObject_op (X : C) :
    IsNoetherianObject X ↔ IsArtinianObject (Opposite.op X) := by
  rw [isArtinianObject_iff_isNoetherianObject_op (Opposite.op X)]
  exact isNoetherianObject_congr (opOpEquivalence C).symm X

lemma isNoetherianObject_of_epi [Epi f] [hX : IsNoetherianObject X] :
    IsNoetherianObject Y := by
  rw [isNoetherianObject_iff_isArtinianObject_op] at *
  exact isArtinianObject_of_mono f.op

@[stacks 0FCI "=>"]
instance : CategoryTheory.isNoetherianObject.IsClosedUnderQuotients (C := C) where
  prop_of_epi f _ hX := (CategoryTheory.isNoetherianObject_of_epi f (hX := ⟨hX⟩)).1

/-- A simple object is Noetherian: its subobject lattice is `{⊥, ⊤}`. -/
lemma isNoetherianObject_of_simple (X : C) [Simple X] : IsNoetherianObject X := by
  rw [isNoetherianObject_iff_not_strictMono]
  intro g hg
  rcases IsSimpleOrder.eq_bot_or_eq_top (g 1) with h | h
  · exact absurd (hg (show (0 : ℕ) < 1 by norm_num)) (by rw [h]; exact not_lt_bot)
  · exact absurd (hg (show (1 : ℕ) < 2 by norm_num)) (by rw [h]; exact not_top_lt)

lemma ShortComplex.ShortExact.isNoetherianObject_X₂ {S : ShortComplex C} (hS : S.ShortExact)
    [IsNoetherianObject S.X₁] [IsNoetherianObject S.X₃] : IsNoetherianObject S.X₂ := by
  have : IsArtinianObject S.op.X₁ := (isNoetherianObject_iff_isArtinianObject_op S.X₃).1 ‹_›
  have : IsArtinianObject S.op.X₃ := (isNoetherianObject_iff_isArtinianObject_op S.X₁).1 ‹_›
  exact (isNoetherianObject_iff_isArtinianObject_op S.X₂).2 hS.op.isArtinianObject_X₂

@[stacks 0FCI "<="]
instance : CategoryTheory.isNoetherianObject.IsClosedUnderExtensions (C := C) where
  prop_X₂_of_shortExact hS h₁ h₃ := by
    rw [← isNoetherianObject.is_iff] at h₁ h₃ ⊢
    have := h₁
    have := h₃
    exact hS.isNoetherianObject_X₂

instance : CategoryTheory.isNoetherianObject.IsSerreClass (C := C) where

/-- **Stacks 0FCI**: for a short exact sequence `0 ⟶ A₁ ⟶ A₂ ⟶ A₃ ⟶ 0` in an abelian
category, `A₂` is Noetherian if and only if `A₁` and `A₃` are Noetherian. -/
@[stacks 0FCI]
lemma isNoetherianObject_iff_of_shortExact {S : ShortComplex C} (hS : S.ShortExact) :
    IsNoetherianObject S.X₂ ↔ IsNoetherianObject S.X₁ ∧ IsNoetherianObject S.X₃ := by
  simp only [ObjectProperty.is_iff]
  exact isNoetherianObject.prop_iff_of_shortExact hS

end CategoryTheory
