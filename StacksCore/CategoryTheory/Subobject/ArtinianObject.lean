module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import StacksCore.CategoryTheory.Abelian.ShortExact
import StacksCore.Tactic.StacksAttribute

/-! ## Artinian Objects

Stacks tag 0FCH: for a short exact sequence `0 ⟶ A₁ ⟶ A₂ ⟶ A₃ ⟶ 0` in an abelian
category, `A₂` is Artinian if and only if `A₁` and `A₃` are Artinian.

The `⟹` direction splits into the subobject half (`isArtinianObject_of_mono`, already in
Mathlib) and the quotient half (`isArtinianObject_of_epi`, obtained here by duality from
`isNoetherianObject_of_mono`).

The `⟸` direction genuinely needs the short exact sequence rather than just a
monomorphism and an epimorphism. A descending chain of subobjects of `A₂` induces
descending chains of their intersections with `A₁` and of their images in `A₃`; both
stabilise, and beyond that point the short five lemma pins the original chain down. The
subobject bookkeeping is in `StacksCore.CategoryTheory.Abelian.ShortExact`.

Beware that `isArtinianObject_of_epi` really does need the category to be abelian: for a
general epimorphism `f : X ⟶ Y`, `Subobject Y` carries no information about `Subobject X`.
-/

add_to_stacks 0FCH "=>" CategoryTheory.instIsClosedUnderSubobjectsIsArtinianObject

@[expose] public section

variable {C : Type*} [Category* C] [CategoryTheory.Abelian C] {X Y : C} (f : X ⟶ Y)

namespace CategoryTheory

open Limits

lemma isArtinianObject_iff_isNoetherianObject_op (X : C) :
    IsArtinianObject X ↔ IsNoetherianObject (Opposite.op X) := by
  rw [isArtinianObject_iff_not_strictAnti, isNoetherianObject_iff_not_strictMono]
  refine ⟨fun h g hg ↦ h (fun n => (Abelian.subobjectIsoSubobjectOp X).symm
    (OrderDual.toDual (g n))) fun a b hab ↦ ?_, fun h g hg ↦ h (fun n => OrderDual.ofDual
    (Abelian.subobjectIsoSubobjectOp X (g n))) fun a b hab ↦ ?_⟩
  · exact (Abelian.subobjectIsoSubobjectOp X).symm.strictMono
      (OrderDual.toDual_lt_toDual.2 (hg hab))
  · exact OrderDual.toDual_lt_toDual.1 ((Abelian.subobjectIsoSubobjectOp X).strictMono (hg hab))

lemma isArtinianObject_of_epi [Epi f] [hX : IsArtinianObject X] :
    IsArtinianObject Y := by
  rw [isArtinianObject_iff_isNoetherianObject_op] at *
  exact isNoetherianObject_of_mono f.op

@[stacks 0FCH "=>"]
instance : CategoryTheory.isArtinianObject.IsClosedUnderQuotients (C := C) where
  prop_of_epi f _ hX := (CategoryTheory.isArtinianObject_of_epi f (hX := ⟨hX⟩)).1

/-- A simple object is Artinian: its subobject lattice is `{⊥, ⊤}`. -/
lemma isArtinianObject_of_simple (X : C) [Simple X] : IsArtinianObject X := by
  rw [isArtinianObject_iff_not_strictAnti]
  intro g hg
  rcases IsSimpleOrder.eq_bot_or_eq_top (g 1) with h | h
  · exact absurd (hg (show (1 : ℕ) < 2 by norm_num)) (by rw [h]; exact not_lt_bot)
  · exact absurd (hg (show (0 : ℕ) < 1 by norm_num)) (by rw [h]; exact not_top_lt)

lemma ShortComplex.ShortExact.isArtinianObject_X₂ {S : ShortComplex C} (hS : S.ShortExact)
    [IsArtinianObject S.X₁] [IsArtinianObject S.X₃] : IsArtinianObject S.X₂ := by
  rw [isArtinianObject_iff_antitone_chain_condition]
  intro F
  obtain ⟨n₁, hn₁⟩ := antitone_chain_condition_of_isArtinianObject
    (X := S.X₁) ⟨fun n => hS.interX₁ (F n), fun _ _ hab => hS.interX₁_le (F.monotone hab)⟩
  obtain ⟨n₃, hn₃⟩ := antitone_chain_condition_of_isArtinianObject
    (X := S.X₃) ⟨fun n => ShortComplex.ShortExact.imageInX₃ (F n),
      fun _ _ hab => ShortComplex.ShortExact.imageInX₃_le (F.monotone hab)⟩
  refine ⟨max n₁ n₃, fun m hm => ?_⟩
  refine (hS.eq_of_le_of_interX₁_eq_of_imageInX₃_eq (F.monotone hm) ?_ ?_).symm
  · exact (hn₁ _ ((le_max_left n₁ n₃).trans hm)).symm.trans (hn₁ _ (le_max_left n₁ n₃))
  · exact (hn₃ _ ((le_max_right n₁ n₃).trans hm)).symm.trans (hn₃ _ (le_max_right n₁ n₃))

@[stacks 0FCH "<="]
instance : CategoryTheory.isArtinianObject.IsClosedUnderExtensions (C := C) where
  prop_X₂_of_shortExact hS h₁ h₃ := by
    rw [← isArtinianObject.is_iff] at h₁ h₃ ⊢
    have := h₁
    have := h₃
    exact hS.isArtinianObject_X₂

instance : CategoryTheory.isArtinianObject.IsSerreClass (C := C) where

/-- **Stacks 0FCH**: for a short exact sequence `0 ⟶ A₁ ⟶ A₂ ⟶ A₃ ⟶ 0` in an abelian
category, `A₂` is Artinian if and only if `A₁` and `A₃` are Artinian. -/
@[stacks 0FCH]
lemma isArtinianObject_iff_of_shortExact {S : ShortComplex C} (hS : S.ShortExact) :
    IsArtinianObject S.X₂ ↔ IsArtinianObject S.X₁ ∧ IsArtinianObject S.X₃ := by
  simp only [ObjectProperty.is_iff]
  exact isArtinianObject.prop_iff_of_shortExact hS

end CategoryTheory
