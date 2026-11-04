module

public import Mathlib.CategoryTheory.Category.GaloisConnection
public import Mathlib.CategoryTheory.Subobject.Basic
public import StacksCore.CategoryTheory.Subobject.MonoOver
import StacksCore.Tactic.StacksAttribute

/-! ## Subobjects.

The section `Ported from mathlib#42757` at the end of this file is temporary; see its header.
-/

@[expose] public section

namespace CategoryTheory.Subobject

open Limits

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

/-- If two monomorphisms into `B` define the same subobject, then any morphism relating
them is an isomorphism. This is the contrapositive of `Subobject.mk_lt_mk_iff_of_comm`. -/
lemma isIso_of_mk_eq_mk {B A₁ A₂ : C} {i₁ : A₁ ⟶ B} {i₂ : A₂ ⟶ B} [Mono i₁] [Mono i₂]
    (f : A₁ ⟶ A₂) (fac : f ≫ i₂ = i₁) (h : mk i₁ = mk i₂) : IsIso f :=
  not_not.mp ((mk_lt_mk_iff_of_comm f fac).not.mp (by rw [h]; exact lt_irrefl _))

/-- An equivalence of categories induces an order isomorphism of subobject lattices. -/
noncomputable def orderIsoCongr (e : C ≌ D) (X : C) :
    Subobject X ≃o Subobject (e.functor.obj X) :=
  (lowerEquivalence (MonoOver.congr X e)).toOrderIso

/-- Pushing `A`, viewed as a subobject of `B`, forward along `B ↪ X` recovers `A`. -/
lemma map_arrow_mk_ofLE {X : C} {A B : Subobject X} (h : A ≤ B) :
    (map B.arrow).obj (mk (ofLE A B h)) = A := by
  rw [map_mk]
  exact (mk_eq_mk_of_comm _ A.arrow (Iso.refl _) (by simp)).trans (mk_arrow A)

/-- The adjunction `exists f ⊣ pullback f` between subobject lattices, in `≤` form:
`f(X') ⊆ Y'` if and only if `X' ⊆ f⁻¹(Y')`. -/
lemma exists_le_iff_le_pullback [HasImages C] [HasPullbacks C] {X Y : C} (f : X ⟶ Y)
    (X' : Subobject X) (Y' : Subobject Y) :
    («exists» f).obj X' ≤ Y' ↔ X' ≤ (pullback f).obj Y' :=
  (existsPullbackAdj f).gc.le_iff_le

/-! ### Ported from mathlib#42757

**Everything in this section is temporary and is expected to be deleted.** It is the
`Subobject` half of mathlib#42757 (`feat(CategoryTheory/Subobject): extend exists and pullback
API`, merged 2026-09-07, after our pinned revision of 2026-09-01), ported with the upstream
names, statements and proofs. Delete the whole section once the pin moves past that commit;
every name then resolves to the mathlib declaration. -/

section Port42757

variable {X Y Z : C}

lemma le_pullback_of_comm [HasPullbacks C] (f : X ⟶ Y) {X' : Subobject X} {Y' : Subobject Y}
    (u : (X' : C) ⟶ Y') (h : u ≫ Y'.arrow = X'.arrow ≫ f) : X' ≤ (pullback f).obj Y' :=
  le_of_comm ((isPullback f Y').lift u X'.arrow h) ((isPullback f Y').lift_snd u X'.arrow h)

variable [HasImages C]

lemma exists_eq_mk_of_mono (f : X ⟶ Y) [Mono f] (X' : Subobject X) :
    («exists» f).obj X' = mk (X'.arrow ≫ f) := by
  conv_lhs => rw [exists_iso_map, ← mk_arrow X']
  rw [map_mk]

theorem exists_le_exists_iff_of_mono (f : X ⟶ Y) [Mono f] (X₁ X₂ : Subobject X) :
    («exists» f).obj X₁ ≤ («exists» f).obj X₂ ↔ X₁ ≤ X₂ :=
  Quotient.inductionOn₂' X₁ X₂ fun _ _ ↦
    ⟨fun ⟨h⟩ ↦ ⟨(MonoOver.exists f).preimage h⟩, fun ⟨h⟩ ↦ ⟨(MonoOver.exists f).map h⟩⟩

theorem le_pullback_exists (f : X ⟶ Y) [HasPullbacks C] (X' : Subobject X) :
    X' ≤ (pullback f).obj ((«exists» f).obj X') :=
  (existsPullbackAdj f).gc.le_u_l X'

theorem exists_pullback_le (f : X ⟶ Y) [HasPullbacks C] (Y' : Subobject Y) :
    («exists» f).obj ((pullback f).obj Y') ≤ Y' :=
  (existsPullbackAdj f).gc.l_u_le Y'

@[simp]
theorem pullback_exists_eq_self_of_mono (f : X ⟶ Y) [Mono f] [HasPullbacks C]
    (X' : Subobject X) : (pullback f).obj ((«exists» f).obj X') = X' := by
  rw [exists_iso_map, pullback_map_self]

theorem exists_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : Subobject X) [HasPullbacks C] :
    («exists» (f ≫ g)).obj x = («exists» g).obj ((«exists» f).obj x) :=
  Quotient.inductionOn' x fun _ ↦ Quotient.sound ⟨(MonoOver.existsComp f g).app _⟩

lemma exists_le_of_comm (f : X ⟶ Y) {X' : Subobject X} {Y' : Subobject Y}
    (u : (X' : C) ⟶ Y') (h : u ≫ Y'.arrow = X'.arrow ≫ f) : («exists» f).obj X' ≤ Y' :=
  le_of_comm ((imageFactorisation f X').isImage.lift ⟨Y', Y'.arrow, u, h⟩)
    ((imageFactorisation f X').isImage.lift_fac _)

end Port42757

end CategoryTheory.Subobject
