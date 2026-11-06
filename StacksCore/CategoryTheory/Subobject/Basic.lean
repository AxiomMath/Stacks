module

public import Mathlib.CategoryTheory.Category.GaloisConnection
public import Mathlib.CategoryTheory.Subobject.Basic
public import StacksCore.CategoryTheory.Subobject.MonoOver
import StacksCore.Tactic.StacksAttribute

/-! ## Subobjects. -/

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

end CategoryTheory.Subobject
