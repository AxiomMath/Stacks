module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import StacksCore.CategoryTheory.Subobject.Basic

/-! ## The lattice of subobjects.

The section `Ported from mathlib#42759` at the end of this file is temporary; see its header.
-/

@[expose] public section

namespace CategoryTheory.Subobject

open Limits

variable {C : Type*} [Category* C]

/-- Pushing the top subobject of `B` forward along `B ↪ X` recovers `B`. -/
lemma map_arrow_top {X : C} (B : Subobject X) : (map B.arrow).obj ⊤ = B := by
  rw [map_top, mk_arrow]

/-- A subobject is `⊥` iff its underlying object is initial; mirrors `Subobject.isIso_iff_mk_eq_top`
and `Subobject.mk_eq_bot_iff_zero`. -/
theorem mk_eq_bot_iff_nonempty_isInitial [HasInitial C] [InitialMonoClass C]
    {A B : C} (f : A ⟶ B) [Mono f] : Subobject.mk f = ⊥ ↔ Nonempty (IsInitial A) := by
  rw [Subobject.bot_eq_initial_to]
  refine ⟨fun h => ⟨initialIsInitial.ofIso (Subobject.isoOfMkEqMk _ _ h).symm⟩, fun ⟨hA⟩ => ?_⟩
  exact Subobject.mk_eq_mk_of_comm _ _ (hA.uniqueUpToIso initialIsInitial) (hA.hom_ext _ _)

/-! ### Own lemmas: transport of subobjects along a monomorphism and along preimages

For a monomorphism `n : Y ⟶ A` and a subobject `X` of `Y`, `n(X)` is represented by
`X.arrow ≫ n` (`map_obj_eq_mk`), so its underlying object is that of `X` (`mapObjIso`,
compatible with the inclusions: `mapObjIso_hom_arrow`, `mapObjIso_inv_arrow`, and
`mapObjIso_hom_comp_arrow` for `n = B.arrow`, where `n(X) ≤ B`: `map_arrow_obj_le`); the
restrictions of a morphism `q` to preimages are compatible with the inclusions
(`ofLE_pullback_comp_pullbackπ`). Used for the towers of Stacks 011N
(`StacksCore.Algebra.Homology.SpectralSequence.Tower`). -/

section Map

variable {Y A : C} (n : Y ⟶ A) [Mono n]

/-- Pushing a subobject `X` of `Y` forward along a monomorphism `n : Y ⟶ A` gives the subobject
of `A` represented by `X.arrow ≫ n`. -/
lemma map_obj_eq_mk (X : Subobject Y) : (map n).obj X = mk (X.arrow ≫ n) :=
  (congrArg (map n).obj (mk_arrow X).symm).trans (map_mk X.arrow n)

/-- The underlying object of `n(X)` is that of `X`, for a monomorphism `n`. -/
noncomputable def mapObjIso (X : Subobject Y) : ((map n).obj X : C) ≅ (X : C) :=
  isoOfEq _ _ (map_obj_eq_mk n X) ≪≫ underlyingIso (X.arrow ≫ n)

/-- The identification `n(X) ≅ X` is compatible with the inclusions into `A`. -/
@[reassoc (attr := simp)]
lemma mapObjIso_hom_arrow (X : Subobject Y) :
    (mapObjIso n X).hom ≫ X.arrow ≫ n = ((map n).obj X).arrow := by
  simp [mapObjIso, underlyingIso_hom_comp_eq_mk]

/-- The identification `n(X) ≅ X` is compatible with the inclusions into `A`. -/
@[reassoc (attr := simp)]
lemma mapObjIso_inv_arrow (X : Subobject Y) :
    (mapObjIso n X).inv ≫ ((map n).obj X).arrow = X.arrow ≫ n := by
  rw [← mapObjIso_hom_arrow n X, Iso.inv_hom_id_assoc]

end Map

section MapArrow

variable {A : C} (B : Subobject A)

/-- A subobject of `B ⊆ A`, pushed forward into `A`, is contained in `B`. -/
lemma map_arrow_obj_le (X : Subobject (B : C)) : (map B.arrow).obj X ≤ B :=
  ((map B.arrow).monotone le_top).trans_eq (map_arrow_top B)

/-- For `X ⊆ B ⊆ A`, the identification `B.arrow(X) ≅ X` followed by `X ⊆ B` is the
inclusion `B.arrow(X) ⊆ B`. -/
@[reassoc (attr := simp)]
lemma mapObjIso_hom_comp_arrow (X : Subobject (B : C)) :
    (mapObjIso B.arrow X).hom ≫ X.arrow = ofLE _ B (map_arrow_obj_le B X) := by
  rw [← cancel_mono B.arrow, ofLE_arrow, Category.assoc, mapObjIso_hom_arrow]

end MapArrow

section Pullback

variable [HasPullbacks C] {Y E : C} (q : Y ⟶ E)

/-- The restrictions of `q` to the preimages of `X' ≤ Y'` are compatible with the inclusions. -/
@[reassoc]
lemma ofLE_pullback_comp_pullbackπ {X' Y' : Subobject E} (h : X' ≤ Y') :
    ofLE _ _ ((pullback q).monotone.imp h) ≫ pullbackπ q Y' = pullbackπ q X' ≫ ofLE X' Y' h := by
  rw [← cancel_mono Y'.arrow, Category.assoc, (isPullback q Y').w, ofLE_arrow_assoc,
    Category.assoc, ofLE_arrow, (isPullback q X').w]

end Pullback

/-! ### Ported from mathlib#42759

**Everything in this section is temporary and is expected to be deleted.** It is the
`Lattice` part of mathlib#42759 (mckoen, `feat(CategoryTheory/Subobject): extend image
subobject API`, merged 2026-09-25, after our pinned revision of 2026-09-01), ported with the
upstream name and statement. The proof is by antisymmetry rather than upstream's `change` into
`MonoOver`, so that it does not rely on unfolding `MonoOver.mk`. Delete the section once the pin
includes that pull request. -/

section Port42759

theorem exists_pullback_eq_inf_of_mono {X Y : C} [HasPullbacks C] [HasImages C] (f : X ⟶ Y)
    [Mono f] (Y' : Subobject Y) :
    («exists» f).obj ((pullback f).obj Y') = Y' ⊓ mk f := by
  apply le_antisymm
  · refine _root_.le_inf (exists_pullback_le f Y') ?_
    rw [exists_eq_mk_of_mono]
    exact mk_le_mk_of_comm _ rfl
  · have hZ : Y' ⊓ mk f ≤ mk f := _root_.inf_le_right
    rw [exists_eq_mk_of_mono]
    refine le_mk_of_comm
      ((isPullback f Y').lift (ofLE _ _ _root_.inf_le_left) (ofLEMk _ f hZ) ?_) ?_
    · rw [ofLE_arrow, ofLEMk_comp]
    · rw [← Category.assoc, IsPullback.lift_snd, ofLEMk_comp]

end Port42759

end CategoryTheory.Subobject
