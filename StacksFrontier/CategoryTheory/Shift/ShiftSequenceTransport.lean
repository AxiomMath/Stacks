module

public import Mathlib.CategoryTheory.Shift.ShiftSequence
public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Transporting an identification of a homological functor along the shifts

Let `R : C ⥤ D` commute with the shifts, let `F : D ⥤ A` carry a shift sequence (as a homological
functor on a triangulated category does, `F.shift n` being its degree-`n` version), and let
`Φ₀ : R ⋙ F.shift 0 ⋙ G ≅ Y` for functors `G : A ⥤ E` and `Y : C ⥤ E`.  Then
`R ⋙ F.shift n ⋙ G ≅ shiftFunctor C n ⋙ Y` for every `n`
(`Stacks.CategoryTheory.ShiftSequenceTransport.shiftedIso`), and these isomorphisms carry the
connecting morphisms of `F` at the image under `R` of a triangle to composition with the shifted
third morphism of the triangle (`Stacks.CategoryTheory.ShiftSequenceTransport.shiftedIso_delta`).

This is used with `R = RΓ(X, -)`, `F = H^0` and `Y = Hom(𝒪_X[0], -)`: it identifies the boundary
maps of cohomology with composition by the third morphism of a distinguished triangle.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.ShiftSequenceTransport

variable {C D A E : Type*} [Category C] [Category D] [Category A] [Category E]
  [HasShift C ℤ] [HasShift D ℤ] (R : C ⥤ D) [R.CommShift ℤ] (F : D ⥤ A) [F.ShiftSequence ℤ]
  (G : A ⥤ E) (Y : C ⥤ E) (Φ₀ : R ⋙ F.shift (0 : ℤ) ⋙ G ≅ Y)

/-- The naturality of the inverse of `F.shiftIso`. -/
@[reassoc]
theorem shiftIso_inv_app_naturality {X X' : D} (n a a' : ℤ) (ha : n + a = a') (g : X ⟶ X') :
    (F.shift a').map g ≫ (F.shiftIso n a a' ha).inv.app X' =
      (F.shiftIso n a a' ha).inv.app X ≫ (F.shift a).map (g⟦n⟧') := by
  rw [← cancel_mono ((F.shiftIso n a a' ha).hom.app X'), Category.assoc, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, F.shiftIso_hom_naturality, Iso.inv_hom_id_app_assoc]

/-- The inverse of `F.shiftIso n₁ 0 n₁` through `n₁ = 1 + n₀`. -/
theorem shiftIso_inv_app_add (n₀ n₁ : ℤ) (h : 1 + n₀ = n₁) (Z : D) :
    (F.shiftIso n₁ 0 n₁ (add_zero n₁)).inv.app Z =
      (F.shiftIso 1 n₀ n₁ h).inv.app Z ≫ (F.shiftIso n₀ 0 n₀ (add_zero n₀)).inv.app (Z⟦(1 : ℤ)⟧) ≫
        (F.shift (0 : ℤ)).map ((shiftFunctorAdd' D 1 n₀ n₁ h).inv.app Z) := by
  rw [← cancel_epi ((F.shiftIso n₁ 0 n₁ (add_zero n₁)).hom.app Z), Iso.hom_inv_id_app,
    F.shiftIso_add'_hom_app n₀ 1 n₁ h 0 n₀ n₁ (add_zero n₀) h]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  simp [← Functor.map_comp]

/-- The commutation of `R` with the shifts by `1`, `n₀` and `1 + n₀`, at an object. -/
theorem commShiftIso_inv_app_add_one {X₁ : C} (n₀ n₁ : ℤ) (h : 1 + n₀ = n₁) :
    ((R.commShiftIso (1 : ℤ)).hom.app X₁)⟦n₀⟧' ≫ (shiftFunctorAdd' D 1 n₀ n₁ h).inv.app (R.obj X₁) ≫
        (R.commShiftIso n₁).inv.app X₁ =
      (R.commShiftIso n₀).inv.app (X₁⟦(1 : ℤ)⟧) ≫
        R.map ((shiftFunctorAdd' C 1 n₀ n₁ h).inv.app X₁) := by
  rw [R.commShiftIso_add' h, Functor.CommShift.isoAdd'_inv_app]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  simp

/-- **The transport of `Φ₀ : R ⋙ F.shift 0 ⋙ G ≅ Y` to every degree**: `R ⋙ F.shift n ⋙ G ≅
shiftFunctor C n ⋙ Y`, through `F.shiftIso n 0 n` and the commutation of `R` with the shift. -/
noncomputable def shiftedIso (n : ℤ) : R ⋙ F.shift n ⋙ G ≅ shiftFunctor C n ⋙ Y :=
  NatIso.ofComponents (fun X => G.mapIso ((F.shiftIso n 0 n (add_zero n)).symm.app (R.obj X)) ≪≫
      G.mapIso ((F.shift (0 : ℤ)).mapIso ((R.commShiftIso n).symm.app X)) ≪≫ Φ₀.app (X⟦n⟧)) (by
    intro X X' f
    simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Iso.symm_hom, Category.assoc]
    rw [← Φ₀.hom.naturality]
    simp only [Functor.comp_map, ← G.map_comp_assoc]
    congr 2
    rw [← Category.assoc, shiftIso_inv_app_naturality, Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, Functor.commShiftIso_inv_naturality])

/-- The components of `shiftedIso`. -/
theorem shiftedIso_hom_app (n : ℤ) (X : C) : (shiftedIso R F G Y Φ₀ n).hom.app X =
    G.map ((F.shiftIso n 0 n (add_zero n)).inv.app (R.obj X)) ≫
      G.map ((F.shift (0 : ℤ)).map ((R.commShiftIso n).inv.app X)) ≫ Φ₀.hom.app (X⟦n⟧) := rfl

/-- **`shiftedIso` carries the connecting morphism to composition with the shifted map.**  For
`h : X₃ ⟶ X₁⟦1⟧` in `C`, the morphism `(F.shift n₀)(R h ≫ (R.commShiftIso 1)) ≫ F.shiftIso 1 n₀ n₁`
(the connecting morphism of the homological functor `F` at the image under `R` of a triangle with
third morphism `h`) corresponds under `shiftedIso` to `Y` of `h⟦n₀⟧ ≫ (X₁⟦1⟧⟦n₀⟧ ≅ X₁⟦n₁⟧)`. -/
theorem shiftedIso_delta {X₁ X₃ : C} (h : X₃ ⟶ X₁⟦(1 : ℤ)⟧) (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) :
    G.map ((F.shift n₀).map (R.map h ≫ (R.commShiftIso (1 : ℤ)).hom.app X₁) ≫
        (F.shiftIso 1 n₀ n₁ (by omega)).hom.app (R.obj X₁)) ≫
      (shiftedIso R F G Y Φ₀ n₁).hom.app X₁ =
      (shiftedIso R F G Y Φ₀ n₀).hom.app X₃ ≫
        Y.map (h⟦n₀⟧' ≫ (shiftFunctorAdd' C 1 n₀ n₁ (by omega)).inv.app X₁) := by
  have h1 : 1 + n₀ = n₁ := by omega
  simp only [shiftedIso_hom_app, Category.assoc]
  rw [← Φ₀.hom.naturality]
  simp only [Functor.comp_map, ← G.map_comp_assoc]
  congr 2
  rw [shiftIso_inv_app_add F n₀ n₁ h1]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  have key := shiftIso_inv_app_naturality F n₀ 0 n₀ (add_zero n₀)
    (R.map h ≫ (R.commShiftIso (1 : ℤ)).hom.app X₁)
  dsimp only [Functor.comp_obj] at key ⊢
  simp only [Functor.map_comp, Category.assoc] at key
  rw [reassoc_of% key]
  simp only [← Functor.map_comp]
  congr 2
  rw [commShiftIso_inv_app_add_one R n₀ n₁ h1, ← Category.assoc,
    Functor.commShiftIso_inv_naturality, Category.assoc, Functor.map_comp]

end Stacks.CategoryTheory.ShiftSequenceTransport

end
