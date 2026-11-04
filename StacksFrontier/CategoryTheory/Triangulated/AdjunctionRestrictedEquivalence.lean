module

public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# An adjunction restricting to an equivalence of subcategories (the argument of Stacks 09J1)

Let `F : C ⥤ D` be left adjoint to `G : D ⥤ C`, with `C` and `D` pretriangulated, `G` triangulated
and the unit of the adjunction invertible. Let `P` and `Q` be properties of objects of `C` and `D`,
with `Q` a triangulated subcategory, such that `F` carries `P` into `Q`, `G` carries `Q` into `P`,
and `G` has zero kernel on `Q`. Then the counit is invertible on `Q`, and the adjunction restricts
to an equivalence between the full subcategories of `P` and of `Q`.

This is the argument of Stacks 09J1, run inside the subcategories: the cone `Z` of the counit
`F G Y ⟶ Y` lies in `Q` because `Q` is closed under cones, and `G Z = 0` because `G` carries the
counit to an isomorphism (triangle identity), so `Z = 0`.

## Main results

* `Stacks.Triangulated.isIso_counit_app_of_ker_eq_zero`: the counit is invertible on `Q`.
* `Stacks.Triangulated.restrictedEquivalence`: the equivalence of full subcategories, with
  functor the restriction of `F` and inverse the restriction of `G`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.Triangulated

variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  {F : C ⥤ D} {G : D ⥤ C} [G.CommShift ℤ] [G.IsTriangulated] (adj : F ⊣ G) [IsIso adj.unit]
  (P : ObjectProperty C) (Q : ObjectProperty D) [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms]

include adj in
/-- **The counit is invertible on `Q`.** If `F` carries `P` into `Q`, `G` carries `Q` into `P` and
`G` has zero kernel on `Q`, then for every `Y` in `Q` the counit `F G Y ⟶ Y` is an isomorphism. -/
theorem isIso_counit_app_of_ker_eq_zero (hFP : ∀ X, P X → Q (F.obj X))
    (hGQ : ∀ Y, Q Y → P (G.obj Y)) (hker : ∀ Y, Q Y → IsZero (G.obj Y) → IsZero Y)
    (Y : D) (hY : Q Y) : IsIso (adj.counit.app Y) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (adj.counit.app Y)
  have hZ : Q Z := Q.ext_of_isTriangulatedClosed₃ _ hT (hFP _ (hGQ _ hY)) hY
  have hGT := G.map_distinguished _ hT
  have h1 : IsIso (adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y)) := by
    rw [adj.right_triangle_components]; exact IsIso.id _
  have hGε : IsIso (G.map (adj.counit.app Y)) :=
    IsIso.of_isIso_comp_left (adj.unit.app (G.obj Y)) (G.map (adj.counit.app Y))
  have hGZ : IsZero (G.obj Z) := Triangle.isZero₃_of_isIso₁ _ hGT hGε
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hker Z hZ hGZ)

/-- **The adjunction restricts to an equivalence of the full subcategories of `P` and `Q`.** Its
functor is the restriction of `F` and its inverse the restriction of `G`; the unit and counit are
those of the adjunction. -/
def restrictedEquivalence (hFP : ∀ X, P X → Q (F.obj X))
    (hGQ : ∀ Y, Q Y → P (G.obj Y)) (hker : ∀ Y, Q Y → IsZero (G.obj Y) → IsZero Y) :
    P.FullSubcategory ≌ Q.FullSubcategory where
  functor := Q.lift (P.ι ⋙ F) fun X ↦ hFP _ X.property
  inverse := P.lift (Q.ι ⋙ G) fun Y ↦ hGQ _ Y.property
  unitIso := NatIso.ofComponents
    (fun X ↦ (ObjectProperty.fullyFaithfulι P).preimageIso (asIso (adj.unit.app X.obj)))
    (fun {X X'} g ↦ (ObjectProperty.fullyFaithfulι P).map_injective (by simp))
  counitIso := NatIso.ofComponents
    (fun Y ↦ (ObjectProperty.fullyFaithfulι Q).preimageIso
      (haveI := isIso_counit_app_of_ker_eq_zero adj P Q hFP hGQ hker Y.obj Y.property
       asIso (adj.counit.app Y.obj)))
    (fun {Y Y'} g ↦ (ObjectProperty.fullyFaithfulι Q).map_injective (by simp))
  functor_unitIso_comp X := (ObjectProperty.fullyFaithfulι Q).map_injective (by simp)

/-- The functor of `restrictedEquivalence` is the restriction of `F`. -/
theorem restrictedEquivalence_functor_obj_obj (hFP : ∀ X, P X → Q (F.obj X))
    (hGQ : ∀ Y, Q Y → P (G.obj Y)) (hker : ∀ Y, Q Y → IsZero (G.obj Y) → IsZero Y)
    (X : P.FullSubcategory) :
    ((restrictedEquivalence adj P Q hFP hGQ hker).functor.obj X).obj = F.obj X.obj :=
  rfl

/-- The inverse of `restrictedEquivalence` is the restriction of `G`. -/
theorem restrictedEquivalence_inverse_obj_obj (hFP : ∀ X, P X → Q (F.obj X))
    (hGQ : ∀ Y, Q Y → P (G.obj Y)) (hker : ∀ Y, Q Y → IsZero (G.obj Y) → IsZero Y)
    (Y : Q.FullSubcategory) :
    ((restrictedEquivalence adj P Q hFP hGQ hker).inverse.obj Y).obj = G.obj Y.obj :=
  rfl

end Stacks.Triangulated

end
