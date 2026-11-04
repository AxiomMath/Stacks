module

public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# An adjunction whose counit is invertible on a subcategory restricts to an equivalence

Let `F : C ⥤ D` be left adjoint to `G : D ⥤ C`, with `C` and `D` pretriangulated and `F`
triangulated. Let `P` and `Q` be properties of objects of `C` and `D`, and `P'` a triangulated
subcategory of `C` containing `P`, such that `F` carries `P` into `Q`, `G` carries `Q` into `P`,
the counit `F G Y ⟶ Y` is invertible for `Y` in `Q`, and `F` has zero kernel on `P'`. Then the
unit `X ⟶ G F X` is invertible on `P`, and the adjunction restricts to an equivalence between the
full subcategories of `P` and of `Q`.

This is the argument of Stacks 09J1 run with the roles of the unit and the counit exchanged and
inside the subcategories, with no global hypothesis on the adjunction: the cone `Z` of the unit
lies in `P'` because `P'` is closed under cones and contains `X` and `G F X`, and `F Z = 0`
because `F` carries the unit to an isomorphism (triangle identity), so `Z = 0`. It is the shape
of Stacks 0AFJ, where `F = Lf^*`, `G = Rf_*`, `P` and `Q` are the quasi-coherent objects supported
on `|Z|` and on `|f⁻¹Z|`, the counit is invertible on `Q` by Stacks 0AEU, and `P'` is the
triangulated subcategory of all objects supported on `|Z|`, on which the kernel of `Lf^*` is zero.
Taking `P' = P` recovers the case of a triangulated `P`.
`Stacks.Triangulated.restrictedEquivalence` is the version with the unit invertible globally and
the counit invertible on `Q`.

## Main results

* `Stacks.Triangulated.isIso_unit_app_of_ker_eq_zero`: the unit is invertible on `P`.
* `Stacks.Triangulated.restrictedEquivalenceOfIsIsoCounit`: the equivalence of full
  subcategories, with functor the restriction of `F` and inverse the restriction of `G`.

## References

* [Stacks Project, Tag 09J1](https://stacks.math.columbia.edu/tag/09J1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.Triangulated

variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  {F : C ⥤ D} {G : D ⥤ C} [F.CommShift ℤ] [F.IsTriangulated] (adj : F ⊣ G)
  (P : ObjectProperty C) (Q : ObjectProperty D) (P' : ObjectProperty C) [P'.IsTriangulated]
  [P'.IsClosedUnderIsomorphisms]

include adj in
/-- **The unit is invertible on `P`.** If `F` carries `P` into `Q`, `G` carries `Q` into `P`, the
counit is invertible on `Q` and `F` has zero kernel on a triangulated subcategory `P'` containing
`P`, then for every `X` in `P` the unit `X ⟶ G F X` is an isomorphism. -/
theorem isIso_unit_app_of_ker_eq_zero (hPP' : ∀ X, P X → P' X) (hFP : ∀ X, P X → Q (F.obj X))
    (hGQ : ∀ Y, Q Y → P (G.obj Y)) (hcounit : ∀ Y, Q Y → IsIso (adj.counit.app Y))
    (hker : ∀ X, P' X → IsZero (F.obj X) → IsZero X) (X : C) (hX : P X) :
    IsIso (adj.unit.app X) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (adj.unit.app X)
  have hZ : P' Z :=
    P'.ext_of_isTriangulatedClosed₃ _ hT (hPP' _ hX) (hPP' _ (hGQ _ (hFP _ hX)))
  have hFT := F.map_distinguished _ hT
  have : IsIso (adj.counit.app (F.obj X)) := hcounit _ (hFP _ hX)
  have h1 : IsIso (F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X)) := by
    have e : F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X) = 𝟙 _ :=
      adj.left_triangle_components X
    rw [e]
    infer_instance
  have hFη : IsIso (F.map (adj.unit.app X)) :=
    IsIso.of_isIso_comp_right (F.map (adj.unit.app X)) (adj.counit.app (F.obj X))
  have hFZ : IsZero (F.obj Z) := Triangle.isZero₃_of_isIso₁ _ hFT hFη
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hker Z hZ hFZ)

/-- **The adjunction restricts to an equivalence of the full subcategories of `P` and `Q`**, in the
situation of `isIso_unit_app_of_ker_eq_zero`. Its functor is the restriction of `F` and its inverse
the restriction of `G`; the unit and counit are those of the adjunction. -/
def restrictedEquivalenceOfIsIsoCounit (hPP' : ∀ X, P X → P' X) (hFP : ∀ X, P X → Q (F.obj X))
    (hGQ : ∀ Y, Q Y → P (G.obj Y)) (hcounit : ∀ Y, Q Y → IsIso (adj.counit.app Y))
    (hker : ∀ X, P' X → IsZero (F.obj X) → IsZero X) :
    P.FullSubcategory ≌ Q.FullSubcategory where
  functor := Q.lift (P.ι ⋙ F) fun X ↦ hFP _ X.property
  inverse := P.lift (Q.ι ⋙ G) fun Y ↦ hGQ _ Y.property
  unitIso := NatIso.ofComponents
    (fun X ↦ (ObjectProperty.fullyFaithfulι P).preimageIso
      (haveI := isIso_unit_app_of_ker_eq_zero adj P Q P' hPP' hFP hGQ hcounit hker X.obj
         X.property
       asIso (adj.unit.app X.obj)))
    (fun {X X'} g ↦ (ObjectProperty.fullyFaithfulι P).map_injective (by simp))
  counitIso := NatIso.ofComponents
    (fun Y ↦ (ObjectProperty.fullyFaithfulι Q).preimageIso
      (haveI := hcounit Y.obj Y.property
       asIso (adj.counit.app Y.obj)))
    (fun {Y Y'} g ↦ (ObjectProperty.fullyFaithfulι Q).map_injective (by simp))
  functor_unitIso_comp X := (ObjectProperty.fullyFaithfulι Q).map_injective (by simp)

/-- The functor of `restrictedEquivalenceOfIsIsoCounit` is the restriction of `F`. -/
theorem restrictedEquivalenceOfIsIsoCounit_functor_obj_obj (hPP' : ∀ X, P X → P' X)
    (hFP : ∀ X, P X → Q (F.obj X))
    (hGQ : ∀ Y, Q Y → P (G.obj Y)) (hcounit : ∀ Y, Q Y → IsIso (adj.counit.app Y))
    (hker : ∀ X, P' X → IsZero (F.obj X) → IsZero X) (X : P.FullSubcategory) :
    ((restrictedEquivalenceOfIsIsoCounit adj P Q P' hPP' hFP hGQ hcounit hker).functor.obj
      X).obj =
      F.obj X.obj :=
  rfl

/-- The inverse of `restrictedEquivalenceOfIsIsoCounit` is the restriction of `G`. -/
theorem restrictedEquivalenceOfIsIsoCounit_inverse_obj_obj (hPP' : ∀ X, P X → P' X)
    (hFP : ∀ X, P X → Q (F.obj X))
    (hGQ : ∀ Y, Q Y → P (G.obj Y)) (hcounit : ∀ Y, Q Y → IsIso (adj.counit.app Y))
    (hker : ∀ X, P' X → IsZero (F.obj X) → IsZero X) (Y : Q.FullSubcategory) :
    ((restrictedEquivalenceOfIsIsoCounit adj P Q P' hPP' hFP hGQ hcounit hker).inverse.obj
      Y).obj =
      G.obj Y.obj :=
  rfl


end Stacks.Triangulated

end
