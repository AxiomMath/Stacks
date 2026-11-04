module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import StacksCore.CategoryTheory.Filtration.Preadditive
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Defs

/-!
# Filtered objects and finite filtered objects

Let `𝒜` be an abelian category. A filtered object of `𝒜` is an object of `𝒜` together with a
decreasing `ℤ`-indexed filtration by subobjects, and these objects form the category
`Fil(𝒜)`. The filtered objects whose filtration is finite — eventually the whole object going
down, eventually zero going up — form the full subcategory `Fil^f(𝒜)`. Both categories are
additive, and a finite filtered object is filtered injective when every graded piece of its
filtration is an injective object of `𝒜`.

## Main definitions

* `CategoryTheory.FilteredObject` bundles an object with a filtration; `Fil(𝒜)` is its
  specialization `CategoryTheory.FilteredObject 𝒜 ℤᵒᵖ`, where indexing by the opposite order
  makes the filtration decreasing.
* `CategoryTheory.FiniteFilteredObject` is the category `Fil^f(𝒜)`.
* `CategoryTheory.FilteredObject.IsFilteredInjective` records a finite filtration together
  with injectivity of every graded piece.

## Main results

* `CategoryTheory.FilteredObject.isFinite_zero` and
  `CategoryTheory.FilteredObject.isFinite_biprodObj`: the zero object has a finite filtration,
  and finiteness is preserved by direct sums.
* `CategoryTheory.FiniteFilteredObject.hasFiniteBiproducts`: `Fil^f(𝒜)` has all finite
  biproducts, which together with its preadditive structure says that it is additive.

## References

* [Stacks Project, Tag 03TA](https://stacks.math.columbia.edu/tag/03TA)
* [Stacks Project, Tag 05RY](https://stacks.math.columbia.edu/tag/05RY)
-/

add_to_stacks 03TA "filtered_objects" CategoryTheory.FilteredObject
add_to_stacks 03TA "filtered_objects" CategoryTheory.FilteredObject.instCategory
add_to_stacks 03TA "finite_filtered" CategoryTheory.FiniteFilteredObject
add_to_stacks 03TA "filtered_additive" CategoryTheory.FilteredObject.preadditive
add_to_stacks 03TA "filtered_additive" CategoryTheory.FilteredObject.hasFiniteBiproducts
add_to_stacks 03TA "filtered_injective" CategoryTheory.FilteredObject.IsFilteredInjective
add_to_stacks 03TA "finite_filtered_additive" CategoryTheory.Preadditive.fullSubcategory

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.FilteredObject

/-- The zero filtered object has a finite filtration. -/
lemma isFinite_zero (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C] :
    (FilteredObject.zero : FilteredObject C ℤᵒᵖ).filtration.IsFinite := by
  have h := (FilteredObject.isZero_iff _).1 (FilteredObject.isZero_zero (C := C) (I := ℤᵒᵖ))
  have h₀ := h.of_mono (FilteredObject.zero.filtration.ι.app (Opposite.op 0))
  exact .of_exists ⟨0, IsZero.isIso h₀ h _⟩ ⟨0, h₀⟩

/-- The direct sum of two filtered objects with finite filtrations has a finite filtration. -/
lemma isFinite_biprodObj (C : Type u) [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] {A B : FilteredObject C ℤᵒᵖ} (hA : A.filtration.IsFinite)
    (hB : B.filtration.IsFinite) : (FilteredObject.biprodObj A B).filtration.IsFinite := by
  obtain ⟨nA, hnA⟩ := hA.exists_isIso_ι
  obtain ⟨nB, hnB⟩ := hB.exists_isIso_ι
  obtain ⟨mA, hmA⟩ := hA.exists_isZero_obj
  obtain ⟨mB, hmB⟩ := hB.exists_isZero_obj
  let f := A.filtration.ι.app (Opposite.op (min nA nB))
  let g := B.filtration.ι.app (Opposite.op (min nA nB))
  let : IsIso f := A.filtration.isIso_ι_app_of_le (min_le_left nA nB) hnA
  let : IsIso g := B.filtration.isIso_ι_app_of_le (min_le_right nA nB) hnB
  refine .of_exists ⟨min nA nB, ?_⟩ ⟨max mA mB, ?_⟩
  · rw [FilteredObject.biprodObj_ι_app]
    show IsIso ((biprod.mapIso (asIso f) (asIso g)).hom)
    infer_instance
  · exact (biprod_isZero_iff _ _).2
      ⟨A.filtration.isZero_obj_of_le (le_max_left mA mB) hmA,
        B.filtration.isZero_obj_of_le (le_max_right mA mB) hmB⟩

end CategoryTheory.FilteredObject

namespace CategoryTheory.FiniteFilteredObject

/-- The category of finite filtered objects has finite biproducts. -/
@[stacks 03TA "finite_filtered_additive"]
noncomputable instance hasFiniteBiproducts (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] :
    HasFiniteBiproducts (FiniteFilteredObject C) := by
  let P : ObjectProperty (FilteredObject C ℤᵒᵖ) := fun F ↦ F.filtration.IsFinite
  let : P.IsClosedUnderIsomorphisms :=
    ⟨fun {X _} e (_ : X.filtration.IsFinite) ↦ FilteredObject.isFinite_of_iso e⟩
  let : P.ContainsZero :=
    ⟨FilteredObject.zero, FilteredObject.isZero_zero, FilteredObject.isFinite_zero C⟩
  let : P.IsClosedUnderBinaryProducts :=
    ⟨fun X ⟨L⟩ ↦ P.prop_of_iso (IsLimit.conePointsIsoOfNatIso L.isLimit
      (FilteredObject.biprodBiconeIsBilimit (L.diag.obj ⟨WalkingPair.left⟩)
        (L.diag.obj ⟨WalkingPair.right⟩)).isLimit (diagramIsoPair L.diag)).symm
      (FilteredObject.isFinite_biprodObj C (L.prop_diag_obj _) (L.prop_diag_obj _))⟩
  let : P.IsClosedUnderFiniteProducts := .mk'
  exact HasFiniteBiproducts.of_hasFiniteProducts

end CategoryTheory.FiniteFilteredObject

end
