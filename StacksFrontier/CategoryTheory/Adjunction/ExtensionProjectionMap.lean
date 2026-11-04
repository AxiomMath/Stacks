module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# The projection map of a left adjoint along a monoidal right adjoint

Let `E ⊣ R` be an adjunction, `E : D ⥤ C`, and let `TC`, `TD` be bifunctors on `C` and `D` with
a comparison `c : R(A ⊗ B) ≅ RA ⊗ RB`. Then there is a canonical map

`E(R L ⊗ Z) ⟶ L ⊗ E Z`,

natural in `L` and `Z`: the adjoint transpose of `R L ⊗ Z ⟶ R L ⊗ R E Z ≅ R(L ⊗ E Z)`, the unit
in the second factor followed by `c⁻¹`. When `E` is extension by zero along an open immersion
and `R` the restriction, this is the map of the projection formula [Stacks, Tag 0GL1] (with the
extension by zero in the second tensor factor), and the projection formula is the assertion that
it is an isomorphism. When the unit of `E ⊣ R` is an isomorphism, `R` sends the map to an
isomorphism, with no further hypothesis.

## Main definitions

* `CategoryTheory.extensionProjectionMapApp`: the map at a pair of objects.
* `CategoryTheory.extensionProjectionMap`: the map as a natural transformation of bifunctors.

## Main results

* `CategoryTheory.homEquiv_extensionProjectionMapApp`: its defining property.
* `CategoryTheory.isIso_map_extensionProjectionMapApp`: when the unit is an isomorphism, `R`
  carries it to an isomorphism.
-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] {E : D ⥤ C} {R : C ⥤ D} (adj : E ⊣ R)
  (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
  (c : Functor.uncurry.obj TC ⋙ R ≅ R.prod R ⋙ Functor.uncurry.obj TD)

/-- **The projection map** `E(R L ⊗ Z) ⟶ L ⊗ E Z` of a left adjoint `E` along a right adjoint `R`
compatible with tensor products: the adjoint transpose of the unit in the second factor followed
by the inverse of the comparison. -/
noncomputable def extensionProjectionMapApp (L : C) (Z : D) :
    E.obj ((TD.obj (R.obj L)).obj Z) ⟶ (TC.obj L).obj (E.obj Z) :=
  (adj.homEquiv _ _).symm ((TD.obj (R.obj L)).map (adj.unit.app Z) ≫ (c.app (L, E.obj Z)).inv)

/-- **The defining property of the projection map**: its adjoint transpose is the unit in the
second factor followed by the inverse of the comparison. -/
theorem homEquiv_extensionProjectionMapApp (L : C) (Z : D) :
    adj.homEquiv _ _ (extensionProjectionMapApp adj TC TD c L Z) =
      (TD.obj (R.obj L)).map (adj.unit.app Z) ≫ (c.app (L, E.obj Z)).inv :=
  Equiv.apply_symm_apply _ _

/-- The projection map `E(R L ⊗ Z) ⟶ L ⊗ E Z` is natural in `Z`. -/
theorem extensionProjectionMapApp_naturality_right (L : C) {Z Z' : D} (z : Z ⟶ Z') :
    E.map ((TD.obj (R.obj L)).map z) ≫ extensionProjectionMapApp adj TC TD c L Z' =
      extensionProjectionMapApp adj TC TD c L Z ≫ (TC.obj L).map (E.map z) := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
    homEquiv_extensionProjectionMapApp, homEquiv_extensionProjectionMapApp]
  have hc := c.inv.naturality ((𝟙 L, E.map z) : (L, E.obj Z) ⟶ (L, E.obj Z'))
  have hu := adj.unit.naturality z
  simp only [Functor.comp_obj, Functor.uncurry_obj_obj, Functor.prod_obj, Functor.comp_map,
    Functor.uncurry_obj_map, Functor.prod_map, Functor.map_id, NatTrans.id_app,
    Category.id_comp, Functor.id_map] at hc hu
  simp only [Iso.app_inv, Category.assoc]
  rw [← Functor.map_comp_assoc, hu, Functor.map_comp_assoc, hc]

/-- The projection map `E(R L ⊗ Z) ⟶ L ⊗ E Z` is natural in `L`. -/
theorem extensionProjectionMapApp_naturality_left {L L' : C} (l : L ⟶ L') (Z : D) :
    E.map ((TD.map (R.map l)).app Z) ≫ extensionProjectionMapApp adj TC TD c L' Z =
      extensionProjectionMapApp adj TC TD c L Z ≫ (TC.map l).app (E.obj Z) := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
    homEquiv_extensionProjectionMapApp, homEquiv_extensionProjectionMapApp]
  have hc := c.inv.naturality ((l, 𝟙 (E.obj Z)) : (L, E.obj Z) ⟶ (L', E.obj Z))
  simp only [Functor.comp_obj, Functor.uncurry_obj_obj, Functor.prod_obj, Functor.comp_map,
    Functor.uncurry_obj_map, Functor.prod_map, Functor.map_id, Category.comp_id] at hc
  simp only [Iso.app_inv, Category.assoc, Functor.comp_obj]
  rw [← NatTrans.naturality_assoc, hc]

/-- **The projection map as a natural transformation of bifunctors**,
`(L, Z) ↦ (E(R L ⊗ Z) ⟶ L ⊗ E Z)`. -/
noncomputable def extensionProjectionMap :
    R ⋙ TD ⋙ (Functor.whiskeringRight D D C).obj E ⟶
      TC ⋙ (Functor.whiskeringLeft D C C).obj E where
  app L :=
    { app := fun Z => extensionProjectionMapApp adj TC TD c L Z
      naturality := fun _ _ z => extensionProjectionMapApp_naturality_right adj TC TD c L z }
  naturality _ _ l := by
    ext Z
    exact extensionProjectionMapApp_naturality_left adj TC TD c l Z

/-- The component of `extensionProjectionMap` at `(L, Z)` is `extensionProjectionMapApp L Z`. -/
theorem extensionProjectionMap_app_app (L : C) (Z : D) :
    ((extensionProjectionMap adj TC TD c).app L).app Z =
      extensionProjectionMapApp adj TC TD c L Z := rfl

/-- **When the unit of `E ⊣ R` is an isomorphism, `R` carries the projection map to an
isomorphism**: its transpose, the unit in the second factor followed by the comparison, is an
isomorphism. -/
theorem isIso_map_extensionProjectionMapApp [IsIso adj.unit] (L : C) (Z : D) :
    IsIso (R.map (extensionProjectionMapApp adj TC TD c L Z)) := by
  have h : adj.unit.app _ ≫ R.map (extensionProjectionMapApp adj TC TD c L Z) =
      (TD.obj (R.obj L)).map (adj.unit.app Z) ≫ (c.app (L, E.obj Z)).inv :=
    (adj.homEquiv_unit _ _ _).symm.trans (homEquiv_extensionProjectionMapApp adj TC TD c L Z)
  have : IsIso (adj.unit.app _ ≫ R.map (extensionProjectionMapApp adj TC TD c L Z)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (adj.unit.app _) _

end CategoryTheory
