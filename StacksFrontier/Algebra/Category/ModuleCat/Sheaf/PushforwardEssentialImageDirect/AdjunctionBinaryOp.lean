module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Transporting a binary operation across the unit of an adjunction

Let `L ⊣ R` be an adjunction between categories with binary products, with `R` preserving binary
products. Suppose a "binary operation" `c : A ⨯ B ⟶ B` upstairs and one `d : X ⨯ L B ⟶ L B`
downstairs are intertwined by `L`, through the canonical product comparison, along a map
`a : L A ⟶ X`. Then the unit of the adjunction intertwines `c` with the operation on `R (L B)`
obtained from `d` by the product comparison for `R`.

This is the only categorical input needed to see that the unit of a morphism of topoi is a
morphism of sheaves of modules: taking `c` to be the addition or the scalar multiplication of a
sheaf of modules and `d` the corresponding operation on its inverse image, the hypothesis is the
statement that the inverse-image module structure is transported from the original one, and the
conclusion is one of the two squares that a morphism of sheaves of modules has to satisfy.

## Main results

* `CategoryTheory.Adjunction.binaryOp_comp_unit`: the displayed transport.
* `CategoryTheory.Adjunction.binaryOp_comp_unit_id`: its case `A = B`, `a = 𝟙`, which is the form
  an additive structure is transported in.

## Implementation notes

The operation downstairs is taken on `X ⨯ L.obj B` rather than on a general `X ⨯ Y` with a map
`L.obj B ⟶ Y`: both applications have that second map an identity, and keeping it an identity
removes a layer of `Functor.map_id` rewriting from every use site.

The hypothesis is an equation between morphisms of the lower category and the conclusion an
equation between morphisms of the upper one; no object of either category is assumed to be a
product of representables or anything else. In particular nothing here is specific to sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C]
  {D : Type u₂} [Category.{v₂} D] [HasBinaryProducts D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [PreservesLimitsOfShape (Discrete WalkingPair) R]

/-- **Transport of a binary operation across the unit of an adjunction.** If `L` carries the
operation `c : A ⨯ B ⟶ B` to the operation `d : X ⨯ L B ⟶ L B` along `a : L A ⟶ X`, read through
the product comparison for `L`, then the unit of `L ⊣ R` carries `c` to the operation on `R (L B)`
read off from `d` through the product comparison for `R`.

The two instances used below are the addition and the scalar multiplication of a sheaf of
modules. -/
theorem binaryOp_comp_unit {A B : C} {X : D} (a : L.obj A ⟶ X)
    (c : A ⨯ B ⟶ B) (d : X ⨯ L.obj B ⟶ L.obj B)
    (h : L.map c = prodComparison L A B ≫ prod.map a (𝟙 (L.obj B)) ≫ d) :
    c ≫ adj.unit.app B =
      prod.map (adj.unit.app A ≫ R.map a) (adj.unit.app B) ≫
        inv (prodComparison R X (L.obj B)) ≫ R.map d := by
  have hp : adj.unit.app (A ⨯ B) ≫ R.map (prodComparison L A B) ≫
      R.map (prod.map a (𝟙 (L.obj B))) ≫ prodComparison R X (L.obj B) =
        prod.map (adj.unit.app A ≫ R.map a) (adj.unit.app B) := by
    have hfst := adj.unit.naturality_assoc (prod.fst (X := A) (Y := B)) (R.map a)
    have hsnd := adj.unit.naturality (prod.snd (X := A) (Y := B))
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hfst hsnd
    have hfst' : adj.unit.app (A ⨯ B) ≫ R.map (L.map (prod.fst (X := A) (Y := B)) ≫ a) =
        prod.fst ≫ adj.unit.app A ≫ R.map a := by
      rw [Functor.map_comp]
      exact hfst.symm
    apply prod.hom_ext
    · simp [← Functor.map_comp, hfst']
    · simp [← Functor.map_comp, ← hsnd]
  calc c ≫ adj.unit.app B = adj.unit.app (A ⨯ B) ≫ R.map (L.map c) :=
        adj.unit.naturality c
    _ = _ := by
      rw [h, Functor.map_comp, Functor.map_comp, ← hp]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]

/-- The case `A = B` and `a = 𝟙` of `CategoryTheory.Adjunction.binaryOp_comp_unit`: an operation
`c : B ⨯ B ⟶ B` carried by `L` to `d : L B ⨯ L B ⟶ L B` is carried by the unit to the operation
on `R (L B)` read off from `d` through the product comparison for `R`.

This is the form the addition of a sheaf of modules is used in; the general form, with a map
`a : L A ⟶ X` in the first variable, is what the scalar multiplication needs. -/
theorem binaryOp_comp_unit_id {B : C} (c : B ⨯ B ⟶ B) (d : L.obj B ⨯ L.obj B ⟶ L.obj B)
    (h : L.map c = prodComparison L B B ≫ d) :
    c ≫ adj.unit.app B =
      prod.map (adj.unit.app B) (adj.unit.app B) ≫
        inv (prodComparison R (L.obj B) (L.obj B)) ≫ R.map d := by
  have h' : L.map c = prodComparison L B B ≫ prod.map (𝟙 (L.obj B)) (𝟙 (L.obj B)) ≫ d := by
    rw [prod.map_id_id, Category.id_comp]
    exact h
  have hu : adj.unit.app B ≫ R.map (𝟙 (L.obj B)) = adj.unit.app B := by
    rw [Functor.map_id]
    exact Category.comp_id _
  have key := adj.binaryOp_comp_unit (𝟙 (L.obj B)) c d h'
  rw [hu] at key
  exact key

end CategoryTheory.Adjunction

end
