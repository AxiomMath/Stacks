module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.ProjectionFormulaInternalHom
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap

/-!
# Duality maps of a cup product pairing, abstractly

Let `L ⊣ R` be an adjunction, `L : 𝒞 ⥤ 𝒟`, let `𝒞` carry a tensor product `T` with an internal
Hom `H` (a `TensorHomAdjunction`) and a natural braiding `β`, let `𝒟` carry a tensor product `B`,
and let `α : L(X ⊗ Y) ⟶ L X ⊗ L Y` be a comparison. For `E : 𝒟`, a multiplication
`ν_Z : E ⊗ Z ⟶ Z` natural in `Z`, an object `M : 𝒞` and a trace `t : R E ⟶ M`, the **duality
map** `D : R E ⟶ H(R E, M)` is adjoint to the pairing `(a, b) ↦ t(ν_*(b ∪ a))` built from the
cup product `R E ⊗ R E ⟶ R(E ⊗ E)` of the adjunction.

The main result, `Stacks.CupDuality.bijective_comp_map_iff`, compares two maps out of hom-sets:
for `H' : 𝒞` at which the projection map `R E ⊗ H' ⟶ R(E ⊗ L H')` is invertible,

`y ↦ t ∘ R(y)`, `Hom(L H', E) ⟶ Hom(R(L H'), M)` is bijective iff `z ↦ D ∘ z`,
`Hom(H', R E) ⟶ Hom(H', H(R E, M))`, is.

The proof is one identity, `Stacks.CupDuality.projection_comp_map_comp`: through the projection
map and the braiding, `t ∘ R(y)` is the adjoint of `D ∘ ŷ`, `ŷ` the adjoint transpose of `y`. It
uses only the naturality of the cup product, of `ν` and of `β`, and the triangle identities; no
unit law of the cup product and no compatibility with shifts. This is the formal core of the
reduction of relative Poincaré duality for a smooth proper curve (part of [Tag 03VH]) to an
isomorphism `R E ≅ H(R E, Λ[-2])`.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Prod
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

namespace Stacks.CupDuality

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {T : C ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ C} (th : TensorHomAdjunction T H)
  (B : D × D ⥤ D) (α : Functor.uncurry.obj T ⋙ L ⟶ L.prod L ⋙ B)

/-- **Tensoring the unit in the second factor turns the cup product into the projection map**:
`(1 ⊗ η_{H'}) ≫ (R G ⊗ R L H' ⟶ R(G ⊗ L H'))` is the projection map `R G ⊗ H' ⟶ R(G ⊗ L H')`. -/
lemma tensor_unit_comp_adjunctionCupProduct (G : D) (H' : C) :
    (T.obj (R.obj G)).map (adj.unit.app H') ≫
        Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct adj
          (Functor.uncurry.obj T) B α G (L.obj H') =
      adjunctionTensorMap adj (Functor.uncurry.obj T) B α G H' := by
  unfold Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct
    adjunctionTensorMap
  have e : (T.obj (R.obj G)).map (adj.unit.app H') =
      (Functor.uncurry.obj T).map (𝟙 (R.obj G) ×ₘ adj.unit.app H') := by
    simp
  rw [e]
  refine (Adjunction.homEquiv_naturality_left adj _ _).symm.trans ?_
  congr 1
  have ha := α.naturality (𝟙 (R.obj G) ×ₘ adj.unit.app H')
  change L.map ((Functor.uncurry.obj T).map (𝟙 (R.obj G) ×ₘ adj.unit.app H')) ≫
      α.app (R.obj G, R.obj (L.obj H')) =
    α.app (R.obj G, H') ≫ B.map (L.map (𝟙 (R.obj G)) ×ₘ L.map (adj.unit.app H')) at ha
  rw [← Category.assoc, ha, Category.assoc, ← Functor.map_comp]
  congr 2
  apply Prod.ext
  · simp
  · simp

variable {B α} (β : ∀ X Y : C, (T.obj X).obj Y ≅ (T.obj Y).obj X)
  (E : D) (ν : ∀ Z : D, B.obj (E, Z) ⟶ Z) (M : C) (t : R.obj E ⟶ M)

/-- **The duality map** `R E ⟶ H(R E, M)`: the adjoint of the pairing `R E ⊗ R E ⟶ M`,
`(a, b) ↦ t(ν_*(b ∪ a))`. -/
def dualityMap : R.obj E ⟶ (H.obj (Opposite.op (R.obj E))).obj M :=
  (th.homEquiv (R.obj E) (R.obj E) M).symm ((β (R.obj E) (R.obj E)).inv ≫
    Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct adj
      (Functor.uncurry.obj T) B α E E ≫ R.map (ν E) ≫ t)

/-- The projection map followed by `R ν`: `R E ⊗ H' ⟶ R(E ⊗ L H') ⟶ R(L H')`. -/
def projectionMultiplication (H' : C) : (T.obj (R.obj E)).obj H' ⟶ R.obj (L.obj H') :=
  adjunctionTensorMap adj (Functor.uncurry.obj T) B α E H' ≫ R.map (ν (L.obj H'))

variable {β ν}

/-- **The key identity**: for `y : L H' ⟶ E` with adjoint transpose `ŷ : H' ⟶ R E`, the trace
of `R(y)` after the projection map is the braiding followed by the adjoint of `D ∘ ŷ`. -/
lemma projection_comp_map_comp
    (hβ : ∀ (X : C) {Y Y' : C} (g : Y ⟶ Y'),
      (T.obj X).map g ≫ (β X Y').hom = (β X Y).hom ≫ (T.map g).app X)
    (hν : ∀ {Z Z' : D} (y : Z ⟶ Z'), B.map (𝟙 E ×ₘ y) ≫ ν Z' = ν Z ≫ y)
    (H' : C) (y : L.obj H' ⟶ E) :
    projectionMultiplication (α := α) adj E ν H' ≫ R.map y ≫ t =
      (β (R.obj E) H').hom ≫ th.homEquiv H' (R.obj E) M
        (adj.homEquiv _ _ y ≫ dualityMap (α := α) adj th β E ν M t) := by
  rw [th.homEquiv_naturality_source, dualityMap, Equiv.apply_symm_apply,
    ← Category.assoc (β (R.obj E) H').hom, ← hβ, Category.assoc, Iso.hom_inv_id_assoc,
    Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have hc := Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct_natural adj
    (Functor.uncurry.obj T) B α (𝟙 E) y
  simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at hc
  rw [reassoc_of% hc, projectionMultiplication,
    ← tensor_unit_comp_adjunctionCupProduct adj B α E H']
  simp only [Category.assoc]
  rw [← R.map_comp_assoc, ← hν, R.map_comp_assoc]

/-- **The duality criterion.** If the projection map `R E ⊗ H' ⟶ R(L H')` (through `ν`) is
invertible, then `y ↦ t ∘ R(y)` on `Hom(L H', E)` is bijective exactly when composition with the
duality map is bijective on `Hom(H', R E)`. -/
theorem bijective_comp_map_iff
    (hβ : ∀ (X : C) {Y Y' : C} (g : Y ⟶ Y'),
      (T.obj X).map g ≫ (β X Y').hom = (β X Y).hom ≫ (T.map g).app X)
    (hν : ∀ {Z Z' : D} (y : Z ⟶ Z'), B.map (𝟙 E ×ₘ y) ≫ ν Z' = ν Z ≫ y)
    (H' : C) [IsIso (projectionMultiplication (α := α) adj E ν H')] :
    Function.Bijective (fun y : L.obj H' ⟶ E => R.map y ≫ t) ↔
      Function.Bijective (fun z : H' ⟶ R.obj E => z ≫ dualityMap (α := α) adj th β E ν M t) := by
  let i : (T.obj H').obj (R.obj E) ≅ R.obj (L.obj H') :=
    (β (R.obj E) H').symm ≪≫ asIso (projectionMultiplication (α := α) adj E ν H')
  have hfac : (fun y : L.obj H' ⟶ E => R.map y ≫ t) =
      ((th.homEquiv H' (R.obj E) M).trans i.homFromEquiv) ∘
        (fun z : H' ⟶ R.obj E => z ≫ dualityMap (α := α) adj th β E ν M t) ∘ adj.homEquiv _ _ := by
    funext y
    simp only [Function.comp_apply, Equiv.trans_apply, Iso.homFromEquiv_apply]
    rw [Iso.eq_inv_comp]
    simp only [i, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
    rw [projection_comp_map_comp (α := α) adj th E M t hβ hν H' y, Iso.inv_hom_id_assoc]
  rw [hfac, Equiv.comp_bijective, Equiv.bijective_comp]

end Stacks.CupDuality
