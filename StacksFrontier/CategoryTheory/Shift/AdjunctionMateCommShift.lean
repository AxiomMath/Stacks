module

public import Mathlib.CategoryTheory.Shift.Adjunction

/-!
# The adjoint transpose of a shift-compatible natural transformation

Let `adj : F ⊣ G` be an adjunction between categories carrying a shift by an additive monoid
`A`, compatible with the shift in the sense of `CategoryTheory.Adjunction.CommShift`, and let
`H` and `K` be two further functors into the two categories, also compatible with the shift.
The adjunction turns a natural transformation `τ : H ⟶ K ⋙ G` into its adjoint transpose
`H ⋙ F ⟶ K`, whose value at an object is the inverse hom-equivalence applied to the value of
`τ`. This file records that the transpose commutes with the shift as soon as `τ` does.

## Main results

* `CategoryTheory.Adjunction.homEquiv_symm_app_commShift`: the shift compatibility of the
  transpose, in the form of a commuting square at an object.
* `CategoryTheory.Adjunction.natTrans_commShift_of_homEquiv_symm`: a natural transformation
  `H ⋙ F ⟶ K` whose values are the transposes of the values of `τ` commutes with the shift.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Category

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Category.{v₁} B] {E : Type u₂} [Category.{v₂} E]
  {D : Type u₃} [Category.{v₃} D] (A : Type*) [AddMonoid A]
  [HasShift B A] [HasShift E A] [HasShift D A]
  {F : B ⥤ E} {G : E ⥤ B} (adj : F ⊣ G)
  [F.CommShift A] [G.CommShift A] [adj.CommShift A]
  (H : D ⥤ B) (K : D ⥤ E) [H.CommShift A] [K.CommShift A]
  (τ : H ⟶ K ⋙ G) [NatTrans.CommShift τ A]

/-- The adjoint transpose of a natural transformation commuting with the shift commutes with the
shift. Both sides are compared after applying the hom-equivalence of the adjunction, where the
statement becomes the compatibility of `τ` with the shift. -/
lemma homEquiv_symm_app_commShift (X : D) (a : A) :
    (Functor.commShiftIso (H ⋙ F) a).hom.app X ≫
        (((adj.homEquiv (H.obj X) (K.obj X)).symm (τ.app X))⟦a⟧') =
      (adj.homEquiv (H.obj (X⟦a⟧)) (K.obj (X⟦a⟧))).symm
          (τ.app (X⟦a⟧)) ≫ (K.commShiftIso a).hom.app X := by
  apply (adj.homEquiv (H.obj (X⟦a⟧)) (K.obj X⟦a⟧)).injective
  simp only [Functor.commShiftIso_comp_hom_app,
    Adjunction.homEquiv_apply, Adjunction.homEquiv_symm_apply]
  simp only [Functor.comp_obj, Functor.map_comp, Adjunction.shift_counit_app, Functor.id_obj,
    Functor.commShiftIso_inv_naturality_assoc, Category.assoc, Iso.hom_inv_id_app_assoc,
    Adjunction.unit_naturality_assoc, Adjunction.right_triangle_components, Category.comp_id,
    Adjunction.right_triangle_components_assoc]
  calc
    _ = τ.app (X⟦a⟧) ≫ (Functor.commShiftIso (K ⋙ G) a).hom.app X ≫
          (G.commShiftIso a).inv.app (K.obj X) := by
      simpa using congrArg (fun f => f ≫ (G.commShiftIso a).inv.app (K.obj X))
        (NatTrans.shift_app_comm τ a X)
    _ = τ.app (X⟦a⟧) ≫ G.map ((K.commShiftIso a).hom.app X) := by
      simp [Functor.commShiftIso_comp_hom_app]

/-- A natural transformation `H ⋙ F ⟶ K` whose value at every object is the adjoint transpose
of the value of `τ` commutes with the shift. -/
lemma natTrans_commShift_of_homEquiv_symm (σ : H ⋙ F ⟶ K)
    (hσ : ∀ X : D, σ.app X = (adj.homEquiv (H.obj X) (K.obj X)).symm (τ.app X)) :
    NatTrans.CommShift σ A := by
  apply NatTrans.CommShift.of_core
  intro a
  constructor
  ext X
  change (Functor.commShiftIso (H ⋙ F) a).hom.app X ≫ (σ.app X)⟦a⟧' =
    σ.app (X⟦a⟧) ≫ (K.commShiftIso a).hom.app X
  rw [hσ X, hσ (X⟦a⟧)]
  exact homEquiv_symm_app_commShift A adj H K τ X a

end CategoryTheory.Adjunction

end
