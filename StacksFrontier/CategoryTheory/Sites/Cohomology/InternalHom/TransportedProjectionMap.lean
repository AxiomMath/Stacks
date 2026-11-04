module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomAdjunctionTransport
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMapTransport

/-!
# The projection-formula map of an adjunction transported along equivalences

Let `e_C : C' ≌ C` and `e_D : D' ≌ D` be equivalences, `adj : L ⊣ R` an adjunction with
`L : C ⥤ D`, and let `L' : C' ⥤ D'`, `R' : D' ⥤ C'` be functors with
`κ : e_C ⋙ L ≅ L' ⋙ e_D` and `ρ : R' ≅ e_D ⋙ R ⋙ e_C⁻¹`. The adjunction `adj` read along the
equivalences is an adjunction `L' ⊣ R'` (`transportedAdjunction`), and a comparison
`μ : T_C(A, B) ⋙ L ≅ ...` of tensor bifunctors is read as a comparison of the transported
bifunctors by `TensorHomAdjunction.transportTensorIso`. This file proves that these transported
data satisfy the two hypotheses of `CategoryTheory.map_adjunctionTensorMap_of_counit_comm` (the
counits and the comparisons correspond), so that the projection-formula map of the transported
data is the one of the original data read through the equivalences; in particular one is
invertible exactly when the other is.

## Main definitions

* `Stacks.CategoryTheory.ProjectionMapTransport.transportedAdjunction`.
* `Stacks.CategoryTheory.ProjectionMapTransport.transportedPushforwardIso`:
  `R' ⋙ e_C ≅ e_D ⋙ R`.
* `Stacks.CategoryTheory.ProjectionMapTransport.transportTensorCompIso`:
  `T_e ⋙ e ≅ (e × e) ⋙ T` for a transported bifunctor.

## Main results

* `Stacks.CategoryTheory.ProjectionMapTransport.map_homEquiv_transportedAdjunction` and
  `counit_transportedAdjunction`: the adjunction bijections and the counits correspond.
* `Stacks.CategoryTheory.ProjectionMapTransport.comparison_transportTensorIso`: the comparisons
  of tensor products correspond.
* `Stacks.CategoryTheory.ProjectionMapTransport.isIso_adjunctionTensorMap_transport_iff`.
-/

@[expose] public noncomputable section

namespace Stacks.CategoryTheory.ProjectionMapTransport

open _root_.CategoryTheory
open scoped _root_.CategoryTheory.Prod
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
  (eC : C' ≌ C) (eD : D' ≌ D)
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {L' : C' ⥤ D'} {R' : D' ⥤ C'}
  (κ : eC.functor ⋙ L ≅ L' ⋙ eD.functor) (ρ : R' ≅ eD.functor ⋙ R ⋙ eC.inverse)

/-- **The adjunction `L ⊣ R` read along the equivalences**, as an adjunction `L' ⊣ R'`. -/
def transportedAdjunction : L' ⊣ R' :=
  ((eC.toAdjunction.comp (adj.comp eD.symm.toAdjunction)).ofNatIsoLeft
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight κ _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ eD.unitIso.symm ≪≫
        Functor.rightUnitor _)).ofNatIsoRight
    ((Functor.associator _ _ _) ≪≫ ρ.symm)

/-- The comparison `R' ⋙ e_C ≅ e_D ⋙ R` induced by `ρ`. -/
def transportedPushforwardIso : R' ⋙ eC.functor ≅ eD.functor ⋙ R :=
  Functor.isoWhiskerRight ρ eC.functor ≪≫
    Functor.isoWhiskerLeft (eD.functor ⋙ R) eC.counitIso ≪≫ Functor.rightUnitor _

/-- **The transported adjunction bijection is the original one**, read through the
equivalences. -/
theorem map_homEquiv_transportedAdjunction (X : C') (Y : D') (f : L'.obj X ⟶ Y) :
    eC.functor.map ((transportedAdjunction eC eD adj κ ρ).homEquiv X Y f) =
      adj.homEquiv _ _ (κ.hom.app X ≫ eD.functor.map f) ≫
        (transportedPushforwardIso eC eD ρ).inv.app Y := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.comp_obj, transportedAdjunction, Adjunction.ofNatIsoRight,
    Equivalence.symm_inverse, Adjunction.ofNatIsoLeft, Equivalence.symm_functor, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_comp, Functor.whiskerRight_twice, Category.assoc, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_comp,
    Functor.whiskerLeft_twice, NatTrans.comp_app, Functor.id_obj, Adjunction.comp_unit_app,
    Equivalence.toAdjunction_unit, Equivalence.symm_unit, Functor.map_comp,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.comp_map,
    CategoryTheory.Functor.map_id, Functor.associator_hom_app, Equivalence.fun_inv_map,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.id_comp, cancelIso,
    Iso.inv_hom_id_app_assoc, Equivalence.functor_unit_comp_assoc, transportedPushforwardIso,
    Functor.rightUnitor_inv_app]
  congr 2
  rw [← R.map_comp_assoc, Equivalence.counitInv_app_functor, ← eD.functor.map_comp,
    Iso.hom_inv_id_app]
  simp only [CategoryTheory.Functor.map_id, Functor.id_obj, Category.id_comp]
  rw [← eC.functor.map_comp, ← ρ.inv.naturality f, eC.functor.map_comp, Functor.comp_map,
    Functor.comp_map, ← Category.assoc, eC.counitInv_naturality, Category.assoc]

/-- **The counit of the transported adjunction is the original one**, read through the
equivalences. -/
theorem counit_transportedAdjunction (Y : D') :
    κ.hom.app (R'.obj Y) ≫ eD.functor.map ((transportedAdjunction eC eD adj κ ρ).counit.app Y) =
      L.map ((transportedPushforwardIso eC eD ρ).hom.app Y) ≫ adj.counit.app (eD.functor.obj Y) :=
          by
  have h₁ := map_homEquiv_transportedAdjunction eC eD adj κ ρ (R'.obj Y) Y
    ((transportedAdjunction eC eD adj κ ρ).counit.app Y)
  rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components,
    CategoryTheory.Functor.map_id] at h₁
  have h₂ : adj.homEquiv _ _ (κ.hom.app (R'.obj Y) ≫
      eD.functor.map ((transportedAdjunction eC eD adj κ ρ).counit.app Y)) =
      (transportedPushforwardIso eC eD ρ).hom.app Y := by
    rw [← cancel_mono ((transportedPushforwardIso eC eD ρ).inv.app Y), Iso.hom_inv_id_app]
    exact h₁.symm
  rw [← (adj.homEquiv _ _).symm_apply_apply (κ.hom.app (R'.obj Y) ≫ eD.functor.map _), h₂,
    Adjunction.homEquiv_counit]
  rfl

/-- **A transported bifunctor followed by the equivalence** is the bifunctor applied to the images:
`T_e(A, B) ⋙ e ≅ T(e A, e B)`, through the counit of `e`. -/
def transportTensorCompIso {E E' : Type*} [Category E] [Category E'] (e : E' ≌ E)
    (T : E ⥤ E ⥤ E) :
    Functor.uncurry.obj (TensorHomAdjunction.transportTensor e T) ⋙ e.functor ≅
      e.functor.prod e.functor ⋙ Functor.uncurry.obj T :=
  Functor.isoWhiskerRight (TensorHomAdjunction.uncurryTransportTensorIso e T) e.functor ≪≫
    Functor.isoWhiskerLeft (e.functor.prod e.functor ⋙ Functor.uncurry.obj T) e.counitIso ≪≫
    Functor.rightUnitor _

variable {TC : C ⥤ C ⥤ C} {TD : D ⥤ D ⥤ D}
  (μ : Functor.uncurry.obj TC ⋙ L ≅ L.prod L ⋙ Functor.uncurry.obj TD)

/-- **The transported comparison of tensor products is the original one**, read through the
equivalences. -/
theorem comparison_transportTensorIso (a b : C') :
    κ.hom.app ((Functor.uncurry.obj (TensorHomAdjunction.transportTensor eC TC)).obj (a, b)) ≫
        eD.functor.map ((TensorHomAdjunction.transportTensorIso eD eC κ μ).hom.app (a, b)) =
      L.map ((transportTensorCompIso eC TC).symm.inv.app (a, b)) ≫
        μ.hom.app (eC.functor.obj a, eC.functor.obj b) ≫
          (Functor.uncurry.obj TD).map (κ.hom.app a ×ₘ κ.hom.app b) ≫
            (transportTensorCompIso eD TD).symm.hom.app (L'.obj a, L'.obj b) := by
  simp [TensorHomAdjunction.transportTensorIso, TensorHomAdjunction.transportInverseIso,
    transportTensorCompIso, TensorHomAdjunction.uncurryTransportTensorIso]

/-- **The projection-formula map of the transported data is invertible exactly when the one of
the original data is**, at the images of the objects under the equivalences. -/
theorem isIso_adjunctionTensorMap_transport_iff (G : D') (H : C') :
    IsIso (adjunctionTensorMap (transportedAdjunction eC eD adj κ ρ)
        (Functor.uncurry.obj (TensorHomAdjunction.transportTensor eC TC))
        (Functor.uncurry.obj (TensorHomAdjunction.transportTensor eD TD))
        (TensorHomAdjunction.transportTensorIso eD eC κ μ).hom G H) ↔
      IsIso (adjunctionTensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) μ.hom
        (eD.functor.obj G) (eC.functor.obj H)) := by
  rw [← isIso_map_adjunctionTensorMap_iff_of_counit_comm (transportedAdjunction eC eD adj κ ρ)
    adj κ (transportedPushforwardIso eC eD ρ).symm (transportTensorCompIso eC TC).symm
    (transportTensorCompIso eD TD).symm _ μ.hom (counit_transportedAdjunction eC eD adj κ ρ)
    (comparison_transportTensorIso eC eD κ μ) G H]
  exact (isIso_iff_of_reflects_iso _ eC.functor).symm

end Stacks.CategoryTheory.ProjectionMapTransport

end
