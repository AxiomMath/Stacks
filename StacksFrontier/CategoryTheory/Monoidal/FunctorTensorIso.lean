module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# The tensor comparison of a monoidal functor, on prescribed bifunctors

Let `F : C ⥤ D` be a monoidal functor, and let `T_C` and `T_D` be bifunctors isomorphic to the
tensor products of `C` and `D`. Then the oplax tensorator of `F`, conjugated by these
isomorphisms, is a natural isomorphism `F(T_C(Q, P)) ≅ T_D(F Q, F P)` of functors on `C × C`.

## Main definitions

* `CategoryTheory.Functor.Monoidal.swapTensorIso`: the natural isomorphism
  `F(T_C(Q, P)) ≅ T_D(F Q, F P)` of functors of `(P, Q) ∈ C × C`.

## Main results

* `CategoryTheory.Functor.Monoidal.swapTensorIso_hom_app`: the component of `swapTensorIso` at
  `(P, Q)` is `F(eC) ≫ δ F Q P ≫ eD⁻¹`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Monoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
  {TC : C ⥤ C ⥤ C} {TD : D ⥤ D ⥤ D} (eC : TC ≅ curriedTensor C) (eD : TD ≅ curriedTensor D)

/-- The component at `(P, Q)` of `swapTensorIso`: `F(T_C(Q, P)) ≅ T_D(F Q, F P)`. -/
abbrev swapTensorIsoApp (P Q : C) :
    F.obj ((TC.obj Q).obj P) ≅ (TD.obj (F.obj Q)).obj (F.obj P) :=
  F.mapIso ((eC.app Q).app P) ≪≫ (μIso F Q P).symm ≪≫ (eD.symm.app (F.obj Q)).app (F.obj P)

/-- The isomorphisms `swapTensorIsoApp F eC eD P Q` are natural in `P` and `Q`. -/
lemma swapTensorIsoApp_naturality {P P' Q Q' : C} (p : P ⟶ P') (q : Q ⟶ Q') :
    F.map ((TC.map q).app P ≫ (TC.obj Q').map p) ≫ (swapTensorIsoApp F eC eD P' Q').hom =
      (swapTensorIsoApp F eC eD P Q).hom ≫
        (TD.map (F.map q)).app (F.obj P) ≫ (TD.obj (F.obj Q')).map (F.map p) := by
  have hC₁ : (TC.map q).app P ≫ (eC.hom.app Q').app P = (eC.hom.app Q).app P ≫ q ▷ P :=
    NatTrans.congr_app (eC.hom.naturality q) P
  have hC₂ : (TC.obj Q').map p ≫ (eC.hom.app Q').app P' = (eC.hom.app Q').app P ≫ Q' ◁ p :=
    (eC.hom.app Q').naturality p
  have hD₁ : (eD.inv.app (F.obj Q)).app (F.obj P) ≫ (TD.map (F.map q)).app (F.obj P) =
      F.map q ▷ F.obj P ≫ (eD.inv.app (F.obj Q')).app (F.obj P) :=
    (NatTrans.congr_app (eD.inv.naturality (F.map q)) (F.obj P)).symm
  have hD₂ : (eD.inv.app (F.obj Q')).app (F.obj P) ≫ (TD.obj (F.obj Q')).map (F.map p) =
      F.obj Q' ◁ F.map p ≫ (eD.inv.app (F.obj Q')).app (F.obj P') :=
    ((eD.inv.app (F.obj Q')).naturality (F.map p)).symm
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, μIso_inv,
    Category.assoc]
  rw [reassoc_of% hD₁, hD₂, ← F.map_comp_assoc, Category.assoc, hC₂,
    reassoc_of% hC₁, F.map_comp_assoc, F.map_comp_assoc, ← δ_natural_right_assoc,
    ← δ_natural_left_assoc]

/-- **The tensor comparison of a monoidal functor on prescribed bifunctors**: the oplax
tensorator `δ` of `F`, conjugated by `eC : T_C ≅ curriedTensor C` and
`eD : T_D ≅ curriedTensor D`, as a natural isomorphism `F(T_C(Q, P)) ≅ T_D(F Q, F P)` of functors
of `(P, Q) ∈ C × C`. -/
def swapTensorIso :
    Prod.swap C C ⋙ Functor.uncurry.obj TC ⋙ F ≅
      F.prod F ⋙ Prod.swap D D ⋙ Functor.uncurry.obj TD :=
  NatIso.ofComponents (fun PQ ↦ swapTensorIsoApp F eC eD PQ.1 PQ.2)
    (fun {_ _} pq ↦ swapTensorIsoApp_naturality F eC eD pq.1 pq.2)

/-- The component of `swapTensorIso` at `(P, Q)` is the composite of `F` applied to `eC`, the
oplax tensorator `δ F Q P`, and the inverse of `eD`. -/
lemma swapTensorIso_hom_app (P Q : C) :
    (swapTensorIso F eC eD).hom.app (P, Q) =
      F.map ((eC.hom.app Q).app P) ≫ δ F Q P ≫ (eD.inv.app (F.obj Q)).app (F.obj P) :=
  rfl

end CategoryTheory.Functor.Monoidal

end
