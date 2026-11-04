module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedUnitSquare
public import StacksFrontier.Homology.DerivedCategory.Bridge.Pushforward

/-!
# The comparison `f_* K ⟶ Rf_* K` on cochain complexes at two models

For a morphism of ringed spaces `f : X ⟶ Y` and a cochain complex `K` of `𝒪_X`-modules, the
comparison `f_* K ⟶ Rf_* K` of the degreewise direct image with the derived direct image, read on
cochain complexes (`StacksDraft.DerivedUnitSquare.unitQ`), is carried by the comparison equivalence
of two models of `D(𝒪_Y)` to the same comparison at the other model, up to the identifications of
the localization functors and of the two derived direct images. Consequently a retraction of a
morphism of the form `Q(κ) ≫ (f_* K ⟶ Rf_* K)` at one model gives one at any other model.

## Main results

* `StacksDraft.DerivedModel.modelEquiv_map_unitQ`: the compatibility.
* `StacksDraft.DerivedModel.exists_retraction_unitQ_of_model`: the transport of a retraction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u w₁ w₂

namespace StacksDraft.DerivedModel

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (hX₁ : HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X)))
  (hY₁ : HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing Y)))
  (hX₂ : HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing X)))
  (hY₂ : HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y)))

/-- A naturality square of an identification `L₁ ⋙ G ≅ L₂`, read after a morphism into the
source. -/
theorem map_comp_comp_hom_app_comp {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L₁ : C ⥤ D} {L₂ : C ⥤ E} {G : D ⥤ E} (e : L₁ ⋙ G ≅ L₂) {X Y : C} (m : X ⟶ Y) {T : D}
    {W : E} (A : T ⟶ L₁.obj X) (R : L₂.obj Y ⟶ W) :
    G.map (A ≫ L₁.map m) ≫ e.hom.app Y ≫ R = G.map A ≫ e.hom.app X ≫ L₂.map m ≫ R := by
  rw [G.map_comp, Category.assoc, ← Category.assoc (G.map (L₁.map m)), ← Functor.comp_map,
    e.hom.naturality, Category.assoc]

/-- **The comparison `f_* K ⟶ Rf_* K` does not depend on the model**: carried by the comparison
equivalence of the models of `D(𝒪_Y)`, and read through the identifications of the localization
functors and of the two derived direct images, it is the comparison at the other model. -/
theorem modelEquiv_map_unitQ (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (modelEquiv hY₁ hY₂).functor.map
        (@StacksDraft.DerivedUnitSquare.unitQ _ _ _ _ _ _ hX₁ hY₁ (modulePushforward f) _
          (@derivedPushforward X Y f hX₁ hY₁) (@derivedPushforwardUnit X Y f hX₁ hY₁) K) ≫
      (derivedPushforwardModelEquivIso f hX₁ hY₁ hX₂ hY₂).hom.app
        ((@DerivedCategory.Q _ _ _ hX₁).obj K) ≫
      (@derivedPushforward X Y f hX₂ hY₂).map ((modelCompQIso hX₁ hX₂).hom.app K) =
    (modelCompQIso hY₁ hY₂).hom.app (((modulePushforward f).mapHomologicalComplex _).obj K) ≫
      @StacksDraft.DerivedUnitSquare.unitQ _ _ _ _ _ _ hX₂ hY₂ (modulePushforward f) _
        (@derivedPushforward X Y f hX₂ hY₂) (@derivedPushforwardUnit X Y f hX₂ hY₂) K := by
  have hfac := derivedPushforwardModelEquivIso_hom_app_fac f hX₁ hY₁ hX₂ hY₂
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
  have hnat := (derivedPushforwardModelEquivIso f hX₁ hY₁ hX₂ hY₂).hom.naturality
    ((@DerivedCategory.quotientCompQhIso _ _ _ hX₁).hom.app K)
  simp only [Functor.comp_map] at hnat
  simp only [StacksDraft.DerivedUnitSquare.unitQ, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat, reassoc_of% hfac]
  simp only [comp_obj, pushforwardToDerivedCategoryModelEquivIso, Iso.trans_hom,
    isoWhiskerLeft_hom, NatTrans.comp_app, associator_hom_app, whiskerLeft_app, Category.id_comp,
    modelCompQIso, isoWhiskerRight_hom, Iso.symm_hom, whiskerRight_app, ← map_comp,
    ← map_comp_assoc, Iso.hom_inv_id_app, map_id, Iso.inv_hom_id_app_assoc, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  exact map_comp_comp_hom_app_comp (G := (modelEquiv hY₁ hY₂).functor)
    (Localization.compUniqFunctor (@DerivedCategory.Qh _ _ _ hY₁) (@DerivedCategory.Qh _ _ _ hY₂)
      (HomotopyCategory.subcategoryAcyclic _).trW) _ _ _

/-- **A retraction of `Q(κ) ≫ (f_* K ⟶ Rf_* K)` transports between models.** -/
theorem exists_retraction_unitQ_of_model
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    {L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ}
    (κ : L ⟶ ((modulePushforward f).mapHomologicalComplex _).obj K)
    (h : ∃ r, (@DerivedCategory.Q _ _ _ hY₁).map κ ≫
        @StacksDraft.DerivedUnitSquare.unitQ _ _ _ _ _ _ hX₁ hY₁ (modulePushforward f) _
          (@derivedPushforward X Y f hX₁ hY₁) (@derivedPushforwardUnit X Y f hX₁ hY₁) K ≫ r =
        𝟙 _) :
    ∃ r, (@DerivedCategory.Q _ _ _ hY₂).map κ ≫
        @StacksDraft.DerivedUnitSquare.unitQ _ _ _ _ _ _ hX₂ hY₂ (modulePushforward f) _
          (@derivedPushforward X Y f hX₂ hY₂) (@derivedPushforwardUnit X Y f hX₂ hY₂) K ≫ r =
        𝟙 _ := by
  obtain ⟨r, hr⟩ := h
  let E := (modelEquiv hY₁ hY₂).functor
  let α := (modelCompQIso hY₁ hY₂).app L
  let β := (derivedPushforwardModelEquivIso f hX₁ hY₁ hX₂ hY₂).app
      ((@DerivedCategory.Q _ _ _ hX₁).obj K) ≪≫
    (@derivedPushforward X Y f hX₂ hY₂).mapIso ((modelCompQIso hX₁ hX₂).app K)
  refine ⟨β.inv ≫ E.map r ≫ α.hom, ?_⟩
  have hq := (modelCompQIso hY₁ hY₂).hom.naturality κ
  have hu := modelEquiv_map_unitQ f hX₁ hY₁ hX₂ hY₂ K
  have key : α.inv ≫ E.map ((@DerivedCategory.Q _ _ _ hY₁).map κ ≫
      @StacksDraft.DerivedUnitSquare.unitQ _ _ _ _ _ _ hX₁ hY₁ (modulePushforward f) _
        (@derivedPushforward X Y f hX₁ hY₁) (@derivedPushforwardUnit X Y f hX₁ hY₁) K) ≫ β.hom =
      (@DerivedCategory.Q _ _ _ hY₂).map κ ≫
        @StacksDraft.DerivedUnitSquare.unitQ _ _ _ _ _ _ hX₂ hY₂ (modulePushforward f) _
          (@derivedPushforward X Y f hX₂ hY₂) (@derivedPushforwardUnit X Y f hX₂ hY₂) K := by
    simp only [Functor.comp_map] at hq
    have hβ : β.hom = (derivedPushforwardModelEquivIso f hX₁ hY₁ hX₂ hY₂).hom.app
        ((@DerivedCategory.Q _ _ _ hX₁).obj K) ≫
        (@derivedPushforward X Y f hX₂ hY₂).map ((modelCompQIso hX₁ hX₂).hom.app K) := rfl
    rw [hβ]
    simp only [Functor.map_comp, Category.assoc]
    rw [hu, reassoc_of% hq]
    simp only [α, Iso.app_inv, Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc, ← key]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← E.map_comp_assoc, Category.assoc, hr, E.map_id, Category.id_comp]
  exact α.inv_hom_id

end StacksDraft.DerivedModel

end
