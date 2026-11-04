module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.ConstantProjectionMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.DirectImageRestrictUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.DerivedExtensionOfScalars

/-!
# The projection map is compatible with the action of `Λ₂`

Let `φ : Λ₁ → Λ₂` be a homomorphism of commutative rings, `g : X ⟶ Y` a morphism of schemes and
`F` an étale sheaf of `Λ₂`-modules on `X`.  The action `res(g_*F) ⊗_{Λ₁} Λ̲₂ ⟶ res(g_*F)` of `Λ₂`
on the direct image is the projection map `g_*(res F) ⊗ Λ̲₂ ⟶ g_*(res F ⊗ Λ̲₂)` followed by the
direct image of the action on `F`.

Both sides are maps out of the sheafified tensor product `res(g_*F) ⊗ Λ̲₂`, so they are determined
by their composites with the sectionwise tensor product of `res(g_*F)` with the constant presheaf
`Λ₂`; on it both sides are the sectionwise action `s ⊗ λ ↦ λ • s`
(`Stacks.EtaleCohomology.presheafCoefficientAction`).

## Main results

* `Stacks.EtaleCohomology.etaleModuleConstantProjectionMapApp_coefficientAction`: the projection
  map intertwines the actions of `Λ₂`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v₁ v₂ u₁ u₂ v₃ u₃ u r

namespace Stacks.SheafTensorSections

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {A : Type u₃} [Category.{v₃} A] [MonoidalCategory A] [HasWeakSheafify J A]
  [(J.W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory

/-- The sheafification of `S ⊗ Q` for a sheaf `S` and a presheaf `Q`, read through the
sheafification of `S ⊗ sheafify Q` and the counit of `S`, is the identity. -/
@[reassoc]
lemma presheafToSheafTensorIso_whiskerLeft_toSheafify_μ (S : Sheaf J A) (Q : Cᵒᵖ ⥤ A) :
    (presheafToSheaf J A).map (S.obj ◁ toSheafify J Q) ≫
        (presheafToSheafTensorIso J S ((presheafToSheaf J A).obj Q)).hom ≫
          (asIso (sheafificationAdjunction J A).counit).inv.app S ▷ (presheafToSheaf J A).obj Q ≫
            Functor.LaxMonoidal.μ (presheafToSheaf J A) S.obj Q =
      𝟙 _ := by
  simp only [presheafToSheafTensorIso, Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv,
    tensorIso_hom, asIso_hom, Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc, whiskerLeft_comp_tensorHom_assoc,
    Adjunction.left_triangle_components, tensorHom_id, ← comp_whiskerRight_assoc,
    show (sheafificationAdjunction J A).counit.app S ≫
        (asIso (sheafificationAdjunction J A).counit).inv.app S = 𝟙 _ from
      (asIso (sheafificationAdjunction J A).counit).hom_inv_id_app S]
  simp

/-- The sectionwise form of `presheafToSheafTensorIso_whiskerLeft_toSheafify_μ`: on the sectionwise
tensor product with the sheafification unit of `Q`, the map `S ⊗ sheafify Q ⟶ sheafify(S ⊗ Q)` is
the sheafification unit of `S ⊗ Q`. -/
@[reassoc]
lemma whiskerLeft_toSheafify_tensorSectionMap_μ (S : Sheaf J A) (Q : Cᵒᵖ ⥤ A) :
    (S.obj ◁ toSheafify J Q) ≫ tensorSectionMap J S ((presheafToSheaf J A).obj Q) ≫
        ((asIso (sheafificationAdjunction J A).counit).inv.app S ▷
          (presheafToSheaf J A).obj Q).hom ≫
          (Functor.LaxMonoidal.μ (presheafToSheaf J A) S.obj Q).hom =
      toSheafify J (S.obj ⊗ Q) := by
  have h := congrArg (fun f => toSheafify J (S.obj ⊗ Q) ≫ f.hom)
    (presheafToSheafTensorIso_whiskerLeft_toSheafify_μ J S Q)
  simp only [ObjectProperty.FullSubcategory.comp_hom] at h
  simp only [tensorSectionMap, Category.assoc]
  rw [toSheafify_naturality_assoc]
  exact h.trans (Category.comp_id _)

section Pushforward

variable {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D) [HasWeakSheafify K A]
  [(K.W (A := A)).IsMonoidal] (G : C ⥤ D) [G.IsContinuous J K]

/-- **The projection map on sections.** On the sectionwise tensor product with the sheafification
unit of the constant presheaf `M`, the projection map `G_*S ⊗ c(M) ⟶ G_*(S ⊗ c(M))` followed by
`G_*f` is the restriction along `G` of the corresponding sectionwise map for `f`. -/
lemma whiskerLeft_constantToSheafify_tensorSectionMap_constantProjectionMap (S : Sheaf K A)
    (M : A) {S' : Sheaf K A} (f : S ⊗ (constantSheaf K A).obj M ⟶ S') :
    ((G.sheafPushforwardContinuous A J K).obj S).obj ◁ constantToSheafify J M ≫
        tensorSectionMap J ((G.sheafPushforwardContinuous A J K).obj S)
          ((constantSheaf J A).obj M) ≫
          (constantProjectionMap J K G S M ≫ (G.sheafPushforwardContinuous A J K).map f).hom =
      Functor.whiskerLeft G.op (S.obj ◁ constantToSheafify K M ≫
        tensorSectionMap K S ((constantSheaf K A).obj M) ≫ f.hom) := by
  simp only [constantProjectionMap, ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
  rw [← tensorSectionMap_whiskerLeft_assoc, ← whiskerLeft_comp_assoc,
    constantToSheafify_constantSheafPushforwardMap,
    tensorSectionMap_sheafPushforwardTensorMap_assoc]
  rfl

end Pushforward

end Stacks.SheafTensorSections

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleMonoidalCategory etaleModuleBraidedCategory

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)

/-- **The sectionwise action of `Λ₂`** on a presheaf `P` of `Λ₂`-modules read as `Λ₁`-modules,
`res P ⊗_{Λ₁} Λ₂ ⟶ res P`: the counit of extension of scalars read through
`res(M ⊗_{Λ₁} Λ₂) ≅ M ⊗_{Λ₁} Λ₂`, section by section. -/
def presheafCoefficientAction {C : Type*} [Category C] (P : C ⥤ ModuleCat.{max (u + 1) r} Λ₂) :
    (P ⋙ ModuleCat.restrictScalars φ) ⊗ (Functor.const C).obj (coefficientModule.{u} φ) ⟶
      P ⋙ ModuleCat.restrictScalars φ :=
  (whiskeringRightTensorRightIso (coefficientModule.{u} φ)).inv.app
      (P ⋙ ModuleCat.restrictScalars φ) ≫
    Functor.whiskerLeft (P ⋙ ModuleCat.restrictScalars φ)
      (extendRestrictScalarsIsoTensorRight.{u} φ).inv ≫
    Functor.whiskerLeft P (Functor.whiskerRight
      (ModuleCat.extendRestrictScalarsAdj.{max (u + 1) r, r, r} φ).counit
      (ModuleCat.restrictScalars φ))

section Sheaf

variable (X : Scheme.{u})

attribute [local instance] isMonoidal_W_smallEtale_module

/-- The inverse of `res(H ⊗_{Λ₁} Λ₂) ≅ H ⊗_{Λ₁} Λ̲₂`, component by component. -/
lemma etaleModuleExtendRestrictScalarsIso_inv_app (H : EtaleModules.{u, r} Λ₁ X) :
    (etaleModuleExtendRestrictScalarsIso.{u, r} φ X).inv.app H =
      (asIso (sheafificationAdjunction X.smallEtaleTopology
          (ModuleCat.{max (u + 1) r} Λ₁)).counit).inv.app H ▷ coefficientSheaf.{u} φ X ≫
        Functor.LaxMonoidal.μ (presheafToSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ₁))
          H.obj ((Functor.const X.Etaleᵒᵖ).obj (coefficientModule.{u} φ)) ≫
        (presheafToSheaf X.smallEtaleTopology _).map
          ((whiskeringRightTensorRightIso (coefficientModule.{u} φ)).inv.app H.obj ≫
            Functor.whiskerLeft H.obj (extendRestrictScalarsIsoTensorRight.{u} φ).inv) ≫
        (sheafComposeNatTrans X.smallEtaleTopology (ModuleCat.restrictScalars.{max (u + 1) r} φ)
          (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ₂))
          (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ₁))).app
          (H.obj ⋙ ModuleCat.extendScalars.{r, r, max (u + 1) r} φ) := by
  rfl

/-- **The action of `Λ₂` on sections.** On the sectionwise tensor product with the sheafification
unit of the constant presheaf `Λ₂`, the action `res F ⊗_{Λ₁} Λ̲₂ ⟶ res F` is the sectionwise
action. -/
lemma whiskerLeft_toSheafify_tensorSectionMap_coefficientAction (F : EtaleModules.{u, r} Λ₂ X) :
    ((etaleModuleRestrictScalarsUniv.{u, r} φ X).obj F).obj ◁
        toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj (coefficientModule.{u} φ)) ≫
      SheafTensorSections.tensorSectionMap X.smallEtaleTopology
        ((etaleModuleRestrictScalarsUniv.{u, r} φ X).obj F) (coefficientSheaf.{u} φ X) ≫
      ((etaleModuleExtendRestrictScalarsIso.{u, r} φ X).inv.app
          ((etaleModuleRestrictScalarsUniv.{u, r} φ X).obj F) ≫
        (etaleModuleRestrictScalarsUniv.{u, r} φ X).map
          ((etaleModuleExtendRestrictAdj.{u, r} φ X).counit.app F)).hom =
      presheafCoefficientAction.{u} φ F.obj := by
  rw [etaleModuleExtendRestrictScalarsIso_inv_app]
  simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
  rw [SheafTensorSections.whiskerLeft_toSheafify_tensorSectionMap_μ_assoc,
    ← toSheafify_naturality_assoc]
  have h : toSheafify X.smallEtaleTopology
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).obj F).obj ⋙ ModuleCat.extendScalars φ ⋙
          ModuleCat.restrictScalars φ) ≫
      ((sheafComposeNatTrans X.smallEtaleTopology (ModuleCat.restrictScalars.{max (u + 1) r} φ)
          (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ₂))
          (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ₁))).app
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).obj F).obj ⋙ ModuleCat.extendScalars φ)).hom =
      Functor.whiskerRight (toSheafify X.smallEtaleTopology
          (((etaleModuleRestrictScalarsUniv.{u, r} φ X).obj F).obj ⋙ ModuleCat.extendScalars φ))
        (ModuleCat.restrictScalars φ) :=
    sheafComposeNatTrans_fac X.smallEtaleTopology
      (ModuleCat.restrictScalars.{max (u + 1) r} φ)
      (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ₂))
      (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ₁))
      (((etaleModuleRestrictScalarsUniv.{u, r} φ X).obj F).obj ⋙ ModuleCat.extendScalars φ)
  rw [reassoc_of% h]
  have h₂ : toSheafify X.smallEtaleTopology
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).obj F).obj ⋙ ModuleCat.extendScalars φ) ≫
      ((etaleModuleExtendRestrictAdj.{u, r} φ X).counit.app F).hom =
      ((ModuleCat.extendRestrictScalarsAdj.{max (u + 1) r, r, r} φ).whiskerRight
        X.Etaleᵒᵖ).counit.app F.obj := by
    rw [etaleModuleExtendRestrictAdj, Sheaf.adjunction_counit_app_hom]
    exact toSheafify_sheafifyLift _ _ _
  have h₃ : Functor.whiskerRight (toSheafify X.smallEtaleTopology
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).obj F).obj ⋙ ModuleCat.extendScalars φ))
        (ModuleCat.restrictScalars φ) ≫
      Functor.whiskerRight ((etaleModuleExtendRestrictAdj.{u, r} φ X).counit.app F).hom
        (ModuleCat.restrictScalars φ) =
      Functor.whiskerRight
        (((ModuleCat.extendRestrictScalarsAdj.{max (u + 1) r, r, r} φ).whiskerRight
          X.Etaleᵒᵖ).counit.app F.obj) (ModuleCat.restrictScalars φ) :=
    (Functor.whiskerRight_comp _ _ _).symm.trans
      (congrArg (Functor.whiskerRight · (ModuleCat.restrictScalars φ)) h₂)
  rw [sheafCompose_map_hom, Category.assoc]
  exact (congrArg (fun t => _ ≫ _ ≫ t) h₃).trans rfl

end Sheaf

/-- **The projection map intertwines the actions of `Λ₂`.** For a sheaf `F` of `Λ₂`-modules on
`X`, the action of `Λ₂` on `res(g_*F) = g_*(res F)` (the counit of extension of coefficients read
through `res(G ⊗_{Λ₁} Λ₂) ≅ G ⊗_{Λ₁} Λ̲₂`) is the projection map followed by `g_*` of the action
on `F`. -/
theorem etaleModuleConstantProjectionMapApp_coefficientAction {X Y : Scheme.{u}} (g : X ⟶ Y)
    (F : EtaleModules.{u, r} Λ₂ X) :
    (etaleModuleExtendRestrictScalarsIso.{u, r} φ Y).inv.app
        ((etaleModuleRestrictScalarsUniv.{u, r} φ Y).obj
          ((etaleModuleDirectImage.{u, r} Λ₂ g).obj F)) ≫
      (etaleModuleRestrictScalarsUniv.{u, r} φ Y).map
        ((etaleModuleExtendRestrictAdj.{u, r} φ Y).counit.app
          ((etaleModuleDirectImage.{u, r} Λ₂ g).obj F)) =
    etaleModuleConstantProjectionMapApp Λ₁ g ((etaleModuleRestrictScalarsUniv.{u, r} φ X).obj F)
        (coefficientModule.{u} φ) ≫
      (etaleModuleDirectImage.{u, r} Λ₁ g).map
        ((etaleModuleExtendRestrictScalarsIso.{u, r} φ X).inv.app
            ((etaleModuleRestrictScalarsUniv.{u, r} φ X).obj F) ≫
          (etaleModuleRestrictScalarsUniv.{u, r} φ X).map
            ((etaleModuleExtendRestrictAdj.{u, r} φ X).counit.app F)) := by
  let := isMonoidal_W_smallEtale_module.{u, r} Λ₁ X
  let := isMonoidal_W_smallEtale_module.{u, r} Λ₁ Y
  apply SheafTensorSections.tensorSectionMap_hom_ext Y.smallEtaleTopology
  refine (Y.smallEtaleTopology.W.whiskerLeft_mem
    ((etaleModuleRestrictScalarsUniv.{u, r} φ Y).obj
      ((etaleModuleDirectImage.{u, r} Λ₂ g).obj F)).obj _
    (Y.smallEtaleTopology.W_toSheafify ((Functor.const Y.Etaleᵒᵖ).obj (coefficientModule.{u} φ)))
    _ (ObjectProperty.FullSubcategory.property _)).1 ?_
  refine (whiskerLeft_toSheafify_tensorSectionMap_coefficientAction φ Y
    ((etaleModuleDirectImage.{u, r} Λ₂ g).obj F)).trans ?_
  beta_reduce
  refine Eq.trans ?_
    (SheafTensorSections.whiskerLeft_constantToSheafify_tensorSectionMap_constantProjectionMap
    Y.smallEtaleTopology X.smallEtaleTopology (smallEtaleBaseChange g)
    ((etaleModuleRestrictScalarsUniv.{u, r} φ X).obj F) (coefficientModule.{u} φ)
    ((etaleModuleExtendRestrictScalarsIso.{u, r} φ X).inv.app
        ((etaleModuleRestrictScalarsUniv.{u, r} φ X).obj F) ≫
      (etaleModuleRestrictScalarsUniv.{u, r} φ X).map
        ((etaleModuleExtendRestrictAdj.{u, r} φ X).counit.app F))).symm
  refine Eq.trans ?_ (congrArg (Functor.whiskerLeft (smallEtaleBaseChange g).op)
    (whiskerLeft_toSheafify_tensorSectionMap_coefficientAction φ X F)).symm
  rfl

end Stacks.EtaleCohomology

end
