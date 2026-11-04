module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.DerivedBaseChange
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FlatBaseChangeOfSimplicialModules
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCoefficientChange

/-!
# Base change of free simplicial modules

For a presheaf of sets `S` on `Δ × C`, the free simplicial `A_•`-module `A_•⟨S⟩` is the
sheafification of the free presheaf of modules on `S`. Its underlying abelian sheaf is the
sheafification of the copower `A_• ⊗ S`, and the unit `A_•⟨S⟩ ⟶ A_•⟨S⟩ ⊗_{A_•} B_•` of base change
along `A_• ⟶ B_•` is, on underlying abelian sheaves, the sheafification of the copower by `S` of
`A_• ⟶ B_•`.

## Main definitions

* `Stacks.SimplicialModules.freeModule`: `S ↦ A_•⟨S⟩`.
* `Stacks.SimplicialModules.unitPresheaf`, `unitPresheafMap`: `A_•` and `A_• ⟶ B_•` as abelian
  presheaves on `Δ × C`.

## Main results

* `Stacks.SimplicialModules.baseChangeUnit_freeModule_arrowIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.SimplicialModules

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- **The free simplicial module** `A_•⟨S⟩` on a presheaf of sets `S` on `Δ × C`. -/
abbrev freeModule (A : SimplicialObject (Sheaf J CommRingCat.{u})) :
    ((SimplexCategory × C)ᵒᵖ ⥤ Type u) ⥤ Modules J A :=
  PresheafOfModules.free.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J A)).obj ⋙
    PresheafOfModules.sheafification.{u}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J A)).obj)

/-- `A_•` as an abelian presheaf on `Δ × C`. -/
abbrev unitPresheaf (A : SimplicialObject (Sheaf J CommRingCat.{u})) :
    (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (commRingSheaf J A).obj ⋙ forgetToAddCommGrp

variable {A B : SimplicialObject (Sheaf J CommRingCat.{u})} (φ : A ⟶ B)

/-- `A_• ⟶ B_•` as a morphism of abelian presheaves on `Δ × C`. -/
abbrev unitPresheafMap : unitPresheaf J A ⟶ unitPresheaf J B :=
  Functor.whiskerRight (commRingSheafMap J φ).hom forgetToAddCommGrp

/-- The underlying morphism of abelian presheaves of `ringAbelianSheafMap J φ` is
`unitPresheafMap J φ`. -/
theorem ringAbelianSheafMap_hom : (ringAbelianSheafMap J φ).hom = unitPresheafMap J φ :=
  rfl

/-- The underlying presheaf of sets of a simplicial module, the right adjoint of `freeModule`. -/
abbrev freeModuleRightAdjoint (A : SimplicialObject (Sheaf J CommRingCat.{u})) :
    Modules J A ⥤ ((SimplexCategory × C)ᵒᵖ ⥤ Type u) :=
  (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)) ⋙
    (PresheafOfModules.toPresheaf _ ⋙ (Functor.whiskeringRight _ _ _).obj (forget Ab))

/-- `freeModule ⊣ freeModuleRightAdjoint`. -/
def freeModuleAdjunction (A : SimplicialObject (Sheaf J CommRingCat.{u})) :
    freeModule J A ⊣ freeModuleRightAdjoint J A :=
  (PresheafOfModules.freeAdjunction _).comp (PresheafOfModules.sheafificationAdjunction _)

/-- Restriction of scalars does not change the underlying presheaf of sets. -/
def restrictScalarsCompFreeModuleRightAdjointIso :
    restrictScalars J φ ⋙ freeModuleRightAdjoint J A ≅ freeModuleRightAdjoint J B :=
  Iso.refl _

/-- **Base change of a free simplicial module is free**: `A_•⟨S⟩ ⊗_{A_•} B_• ≅ B_•⟨S⟩`, both
being left adjoint to the underlying presheaf of sets. -/
def baseChangeFreeModuleIso : freeModule J A ⋙ baseChange J φ ≅ freeModule J B :=
  Adjunction.leftAdjointUniq
    (((freeModuleAdjunction J A).comp (baseChangeAdjunction J φ)).ofNatIsoRight
      (restrictScalarsCompFreeModuleRightAdjointIso J φ)) (freeModuleAdjunction J B)

/-- The `A_•`-linear map `A_•⟨S⟩ ⟶ B_•⟨S⟩` obtained from the base change unit and
`baseChangeFreeModuleIso` is adjoint to the unit `S ⟶ B_•⟨S⟩` of `freeModuleAdjunction J B`. -/
lemma freeModuleAdjunction_unit_baseChangeFreeModuleIso
    (S : (SimplexCategory × C)ᵒᵖ ⥤ Type u) :
    (freeModuleAdjunction J A).unit.app S ≫ (freeModuleRightAdjoint J A).map
      ((baseChangeAdjunction J φ).unit.app ((freeModule J A).obj S) ≫
        (restrictScalars J φ).map ((baseChangeFreeModuleIso J φ).hom.app S)) =
      (freeModuleAdjunction J B).unit.app S := by
  rw [← Adjunction.unit_leftAdjointUniq_hom_app
    (((freeModuleAdjunction J A).comp (baseChangeAdjunction J φ)).ofNatIsoRight
      (restrictScalarsCompFreeModuleRightAdjointIso J φ)) (freeModuleAdjunction J B) S]
  simp only [restrictScalarsCompFreeModuleRightAdjointIso, Functor.map_comp]
  rfl

/-- `A_• ⟶ B_•` as a morphism of presheaves of rings on `Δ × C`. -/
abbrev ringPresheafMap : (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J A)).obj ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J B)).obj :=
  Functor.whiskerRight (commRingSheafMap J φ).hom (forget₂ CommRingCat RingCat)

/-- The `A_•`-linear map of free presheaves of modules `A_•⟨S⟩ ⟶ B_•⟨S⟩` sending each generator
to the corresponding generator. -/
def freeRestrictMap (S : (SimplexCategory × C)ᵒᵖ ⥤ Type u) :
    (PresheafOfModules.free (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J A)).obj).obj
        S ⟶
      (PresheafOfModules.restrictScalars (ringPresheafMap J φ)).obj
        ((PresheafOfModules.free
          (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J B)).obj).obj S) :=
  PresheafOfModules.freeObjDesc (PresheafOfModules.freeAdjunctionUnit _ S)

/-- `freeRestrictMap` sends the function supported at `s` with value `r` to the function
supported at `s` with value the image of `r` in `B_•`. -/
lemma freeRestrictMap_app_single (S : (SimplexCategory × C)ᵒᵖ ⥤ Type u)
    (X : (SimplexCategory × C)ᵒᵖ) (s : S.obj X)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J A)).obj.obj X) :
    ((freeRestrictMap J φ S).app X).hom
        (Finsupp.single s r : ((PresheafOfModules.free
          (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J A)).obj).obj S).obj X) =
      (Finsupp.single s (((ringPresheafMap J φ).app X).hom r) : ((PresheafOfModules.free
          (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J B)).obj).obj S).obj X) := by
  have e : ∀ {R : (SimplexCategory × C)ᵒᵖ ⥤ RingCat.{u}} (r : R.obj X),
      (Finsupp.single s r : ((PresheafOfModules.free R).obj S).obj X) =
        r • ModuleCat.freeMk (R := R.obj X) s := fun {R} r => by
    change (Finsupp.single s r : S.obj X →₀ R.obj X) = r • Finsupp.single s (1 : R.obj X)
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [e, e]
  exact (((freeRestrictMap J φ S).app X).hom.map_smul r _).trans
    (congrArg (r • ·) (ModuleCat.freeDesc_apply _ s))

/-- Under `Stacks.ChaoticSite.freeCopowerIso`, `freeRestrictMap` is the copower by `S` of
`A_• ⟶ B_•` on underlying abelian presheaves. -/
lemma freeCopowerIso_hom_toPresheaf_map_freeRestrictMap
    (S : (SimplexCategory × C)ᵒᵖ ⥤ Type u) :
    (Stacks.ChaoticSite.freeCopowerIso
        (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J A)).obj S).hom ≫
        (PresheafOfModules.toPresheaf _).map (freeRestrictMap J φ S) =
      Functor.copowerMap (unitPresheafMap J φ) (𝟙 S) ≫
        (Stacks.ChaoticSite.freeCopowerIso
          (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J B)).obj S).hom := by
  apply NatTrans.ext
  funext X
  apply Sigma.hom_ext
  intro s
  rw [NatTrans.comp_app]
  refine (Stacks.ChaoticSite.ι_freeCopowerIsoApp_hom_assoc
    (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J A)).obj S X s _).trans
      (Eq.trans ?_ (Functor.ι_copowerMap_app_assoc (unitPresheafMap J φ) (𝟙 S) X s
        ((Stacks.ChaoticSite.freeCopowerIso
          (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J B)).obj S).hom.app X)).symm)
  refine Eq.trans ?_ (congrArg ((unitPresheafMap J φ).app X ≫ ·)
    (Stacks.ChaoticSite.ι_freeCopowerIsoApp_hom
      (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J B)).obj S X s).symm)
  ext r
  exact freeRestrictMap_app_single J φ S X s r

/-- On presheaves of modules, the map `A_•⟨S⟩ ⟶ B_•⟨S⟩` obtained from the base change unit is
`freeRestrictMap` followed by the sheafification unit of `B_•⟨S⟩`; both are checked on
generators. -/
lemma sheafificationUnit_comp_baseChangeFreeModuleMap (S : (SimplexCategory × C)ᵒᵖ ⥤ Type u) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
        ((PresheafOfModules.free
          (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J A)).obj).obj S) ≫
      (PresheafOfModules.restrictScalars (𝟙 _)).map ((SheafOfModules.forget _).map
        ((baseChangeAdjunction J φ).unit.app ((freeModule J A).obj S) ≫
          (restrictScalars J φ).map ((baseChangeFreeModuleIso J φ).hom.app S))) =
    freeRestrictMap J φ S ≫ (PresheafOfModules.restrictScalars (ringPresheafMap J φ)).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
        ((PresheafOfModules.free
          (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J B)).obj).obj S)) := by
  have hu := freeModuleAdjunction_unit_baseChangeFreeModuleIso J φ S
  simp only [freeModuleAdjunction, Adjunction.comp_unit_app,
    PresheafOfModules.freeAdjunction_unit_app, Functor.map_comp, Functor.comp_map,
    Functor.whiskeringRight_obj_map] at hu
  have hf : PresheafOfModules.freeAdjunctionUnit _ S ≫ Functor.whiskerRight
      ((PresheafOfModules.toPresheaf _).map (freeRestrictMap J φ S)) (forget Ab) =
      PresheafOfModules.freeAdjunctionUnit
        (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J B)).obj S :=
    PresheafOfModules.freeHomEquiv.apply_symm_apply _
  apply PresheafOfModules.free_hom_ext
  simp only [Functor.map_comp, Functor.whiskerRight_comp] at hu ⊢
  refine hu.trans ?_
  have h1 : Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map
      (freeRestrictMap J φ S ≫ (PresheafOfModules.restrictScalars (ringPresheafMap J φ)).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
          ((PresheafOfModules.free
            (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J B)).obj).obj S))))
        (forget Ab) =
      Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map (freeRestrictMap J φ S))
          (forget Ab) ≫
        Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map
          ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
            ((PresheafOfModules.free
              (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J B)).obj).obj S)))
          (forget Ab) := by
    rw [Functor.map_comp, Functor.whiskerRight_comp]
    rfl
  exact (congrArg (fun t => t ≫ Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
        ((PresheafOfModules.free
          (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J B)).obj).obj S))) (forget Ab))
      hf.symm).trans
    ((Category.assoc _ _ _).trans (congrArg (fun t => PresheafOfModules.freeAdjunctionUnit
      (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J A)).obj S ≫ t) h1.symm))

/-- On underlying abelian sheaves, the map `A_•⟨S⟩ ⟶ B_•⟨S⟩` obtained from the base change unit
is the sheafification of `freeRestrictMap`. -/
lemma toAbelian_map_baseChangeFreeModuleMap (S : (SimplexCategory × C)ᵒᵖ ⥤ Type u) :
    (toAbelian J A).map ((baseChangeAdjunction J φ).unit.app ((freeModule J A).obj S) ≫
        (restrictScalars J φ).map ((baseChangeFreeModuleIso J φ).hom.app S)) =
      (presheafToSheaf (simplicialProjectionTopology J) AddCommGrpCat.{u}).map
        ((PresheafOfModules.toPresheaf _).map (freeRestrictMap J φ S)) := by
  apply ((sheafificationAdjunction _ _).homEquiv _ _).injective
  refine (Adjunction.homEquiv_unit _ _ _ _).trans
    (Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm)
  have h := congrArg (PresheafOfModules.toPresheaf _).map
    (sheafificationUnit_comp_baseChangeFreeModuleMap J φ S)
  simp only [Functor.map_comp] at h
  refine h.trans ((Functor.map_comp _ _ _).trans ?_)
  exact (sheafificationAdjunction
      (simplicialProjectionTopology J) AddCommGrpCat.{u}).unit.naturality _

/-- **The base change unit at a free simplicial module, on underlying abelian sheaves**, is the
sheafification of the copower by `S` of `A_• ⟶ B_•`. -/
theorem baseChangeUnit_freeModule_arrowIso (S : (SimplexCategory × C)ᵒᵖ ⥤ Type u) :
    Nonempty (Arrow.mk ((toAbelian J A).map
        ((baseChangeAdjunction J φ).unit.app ((freeModule J A).obj S))) ≅
      Arrow.mk ((presheafToSheaf (simplicialProjectionTopology J) AddCommGrpCat.{u}).map
        (Functor.copowerMap (unitPresheafMap J φ) (𝟙 S)))) := by
  refine ⟨Arrow.isoMk
    ((presheafToSheaf (simplicialProjectionTopology J) AddCommGrpCat.{u}).mapIso
      (Stacks.ChaoticSite.freeCopowerIso _ S).symm)
    ((toAbelian J B).mapIso ((baseChangeFreeModuleIso J φ).app S) ≪≫
      (presheafToSheaf (simplicialProjectionTopology J) AddCommGrpCat.{u}).mapIso
        (Stacks.ChaoticSite.freeCopowerIso _ S).symm) ?_⟩
  have key := toAbelian_map_baseChangeFreeModuleMap J φ S
  rw [Functor.map_comp] at key
  change (presheafToSheaf (simplicialProjectionTopology J) AddCommGrpCat.{u}).map
      (Stacks.ChaoticSite.freeCopowerIso
        (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J A)).obj S).inv ≫
      (presheafToSheaf (simplicialProjectionTopology J) AddCommGrpCat.{u}).map
        (Functor.copowerMap (unitPresheafMap J φ) (𝟙 S)) =
    ((toAbelian J A).map ((baseChangeAdjunction J φ).unit.app ((freeModule J A).obj S)) ≫
      (toAbelian J A).map ((restrictScalars J φ).map ((baseChangeFreeModuleIso J φ).hom.app S))) ≫
      (presheafToSheaf (simplicialProjectionTopology J) AddCommGrpCat.{u}).map
        (Stacks.ChaoticSite.freeCopowerIso
          (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J B)).obj S).inv
  rw [key]
  have h3 : (Stacks.ChaoticSite.freeCopowerIso
        (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J A)).obj S).inv ≫
      Functor.copowerMap (unitPresheafMap J φ) (𝟙 S) =
      (PresheafOfModules.toPresheaf _).map (freeRestrictMap J φ S) ≫
        (Stacks.ChaoticSite.freeCopowerIso
          (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J B)).obj S).inv :=
    ((Iso.comp_inv_eq _).2 (((Iso.eq_inv_comp _).2
      (freeCopowerIso_hom_toPresheaf_map_freeRestrictMap J φ S)).trans
        (Category.assoc _ _ _).symm)).symm
  rw [← Functor.map_comp, h3]
  exact Functor.map_comp _ _ _

end Stacks.SimplicialModules
