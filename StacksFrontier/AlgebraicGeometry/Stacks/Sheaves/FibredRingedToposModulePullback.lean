module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoextendScalarsComposition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheafFunctoriality

/-!
# Modules along the morphism of ringed topoi of a 1-morphism

For a 1-morphism `F` of categories fibred in groupoids over `(Sch/S)_fppf`, the morphism of
ringed topoi `AlgebraicGeometry.FibredSite.ringedToposMorphism` has an isomorphism on structure
sheaves. We identify its inverse image of sheaves of modules with
`AlgebraicGeometry.Stack.modulePullback` (`pullbackModulesIsoModulePullback`). By uniqueness of
adjoints, its direct image is then `AlgebraicGeometry.Stack.moduleDirectImage`
(`pushforwardModulesIsoModuleDirectImage`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.FibredSite

universe u v w v' w'

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] {Y : Type v'} [Category.{w'} Y]
  (p : X ⥤ BigFppfOver B S hS) (q : Y ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (F : X ⥤ Y) (hF : p.IsFibredOneMorphism q F) (τ : SiteKind)
  [∀ (G : Xᵒᵖ ⥤ Type u), F.op.HasPointwiseRightKanExtension G]

variable [(associatedRingedTopos B S hS p hp τ).J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [(associatedRingedTopos B S hS q hq τ).J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify (associatedRingedTopos B S hS p hp τ).J AddCommGrpCat.{u}]
  [(associatedRingedTopos B S hS p hp τ).J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The ring map `F⁻¹ 𝒪_𝒴 ⟶ 𝒪_𝒳` of the morphism of ringed topoi of a 1-morphism is an
isomorphism. -/
instance isIso_toModulesHom_fSharpInverseImage_ringedToposMorphism :
    IsIso (ringedToposMorphism B S hS p q hp hq F hF τ).toModulesHom.fSharpInverseImage :=
  have := ringedToposMorphism_isIso_fSharpInverseImage B S hS p q hp hq F hF τ
  RingedToposHom.isIso_toModulesHom_fSharpInverseImage _

/-- **Pullback of sheaves of modules along the morphism of ringed topoi of a 1-morphism is the
inverse image of Stacks 06WE**: restriction along the 1-morphism, read over the structure sheaf of
the source through Stacks 06TW. -/
def pullbackModulesIsoModulePullback :
    (ringedToposMorphism B S hS p q hp hq F hF τ).toModulesHom.pullbackModules ≅
      Stack.modulePullback.{u, v, w, u, v', w'} B S hS p q hp hq F hF.comp_eq (B.baseTopology τ)
        (B.baseTopology_le_topology τ) := by
  letI : p.IsFibered := hp.isFibered
  letI : q.IsFibered := hq.isFibered
  letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology τ).over (B.obj hS))).1
  have e1 := Functor.isoWhiskerRight (restrictionModuleIso.{u}
      (BigFppfOver.associatedTopology B S hS p τ) (BigFppfOver.associatedTopology B S hS q τ) F
      (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS q hq τ).O))
    (extendScalarsFSharp (ringedToposMorphism B S hS p q hp hq F hF τ).toModulesHom)
  have e2 := Functor.isoWhiskerLeft (restrictionModules
      (BigFppfOver.associatedTopology B S hS p τ) (BigFppfOver.associatedTopology B S hS q τ) F
      (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS q hq τ).O) ⋙
      SheafOfModules.restrictScalars (restrictionRingIso
      (BigFppfOver.associatedTopology B S hS p τ) (BigFppfOver.associatedTopology B S hS q τ) F
      (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS q hq τ).O)).hom)
    (RingedToposHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso
      (ringedToposMorphism B S hS p q hp hq F hF τ).toModulesHom)
  have hfs0 := RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage
    (ringedToposMorphism B S hS p q hp hq F hF τ)
  rw [ringedToposMorphism_fSharpInverseImage] at hfs0
  obtain ⟨hc, _⟩ := hF
  subst hc
  have hfs : (ringedToposMorphism B S hS (F ⋙ q) q hp hq F ⟨rfl, ‹_›⟩ τ).fSharpInverseImageRing =
      (restrictionRingIso (BigFppfOver.associatedTopology B S hS (F ⋙ q) τ)
        (BigFppfOver.associatedTopology B S hS q τ) F
        (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS q hq τ).O)).hom := by
    rw [← hfs0]
    rfl
  have hb : (asIso (ringedToposMorphism B S hS (F ⋙ q) q hp hq F ⟨rfl, ‹_›⟩
        τ).toModulesHom.fSharpInverseImage).inv =
      (restrictionRingIso (BigFppfOver.associatedTopology B S hS (F ⋙ q) τ)
        (BigFppfOver.associatedTopology B S hS q τ) F
        (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS q hq τ).O)).inv := by
    have h := (restrictionRingIso (BigFppfOver.associatedTopology B S hS (F ⋙ q) τ)
        (BigFppfOver.associatedTopology B S hS q τ) F
        (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS q hq τ).O)).hom_inv_id
    rw [← hfs] at h
    exact (asIso_inv _).trans (IsIso.inv_eq_of_hom_inv_id h)
  rw [hb] at e2
  have e3 := e1 ≪≫ e2 ≪≫ Functor.associator _ _ _
  have fin : restrictionModules.{u} (BigFppfOver.associatedTopology B S hS (F ⋙ q) τ)
      (BigFppfOver.associatedTopology B S hS q τ) F
      (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS q hq τ).O) ≅
      Stack.modulePullback.{u, v, w, u, v', w'} B S hS (F ⋙ q) q hp hq F rfl (B.baseTopology τ)
        (B.baseTopology_le_topology τ) := Iso.refl _
  have mid := Stacks.Sheaves.RingedPoint.sheafRestrictScalarsCompIsoId
    (restrictionRingIso (BigFppfOver.associatedTopology B S hS (F ⋙ q) τ)
      (BigFppfOver.associatedTopology B S hS q τ) F
      (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS q hq τ).O)).hom
    (restrictionRingIso (BigFppfOver.associatedTopology B S hS (F ⋙ q) τ)
      (BigFppfOver.associatedTopology B S hS q τ) F
      (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS q hq τ).O)).inv
    (Iso.inv_hom_id _)
  exact e3 ≪≫ Functor.isoWhiskerLeft _ mid ≪≫ Functor.rightUnitor _ ≪≫ fin

variable [∀ G : Xᵒᵖ ⥤ RingCat.{u}, F.op.HasPointwiseRightKanExtension G]
  [∀ G : Xᵒᵖ ⥤ AddCommGrpCat.{u}, F.op.HasPointwiseRightKanExtension G]

/-- **The direct image of sheaves of modules along the morphism of ringed topoi of a 1-morphism is
the canonical direct image** `AlgebraicGeometry.Stack.moduleDirectImage`: both are right adjoint
to the same inverse image, by `pullbackModulesIsoModulePullback`. -/
def pushforwardModulesIsoModuleDirectImage :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
      ((B.baseTopology τ).over (B.obj hS))).2
    RingedToposHom.pushforwardModules (ringedToposMorphism B S hS p q hp hq F hF τ) ≅
      Stack.moduleDirectImage.{u, v, w, v', w', u} B S hS p q hp hq F hF.comp_eq (B.baseTopology τ)
        (B.baseTopology_le_topology τ) :=
  letI : p.IsFibered := hp.isFibered
  letI : q.IsFibered := hq.isFibered
  letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology τ).over (B.obj hS))).2
  ((RingedToposHom.pullbackAdjPushforwardModules
      (ringedToposMorphism B S hS p q hp hq F hF τ)).ofNatIsoLeft
    (pullbackModulesIsoModulePullback B S hS p q hp hq F hF τ)).rightAdjointUniq
    (Stack.moduleDirectImageAdjunction.{u, v, w, v', w', u} B S hS p q hp hq F hF.comp_eq
      (B.baseTopology τ) (B.baseTopology_le_topology τ))

end AlgebraicGeometry.FibredSite
