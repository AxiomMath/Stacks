module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsBaseChangeData
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsThickeningSequence

public import StacksFrontier.Deformation.Artin.Obstruction.SectionsTensorBaseChange.CartesianSquare
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsTensorBaseChange.ProjectionFormula

/-!
# The direct image to `W` of `𝓕_A ⊗_A M`: change of base

Sections of `𝓕_A`, read on `W`, and their restriction maps
(`pushforward_reductionMapGen_comp_tensorBaseChangeUnitIsoGen`); the compatibility with the
thickening identification (`tensorBaseChangeIsoGen_thickening`); and the instance at the fibre
product `W_A = Spec A ×_{Spec Λ} W` (`tensorBaseChangeIso`, `tensorBaseChangeSection`).

See `StacksFrontier.Deformation.Artin.Obstruction.SectionsTensorBaseChange` for the overview.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Prod TensorProduct

universe u

namespace Deformation.Artin.SectionsSheaf

/-! ### Sections of `𝓕_A`, read on `W`, and change of base -/

section DegreeZero

open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.AlgebraicGeometry.AffineBaseChange

variable {Λ A : CommRingCat.{u}} (φ : Λ ⟶ A) {W X : Scheme.{u}} {g : W ⟶ Spec Λ}
  {π : X ⟶ Spec A} {p : X ⟶ W} (h : IsPullback π p (Spec.map φ) g) (F : W.Modules)
  [F.IsQuasicoherent]

/-- **`p_* 𝓕_A ≅ 𝓕 ⊗_Λ A`** at a cartesian square over `Spec φ`: `tensorBaseChangeIsoGen` at
`M = A`, after `𝓕_A ≅ 𝓕_A ⊗_A A`. On global sections it reads a section of `𝓕_A` on `X` as a
section of `𝓕 ⊗_Λ A` on `W`. -/
def tensorBaseChangeUnitIsoGen :
    (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj F) ≅
      (tensorSheafFunctor g F).obj ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of A A)) :=
  (Scheme.Modules.pushforward p).mapIso
      (tensorSheafFunctorObjSelf π ((Scheme.Modules.pullback p).obj F)).symm ≪≫
    tensorBaseChangeIsoGen φ h F (ModuleCat.of A A)

/-- `tensorBaseChangeUnitIsoGen` on `inv`, as the composite of the arrows it is built from. -/
theorem tensorBaseChangeUnitIsoGen_inv :
    (tensorBaseChangeUnitIsoGen φ h F).inv =
      (eqToHom (tensorSheafFunctor_obj_eq g F
          ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of A A))) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))).map
          ((tensorBaseChangeFirstIso φ h (ModuleCat.of A A)).hom ×ₘ 𝟙 F) ≫
        (projectionFormulaIsoOfIsPullback φ h F
          ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj (ModuleCat.of A A)))
          (isQuasicoherent_pullback π _)).hom ≫
        (Scheme.Modules.pushforward p).map
          (eqToHom (tensorSheafFunctor_obj_eq π ((Scheme.Modules.pullback p).obj F)
            (ModuleCat.of A A)).symm)) ≫
      (Scheme.Modules.pushforward p).map
        (tensorSheafFunctorObjSelf π ((Scheme.Modules.pullback p).obj F)).hom :=
  rfl

/-- The projection-formula map along `p` is natural in the first factor `G`. -/
private theorem tensorSheaf_map_pushforward_comp_adjunctionTensorMap {X W : Scheme.{u}}
    (p : X ⟶ W) (F : W.Modules) {G G' : X.Modules} (ι : G ⟶ G') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
        ((Scheme.Modules.pushforward p).map ι ×ₘ 𝟙 F) ≫
      adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction p)
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))
        (comparisonNatTrans p.toLRSHom.toShHom) G' F =
    adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction p)
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))
        (comparisonNatTrans p.toLRSHom.toShHom) G F ≫
      (Scheme.Modules.pushforward p).map
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
          (ι ×ₘ 𝟙 ((Scheme.Modules.pullback p).obj F))) := by
  have e := adjunctionTensorMap_natural (Scheme.Modules.pullbackPushforwardAdjunction p)
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))
    (comparisonNatTrans p.toLRSHom.toShHom) ι (𝟙 F)
  rwa [CategoryTheory.Functor.map_id] at e

/-- The projection formula along `p` is natural along `π^* Ã ≅ 𝒪_X`. -/
theorem projectionFormulaIsoOfIsPullback_hom_pullbackUnitIso :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
        ((Scheme.Modules.pushforward p).map (pullbackUnitIso π).hom ×ₘ 𝟙 F) ≫
      adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction p)
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))
        (comparisonNatTrans p.toLRSHom.toShHom) (unitObj X) F =
    (projectionFormulaIsoOfIsPullback φ h F
        ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj (ModuleCat.of A A)))
        (isQuasicoherent_pullback π _)).hom ≫
      (Scheme.Modules.pushforward p).map
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
          ((pullbackUnitIso π).hom ×ₘ 𝟙 ((Scheme.Modules.pullback p).obj F))) := by
  rw [projectionFormulaIsoOfIsPullback_hom]
  exact tensorSheaf_map_pushforward_comp_adjunctionTensorMap p F _

variable {A' : CommRingCat.{u}} (ψ : A ⟶ A') {X' : Scheme.{u}} {π' : X' ⟶ Spec A'}
  (β : X' ⟶ X) (h' : IsPullback π' (β ≫ p) (Spec.map (φ ≫ ψ)) g)
  (hβπ : β ≫ π = π' ≫ Spec.map ψ)

omit [F.IsQuasicoherent] in
include hβπ in
/-- `firstFactor_unitObj_naturality` in the spelling of `tensorBaseChangeFirstIso`. -/
theorem tensorBaseChangeFirstIso_unitObj_naturality :
    (Scheme.Modules.pullback g).map
        ((tilde.functor Λ).map (restrictScalarsHomOfComp (φ := φ) ψ rfl)) ≫
        ((tensorBaseChangeFirstIso (φ ≫ ψ) h' (ModuleCat.of A' A')).hom ≫
          (Scheme.Modules.pushforward (β ≫ p)).map (pullbackUnitIso π').hom) =
      ((tensorBaseChangeFirstIso φ h (ModuleCat.of A A)).hom ≫
          (Scheme.Modules.pushforward p).map (pullbackUnitIso π).hom) ≫
        (Scheme.Modules.pushforward p).map (structureUnitHom β) :=
  (congrArg (fun z => (Scheme.Modules.pullback g).map
      ((tilde.functor Λ).map (restrictScalarsHomOfComp (φ := φ) ψ rfl)) ≫ z)
    (Category.assoc ((Scheme.Modules.pullback g).map
        (tildePushforwardIso (φ ≫ ψ) (ModuleCat.of A' A')).inv)
      ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans h'.w).app
        ((tilde.functor A').obj (ModuleCat.of A' A')))
      ((Scheme.Modules.pushforward (β ≫ p)).map (pullbackUnitIso π').hom))).trans
    ((firstFactor_unitObj_naturality φ ψ β h.w h'.w hβπ
        (restrictScalarsHomOfComp (φ := φ) ψ rfl) fun _ => rfl).trans
      (congrArg (fun z => z ≫ (Scheme.Modules.pushforward p).map (structureUnitHom β))
        (Category.assoc ((Scheme.Modules.pullback g).map
            (tildePushforwardIso φ (ModuleCat.of A A)).inv)
          ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans h.w).app
            ((tilde.functor A).obj (ModuleCat.of A A)))
          ((Scheme.Modules.pushforward p).map (pullbackUnitIso π).hom)).symm))

/-- `tensorBaseChangeUnitIsoGen` on `inv`, contracted: the first tensor factor followed by
`π^* Ã ≅ 𝒪_X`, the projection-formula map along `p` at the structure sheaf, and the left unitor. -/
theorem tensorBaseChangeUnitIsoGen_inv_eq :
    (tensorBaseChangeUnitIsoGen φ h F).inv =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
          (((tensorBaseChangeFirstIso φ h (ModuleCat.of A A)).hom ≫
            (Scheme.Modules.pushforward p).map (pullbackUnitIso π).hom) ×ₘ 𝟙 F) ≫
        adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction p)
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))
          (comparisonNatTrans p.toLRSHom.toShHom) (unitObj X) F ≫
        (Scheme.Modules.pushforward p).map
          (tensorSheafUnitLeftIso X.toRingedSpace ((Scheme.Modules.pullback p).obj F)).hom :=
  tensorChain_contract (Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))
    (Scheme.Modules.pushforward p) _ _ _ _ _ _ _ (eqToHom_refl _ _) (eqToHom_refl _ _) _ _
    (tensorBaseChangeUnitIsoGen_inv φ h F)
    (tensorSheafFunctorObjSelf_hom π ((Scheme.Modules.pullback p).obj F))
    (projectionFormulaIsoOfIsPullback_hom_pullbackUnitIso φ h F)

include hβπ in
/-- **Change of base in degree zero, on `W`, in the bifunctor spelling.** -/
theorem tensorSheaf_map_comp_tensorBaseChangeUnitIsoGen_inv :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map ((Scheme.Modules.pullback g).map
        ((tilde.functor Λ).map (restrictScalarsHomOfComp (φ := φ) ψ rfl)) ×ₘ 𝟙 F) ≫
        (tensorBaseChangeUnitIsoGen (φ ≫ ψ) h' F).inv =
      (tensorBaseChangeUnitIsoGen φ h F).inv ≫
        (Scheme.Modules.pushforward p).map (reductionMapGen p (β ≫ p) F β rfl) :=
  tensorChain_change (Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩))
    (Scheme.Modules.pushforward p) (Scheme.Modules.pushforward (β ≫ p))
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)) _ _ _ _ _ _ _ _ _ _ _
    (tensorBaseChangeUnitIsoGen_inv_eq φ h F)
    (tensorBaseChangeUnitIsoGen_inv_eq (φ ≫ ψ) h' F)
    (tensorBaseChangeFirstIso_unitObj_naturality φ h ψ β h' hβπ)
    (adjunctionTensorMap_unitObj_comp_reductionMapGen p β F)

include hβπ in
/-- **Change of base in degree zero, on `W`.** For a ring map `ψ : A → A'` and a morphism
`β : X' → X` over `W` and over `Spec ψ`, the canonical reduction `𝓕_A ⟶ β_* 𝓕_{A'}`, read on `W`
through `tensorBaseChangeUnitIsoGen`, is the map `𝓕 ⊗_Λ A ⟶ 𝓕 ⊗_Λ A'` induced by `ψ`. -/
theorem pushforward_reductionMapGen_comp_tensorBaseChangeUnitIsoGen :
    (Scheme.Modules.pushforward p).map (reductionMapGen p (β ≫ p) F β rfl) ≫
        (tensorBaseChangeUnitIsoGen (φ ≫ ψ) h' F).hom =
      (tensorBaseChangeUnitIsoGen φ h F).hom ≫
        (tensorSheafFunctor g F).map (restrictScalarsHomOfComp (φ := φ) ψ rfl) := by
  have hbase : (tensorSheafFunctor g F).map (restrictScalarsHomOfComp (φ := φ) ψ rfl) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
        ((Scheme.Modules.pullback g).map
          ((tilde.functor Λ).map (restrictScalarsHomOfComp (φ := φ) ψ rfl)) ×ₘ 𝟙 F) :=
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩
      ((Scheme.Modules.pullback g).map
        ((tilde.functor Λ).map (restrictScalarsHomOfComp (φ := φ) ψ rfl))) (𝟙 F)).symm
  rw [hbase]
  exact hom_naturality_of_inv_naturality _ _ _ _
    (tensorSheaf_map_comp_tensorBaseChangeUnitIsoGen_inv φ h F ψ β h' hβπ)

/-- A presheaf on a thin category sends an endomorphism of an object to the identity. -/
private theorem presheaf_map_eq_id {C D : Type*} [Category C] [Category D] (P : Cᵒᵖ ⥤ D) {U : C}
    [Subsingleton (op U ⟶ op U)] (f : op U ⟶ op U) : P.map f = 𝟙 _ :=
  (P.congr_map (Subsingleton.elim _ (𝟙 _))).trans (P.map_id _)

/-- Restricting sections from `β⁻¹ ⊤` to `⊤` is the identity, the two opens being equal. -/
theorem presheaf_map_eqToHom_top_apply {X' X : Scheme.{u}} (β : X' ⟶ X) (K : X'.Modules)
    (z : Γ(K, β ⁻¹ᵁ ⊤)) :
    (Scheme.Modules.presheaf K).map
        (eqToHom (show (⊤ : X'.Opens) = β ⁻¹ᵁ ⊤ by simp)).op z = z :=
  congrArg (fun φ : K.presheaf.obj (op ⊤) ⟶ K.presheaf.obj (op ⊤) => φ z)
    (presheaf_map_eq_id K.presheaf _)

/-- An equation of composites of morphisms of modules, on sections. -/
theorem modulesHom_app_app_eq_of_comp_eq {Y : Scheme.{u}} {M N N' K : Y.Modules}
    {f : M ⟶ N} {k : N ⟶ K} {f' : M ⟶ N'} {k' : N' ⟶ K} (e : f ≫ k = f' ≫ k') (U : Y.Opens)
    (z : Γ(M, U)) :
    Scheme.Modules.Hom.app k U (Scheme.Modules.Hom.app f U z) =
      Scheme.Modules.Hom.app k' U (Scheme.Modules.Hom.app f' U z) :=
  congrArg (fun q : M ⟶ K => Scheme.Modules.Hom.app q U z) e

include hβπ in
/-- **Change of base in degree zero, on global sections.** Under `tensorBaseChangeUnitIsoGen`,
the pullback of a section of `𝓕_A` along `β : X' → X` — the canonical reduction on global
sections, followed by the restriction from `β⁻¹ ⊤` to `⊤` — is the map on global sections of
`𝓕 ⊗_Λ A ⟶ 𝓕 ⊗_Λ A'` induced by `ψ`. -/
theorem tensorBaseChangeUnitIsoGen_hom_app_restriction {φ' : Λ ⟶ A'} (hψ : φ ≫ ψ = φ')
    {p' : X' ⟶ W} (h'' : IsPullback π' p' (Spec.map φ') g) (hβp : β ≫ p = p')
    (x : Γ((Scheme.Modules.pullback p).obj F, ⊤)) :
    Scheme.Modules.Hom.app (tensorBaseChangeUnitIsoGen φ' h'' F).hom ⊤
        ((Scheme.Modules.presheaf ((Scheme.Modules.pullback p').obj F)).map
          (eqToHom (show (⊤ : X'.Opens) = β ⁻¹ᵁ ⊤ by simp)).op
          (Scheme.Modules.Hom.app (reductionMapGen p p' F β hβp) ⊤ x)) =
      Scheme.Modules.Hom.app ((tensorSheafFunctor g F).map (restrictScalarsHomOfComp ψ hψ)) ⊤
        (Scheme.Modules.Hom.app (tensorBaseChangeUnitIsoGen φ h F).hom ⊤ x) := by
  subst hβp hψ
  refine (congrArg (fun z : Γ((Scheme.Modules.pullback (β ≫ p)).obj F, ⊤) =>
      Scheme.Modules.Hom.app (tensorBaseChangeUnitIsoGen (φ ≫ ψ) h'' F).hom ⊤ z)
    (presheaf_map_eqToHom_top_apply β _ _)).trans ?_
  exact modulesHom_app_app_eq_of_comp_eq
    (pushforward_reductionMapGen_comp_tensorBaseChangeUnitIsoGen φ h F ψ β h'' hβπ) ⊤ x

end DegreeZero

/-! ### Compatibility with the thickening identification -/

section Thickening

open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.AlgebraicGeometry.AffineBaseChange

variable {Λ A' A : CommRingCat.{u}} (φ₀ : Λ ⟶ A') (φ : A' ⟶ A) {W X' X : Scheme.{u}}
  {g : W ⟶ Spec Λ} {π' : X' ⟶ Spec A'} {p : X' ⟶ W} (h : IsPullback π' p (Spec.map φ₀) g)
  {π : X ⟶ Spec A} {i : X ⟶ X'} (hsq : IsPullback π i (Spec.map φ) π')
  (F : W.Modules) [F.IsQuasicoherent]

/-- The projection-formula isomorphism of a closed immersion is the abstract
`CategoryTheory.adjunctionTensorMap` of `i^* ⊣ i_*`. -/
theorem projectionFormulaIsoGen_hom_eq [IsClosedImmersion i] (F' : X'.Modules) (G : X.Modules) :
    (projectionFormulaIsoGen i F' G).hom =
      adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction i)
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩))
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))
        (comparisonNatTrans i.toLRSHom.toShHom) G F' :=
  (Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso_hom i G F').trans
    ((Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_eq i G F').symm.trans
      (adjunctionTensorMap_eq_projectionFormulaMap i F' G).symm)

/-- The projection formula along `p` is natural along the first tensor factor of `i`. -/
theorem projectionFormulaIsoOfIsPullback_hom_naturality_firstFactor (M : ModuleCat.{u} A) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
    ((Scheme.Modules.pushforward p).map
        ((Scheme.Modules.pullback π').map (tildePushforwardIso φ M).inv ≫
          (affineBaseChangeIsoGen φ π' π i hsq ((tilde.functor A).obj M)).hom) ×ₘ 𝟙 F) ≫
      adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction p)
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩))
        (comparisonNatTrans p.toLRSHom.toShHom)
        ((Scheme.Modules.pushforward i).obj
          ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj M))) F =
    (projectionFormulaIsoOfIsPullback φ₀ h F
        ((Scheme.Modules.pullback π').obj
          ((tilde.functor A').obj ((ModuleCat.restrictScalars φ.hom).obj M)))
        (isQuasicoherent_pullback π' _)).hom ≫
      (Scheme.Modules.pushforward p).map
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩)).map
        (((Scheme.Modules.pullback π').map (tildePushforwardIso φ M).inv ≫
          (affineBaseChangeIsoGen φ π' π i hsq ((tilde.functor A).obj M)).hom) ×ₘ
            𝟙 ((Scheme.Modules.pullback p).obj F))) := by
  rw [projectionFormulaIsoOfIsPullback_hom]
  exact tensorSheaf_map_pushforward_comp_adjunctionTensorMap p F _

/-- **Thickening coherence at a cartesian square, on `inv`.** -/
theorem tensorBaseChangeIsoGen_comp_inv [IsClosedImmersion i]
    (h' : IsPullback π (i ≫ p) (Spec.map (φ₀ ≫ φ)) g) (M : ModuleCat.{u} A) :
    (tensorSheafFunctor g F).map
        (ModuleCat.restrictScalarsComp'App φ₀.hom φ.hom (φ₀ ≫ φ).hom rfl M).inv ≫
        (tensorBaseChangeIsoGen (φ₀ ≫ φ) h' F M).inv =
      (tensorBaseChangeIsoGen φ₀ h F ((ModuleCat.restrictScalars φ.hom).obj M)).inv ≫
        (Scheme.Modules.pushforward p).map
          (pushforwardTensorSheafIsoGen φ π' π i hsq ((Scheme.Modules.pullback p).obj F)
            ((Scheme.Modules.pullback (i ≫ p)).obj F) (baseChangeSheafIsoGen p (i ≫ p) F i rfl)
            M).hom ≫
        (Scheme.Modules.pushforwardComp i p).hom.app
          ((tensorSheafFunctor π ((Scheme.Modules.pullback (i ≫ p)).obj F)).obj M) :=
  tensorChain_thickening (Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩))
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)) (Scheme.Modules.pushforward p)
    (Scheme.Modules.pushforward i)
    (Scheme.Modules.pushforward (i ≫ p)) (Scheme.Modules.pushforwardComp i p).hom
    (G₀ := (Scheme.Modules.pullback π).obj ((tilde.functor A).obj M))
    (I' := (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback p).obj F))
    (QX := (Scheme.Modules.pullback (i ≫ p)).obj F)
    (Z := (tensorSheafFunctor π ((Scheme.Modules.pullback (i ≫ p)).obj F)).obj M)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (eqToHom (tensorSheafFunctor_obj_eq π ((Scheme.Modules.pullback (i ≫ p)).obj F) M).symm)
    (eqToHom_refl _ _) (eqToHom_refl _ _) (eqToHom_refl _ _) (eqToHom_refl _ _)
    ((eqToHom_trans _ _).trans (eqToHom_refl _ _))
    _ _ _ _
    (tensorSheafFunctor_map_eq_eqToHom g F _)
    (tensorBaseChangeIsoGen_inv φ₀ h F _)
    (tensorBaseChangeIsoGen_inv (φ₀ ≫ φ) h' F M)
    (pushforwardTensorSheafIsoGen_hom φ π' π i hsq _ _ _ M)
    (projectionFormulaIsoGen_hom_eq _ _)
    (projectionFormulaIsoOfIsPullback_hom_naturality_firstFactor φ₀ φ h hsq F M)
    (tensorBaseChangeFirstIso_comp_naturality φ₀ φ h hsq h' M)
    ((congrArg (fun k => (Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
        ((Scheme.Modules.pushforwardComp i p).hom.app
          ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj M)) ×ₘ 𝟙 F) ≫ k)
      (projectionFormulaIsoOfIsPullback_hom (φ₀ ≫ φ) h' F _ _)).trans
      (adjunctionTensorMap_comp_eq p i F _))

/-- The comparison of the direct images along two equal morphisms, at a reflexivity proof, is the
identity. -/
theorem pushforwardCongr_rfl_inv_app {Y Y' : Scheme.{u}} {f : Y ⟶ Y'} (K : Y.Modules) :
    (Scheme.Modules.pushforwardCongr (rfl : f = f)).inv.app K = 𝟙 _ :=
  Scheme.Modules.hom_ext _ _ fun U => by
    rw [Scheme.Modules.pushforwardCongr_inv_app_app, Scheme.Modules.Hom.id_app]
    exact presheaf_map_eq_id K.presheaf _

/-- **Thickening coherence at a cartesian square.** For `Λ → A' → A`, a cartesian square over
`Spec A' → Spec Λ`, one over `Spec A → Spec A'` with `i` a closed immersion, and the pasted one,
computing `𝓕_A ⊗_A M` on `W` directly, or first on `X'` through the identification
`𝓕_{A'} ⊗_{A'} M ≅ i_*(𝓕_A ⊗_A M)`, gives the same `𝓕 ⊗_Λ M`. -/
theorem tensorBaseChangeIsoGen_thickening [IsClosedImmersion i] {φ' : Λ ⟶ A}
    (hφ : φ₀ ≫ φ = φ') {p' : X ⟶ W} (hp : i ≫ p = p') (h' : IsPullback π p' (Spec.map φ') g)
    (M : ModuleCat.{u} A) :
    (tensorBaseChangeIsoGen φ' h' F M).hom =
      ((Scheme.Modules.pushforwardCongr hp).symm ≪≫
          (Scheme.Modules.pushforwardComp i p).symm).hom.app
        ((tensorSheafFunctor π ((Scheme.Modules.pullback p').obj F)).obj M) ≫
        (Scheme.Modules.pushforward p).map
          (pushforwardTensorSheafIsoGen φ π' π i hsq ((Scheme.Modules.pullback p).obj F)
            ((Scheme.Modules.pullback p').obj F) (baseChangeSheafIsoGen p p' F i hp) M).inv ≫
        (tensorBaseChangeIsoGen φ₀ h F ((ModuleCat.restrictScalars φ.hom).obj M)).hom ≫
        (tensorSheafFunctor g F).map
          (ModuleCat.restrictScalarsComp'App φ₀.hom φ.hom φ'.hom
            (congrArg CommRingCat.Hom.hom hφ).symm M).inv := by
  subst hφ hp
  exact hom_eq_of_comp_inv_eq _ _ _ ((Scheme.Modules.pushforward p).mapIso
    (pushforwardTensorSheafIsoGen φ π' π i hsq ((Scheme.Modules.pullback p).obj F)
      ((Scheme.Modules.pullback (i ≫ p)).obj F) (baseChangeSheafIsoGen p (i ≫ p) F i rfl) M))
    ((Scheme.Modules.pushforwardComp i p).app
      ((tensorSheafFunctor π ((Scheme.Modules.pullback (i ≫ p)).obj F)).obj M)) _
    (pushforwardCongr_rfl_inv_app _)
    (tensorBaseChangeIsoGen_comp_inv φ₀ φ h hsq F h' M)

/-- Reading a global section of `G` as a global section of `i_* G` does not change it. -/
theorem pushforwardSection_apply {Y Y' : Scheme.{u}} (f : Y ⟶ Y') (G : Y.Modules)
    (z : Γ(G, ⊤)) : pushforwardSection f G z = z :=
  congrArg (fun φ : G.presheaf.obj (op ⊤) ⟶ G.presheaf.obj (op ⊤) => φ z)
    (presheaf_map_eq_id G.presheaf _)

/-- An equation `k = c ≫ x₁ ≫ x₂ ≫ x₃` of morphisms of modules, on sections. -/
theorem modulesHom_app_eq_of_eq_comp {Y : Scheme.{u}} {M₀ M₁ M₂ M₃ M₄ : Y.Modules}
    {k : M₀ ⟶ M₄} {c : M₀ ⟶ M₁} {x₁ : M₁ ⟶ M₂} {x₂ : M₂ ⟶ M₃} {x₃ : M₃ ⟶ M₄}
    (e : k = c ≫ x₁ ≫ x₂ ≫ x₃) (U : Y.Opens) (z : Γ(M₀, U)) :
    Scheme.Modules.Hom.app k U z =
      Scheme.Modules.Hom.app x₃ U (Scheme.Modules.Hom.app x₂ U
        (Scheme.Modules.Hom.app x₁ U (Scheme.Modules.Hom.app c U z))) := by
  subst e
  rfl

/-- The comparison of `(i ≫ p)_*` with `p_* i_*`, on global sections, is reading a section of
`G` as a section of `i_* G`. -/
theorem pushforwardCongr_trans_pushforwardComp_app_top (K : X.Modules) (z : Γ(K, ⊤)) :
    Scheme.Modules.Hom.app (((Scheme.Modules.pushforwardCongr (rfl : i ≫ p = i ≫ p)).symm ≪≫
        (Scheme.Modules.pushforwardComp i p).symm).hom.app K) ⊤ z =
      pushforwardSection i K z := by
  have e₁ : ((Scheme.Modules.pushforwardCongr (rfl : i ≫ p = i ≫ p)).symm ≪≫
        (Scheme.Modules.pushforwardComp i p).symm).hom.app K =
      (Scheme.Modules.pushforwardCongr (rfl : i ≫ p = i ≫ p)).inv.app K ≫
        (Scheme.Modules.pushforwardComp i p).inv.app K := rfl
  rw [e₁, pushforwardCongr_rfl_inv_app, Category.id_comp]
  exact (congrArg (fun φ : (Scheme.Modules.presheaf K).obj (op (i ⁻¹ᵁ (p ⁻¹ᵁ ⊤))) ⟶ _ => φ z)
    (Scheme.Modules.pushforwardComp_inv_app_app i p (M := K) ⊤)).trans
    (pushforwardSection_apply i K z).symm

/-- **Thickening coherence at a cartesian square, on global sections at `M = A`.** -/
theorem tensorBaseChangeIsoGen_thickening_app_top [IsClosedImmersion i] {φ' : Λ ⟶ A}
    (hφ : φ₀ ≫ φ = φ') {p' : X ⟶ W} (hp : i ≫ p = p') (h' : IsPullback π p' (Spec.map φ') g)
    (y : Γ((tensorSheafFunctor π ((Scheme.Modules.pullback p').obj F)).obj
      (ModuleCat.of A A), ⊤)) :
    Scheme.Modules.Hom.app (tensorBaseChangeIsoGen φ' h' F (ModuleCat.of A A)).hom ⊤ y =
      Scheme.Modules.Hom.app ((tensorSheafFunctor g F).map
          (ModuleCat.restrictScalarsComp'App φ₀.hom φ.hom φ'.hom
            (congrArg CommRingCat.Hom.hom hφ).symm (ModuleCat.of A A)).inv) ⊤
        (Scheme.Modules.Hom.app
          (tensorBaseChangeIsoGen φ₀ h F
            ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of A A))).hom ⊤
          (Scheme.Modules.Hom.app
            (pushforwardTensorSheafIsoGen φ π' π i hsq ((Scheme.Modules.pullback p).obj F)
              ((Scheme.Modules.pullback p').obj F) (baseChangeSheafIsoGen p p' F i hp)
              (ModuleCat.of A A)).inv ⊤
            (pushforwardSection i _ y))) := by
  subst hφ hp
  exact (modulesHom_app_eq_of_eq_comp
      (tensorBaseChangeIsoGen_thickening φ₀ φ h hsq F rfl rfl h' (ModuleCat.of A A)) ⊤ y).trans
    (congrArg (fun z => Scheme.Modules.Hom.app ((tensorSheafFunctor g F).map
        (ModuleCat.restrictScalarsComp'App φ₀.hom φ.hom (φ₀ ≫ φ).hom rfl
          (ModuleCat.of A A)).inv) ⊤
      (Scheme.Modules.Hom.app (tensorBaseChangeIsoGen φ₀ h F
        ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of A A))).hom ⊤
        (Scheme.Modules.Hom.app ((Scheme.Modules.pushforward p).map
          (pushforwardTensorSheafIsoGen φ π' π i hsq
            ((Scheme.Modules.pullback p).obj F) ((Scheme.Modules.pullback (i ≫ p)).obj F)
            (baseChangeSheafIsoGen p (i ≫ p) F i rfl) (ModuleCat.of A A)).inv) ⊤ z)))
      (pushforwardCongr_trans_pushforwardComp_app_top _ y))

end Thickening

/-! ### The identification on `W_A = Spec A ×_{Spec Λ} W` -/

section Instance

variable {Λ : CommRingCat.{u}} {W : Scheme.{u}} (g : W ⟶ Spec Λ) (F : W.Modules)
  [F.IsQuasicoherent] {A : CommRingCat.{u}} (t : Spec A ⟶ Spec Λ)

/-- `W_A` is the fibre product of `Spec A` and `W` over `Spec Λ`, with `t` read as the spectrum of
its ring map `Spec.preimage t`. -/
theorem isPullback_fst_snd :
    IsPullback (pullback.fst (Over.mk t).hom g) (pullback.snd (Over.mk t).hom g)
      (Spec.map (Spec.preimage t)) g :=
  have key : ∀ {f : Spec A ⟶ Spec Λ}, (Over.mk t).hom = f →
      IsPullback (pullback.fst (Over.mk t).hom g) (pullback.snd (Over.mk t).hom g) f g :=
    fun e => by
      subst e
      exact IsPullback.of_hasPullback (Over.mk t).hom g
  key (Spec.map_preimage t).symm

/-- **`p_*(𝓕_A ⊗_A M) ≅ 𝓕 ⊗_Λ M`.** For an affine scheme `t : Spec A → Spec Λ` over `Λ` and an
`A`-module `M`, the direct image along the projection `p : W_A → W` of `𝓕_A ⊗_A M` is
`𝓕 ⊗_Λ M`, where on the right `M` is regarded as a `Λ`-module along `Λ → A`. It is the inverse
of the projection formula along the affine morphism `p` ([Stacks, Tag 0FZE]) followed by affine
base change ([Stacks, Tag 02KG]) and the direct image of an associated sheaf along `t`
([Stacks, Tag 01I9]). -/
def tensorBaseChangeIso (M : ModuleCat.{u} A) :
    (Scheme.Modules.pushforward (pullback.snd (Over.mk t).hom g)).obj
        ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) ≅
      (tensorSheafFunctor g F).obj ((ModuleCat.restrictScalars (Spec.preimage t).hom).obj M) :=
  tensorBaseChangeIsoGen (Spec.preimage t) (isPullback_fst_snd g t) F M

/-- **`tensorBaseChangeIso` is natural in the `A`-module.** -/
theorem tensorBaseChangeIso_hom_naturality {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (Scheme.Modules.pushforward (pullback.snd (Over.mk t).hom g)).map
        ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).map f) ≫
        (tensorBaseChangeIso g F t N).hom =
      (tensorBaseChangeIso g F t M).hom ≫
        (tensorSheafFunctor g F).map ((ModuleCat.restrictScalars (Spec.preimage t).hom).map f) :=
  tensorBaseChangeIsoGen_hom_naturality (Spec.preimage t) (isPullback_fst_snd g t) F f

/-- **A section of `𝓕_A` on `W_A`, read as a section of `𝓕 ⊗_Λ A` on `W`**: the section of
`𝓕_A ⊗_A A` it corresponds to under `𝓕_A ⊗_A A ≅ 𝓕_A`, read through `tensorBaseChangeIso` at
`M = A`, the global sections of `p_* G` on `W` being those of `G` on `W_A`. -/
def tensorBaseChangeSection (x : Γ(topSheaf t g F, ⊤)) :
    Γ((tensorSheafFunctor g F).obj
      ((ModuleCat.restrictScalars (Spec.preimage t).hom).obj (ModuleCat.of A A)), ⊤) :=
  (tensorBaseChangeIso g F t (ModuleCat.of A A)).hom.app ⊤
    (Scheme.Modules.Hom.app (tensorSheafFunctorObjSelf (topProj t g) (topSheaf t g F)).inv ⊤ x)

/-- `tensorBaseChangeSection` is the global-sections component of `tensorBaseChangeUnitIsoGen` at
the fibre product. -/
theorem tensorBaseChangeSection_eq (x : Γ(topSheaf t g F, ⊤)) :
    tensorBaseChangeSection g F t x =
      Scheme.Modules.Hom.app
        (tensorBaseChangeUnitIsoGen (Spec.preimage t) (isPullback_fst_snd g t) F).hom ⊤ x :=
  rfl

/-- **Degree-zero naturality in the base.** Let `α : Spec A' → Spec A` be a morphism of schemes
over `Spec Λ` which is `Spec ψ` for a ring map `ψ : A → A'`. Reading sections on `W`, the
restriction map `H⁰(W_A, 𝓕_A) → H⁰(W_{A'}, 𝓕_{A'})` of the functor of sections of Stacks 07YH
becomes the map `H⁰(W, 𝓕 ⊗_Λ A) → H⁰(W, 𝓕 ⊗_Λ A')` induced by `ψ`. -/
theorem tensorBaseChangeSection_restriction {A' : CommRingCat.{u}} (t' : Spec A' ⟶ Spec Λ)
    (α : Over.mk t' ⟶ Over.mk t) (ψ : A ⟶ A') (hα : α.left = Spec.map ψ)
    (x : Γ(topSheaf t g F, ⊤)) :
    tensorBaseChangeSection g F t' ((sectionsPresheafOver g F).map α.op x) =
      Scheme.Modules.Hom.app ((tensorSheafFunctor g F).map
          (restrictScalarsHomOfComp ψ (preimage_comp_eq_of_over α ψ hα))) ⊤
        (tensorBaseChangeSection g F t x) := by
  have hβπ : baseChangeMap g α ≫ pullback.fst (Over.mk t).hom g =
      pullback.fst (Over.mk t').hom g ≫ Spec.map ψ :=
    (baseChangeMap_comp_fst g α).trans
      (congrArg (fun k => pullback.fst (Over.mk t').hom g ≫ k) hα)
  have e1 := tensorBaseChangeSection_eq g F t' ((sectionsPresheafOver g F).map α.op x)
  have e2 := sectionsPresheafOver_map_eq_reductionMapGen g F α
  have e3 := tensorBaseChangeUnitIsoGen_hom_app_restriction (Spec.preimage t)
    (isPullback_fst_snd g t) F ψ (baseChangeMap g α) hβπ (preimage_comp_eq_of_over α ψ hα)
    (isPullback_fst_snd g t') (baseChangeMap_comp_snd g α) x
  have e4 := tensorBaseChangeSection_eq g F t x
  refine e1.trans ?_
  refine Eq.trans (congrArg (fun z : Γ((Scheme.Modules.pullback
        (pullback.snd (Over.mk t').hom g)).obj F, ⊤) => Scheme.Modules.Hom.app
      (tensorBaseChangeUnitIsoGen (Spec.preimage t') (isPullback_fst_snd g t') F).hom ⊤ z)
    ((congrArg (fun f => f x) e2).trans (CategoryTheory.comp_apply _ _ x))) ?_
  refine e3.trans ?_
  exact congrArg (fun z : Γ((tensorSheafFunctor g F).obj
      ((ModuleCat.restrictScalars (Spec.preimage t).hom).obj (ModuleCat.of A A)), ⊤) =>
    Scheme.Modules.Hom.app ((tensorSheafFunctor g F).map
      (restrictScalarsHomOfComp ψ (preimage_comp_eq_of_over α ψ hα))) ⊤ z) e4.symm

/-- `tensorBaseChangeIso` is `tensorBaseChangeIsoGen` at the fibre product. -/
theorem tensorBaseChangeIso_eq (M : ModuleCat.{u} A) :
    tensorBaseChangeIso g F t M =
      tensorBaseChangeIsoGen (Spec.preimage t) (isPullback_fst_snd g t) F M :=
  rfl

/-- **Compatibility with the thickening identification.** Let `α : Spec A → Spec A'` be a morphism
of schemes over `Spec Λ` which is `Spec φ` and whose base change `i : W_A → W_{A'}` is a closed
immersion. For an `A`-module `M`, computing `𝓕_A ⊗_A M` on `W` directly, or first on `W_{A'}`
through `𝓕_{A'} ⊗_{A'} M ≅ i_*(𝓕_A ⊗_A M)` (`pushforwardTensorSheafIsoOver`) and then on `W`,
gives the same `𝓕 ⊗_Λ M`. -/
theorem tensorBaseChangeIso_thickening {A' : CommRingCat.{u}} (t₁ : Spec A' ⟶ Spec Λ)
    (α : Over.mk t ⟶ Over.mk t₁) (φ : A' ⟶ A) (hα : α.left = Spec.map φ)
    (hi : IsClosedImmersion (baseChangeMap g α)) (M : ModuleCat.{u} A) :
    (tensorBaseChangeIso g F t M).hom =
      ((Scheme.Modules.pushforwardCongr (baseChangeMap_comp_snd g α)).symm ≪≫
          (Scheme.Modules.pushforwardComp (baseChangeMap g α)
            (pullback.snd (Over.mk t₁).hom g)).symm).hom.app
        ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) ≫
        (Scheme.Modules.pushforward (pullback.snd (Over.mk t₁).hom g)).map
          (pushforwardTensorSheafIsoOver t₁ t α φ g F hα hi M).inv ≫
        (tensorBaseChangeIso g F t₁ ((ModuleCat.restrictScalars φ.hom).obj M)).hom ≫
        (tensorSheafFunctor g F).map
          (ModuleCat.restrictScalarsComp'App (Spec.preimage t₁).hom φ.hom (Spec.preimage t).hom
            (preimage_hom_eq_comp α φ hα) M).inv := by
  rw [tensorBaseChangeIso_eq, tensorBaseChangeIso_eq, pushforwardTensorSheafIsoOver_eq]
  have := hi
  exact tensorBaseChangeIsoGen_thickening (Spec.preimage t₁) φ (isPullback_fst_snd g t₁)
    (isPullback_baseChangeMap_of_eq t₁ t α φ g hα) F (preimage_comp_eq_of_over α φ hα)
    (baseChangeMap_comp_snd g α) (isPullback_fst_snd g t) M

/-- **Compatibility with the thickening identification, in degree zero.** In the situation of
`tensorBaseChangeIso_thickening`, a section of `𝓕_A` on `W_A`, read on `W` directly, is the
section read first on `W_{A'}` through `sectionTransportOver` and then on `W`. -/
theorem tensorBaseChangeSection_thickening {A' : CommRingCat.{u}} (t₁ : Spec A' ⟶ Spec Λ)
    (α : Over.mk t ⟶ Over.mk t₁) (φ : A' ⟶ A) (hα : α.left = Spec.map φ)
    (hi : IsClosedImmersion (baseChangeMap g α)) (x : Γ(topSheaf t g F, ⊤)) :
    tensorBaseChangeSection g F t x =
      Scheme.Modules.Hom.app ((tensorSheafFunctor g F).map
          (ModuleCat.restrictScalarsComp'App (Spec.preimage t₁).hom φ.hom (Spec.preimage t).hom
            (preimage_hom_eq_comp α φ hα) (ModuleCat.of A A)).inv) ⊤
        (Scheme.Modules.Hom.app (tensorBaseChangeIso g F t₁
            ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of A A))).hom ⊤
          (sectionTransportOver t₁ t α φ g F hα hi x)) := by
  have := hi
  unfold sectionTransportOver tensorBaseChangeSection
  rw [pushforwardTensorSheafIsoOver_eq, tensorBaseChangeIso_eq, tensorBaseChangeIso_eq]
  exact tensorBaseChangeIsoGen_thickening_app_top (Spec.preimage t₁) φ
    (isPullback_fst_snd g t₁) (isPullback_baseChangeMap_of_eq t₁ t α φ g hα) F
    (preimage_comp_eq_of_over α φ hα) (baseChangeMap_comp_snd g α) (isPullback_fst_snd g t)
    (Scheme.Modules.Hom.app (tensorSheafFunctorObjSelf (topProj t g) (topSheaf t g F)).inv ⊤
      x)

end Instance

end Deformation.Artin.SectionsSheaf

end
