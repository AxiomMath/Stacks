module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffinePushforwardAlgebra
public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffinePushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffineUnitDescent
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackModel
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# The quasi-coherent module `M~` on the big fppf site of an affine scheme

Let `U` be an affine scheme over `S` and `A = Γ(U, 𝒪_U)`.  For an `A`-module `M` the presheaf
`T ↦ 𝒪(T) ⊗_A M` on `Sch/U` sheafifies to a quasi-coherent module `M~` on the fppf site of `U`,
whose sections over an affine `T` are `𝒪(T) ⊗_A M`.  This is the identification
`Mod_A = QCoh(𝒪_U)` that Stacks 0GRK composes `F ∘ g_{QCoh,*}` with.

## Main definitions

* `AlgebraicGeometry.Stack.schemeGlobalRing`: `A = Γ(U, 𝒪_U)`.
* `AlgebraicGeometry.Stack.tildePresheaf`: the presheaf `T ↦ 𝒪(T) ⊗_A M`.
* `AlgebraicGeometry.Stack.tildeFunctor`: `M ↦ M~`, valued in sheaves of modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] FibredSite.hasWeakSheafify_associatedTopology
  FibredSite.wEqualsLocallyBijective_associatedTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (U : BigFppfOver B S hS)

/-- Sheafification into abelian groups on the fppf site of an algebraic stack. -/
instance AlgebraicStacks.hasWeakSheafify_fppfSiteTopology (𝒴 : AlgebraicStacks.{u, w} B S hS) :
    HasWeakSheafify (AlgebraicStacks.fppfSiteTopology B S hS 𝒴) AddCommGrpCat.{u} :=
  FibredSite.hasWeakSheafify_associatedTopology B S hS 𝒴.val.val.p .fppf

/-- The weak equivalences of abelian presheaves on the fppf site of an algebraic stack are the
locally bijective morphisms. -/
instance AlgebraicStacks.wEqualsLocallyBijective_fppfSiteTopology
    (𝒴 : AlgebraicStacks.{u, w} B S hS) :
    (AlgebraicStacks.fppfSiteTopology B S hS 𝒴).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒴.val.val.p .fppf

/-- The big fppf site of a scheme over `S` is essentially small: it is the fppf site of the
algebraic stack `(Sch/U)_fppf`. -/
instance essentiallySmall_over_bigFppfOver : EssentiallySmall.{u} (Over U) :=
  essentiallySmall_obj_algebraicStack.{u, u} B S hS (schemeStack.{u, u} B S hS U)

/-- Sheafification into abelian groups on the fppf site of `U`. -/
instance hasWeakSheafify_schemeStack :
    HasWeakSheafify (AlgebraicStacks.fppfSiteTopology B S hS (schemeStack.{u, w} B S hS U))
      AddCommGrpCat.{u} :=
  AlgebraicStacks.hasWeakSheafify_fppfSiteTopology _

/-- The weak equivalences of abelian presheaves on the fppf site of `U` are the locally bijective
morphisms. -/
instance wEqualsLocallyBijective_schemeStack :
    (AlgebraicStacks.fppfSiteTopology B S hS (schemeStack.{u, w} B S hS U)).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  AlgebraicStacks.wEqualsLocallyBijective_fppfSiteTopology _

/-- The ring of global functions `A = Γ(U, 𝒪_U)` of a scheme `U` over `S`. -/
noncomputable abbrev schemeGlobalRing : CommRingCat.{u} := Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)

/-- The structure presheaf of commutative rings of the fppf site `Sch/U`: `T ↦ Γ(T, 𝒪_T)`. -/
noncomputable abbrev schemeStructurePresheaf : (Over U)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Over.forget U).op ⋙ (BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ

/-- `schemeStructurePresheaf U` is the structure presheaf of the algebraic stack `Sch/U`. -/
theorem schemeStructurePresheaf_eq :
    schemeStructurePresheaf U =
      (AlgebraicStacks.fppfStructureSheaf B S hS (schemeStack.{u, w} B S hS U)).obj := by
  rw [FibredSite.structureSheaf_obj]
  rfl

/-- The map from the constant presheaf with value `A = Γ(U, 𝒪_U)` to the structure presheaf of
`Sch/U`: pullback of functions along the structure morphisms `T ⟶ U`. -/
noncomputable def schemeGlobalRingHom :
    (Functor.const (Over U)ᵒᵖ).obj (schemeGlobalRing U) ⟶ schemeStructurePresheaf U where
  app T := ((BigFppfOver.toScheme B S hS).map T.unop.hom).appTop
  naturality T T' f := by
    have h1 : ((BigFppfOver.toScheme B S hS).map T'.unop.hom).appTop =
        ((BigFppfOver.toScheme B S hS).map T.unop.hom).appTop ≫
          ((BigFppfOver.toScheme B S hS).map f.unop.left).appTop := by
      rw [← Over.w f.unop, Functor.map_comp, Scheme.Hom.comp_appTop]
    exact (Category.id_comp _).trans h1

/-- An `A`-module, read as a constant presheaf of modules over the constant presheaf of rings
with value `A`. -/
noncomputable def constModulePresheaf (M : ModuleCat.{u} (schemeGlobalRing U)) :
    PresheafOfModules.{u}
      ((Functor.const (Over U)ᵒᵖ).obj (schemeGlobalRing U) ⋙ forget₂ CommRingCat RingCat) where
  obj _ := M
  map _ := ModuleCat.ofHom (Y := (ModuleCat.restrictScalars _).obj M)
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- `M ↦` the constant presheaf of modules with value `M`. -/
noncomputable def constModulePresheafFunctor :
    ModuleCat.{u} (schemeGlobalRing U) ⥤ PresheafOfModules.{u}
      ((Functor.const (Over U)ᵒᵖ).obj (schemeGlobalRing U) ⋙ forget₂ CommRingCat RingCat) where
  obj M := constModulePresheaf U M
  map f := { app _ := f }

/-- **The presheaf `T ↦ 𝒪(T) ⊗_A M`** on `Sch/U`. -/
noncomputable def tildePresheaf (M : ModuleCat.{u} (schemeGlobalRing U)) :
    PresheafOfModules.{u} (schemeStructurePresheaf U ⋙ forget₂ CommRingCat RingCat) :=
  (Stacks.PullbackModel.extendScalars (schemeGlobalRingHom U)).obj (constModulePresheaf U M)

/-- `M ↦ (T ↦ 𝒪(T) ⊗_A M)`, as a functor. -/
noncomputable def tildePresheafFunctor :
    ModuleCat.{u} (schemeGlobalRing U) ⥤
      PresheafOfModules.{u}
        (AlgebraicStacks.fppfStructureRingSheaf B S hS (schemeStack.{u, w} B S hS U)).obj :=
  constModulePresheafFunctor U ⋙ Stacks.PullbackModel.extendScalars (schemeGlobalRingHom U)

/-- `constModulePresheafFunctor U` preserves colimits: colimits of presheaves of modules are
detected objectwise, and each evaluation of a constant presheaf is the module it is built from. -/
instance : PreservesColimitsOfSize.{u, u} (constModulePresheafFunctor U) where
  preservesColimitsOfShape := ⟨⟨fun hc ↦ ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _
    (fun _ ↦ hc)⟩⟩⟩

/-- `tildePresheafFunctor U` preserves colimits, as the composite of
`constModulePresheafFunctor U` with extension of scalars, a left adjoint. -/
instance : PreservesColimitsOfSize.{u, u} (tildePresheafFunctor.{u, w} U) := by
  have : PreservesColimitsOfSize.{u, u} (Stacks.PullbackModel.extendScalars
      (schemeGlobalRingHom U)) := (Stacks.PullbackModel.extendScalarsAdjunction
    (schemeGlobalRingHom U)).leftAdjoint_preservesColimits
  exact Limits.comp_preservesColimits (constModulePresheafFunctor U)
    (Stacks.PullbackModel.extendScalars (schemeGlobalRingHom U))

/-- The identity of the structure presheaf of rings of an algebraic stack is locally
injective. -/
instance isLocallyInjective_id_fppfStructureRingSheaf (𝒴 : AlgebraicStacks.{u, w} B S hS) :
    Presheaf.IsLocallyInjective (AlgebraicStacks.fppfSiteTopology B S hS 𝒴)
      (𝟙 (AlgebraicStacks.fppfStructureRingSheaf B S hS 𝒴).obj) :=
  Presheaf.isLocallyInjective_of_injective _ _ (fun _ _ _ h => h)

/-- The identity of the structure presheaf of rings of an algebraic stack is locally
surjective. -/
instance isLocallySurjective_id_fppfStructureRingSheaf (𝒴 : AlgebraicStacks.{u, w} B S hS) :
    Presheaf.IsLocallySurjective (AlgebraicStacks.fppfSiteTopology B S hS 𝒴)
      (𝟙 (AlgebraicStacks.fppfStructureRingSheaf B S hS 𝒴).obj) :=
  Presheaf.isLocallySurjective_of_surjective _ _ (fun _ x => ⟨x, rfl⟩)

/-- **`M ↦ M~`**: the sheafification of `T ↦ 𝒪(T) ⊗_A M`, a sheaf of modules on the fppf site of
`U`. -/
noncomputable def tildeFunctor :
    ModuleCat.{u} (schemeGlobalRing U) ⥤
      SheafOfModules.{u} (AlgebraicStacks.fppfStructureRingSheaf B S hS
        (schemeStack.{u, w} B S hS U)) :=
  tildePresheafFunctor.{u, w} U ⋙ Stacks.SheafOfModules.sheafifyFunctor
    (AlgebraicStacks.fppfStructureSheaf B S hS (schemeStack.{u, w} B S hS U)).obj
    (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS (schemeStack.{u, w} B S hS U))

/-- `tildeFunctor U` preserves colimits, as the composite of `tildePresheafFunctor U` with
sheafification, a left adjoint. -/
instance : PreservesColimitsOfSize.{u, u} (tildeFunctor.{u, w} U) := by
  have : PreservesColimitsOfSize.{u, u} (Stacks.SheafOfModules.sheafifyFunctor
      (AlgebraicStacks.fppfStructureSheaf B S hS (schemeStack.{u, w} B S hS U)).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS (schemeStack.{u, w} B S hS U))) :=
    (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction
      (AlgebraicStacks.fppfStructureSheaf B S hS (schemeStack.{u, w} B S hS U)).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS
        (schemeStack.{u, w} B S hS U))).leftAdjoint_preservesColimits
  exact @Limits.comp_preservesColimits _ _ _ _ _ _ (tildePresheafFunctor.{u, w} U) _
    inferInstance this

end AlgebraicGeometry.Stack

namespace ModuleCat.ExtendScalars

universe v

variable {A B : Type v} [CommRing A] [CommRing B] (f : A →+* B)

/-- `ModuleCat.ExtendScalars.objSelfIso_hom_tmul` in the `Stacks.PullbackModel.tmul` spelling. -/
lemma objSelfIso_hom_pullbackModelTmul (b : B) (a : A) :
    (objSelfIso f).hom (Stacks.PullbackModel.tmul (M := ModuleCat.of A A) f b a) = b * f a :=
  objSelfIso_hom_tmul f b a

/-- Naturality of `B ⊗_A A ≅ B` in `B`, on the pure tensors `1 ⊗ m`. -/
lemma objSelfIso_hom_naturality_one_tmul {B' : Type v} [CommRing B'] (f' : A →+* B')
    (g : B →+* B') (h : ∀ a, g (f a) = f' a) (m : A) :
    (objSelfIso f').hom (Stacks.PullbackModel.tmul (M := ModuleCat.of A A) f' (g 1) m) =
      g ((objSelfIso f).hom (Stacks.PullbackModel.tmul (M := ModuleCat.of A A) f 1 m)) := by
  rw [objSelfIso_hom_pullbackModelTmul, objSelfIso_hom_pullbackModelTmul]
  simp [h]

/-- Multiplication by `a` on `A` becomes multiplication by `f a` under `B ⊗_A A ≅ B`. -/
lemma objSelfIso_hom_one_tmul_mul (a m : A) :
    (objSelfIso f).hom (Stacks.PullbackModel.tmul (M := ModuleCat.of A A) f 1 (a * m)) =
      f a * (objSelfIso f).hom (Stacks.PullbackModel.tmul (M := ModuleCat.of A A) f 1 m) := by
  rw [objSelfIso_hom_pullbackModelTmul, objSelfIso_hom_pullbackModelTmul]
  simp

end ModuleCat.ExtendScalars

namespace CategoryTheory.Functor

/-- An endomorphism intertwined by an isomorphism `i`, carried through a functor and composed with
an isomorphism `c` natural for the target endomorphism. -/
lemma map_comp_mapIso_trans_hom {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D)
    {X X' : C} {Y : D} (φ : X ⟶ X) (ψ' : X' ⟶ X') (ψ : Y ⟶ Y) (i : X ≅ X') (c : L.obj X' ≅ Y)
    (h₁ : φ ≫ i.hom = i.hom ≫ ψ') (h₂ : c.hom ≫ ψ = L.map ψ' ≫ c.hom) :
    L.map φ ≫ (L.mapIso i ≪≫ c).hom = (L.mapIso i ≪≫ c).hom ≫ ψ := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, h₂, ← L.map_comp_assoc, h₁]

end CategoryTheory.Functor
