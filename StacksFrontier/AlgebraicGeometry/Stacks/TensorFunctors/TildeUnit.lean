module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.TildeModule
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsBetweenCategories.RegularAction

/-!
# The module `A~` is the structure sheaf

Let `U` be a scheme over `S` with ring of global functions `A = Γ(U, 𝒪_U)`.  The functor
`M ↦ M~` of `AlgebraicGeometry.Stack.tildeFunctor` carries the free module `A` to the structure
sheaf `𝒪_U` of the fppf site of `U`, and carries multiplication by `a ∈ A` to multiplication by
the global function `a`.

## Main definitions

* `AlgebraicGeometry.Stack.tildeSelfIso`: `A~ ≅ 𝒪_U`.
* `AlgebraicGeometry.Stack.globalMul`: multiplication by a global function on `𝒪_U`.

## Main results

* `AlgebraicGeometry.Stack.tildeFunctor_map_regularMul`: under `A~ ≅ 𝒪_U`, the image of
  multiplication by `a` on `A` is multiplication by `a` on `𝒪_U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] FibredSite.hasWeakSheafify_associatedTopology
  FibredSite.wEqualsLocallyBijective_associatedTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (U : BigFppfOver B S hS)

local notation "𝒪[" Y "]" => AlgebraicStacks.fppfStructureRingSheaf _ _ _ Y
local notation "𝒪c[" Y "]" => AlgebraicStacks.fppfStructureSheaf _ _ _ Y

/-- The pullback of functions `Γ(U, 𝒪_U) ⟶ Γ(T, 𝒪_T)` along an object `T ⟶ U` of the site. -/
noncomputable abbrev globalRingHomApp (T : (Over U)ᵒᵖ) :
    schemeGlobalRing U →+* (schemeStructurePresheaf U).obj T :=
  ((BigFppfOver.toScheme B S hS).map T.unop.hom).appTop.hom

/-- **`T ↦ 𝒪(T) ⊗_A A` is the structure presheaf**, as presheaves of modules. -/
noncomputable def tildePresheafSelfIso :
    (tildePresheafFunctor.{u, w} U).obj (ModuleCat.of _ (schemeGlobalRing U)) ≅
      PresheafOfModules.unit (𝒪c[schemeStack.{u, w} B S hS U].obj ⋙ forget₂ _ RingCat) :=
  PresheafOfModules.isoMk
    (fun T => ModuleCat.ExtendScalars.objSelfIso (globalRingHomApp U T))
    (fun ⦃T T'⦄ f => Stacks.PullbackModel.extendScalars_hom_ext _ fun m => by
      change (ModuleCat.ExtendScalars.objSelfIso (globalRingHomApp U T')).hom
          (Stacks.PullbackModel.tmul (M := ModuleCat.of _ (schemeGlobalRing U))
            (globalRingHomApp U T') (((schemeStructurePresheaf U).map f).hom 1) m) =
        ((schemeStructurePresheaf U).map f).hom
          ((ModuleCat.ExtendScalars.objSelfIso (globalRingHomApp U T)).hom
            (Stacks.PullbackModel.tmul (M := ModuleCat.of _ (schemeGlobalRing U))
              (globalRingHomApp U T) 1 m))
      exact ModuleCat.ExtendScalars.objSelfIso_hom_naturality_one_tmul _ _ _
        (fun a => Stacks.PullbackModel.app_naturality_apply (schemeGlobalRingHom U) f a) m)

/-- On sections over `T`, the isomorphism `tildePresheafSelfIso` sends `b ⊗ a` to the product of
`b` with the pullback of `a` to `T`. -/
lemma tildePresheafSelfIso_hom_app_tmul (T : (Over U)ᵒᵖ) (b : (schemeStructurePresheaf U).obj T)
    (a : schemeGlobalRing U) :
    ((tildePresheafSelfIso.{u, w} U).hom.app T).hom
        (Stacks.PullbackModel.tmul (M := ModuleCat.of _ (schemeGlobalRing U))
          (globalRingHomApp U T) b a) =
      b * globalRingHomApp U T a :=
  ModuleCat.ExtendScalars.objSelfIso_hom_pullbackModelTmul _ b a

/-- **`A~ ≅ 𝒪_U`**: the sheafification of the structure presheaf is the structure sheaf. -/
noncomputable def tildeSelfIso :
    (tildeFunctor.{u, w} U).obj (ModuleCat.of _ (schemeGlobalRing U)) ≅
      SheafOfModules.unit 𝒪[schemeStack.{u, w} B S hS U] :=
  (Stacks.SheafOfModules.sheafifyFunctor (𝒪c[schemeStack.{u, w} B S hS U]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS (schemeStack.{u, w} B S hS U))).mapIso
      (tildePresheafSelfIso.{u, w} U) ≪≫
    Stacks.SheafOfModules.sheafifyUnitIso (𝒪c[schemeStack.{u, w} B S hS U]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS (schemeStack.{u, w} B S hS U))

/-- The global function `a ∈ A` pulled back to every object `T ⟶ U` of the site. -/
noncomputable def globalSection (a : schemeGlobalRing U) (T : (Over U)ᵒᵖ) :
    (𝒪c[schemeStack.{u, w} B S hS U].obj).obj T :=
  ((schemeGlobalRingHom U).app T).hom a

/-- The pullbacks `globalSection` of a global function are compatible with restriction. -/
lemma globalSection_map (a : schemeGlobalRing U) {T T' : (Over U)ᵒᵖ} (f : T ⟶ T') :
    ((𝒪c[schemeStack.{u, w} B S hS U].obj).map f).hom (globalSection.{u, w} U a T) =
      globalSection.{u, w} U a T' :=
  Stacks.PullbackModel.app_naturality_apply (schemeGlobalRingHom U) f a

/-- **Multiplication by a global function `a ∈ A`** on the structure sheaf of `U`. -/
noncomputable def globalMul (a : schemeGlobalRing U) :
    SheafOfModules.unit 𝒪[schemeStack.{u, w} B S hS U] ⟶
      SheafOfModules.unit 𝒪[schemeStack.{u, w} B S hS U] where
  val := PresheafOfModules.unitMulBy (globalSection.{u, w} U a)
    (fun f => globalSection_map.{u, w} U a f)

/-- On the presheaf level, the image of multiplication by `a` is multiplication by `a`. -/
lemma tildePresheafFunctor_map_regularMul (a : schemeGlobalRing U) :
    (tildePresheafFunctor.{u, w} U).map (ModuleCat.regularMul _ a) ≫
        (tildePresheafSelfIso.{u, w} U).hom =
      (tildePresheafSelfIso.{u, w} U).hom ≫ PresheafOfModules.unitMulBy
        (globalSection.{u, w} U a) (fun f => globalSection_map.{u, w} U a f) := by
  ext1 T
  exact Stacks.PullbackModel.extendScalars_hom_ext _ fun m =>
    ModuleCat.ExtendScalars.objSelfIso_hom_one_tmul_mul (globalRingHomApp U T) a m

/-- The identification of the sheafified structure presheaf with the structure sheaf commutes
with multiplication by a global function. -/
lemma sheafifyUnitIso_hom_globalMul (a : schemeGlobalRing U) :
    (Stacks.SheafOfModules.sheafifyUnitIso (𝒪c[schemeStack.{u, w} B S hS U]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS (schemeStack.{u, w} B S hS U))).hom ≫
        globalMul.{u, w} U a =
      (Stacks.SheafOfModules.sheafifyFunctor (𝒪c[schemeStack.{u, w} B S hS U]).obj
        (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS (schemeStack.{u, w} B S hS U))).map
          (globalMul.{u, w} U a).val ≫
        (Stacks.SheafOfModules.sheafifyUnitIso (𝒪c[schemeStack.{u, w} B S hS U]).obj
          (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS
            (schemeStack.{u, w} B S hS U))).hom :=
  Stacks.SheafOfModules.sheafifyValIso_hom_naturality (𝒪c[schemeStack.{u, w} B S hS U]).obj
    (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS (schemeStack.{u, w} B S hS U))
    (globalMul.{u, w} U a)

/-- **Under `A~ ≅ 𝒪_U`, multiplication by `a` on `A` becomes multiplication by `a` on `𝒪_U`.** -/
theorem tildeFunctor_map_regularMul (a : schemeGlobalRing U) :
    (tildeFunctor.{u, w} U).map (ModuleCat.regularMul _ a) ≫ (tildeSelfIso.{u, w} U).hom =
      (tildeSelfIso.{u, w} U).hom ≫ globalMul.{u, w} U a :=
  Functor.map_comp_mapIso_trans_hom
    (Stacks.SheafOfModules.sheafifyFunctor (𝒪c[schemeStack.{u, w} B S hS U]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS (schemeStack.{u, w} B S hS U)))
    ((tildePresheafFunctor.{u, w} U).map (ModuleCat.regularMul _ a))
    (globalMul.{u, w} U a).val (globalMul.{u, w} U a) (tildePresheafSelfIso.{u, w} U)
    (Stacks.SheafOfModules.sheafifyUnitIso (𝒪c[schemeStack.{u, w} B S hS U]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS (schemeStack.{u, w} B S hS U)))
    (tildePresheafFunctor_map_regularMul.{u, w} U a)
    (sheafifyUnitIso_hom_globalMul.{u, w} U a)

end AlgebraicGeometry.Stack
