module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDirectImageComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardAction
public import StacksFrontier.Algebra.Category.ModuleCat.NatTransExtRegular
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointPullbackDirectImageUnit

/-!
# The action of `g_*𝒪_U` on `g_*N` and the `C`-linearity of Stacks 0GRK

Let `g : U ⟶ 𝒳` be an affine 1-morphism from an affine scheme to an algebraic stack and
`F : QCoh(𝒪_𝒳) ⥤ Mod_R` a right exact tensor functor commuting with direct sums. Stacks 0GRK
(`AlgebraicGeometry.Stack.affineTensorFunctorIso`) identifies `F(g_{QCoh,*}M~)` with `M ⊗_A C`,
`C = F(g_{QCoh,*}𝒪_U)`, as `R`-modules. This file shows that this identification is `C`-linear,
where `C` acts on `F(g_{QCoh,*}N)` through the action `g_*N ⊗ g_*𝒪_U ⟶ g_*N` of the algebra
`g_*𝒪_U`, the sheafification of the objectwise action `n ⊗ s ↦ s • n`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.directImageAct`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImageAct`: the action.
* `AlgebraicGeometry.Stack.AlgebraicStacks.directImageSMul`: multiplication by `c ∈ C` on
  `F(g_{QCoh,*}N)`, natural in `N`, for `F` lax braided for the localized structure (I).
* `AlgebraicGeometry.Stack.AlgebraicStacks.directImageProjection` (strict structure) and
  `AlgebraicGeometry.Stack.AlgebraicStacks.affineQuasicoherentProjectionMap` (localized structure):
  the projection map `M ⊗ g_*𝒪 ⟶ g_*g^*M`, the unit of `g^* ⊣ g_*` followed by the action.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.tensorObjIso_inv_comp_mul_eq_directImageAct`: the
  multiplication of `C` (localized structure) agrees with the action (strict structure).
* `whiskerLeft_directImageSMul_comp_affineTensorFunctorIso_hom` (namespace
  `AlgebraicGeometry.Stack.AlgebraicStacks`): **the isomorphism of Stacks 0GRK is `C`-linear**.

## References

* [Stacks Project, Tag 0GRK](https://stacks.math.columbia.edu/tag/0GRK)
* [Stacks Project, Tag 0GRQ](https://stacks.math.columbia.edu/tag/0GRQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] hasSheafCompose_forget_ringCat
  hasSheafCompose_forget_commRingCat Stacks.hasSheafCompose_forget₂_commRingCat
  FlatFppf.hasSheafify_addCommGrpCat FlatFppf.wEqualsLocallyBijective_addCommGrpCat
  FlatFppf.hasSheafify_fppf_addCommGrpCat FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat
  FlatFppf.hasSheafify_associatedTopology_ab
  FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat
attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric
attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒰 ⟶ 𝒳) (hg : IsAffineHom B S hS g)

/-- The sheafification adjunction of presheaves of modules on the fppf site of `𝒳`. -/
local notation "𝔰" => Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction
  (fppfStructurePresheaf B S hS 𝒳) (fppfStructurePresheaf_isSheaf B S hS 𝒳)

/-- **The action `g_*N ⊗ g_*𝒪_𝒰 ⟶ g_*N`** in `Mod(𝒪_𝒳)`, for the direct image
`g_* = affinePushforward g` (`(g_*N)(x) = N(r x)`): the sheafification of the objectwise action
`n ⊗ s ↦ s • n`, followed by the counit. -/
def directImageAct (N : Stack.fppfModules B S hS 𝒰) :
    (affinePushforward.{u, w, u} g hg).obj N ⊗ affinePushforwardStructureSheaf g hg ⟶
      (affinePushforward.{u, w, u} g hg).obj N :=
  (Stacks.SheafOfModules.sheafifyFunctor (fppfStructurePresheaf B S hS 𝒳)
      (fppfStructurePresheaf_isSheaf B S hS 𝒳)).map
      (PresheafOfModules.pushforwardAct (pushforwardCommRingHom g hg) N.val) ≫
    (Stacks.SheafOfModules.sheafifyValIso (fppfStructurePresheaf B S hS 𝒳)
      (fppfStructurePresheaf_isSheaf B S hS 𝒳) ((affinePushforward.{u, w, u} g hg).obj N)).hom

variable {g hg} in
/-- The objectwise action is natural in the module. -/
theorem directImageActPresheaf_naturality {N N' : Stack.fppfModules B S hS 𝒰} (ψ : N ⟶ N') :
    PresheafOfModules.Monoidal.tensorHom (R := fppfStructurePresheaf B S hS 𝒳)
        ((affinePushforward.{u, w, u} g hg).map ψ).val
        (𝟙 (affinePushforwardStructureSheaf g hg).val) ≫
      PresheafOfModules.pushforwardAct (pushforwardCommRingHom g hg) N'.val =
    PresheafOfModules.pushforwardAct (pushforwardCommRingHom g hg) N.val ≫
      ((affinePushforward.{u, w, u} g hg).map ψ).val :=
  PresheafOfModules.pushforwardAct_naturality (pushforwardCommRingHom g hg) ψ.val

variable {g hg} in
/-- **The action is natural in the module.** -/
theorem directImageAct_naturality {N N' : Stack.fppfModules B S hS 𝒰} (ψ : N ⟶ N') :
    (affinePushforward.{u, w, u} g hg).map ψ ▷ affinePushforwardStructureSheaf g hg ≫
        directImageAct g hg N' =
      directImageAct g hg N ≫ (affinePushforward.{u, w, u} g hg).map ψ :=
  Stacks.SheafOfModules.whiskerRight_comp_sheafify_map_comp (fppfStructurePresheaf B S hS 𝒳)
    (fppfStructurePresheaf_isSheaf B S hS 𝒳) ((affinePushforward.{u, w, u} g hg).map ψ)
    ((affinePushforward.{u, w, u} g hg).map ψ) _ _ (directImageActPresheaf_naturality ψ)

attribute [local instance] AlgebraicStacks.modulesMonoidalCategory in
/-- **On `g_*𝒪_𝒰` the action is the multiplication of the algebra `g_*𝒪_𝒰`** of Stacks 0GRK
(`AlgebraicGeometry.Stack.monObjAffinePushforwardStructureSheaf`, for the localized monoidal
structure), read on the tensor product sheaf through `Stacks.SheafOfModules.tensorObjIso`. -/
theorem tensorObjIso_inv_comp_mul_eq_directImageAct :
    (Stacks.SheafOfModules.tensorObjIso (fppfStructurePresheaf B S hS 𝒳)
        (fppfStructurePresheaf_isSheaf B S hS 𝒳) (affinePushforwardStructureSheaf g hg)
          (affinePushforwardStructureSheaf g hg)).inv ≫
      @MonObj.mul _ _ (AlgebraicStacks.modulesMonoidalCategory B S hS 𝒳) _
        (monObjAffinePushforwardStructureSheaf g hg) =
      directImageAct g hg (SheafOfModules.unit _) :=
  (Stacks.SheafOfModules.tensorObjIso_inv_comp_mul (fppfStructurePresheaf B S hS 𝒳)
    (fppfStructurePresheaf_isSheaf B S hS 𝒳) (affinePushforwardStructureSheaf g hg)
    (hG := PresheafOfModules.monObjAlgebraPresheaf (pushforwardCommRingHom g hg))).trans
    (congrArg (fun k => (Stacks.SheafOfModules.sheafifyFunctor (fppfStructurePresheaf B S hS 𝒳)
      (fppfStructurePresheaf_isSheaf B S hS 𝒳)).map k ≫
        (Stacks.SheafOfModules.sheafifyValIso (fppfStructurePresheaf B S hS 𝒳)
          (fppfStructurePresheaf_isSheaf B S hS 𝒳) (affinePushforwardStructureSheaf g hg)).hom)
      (PresheafOfModules.pushforwardAct_unit (pushforwardCommRingHom g hg)).symm)

section Projection

/-- The objectwise projection map `M(x) ⊗ 𝒪_𝒰(r x) ⟶ M(g(r x))`, `m ⊗ s ↦ s • m|_{g(r x)}`: the
objectwise unit followed by the objectwise action. -/
def directImageProjectionPresheaf (M : Stack.fppfModules B S hS 𝒳) :
    PresheafOfModules.Monoidal.tensorObj (R := fppfStructurePresheaf B S hS 𝒳) M.val
        (affinePushforwardStructureSheaf g hg).val ⟶
      ((affinePushforward.{u, w, u} g hg).obj ((stackModulePullback.{u, w, u} g).obj M)).val :=
  PresheafOfModules.Monoidal.tensorHom (R := fppfStructurePresheaf B S hS 𝒳)
      ((affinePullbackPushforwardAdjunction.{u, w, u} g hg).unit.app M).val
      (𝟙 (affinePushforwardStructureSheaf g hg).val) ≫
    PresheafOfModules.pushforwardAct (pushforwardCommRingHom g hg)
      ((stackModulePullback.{u, w, u} g).obj M).val

theorem directImageProjectionPresheaf_app_tmul (M : Stack.fppfModules B S hS 𝒳)
    (X : 𝒳.val.val.objᵒᵖ) (m : M.val.obj X)
    (s : (fppfStructureRingSheaf B S hS 𝒰).obj.obj (op ((affineRightAdjoint g hg).obj X.unop))) :
    ((directImageProjectionPresheaf g hg M).app X).hom (m ⊗ₜ s) =
      @HSMul.hSMul ((fppfStructureRingSheaf B S hS 𝒰).obj.obj
          (op ((affineRightAdjoint g hg).obj X.unop)))
        (((stackModulePullback.{u, w, u} g).obj M).val.obj
          (op ((affineRightAdjoint g hg).obj X.unop))) _
        instHSMul s (M.val.map ((affineAdjunction g hg).counit.app X.unop).op m) :=
  PresheafOfModules.pushforwardAct_app_tmul (pushforwardCommRingHom g hg)
    ((stackModulePullback.{u, w, u} g).obj M).val X
    (M.val.map ((affineAdjunction g hg).counit.app X.unop).op m) s

open FibredSite in
/-- **The objectwise projection map is bijective over an affine object**, for `M` quasi-coherent:
over `y` it is `M(y) ⊗_{𝒪(y)} 𝒪(g(r y)) ⟶ M(g(r y))`, the base change of the sections of `M` along
the counit `g(r y) ⟶ y`. -/
theorem bijective_directImageProjectionPresheaf_app (M : quasicoherentModules B S hS 𝒳)
    {y : 𝒳.val.val.obj}
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y))) :
    Function.Bijective ((directImageProjectionPresheaf g hg M.obj).app (op y)) := by
  have := isAffineHom_map_affineAdjunction_counit g hg y
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (𝒳.val.val.p.obj ((𝟭 𝒳.val.val.obj).obj y))) := hy
  have hx : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (𝒳.val.val.p.obj
        (g.hom.hom.toFunctor.obj ((affineRightAdjoint g hg).obj y)))) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map
      (𝒳.val.val.p.map ((affineAdjunction g hg).counit.app y)))
  let := objModule B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids M.obj y
  let := objModule B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids M.obj
    (g.hom.hom.toFunctor.obj ((affineRightAdjoint g hg).obj y))
  let := objAlgebra B S hS 𝒳.val.val.p (x := y)
    (y := (g.hom.hom.toFunctor.obj ((affineRightAdjoint g hg).obj y)))
    ((affineAdjunction g hg).counit.app y)
  let : Module (objRing B S hS 𝒳.val.val.p y)
      (M.obj.val.obj (op (g.hom.hom.toFunctor.obj ((affineRightAdjoint g hg).obj y)))) :=
    Module.compHom _ (algebraMap (objRing B S hS 𝒳.val.val.p y)
      (objRing B S hS 𝒳.val.val.p (g.hom.hom.toFunctor.obj ((affineRightAdjoint g hg).obj y))))
  have : IsScalarTower (objRing B S hS 𝒳.val.val.p y)
      (objRing B S hS 𝒳.val.val.p (g.hom.hom.toFunctor.obj ((affineRightAdjoint g hg).obj y)))
      (M.obj.val.obj (op (g.hom.hom.toFunctor.obj ((affineRightAdjoint g hg).obj y)))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hL : Function.Bijective ((restrictionLinear M.obj (x := y)
      (y := (g.hom.hom.toFunctor.obj ((affineRightAdjoint g hg).obj y)))
      ((affineAdjunction g hg).counit.app y)).liftBaseChange
        (objRing B S hS 𝒳.val.val.p (g.hom.hom.toFunctor.obj ((affineRightAdjoint g hg).obj y)))) :=
    bijective_liftBaseChange_of_eq_restriction M.obj M.property (x := y)
      (y := (g.hom.hom.toFunctor.obj ((affineRightAdjoint g hg).obj y)))
      ((affineAdjunction g hg).counit.app y) hy hx _ (fun _ => rfl)
  let := objModule B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (affinePushforwardStructureSheaf g hg) y
  let τ : (affinePushforwardStructureSheaf g hg).val.obj (op y) →ₗ[objRing B S hS 𝒳.val.val.p y]
      objRing B S hS 𝒳.val.val.p (g.hom.hom.toFunctor.obj ((affineRightAdjoint g hg).obj y)) :=
    { toFun := fun s => ((pullbackRingHom g).hom.app (op ((affineRightAdjoint g hg).obj y))).hom s
      map_add' := map_add _
      map_smul' := fun a s => by
        have hres := congrArg (fun φ => (φ.app (op y)).hom a)
          (whiskerRight_counit_eq_of_eq (affineAdjunction g hg)
            (structureSheaf_obj_eq_homFunctor g)).1
        simp only [NatTrans.comp_app, RingCat.hom_comp] at hres
        exact (map_mul ((pullbackRingHom g).hom.app (op ((affineRightAdjoint g hg).obj y))).hom
          (((pushforwardCommRingHom g hg).app (op y)).hom a)
          (s : (fppfStructureRingSheaf B S hS 𝒰).obj.obj
            (op ((affineRightAdjoint g hg).obj y)))).trans (congrArg (· * _) hres.symm) }
  have hτ : Function.Bijective τ :=
    ConcreteCategory.bijective_of_isIso ((eqToIso (ringStructureSheafCore_obj_eq_homFunctor g)).app
      (op ((affineRightAdjoint g hg).obj y))).hom
  exact Function.Bijective.of_tmul_eq_swap (LinearEquiv.refl _ _) (LinearEquiv.ofBijective τ hτ)
    ((directImageProjectionPresheaf g hg M.obj).app (op y)).hom.toAddMonoidHom
    ((restrictionLinear M.obj (x := y)
      (y := (g.hom.hom.toFunctor.obj ((affineRightAdjoint g hg).obj y)))
      ((affineAdjunction g hg).counit.app y)).liftBaseChange
        (objRing B S hS 𝒳.val.val.p
          (g.hom.hom.toFunctor.obj ((affineRightAdjoint g hg).obj y)))).toAddMonoidHom hL
    (fun m s => directImageProjectionPresheaf_app_tmul g hg M.obj (op y) m s)

/-- **The projection map `M ⊗ g_*𝒪_𝒰 ⟶ g_*g^*M`** in `Mod(𝒪_𝒳)` (strict tensor product), for the
direct image `g_* = affinePushforward g`: the sheafification of the objectwise projection map. -/
def directImageProjection (M : Stack.fppfModules B S hS 𝒳) :
    M ⊗ affinePushforwardStructureSheaf g hg ⟶
      (affinePushforward.{u, w, u} g hg).obj ((stackModulePullback.{u, w, u} g).obj M) :=
  ((𝔰).homEquiv _ _).symm (directImageProjectionPresheaf g hg M)

/-- **The projection formula for an affine 1-morphism**: for `M` quasi-coherent the projection map
`M ⊗ g_*𝒪_𝒰 ⟶ g_*g^*M` is an isomorphism. -/
theorem isIso_directImageProjection (M : quasicoherentModules B S hS 𝒳) :
    IsIso (directImageProjection g hg M.obj) := by
  refine isIso_of_bijective_app_of_isAffine 𝒳 _ (fun y hy => ?_)
  have h2 : (𝔰).unit.app _ ≫ (SheafOfModules.forget _ ⋙
      PresheafOfModules.restrictScalars _).map (directImageProjection g hg M.obj) =
        directImageProjectionPresheaf g hg M.obj :=
    ((𝔰).homEquiv_unit (f := directImageProjection g hg M.obj)).symm.trans
      (Equiv.apply_symm_apply _ _)
  have hO : (affinePushforwardStructureSheaf g hg).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((affinePushforwardIsoFppfModulesPushforward g hg).app (SheafOfModules.unit _)).symm
      (isQuasicoherentOnSite_fppfModulesPushforward_of_isAffineHom B S hS g hg
        ⟨SheafOfModules.unit _, SheafOfModules.isQuasicoherentOnSite_unit _⟩)
  have hu := FibredSite.bijective_sheafTensor_unit_app_of_isAffine B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids M.obj (affinePushforwardStructureSheaf g hg)
    (fun φ hz hx _ => FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite M.obj
      M.property φ hz hx)
    (fun φ hz hx _ => FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite _ hO φ hz hx)
    hy
  have hb := bijective_directImageProjectionPresheaf_app g hg M hy
  rw [← h2] at hb
  exact (Function.Bijective.of_comp_iff _ hu).1 hb

/-- The unit followed by the action is the sheafified objectwise projection map. -/
theorem whiskerRight_unit_comp_directImageAct (M : Stack.fppfModules B S hS 𝒳) :
    (affinePullbackPushforwardAdjunction.{u, w, u} g hg).unit.app M ▷
        affinePushforwardStructureSheaf g hg ≫
      directImageAct g hg ((stackModulePullback.{u, w, u} g).obj M) =
      ((Stacks.SheafOfModules.sheafifyFunctor (fppfStructurePresheaf B S hS 𝒳)
          (fppfStructurePresheaf_isSheaf B S hS 𝒳)).map (directImageProjectionPresheaf g hg M) ≫
        (Stacks.SheafOfModules.sheafifyValIso (fppfStructurePresheaf B S hS 𝒳)
          (fppfStructurePresheaf_isSheaf B S hS 𝒳)
          ((affinePushforward.{u, w, u} g hg).obj ((stackModulePullback.{u, w, u} g).obj M))).hom) ≫
        𝟙 _ :=
  Stacks.SheafOfModules.whiskerRight_comp_sheafify_map_comp (fppfStructurePresheaf B S hS 𝒳)
    (fppfStructurePresheaf_isSheaf B S hS 𝒳)
    ((affinePullbackPushforwardAdjunction.{u, w, u} g hg).unit.app M) (𝟙 _)
    (directImageProjectionPresheaf g hg M) _ (Category.comp_id _).symm

/-- For `M` quasi-coherent the unit followed by the action is an isomorphism. -/
theorem isIso_whiskerRight_unit_comp_directImageAct (M : quasicoherentModules B S hS 𝒳) :
    IsIso ((affinePullbackPushforwardAdjunction.{u, w, u} g hg).unit.app M.obj ▷
        affinePushforwardStructureSheaf g hg ≫
      directImageAct g hg ((stackModulePullback.{u, w, u} g).obj M.obj)) := by
  rw [whiskerRight_unit_comp_directImageAct]
  have e2 := Adjunction.homEquiv_counit
    (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction
      (fppfStructurePresheaf B S hS 𝒳) (fppfStructurePresheaf_isSheaf B S hS 𝒳))
    (PresheafOfModules.Monoidal.tensorObj (R := fppfStructurePresheaf B S hS 𝒳) M.obj.val
      (affinePushforwardStructureSheaf g hg).val)
    ((affinePushforward.{u, w, u} g hg).obj ((stackModulePullback.{u, w, u} g).obj M.obj))
    (directImageProjectionPresheaf g hg M.obj)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (e2 ▸ isIso_directImageProjection g hg M) (IsIso.id _)

end Projection

end AlgebraicGeometry.Stack.AlgebraicStacks

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] FibredSite.monoidalCategoryQuasicoherentModules
  AlgebraicStacks.quasicoherentSymmetricCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hg : IsAffineHom B S hS g)

/-- **The action `g_*N ⊗ g_*𝒪_U ⟶ g_*N` in `QCoh(𝒪_𝒳)`**, for the localized monoidal structure
(I): `directImageAct` read on the localized tensor product through
`Stacks.SheafOfModules.tensorObjIso`. -/
def quasicoherentDirectImageAct (N : quasicoherentModules B S hS (schemeStack.{u, w} B S hS U)) :
    (affineQuasicoherentPushforward g hg).obj N ⊗ affineQuasicoherentStructureSheaf g hg ⟶
      (affineQuasicoherentPushforward g hg).obj N :=
  ObjectProperty.homMk ((Stacks.SheafOfModules.tensorObjIso (fppfStructurePresheaf B S hS 𝒳)
      (fppfStructurePresheaf_isSheaf B S hS 𝒳) _ _).hom ≫ directImageAct g hg N.obj)

variable {g hg} in
/-- The action is natural in the module. -/
theorem quasicoherentDirectImageAct_naturality
    {N N' : quasicoherentModules B S hS (schemeStack.{u, w} B S hS U)} (f : N ⟶ N') :
    (affineQuasicoherentPushforward g hg).map f ▷ affineQuasicoherentStructureSheaf g hg ≫
        quasicoherentDirectImageAct g hg N' =
      quasicoherentDirectImageAct g hg N ≫ (affineQuasicoherentPushforward g hg).map f := by
  refine ObjectProperty.hom_ext _ ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ directImageAct g hg N'.obj)
    (Stacks.SheafOfModules.whiskerRight_comp_tensorObjIso_hom (fppfStructurePresheaf B S hS 𝒳)
      (fppfStructurePresheaf_isSheaf B S hS 𝒳) ((affinePushforward.{u, w, u} g hg).map f.hom)
      (affinePushforwardStructureSheaf g hg))).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (directImageAct_naturality f.hom)).trans
    (Category.assoc _ _ _).symm)

/-- **On `𝒪_U` the action is the multiplication of the algebra `g_{QCoh,*}𝒪_U`** of
Stacks 0GRK. -/
theorem quasicoherentDirectImageAct_structureSheaf :
    quasicoherentDirectImageAct g hg (quasicoherentStructureSheaf.{u, w} (U := U)) =
      @MonObj.mul _ _ _ _ (monObjAffineQuasicoherentStructureSheaf g hg) := by
  refine ObjectProperty.hom_ext _ ?_
  exact (congrArg (_ ≫ ·) (tensorObjIso_inv_comp_mul_eq_directImageAct g hg).symm).trans
    (Iso.hom_inv_id_assoc _ _)

/-- The unit `M ⟶ g_* g^* M` of `g^* ⊣ g_*` (the affine direct image), in `QCoh(𝒪_𝒳)`. -/
def affineQuasicoherentUnit (M : quasicoherentModules B S hS 𝒳) :
    M ⟶ (affineQuasicoherentPushforward g hg).obj (quasicoherentPullbackObj B S hS g M) :=
  ObjectProperty.homMk ((affinePullbackPushforwardAdjunction.{u, w, u} g hg).unit.app M.obj)

/-- **The projection map `M ⊗ g_*𝒪_U ⟶ g_*g^*M`** in `QCoh(𝒪_𝒳)` (localized structure): the unit
followed by the action of `g_*𝒪_U` on `g_*g^*M`; on sections over `x`,
`m ⊗ s ↦ s • m|_{g(r x)}`. -/
def affineQuasicoherentProjectionMap (M : quasicoherentModules B S hS 𝒳) :
    M ⊗ affineQuasicoherentStructureSheaf g hg ⟶
      (affineQuasicoherentPushforward g hg).obj (quasicoherentPullbackObj B S hS g M) :=
  affineQuasicoherentUnit g hg M ▷ affineQuasicoherentStructureSheaf g hg ≫
    quasicoherentDirectImageAct g hg (quasicoherentPullbackObj B S hS g M)

/-- **The projection formula in `QCoh(𝒪_𝒳)`** (localized structure): for `M` quasi-coherent the
projection map `M ⊗ g_{QCoh,*}𝒪_U ⟶ g_{QCoh,*}g^*M` is an isomorphism. -/
instance isIso_affineQuasicoherentProjectionMap (M : quasicoherentModules B S hS 𝒳) :
    IsIso (affineQuasicoherentProjectionMap g hg M) := by
  have h : (affineQuasicoherentProjectionMap g hg M).hom =
      (Stacks.SheafOfModules.tensorObjIso (fppfStructurePresheaf B S hS 𝒳)
        (fppfStructurePresheaf_isSheaf B S hS 𝒳) M.obj (affinePushforwardStructureSheaf g hg)).hom ≫
        (@MonoidalCategoryStruct.whiskerRight _ _
            (fppfModulesMonoidal B S hS 𝒳).toMonoidalCategoryStruct _ _
            ((affinePullbackPushforwardAdjunction.{u, w, u} g hg).unit.app M.obj)
            (affinePushforwardStructureSheaf g hg) ≫
          directImageAct g hg ((stackModulePullback.{u, w, u} g).obj M.obj)) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ directImageAct g hg
      ((stackModulePullback.{u, w, u} g).obj M.obj))
        (Stacks.SheafOfModules.whiskerRight_comp_tensorObjIso_hom (fppfStructurePresheaf B S hS 𝒳)
          (fppfStructurePresheaf_isSheaf B S hS 𝒳)
          ((affinePullbackPushforwardAdjunction.{u, w, u} g hg).unit.app M.obj)
          (affinePushforwardStructureSheaf g hg))).trans (Category.assoc _ _ _))
  have hh : IsIso (affineQuasicoherentProjectionMap g hg M).hom := by
    rw [h]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _)
      (isIso_whiskerRight_unit_comp_directImageAct g hg M)
  have : IsIso ((ObjectProperty.ι _).map (affineQuasicoherentProjectionMap g hg M)) := hh
  exact isIso_of_fully_faithful (ObjectProperty.ι _) _

section SMul

variable {R : Type u} [CommRing R]
  (F : quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R) [F.LaxBraided] [F.Additive]

/-- **Multiplication by `c ∈ C = F(g_{QCoh,*}𝒪_U)` on `F(g_{QCoh,*}N)`**, natural in
`N ∈ QCoh(𝒪_U)`: `x ↦ F(act_N)(μ(x ⊗ c))`, for the action
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImageAct` and the tensorator of `F`
for the localized structure (I). -/
def directImageSMul (c : affineTensorAlgebra g hg F) :
    affineQuasicoherentPushforward g hg ⋙ F ⟶ affineQuasicoherentPushforward g hg ⋙ F where
  app N := ModuleCat.ofHom ((F.map (quasicoherentDirectImageAct g hg N)).hom ∘ₗ
    (Functor.LaxMonoidal.μ F ((affineQuasicoherentPushforward g hg).obj N)
      (affineQuasicoherentStructureSheaf g hg)).hom ∘ₗ (TensorProduct.mk R _ _).flip c)
  naturality N N' f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    have h1 := congrArg (fun φ => φ.hom (x ⊗ₜ c)) (Functor.LaxMonoidal.μ_natural_left F
      ((affineQuasicoherentPushforward g hg).map f) (affineQuasicoherentStructureSheaf g hg))
    have h2 := congrArg (fun φ => (F.map φ).hom ((Functor.LaxMonoidal.μ F
      ((affineQuasicoherentPushforward g hg).obj N) (affineQuasicoherentStructureSheaf g hg)).hom
        (x ⊗ₜ c))) (quasicoherentDirectImageAct_naturality f)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Functor.map_comp] at h1 h2
    exact (congrArg (F.map (quasicoherentDirectImageAct g hg N')).hom h1).trans h2

omit [F.Additive] in
/-- **On `g_{QCoh,*}𝒪_U` the multiplication by `c` is the multiplication of `C`.** -/
theorem directImageSMul_app_structureSheaf (c y : affineTensorAlgebra g hg F) :
    ((directImageSMul g hg F c).app (quasicoherentStructureSheaf.{u, w} (U := U))).hom y =
      y * c := by
  show (F.map (quasicoherentDirectImageAct g hg _)).hom
    ((Functor.LaxMonoidal.μ F _ _).hom (y ⊗ₜ c)) = _
  rw [quasicoherentDirectImageAct_structureSheaf]
  rfl

variable [PreservesFiniteColimits F] [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]

omit [PreservesFiniteColimits F] [∀ (J : Type u), PreservesColimitsOfShape (Discrete J) F] in
/-- The isomorphism `F(g_{QCoh,*}A~) ≅ A ⊗_A C` on elements. -/
theorem affineTensorFreeIso_hom_apply
    (z : (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg ⋙ F).obj
      (ModuleCat.of _ (schemeGlobalRing U))) :
    (affineTensorFreeIso g hg F).hom.hom z =
      (ModuleCat.ExtendScalars.objSelfIso (affineTensorRingHom g hg F)).inv.hom
        ((F.map ((affineQuasicoherentPushforward g hg).map
          (tildeQuasicoherentSelfIso.{u, w} U).hom)).hom z) :=
  rfl

/-- **The `R`-linear isomorphism of Stacks 0GRK is `C`-linear**: on `F(g_{QCoh,*}M~) ≅ M ⊗_A C`,
the multiplication by `c ∈ C` given by the action of `g_{QCoh,*}𝒪_U` on `g_{QCoh,*}M~`
(`AlgebraicGeometry.Stack.AlgebraicStacks.directImageSMul`) corresponds to the multiplication by
`c` on `M ⊗_A C`. -/
theorem whiskerLeft_directImageSMul_comp_affineTensorFunctorIso_hom
    (c : affineTensorAlgebra g hg F) :
    Functor.whiskerLeft (tildeQuasicoherent.{u, w} U) (directImageSMul g hg F c) ≫
        (affineTensorFunctorIso g hg F).hom =
      (affineTensorFunctorIso g hg F).hom ≫
        ModuleCat.extendScalarsSMul (affineTensorRingHom g hg F)
          (algebraMap R (affineTensorAlgebra g hg F)) c := by
  have : PreservesColimitsOfSize.{0, 0}
      (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg ⋙ F) :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} _
  refine ModuleCat.natTrans_ext_of_app_self ?_
  have hκ : (affineTensorFunctorIso g hg F).hom.app (ModuleCat.of _ (schemeGlobalRing U)) =
      (affineTensorFreeIso g hg F).hom :=
    ModuleCat.isoOfRegularAction_hom_app _ _ _ _ _ _
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  have hnat := congrArg (fun φ => φ.hom x)
    ((directImageSMul g hg F c).naturality (tildeQuasicoherentSelfIso.{u, w} U).hom)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Functor.comp_map] at hnat
  have key : (affineTensorFreeIso g hg F).hom.hom
        (((directImageSMul g hg F c).app ((tildeQuasicoherent.{u, w} U).obj
          (ModuleCat.of _ (schemeGlobalRing U)))).hom x) =
      ((ModuleCat.extendScalarsSMul (affineTensorRingHom g hg F)
        (algebraMap R (affineTensorAlgebra g hg F)) c).app
          (ModuleCat.of _ (schemeGlobalRing U))).hom
        ((affineTensorFreeIso g hg F).hom.hom x) := by
    refine (affineTensorFreeIso_hom_apply g hg F _).trans ?_
    refine (congrArg (ModuleCat.ExtendScalars.objSelfIso (affineTensorRingHom g hg F)).inv.hom
      hnat.symm).trans ?_
    refine (congrArg (ModuleCat.ExtendScalars.objSelfIso (affineTensorRingHom g hg F)).inv.hom
      (directImageSMul_app_structureSheaf g hg F c _)).trans ?_
    exact (ModuleCat.ExtendScalars.objSelfIso_inv_hom_mul _ _ c).trans
      (congrArg (fun z : (ModuleCat.extendScalars (affineTensorRingHom g hg F)).obj
            (ModuleCat.of _ (schemeGlobalRing U)) =>
        @HSMul.hSMul (affineTensorAlgebra g hg F) _ _ instHSMul c z)
        (affineTensorFreeIso_hom_apply g hg F x).symm)
  exact (congrArg (fun k => k.hom (((directImageSMul g hg F c).app
      ((tildeQuasicoherent.{u, w} U).obj (ModuleCat.of _ (schemeGlobalRing U)))).hom x)) hκ).trans
    (key.trans (congrArg (fun k => ((ModuleCat.extendScalarsSMul (affineTensorRingHom g hg F)
      (algebraMap R (affineTensorAlgebra g hg F)) c).app
        (ModuleCat.of _ (schemeGlobalRing U))).hom (k.hom x)) hκ.symm))

/-- `κ(c · z) = c • κ(z)` on elements. -/
theorem affineTensorFunctorIso_hom_app_directImageSMul (c : affineTensorAlgebra g hg F)
    (M : ModuleCat.{u} (schemeGlobalRing U))
    (z : (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg ⋙ F).obj M) :
    ((affineTensorFunctorIso g hg F).hom.app M).hom
        (((directImageSMul g hg F c).app ((tildeQuasicoherent.{u, w} U).obj M)).hom z) =
      @HSMul.hSMul (affineTensorAlgebra g hg F)
        ((ModuleCat.extendScalars (affineTensorRingHom g hg F)).obj M) _ instHSMul c
        (((affineTensorFunctorIso g hg F).hom.app M).hom z) :=
  congrArg (fun φ => (φ.app M).hom z)
    (whiskerLeft_directImageSMul_comp_affineTensorFunctorIso_hom g hg F c)

/-- **`c ↦ (multiplication by c)` is an action of `C`** on `F(g_{QCoh,*}M~)`. -/
theorem directImageSMul_mul_app_tilde (c c' : affineTensorAlgebra g hg F)
    (M : ModuleCat.{u} (schemeGlobalRing U))
    (z : (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg ⋙ F).obj M) :
    ((directImageSMul g hg F (c' * c)).app ((tildeQuasicoherent.{u, w} U).obj M)).hom z =
      ((directImageSMul g hg F c).app ((tildeQuasicoherent.{u, w} U).obj M)).hom
        (((directImageSMul g hg F c').app ((tildeQuasicoherent.{u, w} U).obj M)).hom z) := by
  refine (ConcreteCategory.bijective_of_isIso
    ((affineTensorFunctorIso g hg F).hom.app M)).1 ?_
  refine (affineTensorFunctorIso_hom_app_directImageSMul g hg F _ M z).trans ?_
  refine Eq.trans ?_ (affineTensorFunctorIso_hom_app_directImageSMul g hg F c M _).symm
  refine Eq.trans ?_ (congrArg
    (fun y : (ModuleCat.extendScalars (affineTensorRingHom g hg F)).obj M =>
    @HSMul.hSMul (affineTensorAlgebra g hg F) _ _ instHSMul c y)
      (affineTensorFunctorIso_hom_app_directImageSMul g hg F c' M z).symm)
  exact (congrArg (fun d : affineTensorAlgebra g hg F => @HSMul.hSMul (affineTensorAlgebra g hg F)
      ((ModuleCat.extendScalars (affineTensorRingHom g hg F)).obj M) _ instHSMul d
        (((affineTensorFunctorIso g hg F).hom.app M).hom z)) (mul_comm c' c)).trans
    (mul_smul c c' _)

omit [F.Additive] [PreservesFiniteColimits F]
  [∀ (J : Type u), PreservesColimitsOfShape (Discrete J) F] in
/-- **`F` of the projection map on `μ(m ⊗ y)` is the multiplication by `y` of `F(η)(m)`.** -/
theorem map_affineQuasicoherentProjectionMap_μ (M : quasicoherentModules B S hS 𝒳) (m : F.obj M)
    (y : affineTensorAlgebra g hg F) :
    (F.map (affineQuasicoherentProjectionMap g hg M)).hom
        ((Functor.LaxMonoidal.μ F M (affineQuasicoherentStructureSheaf g hg)).hom (m ⊗ₜ y)) =
      ((directImageSMul g hg F y).app (quasicoherentPullbackObj B S hS g M)).hom
        ((F.map (affineQuasicoherentUnit g hg M)).hom m) := by
  have h1 := congrArg (fun φ => φ.hom (m ⊗ₜ y)) (Functor.LaxMonoidal.μ_natural_left F
    (affineQuasicoherentUnit g hg M) (affineQuasicoherentStructureSheaf g hg))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [affineQuasicoherentProjectionMap, F.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    ← h1]
  rfl

end SMul

end AlgebraicGeometry.Stack.AlgebraicStacks
