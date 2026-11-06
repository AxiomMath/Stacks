module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffineRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffineBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.CartesianQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCokernelDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentDirectImage

/-!
# The direct image along an affine morphism out of an affine scheme preserves quasi-coherence

Let `g : U ⟶ 𝒳` be an affine 1-morphism from (the algebraic stack of) a scheme `U` to an algebraic
stack `𝒳`, with right adjoint `r : 𝒳 ⥤ Sch/U`, `x ↦ U ×_𝒳 x`.  The direct image `g_*`
(`affinePushforward`) preserves cartesianness on affine objects, because `U ×_𝒳 x` is affine over
`x` and its formation commutes with base change; hence it preserves quasi-coherence.  This is the
quasi-coherent direct image `g_{QCoh,*}` of Stacks 077A for an affine morphism, for which the
coherator is not needed (Stacks 0GQY).

All names are in the namespace `AlgebraicGeometry.Stack`.

## Main definitions

* `affineQuasicoherentPushforward`: the quasi-coherent direct image `g_{QCoh,*}`, the restriction
  of `g_*` to quasi-coherent modules.

## Main results

* `isAffineOver_affineRightAdjoint_obj`: `U ×_𝒳 x` is affine when `x` lies over an affine scheme.
* `isCartesianOnAffines_affinePushforward`: `g_*` preserves cartesianness on affine objects.
* `isQuasicoherentOnSite_affinePushforward`: `g_*` preserves quasi-coherence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u w

namespace AlgebraicGeometry.Stack

local notation "𝒪[" Y "]" => AlgebraicStacks.fppfStructureRingSheaf _ _ _ Y

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hg : AlgebraicStacks.IsAffineHom B S hS g)

/-- The projection `U ×_𝒳 x ⟶ p x` underlying the counit of `g ⊣ r`. -/
noncomputable abbrev affineProjection (x : 𝒳.val.val.obj) :
    ((affineRightAdjoint g hg).obj x).left ⟶ 𝒳.val.val.p.obj x :=
  Functor.counitBase 𝒳.val.val.p g.hom.hom.toFunctor g.hom.hom.w (affineAdjunction g hg) x

/-- The projection `U ×_𝒳 x ⟶ p x` is an affine morphism of schemes. -/
theorem isAffineHom_affineProjection (x : 𝒳.val.val.obj) :
    _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (affineProjection g hg x)) := by
  have := isAffineHom_map_affineAdjunction_counit g hg x
  simp only [affineProjection, Functor.counitBase, Functor.map_comp]
  infer_instance

/-- **`U ×_𝒳 x` is affine as soon as `x` lies over an affine scheme.** -/
theorem isAffineOver_affineRightAdjoint_obj (x : 𝒳.val.val.obj)
    (hx : IsAffineOver B S hS (𝒳.val.val.p.obj x)) :
    IsAffineOver B S hS ((affineRightAdjoint g hg).obj x).left := by
  have := isAffineHom_affineProjection g hg x
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) := hx
  exact isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (affineProjection g hg x))

/-- **The square `U ×_𝒳 x' ⟶ U ×_𝒳 x` over `p x' ⟶ p x` is a pullback of schemes.** -/
theorem isPullback_toScheme_affineProjection {x x' : 𝒳.val.val.obj} (φ : x' ⟶ x) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (affineProjection g hg x'))
      ((BigFppfOver.toScheme B S hS).map ((affineRightAdjoint g hg).map φ).left)
      ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ))
      ((BigFppfOver.toScheme B S hS).map (affineProjection g hg x)) :=
  ((Functor.isPullback_counitBase 𝒳.val.val.p g.hom.hom.toFunctor g.hom.hom.w
    (affineAdjunction g hg) 𝒳.val.isFiberedInGroupoids φ).map
      (BigFppfOver.toScheme B S hS)).flip

omit g in
/-- The global functions of an `eqToHom` of the big fppf category are an `eqToHom`. -/
theorem appTop_toScheme_map_eqToHom {X Y : BigFppfOver B S hS} (h : X = Y) :
    ((BigFppfOver.toScheme B S hS).map (eqToHom h)).appTop =
      eqToHom (by subst h; rfl) := by
  subst h
  simp

/-- The comorphism of `r` at `x` is the map of global functions of the projection
`U ×_𝒳 x ⟶ p x`. -/
theorem pushforwardCommRingHom_app (x : 𝒳.val.val.obj) :
    ((pushforwardCommRingHom g hg).app (op x)).hom =
      ((BigFppfOver.toScheme B S hS).map (affineProjection g hg x)).appTop.hom := by
  simp only [pushforwardCommRingHom, NatTrans.comp_app, Functor.whiskerRight_app,
    NatTrans.op_app, eqToHom_app, affineProjection, Functor.counitBase, Functor.map_comp,
    Scheme.Hom.comp_appTop, appTop_toScheme_map_eqToHom]
  rfl

/-- The comorphisms of `r` are natural: `𝒪(x) ⟶ 𝒪(r x)` commutes with restriction. -/
theorem pushforwardCommRingHom_naturality {x x' : 𝒳.val.val.obj} (φ : x' ⟶ x) :
    ((pushforwardCommRingHom g hg).app (op x')).hom.comp
        ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ)).appTop.hom =
      ((BigFppfOver.toScheme B S hS).map ((affineRightAdjoint g hg).map φ).left).appTop.hom.comp
        ((pushforwardCommRingHom g hg).app (op x)).hom :=
  congrArg CommRingCat.Hom.hom ((pushforwardCommRingHom g hg).naturality φ.op)

/-- **The direct image along an affine morphism preserves cartesianness on affine objects.** -/
theorem isCartesianOnAffines_affinePushforward
    (N : SheafOfModules.{u} 𝒪[schemeStack.{u, w} B S hS U])
    (hN : FibredSite.IsCartesianOnAffines (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids
      N.val) :
    FibredSite.IsCartesianOnAffines 𝒳.val.isFiberedInGroupoids
      ((affinePushforward.{u, w, u} g hg).obj N).val := by
  intro x x' φ hx hx'
  have hA := isAffineOver_affineRightAdjoint_obj g hg x hx
  have hB := isAffineOver_affineRightAdjoint_obj g hg x' hx'
  have hcart := hN ((affineRightAdjoint g hg).map φ) hA hB
  have hp𝒳 := 𝒳.val.isFiberedInGroupoids
  have hp𝒰 := (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids
  let r := affineRightAdjoint g hg
  let iRS : Algebra Γ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x'), ⊤) :=
    FibredSite.sectionAlgebra hp𝒳 φ
  let iRA : Algebra Γ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (r.obj x).left, ⊤) :=
    ((pushforwardCommRingHom g hg).app (op x)).hom.toAlgebra
  let iAB : Algebra Γ((BigFppfOver.toScheme B S hS).obj (r.obj x).left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (r.obj x').left, ⊤) :=
    FibredSite.sectionAlgebra hp𝒰 (r.map φ)
  let iSB : Algebra Γ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x'), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (r.obj x').left, ⊤) :=
    ((pushforwardCommRingHom g hg).app (op x')).hom.toAlgebra
  let iRB : Algebra Γ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (r.obj x').left, ⊤) :=
    (((pushforwardCommRingHom g hg).app (op x')).hom.comp
      ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ)).appTop.hom).toAlgebra
  have : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x'), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (r.obj x').left, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (r.obj x).left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (r.obj x').left, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun c =>
      DFunLike.congr_fun (pushforwardCommRingHom_naturality g hg φ) c)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) := hx
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x')) := hx'
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (r.obj x).left) := hA
  have : Algebra.IsPushout Γ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x'), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (r.obj x).left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (r.obj x').left, ⊤) :=
    algebra_isPushout_appTop_of_isPullback (isPullback_toScheme_affineProjection g hg φ)
      rfl (pushforwardCommRingHom_app g hg x) (pushforwardCommRingHom_app g hg x') rfl
  let iMR : Module Γ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x), ⊤)
      (((affinePushforward.{u, w, u} g hg).obj N).val.obj (op x)) :=
    FibredSite.sectionModule hp𝒳 _ x
  let iMA : Module Γ((BigFppfOver.toScheme B S hS).obj (r.obj x).left, ⊤)
      (((affinePushforward.{u, w, u} g hg).obj N).val.obj (op x)) :=
    FibredSite.sectionModule hp𝒰 N.val (r.obj x)
  have : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (r.obj x).left, ⊤)
      (((affinePushforward.{u, w, u} g hg).obj N).val.obj (op x)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let e := Algebra.IsPushout.cancelBaseChange
    Γ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x), ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x'), ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj (r.obj x).left, ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj (r.obj x').left, ⊤)
    (((affinePushforward.{u, w, u} g hg).obj N).val.obj (op x))
  let : Module (FibredSite.sectionRing hp𝒳 x')
      (((affinePushforward.{u, w, u} g hg).obj N).val.obj (op x')) :=
    FibredSite.sectionModule hp𝒳 _ x'
  let : Module (FibredSite.sectionRing hp𝒰 (r.obj x')) (N.val.obj (op (r.obj x'))) :=
    FibredSite.sectionModule hp𝒰 N.val (r.obj x')
  let F := FibredSite.restrictionBaseChangeMap hp𝒳
    ((affinePushforward.{u, w, u} g hg).obj N).val φ
  let G := FibredSite.restrictionBaseChangeMap hp𝒰 N.val (r.map φ)
  have key : ∀ z, F z = G (e.symm z) := by
    intro z
    induction z with
    | tmul s m =>
      rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
      rfl
    | add z z' hz hz' =>
      exact (F.map_add z z').trans ((congrArg₂ (· + ·) hz hz').trans
        ((congrArg G (e.symm.map_add z z')).trans (G.map_add _ _)).symm)
  have hfun : ⇑F = ⇑G ∘ ⇑e.symm := funext key
  rw [hfun]
  exact hcart.comp e.symm.bijective

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack

local notation "𝒪[" Y "]" => AlgebraicStacks.fppfStructureRingSheaf _ _ _ Y

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hg : AlgebraicStacks.IsAffineHom B S hS g)

/-- **The direct image along an affine morphism out of a scheme preserves quasi-coherence**
(Stacks 0GQY, the part used by Stacks 0GRK). -/
theorem isQuasicoherentOnSite_affinePushforward
    (N : SheafOfModules.{u} 𝒪[schemeStack.{u, w} B S hS U]) (hN : N.IsQuasicoherentOnSite) :
    ((affinePushforward.{u, w, u} g hg).obj N).IsQuasicoherentOnSite :=
  FibredSite.isQuasicoherentOnSite_of_isCartesianOnAffines 𝒳.val.isFiberedInGroupoids _
    (isCartesianOnAffines_affinePushforward g hg N
      (FibredSite.isCartesianOnAffines_of_isQuasicoherentOnSite
        (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids N hN))

/-- **Stacks 077A for an affine 1-morphism `g : U ⟶ 𝒳` out of a scheme: the quasi-coherent direct
image `g_{QCoh,*} : QCoh(𝒪_U) ⥤ QCoh(𝒪_𝒳)`.**  For an affine `g` the direct image of modules `g_*`
already preserves quasi-coherence
(`AlgebraicGeometry.Stack.isQuasicoherentOnSite_affinePushforward`), so the coherator of the
source's construction `Q ∘ g_* ∘ i` is the identity on it and `g_{QCoh,*}` is the restriction of
`g_*` to quasi-coherent modules. -/
noncomputable def affineQuasicoherentPushforward :
    AlgebraicStacks.quasicoherentModules B S hS (schemeStack.{u, w} B S hS U) ⥤
      AlgebraicStacks.quasicoherentModules B S hS 𝒳 :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ affinePushforward.{u, w, u} g hg)
    (fun N => isQuasicoherentOnSite_affinePushforward g hg N.obj N.property)

/-- `g_{QCoh,*}` is `g_*` on underlying sheaves of modules. -/
noncomputable def affineQuasicoherentPushforwardCompι :
    affineQuasicoherentPushforward g hg ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ affinePushforward.{u, w, u} g hg :=
  ObjectProperty.liftCompιIso _ _ _

end AlgebraicGeometry.Stack
