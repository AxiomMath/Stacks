module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelToPointPullback

/-!
# Inverse images to a point commute with base change of the base ring

Let `f : X ⟶ Y` be a morphism of ringed topoi presented by a functor of sites `u`, let `T_X` and
`T_Y` be terminal objects of the two sites with `u(T_Y)` terminal, and let
`p_Y : Y ⟶ (pt, A)` and `p_X : X ⟶ (pt, A')` be the morphisms to punctual ringed topoi given by
ring maps `φ_Y : A ⟶ 𝒪_Y(T_Y)` and `φ_X : A' ⟶ 𝒪_X(T_X)`. If a ring map `ψ : A ⟶ A'` makes the
square of rings

`A ⟶ 𝒪_Y(T_Y) ⟶ 𝒪_X(u T_Y)` and `A ⟶ A' ⟶ 𝒪_X(T_X) ⟶ 𝒪_X(u T_Y)`

commute, then

`f^*(p_Y^* M) ≅ p_X^*(A' ⊗_A M)`

naturally in the `A`-module `M`. Both sides are left adjoint to the functor taking a sheaf of
modules `F` on `X` to its sections over `u(T_Y) ≅ T_X`, read as an `A`-module; so the
isomorphism is the uniqueness of left adjoints.

## Main definitions

* `AlgebraicGeometry.toPointPushforwardCompIso`: the two direct images agree.
* `AlgebraicGeometry.toPointPullbackCompIso`: the inverse images agree.
* `AlgebraicGeometry.Space.spacesEtaleModelToPointPullbackCompIso`: the case of the model of a
  morphism `g : X' ⟶ X` of algebraic spaces, with ring maps `A ⟶ Γ(X, 𝒪_X)`, `A' ⟶ Γ(X', 𝒪_{X'})`
  compatible with `g^*`: `g^*(𝒪_X ⊗_A M) ≅ 𝒪_{X'} ⊗_{A'} (A' ⊗_A M)`.

## Main results

* `AlgebraicGeometry.Space.isTerminal_smallModelBaseChange_obj_terminal`: base change carries the
  terminal object of the model to a terminal object.
* `AlgebraicGeometry.Space.fSharp_spacesEtaleModelGlobalHom_apply`: the structure map of the model
  of `g` over the terminal object is pullback of global functions along `g`.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) {TX : X.C} (hTX : IsTerminal TX) {TY : Y.C}
  (hu : IsTerminal (f.u.obj TY))
  {A A' : Type u} [CommRing A] [CommRing A'] (ψ : A →+* A')
  (φY : CommRingCat.of A ⟶ Y.O.obj.obj (op TY)) (φX : CommRingCat.of A' ⟶ X.O.obj.obj (op TX))
  (hφ : φY ≫ f.fSharp.hom.app (op TY) =
    CommRingCat.ofHom ψ ≫ φX ≫ X.O.obj.map (hTX.from (f.u.obj TY)).op)

/-- The sections over `u(T_Y)` of a sheaf of modules on `X`, read as an `A`-module through
`f^♯ ∘ φ_Y`, are its sections over `T_X`, read as an `A`-module through `φ_X ∘ ψ`. -/
def toPointPushforwardCompLinearEquiv
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ((f.pushforwardTopos ⋙ (toPointRingedTopos Y φY).pushforwardTopos ⋙
        Stacks.PointRingedSite.ev (CommRingCat.of A) ⋙
          (Space.pointModuleCatEquiv (R := A)).functor).obj M) ≃ₗ[A]
      (((toPointRingedTopos X φX).pushforwardTopos ⋙
        Stacks.PointRingedSite.ev (CommRingCat.of A') ⋙
          (Space.pointModuleCatEquiv (R := A')).functor ⋙ ModuleCat.restrictScalars ψ).obj M) where
  toFun x := M.val.map (hu.from TX).op x
  invFun y := M.val.map (hTX.from (f.u.obj TY)).op y
  map_add' x y := (M.val.map (hu.from TX).op).hom.map_add x y
  map_smul' a x := by
    refine (M.val.map_smul (hu.from TX).op (f.fSharp.hom.app (op TY) (φY a)) x).trans ?_
    have h := congrArg (fun k => X.O.obj.map (hu.from TX).op k)
      (ConcreteCategory.congr_hom hφ a)
    refine congrArg (fun r => r • M.val.map (hu.from TX).op x) (h.trans ?_)
    refine (ConcreteCategory.congr_hom (X.O.obj.map_comp _ _).symm _).trans ?_
    refine (congrArg (fun k => (X.O.obj.map k) (φX (ψ a)))
      (show (hTX.from (f.u.obj TY)).op ≫ (hu.from TX).op = 𝟙 (op TX) from
        Quiver.Hom.unop_inj (hTX.hom_ext _ _))).trans ?_
    exact ConcreteCategory.congr_hom (X.O.obj.map_id _) _
  left_inv x := by
    let x' : M.val.obj (op (f.u.obj TY)) := x
    refine (PresheafOfModules.map_comp_apply M.val (hu.from TX).op (hTX.from (f.u.obj TY)).op
      x').symm.trans ?_
    refine (congrArg (fun k => M.val.map k x')
      (show (hu.from TX).op ≫ (hTX.from (f.u.obj TY)).op = 𝟙 _ from
        Quiver.Hom.unop_inj (hu.hom_ext _ _))).trans ?_
    exact congrArg (fun g => g.hom x') (M.val.map_id _)
  right_inv y := by
    let y' : M.val.obj (op TX) := y
    refine (PresheafOfModules.map_comp_apply M.val (hTX.from (f.u.obj TY)).op (hu.from TX).op
      y').symm.trans ?_
    refine (congrArg (fun k => M.val.map k y')
      (show (hTX.from (f.u.obj TY)).op ≫ (hu.from TX).op = 𝟙 _ from
        Quiver.Hom.unop_inj (hTX.hom_ext _ _))).trans ?_
    exact congrArg (fun g => g.hom y') (M.val.map_id _)

/-- **The two direct images to the point of `A` agree**: sections over `u(T_Y)` through `f^♯ φ_Y`,
and sections over `T_X` through `φ_X ψ`. -/
def toPointPushforwardCompIso :
    (toPointRingedTopos X φX).pushforwardTopos ⋙
        Stacks.PointRingedSite.ev (CommRingCat.of A') ⋙
          (Space.pointModuleCatEquiv (R := A')).functor ⋙ ModuleCat.restrictScalars ψ ≅
      f.pushforwardTopos ⋙ (toPointRingedTopos Y φY).pushforwardTopos ⋙
        Stacks.PointRingedSite.ev (CommRingCat.of A) ⋙
          (Space.pointModuleCatEquiv (R := A)).functor :=
  NatIso.ofComponents
    (fun M => (toPointPushforwardCompLinearEquiv f hTX hu ψ φY φX hφ M).toModuleIso.symm)
    (fun {M N} g => by
      ext x
      exact (ConcreteCategory.congr_hom (g.val.naturality (hTX.from (f.u.obj TY)).op) x).symm)

/-- **Inverse images to a point commute with base change of the base ring**:
`f^*(p_Y^* M) ≅ p_X^*(A' ⊗_A M)`, both being left adjoint to sections over `u(T_Y) ≅ T_X` read as
`A`-modules. -/
def toPointPullbackCompIso :
    (Space.pointModuleCatEquiv (R := A)).inverse ⋙
        (Stacks.PointRingedSite.modulesEquiv (CommRingCat.of A)).inverse ⋙
          (toPointRingedTopos Y φY).pullbackTopos ⋙ f.pullbackTopos ≅
      ModuleCat.extendScalars ψ ⋙ (Space.pointModuleCatEquiv (R := A')).inverse ⋙
        (Stacks.PointRingedSite.modulesEquiv (CommRingCat.of A')).inverse ⋙
          (toPointRingedTopos X φX).pullbackTopos :=
  ((Space.pointModuleCatEquiv (R := A)).symm.toAdjunction.comp
    ((Stacks.PointRingedSite.modulesEquiv (CommRingCat.of A)).symm.toAdjunction.comp
      ((toPointRingedTopos Y φY).pullbackPushforwardAdjunctionTopos.comp
        f.pullbackPushforwardAdjunctionTopos))).leftAdjointUniq
    (((ModuleCat.extendRestrictScalarsAdj ψ).comp
      ((Space.pointModuleCatEquiv (R := A')).symm.toAdjunction.comp
        ((Stacks.PointRingedSite.modulesEquiv (CommRingCat.of A')).symm.toAdjunction.comp
          (toPointRingedTopos X φX).pullbackPushforwardAdjunctionTopos))).ofNatIsoRight
      (toPointPushforwardCompIso f hTX hu ψ φY φX hφ))

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)

/-- Base change along `g : X' ⟶ X` carries the terminal object of the model of the spaces-étale
site of `X` to a terminal object: the base change of `X` itself is `X ×_X X' ≅ X'`. -/
def isTerminal_smallModelBaseChange_obj_terminal :
    IsTerminal ((smallModelBaseChange B S hS g).obj (spacesEtaleModelTerminal B S hS X)) := by
  have hW : IsTerminal ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj
      (spacesEtaleModelTerminal B S hS X)) :=
    (isTerminal_spacesEtaleModelTerminal B S hS X).isTerminalObj _
  have h₀ : IsTerminal ((spacesBaseChange B S hS g).functor.obj (SpacesEtale.idObj B S hS X)) :=
    SpacesEtale.isTerminal_of_isIso B S hS _
      (by change IsIso (pullback.snd (𝟙 X) g); infer_instance)
  exact (h₀.ofIso ((spacesBaseChange B S hS g).functor.mapIso
    (hW.uniqueUpToIso (SpacesEtale.isTerminal_idObj B S hS X)).symm)).isTerminalObj _

/-- A morphism to the terminal object `X` of the spaces-étale site of `X` is, on algebraic
spaces, the structure morphism of its source. -/
theorem toSpaces_map_to_idObj {U : SpacesEtale B S hS X} (m : U ⟶ SpacesEtale.idObj B S hS X) :
    (SpacesEtale.toSpaces B S hS X).map m = U.1.hom :=
  (Category.comp_id _).symm.trans (Over.w m.hom)

variable {A A' : Type u} [CommRing A] [CommRing A']
  (ψ : A →+* (SpacesEtale.structurePresheaf B S hS X).obj (op (SpacesEtale.idObj B S hS X)))
  (ψ' : A' →+* (SpacesEtale.structurePresheaf B S hS X').obj (op (SpacesEtale.idObj B S hS X')))
  (α : A →+* A') (hψ : ∀ a, globalFunctionsMap B S hS g (ψ a) = ψ' (α a))

include hψ in
/-- The structure map of the model of `g` over the terminal object, after a ring map
`ψ : A ⟶ Γ(X, 𝒪_X)`, is `A ⟶ A' ⟶ Γ(X', 𝒪_{X'})` restricted to the base change of the terminal
object, as soon as `ψ' ∘ α` is the pullback of `ψ` along `g`. -/
theorem fSharp_spacesEtaleModelGlobalHom_apply (r : A) :
    (spacesEtaleModelHom B S hS g).fSharp.hom.app (op (spacesEtaleModelTerminal B S hS X))
      (spacesEtaleModelGlobalHom B S hS (R := CommRingCat.of A) ψ r) =
    (spacesEtaleModelStructureSheaf B S hS X').obj.map
        ((isTerminal_spacesEtaleModelTerminal B S hS X').from
          ((smallModelBaseChange B S hS g).obj (spacesEtaleModelTerminal B S hS X))).op
      (spacesEtaleModelGlobalHom B S hS (R := CommRingCat.of A') ψ' (α r)) := by
  apply (Shrink.ringEquiv.{u, u + 1} _).injective
  let eX := equivSmallModel.{u} (SpacesEtale B S hS X)
  let eX' := equivSmallModel.{u} (SpacesEtale B S hS X')
  let W := eX.inverse.obj (spacesEtaleModelTerminal B S hS X)
  let Z := eX'.inverse.obj (eX'.functor.obj ((spacesBaseChange B S hS g).functor.obj W))
  let σ : globalFunctions' B S hS X.1 := ψ r
  let t₁ := (SpacesEtale.toSpaces B S hS X').map (eX'.unitIso.inv.app
    ((spacesBaseChange B S hS g).functor.obj W))
  let pr := (spacesBaseChange B S hS g).projection.app W
  let t₀ := (SpacesEtale.toSpaces B S hS X).map (eX.unitIso.inv.app (SpacesEtale.idObj B S hS X))
  let t₃ := (SpacesEtale.toSpaces B S hS X').map (eX'.inverse.map
    ((isTerminal_spacesEtaleModelTerminal B S hS X').from
      ((smallModelBaseChange B S hS g).obj (spacesEtaleModelTerminal B S hS X))))
  let t₂ := (SpacesEtale.toSpaces B S hS X').map (eX'.unitIso.inv.app (SpacesEtale.idObj B S hS X'))
  have hL : t₁ ≫ pr ≫ t₀ = Z.1.hom ≫ g := by
    refine (congrArg (fun k => t₁ ≫ pr ≫ k) (toSpaces_map_to_idObj B S hS _)).trans ?_
    refine (congrArg (fun k => t₁ ≫ k) ((spacesBaseChange B S hS g).isPullback W).w).trans ?_
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ g) (Over.w (eX'.unitIso.inv.app _).hom))
  have hR : t₃ ≫ t₂ ≫ g = Z.1.hom ≫ g :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ g)
      (((SpacesEtale.toSpaces B S hS X').map_comp _ _).symm.trans
        (toSpaces_map_to_idObj B S hS _)))
  have h := RingHom.congr_fun (congrArg (globalFunctionsMap B S hS (U := X)
    (V := (SpacesEtale.toSpaces B S hS X').obj Z)) (hL.trans hR.symm)) σ
  have e₁ : Shrink.ringEquiv.{u, u + 1} _
        (spacesEtaleModelGlobalHom B S hS (R := CommRingCat.of A) ψ r) =
      globalFunctionsMap B S hS t₀ σ :=
    (Shrink.ringEquiv.{u, u + 1} _).apply_symm_apply _
  let y := spacesEtaleModelGlobalHom B S hS (R := CommRingCat.of A') ψ' (α r)
  have e₂ : Shrink.ringEquiv.{u, u + 1} _ y =
      globalFunctionsMap B S hS t₂ (globalFunctionsMap B S hS g σ) :=
    ((Shrink.ringEquiv.{u, u + 1} _).apply_symm_apply _).trans
      (congrArg (globalFunctionsMap B S hS _) (hψ r).symm)
  have e₃ : Shrink.ringEquiv.{u, u + 1} _ ((spacesEtaleModelStructureSheaf B S hS X').obj.map
        ((isTerminal_spacesEtaleModelTerminal B S hS X').from
          ((smallModelBaseChange B S hS g).obj (spacesEtaleModelTerminal B S hS X))).op y) =
      globalFunctionsMap B S hS t₃ (Shrink.ringEquiv.{u, u + 1} _ y) :=
    shrinkCommRingPresheaf_map_apply.{u, u + 1} _ _ _
  refine ((Shrink.ringEquiv.{u, u + 1} _).apply_symm_apply _).trans ?_
  refine Eq.trans ?_ e₃.symm
  refine Eq.trans ?_ (congrArg (globalFunctionsMap B S hS _) e₂).symm
  refine (RingHom.comp_apply _ _ _).trans ?_
  refine (congrArg ((spacesEtaleBaseChangeSharp B S hS g).app (op W)).hom e₁).trans ?_
  refine Eq.trans ?_ (h.trans ?_)
  · exact ((RingHom.congr_fun (globalFunctionsMap_comp B S hS t₁ (pr ≫ t₀)) σ).trans
      (congrArg (globalFunctionsMap B S hS t₁)
        (RingHom.congr_fun (globalFunctionsMap_comp B S hS pr t₀) σ))).symm
  · exact (RingHom.congr_fun (globalFunctionsMap_comp B S hS t₃ (t₂ ≫ g)) σ).trans
      (congrArg (globalFunctionsMap B S hS t₃)
        (RingHom.congr_fun (globalFunctionsMap_comp B S hS t₂ g) σ))

include hψ in
/-- **Inverse images to points commute with base change along a morphism of algebraic spaces**:
for `g : X' ⟶ X`, ring maps `ψ : A ⟶ Γ(X, 𝒪_X)`, `ψ' : A' ⟶ Γ(X', 𝒪_{X'})` and `α : A ⟶ A'` with
`ψ' ∘ α = g^* ∘ ψ`, on the models of the spaces-étale sites
`g^*(𝒪_X ⊗_A M) ≅ 𝒪_{X'} ⊗_{A'} (A' ⊗_A M)`. -/
def spacesEtaleModelToPointPullbackCompIso :
    (pointModuleCatEquiv (R := A)).inverse ⋙
        (Stacks.PointRingedSite.modulesEquiv (CommRingCat.of A)).inverse ⋙
          (spacesEtaleModelToPoint B S hS (R := CommRingCat.of A) ψ).pullbackTopos ⋙
            (spacesEtaleModelHom B S hS g).pullbackTopos ≅
      ModuleCat.extendScalars α ⋙ (pointModuleCatEquiv (R := A')).inverse ⋙
        (Stacks.PointRingedSite.modulesEquiv (CommRingCat.of A')).inverse ⋙
          (spacesEtaleModelToPoint B S hS (R := CommRingCat.of A') ψ').pullbackTopos :=
  toPointPullbackCompIso (spacesEtaleModelHom B S hS g)
    (isTerminal_spacesEtaleModelTerminal B S hS X')
    (isTerminal_smallModelBaseChange_obj_terminal B S hS g) α _ _
    (CommRingCat.hom_ext (RingHom.ext fun a =>
      fSharp_spacesEtaleModelGlobalHom_apply B S hS g ψ ψ' α hψ a))

end Space

end AlgebraicGeometry

end
