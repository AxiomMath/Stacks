module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseLiftFunctor
public import Mathlib.Algebra.Module.Shrink
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseLift

/-!
# Shrinking the universe of a sheaf of modules with small sections

Let `G` be a (pre)sheaf of modules over `R₁` whose sections are `w`-small, and let
`ρ : R₀ ⟶ R₁` be a family of ring maps commuting with restriction. Replacing each section module
by its `Shrink` and letting `R₀` act through `ρ` gives a (pre)sheaf of modules over `R₀` with
sections in `w`. For `ρ` the identity its universe lift is `G` again, and for `ρ` the inclusion
of the structure sheaf of a ringed site into its universe lift, its lift
`Stacks.SheafOfModules.CoherentLift.liftModule` is `G` again. So the essential images of the two
universe lifts consist exactly of the sheaves of modules with small sections.

## Main definitions

* `PresheafOfModules.shrinkObjAlong` and `SheafOfModules.shrinkObj`: the shrink, over `R₀`.
* `SheafOfModules.uliftShrinkIso`: the universe lift of the shrink over the same ring is `G`.
* `Stacks.SheafOfModules.CoherentLift.liftModuleShrinkIso`: the lift of the shrink of a sheaf
  of modules over the lifted structure sheaf is the sheaf itself.

## Main results

* `SheafOfModules.mem_essImage_uliftFunctor`: a sheaf of modules with small sections is a
  universe lift.
* `Stacks.SheafOfModules.CoherentLift.mem_essImage_liftModuleFunctor`: a sheaf of modules over
  the lifted structure sheaf with small sections is in the essential image of
  `Stacks.SheafOfModules.CoherentLift.liftModuleFunctor`.

## Implementation notes

The restriction maps of `G` land in a module with restricted scalars, whose carrier is that of
the target only up to unfolding; `PresheafOfModules.resMap` reads them with a declared codomain
so that `Equiv.symm_apply_apply` can be rewritten under them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v₁ u₁ r₀ r₁

namespace PresheafOfModules

section Shrink

variable {C : Type u₁} [Category.{v₁} C] {R₀ : Cᵒᵖ ⥤ RingCat.{r₀}} {R₁ : Cᵒᵖ ⥤ RingCat.{r₁}}
  (ρ : ∀ V, R₀.obj V →+* R₁.obj V)
  (hρ : ∀ {V W : Cᵒᵖ} (f : V ⟶ W) (a : R₀.obj V), ρ W (R₀.map f a) = R₁.map f (ρ V a))
  (G : PresheafOfModules.{w'} R₁) [∀ V, Small.{w} (G.obj V)]

/-- The module over `R₀(V)` with underlying group `Shrink (G(V))`, scalars acting through `ρ`. -/
def shrinkModule (V : Cᵒᵖ) : ModuleCat.{w} (R₀.obj V) :=
  letI : Module (R₀.obj V) (Shrink.{w} (G.obj V)) := Module.compHom _ (ρ V)
  ModuleCat.of (R₀.obj V) (Shrink.{w} (G.obj V))

/-- A scalar of `R₀(V)` acts on `shrinkModule ρ G V` as its image under `ρ` acts on `G(V)`. -/
theorem shrinkModule_smul (V : Cᵒᵖ) (a : R₀.obj V) (x : shrinkModule.{w} ρ G V) :
    a • x = equivShrink.{w} _ (ρ V a • (equivShrink.{w} _).symm x) := rfl

omit [∀ V, Small.{w} (G.obj V)] in
/-- The restriction map of `G`, with its codomain spelled as the sections of `G`. -/
def resMap {V W : Cᵒᵖ} (f : V ⟶ W) (y : G.obj V) : G.obj W := G.map f y

omit [∀ V, Small.{w} (G.obj V)] in
/-- `resMap G f` is additive. -/
theorem resMap_add {V W : Cᵒᵖ} (f : V ⟶ W) (y z : G.obj V) :
    resMap G f (y + z) = resMap G f y + resMap G f z := map_add (G.map f).hom y z

omit [∀ V, Small.{w} (G.obj V)] in
/-- `resMap G f` is semilinear along the restriction map `R₁.map f`. -/
theorem resMap_smul {V W : Cᵒᵖ} (f : V ⟶ W) (r : R₁.obj V) (y : G.obj V) :
    resMap G f (r • y) = R₁.map f r • resMap G f y := G.map_smul f r y

omit [∀ V, Small.{w} (G.obj V)] in
/-- The restriction map along the identity is the identity. -/
theorem resMap_id (V : Cᵒᵖ) (y : G.obj V) : resMap G (𝟙 V) y = y := by
  unfold resMap
  rw [G.map_id]
  rfl

omit [∀ V, Small.{w} (G.obj V)] in
/-- The restriction map along `f ≫ g` is the composite of those along `f` and `g`. -/
theorem resMap_comp {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (y : G.obj U) :
    resMap G (f ≫ g) y = resMap G g (resMap G f y) := G.map_comp_apply f g y

/-- The restriction maps of `shrinkObjAlong`, on underlying types. -/
def shrinkMap {V W : Cᵒᵖ} (f : V ⟶ W) (x : Shrink.{w} (G.obj V)) : Shrink.{w} (G.obj W) :=
  equivShrink.{w} (G.obj W) (resMap G f ((equivShrink.{w} (G.obj V)).symm x))

/-- `shrinkMap G f` is additive. -/
theorem shrinkMap_add {V W : Cᵒᵖ} (f : V ⟶ W) (x y : Shrink.{w} (G.obj V)) :
    shrinkMap.{w} G f (x + y) = shrinkMap.{w} G f x + shrinkMap.{w} G f y := by
  unfold shrinkMap
  rw [show (equivShrink.{w} (G.obj V)).symm (x + y) =
      (equivShrink.{w} (G.obj V)).symm x + (equivShrink.{w} (G.obj V)).symm y from
    (Shrink.linearEquiv.{w} (R₁.obj V) (G.obj V)).map_add x y, resMap_add]
  exact (Shrink.linearEquiv.{w} (R₁.obj W) (G.obj W)).symm.map_add _ _

include hρ in
/-- `shrinkMap G f` intertwines the action of `a` through `ρ V` with that of `R₀.map f a`
through `ρ W`. -/
theorem shrinkMap_smul {V W : Cᵒᵖ} (f : V ⟶ W) (a : R₀.obj V) (x : Shrink.{w} (G.obj V)) :
    shrinkMap.{w} G f (equivShrink.{w} (G.obj V) (ρ V a • (equivShrink.{w} (G.obj V)).symm x)) =
      equivShrink.{w} (G.obj W) (ρ W (R₀.map f a) • (equivShrink.{w} (G.obj W)).symm
        (shrinkMap.{w} G f x)) := by
  unfold shrinkMap
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, hρ, resMap_smul]

/-- `shrinkMap G` along the identity is the identity. -/
theorem shrinkMap_id (V : Cᵒᵖ) (x : Shrink.{w} (G.obj V)) : shrinkMap.{w} G (𝟙 V) x = x := by
  unfold shrinkMap
  rw [resMap_id]
  exact (equivShrink.{w} (G.obj V)).apply_symm_apply x

/-- `shrinkMap G` along `f ≫ g` is the composite of `shrinkMap G f` and `shrinkMap G g`. -/
theorem shrinkMap_comp {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (x : Shrink.{w} (G.obj U)) :
    shrinkMap.{w} G (f ≫ g) x = shrinkMap.{w} G g (shrinkMap.{w} G f x) := by
  unfold shrinkMap
  rw [Equiv.symm_apply_apply, resMap_comp]

/-- The presheaf of modules over `R₀` with sections `Shrink (G(V))`, scalars acting through
`ρ`: shrinking the universe of a presheaf of modules with small sections. -/
def shrinkObjAlong : PresheafOfModules.{w} R₀ where
  obj V := shrinkModule.{w} ρ G V
  map {V W} f := ModuleCat.ofHom
    (X := shrinkModule.{w} ρ G V)
    (Y := (ModuleCat.restrictScalars (R₀.map f).hom).obj (shrinkModule.{w} ρ G W))
    { toFun := shrinkMap.{w} G f
      map_add' := shrinkMap_add.{w} G f
      map_smul' := shrinkMap_smul.{w} ρ hρ G f }
  map_id V := ModuleCat.hom_ext (LinearMap.ext fun x => shrinkMap_id.{w} G V x)
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun x => shrinkMap_comp.{w} G f g x)

end Shrink

section ShrinkIso

variable {C : Type u₁} [Category.{v₁} C] {R₀ : Cᵒᵖ ⥤ RingCat.{r₀}} {R₁ : Cᵒᵖ ⥤ RingCat.{r₁}}
  (ρ : ∀ V, R₀.obj V →+* R₁.obj V)
  (hρ : ∀ {V W : Cᵒᵖ} (f : V ⟶ W) (a : R₀.obj V), ρ W (R₀.map f a) = R₁.map f (ρ V a))
  (G : PresheafOfModules.{w'} R₁) [∀ V, Small.{w} (G.obj V)]

/-- On underlying abelian groups, the universe lift of `shrinkObjAlong ρ G` is the universe lift
of `G`. -/
def shrinkObjPresheafULiftIso :
    (shrinkObjAlong.{w} ρ hρ G).presheaf ⋙ AddCommGrpCat.uliftFunctor.{w'} ≅
      G.presheaf ⋙ AddCommGrpCat.uliftFunctor.{w} :=
  NatIso.ofComponents
    (fun V => AddEquiv.toAddCommGrpIso
      ((AddEquiv.ulift.trans (Shrink.linearEquiv.{w} (R₁.obj V) (G.obj V)).toAddEquiv).trans
        (AddEquiv.ulift.{_, w}).symm :
        ULift.{w'} (Shrink.{w} (G.obj V)) ≃+ ULift.{w} (G.obj V)))
    (by
      intro V W f
      ext x
      change ULift.up ((equivShrink.{w} (G.obj W)).symm (shrinkMap.{w} G f x.down)) =
        ULift.up (resMap G f ((equivShrink.{w} (G.obj V)).symm x.down))
      unfold shrinkMap
      rw [Equiv.symm_apply_apply])

/-- The sections of `shrinkObjAlong ρ G` at `V` are those of `G`. -/
def shrinkEquiv (V : Cᵒᵖ) : shrinkModule.{w} ρ G V ≃ G.obj V := (equivShrink.{w} (G.obj V)).symm

/-- `shrinkEquiv ρ G V` is additive. -/
theorem shrinkEquiv_add (V : Cᵒᵖ) (x y : shrinkModule.{w} ρ G V) :
    shrinkEquiv.{w} ρ G V (x + y) = shrinkEquiv.{w} ρ G V x + shrinkEquiv.{w} ρ G V y :=
  (Shrink.linearEquiv.{w} (R₁.obj V) (G.obj V)).map_add x y

/-- `shrinkEquiv ρ G V` sends the action of `a` to the action of `ρ V a`. -/
theorem shrinkEquiv_smul (V : Cᵒᵖ) (a : R₀.obj V) (x : shrinkModule.{w} ρ G V) :
    shrinkEquiv.{w} ρ G V (a • x) = ρ V a • shrinkEquiv.{w} ρ G V x :=
  (equivShrink.{w} (G.obj V)).symm_apply_apply _

/-- `shrinkEquiv` commutes with the restriction maps of `shrinkObjAlong ρ G` and of `G`. -/
theorem shrinkEquiv_map {V W : Cᵒᵖ} (f : V ⟶ W) (x : shrinkModule.{w} ρ G V) :
    shrinkEquiv.{w} ρ G W ((shrinkObjAlong.{w} ρ hρ G).map f x) =
      resMap G f (shrinkEquiv.{w} ρ G V x) :=
  (equivShrink.{w} (G.obj W)).symm_apply_apply _

end ShrinkIso

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R₀ : Sheaf J RingCat.{r₀}} {R₁ : Sheaf J RingCat.{r₁}}
  (ρ : ∀ V, R₀.obj.obj V →+* R₁.obj.obj V)
  (hρ : ∀ {V W : Cᵒᵖ} (f : V ⟶ W) (a : R₀.obj.obj V), ρ W (R₀.obj.map f a) = R₁.obj.map f (ρ V a))
  (G : SheafOfModules.{w'} R₁) [∀ V, Small.{w} (G.val.obj V)]

/-- The sheaf of modules over `R₀` with sections `Shrink (G(V))`, scalars acting through `ρ`:
shrinking the universe of a sheaf of modules with small sections. -/
def shrinkObj : SheafOfModules.{w} R₀ where
  val := PresheafOfModules.shrinkObjAlong.{w} ρ hρ G.val
  isSheaf := Presheaf.isSheaf_of_isSheaf_comp J _ AddCommGrpCat.uliftFunctor.{w'}
    ((Presheaf.isSheaf_of_iso_iff (PresheafOfModules.shrinkObjPresheafULiftIso.{w} ρ hρ G.val)).mpr
      (Presheaf.isSheaf_comp_of_isSheaf J _ AddCommGrpCat.uliftFunctor.{w} G.isSheaf))

end SheafOfModules

namespace SheafOfModules

section ULiftShrink

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r₀}}
  (G : SheafOfModules.{max w w'} R) [∀ V, Small.{w} (G.val.obj V)]

/-- The shrink of a sheaf of modules with small sections, over the same ring. -/
abbrev shrinkSame : SheafOfModules.{w} R :=
  shrinkObj.{w} (fun V => RingHom.id (R.obj.obj V)) (fun _ _ => rfl) G

/-- **A sheaf of modules with small sections is a universe lift**: the universe lift of its
shrink is the sheaf itself. -/
def uliftShrinkIso : uliftFunctor.{_, _, _, _, w'}.obj (shrinkSame.{w} G) ≅ G :=
  (fullyFaithfulForget R).preimageIso (PresheafOfModules.isoMk
    (fun V => LinearEquiv.toModuleIso
      { toFun x := PresheafOfModules.shrinkEquiv.{w} (fun V => RingHom.id (R.obj.obj V)) G.val V
          x.down
        invFun y := ULift.up ((PresheafOfModules.shrinkEquiv.{w}
          (fun V => RingHom.id (R.obj.obj V)) G.val V).symm y)
        map_add' x y := PresheafOfModules.shrinkEquiv_add.{w} _ G.val V x.down y.down
        map_smul' a x := PresheafOfModules.shrinkEquiv_smul.{w} _ G.val V a x.down
        left_inv x := congrArg ULift.up ((PresheafOfModules.shrinkEquiv.{w}
          (fun V => RingHom.id (R.obj.obj V)) G.val V).symm_apply_apply x.down)
        right_inv y := (PresheafOfModules.shrinkEquiv.{w}
          (fun V => RingHom.id (R.obj.obj V)) G.val V).apply_symm_apply y })
    (fun V W f => by
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      exact PresheafOfModules.shrinkEquiv_map.{w} _ (fun _ _ => rfl) G.val f x.down))

/-- A sheaf of modules with small sections lies in the essential image of the universe lift. -/
theorem mem_essImage_uliftFunctor : (uliftFunctor.{_, _, _, _, w'} (R := R)).essImage G :=
  ⟨shrinkSame.{w} G, ⟨uliftShrinkIso.{w} G⟩⟩

end ULiftShrink

end SheafOfModules

namespace Stacks.SheafOfModules.CoherentLift

universe u v

attribute [local implicit_reducible] liftRingedSite CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})

/-- The ring map `𝒪(V) → ULift 𝒪(V)` into the sections of the lifted structure sheaf. -/
def liftRingHom (V : X.Cᵒᵖ) :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V →+*
      (Stacks.SheafOfModules.Tensor.ringSheaf (liftRingedSite.{u, v, w} X).O).obj.obj V :=
  (liftRingEquiv X V).symm.toRingHom.comp ULift.ringEquiv.symm.toRingHom

/-- The maps `liftRingHom X` commute with the restriction maps of the two structure sheaves. -/
theorem liftRingHom_naturality {V W : X.Cᵒᵖ} (f : V ⟶ W)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V) :
    liftRingHom X W ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f a) =
      (Stacks.SheafOfModules.Tensor.ringSheaf (liftRingedSite.{u, v, w} X).O).obj.map f
        (liftRingHom X V a) := rfl

variable (G : _root_.SheafOfModules.{max u v w}
    (Stacks.SheafOfModules.Tensor.ringSheaf (liftRingedSite.{u, v, w} X).O))
  [∀ V, Small.{w} (G.val.obj V)]

/-- The shrink of a sheaf of modules over the lifted structure sheaf with small sections, as a
sheaf of modules over the structure sheaf. -/
abbrev shrinkLift : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  _root_.SheafOfModules.shrinkObj.{w} (liftRingHom X) (liftRingHom_naturality X) G

/-- **A sheaf of modules over the lifted structure sheaf with small sections is a universe
lift**: the universe lift of its shrink is the sheaf itself. -/
noncomputable def liftModuleShrinkIso : liftModule X (shrinkLift X G) ≅ G :=
  (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso (PresheafOfModules.isoMk
    (fun V => LinearEquiv.toModuleIso
      { toFun x := PresheafOfModules.shrinkEquiv.{w} (liftRingHom X) G.val V x.down
        invFun y := ULift.up ((PresheafOfModules.shrinkEquiv.{w} (liftRingHom X) G.val V).symm y)
        map_add' x y := PresheafOfModules.shrinkEquiv_add.{w} _ G.val V x.down y.down
        map_smul' a x := PresheafOfModules.shrinkEquiv_smul.{w} _ G.val V a.down x.down
        left_inv x := congrArg ULift.up
          ((PresheafOfModules.shrinkEquiv.{w} (liftRingHom X) G.val V).symm_apply_apply x.down)
        right_inv y :=
          (PresheafOfModules.shrinkEquiv.{w} (liftRingHom X) G.val V).apply_symm_apply y })
    (fun V W f => by
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      exact PresheafOfModules.shrinkEquiv_map.{w} _ (liftRingHom_naturality X) G.val f x.down))

/-- A sheaf of modules over the lifted structure sheaf with small sections lies in the
essential image of the universe lift. -/
theorem mem_essImage_liftModuleFunctor : (liftModuleFunctor X).essImage G :=
  ⟨shrinkLift X G, ⟨liftModuleShrinkIso X G⟩⟩

end Stacks.SheafOfModules.CoherentLift
