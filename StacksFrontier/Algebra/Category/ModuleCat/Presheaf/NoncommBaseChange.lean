module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.Algebra.Category.ModuleCat.NoncommExtendScalars

/-!
# Objectwise extension of scalars for presheaves of modules over a presheaf of rings

Let `α : R ⟶ R'` be a morphism of presheaves of **not necessarily commutative** rings on a
category `C`. This file constructs the left adjoint of
`PresheafOfModules.restrictScalars α` as the objectwise extension of scalars

`M ↦ (V ↦ R'(V) ⊗_{R(V)} M(V))`,

using `Stacks.NoncommChangeOfRings.extendScalars` at each object. Mathlib's own source for
this left adjoint, `PresheafOfModules.pullbackObjIsDefined_eq_top`, resolves a presheaf of
modules into free modules on representables and so needs `C` to be a small category in the
same universe as the rings and the modules; the objectwise construction needs nothing about
`C` at all. The commutative analogue, built on `ModuleCat.extendScalars`, is
`Stacks.PullbackModel.extendScalars`.

## Main definitions

* `Stacks.NoncommChangeOfRings.Presheaf.extendScalarsObj` and
  `Stacks.NoncommChangeOfRings.Presheaf.extendScalars`: the objectwise extension of scalars,
  as an object and as a functor `PresheafOfModules R ⥤ PresheafOfModules R'`.
* `Stacks.NoncommChangeOfRings.Presheaf.transposeApp`: the adjoint transpose of a morphism
  `M ⟶ (PresheafOfModules.restrictScalars α).obj N`, objectwise.
* `Stacks.NoncommChangeOfRings.Presheaf.overId`: `α` read as a morphism over the identity
  functor of `C`, which is the shape `PresheafOfModules.pushforward` and
  `PresheafOfModules.pullback` expect.

## Main results

* `Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction`: extension of scalars is
  left adjoint to restriction of scalars for presheaves of modules, along an arbitrary
  morphism of presheaves of not necessarily commutative rings, over an arbitrary category `C`
  in arbitrary universes. The instance
  `(PresheafOfModules.restrictScalars α).IsRightAdjoint` is registered: this is the hypothesis
  that `Stacks.SheafOfModules.ChangeOfRings.extendRestrictScalarsAdjunction` takes, and it is
  now available with no smallness assumption.
* `Stacks.NoncommChangeOfRings.Presheaf.extendScalarsObj_map_objTmul`,
  `extendScalars_map_app_objTmul`, `transposeApp_objTmul`: the restriction maps, the
  functoriality and the adjoint transpose, computed on pure tensors. This is exactly what the
  abstract left adjoint does not provide.
* `Stacks.NoncommChangeOfRings.Presheaf.extendScalarsIsoPullback`: the objectwise construction
  is canonically isomorphic to Mathlib's `PresheafOfModules.pullback` along `𝟭 C`.

## Implementation notes

**Universes.** The category is `C : Type u₁` with `Category.{v₁} C`, the presheaves of rings
are `RingCat.{u}`-valued, and the presheaves of modules live in universe `max u v`. The
constraint `u ≤ max u v` is forced and not chosen: the sections of the extension of scalars
are `R'(V) ⊗_{R(V)} M(V)`, a tensor product of a `Type u` and a `Type (max u v)`, which lands
in `Type (max u v)`. It is the same constraint that Mathlib's commutative
`ModuleCat.extendRestrictScalarsAdj` carries (its module universe is `max v u₂` for rings in
`Type u₂`). Nothing else couples the universes: `u₁` and `v₁` are free, and in particular `C`
need not be small nor live in the universe of the rings.

**The two spellings of a pure tensor.** As in `Stacks.NoncommChangeOfRings`, a pure tensor is
written `objTmul`, whose ascribed type is `↑((extendScalars f).obj M)`, and a morphism into a
restriction of scalars is applied through `ofRestrict`. Writing either one the other way
produces a term of a definitionally equal but syntactically different type, after which `rw`
reports the goal as "not type-correct under the `implicit` transparency level" and every
subsequent rewrite fails. Consequently the restriction maps of `extendScalarsObj` are compared
with `Stacks.NoncommChangeOfRings.restrict_hom_ext` rather than with `ModuleCat.hom_ext`.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public section

open CategoryTheory PresheafOfModules

universe v u v₁ u₁

namespace Stacks.NoncommChangeOfRings.Presheaf

variable {C : Type u₁} [Category.{v₁} C] {R R' : Cᵒᵖ ⥤ RingCat.{u}} (α : R ⟶ R')

/-- Naturality of `α`, read on elements: pushing a section of `R` forward along `α` and then
restricting agrees with restricting and then pushing forward. This is the commuting square
along which the restriction maps of the extension of scalars are base-changed. -/
lemma app_naturality_apply {V W : Cᵒᵖ} (g : V ⟶ W) (r : R.obj V) :
    (R'.map g).hom ((α.app V).hom r) = (α.app W).hom ((R.map g).hom r) :=
  (RingHom.congr_fun (congrArg RingCat.Hom.hom (α.naturality g)) r).symm

/-- Objectwise extension of scalars of a presheaf of modules along a morphism `α : R ⟶ R'` of
presheaves of not necessarily commutative rings: the presheaf of `R'`-modules
`V ↦ R'(V) ⊗_{R(V)} M(V)`. -/
noncomputable def extendScalarsObj (M : PresheafOfModules.{max u v} R) :
    PresheafOfModules.{max u v} R' where
  obj V := (extendScalars (α.app V).hom).obj (M.obj V)
  map {V W} g :=
    squareMapObj (α.app V).hom (α.app W).hom (app_naturality_apply α g) (M.restrictₛₗ g)
  map_id V := by
    refine restrict_hom_ext (α.app V).hom (R'.map (𝟙 V)).hom fun m => ?_
    rw [ofRestrict_squareMapObj, map_one, restrictₛₗ_apply,
      ConcreteCategory.congr_hom (M.map_id V) m]
    rfl
  map_comp {V W Z} g h := by
    refine restrict_hom_ext (α.app V).hom (R'.map (g ≫ h)).hom fun m => ?_
    rw [ofRestrict_squareMapObj, map_one, restrictₛₗ_apply, M.map_comp_apply]
    have h₁ : ((R'.map h).hom ((R'.map g).hom 1) : R'.obj Z) = 1 := by
      simp only [map_one]
    exact (congrArg (fun c => objTmul (α.app Z).hom c (M.map h (M.map g m))) h₁).symm

/-- The restriction maps of the objectwise extension of scalars, on pure tensors. -/
lemma extendScalarsObj_map_objTmul (M : PresheafOfModules.{max u v} R) {V W : Cᵒᵖ} (g : V ⟶ W)
    (b : R'.obj V) (m : M.obj V) :
    ofRestrict (R'.map g).hom ((extendScalarsObj α M).map g) (objTmul (α.app V).hom b m) =
      objTmul (α.app W).hom ((R'.map g).hom b) (M.map g m) := rfl

/-- The restriction maps of the objectwise extension of scalars send `1 ⊗ m` to
`1 ⊗ M.map g m`. -/
lemma extendScalarsObj_map_one_objTmul (M : PresheafOfModules.{max u v} R) {V W : Cᵒᵖ}
    (g : V ⟶ W) (m : M.obj V) :
    ofRestrict (R'.map g).hom ((extendScalarsObj α M).map g) (objTmul (α.app V).hom 1 m) =
      objTmul (α.app W).hom 1 (M.map g m) := by
  rw [extendScalarsObj_map_objTmul, map_one]

/-- Objectwise extension of scalars, as a functor between categories of presheaves of
modules. -/
noncomputable def extendScalars :
    PresheafOfModules.{max u v} R ⥤ PresheafOfModules.{max u v} R' where
  obj M := extendScalarsObj α M
  map {M N} ψ :=
    { app V := (NoncommChangeOfRings.extendScalars (α.app V).hom).map (Hom.app ψ V)
      naturality := fun {V W} g => by
        refine restrict_hom_ext (α.app V).hom (R'.map g).hom fun m => ?_
        change objTmul (α.app W).hom ((R'.map g).hom 1) (Hom.app ψ W (M.map g m))
          = objTmul (α.app W).hom ((R'.map g).hom 1) (N.map g (Hom.app ψ V m))
        rw [naturality_apply] }
  map_id M := PresheafOfModules.hom_ext fun V =>
    (NoncommChangeOfRings.extendScalars (α.app V).hom).map_id (M.obj V)
  map_comp {M N P} ψ χ := PresheafOfModules.hom_ext fun V =>
    (NoncommChangeOfRings.extendScalars (α.app V).hom).map_comp (Hom.app ψ V) (Hom.app χ V)

/-- Extension of scalars of a morphism of presheaves of modules, on pure tensors. -/
lemma extendScalars_map_app_objTmul {M N : PresheafOfModules.{max u v} R} (ψ : M ⟶ N)
    (V : Cᵒᵖ) (b : R'.obj V) (m : M.obj V) :
    Hom.app ((extendScalars α).map ψ) V (objTmul (α.app V).hom b m) =
      objTmul (α.app V).hom b (Hom.app ψ V m) := rfl

/-! ### The adjunction -/

section Transpose

variable {M : PresheafOfModules.{max u v} R} {N : PresheafOfModules.{max u v} R'}

/-- The adjoint transpose of a morphism `M ⟶ (PresheafOfModules.restrictScalars α).obj N`,
objectwise. -/
noncomputable def transposeApp
    (h : M ⟶ (PresheafOfModules.restrictScalars.{max u v} α).obj N) (V : Cᵒᵖ) :
    (extendScalarsObj α M).obj V ⟶ N.obj V :=
  (homEquiv (α.app V).hom (M.obj V) (N.obj V)).symm (Hom.app h V)

/-- The adjoint transpose `transposeApp α h V` sends `1 ⊗ m` to `h_V(m)`. -/
lemma transposeApp_objTmul (h : M ⟶ (PresheafOfModules.restrictScalars.{max u v} α).obj N)
    (V : Cᵒᵖ) (m : M.obj V) :
    transposeApp α h V (objTmul (α.app V).hom 1 m) =
      ofRestrict (α.app V).hom (Hom.app h V) m :=
  (homEquiv_symm_apply_objTmul (α.app V).hom (Hom.app h V) 1 m).trans (one_smul _ _)

end Transpose

/-- **Extension of scalars is left adjoint to restriction of scalars** for presheaves of
modules over presheaves of not necessarily commutative rings. The bijection is objectwise
`Stacks.NoncommChangeOfRings.homEquiv`, and `transposeApp_objTmul` computes it. -/
noncomputable def extendScalarsAdjunction :
    extendScalars.{v} α ⊣ PresheafOfModules.restrictScalars.{max u v} α :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N =>
        { toFun := fun x =>
            { app := fun V => homEquiv (α.app V).hom (M.obj V) (N.obj V) (Hom.app x V)
              naturality := fun {V W} g => by
                refine restrictScalars_hom_ext (R.map g).hom fun m => ?_
                change Hom.app x W (objTmul (α.app W).hom 1 (M.map g m))
                  = N.map g (Hom.app x V (objTmul (α.app V).hom 1 m))
                rw [← map_one (R'.map g).hom]
                exact naturality_apply x g (objTmul (α.app V).hom 1 m) }
          invFun := fun h =>
            { app := fun V => transposeApp α h V
              naturality := fun {V W} g => by
                refine restrict_hom_ext (α.app V).hom (R'.map g).hom fun m => ?_
                change transposeApp α h W
                      (objTmul (α.app W).hom ((R'.map g).hom 1) (M.restrictₛₗ g m))
                  = N.map g (transposeApp α h V (objTmul (α.app V).hom 1 m))
                rw [map_one, transposeApp_objTmul, transposeApp_objTmul]
                exact naturality_apply h g m }
          left_inv := fun _ => PresheafOfModules.hom_ext fun _ => Equiv.symm_apply_apply _ _
          right_inv := fun _ => PresheafOfModules.hom_ext fun _ => Equiv.apply_symm_apply _ _ }
      homEquiv_naturality_left_symm := fun ψ h =>
        PresheafOfModules.hom_ext fun V =>
          NoncommChangeOfRings.homEquiv_symm_naturality_left (α.app V).hom
            (Hom.app ψ V) (Hom.app h V)
      homEquiv_naturality_right := fun x ψ =>
        PresheafOfModules.hom_ext fun V =>
          NoncommChangeOfRings.homEquiv_naturality_right (α.app V).hom
            (Hom.app x V) (Hom.app ψ V) }

/-- Objectwise extension of scalars is a left adjoint. -/
instance isLeftAdjoint_extendScalars : (extendScalars.{v} α).IsLeftAdjoint :=
  (extendScalarsAdjunction.{v} α).isLeftAdjoint

/-- **Restriction of scalars for presheaves of modules has a left adjoint** along an arbitrary
morphism of presheaves of not necessarily commutative rings, over an arbitrary category `C` in
arbitrary universes. This is the hypothesis of
`Stacks.SheafOfModules.ChangeOfRings.extendRestrictScalarsAdjunction`, which Mathlib otherwise
supplies only for a small site in a single universe. -/
instance isRightAdjoint_restrictScalars :
    (PresheafOfModules.restrictScalars.{max u v} α).IsRightAdjoint :=
  (extendScalarsAdjunction.{v} α).isRightAdjoint

/-- `α`, read with the identity functor inserted: this is the shape
`PresheafOfModules.pushforward` and `PresheafOfModules.pullback` expect. -/
abbrev overId : R ⟶ (𝟭 C).op ⋙ R' := α

/-- Restriction of scalars is the pushforward along the identity functor. -/
lemma pushforward_overId :
    PresheafOfModules.pushforward.{max u v} (overId α) =
      PresheafOfModules.restrictScalars.{max u v} α := rfl

/-- The pushforward of presheaves of modules along `overId α` is a right adjoint. -/
instance isRightAdjoint_pushforward_overId :
    (PresheafOfModules.pushforward.{max u v} (overId α)).IsRightAdjoint :=
  (extendScalarsAdjunction.{v} α).isRightAdjoint

/-- **The objectwise extension of scalars is Mathlib's `PresheafOfModules.pullback` along the
identity functor**, canonically. No smallness hypothesis on `C` is needed: the left adjoint is
produced by the construction rather than by the adjoint functor theorem. -/
noncomputable def extendScalarsIsoPullback :
    extendScalars.{v} α ≅ PresheafOfModules.pullback.{max u v} (overId α) :=
  Adjunction.leftAdjointUniq (extendScalarsAdjunction.{v} α)
    (PresheafOfModules.pullbackPushforwardAdjunction.{max u v} (overId α))

end Stacks.NoncommChangeOfRings.Presheaf

end
