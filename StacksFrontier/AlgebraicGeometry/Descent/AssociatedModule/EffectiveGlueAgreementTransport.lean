module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EffectiveGlueAgreementBridge
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.QcohGlueEffectivity

/-!
# Stacks 03DX (1) for `τ = fppf`: essential surjectivity of `𝓕 ↦ 𝓕^a`

`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreement.lean` proves the
agreement of the local isomorphisms of Stacks 03DX (1) in the `objRestrict` spelling —
`AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso_effectiveGlueObjRestrictIso_eq` — and
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/ObjRestrictRestrFunBridgeEffectivity.lean`
reduces the essential surjectivity to the same agreement in the `homRestr` spelling.  **This file
transports the one into the other and closes the clause.**

The transport is the identity
`AlgebraicGeometry.BigFppfOver.objRestrictPreimageIso_hom_val_app_over_map`: for `g : Z ⟶ T` and
`W` an object of the slice at `Z`, the component at `(Over.map g).obj W` of the preimage of a
local isomorphism `θ` under the reindexing of Stacks 06WI is the component at `W` of the preimage
of its restriction `AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso` along `g`.  With it the
agreement in the `objRestrict` spelling, read through
`AlgebraicGeometry.BigFppfOver.homRestr_objRestrictPreimageIso_eq_of_app`, is the agreement the
gluing step asks for; and `AlgebraicGeometry.BigFppfOver`
`.quasicoherentIsEssImageAssociatedModule_of_refinedDatum` turns that into Stacks 03DX (1)'s
essential surjectivity with nothing left over.

## Main results

* `Stacks.SectionsComponents.conj_cast`: **the sections of a conjugate**, at abstract sites: if
  the two outer factors of `α.symm ≪≫ F.mapIso θ ≪≫ γ` are restriction along arrows `u` and `v`
  of a base site and the middle factor is a map `Φ` of sections there, then the composite is `Φ`
  conjugated by restriction along `u` and `v`.
* `AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso_cast_hom_val_app`: **the component of
  `AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso`**, that conjugate read at the big fppf
  site: the component of `θ` at the reindexed object, restricted along the two reassociation
  arrows `AlgebraicGeometry.BigFppfOver.objRestrictCompArrow` and `…objRestrictCompArrowInv`.
* `AlgebraicGeometry.BigFppfOver.objRestrictPreimageIso_hom_val_app_over_map`: **the transport
  across the bridge**, in the form the agreement needs.
* `AlgebraicGeometry.BigFppfOver.homRestr_objRestrictPreimageIso_effectiveGlueObjRestrictIso_eq`:
  **the agreement of the local isomorphisms of Stacks 03DX (1) in the `homRestr` spelling**,
  unconditionally.
* `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_member`: the gluing step of
  Stacks 03DX (1) with nothing left to supply but the covering family and its local data.
* `AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum`: **the descent datum of
  Stacks 03DX (1)**, unconditionally.
* `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`: **Stacks 03DX (1) for
  `τ = fppf`, essential surjectivity, unconditionally.**  Every quasi-coherent `𝒪`-module on
  `(Sch/S)_fppf` is isomorphic to `𝓕^a` for a quasi-coherent `𝒪_S`-module `𝓕`.

## Implementation notes

Every statement below carries its type identifications as explicit `cast`s along
`AlgebraicGeometry.BigFppfOver.objRestrict_obj_val_obj_eq` and `…objRestrict_comp_obj_val_obj_eq`,
and every application of a morphism of modules to a section is applied to a term whose type is
*already* the domain of that morphism.  That is forced, and for two separate reasons.

First, the sections of two restrictions and the sections of one are the same type only after
unfolding a semireducible definition, so a statement that asks the elaborator to see it does not
fit in the heartbeat budget — this is the measurement recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreementBridge.lean`.  The
`cast`s keep that identification out of every statement, and
`AlgebraicGeometry.BigFppfOver.cast_objRestrict_obj_val_obj` and `…_symm` remove them again one
restriction deep, where the base of the site is a variable and the check is cheap.

Second, the category `SheafOfModules (structureSheaf B (objScheme B S hS Z) _)` has a *second*
spelling as `SheafOfModules (structureSheaf B (objScheme B (objScheme B S hS T) _ (Over.mk g.left))
_)`: the two are the same category, but the comparison of their instances inside a term does not
fit in the budget either.  `AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso` is stated in the
first spelling and `AlgebraicGeometry.BigFppfOver.objRestrictComp` in the second, so a chain that
mentions both must pin one of them: that is what the `S'`, `C` and `D` arguments written out by
name below do.  Pinning is free in an argument position — only an equation between the two
spellings of the *category* is expensive.

Nothing here raises the heartbeat limit, and nothing here is proved by `rfl` at a nesting depth
greater than one.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃ w m u

namespace Stacks.SectionsComponents

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {Mb Nb : SheafOfModules.{m} R}
  {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S' : Sheaf J' RingCat.{w}}

/-- **The sections of a conjugate, at abstract sites.**  Let `α.symm ≪≫ F.mapIso θ ≪≫ γ` be an
isomorphism of sheaves of modules on one site whose two outer factors are, on sections at `U`,
restriction along arrows `u` and `v` of a *second* site — the site of the modules `Mb` and `Nb` —
and whose middle factor is a map `Φ` of sections of `Mb` and `Nb` there.  Then the composite is,
on sections at `U`, the map `Φ` conjugated by restriction along `u` and `v`.

This is the whole of `AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso_cast_hom_val_app`, put
at abstract sites so that the consumer matches it by first-order unification alone; the four type
identifications are carried as `cast`s for the reason the implementation notes give. -/
public theorem conj_cast {D : Type u₃} [Category.{v₃} D] {D' : Type u₃} [Category.{v₃} D']
    (F' : D' ⥤ D) (F : D ⥤ SheafOfModules.{m} S') {Xo Yo : D'}
    (θ : F'.obj Xo ≅ F'.obj Yo) {N₁ N₄ : SheafOfModules.{m} S'}
    {α : (F' ⋙ F).obj Xo ≅ N₁} {γ : (F' ⋙ F).obj Yo ≅ N₄} {Ψ : N₁ ≅ N₄}
    (hΨ : Ψ = α.symm ≪≫ F.mapIso θ ≪≫ γ) (U : C'ᵒᵖ) {A A' : C} {u : A' ⟶ A} {v : A ⟶ A'}
    (Φ : ↥(Mb.val.obj (op A')) → ↥(Nb.val.obj (op A')))
    (hp : InducedAlong Mb α.inv U u) (hq : InducedAlong Nb γ.hom U v)
    (k₁ : ↥(((F' ⋙ F).obj Xo).val.obj U) = ↥(Mb.val.obj (op A')))
    (k₂ : ↥(((F' ⋙ F).obj Yo).val.obj U) = ↥(Nb.val.obj (op A')))
    (hf : ∀ x, cast k₂ ((F.map θ.hom).val.app U x) = Φ (cast k₁ x))
    (e : ↥(N₁.val.obj U) = ↥(Mb.val.obj (op A))) (e' : ↥(N₄.val.obj U) = ↥(Nb.val.obj (op A)))
    (y : ↥(N₁.val.obj U)) :
    cast e' (Ψ.hom.val.app U y) = Nb.val.map v.op (Φ (Mb.val.map u.op (cast e y))) := by
  obtain ⟨a₁, a₂, hu⟩ := hp
  obtain ⟨b₁, b₂, hv⟩ := hq
  refine Eq.trans (congrArg (cast e') (iso_trans3_map_val_app_of_eq F' F θ hΨ U y)) ?_
  refine Eq.trans (hv _) ?_
  refine congrArg (fun tt => Nb.val.map v.op tt) ?_
  refine Eq.trans (hf _) ?_
  exact congrArg Φ (hu y)

end Stacks.SectionsComponents

namespace AlgebraicGeometry.BigFppfOver

open Stacks.SectionsComponents

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The sections identification of one restriction, moved past a morphism -/

/-- **The transport along the sections identification of one restriction, read inside a
morphism.**  The component of the restriction of `φ` is the component of `φ` at the image object,
the two identifications being the `cast`s of
`AlgebraicGeometry.BigFppfOver.objRestrict_obj_val_obj_eq`.  The base of the site is a variable,
which is what makes the `rfl` cheap. -/
public theorem cast_objRestrict_map_val_app (X : Scheme.{u}) (hX : B.Contains X)
    (T : BigFppfOver B X hX) {K L : SheafOfModules.{u} (structureSheaf B X hX)} (φ : K ⟶ L)
    (V : BigFppfOver B (objScheme B X hX T) (contains_objScheme B X hX T))
    (x : ((objRestrict B X hX T).obj K).val.obj (op V)) :
    cast (objRestrict_obj_val_obj_eq B X hX T L V)
        (((objRestrict B X hX T).map φ).val.app (op V) x)
      = φ.val.app (op ((Over.map T.hom).obj V))
          (cast (objRestrict_obj_val_obj_eq B X hX T K V) x) := rfl

/-- **The inverse transport along the sections identification of one restriction is the
identity**, the companion of `AlgebraicGeometry.BigFppfOver.cast_objRestrict_obj_val_obj` in the
other direction.  The base of the site is a variable. -/
public theorem cast_objRestrict_obj_val_obj_symm (X : Scheme.{u}) (hX : B.Contains X)
    (T : BigFppfOver B X hX) (K : SheafOfModules.{u} (structureSheaf B X hX))
    (V : BigFppfOver B (objScheme B X hX T) (contains_objScheme B X hX T))
    (y : K.val.obj (op ((Over.map T.hom).obj V))) :
    cast (objRestrict_obj_val_obj_eq B X hX T K V).symm y = y := rfl

/-- **Naturality of a morphism of modules on the localization at `T`, read on sections.**  The
restricted module acts on an arrow of the slice through the arrow underneath it
(`AlgebraicGeometry.BigFppfOver.over_val_map`), so naturality is an identity between restrictions
along the arrows underneath.  The base of the site is a variable. -/
public theorem over_nat_app (X : Scheme.{u}) (hX : B.Contains X) (T : BigFppfOver B X hX)
    {M N : SheafOfModules.{u} (structureSheaf B X hX)} (ψ : M.over T ⟶ N.over T)
    {P Q : Over T} (m : P ⟶ Q) (y) :
    N.val.map m.left.op (ψ.val.app (op Q) y) =
      ψ.val.app (op P) (M.val.map m.left.op y) :=
  (PresheafOfModules.naturality_apply ψ.val m.op y).symm

/-! ### The component of the functoriality comparison, past a morphism -/

/-- **The component of the restriction of `φ` to the big fppf site of the scheme of `T'`, with
the two-step sections identification of
`AlgebraicGeometry.BigFppfOver.objRestrict_comp_obj_val_obj_eq` on both sides.**  It is the
component of `φ` at the reindexed object, one step down.

The two-step identification is never checked: it is composed of two instances of the one-step
one by `Eq.trans`, and `AlgebraicGeometry.BigFppfOver.cast_objRestrict_map_val_app` moves the
inner instance past the morphism where the base of the site is a variable.  The codomain of the
inner restriction functor is pinned by name — see the implementation notes. -/
public theorem cast_objRestrictComp_map_val_app {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (φ : (objRestrict B S hS T).obj M ⟶ (objRestrict B S hS T).obj N)
    (W : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z))
    (x : ((objRestrict B S hS T ⋙ objRestrict B (objScheme B S hS T)
        (contains_objScheme B S hS T) (Over.mk g.left)).obj M).val.obj (op W)) :
    cast (objRestrict_comp_obj_val_obj_eq B S hS g N W)
        ((CategoryTheory.Functor.map
            (D := SheafOfModules.{u} (structureSheaf B (objScheme B S hS Z)
              (contains_objScheme B S hS Z)))
            (objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T)
              (Over.mk g.left)) φ).val.app (op W) x)
      = cast (objRestrict_obj_val_obj_eq B S hS T N ((Over.map g.left).obj W))
          (φ.val.app (op ((Over.map g.left).obj W))
            (cast (objRestrict_obj_val_obj_eq B S hS T M ((Over.map g.left).obj W)).symm
              (cast (objRestrict_comp_obj_val_obj_eq B S hS g M W) x))) := by
  refine Eq.trans (Eq.symm (cast_cast
    (objRestrict_obj_val_obj_eq B (objScheme B S hS T) (contains_objScheme B S hS T)
      (Over.mk g.left) ((objRestrict B S hS T).obj N) W)
    (objRestrict_obj_val_obj_eq B S hS T N ((Over.map g.left).obj W)) _)) ?_
  refine congrArg (cast (objRestrict_obj_val_obj_eq B S hS T N ((Over.map g.left).obj W))) ?_
  refine Eq.trans (cast_objRestrict_map_val_app B (objScheme B S hS T)
    (contains_objScheme B S hS T) (Over.mk g.left) φ W x) ?_
  refine congrArg (fun tt => φ.val.app (op ((Over.map g.left).obj W)) tt) ?_
  exact Eq.symm (cast_cast (objRestrict_comp_obj_val_obj_eq B S hS g M W)
    (objRestrict_obj_val_obj_eq B S hS T M ((Over.map g.left).obj W)).symm x)

/-! ### The component of the restriction of a local isomorphism -/

/-- **The component of `AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso`.**  The restriction
of a local isomorphism `θ` along `g : Z ⟶ T` has, at an object `W` of the big fppf site of the
scheme of `Z`, the component of `θ` at the image of `W` under the reindexing by `g.left`,
restricted along the two reassociation arrows `AlgebraicGeometry.BigFppfOver.objRestrictCompArrow`
and `…objRestrictCompArrowInv`.

This is `Stacks.SectionsComponents.conj_cast` at the big fppf site: the two outer factors are the
components of `AlgebraicGeometry.BigFppfOver.objRestrictComp`, which
`AlgebraicGeometry.BigFppfOver.inducedAlong_objRestrictComp_app_hom` and `…_inv` exhibit as
restriction along those arrows, and the middle factor is the component of `θ` by
`AlgebraicGeometry.BigFppfOver.cast_objRestrictComp_map_val_app`. -/
public theorem restrictObjRestrictIso_cast_hom_val_app {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (W : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z))
    (z : ((objRestrict B S hS Z).obj M).val.obj (op W))
    (z₀ : M.val.obj (op ((Over.map Z.hom).obj W)))
    (hz : cast (objRestrict_obj_val_obj_eq B S hS Z M W) z = z₀) :
    cast (objRestrict_obj_val_obj_eq B S hS Z N W)
        ((restrictObjRestrictIso B S hS g θ).hom.val.app (op W) z) =
      N.val.map (objRestrictCompArrow B S hS g W).op
        (cast (objRestrict_obj_val_obj_eq B S hS T N ((Over.map g.left).obj W))
          (θ.hom.val.app (op ((Over.map g.left).obj W))
            (cast (objRestrict_obj_val_obj_eq B S hS T M ((Over.map g.left).obj W)).symm
              (M.val.map (objRestrictCompArrowInv B S hS g W).op z₀)))) := by
  subst hz
  have hp : InducedAlong M (Iso.inv (C := SheafOfModules.{u}
      (structureSheaf B (objScheme B S hS Z) (contains_objScheme B S hS Z)))
      ((objRestrictComp B S hS g).app M)) (op W)
      (objRestrictCompArrowInv B S hS g W) :=
    inducedAlong_objRestrictComp_app_inv B S hS g M W
  have hq : InducedAlong N (Iso.hom (C := SheafOfModules.{u}
      (structureSheaf B (objScheme B S hS Z) (contains_objScheme B S hS Z)))
      ((objRestrictComp B S hS g).app N)) (op W)
      (objRestrictCompArrow B S hS g W) :=
    inducedAlong_objRestrictComp_app_hom B S hS g N W
  exact conj_cast (S' := structureSheaf B (objScheme B S hS Z) (contains_objScheme B S hS Z))
    (objRestrict B S hS T)
    (objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left)) θ
    (restrictObjRestrictIso_eq B S hS g θ) (op W)
    (fun tt => cast (objRestrict_obj_val_obj_eq B S hS T N ((Over.map g.left).obj W))
      (θ.hom.val.app (op ((Over.map g.left).obj W))
        (cast (objRestrict_obj_val_obj_eq B S hS T M ((Over.map g.left).obj W)).symm tt)))
    hp hq (objRestrict_comp_obj_val_obj_eq B S hS g M W)
    (objRestrict_comp_obj_val_obj_eq B S hS g N W)
    (cast_objRestrictComp_map_val_app B S hS g θ.hom W)
    (objRestrict_obj_val_obj_eq B S hS Z M W)
    (objRestrict_obj_val_obj_eq B S hS Z N W) z

/-! ### The transport across the bridge -/

/-- The component of the bridge at `P`, restricted along an arrow out of the image of `V` under
the reindexing of Stacks 06WI, is the component of `θ` at `V` applied to the restricted section. -/
private theorem objRestrictPreimageIso_val_app_map {T : BigFppfOver B S hS}
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (V : BigFppfOver B (objScheme B S hS T) (contains_objScheme B S hS T)) {P : Over T}
    (m : (Over.iteratedSliceBackward T).obj V ⟶ P) (y : (M.over T).val.obj (op P)) :
    N.val.map m.left.op ((objRestrictPreimageIso B S hS θ).hom.val.app (op P) y)
      = cast (objRestrict_obj_val_obj_eq B S hS T N V)
          (θ.hom.val.app (op V)
            (cast (objRestrict_obj_val_obj_eq B S hS T M V).symm (M.val.map m.left.op y))) := by
  refine Eq.trans (over_nat_app B S hS T (objRestrictPreimageIso B S hS θ).hom m y) ?_
  refine Eq.trans (objRestrictPreimageIso_hom_val_app B S hS θ V (M.val.map m.left.op y)) ?_
  refine Eq.trans ?_ (Eq.symm (cast_objRestrict_obj_val_obj B S hS T N V _))
  exact congrArg (fun tt => θ.hom.val.app (op V) tt)
    (Eq.symm (cast_objRestrict_obj_val_obj_symm B S hS T M V (M.val.map m.left.op y)))

/-- **The component of the bridge at the image of an object of the slice, read through the
canonical arrow of `CategoryTheory.Over.iteratedSliceEquivOverMapIso`.**  Restricting the
component of `AlgebraicGeometry.BigFppfOver.objRestrictPreimageIso` at `(Over.map g).obj W` along
`Stacks.sliceMapArrow` gives the component of `θ` itself at the image of `W` downstairs: this is
naturality of the preimage followed by
`AlgebraicGeometry.BigFppfOver.objRestrictPreimageIso_hom_val_app`. -/
public theorem objRestrictPreimageIso_val_app_sliceMapArrow {T Z : BigFppfOver B S hS}
    (g : Z ⟶ T) {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N) (W : Over Z)
    (y : (M.over T).val.obj (op ((Over.map g).obj W))) :
    N.val.map (Stacks.sliceMapArrow g W).left.op
        ((objRestrictPreimageIso B S hS θ).hom.val.app (op ((Over.map g).obj W)) y)
      = cast (objRestrict_obj_val_obj_eq B S hS T N
            ((Over.map g.left).obj ((Over.iteratedSliceForward Z).obj W)))
          (θ.hom.val.app (op ((Over.map g.left).obj ((Over.iteratedSliceForward Z).obj W)))
            (cast (objRestrict_obj_val_obj_eq B S hS T M
                ((Over.map g.left).obj ((Over.iteratedSliceForward Z).obj W))).symm
              (M.val.map (Stacks.sliceMapArrow g W).left.op y))) :=
  objRestrictPreimageIso_val_app_map B S hS θ _ (Stacks.sliceMapArrow g W) y

/-- **The same at the canonical arrow of the round trip.**  Restricting the component of the
bridge at `W` along `Stacks.sliceBackArrow` gives the component of the local isomorphism at the
image of `W` in the big fppf site of the scheme of `Z`. -/
public theorem objRestrictPreimageIso_val_app_sliceBackArrow {Z : BigFppfOver B S hS}
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (Ξ : (objRestrict B S hS Z).obj M ≅ (objRestrict B S hS Z).obj N) (W : Over Z)
    (y : (M.over Z).val.obj (op W)) :
    N.val.map (Stacks.sliceBackArrow Z W).left.op
        ((objRestrictPreimageIso B S hS Ξ).hom.val.app (op W) y)
      = cast (objRestrict_obj_val_obj_eq B S hS Z N ((Over.iteratedSliceForward Z).obj W))
          (Ξ.hom.val.app (op ((Over.iteratedSliceForward Z).obj W))
            (cast (objRestrict_obj_val_obj_eq B S hS Z M
                ((Over.iteratedSliceForward Z).obj W)).symm
              (M.val.map (Stacks.sliceBackArrow Z W).left.op y))) :=
  objRestrictPreimageIso_val_app_map B S hS Ξ _ (Stacks.sliceBackArrow Z W) y

/-- **The component of the bridge, restricted along the canonical arrow of the round trip,
through the reassociation arrow.**  The pin
`AlgebraicGeometry.BigFppfOver.objRestrictCompArrow_comp_sliceMapArrow_left` splits the arrow of
the round trip into the reassociation arrow followed by the arrow of
`CategoryTheory.Over.iteratedSliceEquivOverMapIso`, after which
`AlgebraicGeometry.BigFppfOver.objRestrictPreimageIso_val_app_sliceMapArrow` applies. -/
public theorem objRestrictPreimageIso_val_map_sliceBackArrow_left {T Z : BigFppfOver B S hS}
    (g : Z ⟶ T) {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N) (W : Over Z)
    (y : (M.over T).val.obj (op ((Over.map g).obj W))) :
    N.val.map (Stacks.sliceBackArrow Z W).left.op
        ((objRestrictPreimageIso B S hS θ).hom.val.app (op ((Over.map g).obj W)) y)
      = N.val.map (objRestrictCompArrow B S hS g ((Over.iteratedSliceForward Z).obj W)).op
          (cast (objRestrict_obj_val_obj_eq B S hS T N
              ((Over.map g.left).obj ((Over.iteratedSliceForward Z).obj W)))
            (θ.hom.val.app (op ((Over.map g.left).obj ((Over.iteratedSliceForward Z).obj W)))
              (cast (objRestrict_obj_val_obj_eq B S hS T M
                  ((Over.map g.left).obj ((Over.iteratedSliceForward Z).obj W))).symm
                (M.val.map (Stacks.sliceMapArrow g W).left.op y)))) := by
  rw [← objRestrictCompArrow_comp_sliceMapArrow_left B S hS g W]
  refine Eq.trans (Eq.symm (val_map_map N
    (objRestrictCompArrow B S hS g ((Over.iteratedSliceForward Z).obj W))
    (Stacks.sliceMapArrow g W).left _)) ?_
  exact congrArg (fun tt => N.val.map
      (objRestrictCompArrow B S hS g ((Over.iteratedSliceForward Z).obj W)).op tt)
    (objRestrictPreimageIso_val_app_sliceMapArrow B S hS g θ W y)

/-- **The same for the bridge of the restricted local isomorphism.**  Here the component of
`AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso` is read by
`AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso_cast_hom_val_app` and the other pin
`AlgebraicGeometry.BigFppfOver.objRestrictCompArrowInv_comp_sliceBackArrow_left` identifies the
composite of the reassociation arrow with the arrow of the round trip. -/
public theorem objRestrictPreimageIso_restrict_val_map_sliceBackArrow_left
    {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N) (W : Over Z)
    (y : (M.over Z).val.obj (op W)) :
    N.val.map (Stacks.sliceBackArrow Z W).left.op
        ((objRestrictPreimageIso B S hS (restrictObjRestrictIso B S hS g θ)).hom.val.app
          (op W) y)
      = N.val.map (objRestrictCompArrow B S hS g ((Over.iteratedSliceForward Z).obj W)).op
          (cast (objRestrict_obj_val_obj_eq B S hS T N
              ((Over.map g.left).obj ((Over.iteratedSliceForward Z).obj W)))
            (θ.hom.val.app (op ((Over.map g.left).obj ((Over.iteratedSliceForward Z).obj W)))
              (cast (objRestrict_obj_val_obj_eq B S hS T M
                  ((Over.map g.left).obj ((Over.iteratedSliceForward Z).obj W))).symm
                (M.val.map (Stacks.sliceMapArrow g W).left.op y)))) := by
  rw [← objRestrictCompArrowInv_comp_sliceBackArrow_left B S hS g W]
  refine Eq.trans (objRestrictPreimageIso_val_app_sliceBackArrow B S hS
    (restrictObjRestrictIso B S hS g θ) W y) ?_
  refine Eq.trans (restrictObjRestrictIso_cast_hom_val_app B S hS g θ
    ((Over.iteratedSliceForward Z).obj W) _ (M.val.map (Stacks.sliceBackArrow Z W).left.op y)
    (Eq.trans (cast_cast (objRestrict_obj_val_obj_eq B S hS Z M
        ((Over.iteratedSliceForward Z).obj W)).symm
      (objRestrict_obj_val_obj_eq B S hS Z M ((Over.iteratedSliceForward Z).obj W)) _)
      (cast_eq _ _))) ?_
  refine congrArg (fun tt => N.val.map (objRestrictCompArrow B S hS g
        ((Over.iteratedSliceForward Z).obj W)).op
      (cast (objRestrict_obj_val_obj_eq B S hS T N
          ((Over.map g.left).obj ((Over.iteratedSliceForward Z).obj W)))
        (θ.hom.val.app (op ((Over.map g.left).obj ((Over.iteratedSliceForward Z).obj W)))
          (cast (objRestrict_obj_val_obj_eq B S hS T M
              ((Over.map g.left).obj ((Over.iteratedSliceForward Z).obj W))).symm tt)))) ?_
  exact val_map_map M
    (objRestrictCompArrowInv B S hS g ((Over.iteratedSliceForward Z).obj W))
    (Stacks.sliceBackArrow Z W).left y

/-- **The transport of a local isomorphism across the bridge is the bridge of its restriction.**
For `g : Z ⟶ T` and `W` an object of the slice at `Z`, the component at `(Over.map g).obj W` of
the preimage of `θ` under the reindexing of Stacks 06WI is the component at `W` of the preimage
of `AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso` of `θ` along `g`.

Both components are restrictions along the arrow of the round trip of one and the same map —
`AlgebraicGeometry.BigFppfOver.objRestrictPreimageIso_val_map_sliceBackArrow_left` and
`…objRestrictPreimageIso_restrict_val_map_sliceBackArrow_left` — and that restriction is
injective, `Stacks.sliceBackArrow` being an isomorphism with the identity underneath.

This is the identity the agreement of Stacks 03DX (1) is transported along: the left-hand side is
what `AlgebraicGeometry.BigFppfOver.homRestr_objRestrictPreimageIso_eq_of_app` asks about and the
right-hand side is where the agreement in the `objRestrict` spelling is available. -/
public theorem objRestrictPreimageIso_hom_val_app_over_map {T Z : BigFppfOver B S hS}
    (g : Z ⟶ T) {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N) (W : Over Z) :
    (objRestrictPreimageIso B S hS θ).hom.val.app (op ((Over.map g).obj W)) =
      (objRestrictPreimageIso B S hS (restrictObjRestrictIso B S hS g θ)).hom.val.app
        (op W) := by
  refine ConcreteCategory.ext_apply fun y => ?_
  have hcancel : ∀ x, N.val.map (Stacks.sliceForthArrow Z W).left.op
      (N.val.map (Stacks.sliceBackArrow Z W).left.op x) = x := fun x => by
    rw [val_map_map, Stacks.sliceForthArrow_left_comp_sliceBackArrow_left, val_map_id]
  refine Eq.trans (Eq.symm (hcancel _)) (Eq.trans (congrArg
    (fun tt => N.val.map (Stacks.sliceForthArrow Z W).left.op tt) ?_) (hcancel _))
  exact Eq.trans (objRestrictPreimageIso_val_map_sliceBackArrow_left B S hS g θ W y)
    (Eq.symm (objRestrictPreimageIso_restrict_val_map_sliceBackArrow_left B S hS g θ W y))

/-! ### The agreement, and Stacks 03DX (1) -/

variable {I : Type w} (X : I → BigFppfOver B S hS) (G : SheafOfModules.{u} (structureSheaf B S hS))
  (F : ∀ i, (objScheme B S hS (X i)).Modules) (hF : ∀ i, (F i).IsQuasicoherent)
  (e : ∀ i, (associatedModule B (objScheme B S hS (X i))
    (contains_objScheme B S hS (X i))).obj (F i) ≅ (objRestrict B S hS (X i)).obj G)

/-- **The local isomorphisms of Stacks 03DX (1) agree over the fibre products, in the `homRestr`
spelling, with nothing assumed.**  This is the agreement in the `objRestrict` spelling
`AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso_effectiveGlueObjRestrictIso_eq`, carried
across the bridge by
`AlgebraicGeometry.BigFppfOver.objRestrictPreimageIso_hom_val_app_over_map` and read on the
relocalization by `AlgebraicGeometry.BigFppfOver.homRestr_objRestrictPreimageIso_eq_of_app`. -/
public theorem homRestr_objRestrictPreimageIso_effectiveGlueObjRestrictIso_eq
    (heff : (memberQcohDatum B S hS X G F hF e).IsEffective) (i j : I) :
    homRestr (commStructurePresheaf B S hS)
        ((associatedModule B S hS).obj (effectiveGlueModule B S hS X G F hF e heff)).val G.val
        (memberProdFst B S hS X i j)
        (objRestrictPreimageIso B S hS
          (effectiveGlueObjRestrictIso B S hS X G F hF e heff i)).hom.val =
      homRestr (commStructurePresheaf B S hS)
        ((associatedModule B S hS).obj (effectiveGlueModule B S hS X G F hF e heff)).val G.val
        (memberProdSnd B S hS X i j)
        (objRestrictPreimageIso B S hS
          (effectiveGlueObjRestrictIso B S hS X G F hF e heff j)).hom.val :=
  homRestr_objRestrictPreimageIso_eq_of_app B S hS (memberProdFst B S hS X i j)
    (memberProdSnd B S hS X i j) _ _ fun A =>
      Eq.trans (objRestrictPreimageIso_hom_val_app_over_map B S hS
          (memberProdFst B S hS X i j) _ A.unop)
        (Eq.trans (congrArg (fun Ξ => (objRestrictPreimageIso B S hS Ξ).hom.val.app (op A.unop))
            (restrictObjRestrictIso_effectiveGlueObjRestrictIso_eq B S hS X G F hF e heff
              (memberProdFst B S hS X i j) (memberProdSnd B S hS X i j)))
          (Eq.symm (objRestrictPreimageIso_hom_val_app_over_map B S hS
            (memberProdSnd B S hS X i j) _ A.unop)))

include F hF e in
/-- **The gluing step of Stacks 03DX (1), with nothing left but the covering family and its
local data.**  A sheaf of modules `𝒢` on `(Sch/S)_fppf`, a family `X` of objects covering the
final object whose structure morphisms are an fpqc covering family of `S`, and on each member a
quasi-coherent sheaf whose associated module is the restriction of `𝒢` there, exhibit `𝒢` in the
essential image of `𝓕 ↦ 𝓕^a`.

This is `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_agree` with its agreement
discharged by
`AlgebraicGeometry.BigFppfOver.homRestr_objRestrictPreimageIso_effectiveGlueObjRestrictIso_eq`. -/
public theorem essImage_associatedModuleQcoh_of_member
    (hX : (topology B S hS).CoversTop X)
    (hfpqc : (objHypercover B S hS X).presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S) :
    (associatedModuleQcoh B S hS).essImage G :=
  essImage_associatedModuleQcoh_of_agree B S hS X G F hF e hX hfpqc fun i j =>
    homRestr_objRestrictPreimageIso_effectiveGlueObjRestrictIso_eq B S hS X G F hF e
      (isEffective_memberQcohDatum B S hS X G F hF e hfpqc) i j

end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The descent datum of Stacks 03DX (1) for `τ = fppf`, with no assumption.**  For every sheaf
of modules `𝒢` on `(Sch/S)_fppf` and every family `Y` of objects covering the final object whose
structure morphisms are an fpqc covering family of `S` and on whose members the restriction of
`𝒢` is an associated module, there is an fpqc covering family of `S` and a quasi-coherent descent
datum for it whose effectivity exhibits `𝒢` as an associated module.

The quasi-coherent module and the local isomorphisms are the ones
`AlgebraicGeometry.BigFppfOver.effectiveGlueModule` and `…effectiveGlueObjRestrictIso` read off
the effectivity of `AlgebraicGeometry.BigFppfOver.memberQcohDatum`, and their agreement over the
fibre products is
`AlgebraicGeometry.BigFppfOver.homRestr_objRestrictPreimageIso_effectiveGlueObjRestrictIso_eq`. -/
public theorem associatedModuleRefinedDatum : AssociatedModuleRefinedDatum B S hS :=
  associatedModuleRefinedDatum_of_forall_objRestrict B S hS fun G J Y hY hfpqc hlocal => by
    choose F hFq hne using hlocal
    refine ⟨effectiveGlueModule B S hS Y G F hFq (fun j => (hne j).some)
        (isEffective_memberQcohDatum B S hS Y G F hFq (fun j => (hne j).some) hfpqc),
      isQuasicoherent_effectiveGlueModule B S hS Y G F hFq (fun j => (hne j).some)
        (isEffective_memberQcohDatum B S hS Y G F hFq (fun j => (hne j).some) hfpqc),
      effectiveGlueObjRestrictIso B S hS Y G F hFq (fun j => (hne j).some)
        (isEffective_memberQcohDatum B S hS Y G F hFq (fun j => (hne j).some) hfpqc),
      fun j₁ j₂ => ?_⟩
    exact homRestr_objRestrictPreimageIso_effectiveGlueObjRestrictIso_eq B S hS Y G F hFq
      (fun j => (hne j).some)
      (isEffective_memberQcohDatum B S hS Y G F hFq (fun j => (hne j).some) hfpqc) j₁ j₂

/-- **Stacks 03DX (1) for `τ = fppf`, essential surjectivity, with no assumption.**  Every
quasi-coherent `𝒪`-module on the big fppf site of `S` is isomorphic to `𝓕^a` for a quasi-coherent
`𝒪_S`-module `𝓕`.

This is `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule_of_refinedDatum`
with its descent datum discharged by
`AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum`.  Combined with
`AlgebraicGeometry.BigFppfOver.isEquivalence_associatedModuleQcohOnSite'` it gives the clause
itself: `𝓕 ↦ 𝓕^a` is an equivalence `QCoh(𝒪_S) ⥤ QCoh((Sch/S)_fppf, 𝒪)`.

The predicate is named in full.  `AlgebraicGeometry.SmallEtale` has a predicate of the same short
name for the small étale site, and the two statements would otherwise read identically while
being about different sites. -/
public theorem quasicoherentIsEssImageAssociatedModule' :
    AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule B S hS :=
  quasicoherentIsEssImageAssociatedModule_of_refinedDatum B S hS
    (associatedModuleRefinedDatum B S hS)

/-! ### Tag registration for clause (1) at `τ = fppf`

Clause (1) of Stacks 03DX at `τ = fppf` asks for essential surjectivity of `𝓕 ↦ 𝓕^a`, which is
the unconditional statement above, so it is registered against the tag by name rather than
restated.  The tag's small-étale form, clause (2), is registered in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleCounit.lean` and is untouched:
`add_to_stacks` is a command, not a declaration, so these are line comments. -/

-- Essential surjectivity of the clause's functor at the big fppf site.
add_to_stacks 03DX "clause (1) at τ = fppf: essential surjectivity of 𝓕 ↦ 𝓕^a onto the \
quasi-coherent 𝒪-modules of the big fppf site of S, with no assumption"
  quasicoherentIsEssImageAssociatedModule'

end AlgebraicGeometry.BigFppfOver

end
