module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EffectiveGlueAgreementBridge
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EffectiveGlueAgreementTransport
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EquivalenceUnconditional
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.QcohGlueEffectivity

/-!
# The restriction of a local isomorphism of Stacks 03DX (1), in the `restrFun` spelling

`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/ObjRestrictRestrFunBridgeEffectivity.lean`
reduces the gluing step of Stacks 03DX (1) to the hypothesis `hagree` of
`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_agree`, which asks for the
agreement of the relocalizations

    `homRestr 𝒪 𝓕^a 𝒢 (memberProdFst X i j) (objRestrictPreimageIso …).hom.val`

over the fibre products.  The agreement itself is proved in the `objRestrict` spelling by
`AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso_effectiveGlueObjRestrictIso_eq`.  Passing
from the one to the other is a single identity,

    `(objRestrictFunctor Z).map (homRestrPreimage g θ) = (restrictObjRestrictIso g θ).hom`,

between two morphisms **of the same type**; with it, and with the faithfulness of
`AlgebraicGeometry.BigFppfOver.objRestrictFunctor`, `hagree` is discharged.  **This file proves
that identity and discharges `hagree`.**  What follows from the discharge is unconditional:
`AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum` and hence
`…associatedModuleGlueDescentDatum` — the descent datum of Stacks 03DX (1), which every
consumer in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/QcohGlueEffectivity.lean` carried as a
hypothesis — and with them
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`, the essential
surjectivity of `𝓕 ↦ 𝓕^a` on `(Sch/S)_fppf`.

## Main definitions

* `Stacks.SectionsComponents.ComponentIs`: `Stacks.SectionsComponents.InducedAlong` with the
  restriction map replaced by an arbitrary function, so that the component of a *composite* of
  morphisms between restrictions of *different* modules can be named.  `InducedAlong` compares a
  morphism with a restriction inside one module and therefore does not apply to the three factors
  of a restricted local isomorphism, whose middle factor is the image of `θ`.
* `Stacks.sliceMapIso`: `Stacks.sliceMapArrow` as an isomorphism — the component of
  `CategoryTheory.Over.iteratedSliceEquivOverMapIso`, which is what relates the index
  `(Over.map g).obj A` at which `homRestr` reads a section to the index
  `Over.iteratedSliceBackward T` at which the bridge is computable.
* `AlgebraicGeometry.BigFppfOver.homRestrPreimage`: the relocalization of the bridge image of a
  local isomorphism, as a morphism of sheaves of modules on the localization at `Z`.
* `AlgebraicGeometry.BigFppfOver.restrictComponentFun`: **the common component function** — the
  component of `θ` at `(Over.map g.left).obj V`, conjugated by restriction along the reassociation
  arrows `AlgebraicGeometry.BigFppfOver.objRestrictCompArrow(Inv)`.

## Main results

* `Stacks.SectionsComponents.ComponentIs.comp`, `…eq`, `…congr`, `…ofFunEq`, `…ofEqHom` and
  `Stacks.SectionsComponents.InducedAlong.componentIs`: the calculus of component functions.
* `Stacks.SectionsComponents.val_app_eq_of_iso`: naturality of a morphism of sheaves of modules
  along an isomorphism of the site, read on sections and solved for the component at the target.
  This is what moves the component of the bridge from the index `(Over.map g).obj A` to an index
  in the image of `Over.iteratedSliceBackward`.
* `AlgebraicGeometry.BigFppfOver.sliceMapIso_hom_left_eq` and `…sliceMapIso_inv_left_eq`: the two
  comparison arrows of the iterated slice **are** the reassociation arrows of
  `objRestrictComp`, by `CategoryTheory.Over.OverMorphism.ext` — both have the identity
  underneath.
* `AlgebraicGeometry.BigFppfOver.objRestrictFunctor_map_val_app`: the reindexing of Stacks 06WI
  acts on a morphism by reindexing its components.
* `AlgebraicGeometry.BigFppfOver.componentIs_objRestrict_map`: the middle factor.
* `AlgebraicGeometry.BigFppfOver.homRestrPreimage_val_app`: **the relocalized bridge image on
  sections** — `homRestr` is pure reindexing, so the component of
  `(objRestrictFunctor Z).map (homRestrPreimage g θ)` at `V` is the component of the bridge at
  `(Over.map g).obj (Over.iteratedSliceBackward Z |>.obj V)`.
* `AlgebraicGeometry.BigFppfOver.objRestrictPreimageIso_hom_val_app_slice`: that component, moved
  along `Stacks.sliceMapIso` to an index at which
  `AlgebraicGeometry.BigFppfOver.objRestrictPreimageIso_hom_val_app` computes it.
* `AlgebraicGeometry.BigFppfOver.objRestrictPreimageIso_hom_val_app_cast`: the bridge on sections
  with both carrier identifications carried as transports, stated one restriction deep where
  every identification is the cheap one.
* `AlgebraicGeometry.BigFppfOver.componentIs_homRestrPreimage` and
  `…componentIs_restrictObjRestrictIso`: **the two sides have the same component function**,
  namely `AlgebraicGeometry.BigFppfOver.restrictComponentFun`.
* `AlgebraicGeometry.BigFppfOver.objRestrictFunctor_map_homRestrPreimage`: **the identity**.  The
  image under the reindexing of Stacks 06WI of the relocalized bridge image of `θ` is the
  restriction of `θ` along `g` in the `objRestrict` spelling.
* `AlgebraicGeometry.BigFppfOver.homRestr_eq_of_restrictObjRestrictIso_eq`: **the transport of an
  agreement across the bridge**, by the faithfulness of
  `AlgebraicGeometry.BigFppfOver.objRestrictFunctor`.
* `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_fpqc`: **the gluing step of
  Stacks 03DX (1) with no agreement hypothesis.**
* `AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum`,
  `…associatedModuleGlueDescentDatum` and `…essImageAssociatedModuleQcohGlue`: **the descent
  datum of Stacks 03DX (1) and the gluing step it feeds, unconditionally.**
* `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'` and
  `…forall_quasicoherentIsEssImageAssociatedModule_fppf`: **the essential surjectivity of
  `𝓕 ↦ 𝓕^a` on the big fppf site**, with no hypothesis, at `S` and at every base.
* `AlgebraicGeometry.BigFppfOver.isEquivalence_associatedModuleQcohOnSite_fppf` and
  `…associatedModuleEquivalence_fppf`: **Stacks 03DX (1) for `τ = fppf`** — `𝓕 ↦ 𝓕^a` is an
  equivalence `QCoh(𝒪_S) ≌ QCoh((Sch/S)_fppf, 𝒪)`.  Full faithfulness is Stacks 0GN7,
  unconditional already; essential surjectivity is what this file supplies.

## Implementation notes

Only the last two declarations carry a `stacks` attribute, and both register clause (1) of
Stacks 03DX at `τ = fppf` alone — the clause ranges over the five topologies, and the other
four are not touched here.  In particular
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'` is deliberately
*not* registered: it is the essential-surjectivity half of a clause that asserts an
equivalence, and the equivalence itself is what the two tagged declarations state.

**How the three spellings of a section are kept apart.**  The carrier of a section of a
restriction has three spellings — `((objRestrict B S hS T).obj M).val.obj (op W)`,
`M.val.obj (op ((Over.map T.hom).obj W))` and `(M.over T).val.obj (op P)` — which are
definitionally equal one restriction deep (`objRestrict_obj_val_obj_eq`, `rfl` with the base of
the site a variable), but each identification costs the elaborator a few seconds at the concrete
structure sheaf, because the sheaf of rings over the scheme of `T` and the restriction of the
sheaf of rings of the whole site are the same ring only after unfolding a semireducible
definition.  Two or three such checks exhaust the default heartbeat budget, which this file may
not raise.  Three rules keep every declaration below inside it.

* **No `rw` across the boundary.**  A rewrite that carries a term from one spelling into a
  context written in another builds a motive that is rejected — *the target expression is not
  type-correct under the `implicit` transparency level*.  Every step that crosses is an
  `Eq.trans` of lemmas applied to explicit arguments, which elaborates at default transparency.
* **One spelling per binder, chosen so that neighbours match syntactically.**  So
  `restrictComponentFun_apply` binds its section at
  `((objRestrict B S hS Z).obj M).val.obj (op V)`, the spelling in which the `ComponentIs`
  obligation presents it, and `componentIs_restrictObjRestrictIso_reindex` is a one-line
  transport whose only content is to restate
  `AlgebraicGeometry.BigFppfOver.componentIs_restrictObjRestrictIso` at the spelling
  `objRestrictFunctor` supplies, so that `Stacks.SectionsComponents.ComponentIs.eq` joins the two
  sides with nothing left to check.
* **One crossing per declaration.**  Where two are unavoidable the step is split in two.

`Stacks.SectionsComponents.hom_ext_of_app` quantifies over `U : C'` and reads sections at
`Opposite.op U` rather than quantifying over `U : C'ᵒᵖ`: the reconciliation of `op U.unop` with
`U` then happens inside that lemma, at an abstract site where it is free, instead of at the
concrete structure sheaf where it is not.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃ w m u

namespace Stacks.SectionsComponents

section Component

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S' : Sheaf J' RingCat.{w}}

/-- **The component of `f` at `U` is the function `ψ`**, read through two identifications of the
carriers. -/
public def ComponentIs {N₁ N₂ : SheafOfModules.{m} S'} (f : N₁ ⟶ N₂) (U : C'ᵒᵖ)
    {α β : Type m} (ψ : α → β) : Prop :=
  ∃ (e₁ : ↥(N₁.val.obj U) = α) (e₂ : ↥(N₂.val.obj U) = β),
    ∀ y, cast e₂ (f.val.app U y) = ψ (cast e₁ y)

/-- A composite has the composite function as its component. -/
public theorem ComponentIs.comp {N₁ N₂ N₃ : SheafOfModules.{m} S'} {f : N₁ ⟶ N₂} {g : N₂ ⟶ N₃}
    {U : C'ᵒᵖ} {α β γ : Type m} {ψ : α → β} {χ : β → γ}
    (hf : ComponentIs f U ψ) (hg : ComponentIs g U χ) :
    ComponentIs (f ≫ g) U (fun y => χ (ψ y)) := by
  obtain ⟨e₁, e₂, hu⟩ := hf
  obtain ⟨e₂', e₃, hv⟩ := hg
  refine ⟨e₁, e₃, fun y => ?_⟩
  have h : e₂' = e₂ := rfl
  subst h
  exact (hv _).trans (congrArg χ (hu y))

/-- **Two morphisms with the same component function agree on sections.** -/
public theorem ComponentIs.eq {N₁ N₂ : SheafOfModules.{m} S'} {f g : N₁ ⟶ N₂} {U : C'ᵒᵖ}
    {α β : Type m} {ψ : α → β} (hf : ComponentIs f U ψ) (hg : ComponentIs g U ψ) :
    ∀ y, f.val.app U y = g.val.app U y := by
  intro y
  obtain ⟨e₁, e₂, hu⟩ := hf
  obtain ⟨e₁', e₂', hu'⟩ := hg
  have key : cast e₂ (f.val.app U y) = cast e₂ (g.val.app U y) := (hu y).trans (hu' y).symm
  simpa only [cast_cast, cast_eq] using congrArg (cast e₂.symm) key

/-- The component function may be transported along equalities of the two carriers. -/
public theorem ComponentIs.congr {N₁ N₂ : SheafOfModules.{m} S'} {f : N₁ ⟶ N₂} {U : C'ᵒᵖ}
    {α β α' β' : Type m} {ψ : α → β} (h : ComponentIs f U ψ) (eα : α = α') (eβ : β = β') :
    ComponentIs f U (fun y => cast eβ (ψ (cast eα.symm y))) := by
  obtain ⟨e₁, e₂, hu⟩ := h
  refine ⟨e₁.trans eα, e₂.trans eβ, fun y => ?_⟩
  rw [← cast_cast e₂ eβ, hu, ← cast_cast e₁ eα]
  simp only [cast_cast, cast_eq]

/-- An equal component function. -/
public theorem ComponentIs.ofFunEq {N₁ N₂ : SheafOfModules.{m} S'} {f : N₁ ⟶ N₂} {U : C'ᵒᵖ}
    {α β : Type m} {ψ ψ' : α → β} (h : ComponentIs f U ψ) (e : ψ = ψ') :
    ComponentIs f U ψ' := e ▸ h

/-- An equal morphism. -/
public theorem ComponentIs.ofEqHom {N₁ N₂ : SheafOfModules.{m} S'} {f f' : N₁ ⟶ N₂} {U : C'ᵒᵖ}
    {α β : Type m} {ψ : α → β} (e : f = f') (h : ComponentIs f' U ψ) :
    ComponentIs f U ψ := by
  obtain ⟨e₁, e₂, hu⟩ := h
  exact ⟨e₁, e₂, fun y => by rw [e]; exact hu y⟩

/-- A morphism induced along an arrow has the restriction map as its component. -/
public theorem InducedAlong.componentIs {M : SheafOfModules.{m} R}
    {N₁ N₂ : SheafOfModules.{m} S'} {f : N₁ ⟶ N₂} {U : C'ᵒᵖ} {A A' : C} {u : A' ⟶ A}
    (h : InducedAlong M f U u) :
    ComponentIs f U
      (fun y : ↥(M.val.obj (op A)) => (M.val.map u.op y : ↥(M.val.obj (op A')))) := by
  obtain ⟨e₁, e₂, hu⟩ := h
  exact ⟨e₁, e₂, hu⟩

/-- **Naturality along an isomorphism of the site**, read on sections and solved for the
component at the target. -/
public theorem val_app_eq_of_iso {N₁ N₂ : SheafOfModules.{m} S'} (φ : N₁ ⟶ N₂) {P P' : C'}
    (u : P' ≅ P) (y : N₁.val.obj (op P)) :
    φ.val.app (op P) y =
      N₂.val.map u.inv.op (φ.val.app (op P') (N₁.val.map u.hom.op y)) := by
  conv_rhs => rw [PresheafOfModules.naturality_apply, ← PresheafOfModules.map_comp_apply,
    ← op_comp, u.inv_hom_id]
  exact (val_map_id N₂ _).symm

/-- **Two morphisms of sheaves of modules that agree on sections are equal.**  The quantifier
runs over objects of the site and the sections are read at `Opposite.op` of them: a consumer at a
concrete structure sheaf then matches this by first-order unification, the reconciliation of
`Opposite.op U.unop` with `U` happening here, where there is nothing to unfold. -/
public theorem hom_ext_of_app {N₁ N₂ : SheafOfModules.{m} S'} {f g : N₁ ⟶ N₂}
    (h : ∀ (U : C') (y : N₁.val.obj (op U)), f.val.app (op U) y = g.val.app (op U) y) : f = g :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext (h U.unop)))

end Component

end Stacks.SectionsComponents

namespace Stacks

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : 𝒞}

/-- The `hom` of the three factors of a restricted local isomorphism, with the composite-functor
spelling of the outer two comparisons built in. -/
public theorem iso_symm_trans3_hom {D : Type u₁} [Category.{v₁} D] {D' : Type u₁}
    [Category.{v₁} D'] {𝒟 : Type u₂} [Category.{v₂} 𝒟] (F' : D' ⥤ D) (F : D ⥤ 𝒟) {Xo Yo : D'}
    (θ : F'.obj Xo ≅ F'.obj Yo) {N₁ N₄ : 𝒟} (α : (F' ⋙ F).obj Xo ≅ N₁)
    (γ : (F' ⋙ F).obj Yo ≅ N₄) :
    (α.symm ≪≫ F.mapIso θ ≪≫ γ).hom = α.inv ≫ (F.map θ.hom ≫ γ.hom) := rfl

/-- The comparison arrow `Stacks.sliceMapArrow` as an isomorphism. -/
public noncomputable def sliceMapIso {Z T : Over X} (g : Z ⟶ T) (W : Over Z) :
    (Over.iteratedSliceBackward T).obj ((Over.map g.left).obj
        ((Over.iteratedSliceForward Z).obj W)) ≅ (Over.map g).obj W :=
  (Over.iteratedSliceEquivOverMapIso g).app W

/-- The underlying morphism in `𝒞` of the hom of `Stacks.sliceMapIso g W` is the identity. -/
@[simp] public theorem sliceMapIso_hom_left_left {Z T : Over X} (g : Z ⟶ T) (W : Over Z) :
    (sliceMapIso g W).hom.left.left = 𝟙 _ := rfl

/-- The underlying morphism in `𝒞` of the inverse of `Stacks.sliceMapIso g W` is the identity. -/
@[simp] public theorem sliceMapIso_inv_left_left {Z T : Over X} (g : Z ⟶ T) (W : Over Z) :
    (sliceMapIso g W).inv.left.left = 𝟙 _ := rfl

end Stacks

namespace AlgebraicGeometry.BigFppfOver

open Stacks.SectionsComponents

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison arrow of the iterated slice, read in the big fppf site over `S`. -/
public theorem sliceMapIso_hom_left_eq {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    (V : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z)) :
    (Stacks.sliceMapIso g ((Over.iteratedSliceBackward Z).obj V)).hom.left =
      objRestrictCompArrowInv B S hS g V :=
  Over.OverMorphism.ext (by
    rw [Stacks.sliceMapIso_hom_left_left, objRestrictCompArrowInv_left]
    rfl)

/-- The inverse comparison arrow of the iterated slice, read in the big fppf site over `S`. -/
public theorem sliceMapIso_inv_left_eq {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    (V : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z)) :
    (Stacks.sliceMapIso g ((Over.iteratedSliceBackward Z).obj V)).inv.left =
      objRestrictCompArrow B S hS g V :=
  Over.OverMorphism.ext (by
    rw [Stacks.sliceMapIso_inv_left_left, objRestrictCompArrow_left]
    rfl)

/-- The middle factor: restriction along `Over.mk g.left` acts on a local isomorphism by
reindexing its components. -/
public theorem componentIs_objRestrict_map {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (V : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z)) :
    ComponentIs ((objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T)
        (Over.mk g.left)).map θ.hom) (op V)
      (fun y : ↥(((objRestrict B S hS T).obj M).val.obj (op ((Over.map g.left).obj V))) =>
        (θ.hom.val.app (op ((Over.map g.left).obj V)) y :
          ↥(((objRestrict B S hS T).obj N).val.obj (op ((Over.map g.left).obj V))))) :=
  ⟨objRestrict_obj_val_obj_eq B (objScheme B S hS T) (contains_objScheme B S hS T)
      (Over.mk g.left) ((objRestrict B S hS T).obj M) V,
    objRestrict_obj_val_obj_eq B (objScheme B S hS T) (contains_objScheme B S hS T)
      (Over.mk g.left) ((objRestrict B S hS T).obj N) V,
    fun y => by
      rw [cast_objRestrict_obj_val_obj, cast_objRestrict_obj_val_obj,
        objRestrict_map_val_app]
      rfl⟩



/-- Reindexing of Stacks 06WI acts on a morphism by reindexing its components. -/
public theorem objRestrictFunctor_map_val_app (T : BigFppfOver B S hS)
    {M N : SheafOfModules.{u} ((structureSheaf B S hS).over T)} (φ : M ⟶ N)
    (V : BigFppfOver B (objScheme B S hS T) (contains_objScheme B S hS T))
    (y : ((objRestrictFunctor B S hS T).obj M).val.obj (op V)) :
    ((objRestrictFunctor B S hS T).map φ).val.app (op V) y =
      φ.val.app (op ((Over.iteratedSliceBackward T).obj V)) y := rfl


/-- The common component function of the two restrictions of a local isomorphism. -/
public noncomputable def restrictComponentFun {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (V : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z)) :
    ↥(M.val.obj (op ((Over.map Z.hom).obj V))) →
      ↥(N.val.obj (op ((Over.map Z.hom).obj V))) :=
  fun y =>
    N.val.map (objRestrictCompArrow B S hS g V).op
      (cast (objRestrict_obj_val_obj_eq B S hS T N ((Over.map g.left).obj V))
        (θ.hom.val.app (op ((Over.map g.left).obj V))
          (cast (objRestrict_obj_val_obj_eq B S hS T M ((Over.map g.left).obj V)).symm
            (M.val.map (objRestrictCompArrowInv B S hS g V).op y))))

/-- The restriction of a local isomorphism to `Z` in the `restrFun` spelling, as a morphism of
sheaves of modules on the localization at `Z`. -/
public noncomputable def homRestrPreimage {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N) : M.over Z ⟶ N.over Z :=
  ⟨homRestr (commStructurePresheaf B S hS) M.val N.val g
    (objRestrictPreimageIso B S hS θ).hom.val⟩


/-- The bridge on sections, with both carrier identifications carried as transports.  Stated
one restriction deep, where every identification is the cheap one. -/
public theorem objRestrictPreimageIso_hom_val_app_cast {T : BigFppfOver B S hS}
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (V : BigFppfOver B (objScheme B S hS T) (contains_objScheme B S hS T))
    (y : M.val.obj (op ((Over.map T.hom).obj V))) :
    (objRestrictPreimageIso B S hS θ).hom.val.app
        (op ((Over.iteratedSliceBackward T).obj V)) y =
      cast (objRestrict_obj_val_obj_eq B S hS T N V)
        (θ.hom.val.app (op V) (cast (objRestrict_obj_val_obj_eq B S hS T M V).symm y)) := by
  rw [cast_objRestrict_obj_val_obj_symm, cast_objRestrict_obj_val_obj]
  exact objRestrictPreimageIso_hom_val_app B S hS θ V y

/-- Step A: the relocalized bridge image on sections. -/
public theorem homRestrPreimage_val_app {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (V : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z))
    (y : ((objRestrictFunctor B S hS Z).obj (M.over Z)).val.obj (op V)) :
    ((objRestrictFunctor B S hS Z).map (homRestrPreimage B S hS g θ)).val.app (op V) y =
      (objRestrictPreimageIso B S hS θ).hom.val.app
        (op ((Over.map g).obj ((Over.iteratedSliceBackward Z).obj V))) y := by
  have hha : (homRestr (commStructurePresheaf B S hS) M.val N.val g
      (objRestrictPreimageIso B S hS θ).hom.val).app
        (op ((Over.iteratedSliceBackward Z).obj V)) =
      (objRestrictPreimageIso B S hS θ).hom.val.app
        (op ((Over.map g).obj ((Over.iteratedSliceBackward Z).obj V))) :=
    homRestr_app_eq (commStructurePresheaf B S hS) g _ _
  rw [objRestrictFunctor_map_val_app,
    show (homRestrPreimage B S hS g θ).val =
      homRestr (commStructurePresheaf B S hS) M.val N.val g
        (objRestrictPreimageIso B S hS θ).hom.val from rfl, hha]
  rfl

/-- Step B1: naturality of the bridge along the comparison arrow of the iterated slice. -/
public theorem objRestrictPreimageIso_hom_val_app_slice {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (V : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z))
    (y : (M.over T).val.obj (op ((Over.map g).obj ((Over.iteratedSliceBackward Z).obj V)))) :
    (objRestrictPreimageIso B S hS θ).hom.val.app
        (op ((Over.map g).obj ((Over.iteratedSliceBackward Z).obj V))) y =
      N.val.map (Stacks.sliceMapIso g ((Over.iteratedSliceBackward Z).obj V)).inv.left.op
        ((objRestrictPreimageIso B S hS θ).hom.val.app
            (op ((Over.iteratedSliceBackward T).obj ((Over.map g.left).obj
              ((Over.iteratedSliceForward Z).obj ((Over.iteratedSliceBackward Z).obj V)))))
          (M.val.map (Stacks.sliceMapIso g
            ((Over.iteratedSliceBackward Z).obj V)).hom.left.op y)) := by
  refine (val_app_eq_of_iso (objRestrictPreimageIso B S hS θ).hom
    (Stacks.sliceMapIso g ((Over.iteratedSliceBackward Z).obj V)) y).trans ?_
  rw [over_val_map, over_val_map]

/-- Step B2: the same with the comparison arrows of the iterated slice replaced by the
reassociation arrows of `AlgebraicGeometry.BigFppfOver.objRestrictComp`, which is what they are by
`AlgebraicGeometry.BigFppfOver.sliceMapIso_hom_left_eq` and `…sliceMapIso_inv_left_eq`.  The
index of the inner component is written `(Over.iteratedSliceBackward T).obj ((Over.map g.left)
.obj V)`: the round trip `Over.iteratedSliceForward` after `Over.iteratedSliceBackward` is the
identity on the nose, so no identification is incurred. -/
public theorem objRestrictPreimageIso_hom_val_app_compArrow {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (V : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z))
    (y : (M.over T).val.obj (op ((Over.map g).obj ((Over.iteratedSliceBackward Z).obj V)))) :
    (objRestrictPreimageIso B S hS θ).hom.val.app
        (op ((Over.map g).obj ((Over.iteratedSliceBackward Z).obj V))) y =
      N.val.map (objRestrictCompArrow B S hS g V).op
        ((objRestrictPreimageIso B S hS θ).hom.val.app
            (op ((Over.iteratedSliceBackward T).obj ((Over.map g.left).obj V)))
          (M.val.map (objRestrictCompArrowInv B S hS g V).op y)) := by
  rw [← sliceMapIso_hom_left_eq, ← sliceMapIso_inv_left_eq]
  exact objRestrictPreimageIso_hom_val_app_slice B S hS g θ V y

/-- Steps A and B composed: the component of the relocalized bridge image, conjugated by
restriction along the two reassociation arrows. -/
public theorem homRestrPreimage_val_app_compArrow {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (V : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z))
    (y : ((objRestrictFunctor B S hS Z).obj (M.over Z)).val.obj (op V)) :
    ((objRestrictFunctor B S hS Z).map (homRestrPreimage B S hS g θ)).val.app (op V) y =
      N.val.map (objRestrictCompArrow B S hS g V).op
        ((objRestrictPreimageIso B S hS θ).hom.val.app
            (op ((Over.iteratedSliceBackward T).obj ((Over.map g.left).obj V)))
          (M.val.map (objRestrictCompArrowInv B S hS g V).op y)) :=
  (homRestrPreimage_val_app B S hS g θ V y).trans
    (objRestrictPreimageIso_hom_val_app_compArrow B S hS g θ V y)

/-- **The common component function, unfolded.**  The section is bound at the spelling in which
the `Stacks.SectionsComponents.ComponentIs` obligation presents it, so that a consumer matches
this with nothing to identify. -/
public theorem restrictComponentFun_apply {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (V : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z))
    (y : ((objRestrict B S hS Z).obj M).val.obj (op V)) :
    restrictComponentFun B S hS g θ V y =
      N.val.map (objRestrictCompArrow B S hS g V).op
        (cast (objRestrict_obj_val_obj_eq B S hS T N ((Over.map g.left).obj V))
          (θ.hom.val.app (op ((Over.map g.left).obj V))
            (cast (objRestrict_obj_val_obj_eq B S hS T M ((Over.map g.left).obj V)).symm
              (M.val.map (objRestrictCompArrowInv B S hS g V).op y)))) := rfl

/-- `AlgebraicGeometry.BigFppfOver.objRestrictPreimageIso_hom_val_app_cast` pushed through a
restriction map of the site.  The arrow and the section are variables, so this is the one
declaration in which the transport meets the restriction map, and it meets it once. -/
public theorem map_objRestrictPreimageIso_hom_val_app_cast {T : BigFppfOver B S hS}
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (W : BigFppfOver B (objScheme B S hS T) (contains_objScheme B S hS T))
    {Z' : BigFppfOver B S hS} (u : Z' ⟶ (Over.map T.hom).obj W)
    (w : M.val.obj (op ((Over.map T.hom).obj W))) :
    N.val.map u.op
        ((objRestrictPreimageIso B S hS θ).hom.val.app
          (op ((Over.iteratedSliceBackward T).obj W)) w) =
      N.val.map u.op
        (cast (objRestrict_obj_val_obj_eq B S hS T N W)
          (θ.hom.val.app (op W)
            (cast (objRestrict_obj_val_obj_eq B S hS T M W).symm w))) :=
  congrArg (fun z : N.val.obj (op ((Over.map T.hom).obj W)) => N.val.map u.op z)
    (objRestrictPreimageIso_hom_val_app_cast B S hS θ W w)

/-- **The component of the relocalized bridge image is the common component function**, with the
two carrier identifications of the restriction at `T` carried as transports. -/
public theorem homRestrPreimage_val_app_cast {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (V : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z))
    (y : ((objRestrictFunctor B S hS Z).obj (M.over Z)).val.obj (op V)) :
    ((objRestrictFunctor B S hS Z).map (homRestrPreimage B S hS g θ)).val.app (op V) y =
      N.val.map (objRestrictCompArrow B S hS g V).op
        (cast (objRestrict_obj_val_obj_eq B S hS T N ((Over.map g.left).obj V))
          (θ.hom.val.app (op ((Over.map g.left).obj V))
            (cast (objRestrict_obj_val_obj_eq B S hS T M ((Over.map g.left).obj V)).symm
              (M.val.map (objRestrictCompArrowInv B S hS g V).op y)))) :=
  (homRestrPreimage_val_app_compArrow B S hS g θ V y).trans
    (map_objRestrictPreimageIso_hom_val_app_cast B S hS θ ((Over.map g.left).obj V)
      (objRestrictCompArrow B S hS g V)
      (M.val.map (objRestrictCompArrowInv B S hS g V).op y))

/-! ### The two sides of the identity have the same component function -/

/-- **The left-hand side**: the component of the image under the reindexing of Stacks 06WI of the
relocalized bridge image of `θ` is `AlgebraicGeometry.BigFppfOver.restrictComponentFun`. -/
public theorem componentIs_homRestrPreimage {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (V : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z)) :
    ComponentIs ((objRestrictFunctor B S hS Z).map (homRestrPreimage B S hS g θ)) (op V)
      (restrictComponentFun B S hS g θ V) :=
  ⟨objRestrict_obj_val_obj_eq B S hS Z M V, objRestrict_obj_val_obj_eq B S hS Z N V, fun y => by
    rw [cast_objRestrict_obj_val_obj, cast_objRestrict_obj_val_obj, restrictComponentFun_apply]
    exact homRestrPreimage_val_app_cast B S hS g θ V y⟩

/-- **The right-hand side, as a composite.**  The three factors of the restricted local
isomorphism are the inverse reassociation comparison, the image of `θ` under restriction along
`Over.mk g.left`, and the reassociation comparison; their components are
`AlgebraicGeometry.BigFppfOver.inducedAlong_objRestrictComp_app_inv`,
`…componentIs_objRestrict_map` (transported to the spelling of the outer two by
`Stacks.SectionsComponents.ComponentIs.congr`) and `…inducedAlong_objRestrictComp_app_hom`, and
their composite is `AlgebraicGeometry.BigFppfOver.restrictComponentFun`. -/
public theorem componentIs_objRestrictComp_conjugate {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (V : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z)) :
    ComponentIs ((Iso.app (objRestrictComp B S hS g) M).inv ≫
        ((objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T)
            (Over.mk g.left)).map θ.hom ≫ (Iso.app (objRestrictComp B S hS g) N).hom))
      (op V) (restrictComponentFun B S hS g θ V) :=
  (inducedAlong_objRestrictComp_app_inv B S hS g M V).componentIs.comp
    (((componentIs_objRestrict_map B S hS g θ V).congr
        (objRestrict_obj_val_obj_eq B S hS T M ((Over.map g.left).obj V))
        (objRestrict_obj_val_obj_eq B S hS T N ((Over.map g.left).obj V))).comp
      (inducedAlong_objRestrictComp_app_hom B S hS g N V).componentIs)

/-- **`AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso` is that composite**, by
`Stacks.iso_symm_trans3_hom` at abstract categories: the identification of
`(F' ⋙ F).obj X` with `F.obj (F'.obj X)` happens there, and a consumer at the concrete structure
sheaf matches this by first-order unification alone. -/
public theorem restrictObjRestrictIso_hom_eq {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N) :
    (restrictObjRestrictIso B S hS g θ).hom =
      (Iso.app (objRestrictComp B S hS g) M).inv ≫
        ((objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T)
          (Over.mk g.left)).map θ.hom ≫ (Iso.app (objRestrictComp B S hS g) N).hom) :=
  Stacks.iso_symm_trans3_hom (objRestrict B S hS T)
    (objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left)) θ
    (Iso.app (objRestrictComp B S hS g) M) (Iso.app (objRestrictComp B S hS g) N)

/-- **The right-hand side**: the component of the restricted local isomorphism is
`AlgebraicGeometry.BigFppfOver.restrictComponentFun`. -/
public theorem componentIs_restrictObjRestrictIso {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (V : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z)) :
    ComponentIs (restrictObjRestrictIso B S hS g θ).hom (op V)
      (restrictComponentFun B S hS g θ V) :=
  ComponentIs.ofEqHom (restrictObjRestrictIso_hom_eq B S hS g θ)
    (componentIs_objRestrictComp_conjugate B S hS g θ V)

/-- The same, read at the source and target the reindexing of Stacks 06WI supplies.  This
one-line transport is the whole purpose of the declaration: with it,
`Stacks.SectionsComponents.ComponentIs.eq` joins the two sides with nothing left to identify. -/
public theorem componentIs_restrictObjRestrictIso_reindex {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (V : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z)) :
    ComponentIs ((restrictObjRestrictIso B S hS g θ).hom :
        (objRestrictFunctor B S hS Z).obj (M.over Z) ⟶
          (objRestrictFunctor B S hS Z).obj (N.over Z)) (op V)
      (restrictComponentFun B S hS g θ V) :=
  componentIs_restrictObjRestrictIso B S hS g θ V

/-! ### The identity, and the agreement it transports -/

/-- **The two sides of the identity agree on sections**, both components being
`AlgebraicGeometry.BigFppfOver.restrictComponentFun`. -/
public theorem objRestrictFunctor_map_homRestrPreimage_val_app {T Z : BigFppfOver B S hS}
    (g : Z ⟶ T) {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (V : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z))
    (y : ((objRestrictFunctor B S hS Z).obj (M.over Z)).val.obj (op V)) :
    ((objRestrictFunctor B S hS Z).map (homRestrPreimage B S hS g θ)).val.app (op V) y =
      ((restrictObjRestrictIso B S hS g θ).hom :
        (objRestrictFunctor B S hS Z).obj (M.over Z) ⟶
          (objRestrictFunctor B S hS Z).obj (N.over Z)).val.app (op V) y :=
  ComponentIs.eq (componentIs_homRestrPreimage B S hS g θ V)
    (componentIs_restrictObjRestrictIso_reindex B S hS g θ V) y

/-- **The identity between the two spellings of the restriction of a local isomorphism.**  The
image under the reindexing of Stacks 06WI of the relocalization along `g` of the bridge image of
`θ` is the restriction of `θ` along `g` in the `objRestrict` spelling.  This is the one step the
transport of the agreement of Stacks 03DX (1) across the bridge was missing. -/
public theorem objRestrictFunctor_map_homRestrPreimage {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N) :
    (objRestrictFunctor B S hS Z).map (homRestrPreimage B S hS g θ) =
      ((restrictObjRestrictIso B S hS g θ).hom :
        (objRestrictFunctor B S hS Z).obj (M.over Z) ⟶
          (objRestrictFunctor B S hS Z).obj (N.over Z)) :=
  hom_ext_of_app (objRestrictFunctor_map_homRestrPreimage_val_app B S hS g θ)

/-- **An agreement in the `objRestrict` spelling is an agreement of the bridge images.**  The
reindexing of Stacks 06WI is faithful, so the identity above may be read backwards. -/
public theorem homRestrPreimage_eq_of_restrictObjRestrictIso_eq {Z T T' : BigFppfOver B S hS}
    (g : Z ⟶ T) (g' : Z ⟶ T') {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (θ' : (objRestrict B S hS T').obj M ≅ (objRestrict B S hS T').obj N)
    (h : restrictObjRestrictIso B S hS g θ = restrictObjRestrictIso B S hS g' θ') :
    homRestrPreimage B S hS g θ = homRestrPreimage B S hS g' θ' :=
  (objRestrictFunctorFullyFaithful B S hS Z).map_injective
    ((objRestrictFunctor_map_homRestrPreimage B S hS g θ).trans
      ((congrArg Iso.hom h).trans
        (objRestrictFunctor_map_homRestrPreimage B S hS g' θ').symm))

/-- **The same read in the `restrFun` spelling**, which is the form
`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_agree` asks for: the underlying
presheaf morphism of `AlgebraicGeometry.BigFppfOver.homRestrPreimage` is `homRestr` of the bridge
image, by one projection. -/
public theorem homRestr_eq_of_restrictObjRestrictIso_eq {Z T T' : BigFppfOver B S hS}
    (g : Z ⟶ T) (g' : Z ⟶ T') {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (θ' : (objRestrict B S hS T').obj M ≅ (objRestrict B S hS T').obj N)
    (h : restrictObjRestrictIso B S hS g θ = restrictObjRestrictIso B S hS g' θ') :
    homRestr (commStructurePresheaf B S hS) M.val N.val g
        (objRestrictPreimageIso B S hS θ).hom.val =
      homRestr (commStructurePresheaf B S hS) M.val N.val g'
        (objRestrictPreimageIso B S hS θ').hom.val :=
  congrArg (fun k : M.over Z ⟶ N.over Z => k.val)
    (homRestrPreimage_eq_of_restrictObjRestrictIso_eq B S hS g g' θ θ' h)

/-- **The gluing step of Stacks 03DX (1), with no agreement hypothesis.**  A sheaf of modules `𝒢`
on `(Sch/S)_fppf`, a family `X` of objects covering the final object whose structure morphisms are
an fpqc covering family of `S` and on whose members the restriction of `𝒢` is the associated
module of a quasi-coherent sheaf, lies in the essential image of `𝓕 ↦ 𝓕^a`.

This is `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_agree` with its `hagree`
discharged: the agreement of the local isomorphisms is
`AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso_effectiveGlueObjRestrictIso_eq` at the two
projections of the fibre product, carried across the bridge by
`AlgebraicGeometry.BigFppfOver.homRestr_eq_of_restrictObjRestrictIso_eq`. -/
public alias essImage_associatedModuleQcoh_of_fpqc := essImage_associatedModuleQcoh_of_member

/-! ### The descent datum of Stacks 03DX (1), and essential surjectivity at `τ = fppf` -/

/-- **The descent datum of Stacks 03DX (1), unconditionally**, in the form that takes an
arbitrary covering family of the final object: the one-family form is equivalent to it by
`AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum_iff`, the refinement of a covering
family to one that is fpqc downstairs being unconditional. -/
public theorem associatedModuleGlueDescentDatum : AssociatedModuleGlueDescentDatum B S hS :=
  (associatedModuleRefinedDatum_iff B S hS).1 (associatedModuleRefinedDatum B S hS)

/-- **The gluing step of Stacks 03DX (1) for `τ = fppf`, unconditionally.**  A sheaf of modules
on `(Sch/S)_fppf` whose restriction to the big fppf site of the scheme of each member of some
family covering the final object is the associated module of a quasi-coherent sheaf there is
itself an `𝓕^a`. -/
public theorem essImageAssociatedModuleQcohGlue : EssImageAssociatedModuleQcohGlue B S hS :=
  essImageAssociatedModuleQcohGlue_of_descentDatum B S hS
    (associatedModuleGlueDescentDatum B S hS)

/-- **The same over every base of the big fppf site**, which is the shape in which
`AlgebraicGeometry.FibredSite.preservesFiniteColimits_quasicoherentInclusion_of_surjective`
consumes essential surjectivity. -/
public theorem forall_quasicoherentIsEssImageAssociatedModule_fppf :
    ∀ (T : Scheme.{u}) (hT : B.Contains T), QuasicoherentIsEssImageAssociatedModule B T hT :=
  fun T hT => quasicoherentIsEssImageAssociatedModule' B T hT

/-- **Stacks 03DX (1) for `τ = fppf`: `𝓕 ↦ 𝓕^a` is an equivalence.**  The functor
`QCoh(𝒪_S) ⥤ QCoh((Sch/S)_fppf, 𝒪)` is fully faithful unconditionally
(`AlgebraicGeometry.BigFppfOver.fullyFaithfulAssociatedModuleQcohOnSite'`, Stacks 0GN7) and
essentially surjective by
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`. -/
@[stacks 03DX "clause (1) at τ = fppf: 𝓕 ↦ 𝓕^a is an equivalence \
QCoh(𝒪_S) ⥤ QCoh((Sch/S)_fppf, 𝒪)"]
public theorem isEquivalence_associatedModuleQcohOnSite_fppf :
    (associatedModuleQcohOnSite' B S hS).IsEquivalence :=
  isEquivalence_associatedModuleQcohOnSite' B S hS
    (quasicoherentIsEssImageAssociatedModule' B S hS)

/-- **The equivalence of categories of Stacks 03DX (1) for `τ = fppf`**,
`QCoh(𝒪_S) ≌ QCoh((Sch/S)_fppf, 𝒪)`, with `𝓕 ↦ 𝓕^a` as its functor. -/
@[stacks 03DX "clause (1) at τ = fppf: the equivalence of categories \
QCoh(𝒪_S) ≌ QCoh((Sch/S)_fppf, 𝒪)"]
public noncomputable def associatedModuleEquivalence_fppf :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).FullSubcategory :=
  associatedModuleEquivalence' B S hS (quasicoherentIsEssImageAssociatedModule' B S hS)

end AlgebraicGeometry.BigFppfOver

end
