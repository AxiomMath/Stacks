module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EffectiveGlueAgreement

/-!
# The functoriality comparison of restriction to an object, on sections

`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreement.lean` proves the
agreement of the local isomorphisms of Stacks 03DX (1) in the `objRestrict` spelling
(`AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso_effectiveGlueObjRestrictIso_eq`), and its
implementation notes identify the one step that blocks the transport of that agreement into the
`homRestr` spelling which
`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_agree` asks for: **the component
of `AlgebraicGeometry.BigFppfOver.objRestrictComp` on sections.**  This file proves it.

## Main definitions

* `Stacks.SectionsComponents.InducedAlong`: `Stacks.SectionsComponents.Induced` with the arrow of
  the site **pinned** rather than existentially quantified.  Pinning is what lets two induced
  morphisms be compared when the relevant hom-set of the site is not a subsingleton, which is the
  case here — so `Stacks.SectionsComponents.Induced.eq` does not apply.
* `Stacks.sliceBackArrow`, `Stacks.sliceForthArrow` and `Stacks.sliceMapArrow`: the canonical
  arrows of an iterated slice category coming from `CategoryTheory.Over.iteratedSliceEquiv` and
  `CategoryTheory.Over.iteratedSliceEquivOverMapIso`, each with the identity underneath.
* `AlgebraicGeometry.BigFppfOver.objRestrictCompArrow` and `…objRestrictCompArrowInv`: **the
  reassociation arrow of the big fppf site over `S` that `objRestrictComp` restricts along.**  For
  `g : Z ⟶ T` and `W` over the scheme of `Z`, reading `W` over `Z` and reading it over `T` through
  `g` gives two objects with the same underlying scheme, and `CategoryTheory.Over.w` of `g` makes
  the identity underneath into an arrow between them.

## Main results

* `AlgebraicGeometry.BigFppfOver.inducedAlong_objRestrictComp_app_hom` and
  `…inducedAlong_objRestrictComp_app_inv`: **the component of
  `AlgebraicGeometry.BigFppfOver.objRestrictComp` is restriction along the reassociation arrow**,
  in both directions.  This is the step the implementation notes of `EffectiveGlueAgreement.lean`
  record as blocked; it is unconditional.
* `AlgebraicGeometry.BigFppfOver.objRestrict_obj_val_obj_eq` and
  `…objRestrict_comp_obj_val_obj_eq`: the sections of one restriction and of two.  The second is
  the composite of two instances of the first and is *never* checked directly — see the
  implementation notes.
* `Stacks.SectionsComponents.iso_trans3_map_val_app`: the three factors of a restricted local
  isomorphism on sections, at abstract categories, with the composite-functor spelling of the
  outer two comparisons built in.
* `Stacks.SectionsComponents.overMapCompIso_inv_app_val_app` and
  `…overMapCongrIso_inv_app_val_app`: the sections of the two comparison isomorphisms of
  restriction along a single arrow, in the direction
  `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/RestrictCompCoherence.lean` does not
  record.
* `AlgebraicGeometry.BigFppfOver.objRestrictCompArrowInv_comp_sliceBackArrow_left` and
  `…objRestrictCompArrow_comp_sliceMapArrow_left`: the two pins — every arrow in sight has the
  identity underneath, so `CategoryTheory.Over.OverMorphism.ext` identifies the composites.

## Implementation notes

Nothing here carries a `stacks` attribute.

**Why the identifications are carried as `cast`s.**  The sections of a restriction to the big fppf
site of the scheme of an object are the sections of the module itself over the image object, and
one restriction deep this is `rfl` at no cost
(`AlgebraicGeometry.BigFppfOver.objRestrict_obj_val_obj_eq`, proved with the base of the site a
*variable*).  *Two* restrictions deep the same identification does **not** fit in the
heartbeat budget — `rfl` for

    `↥(((objRestrict B S hS T ⋙ objRestrict B (objScheme B S hS T) _
          (Over.mk g.left)).obj K).val.obj (op W))
      = ↥(K.val.obj (op ((Over.map T.hom).obj ((Over.map g.left).obj W))))`

times out, because the base of the inner restriction is `AlgebraicGeometry.BigFppfOver.objScheme`
of `T` and identifying the structure sheaf there with the restriction of the structure sheaf of
the whole site unfolds a semireducible definition.  So
`AlgebraicGeometry.BigFppfOver.objRestrict_comp_obj_val_obj_eq` composes two instances of the
one-step lemma by `Eq.trans` and the composite defeq is never checked, and every statement
below carries the identification as a `cast` — the design of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SectionsComponentsInduced.lean`.

For the same reason every category-theoretic step is an instance of a lemma proved at **abstract**
categories, matched by first-order unification alone: at the concrete structure sheaf of the big
fppf site no composition, no `CategoryTheory.Iso.trans` and no `CategoryTheory.Functor.mapIso` can
be recognized through its instance.  `Stacks.SectionsComponents.iso_trans3_map_val_app` carries
the identification of `(F' ⋙ F).obj X` with `F.obj (F'.obj X)` for exactly that reason.

**What consumes this.**  With the component of `objRestrictComp` in hand, the transport of the
agreement across the bridge is the chain: naturality of the preimage along
`Stacks.sliceBackArrow` and `Stacks.sliceMapArrow`,
`AlgebraicGeometry.BigFppfOver.objRestrictPreimageIso_hom_val_app`,
`AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso_eq` together with
`Stacks.SectionsComponents.iso_trans3_map_val_app`, the two components of `objRestrictComp`, and
the two pins.  That chain is carried out in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreementTransport.lean`,
which closes the clause.

Two things make it go through, and both have to be respected by anything added here.  Every
statement keeps its carrier identifications as explicit `cast`s and applies a morphism of modules
only to a term whose type is already that morphism's domain — a statement that lets the elaborator
discover the two-restriction identification on its own does not fit in the heartbeat budget.  And
the category `SheafOfModules (structureSheaf B (objScheme B S hS Z) _)` has a second spelling,
through `AlgebraicGeometry.BigFppfOver.objScheme` of `Over.mk g.left`, which
`AlgebraicGeometry.BigFppfOver.objRestrictComp` is stated in while
`AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso` is stated in the first; pinning one of the
two by name in an argument position is free, whereas letting the two spellings of the *category*
meet in an equation is not.

Nothing here is tagged: the tag is registered on the unconditional statement downstream.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃ w m

namespace Stacks.SectionsComponents

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  (M : SheafOfModules.{m} R)

section Def

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {S' : Sheaf J' RingCat.{w}}

/-- **The component of `f` at `U` is restriction along the given arrow `u` of the site of `M`.**
This is `Stacks.SectionsComponents.Induced` with the arrow *pinned*: the arrow is part of the
statement rather than existentially quantified, which is what lets two induced morphisms be
compared when the hom-set of the site is not a subsingleton. -/
public def InducedAlong {N₁ N₂ : SheafOfModules.{m} S'} (f : N₁ ⟶ N₂) (U : C'ᵒᵖ) {A A' : C}
    (u : A' ⟶ A) : Prop :=
  ∃ (e₁ : ↥(N₁.val.obj U) = ↥(M.val.obj (op A)))
    (e₂ : ↥(N₂.val.obj U) = ↥(M.val.obj (op A'))),
    ∀ y, cast e₂ (f.val.app U y) = M.val.map u.op (cast e₁ y)

variable {M}

/-- An induced morphism is induced in the existential sense. -/
public theorem InducedAlong.induced {N₁ N₂ : SheafOfModules.{m} S'} {f : N₁ ⟶ N₂} {U : C'ᵒᵖ}
    {A A' : C} {u : A' ⟶ A} (h : InducedAlong M f U u) : Induced M f U A A' :=
  ⟨u, h⟩

/-- **A morphism whose sections are a `cast` is induced by the identity arrow.** -/
public theorem InducedAlong.ofCast {N₁ N₂ : SheafOfModules.{m} S'} (f : N₁ ⟶ N₂) (U : C'ᵒᵖ)
    {A : C} (e : ↥(N₁.val.obj U) = ↥(N₂.val.obj U)) (hf : ∀ y, f.val.app U y = cast e y)
    (e₁ : ↥(N₁.val.obj U) = ↥(M.val.obj (op A))) : InducedAlong M f U (𝟙 A) := by
  refine ⟨e₁, e.symm.trans e₁, fun y => ?_⟩
  refine Eq.trans (congrArg (cast (e.symm.trans e₁)) (hf y)) ?_
  exact Eq.trans (cast_cast e (e.symm.trans e₁) y) (val_map_id M (cast e₁ y)).symm

/-- **A composite of induced morphisms is induced by the composite arrow.** -/
public theorem InducedAlong.comp {N₁ N₂ N₃ : SheafOfModules.{m} S'} {f : N₁ ⟶ N₂} {g : N₂ ⟶ N₃}
    {U : C'ᵒᵖ} {A₁ A₂ A₃ : C} {u : A₂ ⟶ A₁} {v : A₃ ⟶ A₂} (hf : InducedAlong M f U u)
    (hg : InducedAlong M g U v) : InducedAlong M (f ≫ g) U (v ≫ u) := by
  obtain ⟨e₁, e₂, hu⟩ := hf
  obtain ⟨e₂', e₃, hv⟩ := hg
  refine ⟨e₁, e₃, fun y => ?_⟩
  have h : e₂' = e₂ := rfl
  subst h
  exact Eq.trans (hv _) (Eq.trans (congrArg (fun z => M.val.map v.op z) (hu y))
    (val_map_map M v u (cast e₁ y)))

/-- **The arrow may be replaced by an equal arrow.** -/
public theorem InducedAlong.arrowCongr {N₁ N₂ : SheafOfModules.{m} S'} {f : N₁ ⟶ N₂} {U : C'ᵒᵖ}
    {A A' : C} {u u' : A' ⟶ A} (h : InducedAlong M f U u) (he : u = u') :
    InducedAlong M f U u' := he ▸ h

/-- **An equal morphism is induced along the same arrow.** -/
public theorem InducedAlong.ofEq {N₁ N₂ : SheafOfModules.{m} S'} {f f' : N₁ ⟶ N₂} {U : C'ᵒᵖ}
    {A A' : C} {u : A' ⟶ A} (he : f = f') (h : InducedAlong M f' U u) :
    InducedAlong M f U u := he ▸ h

/-- **Two morphisms induced along the same arrow agree on sections.**  This is the point of
pinning the arrow: no subsingleton hypothesis on the hom-sets of the site is needed. -/
public theorem InducedAlong.eq {N₁ N₂ : SheafOfModules.{m} S'} {f g : N₁ ⟶ N₂} {U : C'ᵒᵖ}
    {A A' : C} {u : A' ⟶ A} (hf : InducedAlong M f U u) (hg : InducedAlong M g U u) :
    ∀ y, f.val.app U y = g.val.app U y := by
  intro y
  obtain ⟨e₁, e₂, hu⟩ := hf
  obtain ⟨e₁', e₂', hu'⟩ := hg
  have key : cast e₂ (f.val.app U y) = cast e₂ (g.val.app U y) := (hu y).trans (hu' y).symm
  simpa only [cast_cast, cast_eq] using congrArg (cast e₂.symm) key

/-- **A composite of two isomorphisms of sheaves of modules, on sections.**  Stated at abstract
sites: at the concrete structure sheaf of the big fppf site no composition can be recognized
through its instance. -/
public theorem iso_trans_hom_val_app {N₁ N₂ N₃ : SheafOfModules.{m} S'} (α : N₁ ≅ N₂)
    (β : N₂ ≅ N₃) (U : C'ᵒᵖ) (y) :
    (α ≪≫ β).hom.val.app U y = β.hom.val.app U (α.hom.val.app U y) := rfl

end Def

section EqToIso

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {S' : Sheaf J' RingCat.{w}} {𝒞 : Type u₃} [Category.{v₃} 𝒞]

/-- **The transport along an equality of functors into sheaves of modules is a `cast` on
sections.**  Proved by `cases` on the equality, which is what makes it cheap: both functors are
variables, so nothing at a concrete structure sheaf has to be unfolded. -/
public theorem eqToIso_app_hom_val_app {P Q : 𝒞 ⥤ SheafOfModules.{m} S'} (h : P = Q) (K : 𝒞)
    (U : C'ᵒᵖ) (e : ↥((P.obj K).val.obj U) = ↥((Q.obj K).val.obj U)) (y) :
    ((Iso.app (eqToIso h) K).hom).val.app U y = cast e y := by
  cases h
  exact (cast_eq e y).symm

/-- **The inverse transport along an equality of functors is a `cast` on sections.** -/
public theorem eqToIso_app_inv_val_app {P Q : 𝒞 ⥤ SheafOfModules.{m} S'} (h : P = Q) (K : 𝒞)
    (U : C'ᵒᵖ) (e : ↥((Q.obj K).val.obj U) = ↥((P.obj K).val.obj U)) (y) :
    ((Iso.app (eqToIso h) K).inv).val.app U y = cast e y := by
  cases h
  exact (cast_eq e y).symm

variable {M}

/-- **The transport along an equality of functors is induced by the identity arrow.** -/
public theorem InducedAlong.eqToIsoHom {P Q : 𝒞 ⥤ SheafOfModules.{m} S'} (h : P = Q) (K : 𝒞)
    (U : C'ᵒᵖ) {A : C} (e₁ : ↥((P.obj K).val.obj U) = ↥(M.val.obj (op A))) :
    InducedAlong M ((Iso.app (eqToIso h) K).hom) U (𝟙 A) :=
  InducedAlong.ofCast _ U
    (congrArg (fun P' : 𝒞 ⥤ SheafOfModules.{m} S' => ↥((P'.obj K).val.obj U)) h)
    (fun y => eqToIso_app_hom_val_app h K U _ y) e₁

/-- **The inverse transport along an equality of functors is induced by the identity arrow.** -/
public theorem InducedAlong.eqToIsoInv {P Q : 𝒞 ⥤ SheafOfModules.{m} S'} (h : P = Q) (K : 𝒞)
    (U : C'ᵒᵖ) {A : C} (e₁ : ↥((Q.obj K).val.obj U) = ↥(M.val.obj (op A))) :
    InducedAlong M ((Iso.app (eqToIso h) K).inv) U (𝟙 A) :=
  InducedAlong.ofCast _ U
    (congrArg (fun P' : 𝒞 ⥤ SheafOfModules.{m} S' => ↥((P'.obj K).val.obj U)) h.symm)
    (fun y => eqToIso_app_inv_val_app h K U _ y) e₁

/-- **A composite of two natural isomorphisms is induced by the composite arrow.**  Stated with
`CategoryTheory.Iso.app` of `CategoryTheory.Iso.trans` so that a consumer matches it against a
goal by first-order unification alone: at the concrete sites of this development no composition
in a category of sheaves of modules can be recognized through its instance. -/
public theorem InducedAlong.isoTransHom {F G H : 𝒞 ⥤ SheafOfModules.{m} S'} (α : F ≅ G)
    (β : G ≅ H) (K : 𝒞) {U : C'ᵒᵖ} {A₁ A₂ A₃ : C} {u : A₂ ⟶ A₁} {v : A₃ ⟶ A₂}
    (h₁ : InducedAlong M ((Iso.app α K).hom) U u)
    (h₂ : InducedAlong M ((Iso.app β K).hom) U v) :
    InducedAlong M ((Iso.app (α ≪≫ β) K).hom) U (v ≫ u) := h₁.comp h₂

/-- **The inverse of a composite of two natural isomorphisms.** -/
public theorem InducedAlong.isoTransInv {F G H : 𝒞 ⥤ SheafOfModules.{m} S'} (α : F ≅ G)
    (β : G ≅ H) (K : 𝒞) {U : C'ᵒᵖ} {A₁ A₂ A₃ : C} {u : A₂ ⟶ A₁} {v : A₃ ⟶ A₂}
    (h₁ : InducedAlong M ((Iso.app β K).inv) U u)
    (h₂ : InducedAlong M ((Iso.app α K).inv) U v) :
    InducedAlong M ((Iso.app (α ≪≫ β) K).inv) U (v ≫ u) := h₁.comp h₂

/-- **The three factors of a restricted local isomorphism, on sections.**  The composite
`α.symm ≪≫ F.mapIso θ ≪≫ γ` of two comparison isomorphisms around the image of `θ` is, on
sections, the three components applied in turn.

The source and target of the two comparisons are written with the *composite* functor `F' ⋙ F`,
which is the spelling `AlgebraicGeometry.BigFppfOver.objRestrictComp` uses, while the middle
factor is written with `F` applied to the image of `F'`: identifying the two happens *here*, at
abstract categories, where it costs nothing.  A consumer at the concrete structure sheaf of the
big fppf site matches this by first-order unification alone — which is the only thing that works
there, the same identification at the concrete sheaf not fitting in the heartbeat budget. -/
public theorem iso_trans3_map_val_app {D : Type u₃} [Category.{v₃} D] {D' : Type u₃}
    [Category.{v₃} D'] (F' : D' ⥤ D) (F : D ⥤ SheafOfModules.{m} S') {Xo Yo : D'}
    (θ : F'.obj Xo ≅ F'.obj Yo) {N₁ N₄ : SheafOfModules.{m} S'}
    (α : (F' ⋙ F).obj Xo ≅ N₁) (γ : (F' ⋙ F).obj Yo ≅ N₄) (U : C'ᵒᵖ) (y) :
    (α.symm ≪≫ F.mapIso θ ≪≫ γ).hom.val.app U y =
      γ.hom.val.app U ((F.map θ.hom).val.app U (α.inv.val.app U y)) := rfl

/-- **The same, read off an equation.**  The two comparisons are implicit, so a consumer supplies
only the equation exhibiting the isomorphism as the composite and the two are read off it by
first-order matching — no composite is elaborated afresh, which is what keeps the two spellings of
the middle object from meeting at a concrete structure sheaf. -/
public theorem iso_trans3_map_val_app_of_eq {D : Type u₃} [Category.{v₃} D] {D' : Type u₃}
    [Category.{v₃} D'] (F' : D' ⥤ D) (F : D ⥤ SheafOfModules.{m} S') {Xo Yo : D'}
    (θ : F'.obj Xo ≅ F'.obj Yo) {N₁ N₄ : SheafOfModules.{m} S'}
    {α : (F' ⋙ F).obj Xo ≅ N₁} {γ : (F' ⋙ F).obj Yo ≅ N₄} {Ψ : N₁ ≅ N₄}
    (hΨ : Ψ = α.symm ≪≫ F.mapIso θ ≪≫ γ) (U : C'ᵒᵖ) (y) :
    Ψ.hom.val.app U y =
      γ.hom.val.app U ((F.map θ.hom).val.app U (α.inv.val.app U y)) := by
  subst hΨ
  rfl

end EqToIso

/-! ### The four comparison factors of restriction along an arrow of the site -/

section OverMap

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  {U V W : C}

/-- **The sections of a restriction along an arrow of the site**: a section over `A` is a section
of the module over the image of `A`.  Stated at an abstract site, where it is `rfl` at no
cost. -/
public theorem overMap_obj_val_obj_eq (f : V ⟶ U) (M : SheafOfModules.{w} (R.over U))
    (A : Over V) :
    ↥(((SheafOfModules.overMap.{w} R f).obj M).val.obj (op A)) =
      ↥(M.val.obj (op ((Over.map f).obj A))) := rfl

/-- **The sections of an iterated restriction**, by composing two instances of
`Stacks.SectionsComponents.overMap_obj_val_obj_eq`. -/
public theorem overMap_comp_obj_val_obj_eq (f : V ⟶ U) (g : W ⟶ V)
    (M : SheafOfModules.{w} (R.over U)) (A : Over W) :
    ↥(((SheafOfModules.overMap.{w} R f ⋙ SheafOfModules.overMap.{w} R g).obj M).val.obj (op A)) =
      ↥(M.val.obj (op ((Over.map f).obj ((Over.map g).obj A)))) :=
  (overMap_obj_val_obj_eq R g ((SheafOfModules.overMap.{w} R f).obj M) A).trans
    (overMap_obj_val_obj_eq R f M ((Over.map g).obj A))

/-- **The sections of the inverse composition comparison of restriction**: the module's action on
the inverse of the arrow `CategoryTheory.Over.mapComp` of the slice category, whose underlying
map is the identity.  This is the direction
`Stacks.SheafOfModules.overMapCompIso_hom_app_val_app` does not record. -/
@[simp] public theorem overMapCompIso_inv_app_val_app (f : V ⟶ U) (g : W ⟶ V)
    (M : SheafOfModules.{w} (R.over U)) (A : (Over W)ᵒᵖ) (x) :
    (ModuleCat.Hom.hom (((Stacks.SheafOfModules.overMapCompIso R f g).inv.app M).val.app A)) x =
      (ModuleCat.Hom.hom (M.val.map ((Over.mapComp g f).inv.app A.unop).op)) x := rfl

/-- **The sections of the inverse congruence isomorphism of restriction.** -/
@[simp] public theorem overMapCongrIso_inv_app_val_app {a b : W ⟶ U} (e : a = b)
    (M : SheafOfModules.{w} (R.over U)) (A : (Over W)ᵒᵖ) (x) :
    (ModuleCat.Hom.hom (((Stacks.SheafOfModules.overMapCongrIso R e).inv.app M).val.app A)) x =
      (ModuleCat.Hom.hom (M.val.map ((Over.mapCongr b a e.symm).inv.app A.unop).op)) x := rfl

/-- **The composition comparison of restriction is induced by `CategoryTheory.Over.mapComp`.** -/
public theorem InducedAlong.overMapCompHom (f : V ⟶ U) (g : W ⟶ V)
    (M : SheafOfModules.{w} (R.over U)) (A : Over W) :
    InducedAlong M ((Iso.app (Stacks.SheafOfModules.overMapCompIso R f g) M).hom) (op A)
      ((Over.mapComp g f).hom.app A) :=
  ⟨rfl, rfl, fun y =>
    Stacks.SheafOfModules.overMapCompIso_hom_app_val_app R f g M (op A) y⟩

/-- **The inverse composition comparison is induced by the inverse of
`CategoryTheory.Over.mapComp`.** -/
public theorem InducedAlong.overMapCompInv (f : V ⟶ U) (g : W ⟶ V)
    (M : SheafOfModules.{w} (R.over U)) (A : Over W) :
    InducedAlong M ((Iso.app (Stacks.SheafOfModules.overMapCompIso R f g) M).inv) (op A)
      ((Over.mapComp g f).inv.app A) :=
  ⟨rfl, rfl, fun y => overMapCompIso_inv_app_val_app R f g M (op A) y⟩

/-- **The congruence isomorphism of restriction is induced by
`CategoryTheory.Over.mapCongr`.** -/
public theorem InducedAlong.overMapCongrHom {a b : W ⟶ U} (e : a = b)
    (M : SheafOfModules.{w} (R.over U)) (A : Over W) :
    InducedAlong M ((Iso.app (Stacks.SheafOfModules.overMapCongrIso R e) M).hom) (op A)
      ((Over.mapCongr b a e.symm).hom.app A) :=
  ⟨rfl, rfl, fun y =>
    Stacks.SheafOfModules.overMapCongrIso_hom_app_val_app R e M (op A) y⟩

/-- **The inverse congruence isomorphism is induced by the inverse of
`CategoryTheory.Over.mapCongr`.** -/
public theorem InducedAlong.overMapCongrInv {a b : W ⟶ U} (e : a = b)
    (M : SheafOfModules.{w} (R.over U)) (A : Over W) :
    InducedAlong M ((Iso.app (Stacks.SheafOfModules.overMapCongrIso R e) M).inv) (op A)
      ((Over.mapCongr b a e.symm).inv.app A) :=
  ⟨rfl, rfl, fun y => overMapCongrIso_inv_app_val_app R e M (op A) y⟩

end OverMap

end Stacks.SectionsComponents

namespace Stacks

/-! ### The canonical arrows of an iterated slice that have the identity underneath -/

section Slice

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : 𝒞}

/-- **The canonical arrow of the slice at `Z` out of the round trip through the slice at the
underlying object of `Z`.**  It is the inverse unit of `CategoryTheory.Over.iteratedSliceEquiv`;
what matters about it is that the arrow underneath the arrow underneath is the identity. -/
public noncomputable def sliceBackArrow (Z : Over X) (W : Over Z) :
    (Over.iteratedSliceBackward Z).obj ((Over.iteratedSliceForward Z).obj W) ⟶ W :=
  ((Over.iteratedSliceEquiv Z).unitIso.app W).inv

/-- **The canonical arrow into the round trip**, inverse to
`Stacks.sliceBackArrow`. -/
public noncomputable def sliceForthArrow (Z : Over X) (W : Over Z) :
    W ⟶ (Over.iteratedSliceBackward Z).obj ((Over.iteratedSliceForward Z).obj W) :=
  ((Over.iteratedSliceEquiv Z).unitIso.app W).hom

/-- **The canonical arrow comparing `CategoryTheory.Over.map` of an arrow of the base slice with
`CategoryTheory.Over.map` of the arrow underneath it**, through the two iterated slices.  It is
the component of `CategoryTheory.Over.iteratedSliceEquivOverMapIso`. -/
public noncomputable def sliceMapArrow {Z T : Over X} (g : Z ⟶ T) (W : Over Z) :
    (Over.iteratedSliceBackward T).obj ((Over.map g.left).obj
        ((Over.iteratedSliceForward Z).obj W)) ⟶ (Over.map g).obj W :=
  (Over.iteratedSliceEquivOverMapIso g).hom.app W

/-- The arrow of `X` underneath `Stacks.sliceBackArrow` is the identity. -/
@[simp] public theorem sliceBackArrow_left_left (Z : Over X) (W : Over Z) :
    (sliceBackArrow Z W).left.left = 𝟙 _ := rfl

/-- The arrow of `X` underneath `Stacks.sliceForthArrow` is the identity. -/
@[simp] public theorem sliceForthArrow_left_left (Z : Over X) (W : Over Z) :
    (sliceForthArrow Z W).left.left = 𝟙 _ := rfl

/-- The arrow of `X` underneath `Stacks.sliceMapArrow` is the identity. -/
@[simp] public theorem sliceMapArrow_left_left {Z T : Over X} (g : Z ⟶ T) (W : Over Z) :
    (sliceMapArrow g W).left.left = 𝟙 _ := rfl

/-- **The two canonical arrows of the round trip compose to the identity, underneath.** -/
public theorem sliceForthArrow_left_comp_sliceBackArrow_left (Z : Over X) (W : Over Z) :
    (sliceForthArrow Z W).left ≫ (sliceBackArrow Z W).left = 𝟙 W.left :=
  congrArg (fun k : W ⟶ W => k.left) ((Over.iteratedSliceEquiv Z).unitIso.app W).hom_inv_id

/-- **The other composite is the identity, underneath.** -/
public theorem sliceBackArrow_left_comp_sliceForthArrow_left (Z : Over X) (W : Over Z) :
    (sliceBackArrow Z W).left ≫ (sliceForthArrow Z W).left = 𝟙 _ :=
  congrArg (fun k : (Over.iteratedSliceBackward Z).obj ((Over.iteratedSliceForward Z).obj W) ⟶
      (Over.iteratedSliceBackward Z).obj ((Over.iteratedSliceForward Z).obj W) => k.left)
    ((Over.iteratedSliceEquiv Z).unitIso.app W).inv_hom_id

end Slice

end Stacks

namespace AlgebraicGeometry.BigFppfOver

open Stacks.SectionsComponents

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The sections of one restriction, and of two -/

/-- **The sections of the restriction of a module to the big fppf site of the scheme of `T`.**  A
section over `V` is a section of the module itself over the image of `V` in the big fppf site
over the base.

The base of the site is a *variable* here, and that is the whole point: the same identification
one restriction deeper does not fit in the heartbeat budget, and the only way to it is to compose
two instances of this lemma — see
`AlgebraicGeometry.BigFppfOver.objRestrict_comp_obj_val_obj_eq`. -/
public theorem objRestrict_obj_val_obj_eq (X : Scheme.{u}) (hX : B.Contains X)
    (T : BigFppfOver B X hX) (K : SheafOfModules.{u} (structureSheaf B X hX))
    (V : BigFppfOver B (objScheme B X hX T) (contains_objScheme B X hX T)) :
    ↥(((objRestrict B X hX T).obj K).val.obj (op V)) =
      ↥(K.val.obj (op ((Over.map T.hom).obj V))) := rfl

/-- **The sections of the iterated restriction**, by composing two instances of
`AlgebraicGeometry.BigFppfOver.objRestrict_obj_val_obj_eq`.  Proving this by `rfl`
directly exhausts the heartbeat budget, because the base of the inner restriction is
`AlgebraicGeometry.BigFppfOver.objScheme` of `T` and identifying the structure sheaf there with
the restriction of the structure sheaf of the whole site unfolds a semireducible definition.  The
same identification one restriction deep is `rfl` at no cost, so the composite is reached by
`Eq.trans` and never by a direct defeq check. -/
public theorem objRestrict_comp_obj_val_obj_eq {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    (K : SheafOfModules.{u} (structureSheaf B S hS))
    (W : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z)) :
    ↥(((objRestrict B S hS T ⋙ objRestrict B (objScheme B S hS T)
          (contains_objScheme B S hS T) (Over.mk g.left)).obj K).val.obj (op W)) =
      ↥(K.val.obj (op ((Over.map T.hom).obj ((Over.map g.left).obj W)))) :=
  (objRestrict_obj_val_obj_eq B (objScheme B S hS T) (contains_objScheme B S hS T)
      (Over.mk g.left) ((objRestrict B S hS T).obj K) W).trans
    (objRestrict_obj_val_obj_eq B S hS T K ((Over.map g.left).obj W))

/-! ### The arrow of the site that the functoriality comparison restricts along -/

/-- **The reassociation arrow of the big fppf site over `S` that
`AlgebraicGeometry.BigFppfOver.objRestrictComp` restricts along.**  For `g : Z ⟶ T` and `W` an
object of the big fppf site of the scheme of `Z`, the two objects of the big fppf site over `S`
obtained by reading `W` over `Z` and by reading it over `T` through `g` have the same underlying
scheme, and the arrow between them has the identity underneath; `CategoryTheory.Over.w` of `g`
is what makes it an arrow at all. -/
public def objRestrictCompArrow {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    (W : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z)) :
    ((Over.map Z.hom).obj W : BigFppfOver B S hS) ⟶
      (Over.map T.hom).obj ((Over.map g.left).obj W) :=
  Over.homMk (𝟙 _) (by
    dsimp only [Over.map_obj_left, Over.map_obj_hom, Functor.const_obj_obj, Over.mk_hom]
    rw [Category.id_comp, Category.assoc, Over.w g])

/-- The same arrow in the other direction. -/
public def objRestrictCompArrowInv {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    (W : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z)) :
    ((Over.map T.hom).obj ((Over.map g.left).obj W) : BigFppfOver B S hS) ⟶
      (Over.map Z.hom).obj W :=
  Over.homMk (𝟙 _) (by
    dsimp only [Over.map_obj_left, Over.map_obj_hom, Functor.const_obj_obj, Over.mk_hom]
    rw [Category.id_comp, Category.assoc, Over.w g])

/-- The morphism of schemes underneath `AlgebraicGeometry.BigFppfOver.objRestrictCompArrow` is
the identity. -/
@[simp] public theorem objRestrictCompArrow_left {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    (W : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z)) :
    (objRestrictCompArrow B S hS g W).left = 𝟙 _ := rfl

/-- The morphism of schemes underneath `AlgebraicGeometry.BigFppfOver.objRestrictCompArrowInv`
is the identity. -/
@[simp] public theorem objRestrictCompArrowInv_left {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    (W : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z)) :
    (objRestrictCompArrowInv B S hS g W).left = 𝟙 _ := rfl

/-! ### The functoriality comparison, on sections -/

/-- **The component of `AlgebraicGeometry.BigFppfOver.objRestrictComp` is restriction along the
reassociation arrow of the site.**  This is the characterisation
`AlgebraicGeometry.BigFppfOver.objRestrictComp_eq` makes possible, read on sections: the two
transports between the two spellings of restriction are `cast`s, and the two comparison
isomorphisms of restriction along a single arrow are the module's action on
`CategoryTheory.Over.mapComp` and `CategoryTheory.Over.mapCongr`, all three of which have the
identity underneath.  The composite arrow is therefore the one of
`AlgebraicGeometry.BigFppfOver.objRestrictCompArrow`, and the identification of the two is
`CategoryTheory.Over.OverMorphism.ext`. -/
public theorem inducedAlong_objRestrictComp_app_hom {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    (K : SheafOfModules.{u} (structureSheaf B S hS))
    (W : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z)) :
    InducedAlong K ((Iso.app (objRestrictComp B S hS g) K).hom) (op W)
      (objRestrictCompArrow B S hS g W) := by
  rw [objRestrictComp_eq]
  refine InducedAlong.arrowCongr
    (InducedAlong.isoTransHom _ _ K
      (InducedAlong.eqToIsoHom (objRestrict_comp_eq_overMap_comp B S hS g) K (op W)
        (objRestrict_comp_obj_val_obj_eq B S hS g K W))
      (InducedAlong.isoTransHom _ _ K
        (InducedAlong.isoTransHom _ _ K
          (InducedAlong.overMapCompHom B.structureSheaf T.hom g.left K W)
          (InducedAlong.overMapCongrHom B.structureSheaf (Over.w g) K W))
        (InducedAlong.eqToIsoHom (objRestrict_eq_overMap B S hS Z).symm K (op W)
          (overMap_obj_val_obj_eq B.structureSheaf Z.hom K W)))) ?_
  refine Over.OverMorphism.ext ?_
  simp

/-- **The same for the inverse component.** -/
public theorem inducedAlong_objRestrictComp_app_inv {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    (K : SheafOfModules.{u} (structureSheaf B S hS))
    (W : BigFppfOver B (objScheme B S hS Z) (contains_objScheme B S hS Z)) :
    InducedAlong K ((Iso.app (objRestrictComp B S hS g) K).inv) (op W)
      (objRestrictCompArrowInv B S hS g W) := by
  rw [objRestrictComp_eq]
  refine InducedAlong.arrowCongr
    (InducedAlong.isoTransInv _ _ K
      (InducedAlong.isoTransInv _ _ K
        (InducedAlong.eqToIsoInv (objRestrict_eq_overMap B S hS Z).symm K (op W)
          (objRestrict_obj_val_obj_eq B S hS Z K W))
        (InducedAlong.isoTransInv _ _ K
          (InducedAlong.overMapCongrInv B.structureSheaf (Over.w g) K W)
          (InducedAlong.overMapCompInv B.structureSheaf T.hom g.left K W)))
      (InducedAlong.eqToIsoInv (objRestrict_comp_eq_overMap_comp B S hS g) K (op W)
        (overMap_comp_obj_val_obj_eq B.structureSheaf T.hom g.left K W))) ?_
  refine Over.OverMorphism.ext ?_
  simp

/-! ### The pins: every arrow in sight has the identity underneath -/

/-- **The reassociation arrow absorbs the canonical arrow of the round trip.**  Both sides are
arrows of the big fppf site over `S` with the identity underneath, between the same two objects,
so `CategoryTheory.Over.OverMorphism.ext` identifies them. -/
public theorem objRestrictCompArrowInv_comp_sliceBackArrow_left {T Z : BigFppfOver B S hS}
    (g : Z ⟶ T) (W : Over Z) :
    objRestrictCompArrowInv B S hS g ((Over.iteratedSliceForward Z).obj W) ≫
        (Stacks.sliceBackArrow Z W).left = (Stacks.sliceMapArrow g W).left :=
  Over.OverMorphism.ext (Category.comp_id _)

/-- **The same with the reassociation arrow in the other direction.** -/
public theorem objRestrictCompArrow_comp_sliceMapArrow_left {T Z : BigFppfOver B S hS}
    (g : Z ⟶ T) (W : Over Z) :
    objRestrictCompArrow B S hS g ((Over.iteratedSliceForward Z).obj W) ≫
        (Stacks.sliceMapArrow g W).left = (Stacks.sliceBackArrow Z W).left :=
  Over.OverMorphism.ext (Category.comp_id _)

/-! ### Three further sections computations -/

/-- **The transport along the sections identification of one restriction is the identity.**  The
base of the site is a variable, which is what makes this `rfl` cheap. -/
public theorem cast_objRestrict_obj_val_obj (X : Scheme.{u}) (hX : B.Contains X)
    (T : BigFppfOver B X hX) (K : SheafOfModules.{u} (structureSheaf B X hX))
    (V : BigFppfOver B (objScheme B X hX T) (contains_objScheme B X hX T))
    (y : ((objRestrict B X hX T).obj K).val.obj (op V)) :
    cast (objRestrict_obj_val_obj_eq B X hX T K V) y = y := rfl

/-- **Restriction to the localization at `T` acts on an arrow of the slice through the arrow
underneath it.**  The base of the site is a variable. -/
public theorem over_val_map (X : Scheme.{u}) (hX : B.Contains X) (T : BigFppfOver B X hX)
    (K : SheafOfModules.{u} (structureSheaf B X hX)) {A A' : Over T} (u : A ⟶ A') (y) :
    (K.over T).val.map u.op y = K.val.map u.left.op y := rfl

/-! ### The restriction of a local isomorphism, on sections -/

/-- **`AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso` read back as the composite it is
defined to be.**  The definition is a composite of three isomorphisms; this is that composite,
and it is `rfl`. -/
public theorem restrictObjRestrictIso_eq {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N) :
    restrictObjRestrictIso B S hS g θ =
      ((objRestrictComp B S hS g).app M).symm ≪≫
        (objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T)
          (Over.mk g.left)).mapIso θ ≪≫ (objRestrictComp B S hS g).app N := rfl

/-- **Restriction to the big fppf site of the scheme of `T` acts on a morphism by reindexing its
components.**  The base of the site is a variable, which is what makes this `rfl` cheap. -/
public theorem objRestrict_map_val_app (X : Scheme.{u}) (hX : B.Contains X)
    (T : BigFppfOver B X hX) {K L : SheafOfModules.{u} (structureSheaf B X hX)} (φ : K ⟶ L)
    (V : BigFppfOver B (objScheme B X hX T) (contains_objScheme B X hX T))
    (y : ((objRestrict B X hX T).obj K).val.obj (op V)) :
    ((objRestrict B X hX T).map φ).val.app (op V) y =
      φ.val.app (op ((Over.map T.hom).obj V)) y := rfl

/-- **The bridge of Stacks 03DX (1), on sections.**  The component of
`AlgebraicGeometry.BigFppfOver.objRestrictPreimageIso` at the image of `V` under the reindexing
of Stacks 06WI is the component of the local isomorphism at `V`.  This is
`AlgebraicGeometry.BigFppfOver.objRestrictFunctor_map_objRestrictPreimageIso` read through
`Stacks.SectionsComponents.pushforward_map_val_app`. -/
public theorem objRestrictPreimageIso_hom_val_app {T : BigFppfOver B S hS}
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (V : BigFppfOver B (objScheme B S hS T) (contains_objScheme B S hS T))
    (y : ((objRestrict B S hS T).obj M).val.obj (op V)) :
    (objRestrictPreimageIso B S hS θ).hom.val.app
        (op ((Over.iteratedSliceBackward T).obj V)) y = θ.hom.val.app (op V) y :=
  congrArg (fun k => k.val.app (op V) y)
    (objRestrictFunctor_map_objRestrictPreimageIso B S hS θ)

end AlgebraicGeometry.BigFppfOver

end
