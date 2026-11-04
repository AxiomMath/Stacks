module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

/-!
# Transporting a pushforward of presheaves of modules across an isomorphism of index functors

For a functor `K : C ⥤ D` and a morphism of presheaves of rings `φ : S ⟶ K.op ⋙ R`, the functor
`PresheafOfModules.pushforward φ` reindexes a presheaf of modules over `R : Dᵒᵖ ⥤ RingCat` along
`K` and restricts its scalars along `φ`.  Mathlib compares these pushforwards for the identity
index functor (`PresheafOfModules.pushforwardId`) and for a composite of index functors
(`PresheafOfModules.pushforwardComp`), but not for two index functors that are merely
*isomorphic*.  That comparison is what this file supplies.

Mathlib does have the corresponding comparison one level up, for sheaves of modules on sites:
`SheafOfModules.pushforwardNatTrans`, `SheafOfModules.pushforwardNatIso` and
`SheafOfModules.pushforwardCongr₂`, whose statement this file's declarations mirror.  Those are
unavailable for the pushforwards considered here, because they require the index functor to be a
continuous functor between two sites, while `PresheafOfModules.pushforward` asks only for a
functor between two categories; a pushforward along a functor out of a category carrying no
topology, such as a category of algebras, is not in their scope.

The comparison is *not* a statement about underlying presheaves alone: a pushforward carries a
module structure over the presheaf of rings `S`, and the scalars of the two pushforwards are
restricted along two different morphisms `φ : S ⟶ K.op ⋙ R` and `ψ : S ⟶ L.op ⋙ R`.  So the
hypothesis of every statement below is the compatibility of those two morphisms with the
comparison `β : K.op ⟶ L.op` of index functors, namely `φ ≫ Functor.whiskerRight β R = ψ`; it is
exactly what makes the restriction map `M.map (β.app X)` semilinear over `S`, and without it the
comparison does not exist as a morphism of presheaves of modules at all.

## Main definitions

* `Stacks.PresheafOfModules.pushforwardIndexMap` — the comparison
  `PresheafOfModules.pushforward φ ⟶ PresheafOfModules.pushforward ψ` induced by a natural
  transformation `β : K.op ⟶ L.op` of the opposites of the index functors, compatible with `φ`
  and `ψ`.  Its component at a presheaf of modules `M` and an object `X` is the restriction map
  `M.map (β.app X)`, as `pushforwardIndexMap_app_app_apply` records.
* `Stacks.PresheafOfModules.pushforwardIsoOfIndexIso` — for a natural isomorphism `α : K ≅ L` of
  index functors and `φ`, `ψ` compatible with it, the induced isomorphism
  `PresheafOfModules.pushforward φ ≅ PresheafOfModules.pushforward ψ`.
* `Stacks.PresheafOfModules.comp_whiskerRight_eqToIso_inv` — the compatibility hypothesis in the
  case that the two index functors are *equal* and the two scalar morphisms are the same map.

## Implementation notes

The comparison is stated for a natural transformation `β : K.op ⟶ L.op` between the *opposite*
functors rather than for a natural transformation `L ⟶ K`; the two are interchangeable, and the
opposite form is what both the construction and the applications use, since the restriction maps
of a presheaf of modules over `R : Dᵒᵖ ⥤ RingCat` are indexed by morphisms of `Dᵒᵖ`.

The semilinearity of the comparison is obtained from Mathlib rather than by hand: the hypothesis
`φ ≫ Functor.whiskerRight β R = ψ` says precisely that `(ψ.app X).hom` is the composite of
`(φ.app X).hom` with `(R.map (β.app X)).hom`, which is the hypothesis of
`ModuleCat.restrictScalarsComp'App`.  The comparison is therefore the image of the restriction
map `M.map (β.app X)` under `ModuleCat.restrictScalars (φ.app X).hom`, followed by that
isomorphism.

`Functor.whiskerRight β R` is an isomorphism when `β` is, which is why
`Stacks.PresheafOfModules.whiskerRight_hom_comp` can turn the compatibility hypothesis for
`(NatIso.op α).inv` into the one for `(NatIso.op α).hom`; this is what supplies the inverse of
`pushforwardIsoOfIndexIso`, and it is why the direction of the isomorphism `α` is immaterial.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w t v₁ u₁ v₂ u₂

namespace Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {R : Dᵒᵖ ⥤ RingCat.{t}} {S : Cᵒᵖ ⥤ RingCat.{t}}

section

variable {K L : C ⥤ D} {φ : S ⟶ K.op ⋙ R} {ψ : S ⟶ L.op ⋙ R}

/-- The compatibility `φ ≫ Functor.whiskerRight β R = ψ` of the two scalar morphisms with the
comparison `β` of index functors, read at an object as a factorisation of ring maps: the scalars
of the pushforward along `L` are those of the pushforward along `K` followed by the ring map that
`R` assigns to `β`. -/
theorem app_hom_eq_comp (β : K.op ⟶ L.op) (h : φ ≫ Functor.whiskerRight β R = ψ) (X : Cᵒᵖ) :
    (ψ.app X).hom = ((R.map (β.app X)).hom).comp (φ.app X).hom := by
  have h0 : φ.app X ≫ R.map (β.app X) = ψ.app X := NatTrans.congr_app h X
  rw [← h0]
  rfl

/-- The component at an object `X` of the comparison of the two pushforwards of `M`: the
restriction map `M.map (β.app X)`, made `S.obj X`-linear by `app_hom_eq_comp`. -/
def pushforwardIndexApp (β : K.op ⟶ L.op) (h : φ ≫ Functor.whiskerRight β R = ψ)
    (M : PresheafOfModules.{w} R) (X : Cᵒᵖ) :
    ((PresheafOfModules.pushforward.{w} φ).obj M).obj X ⟶
      ((PresheafOfModules.pushforward.{w} ψ).obj M).obj X :=
  (ModuleCat.restrictScalars (φ.app X).hom).map (M.map (β.app X)) ≫
    (ModuleCat.restrictScalarsComp'App (φ.app X).hom (R.map (β.app X)).hom (ψ.app X).hom
      (app_hom_eq_comp β h X) (M.obj (L.op.obj X))).inv

/-- The comparison of the two pushforwards of `M` is the restriction map of `M` along `β`. -/
@[simp] theorem pushforwardIndexApp_apply (β : K.op ⟶ L.op)
    (h : φ ≫ Functor.whiskerRight β R = ψ) (M : PresheafOfModules.{w} R) (X : Cᵒᵖ)
    (x : ((PresheafOfModules.pushforward.{w} φ).obj M).obj X) :
    pushforwardIndexApp β h M X x = M.map (β.app X) x := rfl

/-- The comparison of the two pushforwards of a fixed presheaf of modules `M`, as a morphism of
presheaves of modules over `S`. -/
def pushforwardIndexObjMap (β : K.op ⟶ L.op) (h : φ ≫ Functor.whiskerRight β R = ψ)
    (M : PresheafOfModules.{w} R) :
    (PresheafOfModules.pushforward.{w} φ).obj M ⟶
      (PresheafOfModules.pushforward.{w} ψ).obj M where
  app X := pushforwardIndexApp β h M X
  naturality {X Y} f := by
    have key : ∀ y : M.obj (K.op.obj X),
        M.map (β.app Y) (M.map (K.op.map f) y) = M.map (L.op.map f) (M.map (β.app X) y) := by
      intro y
      rw [← M.map_comp_apply, ← M.map_comp_apply, β.naturality f]
    refine ModuleCat.hom_ext (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x => ?_)
    exact key x

/-- The comparison of the pushforward along `K` with the pushforward along `L`, induced by a
natural transformation `β : K.op ⟶ L.op` compatible with the two scalar morphisms. -/
def pushforwardIndexMap (β : K.op ⟶ L.op) (h : φ ≫ Functor.whiskerRight β R = ψ) :
    PresheafOfModules.pushforward.{w} φ ⟶ PresheafOfModules.pushforward.{w} ψ where
  app M := pushforwardIndexObjMap β h M
  naturality {M N} g := by
    refine PresheafOfModules.hom_ext fun X => ?_
    refine ModuleCat.hom_ext (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x => ?_)
    exact (PresheafOfModules.naturality_apply g (β.app X) x).symm

/-- Every component of `pushforwardIndexMap` is a restriction map of the presheaf of modules
being pushed forward: no part of the module structure is discarded. -/
@[simp] theorem pushforwardIndexMap_app_app_apply (β : K.op ⟶ L.op)
    (h : φ ≫ Functor.whiskerRight β R = ψ) (M : PresheafOfModules.{w} R) (X : Cᵒᵖ)
    (x : ((PresheafOfModules.pushforward.{w} φ).obj M).obj X) :
    ((pushforwardIndexMap.{w} β h).app M).app X x = M.map (β.app X) x := rfl

end

section

variable {K L : C ⥤ D} (α : K ≅ L) {φ : S ⟶ K.op ⋙ R} {ψ : S ⟶ L.op ⋙ R}

/-- The compatibility hypothesis for an isomorphism of index functors holds in both directions:
if `ψ` is `φ` followed by the ring maps of `(NatIso.op α).inv`, then `φ` is `ψ` followed by the
ring maps of `(NatIso.op α).hom`. -/
theorem whiskerRight_hom_comp (h : φ ≫ Functor.whiskerRight (NatIso.op α).inv R = ψ) :
    ψ ≫ Functor.whiskerRight (NatIso.op α).hom R = φ := by
  rw [← h, Category.assoc, ← Functor.whiskerRight_comp, Iso.inv_hom_id,
    Functor.whiskerRight_id', Category.comp_id]

/-- The compatibility hypothesis for two *equal* index functors: if `K = L` and the two scalar
morphisms are the same map — which is what `HEq` says of them, their types being equal — then
they are compatible with the comparison of index functors that the equality induces.

This is the form the hypothesis takes whenever the two index functors agree on the nose, as
opposed to up to a chosen isomorphism; it is proved by substituting the equality, after which
the comparison is an identity. -/
theorem comp_whiskerRight_eqToIso_inv (e : K = L) (h : HEq φ ψ) :
    φ ≫ Functor.whiskerRight (NatIso.op (eqToIso e)).inv R = ψ := by
  subst e
  obtain rfl := eq_of_heq h
  simp

/-- **Transport of a pushforward of presheaves of modules across an isomorphism of index
functors.** For `α : K ≅ L` an isomorphism of index functors and `φ : S ⟶ K.op ⋙ R`,
`ψ : S ⟶ L.op ⋙ R` two morphisms of presheaves of rings compatible with it, the pushforward
along `K` with scalars `φ` and the pushforward along `L` with scalars `ψ` are isomorphic as
functors `PresheafOfModules R ⥤ PresheafOfModules S`.  Both components are restriction maps of
the presheaf of modules being pushed forward, and the isomorphism is compatible with the module
structures over `S` by construction. -/
def pushforwardIsoOfIndexIso (h : φ ≫ Functor.whiskerRight (NatIso.op α).inv R = ψ) :
    PresheafOfModules.pushforward.{w} φ ≅ PresheafOfModules.pushforward.{w} ψ where
  hom := pushforwardIndexMap.{w} (NatIso.op α).inv h
  inv := pushforwardIndexMap.{w} (NatIso.op α).hom (whiskerRight_hom_comp α h)
  hom_inv_id := by
    refine NatTrans.ext (funext fun M => PresheafOfModules.hom_ext fun X => ?_)
    refine ModuleCat.hom_ext (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x => ?_)
    have key : ∀ y : M.obj (K.op.obj X),
        M.map ((NatIso.op α).hom.app X) (M.map ((NatIso.op α).inv.app X) y) = y := by
      intro y
      rw [← M.map_comp_apply, (NatIso.op α).inv_hom_id_app, _root_.PresheafOfModules.map_id_apply]
    exact key x
  inv_hom_id := by
    refine NatTrans.ext (funext fun M => PresheafOfModules.hom_ext fun X => ?_)
    refine ModuleCat.hom_ext (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x => ?_)
    have key : ∀ y : M.obj (L.op.obj X),
        M.map ((NatIso.op α).inv.app X) (M.map ((NatIso.op α).hom.app X) y) = y := by
      intro y
      rw [← M.map_comp_apply, (NatIso.op α).hom_inv_id_app, _root_.PresheafOfModules.map_id_apply]
    exact key x

/-- The forward direction of `pushforwardIsoOfIndexIso` is the restriction map of the presheaf
of modules along `(NatIso.op α).inv`. -/
@[simp] theorem pushforwardIsoOfIndexIso_hom_app_app_apply
    (h : φ ≫ Functor.whiskerRight (NatIso.op α).inv R = ψ)
    (M : PresheafOfModules.{w} R) (X : Cᵒᵖ)
    (x : ((PresheafOfModules.pushforward.{w} φ).obj M).obj X) :
    (((pushforwardIsoOfIndexIso.{w} α h).hom.app M).app X) x =
      M.map ((NatIso.op α).inv.app X) x := rfl

/-- The backward direction of `pushforwardIsoOfIndexIso` is the restriction map of the presheaf
of modules along `(NatIso.op α).hom`. -/
@[simp] theorem pushforwardIsoOfIndexIso_inv_app_app_apply
    (h : φ ≫ Functor.whiskerRight (NatIso.op α).inv R = ψ)
    (M : PresheafOfModules.{w} R) (X : Cᵒᵖ)
    (x : ((PresheafOfModules.pushforward.{w} ψ).obj M).obj X) :
    (((pushforwardIsoOfIndexIso.{w} α h).inv.app M).app X) x =
      M.map ((NatIso.op α).hom.app X) x := rfl

end

end Stacks.PresheafOfModules

end
