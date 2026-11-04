module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-!
# The mate of the contraction of an iterated pullback of sheaves of modules

Let `F : C ⥤ D` and `G : D ⥤ D'` be continuous functors between sites, let
`φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R` and
`ψ : R ⟶ (G.sheafPushforwardContinuous RingCat K K').obj R'` be morphisms of sheaves of rings,
and suppose both pushforward functors on sheaves of modules admit left adjoints.  Mathlib's
`SheafOfModules.pullbackComp` contracts the iterated pullback,

    `pullback φ ⋙ pullback ψ ≅ pullback (φ ≫ map ψ)`,

and `SheafOfModules.pushforwardComp` contracts the iterated pushforward in the other order.
`CategoryTheory.conjugateIsoEquiv` is the bijection between isomorphisms of left adjoints and
isomorphisms of the corresponding right adjoints; this file records that the two contractions
correspond to one another under it.

Mathlib's `SheafOfModules.conjugateEquiv_pullbackComp_inv` is this statement about the
*underlying natural transformations*, i.e. about the `hom` field alone.  An identity between
isomorphisms is what a coherence computation needs, because a comparison isomorphism assembled
from several factors has its mate computed factor by factor — by `conjugateIsoEquiv` applied to
each factor — and the factors are isomorphisms, not natural transformations.

## Main results

* `Stacks.SheafOfModules.conjugateIsoEquiv_pullbackComp`: **the mate of the contraction of an
  iterated pullback of sheaves of modules is the inverse of the contraction of the iterated
  pushforward.**  The orientation is reversed because conjugation is contravariant.
* `Stacks.SheafOfModules.conjugateIsoEquiv_pullbackComp_symm`: the same identity read on the
  other orientation, the mate of `(SheafOfModules.pullbackComp φ ψ).symm` being
  `SheafOfModules.pushforwardComp φ ψ` itself.

## Implementation notes

This file is general sheaf-of-modules infrastructure at an arbitrary site: no scheme, and no
ringed space, appears anywhere in it.  In particular it is *not* the scheme-level statement
`Stacks.Scheme.Modules.conjugateIsoEquiv_pullbackComp`, which is about
`AlgebraicGeometry.Scheme.Modules.pullbackComp`; the two concern different constructions and
neither implies the other.

The proof does not go through Mathlib's component-level lemma at all, and this is what makes it
cheap.  `SheafOfModules.pullbackComp φ ψ` is *defined* as
`CategoryTheory.Adjunction.leftAdjointCompIso` of `SheafOfModules.pushforwardComp φ ψ`, and
`leftAdjointCompIso` is in turn defined as `(conjugateIsoEquiv _ _).symm` applied to the inverse
isomorphism.  So the first result below is an instance of `Equiv.apply_symm_apply`: it needs only
that `conjugateIsoEquiv` is an equivalence, with both sides matching by unfolding two
definitions.  Deriving it instead from `SheafOfModules.conjugateEquiv_pullbackComp_inv` by
`CategoryTheory.Iso.ext` and then re-orienting with a rewrite forces the elaborator to compare
two composite conjugations up to definitional unfolding, and that comparison does not terminate
within the default heartbeat budget; the whole file as written elaborates in about one second.
-/

@[expose] public section

open CategoryTheory

universe v u v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {K' : GrothendieckTopology D'}
  {F : C ⥤ D} {G : D ⥤ D'}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} {R' : Sheaf K' RingCat.{u}}
  [Functor.IsContinuous F J K] [Functor.IsContinuous G K K']
  [Functor.IsContinuous (F ⋙ G) J K']

/-- **The mate of the contraction of an iterated pullback of sheaves of modules is the inverse of
the contraction of the iterated pushforward.**  With respect to the pullback–pushforward
adjunction of the composite morphism of sheaves of rings on the one side and the composite of the
two pullback–pushforward adjunctions on the other, `SheafOfModules.pullbackComp φ ψ` has as mate
`(SheafOfModules.pushforwardComp φ ψ).symm`; the orientation is reversed because conjugation is
contravariant.

This holds with no hypothesis beyond the existence of the two pullbacks, because
`SheafOfModules.pullbackComp` is *defined* as the inverse conjugate of
`SheafOfModules.pushforwardComp`: the statement is `Equiv.apply_symm_apply` for the bijection
`CategoryTheory.conjugateIsoEquiv`. -/
public theorem conjugateIsoEquiv_pullbackComp
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj R')
    [(_root_.SheafOfModules.pushforward.{v} φ).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} ψ).IsRightAdjoint] :
    conjugateIsoEquiv
        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} (F := F ⋙ G)
          (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ))
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} φ).comp
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} ψ))
        (_root_.SheafOfModules.pullbackComp.{v} φ ψ) =
      (_root_.SheafOfModules.pushforwardComp.{v} φ ψ).symm :=
  (conjugateIsoEquiv _ _).apply_symm_apply _

/-- **The mate of the inverse contraction of an iterated pullback of sheaves of modules is the
contraction of the iterated pushforward**, the companion of
`Stacks.SheafOfModules.conjugateIsoEquiv_pullbackComp` on the other orientation, with the two
adjunctions exchanged.

This is the orientation in which the comparison occurs inside
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictIso`, where the iterated pullback is
split apart rather than contracted, so it is the form a factor-by-factor computation of that
mate consumes.  It is Mathlib's `SheafOfModules.conjugateEquiv_pullbackComp_inv` read as an
identity of isomorphisms rather than of their underlying natural transformations. -/
public theorem conjugateIsoEquiv_pullbackComp_symm
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj R')
    [(_root_.SheafOfModules.pushforward.{v} φ).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} ψ).IsRightAdjoint] :
    conjugateIsoEquiv
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} φ).comp
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} ψ))
        (_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} (F := F ⋙ G)
          (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ))
        (_root_.SheafOfModules.pullbackComp.{v} φ ψ).symm =
      _root_.SheafOfModules.pushforwardComp.{v} φ ψ :=
  Iso.ext (_root_.SheafOfModules.conjugateEquiv_pullbackComp_inv.{v} φ ψ)

end Stacks.SheafOfModules

end
