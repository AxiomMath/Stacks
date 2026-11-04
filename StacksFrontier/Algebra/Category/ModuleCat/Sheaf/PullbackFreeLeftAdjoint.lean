module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Comparing an arbitrary left adjoint of restriction of scalars with extension of scalars

Let `F : C ⥤ D` be a continuous functor between sites and let `φ : S ⟶ F_*R` be a morphism of
sheaves of rings.  Restriction of scalars `SheafOfModules.pushforward φ` then has
`SheafOfModules.pullback φ` as a left adjoint, but a consumer may have a *different*
left adjoint `L` in hand -- the restriction of a sheaf of modules to an open subscheme, say -- and
with it a comparison `CategoryTheory.Adjunction.leftAdjointUniq` of the two.  This file says what
that comparison does to the unit sheaf and to a free sheaf of modules.

## Main results

* `Stacks.SheafOfModules.leftAdjointUniq_hom_app_unit_comp_pullbackObjUnitToUnit`: **the
  comparison of two left adjoints of restriction of scalars, followed at the unit sheaf by
  Mathlib's unit comparison for extension of scalars, is the transpose of
  `SheafOfModules.unitToPushforwardObjUnit`.**  No finality hypothesis is needed:
  the right-hand side is a transpose and not an inverse.
* `Stacks.SheafOfModules.pullbackObjFreeIso_hom_eq_mapFreeIso_inv_of_unit`: **a transformation
  from a coproduct-preserving functor `L` into extension of scalars which is compatible with the
  unit identifications is compatible with the free identifications**: composing it with Mathlib's
  `SheafOfModules.pullbackObjFreeIso` gives back the free identification
  `SheafOfModules.mapFreeIso` built from `L`'s own unit identification.

## Implementation notes

The free statement takes the unit identification `η`, the transformation `τ` and their
compatibility as parameters rather than specialising to a comparison of adjunctions, as
`Stacks.SheafOfModules.free_comp_pullbackObjFreeIso_hom_of_unit` does:  a consumer whose functor
is only definitionally the one a specialised statement would name cannot present it in that
shape, because instance resolution for its extension of scalars does not succeed there.

The coproduct-preservation hypothesis of `L` is an instance binder, matching
`SheafOfModules.mapFreeIso`, so that a consumer for which instance search misses
it -- as it does for the restriction functor of a scheme, see
`Stacks.Modules.preservesColimitsOfShape_discrete_restrictFunctor` -- can supply
it as an explicit argument of an `@`-application.  The class is a `Prop`, so the `mapFreeIso` of
the conclusion is then the same term as one built with any other proof of it.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules

universe v₁ v₂ u₁ u₂ u

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  [hadj : (_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]

/-- **The comparison of an arbitrary left adjoint of restriction of scalars with extension of
scalars, read at the unit sheaf and followed by the unit comparison of extension of scalars, is
the transpose of `SheafOfModules.unitToPushforwardObjUnit`.**

Transposing across `adj` turns the comparison into the unit of the extension–restriction
adjunction by `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app`, and the unit followed
by the restriction of scalars of a morphism is that morphism's transpose, which Mathlib's
`SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`
identifies. -/
theorem leftAdjointUniq_hom_app_unit_comp_pullbackObjUnitToUnit
    {L : _root_.SheafOfModules.{u} S ⥤ _root_.SheafOfModules.{u} R}
    (adj : L ⊣ _root_.SheafOfModules.pushforward.{u} φ) :
    (adj.leftAdjointUniq
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ)).hom.app (unit S) ≫
        pullbackObjUnitToUnit φ =
      (adj.homEquiv (unit S) (unit R)).symm (unitToPushforwardObjUnit φ) := by
  refine (adj.homEquiv (unit S) (unit R)).injective ?_
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit,
    _root_.SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]

section Free

variable [hsJ : HasWeakSheafify J AddCommGrpCat.{u}] [hsK : HasSheafify K AddCommGrpCat.{u}]
  [hwJ : J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [hwK : K.WEqualsLocallyBijective AddCommGrpCat.{u}] [hfin : F.Final]

/-- **A transformation from a coproduct-preserving functor into extension of scalars which is
compatible with the unit identifications is compatible with the free identifications.**  The
functor `L`, its unit identification `η`, the transformation `τ` and the compatibility are all
parameters, so nothing here mentions a comparison of adjunctions.

A free sheaf of modules is a coproduct of copies of the unit sheaf and `L` preserves that
coproduct, so both sides agree as soon as they agree after each tautological inclusion;  there
Mathlib's `SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom` and
`SheafOfModules.map_ιFree_mapFreeIso_inv` leave exactly the hypothesis. -/
theorem pullbackObjFreeIso_hom_eq_mapFreeIso_inv_of_unit
    {L : _root_.SheafOfModules.{u} S ⥤ _root_.SheafOfModules.{u} R} (I : Type u)
    [hL : PreservesColimitsOfShape.{u, u} (Discrete I) L]
    (η : unit R ≅ L.obj (unit S))
    (τ : L ⟶ _root_.SheafOfModules.pullback.{u} φ)
    (hτ : τ.app (unit S) ≫ pullbackObjUnitToUnit φ = η.inv) :
    τ.app (free (R := S) I) ≫ (pullbackObjFreeIso φ I).hom = (mapFreeIso L I η).inv := by
  refine Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit L _ _
    (isColimitFreeCofan (R := S) I)) _ _ fun i => ?_
  have hnat := τ.naturality (ιFree (R := S) i)
  dsimp only [cofan_mk_inj] at hnat ⊢
  rw [← Category.assoc, hnat, Category.assoc,
    _root_.SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom,
    ← Category.assoc, hτ, map_ιFree_mapFreeIso_inv]

end Free

end Stacks.SheafOfModules

end
