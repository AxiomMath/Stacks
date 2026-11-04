module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FibreProduct.Gluing

/-!
# Fibre products of divided power schemes: existence and comparison maps

This file deduces the main results: divided power schemes have fibre products, the underlying
scheme of the fibre product is a closed subscheme of the ordinary fibre product, and its closed
fibre is the fibre product of the closed fibres.

## Main definitions

* `Crystalline.DividedPowerScheme.underlyingPullbackComparison` — the canonical morphism from
  the underlying scheme of the divided power fibre product to the ordinary fibre product of the
  underlying schemes.
* `Crystalline.DividedPowerScheme.closedFiberPullbackComparison` — the canonical morphism from
  the closed fibre of the divided power fibre product to the ordinary fibre product of the two
  closed fibres, together with the two projection equations
  `closedFiberPullbackComparison_fst` and `closedFiberPullbackComparison_snd` that pin it down.

## Main results

* `Crystalline.DividedPowerScheme.instHasPullbacksDividedPowerScheme` — divided power schemes
  have fibre products.
* `Crystalline.DividedPowerScheme.underlyingPullbackComparison_isClosedImmersion` — the
  underlying scheme of the divided power fibre product is a closed subscheme of the ordinary
  fibre product.
* `Crystalline.DividedPowerScheme.closedFiberPullbackComparison_isIso` — the closed fibre of the
  divided power fibre product is the ordinary fibre product of the closed fibres.

## Implementation notes

A scheme carries a divided power structure with zero ideal
(`Crystalline.DividedPowerScheme.zeroDividedPowerScheme`), and morphisms out of it are exactly
morphisms of schemes into a closed fibre; this is how the closed fibre is probed by a cone, and
it is what turns the closed-fibre comparison into an isomorphism.  The charts are organised by
`Crystalline.DividedPowerScheme.DividedPowerPullbackChart`, a triple of affine opens, and glued
through `Crystalline.DividedPowerScheme.DividedPowerOpenPresentation`, an open cover of a scheme
by divided power schemes whose transition maps induce the ideal sheaf on each smaller chart.
That gluing machinery, together with the zero divided power structure and the closed fibre as a
functor, lives in `StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerGluing`: it is needed
by other constructions that assemble a divided power scheme from affine charts, so it is public
there rather than private here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Opposite
open scoped AlgebraicGeometry

universe u v w

namespace Crystalline.DividedPowerScheme

attribute [local implicit_reducible] specDividedPowerScheme toSpecDividedPowerScheme
  specDividedPowerSchemeUnit specDividedPowerHomEquiv

attribute [local implicit_reducible] affineDividedPowerPushoutComparison

attribute [local implicit_reducible] dividedPowersOfSeparatingFamily

attribute [local implicit_reducible] idealTypeSheaf

attribute [local implicit_reducible] kernelSubmodule

attribute [local implicit_reducible] kernelSubmoduleIsLimit

attribute [local implicit_reducible] kernelSubmoduleIso

attribute [local implicit_reducible] dividedPowerIdealData

attribute [local implicit_reducible] openDividedPowerScheme

attribute [local implicit_reducible] openDividedPowerInclusion

attribute [local implicit_reducible] inducedOpenLift

attribute [local implicit_reducible] globalSectionsDPMorphism

attribute [local implicit_reducible] dividedPowerSchemeForget

attribute [local implicit_reducible] coneSchemeComparison

attribute [local implicit_reducible] zeroDividedPowerScheme

attribute [local implicit_reducible] zeroDividedPowerScheme_map

attribute [local implicit_reducible] zeroClosedFiberPresentation

attribute [local implicit_reducible] zeroDividedPowerScheme_map_factorSpec

attribute [local implicit_reducible] zeroDividedPowerScheme_map_factor

attribute [local implicit_reducible] closedFiberFunctor

attribute [local implicit_reducible] DividedPowerOpenPresentation.closedFiberGluing

attribute [local implicit_reducible] DividedPowerOpenPresentation.ideal

attribute [local implicit_reducible] DividedPowerOpenPresentation.basisDividedPowers

attribute [local implicit_reducible] DividedPowerOpenPresentation.gluedMap

attribute [local implicit_reducible] DividedPowerOpenPresentation.cocone

attribute [local implicit_reducible] DividedPowerOpenPresentation.isColimit

attribute [local implicit_reducible] restrictDividedPowerHom

attribute [local implicit_reducible] DividedPowerPullbackChart.data

attribute [local implicit_reducible] DividedPowerPullbackChart.fst

attribute [local implicit_reducible] DividedPowerPullbackChart.snd

attribute [local implicit_reducible] CategoryTheory.PreZeroHypercover.pullback₁
  CategoryTheory.Precoverage.ZeroHypercover.pullback₁ CategoryTheory.Limits.PullbackCone.mk

/-- Divided power schemes admit fibre products. -/
@[stacks 07ME "existence of fibre products"]
public instance instHasPullbacksDividedPowerScheme :
    HasPullbacks (DividedPowerScheme.{u}) := by
  have : ∀ {X Y Z : DividedPowerScheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z},
      HasLimit (cospan f g) := by
    intro X Y Z f g
    obtain ⟨d⟩ := nonempty_dividedPowerPullbackData f g
    exact (IsPullback.of_isLimit d.isLimit).hasPullback
  exact hasPullbacks_of_hasLimit_cospan _

variable {S T T' : DividedPowerScheme.{u}}
variable (f : T ⟶ S) (f' : T' ⟶ S)

/-- The canonical comparison from the underlying scheme of a divided power fibre product
to the ordinary fibre product of the underlying schemes. -/
public def underlyingPullbackComparison :
    (pullback f f').scheme ⟶ pullback f.hom f'.hom :=
  pullback.lift (pullback.fst f f').hom (pullback.snd f f').hom (by
    simpa only [DividedPowerScheme.Hom.comp_hom] using
      congrArg (fun h : pullback f f' ⟶ S => h.hom)
        (pullback.condition : pullback.fst f f' ≫ f = pullback.snd f f' ≫ f'))

attribute [local implicit_reducible] underlyingPullbackComparison

private theorem underlyingPullbackComparison_fst :
    underlyingPullbackComparison f f' ≫ pullback.fst f.hom f'.hom =
      (pullback.fst f f').hom :=
  pullback.lift_fst _ _ _

private theorem underlyingPullbackComparison_snd :
    underlyingPullbackComparison f f' ≫ pullback.snd f.hom f'.hom =
      (pullback.snd f f').hom :=
  pullback.lift_snd _ _ _

/-- The underlying scheme of the divided power fibre product is a closed subscheme
of the ordinary scheme-theoretic fibre product. -/
@[stacks 07ME "closed immersion into the ordinary fibre product"]
public theorem underlyingPullbackComparison_isClosedImmersion :
    IsClosedImmersion (underlyingPullbackComparison f f') := by
  obtain ⟨d⟩ := nonempty_dividedPowerPullbackData f f'
  let h := IsPullback.of_isLimit d.isLimit
  let e := h.isoPullback
  have hi : IsIso e.inv.hom := dividedPowerSchemeForget.map_isIso e.inv
  have hc := d.isClosedImmersion
  have he : underlyingPullbackComparison f f' = e.inv.hom ≫ coneSchemeComparison d.cone := by
    apply pullback.hom_ext
    · rw [underlyingPullbackComparison_fst, Category.assoc, coneSchemeComparison,
        pullback.lift_fst]
      exact (congrArg DividedPowerScheme.Hom.hom h.isoPullback_inv_fst).symm
    · rw [underlyingPullbackComparison_snd, Category.assoc, coneSchemeComparison,
        pullback.lift_snd]
      exact (congrArg DividedPowerScheme.Hom.hom h.isoPullback_inv_snd).symm
  rw [he]
  infer_instance

/-- **Stacks Tag 07ME.** The canonical morphism from the closed fibre of the divided power fibre
product to the ordinary fibre product of the two closed fibres, together with the two projection
equations that characterize it. -/
public noncomputable def closedFiberPullbackComparisonSpec :
    {c : closedFiber (pullback f f') ⟶
      pullback (closedFiberMap f) (closedFiberMap f') //
      (c ≫ pullback.fst (closedFiberMap f) (closedFiberMap f') =
        closedFiberMap (pullback.fst f f')) ∧
      (c ≫ pullback.snd (closedFiberMap f) (closedFiberMap f') =
        closedFiberMap (pullback.snd f f'))} :=
  ClosedFiberPresentation.pullbackComparison (closedFiberPresentation S)
    (closedFiberPresentation T) (closedFiberPresentation T')
    (closedFiberPresentation (pullback f f')) pullback.condition

attribute [local implicit_reducible] closedFiberPullbackComparisonSpec

/-- The canonical morphism from the closed fibre of the divided power fibre product to the
ordinary fibre product of the two closed fibres. -/
public noncomputable def closedFiberPullbackComparison :
    closedFiber (pullback f f') ⟶
      pullback (closedFiberMap f) (closedFiberMap f') :=
  (closedFiberPullbackComparisonSpec f f').val

attribute [local implicit_reducible] closedFiberPullbackComparison

/-- The closed-fibre comparison followed by the first projection is the closed fibre of the
first projection. -/
@[stacks 07ME "closed-fibre comparison commutes with first projection"]
public theorem closedFiberPullbackComparison_fst :
    closedFiberPullbackComparison f f' ≫
      pullback.fst (closedFiberMap f) (closedFiberMap f') =
        closedFiberMap (pullback.fst f f') :=
  (closedFiberPullbackComparisonSpec f f').property.1

/-- The closed-fibre comparison followed by the second projection is the closed fibre of the
second projection. -/
@[stacks 07ME "closed-fibre comparison commutes with second projection"]
public theorem closedFiberPullbackComparison_snd :
    closedFiberPullbackComparison f f' ≫
      pullback.snd (closedFiberMap f) (closedFiberMap f') =
        closedFiberMap (pullback.snd f f') :=
  (closedFiberPullbackComparisonSpec f f').property.2

/-- The canonical comparison of closed fibres is an isomorphism. -/
@[stacks 07ME "fibre product of closed fibres"]
public theorem closedFiberPullbackComparison_isIso :
    IsIso (closedFiberPullbackComparison f f') := by
  classical
  let Q := pullback (closedFiberMap f) (closedFiberMap f')
  let q₁ := pullback.fst (closedFiberMap f) (closedFiberMap f')
  let q₂ := pullback.snd (closedFiberMap f) (closedFiberMap f')
  let e₁ := zeroDividedPowerScheme_map q₁
  let e₂ := zeroDividedPowerScheme_map q₂
  have hq : q₁ ≫ closedFiberMap f = q₂ ≫ closedFiberMap f' :=
    pullback.condition
  have hcone : e₁ ≫ f = e₂ ≫ f' := by
    apply DividedPowerScheme.Hom.ext
    show (q₁ ≫ closedFiberι T ≫ f.hom) =
      (q₂ ≫ closedFiberι T' ≫ f'.hom)
    rw [← closedFiberMap_comp_closedFiberι, ← closedFiberMap_comp_closedFiberι,
      reassoc_of% hq]
  let ell := pullback.lift e₁ e₂ hcone
  let d := zeroDividedPowerScheme_map_factor ell
  let c := closedFiberPullbackComparison f f'
  have hdinc : d ≫ closedFiberι (pullback f f') = ell.hom :=
    zeroDividedPowerScheme_map_factor_comp ell
  have hlfst : ell.hom ≫ (pullback.fst f f').hom = e₁.hom := by
    simpa only [DividedPowerScheme.Hom.comp_hom] using
      congrArg DividedPowerScheme.Hom.hom (pullback.lift_fst e₁ e₂ hcone)
  have hlsnd : ell.hom ≫ (pullback.snd f f').hom = e₂.hom := by
    simpa only [DividedPowerScheme.Hom.comp_hom] using
      congrArg DividedPowerScheme.Hom.hom (pullback.lift_snd e₁ e₂ hcone)
  have hcfst : c ≫ q₁ = closedFiberMap (pullback.fst f f') :=
    closedFiberPullbackComparison_fst f f'
  have hcsnd : c ≫ q₂ = closedFiberMap (pullback.snd f f') :=
    closedFiberPullbackComparison_snd f f'
  have hd₁ : d ≫ closedFiberMap (pullback.fst f f') = q₁ := by
    apply (cancel_mono (closedFiberι T)).mp
    rw [Category.assoc, closedFiberMap_comp_closedFiberι, reassoc_of% hdinc]
    exact hlfst
  have hd₂ : d ≫ closedFiberMap (pullback.snd f f') = q₂ := by
    apply (cancel_mono (closedFiberι T')).mp
    rw [Category.assoc, closedFiberMap_comp_closedFiberι, reassoc_of% hdinc]
    exact hlsnd
  have hext : ∀ {a b : closedFiber (pullback f f') ⟶ closedFiber (pullback f f')},
      a ≫ closedFiberMap (pullback.fst f f') = b ≫ closedFiberMap (pullback.fst f f') →
      a ≫ closedFiberMap (pullback.snd f f') = b ≫ closedFiberMap (pullback.snd f f') →
      a = b := by
    intro a b h₁ h₂
    have key : zeroDividedPowerScheme_map a = zeroDividedPowerScheme_map b := by
      apply pullback.hom_ext <;> apply DividedPowerScheme.Hom.ext
      · show a ≫ closedFiberι (pullback f f') ≫ (pullback.fst f f').hom =
          b ≫ closedFiberι (pullback f f') ≫ (pullback.fst f f').hom
        rw [← closedFiberMap_comp_closedFiberι, reassoc_of% h₁]
      · show a ≫ closedFiberι (pullback f f') ≫ (pullback.snd f f').hom =
          b ≫ closedFiberι (pullback f f') ≫ (pullback.snd f f').hom
        rw [← closedFiberMap_comp_closedFiberι, reassoc_of% h₂]
    exact (cancel_mono (closedFiberι (pullback f f'))).mp
      (congrArg DividedPowerScheme.Hom.hom key)
  refine ⟨d, hext ?_ ?_, pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, hd₁, Category.id_comp, hcfst]
  · rw [Category.assoc, hd₂, Category.id_comp, hcsnd]
  · rw [Category.assoc, hcfst, hd₁, Category.id_comp]
  · rw [Category.assoc, hcsnd, hd₂, Category.id_comp]

end Crystalline.DividedPowerScheme

end
