module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentMayerVietorisStageExt

/-!
# The Mayer--Vietoris terms of Tag 0DI7 as morphism sets of restrictions

The Mayer--Vietoris sequence of Stacks 08BW on `U₀ ∪ V₀`, pushed to a stage by the derived
pullback, has for its terms the morphism groups out of the extensions by zero of the two opens
cut out by `U₀` and by `V₀`
(`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentMayerVietorisStageExt.lean`). The four
systems of derived morphism sets the union step compares are instead morphism groups *of the
restrictions*. This file crosses that gap, which is Stacks 08BT: morphisms out of `j_{!}j^*E`
into a shift of `F` are morphisms from `E|_A` into the shift of `F|_A`.

Composing the derived base change of
`RelativeDescentMayerVietorisStageExt.lean` with the adjunction of Stacks 08BT gives, at a stage
and at the limit, an additive identification of the Mayer--Vietoris term with a morphism group of
restrictions to the open cut out there. What remains afterwards is to replace the restriction
`j_A^*` by the derived pullback along the inclusion of `A`, which is
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso`, and then to recognise
that pullback as the one of the restricted situation, which is the content of
`AlgebraicGeometry.RelativeDescentSituation.bijective_schemeFactorTowerHom_isoOpensRange`.

## Main definitions

* `AlgebraicGeometry.RelativeDescentSituation.restrictSupLimitOpenLeft` and
  `restrictSupLimitOpenRight`: the opens cut out by `U₀` and by `V₀` at the limit, the limit
  counterparts of `restrictSupStageOpenLeft` and `restrictSupStageOpenRight`.
* `AlgebraicGeometry.RelativeDescentSituation.restrictSupStageExtAddEquivLeft` and
  `restrictSupStageExtAddEquivRight`: **the Mayer--Vietoris term at a stage is a morphism group of
  restrictions.** Derived base change for extension by zero, followed by the adjunction of
  Stacks 08BT.
* `AlgebraicGeometry.RelativeDescentSituation.restrictSupLimitExtAddEquivLeft` and
  `restrictSupLimitExtAddEquivRight`: the same at the limit.

## Implementation notes

The two steps go in this order and no other. Stacks 08BT is stated at the extension by zero of
the restriction *on the space where the restriction is taken*, so it can only be applied after
the base change has moved the extension by zero from `U₀ ∪ V₀` to the stage; applying it first
would leave the derived pullback on the wrong side of the adjunction.

The base change isomorphism is used through `Stacks.ExtensionByZero.precompAddEquiv` rather than
by rewriting, since the terms are morphism groups and the comparison acts on their sources; its
`symm` appears because `precompAddEquiv` is contravariant in the source.

Every argument of `precompAddEquiv` and of `extensionRestrictionExtEquiv` is written out rather
than left to unification. With them elided the elaborator has to solve for the structure sheaf
and the open by unifying against the stated type, and each of these four definitions then kills
the process outright; naming the arguments is what makes them elaborate in seconds. The opens at
the limit are abbreviated for the same reason, to keep the stated types small.

## References

* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 08BW](https://stacks.math.columbia.edu/tag/08BW)
* [Stacks Project, Tag 08BT](https://stacks.math.columbia.edu/tag/08BT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction ExtensionByZeroModules
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.ExtensionByZero
  (derivedExtensionRestriction derivedRestriction extensionRestrictionExtEquiv precompAddEquiv)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

attribute [local implicit_reducible] restrict

section Sup

variable (K₀ L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))
  (U₀ V₀ : D.X₀.left.Opens)
  (hsup : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left))

/-- The open cut out by `U₀` at the limit of the situation restricted to `U₀ ∪ V₀`. -/
abbrev restrictSupLimitOpenLeft :
    TopologicalSpace.Opens (D.restrict (U₀ ⊔ V₀) hsup).limitScheme.toRingedSpace.carrier :=
  (TopologicalSpace.Opens.map
    (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage.toLRSHom.toShHom.hom.base).obj
      (D.restrictSupOpenLeft U₀ V₀)

/-- The open cut out by `V₀` at the limit of the situation restricted to `U₀ ∪ V₀`. -/
abbrev restrictSupLimitOpenRight :
    TopologicalSpace.Opens (D.restrict (U₀ ⊔ V₀) hsup).limitScheme.toRingedSpace.carrier :=
  (TopologicalSpace.Opens.map
    (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage.toLRSHom.toShHom.hom.base).obj
      (D.restrictSupOpenRight U₀ V₀)

/-- **The Mayer--Vietoris term attached to `U₀` at a stage is a morphism group of restrictions.**
Morphisms from the derived pullback of the extension by zero of `K₀|_{U₀∪V₀}` to the open cut out
by `U₀`, into the `n`-th shift of the derived pullback of `L₀|_{U₀∪V₀}`, are morphisms between the
restrictions of those derived pullbacks to the open cut out by `U₀` at that stage. This is derived
base change for extension by zero followed by Stacks 08BT. -/
def restrictSupStageExtAddEquivLeft (n : ℤ) (i : D.LaterIndex) :
    ((derivedExtensionRestriction (D.restrictSupRing U₀ V₀) (D.restrictSupOpenLeft U₀ V₀) ⋙
            derivedPullback
              ((D.restrict (U₀ ⊔ V₀) hsup).toFixedStage i).toLRSHom.toShHom).obj
          ((derivedPullback (U₀ ⊔ V₀ : D.X₀.left.Opens).ι.toLRSHom.toShHom).obj K₀) ⟶
        (D.restrictStageObj (U₀ ⊔ V₀) hsup L₀ i)⟦n⟧) ≃+
      ((derivedRestriction (D.restrictSupStageRing U₀ V₀ hsup i)
              (D.restrictSupStageOpenLeft U₀ V₀ hsup i)).obj
            (D.restrictStageObj (U₀ ⊔ V₀) hsup K₀ i) ⟶
          ((derivedRestriction (D.restrictSupStageRing U₀ V₀ hsup i)
              (D.restrictSupStageOpenLeft U₀ V₀ hsup i)).obj
            (D.restrictStageObj (U₀ ⊔ V₀) hsup L₀ i))⟦n⟧) :=
  (precompAddEquiv ((D.restrictStageObj (U₀ ⊔ V₀) hsup L₀ i)⟦n⟧)
      (((D.restrictSupStageExtensionIsoLeft U₀ V₀ hsup i).app
        ((derivedPullback (U₀ ⊔ V₀ : D.X₀.left.Opens).ι.toLRSHom.toShHom).obj K₀)).symm)).trans
    (extensionRestrictionExtEquiv (D.restrictSupStageRing U₀ V₀ hsup i)
      (D.restrictSupStageOpenLeft U₀ V₀ hsup i)
      (D.restrictStageObj (U₀ ⊔ V₀) hsup K₀ i)
      (D.restrictStageObj (U₀ ⊔ V₀) hsup L₀ i) n)

/-- **The Mayer--Vietoris term attached to `V₀` at a stage is a morphism group of
restrictions.** -/
def restrictSupStageExtAddEquivRight (n : ℤ) (i : D.LaterIndex) :
    ((derivedExtensionRestriction (D.restrictSupRing U₀ V₀) (D.restrictSupOpenRight U₀ V₀) ⋙
            derivedPullback
              ((D.restrict (U₀ ⊔ V₀) hsup).toFixedStage i).toLRSHom.toShHom).obj
          ((derivedPullback (U₀ ⊔ V₀ : D.X₀.left.Opens).ι.toLRSHom.toShHom).obj K₀) ⟶
        (D.restrictStageObj (U₀ ⊔ V₀) hsup L₀ i)⟦n⟧) ≃+
      ((derivedRestriction (D.restrictSupStageRing U₀ V₀ hsup i)
              (D.restrictSupStageOpenRight U₀ V₀ hsup i)).obj
            (D.restrictStageObj (U₀ ⊔ V₀) hsup K₀ i) ⟶
          ((derivedRestriction (D.restrictSupStageRing U₀ V₀ hsup i)
              (D.restrictSupStageOpenRight U₀ V₀ hsup i)).obj
            (D.restrictStageObj (U₀ ⊔ V₀) hsup L₀ i))⟦n⟧) :=
  (precompAddEquiv ((D.restrictStageObj (U₀ ⊔ V₀) hsup L₀ i)⟦n⟧)
      (((D.restrictSupStageExtensionIsoRight U₀ V₀ hsup i).app
        ((derivedPullback (U₀ ⊔ V₀ : D.X₀.left.Opens).ι.toLRSHom.toShHom).obj K₀)).symm)).trans
    (extensionRestrictionExtEquiv (D.restrictSupStageRing U₀ V₀ hsup i)
      (D.restrictSupStageOpenRight U₀ V₀ hsup i)
      (D.restrictStageObj (U₀ ⊔ V₀) hsup K₀ i)
      (D.restrictStageObj (U₀ ⊔ V₀) hsup L₀ i) n)

/-- **The Mayer--Vietoris term attached to `U₀` at the limit is a morphism group of
restrictions.** -/
def restrictSupLimitExtAddEquivLeft (n : ℤ) :
    ((derivedExtensionRestriction (D.restrictSupRing U₀ V₀) (D.restrictSupOpenLeft U₀ V₀) ⋙
            derivedPullback
              (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage.toLRSHom.toShHom).obj
          ((derivedPullback (U₀ ⊔ V₀ : D.X₀.left.Opens).ι.toLRSHom.toShHom).obj K₀) ⟶
        (D.restrictLimitObj (U₀ ⊔ V₀) hsup L₀)⟦n⟧) ≃+
      ((derivedRestriction (D.restrictSupLimitRing U₀ V₀ hsup)
              (D.restrictSupLimitOpenLeft U₀ V₀ hsup)).obj
            (D.restrictLimitObj (U₀ ⊔ V₀) hsup K₀) ⟶
          ((derivedRestriction (D.restrictSupLimitRing U₀ V₀ hsup)
              (D.restrictSupLimitOpenLeft U₀ V₀ hsup)).obj
            (D.restrictLimitObj (U₀ ⊔ V₀) hsup L₀))⟦n⟧) :=
  (precompAddEquiv ((D.restrictLimitObj (U₀ ⊔ V₀) hsup L₀)⟦n⟧)
      (((D.restrictSupLimitExtensionIsoLeft U₀ V₀ hsup).app
        ((derivedPullback (U₀ ⊔ V₀ : D.X₀.left.Opens).ι.toLRSHom.toShHom).obj K₀)).symm)).trans
    (extensionRestrictionExtEquiv (D.restrictSupLimitRing U₀ V₀ hsup)
      (D.restrictSupLimitOpenLeft U₀ V₀ hsup)
      (D.restrictLimitObj (U₀ ⊔ V₀) hsup K₀)
      (D.restrictLimitObj (U₀ ⊔ V₀) hsup L₀) n)

/-- **The Mayer--Vietoris term attached to `V₀` at the limit is a morphism group of
restrictions.** -/
def restrictSupLimitExtAddEquivRight (n : ℤ) :
    ((derivedExtensionRestriction (D.restrictSupRing U₀ V₀) (D.restrictSupOpenRight U₀ V₀) ⋙
            derivedPullback
              (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage.toLRSHom.toShHom).obj
          ((derivedPullback (U₀ ⊔ V₀ : D.X₀.left.Opens).ι.toLRSHom.toShHom).obj K₀) ⟶
        (D.restrictLimitObj (U₀ ⊔ V₀) hsup L₀)⟦n⟧) ≃+
      ((derivedRestriction (D.restrictSupLimitRing U₀ V₀ hsup)
              (D.restrictSupLimitOpenRight U₀ V₀ hsup)).obj
            (D.restrictLimitObj (U₀ ⊔ V₀) hsup K₀) ⟶
          ((derivedRestriction (D.restrictSupLimitRing U₀ V₀ hsup)
              (D.restrictSupLimitOpenRight U₀ V₀ hsup)).obj
            (D.restrictLimitObj (U₀ ⊔ V₀) hsup L₀))⟦n⟧) :=
  (precompAddEquiv ((D.restrictLimitObj (U₀ ⊔ V₀) hsup L₀)⟦n⟧)
      (((D.restrictSupLimitExtensionIsoRight U₀ V₀ hsup).app
        ((derivedPullback (U₀ ⊔ V₀ : D.X₀.left.Opens).ι.toLRSHom.toShHom).obj K₀)).symm)).trans
    (extensionRestrictionExtEquiv (D.restrictSupLimitRing U₀ V₀ hsup)
      (D.restrictSupLimitOpenRight U₀ V₀ hsup)
      (D.restrictLimitObj (U₀ ⊔ V₀) hsup K₀)
      (D.restrictLimitObj (U₀ ⊔ V₀) hsup L₀) n)

end Sup

end AlgebraicGeometry.RelativeDescentSituation

end
