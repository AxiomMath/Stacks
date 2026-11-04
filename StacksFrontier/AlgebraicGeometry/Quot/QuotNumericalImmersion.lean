module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalSubstackFlatClosed
public import StacksFrontier.AlgebraicGeometry.Quot.QuotCoherentCondition

/-!
# `Quot^P_{F/X/B} ⟶ Quot_{F/X/B}` by base change from `Coh^P_{X/B} ⟶ Coh_{X/B}` (Stacks 0DP6)

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation and `F` a
quasi-coherent `𝒪_X`-module.  For a condition `Q` on the objects of `Coh_{X/B}` which is inherited
along the morphisms of `Coh_{X/B}`, the fibre product `Quot_{F/X/B} ×_{Coh_{X/B}} Coh^Q_{X/B}` is
the subfunctor `AlgebraicGeometry.Space.QuotSituation.quotCondition` of the Quot functor.  Remark
0DP6 deduces the properties of its inclusion into `Quot_{F/X/B}` from those of the inclusion
`Coh^Q_{X/B} ⟶ Coh_{X/B}`, by base change along `Quot_{F/X/B} ⟶ Coh_{X/B}`: if `Coh^Q_{X/B}` is a
flat closed substack, then `Quot^Q_{F/X/B} ⟶ Quot_{F/X/B}` is representable by flat closed
immersions, and if it is an open and closed substack, then that inclusion is representable by open
and closed immersions.  This file records the two base changes, in the vocabulary
`AlgebraicGeometry.Space.CoherentSituation.IsFlatClosedCondition` and
`AlgebraicGeometry.Space.CoherentSituation.IsOpenAndClosedCondition` of Stacks 04XB for strictly
full subcategories of `Coh_{X/B}`.

## Main results

* `relative_closedImmersion_flat_quotCondition_ι_of_isFlatClosedCondition`:
  the base change of a flat closed substack of `Coh_{X/B}`.
* `relative_openImmersion_closedImmersion_quotCondition_ι_of_isOpenAndClosedCondition`:
  the base change of an open and closed substack of `Coh_{X/B}`.

## References

* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS) {Q : CoherentObject D.toCoherentSituation → Prop}

/-- **The base change of a flat closed substack of `Coh_{X/B}`.**  If a condition `Q` on the
objects of `Coh_{X/B}`, inherited along its morphisms, cuts out a flat closed substack, then the
inclusion of the fibre product `Quot_{F/X/B} ×_{Coh_{X/B}} Coh^Q_{X/B}` into `Quot_{F/X/B}` is
representable by flat closed immersions. -/
theorem relative_closedImmersion_flat_quotCondition_ι_of_isFlatClosedCondition
    (hQ : ∀ {A' A : CoherentObject D.toCoherentSituation}, CoherentHom A' A → Q A → Q A')
    (h : CoherentSituation.IsFlatClosedCondition D.toCoherentSituation Q) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} (D.quotCondition Q hQ).ι :=
  D.relative_closedImmersion_flat_quotCondition_ι hQ
    (CoherentSituation.isFlatClosedCondition_iff_isCutOutOnTestSchemes.1 h)

/-- **The base change of an open and closed substack of `Coh_{X/B}`.**  If a condition `Q` on the
objects of `Coh_{X/B}`, inherited along its morphisms, cuts out an open and closed substack, then
the inclusion of the fibre product `Quot_{F/X/B} ×_{Coh_{X/B}} Coh^Q_{X/B}` into `Quot_{F/X/B}` is
representable by morphisms which are open and closed immersions. -/
theorem relative_openImmersion_closedImmersion_quotCondition_ι_of_isOpenAndClosedCondition
    (hQ : ∀ {A' A : CoherentObject D.toCoherentSituation}, CoherentHom A' A → Q A → Q A')
    (h : CoherentSituation.IsOpenAndClosedCondition D.toCoherentSituation Q) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} ⊓
        @_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} (D.quotCondition Q hQ).ι :=
  D.relative_openImmersion_closedImmersion_quotCondition_ι hQ
    (CoherentSituation.isOpenAndClosedCondition_iff_isCutOutOnTestSchemes.1 h)

end QuotSituation

end AlgebraicGeometry.Space

end
