module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Kaehler.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge

/-!
# The transition maps between affine étale charts are étale ring maps

Let `F` be an algebraic space over a scheme `S` and let `f : V ⟶ U` be a morphism of the small
étale site of `F`.  When the two underlying schemes are affine, the restriction ring map

`𝒪_F(U) ⟶ 𝒪_F(V)`

is étale, and so `Ω[𝒪_F(V)⁄𝒪_F(U)] = 0` by Algebra, Lemma 00UU.

The affineness of the larger chart cannot be dropped: for `F = P¹_k` over `S = Spec k`, `U` the
identity chart and `V` the open immersion `A¹ ↪ P¹`, one has `𝒪_F(U) = k` and `𝒪_F(V) = k[t]`,
and `Ω[k[t]⁄k]` is free of rank one.

## Main results

* `AlgebraicGeometry.Space.etale_chartRestrict_of_affineChart`: restriction along a morphism of
  affine étale charts is an étale ring map.
* `AlgebraicGeometry.Space.subsingleton_kaehlerDifferential_chartRing_of_affineChart`:
  the module of differentials of that ring map vanishes.

## References

* [Stacks Project, Tag 00UU](https://stacks.math.columbia.edu/tag/00UU), unramified ring maps.
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED), the small étale site.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- Restriction of regular functions along a morphism of affine étale charts is an étale ring
map. -/
theorem etale_chartRestrict_of_affineChart {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    (chartRestrict (hF := hF) f).Etale := by
  have _ := hU
  have _ := hV
  have _ : AlgebraicGeometry.Etale
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map f) :=
    etale_of_comp_etale_chart B S hS V.property U.property (CostructuredArrow.w f.hom)
  exact HasRingHomProperty.appTop (P := @AlgebraicGeometry.Etale)
    ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map f) inferInstance

/-- For a morphism `f : V ⟶ U` of étale charts of `F` whose two underlying schemes are affine, the
module of differentials of the restriction ring map `𝒪_F(U) ⟶ 𝒪_F(V)` vanishes. -/
theorem subsingleton_kaehlerDifferential_chartRing_of_affineChart {U V : SmallEtale B S hS F}
    (f : V ⟶ U)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    letI := chartAlgebra (hF := hF) f
    Subsingleton (KaehlerDifferential (chartRing B S hS F hF U)
      (chartRing B S hS F hF V)) :=
  (etale_chartRestrict_of_affineChart B S hS (hF := hF) f hU
    hV).formallyUnramified.subsingleton_kaehlerDifferential

end AlgebraicGeometry.Space

end
