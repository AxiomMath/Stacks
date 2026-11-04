module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SiteEnlargementDense
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-!
# Restriction of sheaves along the transport of étale charts

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B` and let
`X` be an algebraic space over `S` for `B`, with inverse image `X'` on the enlarged site. The
transport of étale charts is a dense subsite inclusion
(`AlgebraicGeometry.SiteEnlargement.chartTransport_isDenseSubsite`), so restriction of sheaves
along it is an equivalence of categories for every category of coefficients with limits of size
`u`. This file records the instances that make the equivalence available, and the identification
of the restricted structure sheaf with the structure sheaf.

## Main results

* `AlgebraicGeometry.SiteEnlargement.isEquivalence_restrict`: restriction of sheaves is an
  equivalence.
* `AlgebraicGeometry.SiteEnlargement.hasLimitsOfShape_structuredArrow`: the limits computing the
  right Kan extension along the transport exist, for coefficients with limits of size `u`.
* `AlgebraicGeometry.SiteEnlargement.restrict_structureSheaf`: the restriction of the structure
  sheaf of `X'` is the structure sheaf of `X`, on the nose.

## References

* [Stacks Project, Tag 03G7](https://stacks.math.columbia.edu/tag/03G7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SiteEnlargement

open Space

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The transport of étale charts is continuous. This is registered as an instance on its own,
rather than through the dense subsite property, so that instance search for unrelated classes on
the small étale site of `X'` is not routed through the comparison of topoi. -/
instance isContinuous_chartTransport :
    (chartTransport B B' h S hS X).IsContinuous (Space.SmallEtale.topology B S hS X.obj)
      (Space.SmallEtale.topology B' S (largerContains h hS)
        ((changeBigSite B B' h S hS).obj X).obj) :=
  haveI := chartTransport_isDenseSubsite B B' h S hS X
  inferInstance

/-- The transport of étale charts is cocontinuous. -/
instance isCocontinuous_chartTransport :
    (chartTransport B B' h S hS X).IsCocontinuous (Space.SmallEtale.topology B S hS X.obj)
      (Space.SmallEtale.topology B' S (largerContains h hS)
        ((changeBigSite B B' h S hS).obj X).obj) :=
  haveI := chartTransport_isDenseSubsite B B' h S hS X
  inferInstance

/-- The right Kan extension along the transport of étale charts exists for coefficients with
limits of size `u`: the indexing categories are essentially small. -/
instance hasLimitsOfShape_structuredArrow (A : Type*) [Category.{u} A]
    [HasLimitsOfSize.{u, u} A]
    (V : (Space.SmallEtale B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj X).obj)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow V (chartTransport B B' h S hS X).op) A :=
  hasLimitsOfShape_of_essentiallySmall _ _

/-- **Restriction along the transport of étale charts is an equivalence of categories of
sheaves**, for coefficients with limits of size `u`: the comparison lemma for the dense subsite
inclusion `AlgebraicGeometry.SiteEnlargement.chartTransport_isDenseSubsite`. -/
instance isEquivalence_restrict (A : Type*) [Category.{u} A] [HasLimitsOfSize.{u, u} A] :
    ((chartTransport B B' h S hS X).sheafPushforwardContinuous A
        (Space.SmallEtale.topology B S hS X.obj)
        (Space.SmallEtale.topology B' S (largerContains h hS)
          ((changeBigSite B B' h S hS).obj X).obj)).IsEquivalence :=
  haveI := chartTransport_isDenseSubsite B B' h S hS X
  inferInstance

/-- **The restriction of the structure sheaf of `X'` along the transport of étale charts is the
structure sheaf of `X`**, on the nose: both assign to a chart the global functions of the same
scheme. -/
theorem restrict_structureSheaf :
    ((chartTransport B B' h S hS X).sheafPushforwardContinuous CommRingCat.{u}
        (Space.SmallEtale.topology B S hS X.obj)
        (Space.SmallEtale.topology B' S (largerContains h hS)
          ((changeBigSite B B' h S hS).obj X).obj)).obj
        (smallEtaleRingedTopos B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X)).O =
      (smallEtaleRingedTopos B S hS X).O :=
  rfl

example : ((chartTransport B B' h S hS X).sheafPushforwardContinuous (Type u)
        (Space.SmallEtale.topology B S hS X.obj)
        (Space.SmallEtale.topology B' S (largerContains h hS)
          ((changeBigSite B B' h S hS).obj X).obj)).IsEquivalence := inferInstance

example : ((chartTransport B B' h S hS X).sheafPushforwardContinuous CommRingCat.{u}
        (Space.SmallEtale.topology B S hS X.obj)
        (Space.SmallEtale.topology B' S (largerContains h hS)
          ((changeBigSite B B' h S hS).obj X).obj)).IsEquivalence := inferInstance

end AlgebraicGeometry.SiteEnlargement

end
