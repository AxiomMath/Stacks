module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFiniteTypeCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentingRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterizationRefined
public import StacksFrontier.RingTheory.Rig.FiniteType

/-!
# Characterising finite type morphisms of locally adic\* formal algebraic spaces: the refined forms

For a morphism of locally adic\* formal algebraic spaces, being locally of finite type is
equivalent to each of three conditions tested on affine étale charts: that the arrows of
`WAdm^{adic*}` arising from charts are adic and topologically of finite type.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_adicStar_tfae'`: for a morphism of
  locally adic\* formal algebraic spaces, the three chart-tested conditions and being locally of
  finite type are equivalent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {B S hS}

/-- For a morphism `f : X ⟶ Y` of locally adic\* formal algebraic spaces over `S`, the condition
that every affine representable étale square over `f` carry an adic, topologically of finite type
arrow of `WAdm^{adic*}`, the existence of an affine étale covering of `Y` together with affine
étale coverings of the fibre products of its members with `X` on which that condition holds, the
existence of an affine étale covering of `X` whose members factor through affine representable
étale charts of `Y` by such arrows, and `f` being locally of finite type, are all equivalent,
given `hchart : ChartPresentationIsAdicStar`, which asks that every ring presenting an affine
chart, weakly admissible or not, be adic\*.

Stacks 0GC0 itself, at the source's hypotheses, is
`AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_tfae_of_isLocallyAdicStar`: the input it
needs is the weakly admissible form of `hchart`,
`AlgebraicGeometry.FormalSpace.chartPresentationIsAdicStarOfWeaklyAdmissible`, which the library
proves from Stacks 0AKX for the adic\* property and Stacks 0AIC. -/
theorem isLocallyOfFiniteType_adicStar_tfae' {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y)
    (hchart : ChartPresentationIsAdicStar B S hS) :
    List.TFAE
      [HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar
          TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom f,
        HasPropertyAfterTargetCover B S hS TopologicalRing.IsAdicStar
          TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom f,
        HasPropertyAfterSourceCover B S hS TopologicalRing.IsAdicStar
          TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom f,
        IsLocallyOfFiniteType B S hS f] := by
  have h0ANW := isLocallyOfFiniteType_tfae' f
    (isLocallyCountablyIndexed_of_isLocallyAdicStar hX)
    (isLocallyCountablyIndexed_of_isLocallyAdicStar hY)
  tfae_have 1 ↔ 4 :=
    (hasPropertyOnEveryAffineEtaleDiagram_adicStar_iff hchart f hX hY).trans (h0ANW.out 1 4)
  tfae_have 2 ↔ 4 :=
    (hasPropertyAfterTargetCover_adicStar_iff hchart f hX hY).trans (h0ANW.out 2 4)
  tfae_have 3 ↔ 4 :=
    (hasPropertyAfterSourceCover_adicStar_iff hchart f hX hY).trans (h0ANW.out 3 4)
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
