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
provided chart presentations are adic\*. -/
@[stacks 0GC0 "all four conditions, with all six equivalences proved, from one named \
hypothesis this library does not have: Stacks 0AKX in the adic* form of Stacks 0AKT together \
with Stacks 0AIC as `hchart`. The library's Stacks 0ANW is unconditional, so nothing is \
forwarded from it; the covering refinement of Stacks 0AJ2 and the implication (2) implies (1) \
of Stacks 0AKX, which used to be forwarded as `href` and `h0AKX`, are theorems. \
Stacks 0AJ3, the implication (4) \
implies (1) of Stacks 0ANL and Stacks 0ANV on countably indexed charts are no longer among \
them: Stacks 0AJ3 is proved for a base which is a formal algebraic space, (4) implies (1) \
is obtained as (4) implies (5) implies (1), and Stacks 0ANV on countably indexed charts is \
proved. Neither are the locality axioms of Situation 0CBA \
for tautness with topological finite type: they follow from the locality of Stacks 0ANU"]
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
