module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.StabilizerDimension
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SourceFiberIdentity
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionStabilizer
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.Topology.Dimension.Krull
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.RestrictedArrowStalk

/-!
# The stabilizer fibre is at most as large as the source fibre at the identity

Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `s` and `t` locally of finite
presentation, let `u` be a finite type point of `U`, let `F_u = s^{-1}(u)` be the source fibre
and let `G_u` be the fibre at `u` of the stabilizer group scheme. Then

  `dim(G_u) ≤ dim_{e(u)}(F_u)`,

the dimension of the stabilizer fibre being bounded by the *local* dimension of the source fibre
at the identity arrow.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_stabilizerFiber_le_sourceFiberIdentity` is the
  inequality.

## Implementation notes

The inequality is the exhaustiveness input for the induction of Tag 04MZ: its base case is the
equality `dim_{e(u)}(F_u) = dim(G_u)` while the slicing lemma of Tag 0461 needs the strict
inequality `dim(G_u) < dim_{e(u)}(F_u)`, so without this bound the remaining case could not be
excluded.

Three steps make up the proof. First, the arrow scheme `R_u` of the restriction of `G` to
`Spec κ(u)` has the dimension of `G_u`; this is Tag 04MQ applied to that restriction, whose
object scheme is `Spec κ(u)`, together with the identification of its stabilizer as the base
change of the stabilizer of `G` (Tag 04ML). Second, `R_u` is the fibre over `u` of the target map
restricted to `F_u`, which is a chain of fibre-product manipulations. Third, the dimension of
`R_u` is its *local* dimension at every point, by Tag 04LU, and the local dimension of a fibre of
a morphism out of `F_u` at a point bounds no more than the local dimension of `F_u` there,
because a fibre embeds.

The pullback comparisons, the restricted target map and the chart `Spec(κ(u)) ⟶ U` are shared
with the proof of Tag 0461 and are imported rather than restated: `overPullbackLeftIso` from
`StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.OverPullbackLeft`, and
`GroupoidScheme.residueChart`, `GroupoidScheme.targetOnSourceFiber` and
`GroupoidScheme.targetOnSourceFiber_sourceFiberIdentity` from
`StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.RestrictedArrowStalk`. The pullback in `Over S`
used by the restriction of a groupoid scheme is compared with the pullback of schemes by
`AlgebraicGeometry.overFibreProduct_isPullback`.

## References

* [Stacks Project, Tag 04MZ](https://stacks.math.columbia.edu/tag/04MZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

open GroupoidScheme

/-! ### Comparisons of pullbacks -/

/-! ### The restriction to the residue field at a point -/

/-! ### The inequality -/

/-- The local dimension at a point of a fibre of a morphism out of `X` is at most the local
dimension of `X` at the image of that point, the fibre being embedded in `X`. -/
private theorem stabDimKrullDimAt_fiber_le {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (z : f.fiber y) :
    topologicalKrullDimAt (f.fiber y) z ≤ topologicalKrullDimAt X (f.fiberι y z) :=
  topologicalKrullDimAt_le_of_isEmbedding (f.fiberι y).isEmbedding z

/-- **Stacks Project, Tag 04MZ**, exhaustiveness input. Let `(U, R, s, t, c)` be a groupoid
scheme over `S` with `s` and `t` locally of finite presentation and let `u` be a finite type
point of `U`. Then the fibre `G_u` at `u` of the stabilizer group scheme has dimension at most
the local dimension of the source fibre `F_u` at the identity arrow `e(u)`.

The stabilizer fibre is the arrow scheme of the restriction of the groupoid to `Spec κ(u)`, by
Tag 04MQ and Tag 04ML; that arrow scheme is a fibre of the target map restricted to `F_u`, and
its dimension is its local dimension at the identity arrow by Tag 04LU, since its own object
scheme is the spectrum of a field. A fibre embeds, so that local dimension is at most the local
dimension of `F_u` at `e(u)`.

This is the inequality which makes the induction of Tag 04MZ exhaustive: that induction splits
on `dim_{e(u)}(F_u) = dim(G_u)` versus `dim_{e(u)}(F_u) > dim(G_u)`, and the remaining case is
excluded here. -/
public theorem topologicalKrullDim_stabilizerFiber_le_sourceFiberIdentity {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.objects.left) (hu : IsFiniteTypePoint u)
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left] :
    topologicalKrullDim ((stabilizer G).hom.fiber u) ≤
      topologicalKrullDimAt (G.source.left.fiber u) (sourceFiberIdentity G u) := by
  have hp : LocallyOfFiniteType (G.objects.left.fromSpecResidueField u) := hu.1
  have hs : LocallyOfFiniteType
      (GroupoidScheme.restrict G (residueChart G u)).groupoid.source.left :=
    restrictionSource_locallyOfFiniteType G (G.objects.left.fromSpecResidueField u)
  have ht : LocallyOfFiniteType
      (GroupoidScheme.restrict G (residueChart G u)).groupoid.target.left :=
    restrictionTarget_locallyOfFiniteType G (G.objects.left.fromSpecResidueField u)
  set f := targetOnSourceFiber G u with hf
  set y := f (sourceFiberIdentity G u) with hy
  -- The identity arrow, as a point of the fibre of `f` over its own image.
  let z : f.fiber y := f.asFiber (sourceFiberIdentity G u)
  let eIso := restrictedArrows_iso_sourceFiberTargetCut G u
  let e : (GroupoidScheme.restrict G (residueChart G u)).groupoid.objects.left ≅
      Spec (.of (G.objects.left.residueField u)) :=
    eqToIso (congrArg Over.left
      (GroupoidScheme.restrict G (residueChart G u)).objects_eq)
  -- Tag 04LU: the dimension of the restricted arrow scheme is its local dimension anywhere.
  have hLU := GroupoidScheme.topologicalKrullDim_arrows_eq_topologicalKrullDimAt
    (GroupoidScheme.restrict G (residueChart G u)).groupoid e (eIso.inv z)
  rw [topologicalKrullDimAt_eq_of_homeomorph eIso.hom.homeomorph] at hLU
  have hz : eIso.hom.homeomorph (eIso.inv z) = z := by
    change (eIso.inv ≫ eIso.hom) z = z
    simp
  rw [hz] at hLU
  calc topologicalKrullDim ((stabilizer G).hom.fiber u)
      = topologicalKrullDim
          (GroupoidScheme.restrict G (residueChart G u)).groupoid.arrows.left :=
        (restrictedArrows_dimension_eq_stabilizerFiber G u hu).symm
    _ = topologicalKrullDimAt (f.fiber y) z := hLU
    _ ≤ topologicalKrullDimAt (G.source.left.fiber u) (f.fiberι y z) :=
        stabDimKrullDimAt_fiber_le f y z
    _ = topologicalKrullDimAt (G.source.left.fiber u) (sourceFiberIdentity G u) := by
        rw [show f.fiberι y z = sourceFiberIdentity G u from f.fiberι_asFiber _]

end AlgebraicGeometry

end
