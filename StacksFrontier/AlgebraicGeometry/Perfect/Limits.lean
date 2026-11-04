module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent along a directed inverse system of schemes

A directed inverse system of quasi-compact and quasi-separated schemes with affine transition
morphisms, together with a chosen limit and a chosen index, is the standing situation for
descent along such a system.

## Main definitions

* `AlgebraicGeometry.DescentSituation` is the standing situation for descent along a directed
  inverse system of schemes with affine transition morphisms.

## Implementation notes

The inverse system is represented by a functor from the opposite of the directed preorder. Its
chosen limiting scheme, projections, and their naturality are bundled as a limit cone.

## References

* [Stacks Project, Tag 09RD](https://stacks.math.columbia.edu/tag/09RD)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits in
/-- A directed inverse system of quasi-compact and quasi-separated schemes whose transition
morphisms are affine, equipped with a chosen limit cone and a chosen index. -/
@[stacks 09RD, sga "6 IV 3.2"]
structure AlgebraicGeometry.DescentSituation (I : Type v) [Preorder I]
    [IsDirected I (· ≤ ·)] where
  /-- The inverse system of schemes. -/
  system : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{u}
  /-- Every transition morphism in the inverse system is affine. -/
  transition_affine : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), AlgebraicGeometry.IsAffineHom (system.map f)
  /-- Every scheme in the inverse system is quasi-compact. -/
  quasiCompact : ∀ i : I, CompactSpace (system.obj (Opposite.op i))
  /-- Every scheme in the inverse system is quasi-separated. -/
  quasiSeparated : ∀ i : I, QuasiSeparatedSpace (system.obj (Opposite.op i))
  /-- The chosen cone exhibiting the limiting scheme and its projections. -/
  limitCone : Cone system
  /-- The chosen cone is limiting. -/
  isLimit : IsLimit limitCone
  /-- The fixed index of the system. -/
  base : I
