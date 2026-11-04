module

public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings

/-!
# The index universe of a covering family of algebraic spaces

A covering family of algebraic spaces over `S` for one of the five topologies of **Stacks
03YH** is indexed by a type `I : Type v`, and the universe `v` is independent of the universe
`u` of the site: it occurs in `AlgebraicGeometry.Space.Topology.precoverage` only inside the
existential quantifier that produces the index type. This module records that the resulting
precoverage grows as that universe grows, so that a property of morphisms of algebraic spaces
known to be local at the target for coverings indexed in a large universe is local at the
target for coverings indexed in a small one.

The content is a reindexing: a covering family stays a covering family when composed with a
surjection of index types, because each of the five conditions is either a condition on every
member of the family or the joint surjectivity of the maps on points, and both are unchanged
by precomposition with a surjection. Taking the surjection to be `ULift.down` turns a family
indexed by `I : Type v` into one indexed by `ULift.{w} I : Type (max v w)` spanning the same
presieve, which is the inequality below.

## Main results

* `AlgebraicGeometry.Space.Topology.IsCovering.comp_of_surjective`: a covering family composed
  with a surjection of index types is a covering family.
* `AlgebraicGeometry.Space.Topology.precoverage_le_precoverage_max`: the precoverage of
  **Stacks 03YH** at index universe `v` is contained in the one at index universe
  `max v w`.

## Implementation notes

The inequality is stated between the index universes `v` and `max v w` rather than between two
unrelated universes, and that is the strongest form available: membership in
`AlgebraicGeometry.Space.Topology.precoverage` asks for the presieve to be *equal* to
`CategoryTheory.Presieve.ofArrows` of a family indexed in the given universe, and a family
indexed by a type of `Type v` can be reindexed by a type of `Type v'` only when `Type v'`
contains a type surjecting onto it, which `ULift` provides exactly when `v'` is at least `v`.
No refinement of the covering family is permitted, since the order on
`CategoryTheory.Precoverage` compares the sets of covering presieves directly.

Combined with `CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le`, this transfers locality
at the target downwards along the index universe. The locality hypothesis must be written with
its universe arguments supplied, as instance synthesis does not see through a missing universe
annotation even when the two spellings print alike.

## References

* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v v' w

/-- A `τ`-covering family of algebraic spaces over `S` composed with a surjection `a` of index
types is again a `τ`-covering family: every condition imposed on the members of the family is
inherited by a subfamily, and the union of the images of the maps on points is unchanged by
precomposition with a surjection. -/
theorem Topology.IsCovering.comp_of_surjective {τ : Topology} {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} {I : Type v} {J : Type v'}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Yi : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g : ∀ i, Yi i ⟶ Y} (hg : τ.IsCovering B S hS Yi g) {a : J → I}
    (ha : Function.Surjective a) :
    τ.IsCovering B S hS (fun j => Yi (a j)) (fun j => g (a j)) := by
  obtain ⟨hY, hYi, hτ⟩ := hg
  refine ⟨hY, fun j => hYi (a j), ?_⟩
  cases τ with
  | fpqc => exact isFpqcCovering_reindex B S hS hτ ha
  | fppf => exact hτ.reindex B S hS ha
  | syntomic => exact hτ.reindex B S hS ha
  | smooth => exact hτ.reindex B S hS ha
  | etale => exact hτ.reindex B S hS ha

/-- **Stacks 03YH** is monotone in the index universe of its covering families: a presieve
that is a `τ`-covering indexed by a type of `Type v` is also a `τ`-covering indexed by a type
of `Type (max v w)`, namely by the `ULift` of the original index type. Together with
`CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le` this carries locality at the target
from the larger index universe to the smaller one. -/
theorem Topology.precoverage_le_precoverage_max (τ : Topology) (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    τ.precoverage.{u, v} B S hS ≤ τ.precoverage.{u, max v w} B S hS := by
  intro Y R hR
  obtain ⟨I, Yi, g, rfl, hg⟩ := hR
  refine ⟨ULift.{w} I, fun j => Yi j.down, fun j => g j.down, ?_, ?_⟩
  · exact (Presieve.ofArrows_comp_eq_of_surjective g ULift.down_surjective).symm
  · exact hg.comp_of_surjective ULift.down_surjective

end AlgebraicGeometry.Space

end
