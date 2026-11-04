module

public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# Finite covering families whose iterated fibre products stay in a collection of objects

Stacks 0739 compares filtered colimits with cohomology over an object of a site, under the
hypothesis that the object admits a cofinal collection of covering families which are finite
and whose iterated fibre products again belong to a prescribed collection `B` of objects of the
site. This file isolates that hypothesis as a predicate on a covering family.

## Main definitions

* `Stacks.Cohomology.HasIntersectionsIn`: a covering family is finite, and its target, its
  members and all of its nonempty iterated fibre products lie in a given collection of objects.

## Implementation notes

A covering family `{Xᵢ ⟶ U}` is a `CategoryTheory.PreZeroHypercover`. An iterated fibre product
of the members along a finite list of indices is expressed invariantly, as the vertex of a
limiting wide-pullback cone over the chosen members, rather than through a choice of pullbacks:
the site is not assumed to have fibre products, so the condition is that such a limit exists
*and* that its vertex lies in `B`. Lists of indices are indexed by `Fin (n + 1)`, which is the
nonemptiness restriction of the source — the empty intersection would be the covered object `U`,
whose membership is recorded separately.

## References

* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.Cohomology

/-- A finite family `{Xᵢ ⟶ U}` whose target, whose members, and every nonempty iterated fibre
product of whose members over `U` lie in `B`. -/
public def HasIntersectionsIn {C : Type u} [Category.{v} C] (B : Set C) {U : C}
    (E : PreZeroHypercover.{w} U) : Prop :=
  Finite E.I₀ ∧ B U ∧ (∀ i, B (E.X i)) ∧
    ∀ (n : ℕ) (a : Fin (n + 1) → E.I₀),
      ∃ t : WidePullbackCone (fun i ↦ E.f (a i)), Nonempty (IsLimit t) ∧ B t.pt

end Stacks.Cohomology

end
