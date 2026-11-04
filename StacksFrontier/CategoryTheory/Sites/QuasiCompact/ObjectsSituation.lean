module

public import StacksFrontier.CategoryTheory.Sites.QuasiCompact
import StacksCore.Tactic.StacksAttribute

/-!
# Sites with a distinguished family of quasi-compact objects

The discussion of presentations of sheaves of modules in the Stacks Project runs under a
standing hypothesis on the site: one fixes a collection of objects which covers the site, whose
members are quasi-compact, and for which the pairwise fibre products occurring in a cover by
members of the collection are again quasi-compact. This file records that situation and its
three conditions.

## Main definitions

* `Stacks.Sites.QuasiCompactObjectsSituation`: a Grothendieck topology on a category together
  with a distinguished collection of objects of that category.
* `Stacks.Sites.QuasiCompactObjectsSituation.HasEnoughObjects`: condition (1), that the
  distinguished objects cover every object of the site.
* `Stacks.Sites.QuasiCompactObjectsSituation.ObjectsAreQuasiCompact`: condition (2), that every
  distinguished object is quasi-compact.
* `Stacks.Sites.QuasiCompactObjectsSituation.CoverPullbacksAreQuasiCompact`: condition (3), that
  the pairwise fibre products in a cover of a distinguished object by distinguished objects
  exist and are quasi-compact.

## Implementation notes

A site is a category with a Grothendieck topology, and a covering family of an object `U` is a
`PreZeroHypercover` over `U` whose generated sieve lies in the topology. A Grothendieck topology
does not provide fibre products, so condition (3) asserts their existence as well as their
quasi-compactness; the quasi-compactness conjunct is quantified over the `HasPullback` instance
used to choose the pullback, so that the condition does not depend on a global choice.

## References

* [Stacks Project, Tag 0937](https://stacks.math.columbia.edu/tag/0937)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.Sites

/-- A site together with a distinguished collection of its objects. This is the standing data
of the Stacks Project's discussion of presentations of sheaves of modules. -/
@[stacks 0937 "the standing data"]
structure QuasiCompactObjectsSituation (C : Type u) [Category.{v} C] where
  /-- The Grothendieck topology defining the site. -/
  topology : GrothendieckTopology C
  /-- The distinguished collection of objects. -/
  objects : Set C

namespace QuasiCompactObjectsSituation

variable {C : Type u} [Category.{v} C]

/-- Condition (1): every object of the site has a covering family all of whose members belong
to the distinguished collection. -/
@[stacks 0937 "condition (1)"]
def HasEnoughObjects (S : QuasiCompactObjectsSituation C) : Prop :=
  ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U,
    𝒰.sieve₀ ∈ S.topology U ∧ ∀ i, 𝒰.X i ∈ S.objects

/-- Condition (2): every object of the distinguished collection is quasi-compact. -/
@[stacks 0937 "condition (2)"]
def ObjectsAreQuasiCompact (S : QuasiCompactObjectsSituation C) : Prop :=
  ∀ U : C, U ∈ S.objects → S.topology.IsQuasiCompactObject U

/-- Condition (3): for a covering family of a distinguished object whose members are
distinguished, every pairwise fibre product exists and is quasi-compact. -/
@[stacks 0937 "condition (3)"]
def CoverPullbacksAreQuasiCompact (S : QuasiCompactObjectsSituation C) : Prop :=
  ∀ (U : C) (𝒰 : PreZeroHypercover.{max u v} U),
    𝒰.sieve₀ ∈ S.topology U →
      U ∈ S.objects →
      (∀ i, 𝒰.X i ∈ S.objects) →
      ∀ i j,
        HasPullback (𝒰.f i) (𝒰.f j) ∧
          ∀ [HasPullback (𝒰.f i) (𝒰.f j)],
            S.topology.IsQuasiCompactObject (pullback (𝒰.f i) (𝒰.f j))

end QuasiCompactObjectsSituation

end Stacks.Sites

end
