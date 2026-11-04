module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Syntomic coverings

A syntomic covering of a scheme is a family of syntomic morphisms into it whose images cover
it. A *standard* syntomic covering is the affine, finite case: finitely many standard syntomic
morphisms between affine schemes, jointly surjective.

These are the covering families of the syntomic topology, in the same way that jointly
surjective families of étale morphisms are the covering families of the étale topology.

## Main definitions

* `AlgebraicGeometry.IsSyntomicCovering` — a family of morphisms is componentwise syntomic and
  jointly surjective.
* `AlgebraicGeometry.IsStandardSyntomicCovering` — a family is finite, has affine source and
  target schemes, is componentwise standard syntomic, and is jointly surjective.

## Implementation notes

Joint surjectivity is expressed by the union of the set-theoretic ranges of the underlying
continuous maps being everything, rather than through a precoverage, so that the predicate can
be stated before any topology is available.

`IsSyntomicCovering` is an abbreviation, so clients can use the API for conjunctions,
universal quantification and set-theoretic unions on it directly.

For `IsStandardSyntomicCovering` the finiteness and affineness conditions are fields rather
than prerequisites for forming the predicate, so that it can be stated for an arbitrary family;
clients may install those fields as local instances in order to use the componentwise
standard-syntomic condition.

## References

* [Stacks Project, Tag 0225](https://stacks.math.columbia.edu/tag/0225)
* [Stacks Project, Tag 0229](https://stacks.math.columbia.edu/tag/0229)
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- A family `fᵢ : Tᵢ ⟶ T` is a **syntomic covering** if every `fᵢ` is
syntomic and their images cover `T`. -/
@[stacks 0225] public abbrev IsSyntomicCovering {T : AlgebraicGeometry.Scheme.{u}}
    {I : Type v} (X : I → AlgebraicGeometry.Scheme.{u}) (f : ∀ i, X i ⟶ T) : Prop :=
  (∀ i, Syntomic (f i)) ∧ (⋃ i, Set.range (f i)) = Set.univ

/-- A family `fᵢ : Uᵢ ⟶ T` is a **standard syntomic covering** if its
indexing type is finite, its source and target schemes are affine, every `fᵢ`
is standard syntomic, and their images cover `T`. -/
@[stacks 0229] public structure IsStandardSyntomicCovering {T : Scheme.{u}} {I : Type v}
    (U : I → Scheme.{u}) (f : ∀ i, U i ⟶ T) : Prop where
  /-- The family has finitely many members. -/
  finite_index : Finite I
  /-- The target of the covering is affine. -/
  affine_target : IsAffine T
  /-- Every member of the covering is affine. -/
  affine_source : ∀ i, IsAffine (U i)
  /-- Every morphism in the family is standard syntomic. -/
  standard_syntomic : ∀ i, @IsStandardSyntomic (U i) T (affine_source i) affine_target (f i)
  /-- The images of the morphisms cover the target. -/
  jointly_surjective : (⋃ i, Set.range (f i)) = Set.univ

end AlgebraicGeometry
