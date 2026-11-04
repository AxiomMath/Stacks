module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Relations and étale equivalence relations on a scheme

Let `U` be a scheme over a base scheme `S`. A *pre-relation* on `U` is a morphism from an
`S`-scheme `R` to the product `U ⨯ U` of `S`-schemes. It induces two maps from `R` to `U`
and, on the `T`-valued points of `U` for every `S`-scheme `T`, a binary relation. A
pre-relation is a *pre-equivalence relation* when all of those binary relations are
equivalence relations, and an *étale equivalence relation* when it is an equivalence
relation in the internal sense whose two maps to `U` are étale.

## Main definitions

* `Stacks.Groupoids.PreRelation` is a pre-relation on an `S`-scheme.
* `Stacks.Groupoids.PreRelation.target` and `Stacks.Groupoids.PreRelation.source` are its
  two maps to `U`, and `Stacks.Groupoids.PreRelation.Rel` is the relation it induces on
  `T`-valued points.
* `Stacks.Groupoids.IsPreEquivalenceRelation` is the pointwise equivalence condition.
* `Stacks.Groupoids.IsEtaleEquivalenceRelation` says that a pre-relation is an étale
  equivalence relation.

## Main results

There are no propositional results.

## Implementation notes

Schemes over `S` are objects of `CategoryTheory.Over S`, whose categorical product is the
fibre product over `S`; so a pre-relation is literally a morphism to a categorical
product, and being a *relation* rather than a pre-relation is `CategoryTheory.Mono` on it.
Mathlib's `CategoryTheory.IsEquivalenceRelation`, applied to the target and source maps, is
the internal categorical form of the condition that the induced relation on every set of
`T`-valued points is an equivalence relation; the pointwise condition without monicity is
retained separately as `Stacks.Groupoids.IsPreEquivalenceRelation`.

The three conditions defining an étale equivalence relation are stored as instance fields,
so that the equivalence-relation and étaleness APIs apply to it directly.

## References

* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids

variable {S : Scheme.{u}}

/-- **Stacks 022P, part (1).** A *pre-relation* from `R` to `U` over `S` is a morphism of
`S`-schemes from `R` to the product `U ×_S U`. -/
@[stacks 022P "part (1): pre-relation"]
abbrev PreRelation (R U : Over S) := R ⟶ U ⨯ U

namespace PreRelation

variable {R U : Over S} (j : PreRelation R U)

/-- **Stacks 022P, part (1).** The *target* map of a pre-relation, its composite with the
first projection of the product. -/
@[stacks 022P "part (1): target"]
noncomputable abbrev target : R ⟶ U := j ≫ prod.fst

/-- **Stacks 022P, part (1).** The *source* map of a pre-relation, its composite with the
second projection of the product. -/
@[stacks 022P "part (1): source"]
noncomputable abbrev source : R ⟶ U := j ≫ prod.snd

/-- The relation induced by a pre-relation on the `T`-valued points of `U`: two points are
related when they are the target and the source of a common `T`-valued point of `R`. -/
abbrev Rel {T : Over S} (x y : T ⟶ U) : Prop :=
  ∃ r : T ⟶ R, r ≫ j.target = x ∧ r ≫ j.source = y

end PreRelation

/-- **Stacks 022P, part (3).** A pre-relation is a *pre-equivalence relation* when the
relation it induces on the `T`-valued points of `U` is an equivalence relation for every
scheme `T` over `S`. -/
@[stacks 022P "part (3): pre-equivalence relation", sga "3 IV 3.1" "pre-equiv. relation def"]
abbrev IsPreEquivalenceRelation {R U : Over S} (j : PreRelation R U) : Prop :=
  ∀ T : Over S, Equivalence (j.Rel (T := T))

add_to_stacks 022P "part (2): relation" CategoryTheory.Mono
add_to_stacks 022P "part (4): equivalence relation" CategoryTheory.IsEquivalenceRelation
add_to_sga "3 IV 3.1.1" CategoryTheory.IsEquivalenceRelation
add_to_sga "4 I 10.9" CategoryTheory.IsEquivalenceRelation
add_to_sga "4 IV 9.8.2" CategoryTheory.IsEquivalenceRelation

/-- **Stacks 02WS.** An equivalence relation over `S` is *étale* when its source and
target maps are étale morphisms of schemes. -/
@[stacks 02WS]
class IsEtaleEquivalenceRelation {R U : Over S} (j : PreRelation R U) : Prop where
  /-- The source and target maps form an equivalence relation. -/
  [isEquivalenceRelation : IsEquivalenceRelation j.target j.source]
  /-- The source map is étale. -/
  [etale_source : Etale j.source.left]
  /-- The target map is étale. -/
  [etale_target : Etale j.target.left]

attribute [instance] IsEtaleEquivalenceRelation.isEquivalenceRelation
  IsEtaleEquivalenceRelation.etale_source IsEtaleEquivalenceRelation.etale_target

end Stacks.Groupoids

end
