module

public import StacksFrontier.AlgebraicGeometry.Stacks.DenseTestValuativeSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.RefinedValuativeCriterion

/-!
# Comparing the two encodings of the hypothesis of Stacks 0E95

The hypothesis of **Stacks 0E95** — for every discrete valuative test diagram whose generic point
factors through `h`, the category of dotted arrows is empty or a setoid with exactly one
isomorphism class — is carried by two predicates in this development, differing in the shape of
the test diagram they quantify over:

* `AlgebraicGeometry.Stack.ValuativeCriterion.DiscreteUniquenessAlong` quantifies over
  `AlgebraicGeometry.Stack.ValuativeDiagram`, whose two points are carried by *arbitrary* objects
  of the site whose underlying schemes are isomorphic to the spectra of a valuation ring and of
  its canonical fraction field;
* `AlgebraicGeometry.Stack.ValuativeCriterion.DenseTestUniqueness` quantifies over
  `AlgebraicGeometry.Stack.ValuativeSquare`, whose two points are carried by the *canonical*
  objects `AlgebraicGeometry.Stack.siteObject` built from a chosen base morphism, for an arbitrary
  fraction field, and whose factorization through `h` is an existential hypothesis rather than a
  universally quantified datum.

This file records the comparison: a square is a diagram
(`AlgebraicGeometry.Stack.ValuativeSquare.toValuativeDiagram`), so the diagram-indexed predicate
implies the square-indexed one.

## Main results

* `AlgebraicGeometry.Stack.ValuativeCriterion.denseTestUniqueness_of_discreteUniquenessAlong`:
  `DiscreteUniquenessAlong` implies `DenseTestUniqueness`, so a 1-morphism satisfying the
  diagram-indexed hypothesis is separated by Stacks 0E95.

## Implementation notes

Only this implication is available. The converse would ask for a valuative square built from a
valuative diagram, and a diagram carries strictly less data than a square: it has no membership
witness `B.Contains (Spec R)` for the spectrum of its valuation ring, none for the spectrum of the
fraction field, and no base morphism `Spec R ⟶ S`; and even granting those three, its generic and
special points live over `AlgebraicGeometry.Stack.schemeFibredCategory` of the site objects
`generic` and `whole`, which are only isomorphic *as schemes* to the canonical spectra, with no
compatibility with the structure morphism to `S`. Turning a diagram into a square therefore means
transporting the whole category of dotted arrows along an equivalence of categories fibred in
groupoids, and both halves of the conclusion along that equivalence.

## References

* [Stacks Project, Tag 0E95](https://stacks.math.columbia.edu/tag/0E95)
* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 0CLG](https://stacks.math.columbia.edu/tag/0CLG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack.ValuativeCriterion

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **The diagram-indexed form of the hypothesis of Stacks 0E95 implies the square-indexed
form.** A valuative square is a valuative diagram with the same valuation ring, the same generic
point, the same special point and the same filler
(`AlgebraicGeometry.Stack.ValuativeSquare.toValuativeDiagram`), and the two conclusions are the
same statement about the same category of dotted arrows.

Composed with `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_denseTestUniqueness`, this
gives Stacks 0E95 for a 1-morphism whose valuative hypothesis is phrased over diagrams. -/
theorem denseTestUniqueness_of_discreteUniquenessAlong {h : 𝒰 ⟶ 𝒳} {f : 𝒳 ⟶ 𝒴}
    (hb : DiscreteUniquenessAlong B S hS h f) :
    DenseTestUniqueness B S hS h f := by
  rintro q hq ⟨u, hu⟩
  exact hb (ValuativeSquare.toValuativeDiagram B S hS q) hq u hu

end AlgebraicGeometry.Stack.ValuativeCriterion

end
