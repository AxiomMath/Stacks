module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.CanonicalDatum

/-!
# Descending types of morphisms

A property of morphisms of schemes over a base satisfies descent for a type of coverings when
every descent datum whose component morphisms have the property is effective.

## Main definitions

* `AlgebraicGeometry.SatisfiesDescent` expresses effective descent of morphisms with a given
  property along all covering families of a precoverage.

## Implementation notes

The type of coverings is represented by a precoverage on schemes. This covers the Zariski,
fpqc, fppf, étale and smooth cases of the source at once, through Mathlib's
`AlgebraicGeometry.Scheme.zariskiPrecoverage`, `AlgebraicGeometry.Scheme.fpqcPrecoverage`,
`AlgebraicGeometry.Scheme.fppfPrecoverage` and `AlgebraicGeometry.Scheme.etalePrecoverage`, and
the syntomic case through `AlgebraicGeometry.Scheme.precoverage` of
`AlgebraicGeometry.Syntomic`.

The property is tested on the structure morphism of each component of the descent datum. The
definition is an abbreviation, so a client gets the quantifier and implication API directly,
and the index type lives in a universe independent of the universe of schemes.

## References

* [Stacks Project, Tag 02W2](https://stacks.math.columbia.edu/tag/02W2)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 02W2.** Morphisms with property `P` satisfy descent for the coverings
of a precoverage `K` if every descent datum relative to a `K`-covering whose components are
`P`-morphisms is effective. -/
@[stacks 02W2]
abbrev SatisfiesDescent (P : MorphismProperty Scheme.{u}) (K : Precoverage Scheme.{u}) : Prop :=
  ∀ {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S),
    Presieve.ofArrows X f ∈ K S → ∀ D : DescentData f,
      (∀ i, P (D.obj i).hom) → D.IsFamilyEffective

end AlgebraicGeometry

end
