module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Injective amplitude and injective dimension in a derived category

An object of the derived category of an abelian category has *injective amplitude in `[a, b]`*
when it is represented by a complex of injective objects supported in degrees `a` through `b`,
and *finite injective dimension* when some finite interval works.

## Main definitions

* `StacksDraft.InjectiveDimension.HasInjectiveAmplitude`: injective amplitude in `[a, b]`.
* `StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension`: finite injective dimension.

## Implementation notes

The definitions are stated for an arbitrary abelian category, so they apply in particular to the
derived category of modules over a ring. The strict bounds `IsStrictlyGE`/`IsStrictlyLE` express
that the representing complex vanishes outside the specified interval.

## References

* [Stacks Project, Tag 0A5S](https://stacks.math.columbia.edu/tag/0A5S)
-/

@[expose] public section

open CategoryTheory

namespace StacksDraft.InjectiveDimension

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- An object of a derived category has *injective amplitude in `[a, b]`* if it is isomorphic
to the image of a cochain complex which vanishes below `a` and above `b` and whose terms are
injective. -/
@[stacks 0A5S "injective amplitude", sga "6 I 5.7" "(i) definition"]
public def HasInjectiveAmplitude (K : DerivedCategory C) (a b : ℤ) : Prop :=
  ∃ (I : CochainComplex C ℤ) (_ : I.IsStrictlyGE a) (_ : I.IsStrictlyLE b),
    (∀ i : ℤ, Injective (I.X i)) ∧ Nonempty (K ≅ DerivedCategory.Q.obj I)

/-- An object of a derived category has *finite injective dimension* if it has injective
amplitude in some finite integer interval. -/
@[stacks 0A5S "finite injective dimension"]
public def HasFiniteInjectiveDimension (K : DerivedCategory C) : Prop :=
  ∃ a b : ℤ, HasInjectiveAmplitude K a b

end StacksDraft.InjectiveDimension
