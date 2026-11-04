module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksCore.Tactic.StacksAttribute

/-!
# Projective amplitude of an object of the derived category

An object of the derived category `D(R)` of `R`-modules has *projective amplitude in `[a, b]`*
when it is represented by a complex of projective modules supported in degrees `a` through `b`,
and *finite projective dimension* when some finite interval works.

This is the derived-category notion. It is a companion to, and distinct from, the projective
dimension of a single object recorded by `CategoryTheory.HasProjectiveDimensionLT` and the
resolution-length characterisations in `StacksFrontier.Algebra.Homology.ProjectiveDimension`.

## Main definitions

* `StacksDraft.ProjectiveDimension.HasProjectiveAmplitude`: projective amplitude in `[a, b]`.
* `StacksDraft.ProjectiveDimension.HasFiniteProjectiveDimension`: finite projective dimension.

## Implementation notes

A representative of a derived object is expressed by an isomorphism from the image of a cochain
complex under the localization functor `Q`. Support in `[a, b]` is expressed using the strict
bounds `IsStrictlyGE`/`IsStrictlyLE` on that complex.

## References

* [Stacks Project, Tag 0A5N](https://stacks.math.columbia.edu/tag/0A5N)
-/

@[expose] public section

open CategoryTheory

namespace StacksDraft.ProjectiveDimension

universe w v u

variable {R : Type u} [Ring R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]

/-- An object of `D(R)` has **projective amplitude in `[a, b]`** if it is represented by a
complex of projective `R`-modules whose terms vanish outside degrees `a` through `b`. -/
@[stacks 0A5N "projective amplitude"]
public def HasProjectiveAmplitude
    (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ) : Prop :=
  ∃ P : CochainComplex (ModuleCat.{v} R) ℤ,
    Nonempty (DerivedCategory.Q.obj P ≅ K) ∧
      (∀ i : ℤ, Module.Projective R (P.X i)) ∧
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b

/-- An object of `D(R)` has **finite projective dimension** if it is represented by a bounded
complex of projective `R`-modules. -/
@[stacks 0A5N "finite projective dimension"]
public def HasFiniteProjectiveDimension
    (K : DerivedCategory (ModuleCat.{v} R)) : Prop :=
  ∃ a b : ℤ, HasProjectiveAmplitude K a b

end StacksDraft.ProjectiveDimension
