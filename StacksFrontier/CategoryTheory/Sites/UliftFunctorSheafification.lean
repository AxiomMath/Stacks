module

public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The universe lift of sheaves of sets preserves sheafification

The pointwise universe lift `CategoryTheory.uliftFunctor` from `Type max u v` to a larger
`Type max u v w` carries sheaves on a site `C : Type u` with `Category.{v} C` to sheaves and
commutes with sheafification.

## Main results

* `CategoryTheory.GrothendieckTopology.hasSheafCompose_uliftFunctor`: the universe lift carries
  sheaves of sets to sheaves of sets.
* `CategoryTheory.GrothendieckTopology.preservesSheafification_uliftFunctor`: the universe lift
  commutes with sheafification.

## Implementation notes

Both facts are consequences of Mathlib's instances for a functor between concrete categories with
the appropriate limits and colimits, but deriving them is a long instance search: with the
instances of a large development in scope it exhausts the `synthInstance` heartbeats. This module
imports only the two Mathlib files they need and records the results as instances, so that every
later use is a single instance step.

The statement is made for an arbitrary site, so that it serves both for a site and for its
localizations: the objects of `CategoryTheory.Over V` for `V : C` form a `Type (max u v)` with
`Category.{v}`, and the instance at that site is this one with `u := max u v`, its two set
universes `max (max u v) v = max u v` and `max (max u v) v w = max u v w` being the same two.

The lift is written `uliftFunctor.{w, max u v}`, parametrized by the level the universe is raised
*by* rather than by the universe it is raised *to*. That is forced: an instance whose statement
names the target universe `max u v s` can never be matched, Lean having no solution for the
universe constraint `max u v ?s =?= max u v s`, whereas the level `w` of the lift is determined
by the functor in the goal.
-/

@[expose] public section

open CategoryTheory Limits

universe w v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type max u v)] [HasWeakSheafify J (Type max u v w)]

/-- The pointwise universe lift carries sheaves of sets to sheaves of sets. -/
public instance hasSheafCompose_uliftFunctor :
    J.HasSheafCompose uliftFunctor.{w, max u v} :=
  inferInstance

/-- The pointwise universe lift of sheaves of sets commutes with sheafification. -/
public instance preservesSheafification_uliftFunctor :
    J.PreservesSheafification uliftFunctor.{w, max u v} :=
  inferInstance

end CategoryTheory.GrothendieckTopology

end
