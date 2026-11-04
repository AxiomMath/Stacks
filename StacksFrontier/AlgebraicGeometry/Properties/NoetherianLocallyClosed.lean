module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute

/-!
# Locally closed subschemes of (locally) Noetherian schemes

A locally closed subscheme of a scheme `X` is the source of an immersion `f : Z ⟶ X`, that is,
of a closed immersion into an open subscheme of `X`. Such a subscheme inherits both
Noetherianity and local Noetherianity from `X`.

## Main results

* `AlgebraicGeometry.isLocallyNoetherian_of_isImmersion`: the source of an immersion into a
  locally Noetherian scheme is locally Noetherian.
* `AlgebraicGeometry.isNoetherian_of_isImmersion`: the source of an immersion into a Noetherian
  scheme is Noetherian.

## Implementation notes

An immersion is locally of finite type, so the local statement is the finite-type statement
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`; concretely this is the Stacks hint
that a quotient and a localization of a Noetherian ring are Noetherian.

For the global statement only quasi-compactness of `Z` is left to prove, `IsNoetherian` being
`IsLocallyNoetherian` together with `CompactSpace`. The underlying space of a Noetherian scheme
is a Noetherian topological space, an immersion is in particular a topological embedding, and
a space induced from a Noetherian space is Noetherian, hence compact. This is the Stacks hint
that a subset of a Noetherian space is a Noetherian space in the induced topology.

Neither statement is an instance: the target `X` is not determined by the source `Z`, so
instance search could not use them.

## References

* [Stacks Project, Tag 02IK](https://stacks.math.columbia.edu/tag/02IK)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {Z X : Scheme.{u}} (f : Z ⟶ X)

/-- A locally closed subscheme of a locally Noetherian scheme is locally Noetherian: the source
of an immersion into a locally Noetherian scheme is locally Noetherian. -/
@[stacks 02IK "the locally Noetherian case, for the source of an arbitrary immersion",
  ega "I 6.1.4"]
theorem isLocallyNoetherian_of_isImmersion [IsImmersion f] [IsLocallyNoetherian X] :
    IsLocallyNoetherian Z :=
  LocallyOfFiniteType.isLocallyNoetherian f

/-- The underlying space of the source of an immersion into a Noetherian scheme is a Noetherian
topological space. -/
@[ega "I 6.1.2" "more general"]
theorem noetherianSpace_of_isImmersion [IsImmersion f] [IsNoetherian X] :
    NoetherianSpace Z :=
  f.isEmbedding.isInducing.noetherianSpace

/-- A locally closed subscheme of a Noetherian scheme is Noetherian: the source of an immersion
into a Noetherian scheme is Noetherian. -/
@[stacks 02IK "the Noetherian case, for the source of an arbitrary immersion", ega "I 6.1.4"]
theorem isNoetherian_of_isImmersion [IsImmersion f] [IsNoetherian X] : IsNoetherian Z :=
  have : IsLocallyNoetherian Z := isLocallyNoetherian_of_isImmersion f
  have : NoetherianSpace Z := noetherianSpace_of_isImmersion f
  ⟨⟩

end AlgebraicGeometry

end
