module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal
public import StacksCore.Tactic.StacksAttribute

/-!
# Locality of properties for a precoverage

A property of objects is local for a precoverage when it holds on an object if and only if it
holds on every member of any covering family. A property of morphisms is local on the source,
respectively on the target, when it holds for a morphism exactly when it holds after
precomposition with, respectively after pullback along, every member of any covering family of
the source, respectively of the target.

## Main definitions

* `CategoryTheory.ObjectProperty.IsLocal` expresses that an object property is local for a
  precoverage.
* `CategoryTheory.MorphismProperty.IsLocalAtSource` expresses locality on the source for a
  precoverage.
* `CategoryTheory.MorphismProperty.IsLocalAtTarget` expresses locality on the target for a
  precoverage.

## Main results

There are no results beyond the definitions.

## Implementation notes

All three notions are Mathlib's, stated for an arbitrary category and an arbitrary
precoverage. Specializing the category to schemes and the precoverage to the Zariski, fpqc,
fppf, étale, smooth, or syntomic covering families gives the six notions in each of the
sources. The component and gluing fields are the two implications of the displayed
equivalence, and the inherited `RespectsIso` field records the isomorphism invariance that the
sources require explicitly.

## References

* [Stacks Project, Tag 0348](https://stacks.math.columbia.edu/tag/0348)
* [Stacks Project, Tag 02KO](https://stacks.math.columbia.edu/tag/02KO)
* [Stacks Project, Tag 036G](https://stacks.math.columbia.edu/tag/036G)
-/

@[expose] public section

add_to_stacks 0348 CategoryTheory.ObjectProperty.IsLocal
add_to_sga "4 IV 8.2" CategoryTheory.ObjectProperty.IsLocal
add_to_sga "4½ Arcata 1.1" "more general" CategoryTheory.ObjectProperty.IsLocal

add_to_stacks 02KO CategoryTheory.MorphismProperty.IsLocalAtTarget
add_to_sga "3 IV 4.6.3" "(e_T)" CategoryTheory.MorphismProperty.IsLocalAtTarget
add_to_sga "3 VIB 2.0" "b)" CategoryTheory.MorphismProperty.IsLocalAtTarget

add_to_stacks 036G CategoryTheory.MorphismProperty.IsLocalAtSource
add_to_sga "4 IV 8.5.4" CategoryTheory.MorphismProperty.IsLocalAtSource
