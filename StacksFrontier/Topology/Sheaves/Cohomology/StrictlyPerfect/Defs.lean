module

public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.FiniteFreeSummands
import StacksCore.Tactic.StacksAttribute

/-!
# Strictly perfect complexes of modules on a ringed space

A complex of `O_X`-modules on a ringed space `X` is *strictly perfect* when it has only
finitely many nonzero terms and every term is a direct summand of a finite free
`O_X`-module. This is Stacks 08C4.

Both halves of that condition are already developed in `StacksDraft.Ch20.Sec46.Tag08C5`,
where they are the hypotheses of the lemma that a cone of a morphism of strictly perfect
complexes is strictly perfect: `StrictlyPerfect.IsDirectSummandOfFiniteFree` is the retract
condition on a single module and `StrictlyPerfect.IsStrictlyPerfect` is the conjunction of
boundedness with that condition in every degree. This file registers the tag against that
predicate rather than introducing a second copy of it, so that the closure properties
already proved there apply to the tagged notion.

## Main definitions

* `StrictlyPerfect.IsStrictlyPerfect` (in `Tag08C5`): a complex of `O_X`-modules is
  bounded and each of its terms is a direct summand of a finite free module.

## Implementation notes

The retract condition is stated through `StrictlyPerfect.moduleULift` so that the module and
the finite free module it is a summand of may have sections in different universes; when the
module and ring universes agree it is equivalent to an ordinary retract, which is the content
of `StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract`. Keeping the universes
independent is why the predicate is not simply `Retract` in the category of sheaves of
modules.

## References

* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
-/

@[expose] public section

add_to_stacks 08C4 StrictlyPerfect.IsStrictlyPerfect
