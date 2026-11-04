module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.UniversallyCatenaryDimension
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.FirstLocalCohomologyKollar
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.KollarCriterionAssembled

/-!
# Kollár's criterion and its two consequences, collected

[Stacks, Tag 0BK3] (Kollár's criterion) is proved in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.KollarCriterionAssembled`, as
`Stacks.LocalCohomology.isCoherent_pushforward_iff_forall_two_le_ringKrullDim`. The two statements
that consume it — [Stacks, Tag 0BL9] and [Stacks, Tag 0AWB] — are proved each in its own module,
[Stacks, Tag 0AWB] as
`AlgebraicGeometry.isCoherent_pushforward_iff_two_le_ringKrullDim_stalk_pointClosure` and
[Stacks, Tag 0BL9] as
`Stacks.LocalCohomology.finite_localCohomologyModule_one_iff_forall_ringKrullDim_ne_one`. This
module imports all three, so that the forms of the criterion can be read off together; the two
consequences are kept here only as aliases of the declarations that prove and register them.

## Main results

* `Stacks.LocalCohomology.finite_localCohomologyModule_one_iff_forall_ringKrullDim_ne_one'`:
  alias of the [Stacks, Tag 0BL9] declaration.
* `AlgebraicGeometry.isCoherent_pushforward_iff_two_le_ringKrullDim_stalk_pointClosure'`:
  alias of the [Stacks, Tag 0AWB] declaration.

## References

* [Stacks Project, Tag 0BK3](https://stacks.math.columbia.edu/tag/0BK3)
* [Stacks Project, Tag 0BL9](https://stacks.math.columbia.edu/tag/0BL9)
* [Stacks Project, Tag 0AWB](https://stacks.math.columbia.edu/tag/0AWB)
* [Stacks Project, Tag 0BK1](https://stacks.math.columbia.edu/tag/0BK1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open scoped TensorProduct

namespace Stacks.LocalCohomology

/-- The statement of [Stacks, Tag 0BL9], proved and registered as
`Stacks.LocalCohomology.finite_localCohomologyModule_one_iff_forall_ringKrullDim_ne_one`. -/
alias finite_localCohomologyModule_one_iff_forall_ringKrullDim_ne_one' :=
  Stacks.LocalCohomology.finite_localCohomologyModule_one_iff_forall_ringKrullDim_ne_one

end Stacks.LocalCohomology

namespace AlgebraicGeometry

/-- The statement of [Stacks, Tag 0AWB], proved and registered as
`AlgebraicGeometry.isCoherent_pushforward_iff_two_le_ringKrullDim_stalk_pointClosure`. -/
alias isCoherent_pushforward_iff_two_le_ringKrullDim_stalk_pointClosure' :=
  AlgebraicGeometry.isCoherent_pushforward_iff_two_le_ringKrullDim_stalk_pointClosure

end AlgebraicGeometry

end
