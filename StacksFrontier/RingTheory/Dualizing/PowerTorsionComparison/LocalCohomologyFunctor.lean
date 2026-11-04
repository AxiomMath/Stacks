module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.Algebra.Module.Shrink
public import StacksFrontier.RingTheory.Dualizing.DerivedTorsion
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Basic
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.RightAdjoint
public import StacksFrontier.RingTheory.LocalCohomology.BaseChange.Coreflection

/-!
# Local cohomology with support in a closed subset

Let `I` be a finitely generated ideal of a commutative ring `A` and let `Z = V(I)` be the
corresponding closed subset of `Spec(A)`. The full subcategory
`D_{I^∞-torsion}(A) ⊆ D(A)` of objects all of whose cohomology modules are `I`-power torsion
is a coreflective subcategory: the inclusion has a right adjoint, and that right adjoint is
local cohomology `RΓ_Z`.

The construction is the one of the Stacks project. Choose generators `f₁, …, f_r` of `I`. An
object `K` of `D(A)` has `I`-power-torsion cohomology exactly when every localization
`K[1/f_i]` vanishes, because a module over a ring is `I`-power torsion precisely when it is
killed by inverting each generator of `I`. For a single `f` the fibre of the unit
`K → K[1/f]` is the universal object of `D(A)` with vanishing `f`-localization mapping to `K`;
iterating over the finitely many generators produces the universal object with all
localizations vanishing, which is the value of the right adjoint.

## Main results

The existence of the right adjoint is `Dualizing.localCohomologyRightAdjoint_nonempty`, the
chosen right adjoint is `Dualizing.localCohomologyRightAdjoint`, the adjunction is
`Dualizing.localCohomologyAdjunction` and local cohomology `RΓ_Z` itself is
`Dualizing.localCohomologyFunctor`; all of them live in
`StacksFrontier/RingTheory/Dualizing/LocalCohomology/`, which this module imports.

The exact endofunctor of `ModuleCat.{v} A` inverting a submonoid, and the characterisation of
`I`-power torsion by the vanishing of those localizations, are
`Dualizing.smallLocalizationFunctor` and
`Dualizing.derivedPowerTorsionProperty_iff_isZero_mapDerivedCategory` of
`StacksFrontier/RingTheory/Dualizing/TorsionComplete/SmallLocalization.lean`, imported through
the module above.

## Implementation notes

This module declares nothing of its own: it only gathers the modules above, which carry the
construction and the localization API under their canonical names. The modules downstream of
this one, `LocalCohomology/Composition.lean` and
`TorsionComplete/CompletionAfterLocalCohomology.lean`, use those names directly.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
-/
