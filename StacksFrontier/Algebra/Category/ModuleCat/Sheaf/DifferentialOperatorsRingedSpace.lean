module

public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialOperatorsOrder
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialOperators
import StacksCore.Tactic.StacksAttribute

/-!
# Differential operators on a ringed space

Section 17.29 of the Stacks project discusses differential operators on a ringed space. The
two statements recorded here — that differential operators are closed under composition with
their orders adding (Tag 0G3R), and that the differential operators of order at most `k` out
of a fixed sheaf of modules are corepresented by the sheaf of principal parts (Tag 0G3S) —
are the ringed-space specializations of the corresponding statements for sheaves of modules
on an arbitrary site, Tags 09CS and 09CT. Since the site of opens of a topological space is
such a site, nothing has to be proved again: this file only records the two tags on the
general declarations.

## Main results

* `DiffOp.isGlobalDiffOpOfOrder_comp` (Tag 09CS) also realizes Tag 0G3R.
* `AlgebraicGeometry.SheafOfModules.differentialOperatorsFunctor_isCorepresentable`
  (Tag 09CT) also realizes Tag 0G3S.

## Implementation notes

Both declarations live in the site-theoretic development and are stated for an arbitrary
Grothendieck topology `J` on an arbitrary category `C`. Specializing `C` to `Opens X` and `J`
to `Opens.grothendieckTopology X` gives exactly the ringed-space statements of Section 17.29,
so these tags are added to the existing declarations rather than to restricted copies.

## References

* [Stacks Project, Tag 0G3R](https://stacks.math.columbia.edu/tag/0G3R)
* [Stacks Project, Tag 0G3S](https://stacks.math.columbia.edu/tag/0G3S)
-/

@[expose] public section

add_to_stacks 0G3R "the ringed-space case of 09CS" DiffOp.isGlobalDiffOpOfOrder_comp

add_to_stacks 0G3S "the ringed-space case of 09CT"
  AlgebraicGeometry.SheafOfModules.differentialOperatorsFunctor_isCorepresentable

end
