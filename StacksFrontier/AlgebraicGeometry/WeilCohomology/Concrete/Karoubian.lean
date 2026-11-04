module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Motives
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiIdempotentComplete
public import StacksCore.Tactic.StacksAttribute

/-!
# The category `M_k` of Chow motives is Karoubian

Stacks 0FGB: the category `M_k` of Chow motives over `k` is Karoubian, that is (Homology,
Definition 09SG) every idempotent endomorphism of a motive has a kernel.

The source's argument: for a projector `a` of `M = (X, p, m)`, the motive `N = (X, a, m)` is a
kernel of `1 - a`. That is the splitting `(X, a, m) ⟶ (X, p, m) ⟶ (X, a, m)` of
`CategoryTheory.GradedCategory.TwistedKaroubi.instIsIdempotentComplete`, `M_k` being the twisted
Karoubi envelope `Stacks.WeilCohomology.ChowMotiveCat k` of the graded category of
correspondences; Mathlib's `isIdempotentComplete_iff_idempotents_have_kernels` turns the
splitting of every idempotent into the existence of the kernels.

## Main results

* `Stacks.WeilCohomology.ChowMotiveCat.hasKernel_of_idem`: **Stacks 0FGB**, every idempotent
  endomorphism in `M_k` has a kernel.

## References

* [Stacks Project, Tag 0FGB](https://stacks.math.columbia.edu/tag/0FGB)
* [Stacks Project, Tag 09SG](https://stacks.math.columbia.edu/tag/09SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

universe u

namespace Stacks.WeilCohomology.ChowMotiveCat

variable {k : Type u} [Field k]

/-- **Stacks Project, Tag 0FGB.** The category `M_k` of Chow motives is Karoubian in the sense of
Homology, Definition 09SG: every idempotent endomorphism `a` of a motive `M` has a kernel. -/
@[stacks 0FGB]
theorem hasKernel_of_idem (M : ChowMotiveCat k) (a : M ⟶ M) (ha : a ≫ a = a) : HasKernel a :=
  (isIdempotentComplete_iff_idempotents_have_kernels (ChowMotiveCat k)).1 inferInstance M a ha

end Stacks.WeilCohomology.ChowMotiveCat
