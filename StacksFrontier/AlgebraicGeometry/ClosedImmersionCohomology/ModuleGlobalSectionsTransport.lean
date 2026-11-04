module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.CechAffineCover
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.GlobalSheafCohomology

/-!
# Vanishing on a closed subscheme, transported to the ambient scheme and to the module spelling

Let `v : Z ⟶ X` be a closed immersion of schemes and `G` a sheaf of `𝒪_Z`-modules. Cohomology
does not change along a closed immersion ([Stacks, Tag 089W]), so `Hᵖ(Z, G) = 0` exactly when
`Hᵖ(X, v_* G) = 0`; and the two spellings of sheaf cohomology in this development — the
`AddCommGrpCat`-valued `Hgroup` and the `Γ(X, ⊤)`-module-valued right derived functor of
`Stacks.Cohomology.AffineBase.moduleGlobalSections` — vanish together.

This file composes those two facts into the single step that a vanishing theorem proved on a
closed subscheme needs in order to be used by a consumer stated on the ambient scheme in the
module spelling. Both halves are in the library and neither needs quasi-coherence:
`Stacks.Cohomology.ClosedImmersion.isZero_hgroup_iff_pushforward` and
`Stacks.Cohomology.Affine.isZero_rightDerived_evaluation_of_isZero_Hgroup`.

It exists as its own declaration because the two steps are always taken together and in this
order, and because `Stacks.Cohomology.AffineBase.moduleGlobalSections` is one of eight
declarations of that name — composing the steps once, at that spelling, keeps every consumer
from having to pick the right homonym.

## Main results

* `Stacks.Cohomology.ClosedImmersion.isZero_rightDerived_moduleGlobalSections_pushforward`:
  **`Hᵖ(Z, G) = 0` gives `Hᵖ(X, v_* G) = 0` in the module spelling.**

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Cohomology.ClosedImmersion

variable {Z X : AlgebraicGeometry.Scheme.{u}} (v : Z ⟶ X)

/-- **Vanishing on a closed subscheme transported to the ambient scheme, in the module
spelling.** If `Hᵖ(Z, G)` is a zero object then so is the degree-`p` right derived functor of
`Stacks.Cohomology.AffineBase.moduleGlobalSections X` at `v_* G`.

The first step is [Stacks, Tag 089W]
(`Stacks.Cohomology.ClosedImmersion.isZero_hgroup_iff_pushforward`), the second is the agreement
of the two spellings of cohomology on vanishing
(`Stacks.Cohomology.Affine.isZero_rightDerived_evaluation_of_isZero_Hgroup`). Neither asks
anything of `G`. -/
theorem isZero_rightDerived_moduleGlobalSections_pushforward
    [AlgebraicGeometry.IsClosedImmersion v] (G : Z.Modules) (p : ℕ)
    (h : IsZero (Hgroup Z.ringCatSheaf ⊤ p G)) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj
      ((AlgebraicGeometry.Scheme.Modules.pushforward v).obj G)) :=
  Stacks.Cohomology.Affine.isZero_rightDerived_evaluation_of_isZero_Hgroup X.ringCatSheaf ⊤ p
    ((AlgebraicGeometry.Scheme.Modules.pushforward v).obj G)
    ((isZero_hgroup_iff_pushforward v G p).mp h)

end Stacks.Cohomology.ClosedImmersion

end
