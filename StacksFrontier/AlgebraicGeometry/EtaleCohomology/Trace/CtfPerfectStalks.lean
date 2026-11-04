module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CohomologicalTraceFormula

/-!
# The stalks of an object of `D_ctf` are perfect, in the form used by the trace formula

The trace formula `T''(X, K) = T'(X, K)` of [Stacks, Tag 03V3] is stated for `K` in
`D_ctf(X_étale, Λ)`; its right hand side `T'(X, K) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)` needs the stalks
`K_x̄` to be perfect. For a bounded below complex `K` whose image in the derived category lies in
`D_ctf(X_étale, Λ)` (`Stacks.EtaleCohomology.IsCtf`), this file records that its stalk complexes at
all geometric points are perfect (`Stacks.EtaleCohomology.HasPerfectStalks`), from
`Stacks.EtaleCohomology.isPerfect_derivedEtaleModuleStalk_of_isCtf` (Tags 03TT and 03TR) and the
exactness of the stalk functor.

## Main results

* `Stacks.EtaleCohomology.hasPerfectStalks_of_isCtf`.

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModules_ab5OfSize moduleCat_hasLimitsOfSize

/-- **The stalks of a complex in `D_ctf` are perfect.** If the image in the derived category of a
bounded below complex `K` of sheaves of `Λ`-modules on `X_étale` lies in `D_ctf(X_étale, Λ)`, then
the stalk complex of `K` at every geometric point of `X` is perfect. -/
theorem hasPerfectStalks_of_isCtf (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
    (Λ : Type) [Ring Λ] (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hK : IsCtf B (B.obj X hX) Λ (DerivedCategory.Q.obj K.obj)) : HasPerfectStalks Λ K := by
  intro s
  have := etaleModuleStalk_additive.{u, 0} B (B.obj X hX) Λ s
  exact StacksDraft.Perfect.isPerfect_of_iso
    ((etaleModuleStalk.{u, 0} B (B.obj X hX) Λ s).mapDerivedCategoryFactors.app K.obj).symm
    (isPerfect_derivedEtaleModuleStalk_of_isCtf B (B.obj X hX) Λ _ hK s)

end Stacks.EtaleCohomology

end
