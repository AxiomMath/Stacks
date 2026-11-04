module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded.ModuleGeneration
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded.GradedAlgebra
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded.AffineLimitProjection
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded.GradedModuleFiniteType

/-!
# The associated graded module of a coherent adic system

Let `X` be a Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals and `(F_n)` an object of
`Coh(X, ℐ)`. The sheaf `F_0` in degree zero and the transition kernels
`Ker(F_{n + 1} ⟶ F_n)` in degree `n + 1` form a finite type, graded, quasi-coherent module over
the associated graded algebra `⨁ ℐ ⁿ / ℐ ⁿ⁺¹` ([Stacks, Tag 087Z]).

Over an affine open `U`, the projection `Γ(lim F_m, U) ⟶ Γ(F_n, U)` is surjective with kernel
`I(U) ^ (n + 1) Γ(lim F_m, U)`, and the homogeneous pieces of the graded module are identified
with the associated graded pieces of `Γ(lim F_m, U)`.

## Main definitions

* `Stacks.Coherent.sectionsSystem`, `Stacks.Coherent.sectionsLimit`: the inverse system of
  sections of a coherent adic system over an open, and its limit.
* `Stacks.Coherent.IsFiniteTypeOnAffine`: local finite generation of a graded module by
  homogeneous sections.
* `Stacks.Coherent.AssociatedGradedAlgebraData`: the associated graded algebra of an ideal
  sheaf, with the affine identifications of its homogeneous pieces.
* `Stacks.Coherent.AssociatedGradedData`: a graded module over it whose homogeneous pieces are
  `F_0` and the transition kernels, with their affine identifications.

## Main results

* `Stacks.Coherent.affineOpen_limit_projection_surjective`: over an affine open the projection
  from the sections of the limit to the sections of `F_n` is surjective.
* `Stacks.Coherent.affineOpen_limit_projection_ker`: its kernel is
  `I(U) ^ (n + 1) Γ(lim F_m, U)`.
* `Stacks.Coherent.finiteTypeAssociatedGradedData`: [Stacks, Tag 087Z].

## References

* [Stacks Project, Tag 087Z](https://stacks.math.columbia.edu/tag/087Z)
-/
