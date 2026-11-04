module

public import StacksFrontier.AlgebraicGeometry.Curves.Node.AlgebraCompletion
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.PrincipalConductor
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.QuadraticRelationDeltaOne
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.SeparableFibreDeltaOne
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.BaseChangeDelta
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Completion
public import StacksFrontier.RingTheory.Branches.Completion
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian
import all StacksFrontier.AlgebraicGeometry.Curves.Node.Algebra
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Nodal local algebras from the delta invariant and the number of geometric branches

A Nagata local algebra over a field is nodal exactly when it is reduced and one-dimensional, its
residue field is separable over the ground field, its delta invariant is one, and it has two
geometric branches.

## Main results

* `Stacks.Curves.hasNodalQuadraticRelation_of_deltaInvariant_eq_one_of_two_branches` — a
  henselian reduced one-dimensional Nagata local ring of delta invariant one with two geometric
  branches carries a nodal quadratic relation.
* `Stacks.Curves.isNodalAlgebra_of_deltaInvariant_eq_one_and_two_geometricBranches` — the reverse
  implication of Stacks Tag 0C4A.
* `Stacks.Curves.isNodalAlgebra_iff_deltaInvariant_eq_one_and_two_geometricBranches` — the
  equivalence of Stacks Tag 0C4A.

## References

* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 0C49](https://stacks.math.columbia.edu/tag/0C49)
* [Stacks Project, Tag 0C2D](https://stacks.math.columbia.edu/tag/0C2D)
* [Stacks Project, Tag 0C3V](https://stacks.math.columbia.edu/tag/0C3V)
* [Stacks Project, Tag 0C3W](https://stacks.math.columbia.edu/tag/0C3W)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Curves

/-- A henselian reduced one-dimensional Nagata local ring of delta invariant one with two
geometric branches carries a nodal quadratic relation. -/
public theorem hasNodalQuadraticRelation_of_deltaInvariant_eq_one_of_two_branches
    (A : Type u) [CommRing A] [HenselianLocalRing A] [IsReduced A] (hNagata : IsNagataRing A)
    (hdim : ringKrullDim A = 1) (hdelta : Ring.deltaInvariant A = 1)
    (hbr : numberOfGeometricBranchesOfLocalRing A = 2) :
    HasNodalQuadraticRelation A := by
  let : IsNoetherianRing A := hNagata.1
  obtain ⟨θ, hθm, hθnzd, hprinc⟩ :=
    exists_generator_map_maximalIdeal_of_deltaInvariant_eq_one A hNagata hdim hdelta
  exact hasNodalQuadraticRelation_of_deltaInvariant_eq_one_of_isPrincipal A hdelta
    (isSeparable_quadraticAlgebra_of_deltaInvariant_eq_one_of_two_branches A hdelta hbr)
    θ hθm hθnzd hprinc

/-- A Nagata local algebra over a field which is reduced and one-dimensional, has separable
residue extension, delta invariant one and two geometric branches, is nodal. -/
public theorem isNodalAlgebra_of_deltaInvariant_eq_one_and_two_geometricBranches
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (hNagata : IsNagataRing A) (hsep : Algebra.IsSeparableExtension k (ResidueField A))
    (hred : IsReduced A) (hdim : ringKrullDim A = 1) (hdelta : Ring.deltaInvariant A = 1)
    (hbr : numberOfGeometricBranchesOfLocalRing A = 2) :
    IsNodalAlgebra k A := by
  let : IsNoetherianRing A := hNagata.1
  refine isNodalAlgebra_of_isNodalAlgebra_adicCompletion k A ?_
  let Ahat := AdicCompletion (maximalIdeal A) A
  let : IsLocalRing Ahat :=
    AdicCompletion.isLocalRing_of_fg (maximalIdeal A).fg_of_isNoetherianRing
  let : IsNoetherianRing Ahat := AdicCompletion.isNoetherianRing (maximalIdeal A)
  let : HenselianLocalRing Ahat :=
    henselianLocalRing_adicCompletion A (maximalIdeal A).fg_of_isNoetherianRing
  have hredHat : IsReduced Ahat :=
    IsLocalRing.isReduced_adicCompletion_maximalIdeal_of_isNagataRing hNagata
  have hbrHat : numberOfGeometricBranchesOfLocalRing Ahat = 2 :=
    (numberOfBranches_and_numberOfGeometricBranches_eq_adicCompletion_of_dimension_one
      A (henselizationData A).carrier (henselizationData Ahat).carrier
      (strictHenselizationData A).carrier (strictHenselizationData Ahat).carrier
      (SeparableClosure (ResidueField A)) (SeparableClosure (ResidueField Ahat))
      hdim).2.symm.trans hbr
  exact ⟨isSeparableExtension_of_algEquiv (residueFieldAlgEquiv_adicCompletion k A) hsep, hredHat,
    hasNodalQuadraticRelation_of_deltaInvariant_eq_one_of_two_branches Ahat
      IsLocalRing.isNagataRing_adicCompletion_maximalIdeal
      (IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal.trans hdim)
      ((deltaInvariant_adicCompletion_maximalIdeal A hNagata hdim).trans hdelta) hbrHat⟩

/-- A Nagata local algebra over a field is nodal if and only if it is reduced
and one-dimensional, its residue field is separable, its delta invariant is one, and it has two
geometric branches. -/
@[stacks 0C4A "equivalence", sga "7 X 2.24" "more general"]
public theorem isNodalAlgebra_iff_deltaInvariant_eq_one_and_two_geometricBranches
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (hA : IsNagataRing A) :
    IsNodalAlgebra k A ↔
      Algebra.IsSeparableExtension k (ResidueField A) ∧
        IsReduced A ∧
        ringKrullDim A = 1 ∧
        Ring.deltaInvariant A = 1 ∧
        numberOfGeometricBranchesOfLocalRing A = 2 :=
  ⟨deltaInvariant_eq_one_and_two_geometricBranches_of_isNodalAlgebra k A hA,
    fun ⟨hsep, hred, hdim, hdelta, hbr⟩ =>
      isNodalAlgebra_of_deltaInvariant_eq_one_and_two_geometricBranches k A hA hsep hred hdim
        hdelta hbr⟩

end Stacks.Curves

end
