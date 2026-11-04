module

public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic

/-!
# The dimension of projective space over a field

Projective `n`-space over a field `k` has dimension `n`. The dimension of
`Proj k[T₀, …, T_r]` is `r` (`Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin`), and the
base-change model `ℙⁿ_{Spec k}` is isomorphic to `Proj k[T₀, …, Tₙ]` by the coordinate-pinned
comparison `Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison`, so the two
computations agree.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_projectiveSpaceOverRing`: the dimension of `ℙⁿ` over a
  field is `n`.

## References

* [Stacks Project, Tag 0B2P](https://stacks.math.columbia.edu/tag/0B2P)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0B2P (dimension).** Projective `n`-space over a field has Krull
dimension `n` as a topological space. -/
@[stacks 0B2P "projective_space_dimension"]
theorem topologicalKrullDim_projectiveSpaceOverRing (k : Type u) [Field k] (n : ℕ) :
    topologicalKrullDim (projectiveSpaceOverRing n (CommRingCat.of k)) = (n : WithBot ℕ∞) := by
  have hiso := (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k n).iso
  rw [IsHomeomorph.topologicalKrullDim_eq _ hiso.hom.homeomorph.isHomeomorph]
  simpa using Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin k (r := n + 1) n.succ_pos

end AlgebraicGeometry

end
