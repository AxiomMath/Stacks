module

public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinesAvoidingSubvariety

/-!
# The locus of centres of projection tangent to a subvariety at a point

Let `V` be a finite-dimensional vector space over an algebraically closed field `k`, let `x` be a
closed point of `𝐏(V)` with hyperplane `W_x` of degree-one forms vanishing at it, and let
`N ≤ W_x` be a submodule. For a closed point `p ≠ x` with hyperplane `W_p`, the hyperplane
`W_p ⊓ W_x` of `W_x` spans `W_x` together with `N` exactly when `p` does not lie on the linear
subspace cut out by `N`.

The projection away from `p` restricts on the cotangent space of `𝐏(V)` at `x` — which is `W_x` —
to the inclusion of `W_p ⊓ W_x`, and `N` is the conormal space at `x` of a closed subvariety
through `x`. So this says that the projection away from `p` is injective on the tangent space of
that subvariety at `x` exactly when `p` avoids the linear subspace cut out by the conormal space,
which is therefore the locus of centres whose projection is tangent to the subvariety at `x`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.pointSubmodule_le_of_le_of_isClosed`: a closed point
  of `𝐏(V)` whose hyperplane contains the hyperplane of another closed point equals it.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.sup_inf_pointSubmodule_eq_iff_notMem_linearSubspace`:
  the hyperplane `W_p ⊓ W_x` of `W_x` spans `W_x` together with a submodule `N ≤ W_x` exactly when
  `p` lies off the linear subspace cut out by `N`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_closedPoint_notMem_linearSubspace`: the linear
  subspace cut out by a nonzero submodule omits some closed point, so its complement is a nonempty
  open subset of `𝐏(V)`.

## Implementation notes

Both directions are explicit rather than lattice-theoretic. A closed point `p` of `𝐏(V)` over an
algebraically closed field is cut out by a nonzero linear functional whose kernel is `W_p`, so
`N ⊄ W_p` provides a vector `ν ∈ N` with `φ ν ≠ 0`; subtracting the right multiple of `ν` from a
given `w ∈ W_x` lands in `W_p ⊓ W_x`, which is the spanning statement. Conversely a submodule
inside `W_p` spans with `W_p ⊓ W_x` only a submodule of `W_p`, and `W_x` is not one, since two
distinct closed points have distinct hyperplanes and these have equal finite corank.

## References

* [Stacks Project, Tag 0B1Q](https://stacks.math.columbia.edu/tag/0B1Q)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u v

variable (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]

/-- Two closed points of `𝐏(V)` whose hyperplanes of degree-one forms are nested are equal: both
hyperplanes have corank one, hence equal finite rank. -/
public theorem pointSubmodule_le_of_le_of_isClosed [IsAlgClosed k] [Module.Finite k V]
    {p q : projectiveSpaceOfModule k V}
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k V)))
    (h : pointSubmodule k V p ≤ pointSubmodule k V q) : p = q := by
  have hrank : ∀ r : projectiveSpaceOfModule k V,
      IsClosed ({r} : Set (projectiveSpaceOfModule k V)) →
      Module.finrank k (pointSubmodule k V r) + 1 = Module.finrank k V := by
    intro r hr
    have hquot := Submodule.finrank_quotient_add_finrank (pointSubmodule k V r)
    rw [finrank_quotient_pointSubmodule k V r hr] at hquot
    omega
  exact eq_of_pointSubmodule_eq k V hp hq (Submodule.eq_of_le_of_finrank_eq h
    (Nat.add_right_cancel ((hrank p hp).trans (hrank q hq).symm)))

/-- **The tangency criterion for a centre of projection.** Let `x` and `p` be distinct closed
points of `𝐏(V)` and let `N` be a submodule of the hyperplane `W_x` of `x`. The hyperplane
`W_p ⊓ W_x` of `W_x` spans `W_x` together with `N` exactly when `p` does not lie on the linear
subspace cut out by `N`. -/
public theorem sup_inf_pointSubmodule_eq_iff_notMem_linearSubspace [IsAlgClosed k]
    [Module.Finite k V] {x p : projectiveSpaceOfModule k V}
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V))) (hxp : x ≠ p)
    {N : Submodule k V} (hN : N ≤ pointSubmodule k V x) :
    (pointSubmodule k V p ⊓ pointSubmodule k V x) ⊔ N = pointSubmodule k V x ↔
      p ∉ linearSubspace k V N := by
  obtain ⟨φ, hφ, rfl⟩ := exists_eq_linearFunctionalPoint k V p hp
  have hker : pointSubmodule k V (linearFunctionalPoint k V φ hφ) = LinearMap.ker φ :=
    pointSubmodule_linearFunctionalPoint k V φ hφ
  rw [mem_linearSubspace_iff, hker]
  refine ⟨fun hsup hle => hxp (pointSubmodule_le_of_le_of_isClosed k V hx hp
    ((hsup.ge.trans (sup_le inf_le_left hle)).trans hker.ge)), fun hle => ?_⟩
  obtain ⟨ν, hνN, hν⟩ : ∃ ν ∈ N, φ ν ≠ 0 := by
    obtain ⟨ν, hνN, hν⟩ := IsConcreteLE.not_le_iff_exists.mp hle
    exact ⟨ν, hνN, fun h => hν (LinearMap.mem_ker.mpr h)⟩
  refine le_antisymm (sup_le inf_le_right hN) fun w hw => ?_
  refine Submodule.mem_sup.mpr ⟨w - (φ w / φ ν) • ν, ?_, (φ w / φ ν) • ν, ?_, by abel⟩
  · refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hν, sub_self]
    · exact Submodule.sub_mem _ hw (Submodule.smul_mem _ _ (hN hνN))
  · exact Submodule.smul_mem _ _ hνN

/-- The linear subspace cut out by a nonzero submodule of `V` omits a closed point of `𝐏(V)`:
a functional not vanishing on a chosen nonzero vector of the submodule cuts out such a point. -/
public theorem exists_closedPoint_notMem_linearSubspace {N : Submodule k V} (hN : N ≠ ⊥) :
    ∃ q : projectiveSpaceOfModule k V,
      IsClosed ({q} : Set (projectiveSpaceOfModule k V)) ∧ q ∉ linearSubspace k V N := by
  obtain ⟨ν, hνN, hν⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  obtain ⟨φ, hφν⟩ := Module.Projective.exists_dual_eq_one k hν
  have hφ : φ ≠ 0 := fun h => by simp [h] at hφν
  refine ⟨linearFunctionalPoint k V φ hφ, linearFunctionalPoint_isClosed k V φ hφ, ?_⟩
  rw [mem_linearSubspace_iff, pointSubmodule_linearFunctionalPoint k V φ hφ]
  exact fun hle => one_ne_zero (hφν.symm.trans (LinearMap.mem_ker.mp (hle hνN)))

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
