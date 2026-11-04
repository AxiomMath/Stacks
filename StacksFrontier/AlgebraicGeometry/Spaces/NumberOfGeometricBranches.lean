module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BranchCount

/-!
# The number of geometric branches of an algebraic space at a point

The equivalent conditions of Tag 0DQ3 single out at most one natural number at a point `x` of an
algebraic space `F`: the number of geometric branches of `F` at `x`. It is defined here as the
infimum, in `ℕ∞`, of the natural numbers satisfying the geometric-chart condition, so that the
empty infimum records the case of infinitely many geometric branches.

## Main definitions

* `AlgebraicGeometry.Space.numberOfGeometricBranches` is the number of geometric branches of an
  algebraic space at a point, with value in `ℕ∞`.

## Main results

* `AlgebraicGeometry.Space.numberOfGeometricBranches_eq_nat_iff`: a finite value of the count is
  exactly the value appearing in the equivalent conditions of Tag 0DQ3.
* `AlgebraicGeometry.Space.numberOfGeometricBranches_eq_top_iff`: the count is infinite exactly
  when no natural number satisfies those conditions.

## Implementation notes

The infimum is taken over the condition `AlgebraicGeometry.Space.HasGeometricBranchCount`, which
asks that every étale scheme chart above `x` have exactly `n` geometric branches. For an
algebraic space Tag 0DQ3 identifies that condition with the three branch-count conditions on the
charts, and the identification forces the value to be unique: a condition which bounds the
branch count by `n` and attains it determines `n`. The two characterizations below let clients
use the count without unfolding the infimum.

The number of geometric branches of a *scheme* at a point is the separate
`AlgebraicGeometry.numberOfGeometricBranches`, the number of minimal primes of a strict
henselization of its local ring there; the two agree on an étale chart of `F` above `x` by the
first characterization below together with Tag 0DQ3.

## References

* [Stacks Project, Tag 0DQ4](https://stacks.math.columbia.edu/tag/0DQ4)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

/-- The infimum in `ℕ∞` of the natural numbers satisfying a predicate which holds for at most
one of them is a given finite value exactly when the predicate holds for it: the set of values
is either empty, with infimum `⊤`, or a singleton. -/
private theorem sInf_natCast_eq_natCast_iff {P : ℕ → Prop}
    (huniq : ∀ {m k : ℕ}, P m → P k → m = k) (n : ℕ) :
    sInf {v : ℕ∞ | ∃ m : ℕ, P m ∧ v = (m : ℕ∞)} = (n : ℕ∞) ↔ P n := by
  have hsingleton : ∀ {m : ℕ}, P m →
      {v : ℕ∞ | ∃ k : ℕ, P k ∧ v = (k : ℕ∞)} = {(m : ℕ∞)} := by
    intro m hm
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun ⟨k, hk, hv⟩ ↦ by rw [hv, huniq hk hm], fun hv ↦ ⟨m, hm, hv⟩⟩
  refine ⟨fun h ↦ ?_, fun hn ↦ by rw [hsingleton hn, sInf_singleton]⟩
  rcases em (∃ m : ℕ, P m) with ⟨m, hm⟩ | hempty
  · rw [hsingleton hm, sInf_singleton] at h
    obtain rfl : m = n := by exact_mod_cast h
    exact hm
  · have hset : {v : ℕ∞ | ∃ k : ℕ, P k ∧ v = (k : ℕ∞)} = ∅ := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨k, hk, -⟩
      exact hempty ⟨k, hk⟩
    rw [hset, sInf_empty] at h
    exact absurd h (ENat.natCast_lt_top n).ne'

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- At most one natural number satisfies the geometric-chart condition of Tag 0DQ3 at a point of
an algebraic space: by that lemma it is also the branch count of the charts, which is both a
bound and attained, and two such numbers bound each other. -/
private theorem hasGeometricBranchCount_unique (hF : IsAlgebraicSpace B S hS F)
    (x : points B S hS F) {n m : ℕ} (hn : HasGeometricBranchCount B S hS x n)
    (hm : HasGeometricBranchCount B S hS x m) : n = m := by
  obtain ⟨hnall, U, a, u, ha, hu, hnex⟩ :=
    (branchCount_iff_geometricBranchCount B S hS hF x n).2 hn
  obtain ⟨hmall, V, b, v, hb, hv, hmex⟩ :=
    (branchCount_iff_geometricBranchCount B S hS hF x m).2 hm
  exact_mod_cast le_antisymm (hnex.symm.trans_le (hmall U a u ha hu))
    (hmex.symm.trans_le (hnall V b v hb hv))

/-- **Stacks 0DQ4.** The number of geometric branches of an algebraic space at a point: the
natural number satisfying the equivalent conditions of Tag 0DQ3 if there is one, and `⊤`
otherwise. -/
@[stacks 0DQ4]
def numberOfGeometricBranches (x : points B S hS F) : ℕ∞ :=
  sInf {v : ℕ∞ | ∃ n : ℕ, HasGeometricBranchCount B S hS x n ∧ v = (n : ℕ∞)}

/-- **Stacks 0DQ4.** A finite value of the number of geometric branches of an algebraic space at
a point is exactly the value appearing in the equivalent conditions of Tag 0DQ3. -/
@[stacks 0DQ4 "finite value"]
theorem numberOfGeometricBranches_eq_nat_iff (hF : IsAlgebraicSpace B S hS F)
    (x : points B S hS F) (n : ℕ) :
    numberOfGeometricBranches B S hS x = (n : ℕ∞) ↔ HasGeometricBranchCount B S hS x n :=
  sInf_natCast_eq_natCast_iff
    (fun hm hk ↦ hasGeometricBranchCount_unique B S hS hF x hm hk) n

/-- **Stacks 0DQ4.** The number of geometric branches of an algebraic space at a point is
infinite exactly when no natural number satisfies the equivalent conditions of Tag 0DQ3. -/
@[stacks 0DQ4 "infinite value"]
theorem numberOfGeometricBranches_eq_top_iff (x : points B S hS F) :
    numberOfGeometricBranches B S hS x = ⊤ ↔
      ∀ n : ℕ, ¬ HasGeometricBranchCount B S hS x n := by
  rw [numberOfGeometricBranches, sInf_eq_top]
  refine ⟨fun h n hn ↦ ?_, fun h v hv ↦ ?_⟩
  · exact absurd (h (n : ℕ∞) ⟨n, hn, rfl⟩) (ENat.natCast_lt_top n).ne
  · obtain ⟨n, hn, -⟩ := hv
    exact absurd hn (h n)

end AlgebraicGeometry.Space

end
