module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# The dual of an exterior power of a surjection with torsion kernel

Over an integral domain, let `u : M → M'` be a surjection whose kernel consists of torsion
elements. Then the transpose of `⋀^r u`, and hence its double transpose, is bijective: an
alternating form over a domain vanishes as soon as one of its arguments is torsion, so every
alternating form on `M` descends along `u`, and no functional on `⋀^r M` sees the kernel.

This is the step of [Stacks, Tag 0B3T] saying that the comparison map of determinant line
bundles is an isomorphism away from the divisor, at a point whose local ring is an arbitrary
domain rather than a discrete valuation ring.

## Main results

* `exteriorPower.bijective_dualMap_map_of_surjective_of_ker_le_torsion`: the transpose of
  `⋀^r u` is bijective.
* `exteriorPower.bijective_dualMap_dualMap_map_of_surjective_of_ker_le_torsion`: **so is its
  double transpose.**

## Implementation notes

The descent is built from a set-theoretic section of `u`, the point being that the value of the
form does not depend on the choice of lifts. That independence is `MultilinearMap.map_add_univ`,
which expands the form on a sum over all subsets of the coordinates, every summand but one
having a torsion entry.

Neither finiteness nor principality is needed, which is the point: the route through
`exteriorPower.torsionQuotientEquiv` needs a principal ideal domain, and is therefore
unavailable at a closed point of a surface, where `⋀^r` of a torsion-free module can have
torsion.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public noncomputable section

namespace exteriorPower

variable {A : Type*} [CommRing A] [IsDomain A] {M M' : Type*} [AddCommGroup M] [Module A M]
  [AddCommGroup M'] [Module A M'] {r : ℕ}

/-- Over a domain an alternating form with values in the ring vanishes on a vector one of whose
entries is torsion. -/
private theorem alternatingMap_eq_zero_of_mem_torsion (Φ : M [⋀^Fin r]→ₗ[A] A)
    (v : Fin r → M) (i : Fin r) (hi : v i ∈ Submodule.torsion A M) : Φ v = 0 := by
  classical
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (v i)).mp hi
  have key := Φ.toMultilinearMap.map_update_smul v i (a : A) (v i)
  rw [show (a : A) • v i = 0 from ha, MultilinearMap.map_update_zero,
    Function.update_eq_self] at key
  have hmul : (a : A) * Φ v = 0 := by
    rw [← smul_eq_mul]
    exact key.symm
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd h (nonZeroDivisors.coe_ne_zero a)
  · exact h

/-- **An alternating form over a domain only depends on its arguments through a map with torsion
kernel.** Expanding the form on `w = v + (w - v)` over all subsets of the coordinates leaves one
summand with no torsion entry. -/
private theorem alternatingMap_congr_of_ker_le_torsion (Φ : M [⋀^Fin r]→ₗ[A] A)
    {u : M →ₗ[A] M'} (hker : LinearMap.ker u ≤ Submodule.torsion A M) {v w : Fin r → M}
    (h : ∀ i, u (v i) = u (w i)) : Φ v = Φ w := by
  classical
  have htor : ∀ i, (w - v) i ∈ Submodule.torsion A M := fun i =>
    hker (by simp only [LinearMap.mem_ker, Pi.sub_apply, map_sub, h i, sub_self])
  have hvw : v + (w - v) = w := by abel
  have hsum : Φ (v + (w - v)) = ∑ S : Finset (Fin r), Φ (S.piecewise v (w - v)) :=
    Φ.toMultilinearMap.map_add_univ v (w - v)
  rw [hvw] at hsum
  rw [hsum, Finset.sum_eq_single_of_mem Finset.univ (Finset.mem_univ _)]
  · rw [Finset.piecewise_univ]
  · intro S _ hS
    obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
      by_contra hc
      exact hS (Finset.eq_univ_iff_forall.2 fun i => not_not.1 (not_exists.1 hc i))
    exact alternatingMap_eq_zero_of_mem_torsion Φ _ i
      (by rw [Finset.piecewise_eq_of_notMem _ _ _ hi]; exact htor i)

/-- Evaluating on lifts of an updated family only depends on the lift of the updated entry
through its image. -/
private theorem alternatingMap_surjInv_update [DecidableEq (Fin r)]
    (Φ : M [⋀^Fin r]→ₗ[A] A) {u : M →ₗ[A] M'}
    (hu : Function.Surjective u) (hker : LinearMap.ker u ≤ Submodule.torsion A M)
    (v' : Fin r → M') (i : Fin r) (z : M') (z' : M) (hz : u z' = z) :
    Φ (fun k => Function.surjInv hu (Function.update v' i z k))
      = Φ (Function.update (fun k => Function.surjInv hu (v' k)) i z') := by
  refine alternatingMap_congr_of_ker_le_torsion Φ hker fun k => ?_
  by_cases hk : k = i
  · subst hk; simp [Function.surjInv_eq hu, hz]
  · simp [Function.update_of_ne hk, Function.surjInv_eq hu]

/-- The descent of an alternating form along a surjection with torsion kernel, defined by
evaluating on arbitrary lifts of the arguments. -/
private def descend (Φ : M [⋀^Fin r]→ₗ[A] A) {u : M →ₗ[A] M'} (hu : Function.Surjective u)
    (hker : LinearMap.ker u ≤ Submodule.torsion A M) : M' [⋀^Fin r]→ₗ[A] A where
  toFun v' := Φ fun i => Function.surjInv hu (v' i)
  map_update_add' v' i x y := by
    rw [alternatingMap_surjInv_update Φ hu hker v' i (x + y)
        (Function.surjInv hu x + Function.surjInv hu y) (by simp [Function.surjInv_eq hu]),
      alternatingMap_surjInv_update Φ hu hker v' i x _ (Function.surjInv_eq hu x),
      alternatingMap_surjInv_update Φ hu hker v' i y _ (Function.surjInv_eq hu y)]
    exact Φ.map_update_add _ i _ _
  map_update_smul' v' i c x := by
    rw [alternatingMap_surjInv_update Φ hu hker v' i (c • x) (c • Function.surjInv hu x)
        (by simp [Function.surjInv_eq hu]),
      alternatingMap_surjInv_update Φ hu hker v' i x _ (Function.surjInv_eq hu x)]
    exact Φ.map_update_smul _ i c _
  map_eq_zero_of_eq' _v' i j hv hij :=
    Φ.map_eq_zero_of_eq _ (i := i) (j := j) (congrArg (Function.surjInv hu) hv) hij

/-- The descent recovers the original form on images. -/
private theorem descend_comp (Φ : M [⋀^Fin r]→ₗ[A] A) {u : M →ₗ[A] M'}
    (hu : Function.Surjective u) (hker : LinearMap.ker u ≤ Submodule.torsion A M)
    (v : Fin r → M) : descend Φ hu hker (⇑u ∘ v) = Φ v :=
  alternatingMap_congr_of_ker_le_torsion Φ hker fun i => Function.surjInv_eq hu (u (v i))

/-- **The transpose of `⋀^r` of a surjection with torsion kernel is bijective**, over an
arbitrary integral domain. Injectivity is formal; surjectivity is the descent of alternating
forms along `u`. -/
public theorem bijective_dualMap_map_of_surjective_of_ker_le_torsion (r : ℕ) {u : M →ₗ[A] M'}
    (hu : Function.Surjective u) (hker : LinearMap.ker u ≤ Submodule.torsion A M) :
    Function.Bijective (exteriorPower.map r u).dualMap := by
  refine ⟨LinearMap.dualMap_injective_of_surjective (exteriorPower.map_surjective hu),
    fun phi => ?_⟩
  refine ⟨exteriorPower.alternatingMapLinearEquiv
    (descend (exteriorPower.alternatingMapLinearEquiv.symm phi) hu hker), ?_⟩
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v => ?_)
  show exteriorPower.alternatingMapLinearEquiv
      (descend (exteriorPower.alternatingMapLinearEquiv.symm phi) hu hker)
      (exteriorPower.map r u (exteriorPower.ιMulti A r v))
    = phi (exteriorPower.ιMulti A r v)
  rw [exteriorPower.map_apply_ιMulti, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    descend_comp, exteriorPower.alternatingMapLinearEquiv_symm_apply]
  rfl

/-- **The double transpose of `⋀^r` of a surjection with torsion kernel is bijective**, over an
arbitrary integral domain. This is the comparison map of determinant modules of
[Stacks, Tag 0B3T] away from the divisor. -/
public theorem bijective_dualMap_dualMap_map_of_surjective_of_ker_le_torsion (r : ℕ)
    {u : M →ₗ[A] M'} (hu : Function.Surjective u)
    (hker : LinearMap.ker u ≤ Submodule.torsion A M) :
    Function.Bijective (exteriorPower.map r u).dualMap.dualMap :=
  (LinearEquiv.ofBijective _
    (bijective_dualMap_map_of_surjective_of_ker_le_torsion r hu hker)).dualMap.bijective

end exteriorPower

end
