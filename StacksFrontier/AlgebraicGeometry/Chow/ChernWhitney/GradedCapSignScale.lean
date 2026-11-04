module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedCapRing

/-!
# The `(-1)^i`-scaling of a graded cap family

Let `G : ℤ → Type*` be a family of abelian groups — the Chow groups `A_k(X)` of a scheme are the
case of interest — and let `GradedCapFamily G` be the ring of graded cap families of
`StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedCapRing`, with the convolution

  `(a ∗ b)_k^m = ∑_{i + j = m} a_{k-j}^{i} ∘ b_k^{j}`

as multiplication. This file defines the `(-1)^i`-scaling `Stacks.Chow.capFamilySignScale`,
which multiplies the index-`i` component by `(-1)^i`, and shows that it is a ring endomorphism:
`Stacks.Chow.capFamilySignScale_one` and `Stacks.Chow.capFamilySignScale_mul`. On the index-`m`
component of a product the two factors contribute `(-1)^i (-1)^j = (-1)^m`, which is the whole
content of the multiplicativity.

## Implementation notes

`Stacks.Chow.chowSeriesSignScale` of `StacksFrontier.AlgebraicGeometry.Chow.ChernCharacterDual` is
the same substitution `c_j ↦ (-1)^j c_j` on `Stacks.Chow.chowCohomologySeries`, a product of
*bivariant groups* `A^i(X)`. Neither map is an instance of the other: a graded cap family is a
rule `A_k(X) ⟶ A_{k-i}(X)` on Chow groups, and the two types are unrelated — the passage from a
bivariant class to the cap operations it induces is `Stacks.Chow.TotalChowClass.op`, which is a
ring homomorphism into the graded cap families of a *test scheme* and not an identification. The
`(-1)^i`-scaling has to be stated on whichever of the two a given formula is read on, and
Stacks 02UI is read on the graded cap families.

## Main definitions

* `Stacks.Chow.capFamilySignScale` — the `(-1)^i`-scaling of a graded cap family.

## Main results

* `Stacks.Chow.capFamilySignScale_one`, `Stacks.Chow.capFamilySignScale_mul` — it is a ring
  endomorphism.
* `Stacks.Chow.Intertwines.capFamilySignScale` — an intertwiner of two families intertwines
  their scalings.

## References

* [Stacks Project, Tag 0FA5](https://stacks.math.columbia.edu/tag/0FA5)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
-/

@[expose] public noncomputable section

open Finset

namespace Stacks.Chow

universe v

variable {G H : ℤ → Type v} [∀ k, AddCommGroup (G k)] [∀ k, AddCommGroup (H k)]

/-! ### The `(-1)^i`-scaling -/

/-- **The `(-1)^i`-scaling of a graded cap family**: the family whose index-`i` component is
`(-1)^i` times that of `a`. Read on the total Chern class of a finite locally free module this
is the substitution `c_i ↦ (-1)^i c_i` of [Stacks, Tag 0FA5]. -/
def capFamilySignScale (a : GradedCapFamily G) : GradedCapFamily G :=
  fun k i => AddMonoidHom.mk' (fun x => ((-1 : ℤ) ^ i) • a k i x)
    fun x y => by rw [map_add, smul_add]

/-- The index-`i` component of `capFamilySignScale a` sends `x` to `(-1)^i • a k i x`. -/
@[simp]
theorem capFamilySignScale_apply (a : GradedCapFamily G) (k : ℤ) (i : ℕ) (x : G k) :
    capFamilySignScale a k i x = ((-1 : ℤ) ^ i) • a k i x :=
  rfl

/-- **The scaling fixes the unit.** The unit is concentrated in index `0`, where the factor is
`(-1)^0 = 1`. -/
theorem capFamilySignScale_one : capFamilySignScale (1 : GradedCapFamily G) = 1 := by
  funext k i
  refine AddMonoidHom.ext fun x => ?_
  rcases i with _ | i
  · rw [capFamilySignScale_apply, pow_zero, one_smul]
  · rw [capFamilySignScale_apply, gradedCap_one_of_ne (Nat.succ_ne_zero i) k]
    simp

/-- **The scaling is multiplicative for the convolution.** The index-`m` component of a product
is a sum over the pairs `i + j = m`, and on the summand indexed by `(m - j, j)` the two factors
contribute `(-1)^{m-j} (-1)^j = (-1)^m`. -/
theorem capFamilySignScale_mul (a b : GradedCapFamily G) :
    capFamilySignScale (a * b) = capFamilySignScale a * capFamilySignScale b := by
  funext k m
  refine AddMonoidHom.ext fun x => ?_
  rw [capFamilySignScale_apply, gradedCap_mul_apply, gradedCap_mul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [convolveTerm_of_le a b k hjm,
    convolveTerm_of_le (capFamilySignScale a) (capFamilySignScale b) k hjm,
    capTo_def, capTo_def, capFamilySignScale_apply, capFamilySignScale_apply, map_zsmul,
    map_zsmul, map_zsmul, smul_smul, ← pow_add, show m - j + j = m from by omega]

/-- An intertwiner of two graded cap families intertwines their `(-1)^i`-scalings: a
degree-shifting additive map commutes with multiplication by an integer. -/
theorem Intertwines.capFamilySignScale {d : ℤ} {pull : ∀ k : ℤ, G k →+ H (k + d)}
    {a : GradedCapFamily G} {a' : GradedCapFamily H} (ha : Intertwines pull a a') :
    Intertwines pull (Stacks.Chow.capFamilySignScale a)
      (Stacks.Chow.capFamilySignScale a') := by
  intro k i x
  rw [Stacks.Chow.capFamilySignScale_apply, map_zsmul, ha k i x,
    Stacks.Chow.capFamilySignScale_apply, map_zsmul]

end Stacks.Chow

end
