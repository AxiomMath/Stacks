module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Two
public import Mathlib.RingTheory.Localization.Basic
public import StacksFrontier.RingTheory.NodalCurve

/-!
# The Artin–Schreier cover of the node, in characteristic `2`

Let `k` be a field of characteristic `2`, let `A = {g ∈ k[t] ∣ g(0) = g(1)}` be the node — the
affine line with the two points `t = 0` and `t = 1` glued, `Stacks.nodeRing` — and let
`B = k[t, 1/t]` be the affine line with `t = 0` removed. Put `a = t² + t`, which lies in `A`
because `a(0) = 0 = a(1)` in characteristic `2`, and consider the Artin–Schreier equation

`z² + z = a`.

This file counts its solutions on both sides: there are **none** in `A`, and **exactly two** in
`B`, namely `t` and `t + 1`.

That count is the arithmetic heart of the counterexample to the Stacks Project tag 0EZK as the
source writes it, recorded as a *Stacks erratum* in the docstrings
of `Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageIso`. There, `T` is the étale
double cover `Spec A[z]/(z² + z + a)` of `S = Spec A`, étale because the derivative of
`z² + z + a` in `z` is the unit `1`; `F = h_T` is its functor of points; and
`f : X = Spec B ⟶ S = Spec A` is the homeomorphism of the Stacks proof, bijective because the
node has already glued the removed point `t = 0` to the surviving point `t = 1`
(`Stacks.NodalCurve.isClosedEmbedding_comap_localizationAway` together with
`Stacks.NodalCurve.comap_nodeRingSubtype_image_eq_univ`). Sections of `T` over `S` are solutions
of `z² + z = a` in `A`, and sections of `X ×_S T` over `X` are solutions in `B`, so the two
counts below are `Γ(S, F) = ∅` against two elements of `Γ(X, f⁻¹F)`, contradicting the equality
the tag asserts.

## Scope

What is proved here is the solution count, and only that. **Nothing in this file refutes the
tag**, and no declaration here carries a Stacks tag: turning the count into a refutation needs
the sheaf-theoretic half — that `T` is étale over `S`, that `f` is submersive with geometrically
connected fibres, and that sections of the representable sheaf and of its inverse image are the
two solution sets — none of which is proved here or elsewhere in the tree.

## Main results

* `Stacks.NodalCurve.sq_add_self_eq_sq_add_self_iff` — in a characteristic-`2` domain the
  solutions of `z² + z = c² + c` are exactly `c` and `c + 1`.
* `Stacks.NodalCurve.no_artinSchreier_root_nodeRing` — there is no solution in the node ring.
* `Stacks.NodalCurve.setOf_artinSchreier_root_localizationAway` — the solution set in
  `k[t, 1/t]` is `{t, t + 1}`, whose two members are distinct by
  `Stacks.NodalCurve.algebraMap_X_ne_algebraMap_X_add_one`.

## References

* [Stacks Project, Tag 0EZK](https://stacks.math.columbia.edu/tag/0EZK)
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.NodalCurve

/-! ### The Artin–Schreier equation in a characteristic-`2` domain -/

/-- **The Artin–Schreier equation in characteristic `2`.** In a domain of characteristic `2` the
equation `z² + z = c² + c` has exactly the two solutions `c` and `c + 1`. Both are solutions
because `(c + 1)² + (c + 1) = c² + c` once `2 = 0`, and there are no others because the equation
factors as `(z + c)(z + c + 1) = 0`. -/
public theorem sq_add_self_eq_sq_add_self_iff {R : Type*} [CommRing R] [IsDomain R] [CharP R 2]
    {z c : R} : z ^ 2 + z = c ^ 2 + c ↔ z = c ∨ z = c + 1 := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  constructor
  · intro hz
    have hfac : (z + c) * (z + c + 1) = 0 := by
      linear_combination hz + (c ^ 2 + c + z * c) * h2
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (by linear_combination h - c * h2)
    · exact Or.inr (by linear_combination h - (c + 1) * h2)
  · rintro (rfl | rfl)
    · rfl
    · linear_combination (c + 1) * h2

variable (k : Type*) [Field k] [CharP k 2]

/-! ### No solution over the node -/

/-- In characteristic `2` the element `a = t² + t` lies in the node ring: it vanishes at `0`, and
at `1` it takes the value `1 + 1 = 0`. -/
public theorem X_sq_add_X_mem_nodeRing : (X ^ 2 + X : Polynomial k) ∈ nodeRing k := by
  rw [mem_nodeRing_iff]
  simp [CharTwo.add_self_eq_zero]

omit [CharP k 2] in
/-- `t` does not lie in the node ring: it takes the value `0` at `0` and `1` at `1`. -/
public theorem X_not_mem_nodeRing : (X : Polynomial k) ∉ nodeRing k := by
  rw [mem_nodeRing_iff]
  simp

/-- `t + 1` does not lie in the node ring: it takes the value `1` at `0` and `1 + 1 = 0` at
`1`. -/
public theorem X_add_one_not_mem_nodeRing : (X + 1 : Polynomial k) ∉ nodeRing k := by
  rw [mem_nodeRing_iff]
  simp only [eval_add, eval_X, eval_one, zero_add, CharTwo.add_self_eq_zero]
  exact one_ne_zero

/-- **No section downstairs.** In characteristic `2` the Artin–Schreier equation `z² + z = a`
with `a = t² + t` has no solution in the node ring: a solution in `k[t]` is `t` or `t + 1`, and
neither takes the same value at `0` and at `1`. -/
public theorem no_artinSchreier_root_nodeRing :
    ∀ z ∈ nodeRing k, (z : Polynomial k) ^ 2 + z ≠ X ^ 2 + X := by
  intro z hz hroot
  rcases sq_add_self_eq_sq_add_self_iff.mp hroot with h | h
  · exact X_not_mem_nodeRing k (h ▸ hz)
  · exact X_add_one_not_mem_nodeRing k (h ▸ hz)

/-! ### Two solutions over the punctured line -/

/-- `B = k[t, 1/t]` is a domain: it is a localization of `k[t]` at powers of the nonzero
element `t`. -/
public instance isDomain_localizationAway : IsDomain (Localization.Away (X : Polynomial k)) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (prime_X (R := k)).ne_zero)

omit [CharP k 2] in
/-- The structure map `k[t] → k[t, 1/t]` is injective, `t` being a nonzero divisor. -/
public theorem injective_algebraMap_localizationAway :
    Function.Injective (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k))) :=
  IsLocalization.injective _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (prime_X (R := k)).ne_zero)

/-- `B = k[t, 1/t]` has characteristic `2`, the structure map from `k[t]` being injective. -/
public instance charP_localizationAway :
    CharP (Localization.Away (X : Polynomial k)) 2 :=
  charP_of_injective_algebraMap (injective_algebraMap_localizationAway k) 2

/-- **The solutions over `k[t, 1/t]`.** In characteristic `2` the Artin–Schreier equation
`z² + z = a` with `a = t² + t` has exactly the two solutions `t` and `t + 1` in `k[t, 1/t]`. -/
public theorem artinSchreier_root_localizationAway_iff
    {z : Localization.Away (X : Polynomial k)} :
    z ^ 2 + z = algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) (X ^ 2 + X) ↔
      z = algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X ∨
        z = algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X + 1 := by
  rw [map_add, map_pow]
  exact sq_add_self_eq_sq_add_self_iff

omit [CharP k 2] in
/-- The two solutions upstairs are distinct, because `B = k[t, 1/t]` is not the zero ring. -/
public theorem algebraMap_X_ne_algebraMap_X_add_one :
    algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X ≠
      algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X + 1 := by
  intro h
  exact one_ne_zero (show (1 : Localization.Away (X : Polynomial k)) = 0 by
    linear_combination -h)

/-- **Two sections upstairs.** The solution set of `z² + z = a` with `a = t² + t` in
`k[t, 1/t]` is exactly `{t, t + 1}`, a set with two distinct elements by
`Stacks.NodalCurve.algebraMap_X_ne_algebraMap_X_add_one`. -/
public theorem setOf_artinSchreier_root_localizationAway :
    {z : Localization.Away (X : Polynomial k) |
        z ^ 2 + z =
          algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) (X ^ 2 + X)} =
      {algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X,
        algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X + 1} := by
  ext z
  simpa using artinSchreier_root_localizationAway_iff k

end Stacks.NodalCurve

end
