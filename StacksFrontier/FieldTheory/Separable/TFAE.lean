module

import Mathlib.FieldTheory.SeparablyGenerated

public import StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct

@[expose] public section

/-!
# Separability of a field extension: the `p`-th power criteria

Proof of `Algebra.isSeparableExtension_tfae`: for a field `k` of exponential characteristic `p` and
a field extension `K/k`, separability of `K/k` in the sense of [Stacks 030O], the criterion that
raising to the `p`-th power carry every `k`-linearly independent subset of `K` to a `k`-linearly
independent subset, reducedness of `K ⊗[k] k^{1/p}` and geometric reducedness of `K` over `k` are
all equivalent.

The four conditions are closed into the cycle (1) ⇒ (4) ⇒ (3) ⇒ (2) ⇒ (1).

(1) ⇒ (4) is Lemma [Stacks 030U] with `S` an algebraic closure of `k`, and (4) ⇒ (3) is that same
base change specialized to `k^{1/p}`, which is algebraic — indeed purely inseparable — over `k`.
Both read the base change with the field extension on the left, as 030U states it, and transport
reducedness across `Algebra.TensorProduct.comm`.

(3) ⇒ (2) is the source's argument, run on `k^{1/p} ⊗[k] K` rather than on `K ⊗[k] k^{1/p}`. Let
`(a_i)_{i ∈ s}` be `k`-linearly independent in `K` and let `∑ c_i a_i ^ p = 0` be a `k`-linear
relation among their `p`-th powers. The element `y = ∑ c_i^{1/p} ⊗ a_i` has
`y ^ p = 1 ⊗ ∑ c_i a_i ^ p = 0`, because raising to the `p`-th power is additive and carries
`c_i^{1/p}` to `c_i`; so `y = 0` by reducedness. The family `(1 ⊗ a_i)` is `k^{1/p}`-linearly
independent, `k^{1/p}` being flat over `k`, whence `c_i^{1/p} = 0` and `c_i = 0`. The source
instead uses the ring map `m : K ⊗[k] k^{1/p} → K`, `λ ⊗ μ ↦ λ^p μ^p`, whose injectivity is the
same computation read backwards; the map itself is not `k`-linear, only Frobenius-semilinear, so
exhibiting the single element `y` is shorter.

(2) ⇒ (1) is Mathlib's
`exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType`, which is the
source's transcendence-base argument — minimize the degree of inseparability over all
transcendence bases and use [Stacks 0H71] to exchange a basis element for an inseparable generator
— together with the observation that condition (2) passes to a subextension `K'` of `K`, since
linear independence over `k` may be tested after the injection `K' → K`.

## Main results

* `Stacks.Separable.PthPowerCriteria.solution`: the statement of Stacks Tag 030W.

## Implementation notes

The computation carrying (3) ⇒ (2) is isolated as
`Stacks.FormallySmooth.SeparableTFAE.sum_smul_pow_char`: Frobenius is semilinear along any
section `r` of the `p`-th power map, in the sense that `(∑ r (c i) • x i) ^ p = ∑ c i • x i ^ p`
in an algebra of exponential characteristic `p`. That is the whole of the characteristic-`p` input;
the tensor product enters only through `k`-linearity of `1 ⊗ (·) : K → k^{1/p} ⊗[k] K`, and
reducedness and flatness of `k^{1/p}` are then applied to `y` and to the family `(1 ⊗ a_i)`
respectively.

In exponential characteristic `p = 1` the field `k` has characteristic zero, hence is perfect, and
(2) ⇒ (1) is Mathlib's `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`; the
computation proving (3) ⇒ (2) is characteristic-free, `y ^ 1 = y` being the degenerate case of the
additivity of Frobenius.

## References

* [Stacks 030W](https://stacks.math.columbia.edu/tag/030W), in the section "Separable extensions".
  The two notions of separability are Definition 030O, the base change used for (1) ⇒ (4) and
  (4) ⇒ (3) is Lemma 030U, and the exchange of a transcendence basis element is Lemma 0H71.
-/

namespace Stacks.Separable.PthPowerCriteria

open scoped TensorProduct

/-- Reducedness of a tensor product of algebras does not depend on the order of the factors. -/
private theorem isReduced_tensorProduct_comm {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] (h : IsReduced (A ⊗[R] B)) : IsReduced (B ⊗[R] A) :=
  have := h
  isReduced_of_injective (Algebra.TensorProduct.comm R B A)
    (Algebra.TensorProduct.comm R B A).injective

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- If `K` is geometrically reduced over `k` then `K ⊗[k] k^{1/p}` is reduced: the extension
`k^{1/p}/k` is purely inseparable, in particular algebraic. -/
private theorem isReduced_tensorProduct_adjoinPthRoots (k K : Type*) [Field k] [Field K]
    [Algebra k K] [Algebra.IsGeometricallyReduced k K] :
    IsReduced (K ⊗[k] AdjoinPthRoots k) :=
  isReduced_tensorProduct_comm inferInstance

open Stacks.FormallySmooth.SeparableTFAE in
/-- For a field extension `K/k` with `k` of exponential characteristic `p`, the following are
equivalent: `K/k` is separable; `x ↦ x ^ p` carries every `k`-linearly independent subset of `K`
to a `k`-linearly independent family; `K ⊗[k] AdjoinPthRoots k` is reduced; and `K` is
geometrically reduced over `k`. -/
public theorem solution (k K : Type*) [Field k] [Field K] [Algebra k K]
    (p : ℕ) [ExpChar k p] :
    List.TFAE
      [Algebra.IsSeparableExtension k K,
        ∀ s : Set K, LinearIndepOn k _root_.id s → LinearIndepOn k (· ^ p) s,
        IsReduced (K ⊗[k] AdjoinPthRoots k),
        Algebra.IsGeometricallyReduced k K] := by
  tfae_have 1 → 4 := fun _ ↦ isGeometricallyReduced_of_isSeparableExtension k K
  tfae_have 4 → 3 := fun _ ↦ isReduced_tensorProduct_adjoinPthRoots k K
  tfae_have 3 → 2 := fun h _ hs ↦ linearIndepOn_pow_of_isReduced p h hs
  tfae_have 2 → 1 := fun H ↦ isSeparableExtension_of_forall_linearIndepOn_pow p H
  tfae_finish

end Stacks.Separable.PthPowerCriteria

/-!
# Separability of a field extension: the `p`-th power criteria

Let `k` be a field of exponential characteristic `p` and let `K/k` be a field extension. Four
properties of `K/k` are equivalent: that `K` is separable over `k` in the sense of Definition
030O, that raising to the `p`-th power carries every `k`-linearly independent subset of `K` to a
`k`-linearly independent subset, that the ring `K ⊗_k k^{1/p}` is reduced, and that `K` is
geometrically reduced over `k`.

The two middle conditions are the computational content: the second is what a transcendence-basis
argument consumes, and the third is what a base-change argument produces. `k^{1/p}`, the field
obtained by adjoining `p`-th roots of all elements of `k`, is Mathlib's `AdjoinPthRoots k`: the
field `k` again, with the `k`-algebra structure given by the Frobenius of the exponential
characteristic, which is `k^{1/p}` transported along its own Frobenius isomorphism onto `k`.

## Main results

* `Algebra.isSeparableExtension_tfae`: separability of `K/k`, the `p`-th power criterion for
  `k`-linear independence, reducedness of `K ⊗_k k^{1/p}`, and geometric reducedness of `K` over
  `k` are equivalent.

## Implementation notes

The source assumes `k` of characteristic `p > 0`; here `p` is the *exponential* characteristic
(`ExpChar k p`), so characteristic zero is included with `p = 1`. Nothing is lost and one thing is
gained: in characteristic zero all four conditions hold — the second because `x ^ 1 = x`, the third
because `AdjoinPthRoots k` is then `k` with the identity structure map, and the first because a
characteristic-zero field is perfect — so the equivalence is true uniformly, and stating it
uniformly is what lets Proposition 0322, itself stated for every characteristic, cite this lemma
without a case split. The characteristic-zero case of (2) ⇒ (1) is Mathlib's
`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`, and the positive-characteristic case
of that implication, for a finitely generated extension, is Mathlib's
`exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType`, which already
carries this tag; the remaining implications, and the passage from finitely generated subextensions
to `K`, are new.

Condition (2) quantifies over arbitrary subsets `s : Set K` rather than over the finite subsets the
source displays as `{a_1, …, a_m}`. The two are equivalent — a set is linearly independent iff each
of its finite subsets is (`linearIndepOn_of_finite`) — and the unrestricted form is the one a user
applies without first extracting a finite subset. `LinearIndepOn k id s` is Mathlib's spelling of
"the set `s` is `k`-linearly independent", and `LinearIndepOn k (· ^ p) s` of "the set of `p`-th
powers of elements of `s` is `k`-linearly independent", the family being indexed by `s`, so that it
also records that distinct elements of `s` have distinct `p`-th powers.

Separability of a not necessarily algebraic extension is `Algebra.IsSeparableExtension` of Tag
030O. Mathlib's `Algebra.IsSeparable` is separability of an *algebraic* extension, strictly
stronger here — `k(x)/k` is separable but not algebraic — and is not the source's condition (1).

Geometric reducedness is Mathlib's `Algebra.IsGeometricallyReduced k K`, reducedness of every base
change of `K` to a field extension of `k`, equivalently of `AlgebraicClosure k ⊗_k K`
(`Algebra.isGeometricallyReduced_field_iff`); the source's condition (4) is thus not narrowed to
one chosen algebraic closure.

Faithfulness. (1) No hypothesis is idle: the data is a field extension `K/k` and an exponential
characteristic `p` for `k`, and `p` occurs in condition (2) while `ExpChar k p` is what ties it to
`k` — for `k = 𝐅_2(t)`, `K = k(t^{1/2})` and `p = 2` conditions (1)–(4) all fail, whereas the same
`K/k` with the (impossible) datum `p = 3` would make (2) hold, so the instance is load-bearing.
(2) The scalars and base are the source's: separability, geometric reducedness, the tensor product
and the linear independence are all taken over `k` itself, and `K ⊗_k k^{1/p}` is the tensor
product over `k`, not over `k^{1/p}`. (3) Where the source names maps they are pinned, not merely
asserted to exist: the `k`-algebra structure on `k^{1/p}` is the Frobenius of the exponential
characteristic, and the map of condition (2) is `x ↦ x ^ p` itself rather than an abstract
`p`-power endomorphism. (4) The instantiation is not degenerate: for `k = 𝐅_p(u)` and `K = k(t)`
purely transcendental all four conditions hold with `K/k` neither trivial nor algebraic, for
`K = k(u^{1/p})` all four fail, and `k = 𝐐`, `K = 𝐐(t)` witnesses the characteristic-zero case
`p = 1`.

## References

* [Stacks 030W](https://stacks.math.columbia.edu/tag/030W)
* [Stacks 030O](https://stacks.math.columbia.edu/tag/030O), the two notions of separability
* [Stacks 030U](https://stacks.math.columbia.edu/tag/030U), which gives (1) ⇒ (4)
-/

@[expose] public section

open scoped TensorProduct

/-- **Stacks 030W.** Let `k` be a field of exponential characteristic `p` and let `K/k` be a field
extension. The following are equivalent: `K` is separable over `k` (Definition
[Stacks 030O](https://stacks.math.columbia.edu/tag/030O)); for every `k`-linearly independent
subset `s` of `K` the set of `p`-th powers of elements of `s` is `k`-linearly independent; the ring
`K ⊗_k k^{1/p}` is reduced; and `K` is geometrically reduced over `k`. -/
@[stacks 030W "Stated for the exponential characteristic, so that characteristic zero is the case
  `p = 1`, where all four conditions hold; the source assumes `p > 0`. Condition (2) quantifies over
  arbitrary, not just finite, linearly independent subsets. See the module docstring."]
public theorem Algebra.isSeparableExtension_tfae (k K : Type*) [Field k] [Field K] [Algebra k K]
    (p : ℕ) [ExpChar k p] :
    List.TFAE
      [Algebra.IsSeparableExtension k K,
        ∀ s : Set K, LinearIndepOn k _root_.id s → LinearIndepOn k (· ^ p) s,
        IsReduced (K ⊗[k] AdjoinPthRoots k),
        Algebra.IsGeometricallyReduced k K] := by apply Stacks.Separable.PthPowerCriteria.solution

end
