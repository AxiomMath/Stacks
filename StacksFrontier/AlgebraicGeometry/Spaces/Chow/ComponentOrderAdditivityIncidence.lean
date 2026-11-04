module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentOrderAdditivity
public import StacksFrontier.RingTheory.MinimalPrimes.DimensionOne

/-!
# The additivity over the components, with the branch-to-component map given by incidence alone

`AlgebraicGeometry.natCast_ord_sub_eq_finsum_components_mul` computes the order of vanishing of a
fraction on a one-dimensional Noetherian local ring `A` as the sum, over a family of ideals
`I i` cutting out the irreducible components through the closed point, of the multiplicity of the
component times the order of vanishing on it. Two of its hypotheses say nothing about the
branch-to-component map `c` itself:

* `hItop`, that `I i ≠ ⊤`;
* `hc`, that the primes of `A` minimal over `I i` are exactly the minimal primes `𝔮` of `A` with
  `c 𝔮 = i`.

Both are consequences of the dimension hypotheses together with the *incidence* statement that a
branch lies on the `i`-th component exactly when `c` sends it there, which is the only thing a
geometric consumer should have to prove about `c`. This file records that version.

`hItop` follows from `dim(A ⧸ I i) = 1`: the quotient has a prime, so it is nontrivial. For `hc`,
`Ideal.minimalPrimes_eq_setOf_mem_minimalPrimes_of_ringKrullDim_eq_one` says that in a local ring
of dimension one the primes minimal over a one-dimensional ideal are exactly the minimal primes
of the ring containing it; so `𝔮 ∈ (I i).minimalPrimes` is `𝔮 ∈ minimalPrimes A ∧ I i ≤ 𝔮`, and
the second conjunct is what the incidence hypothesis converts into `c 𝔮 = i`.

The point is which part of the geometry is still owed. The source's argument that the branches
over a component are the branches of the component is a dimension count — the component has the
same dimension as the ambient space, so a branch on it has height zero — and that count is now
done, once, in `StacksFrontier/RingTheory/MinimalPrimes/DimensionOne.lean`. What remains is the
incidence statement `hinc`, which has no dimension theory in it; it is supplied, for the
branches of a flat algebra over an étale chart's local ring, by
`AlgebraicGeometry.Space.exists_componentIdealFamily_le_iff_eq` in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentIdealBranchIncidence`.

## Main results

* `AlgebraicGeometry.natCast_ord_sub_eq_finsum_components_mul_of_le_iff`: the additivity formula
  with `hItop` and `hc` replaced by the incidence hypothesis.

## References

* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EQ2](https://stacks.math.columbia.edu/tag/0EQ2)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
-/

@[expose] public section

namespace AlgebraicGeometry

/-- **Additivity of the order of vanishing over the irreducible components, with the
branch-to-component map pinned down by incidence alone.** Let `A` be a one-dimensional Noetherian
local ring, let `a` and `b` be nonzerodivisors of finite colength, let the components through the
closed point be cut out by ideals `I i` with `A ⧸ I i` reduced of dimension one, let
`c` send each branch — each minimal prime of `A` — to a component, and let `m i` be the
multiplicity of the `i`-th component. If a branch `𝔮` lies on the `i`-th component, that is
`I i ≤ 𝔮`, exactly when `c 𝔮 = i`, then

  `ord_A(a) - ord_A(b) = ∑_i m i · (ord_{A ⧸ I i}(a) - ord_{A ⧸ I i}(b))`.

This is `AlgebraicGeometry.natCast_ord_sub_eq_finsum_components_mul` with its hypotheses `hItop`
and `hc` derived rather than assumed; see the module docstring. -/
theorem natCast_ord_sub_eq_finsum_components_mul_of_le_iff
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {ι : Type*}
    (a b : A) (ha : IsSMulRegular A a) (hb : IsSMulRegular A b) (hdim : ringKrullDim A = 1)
    (hfinitea : Module.length A (A ⧸ Ideal.span {a}) ≠ ⊤)
    (hfiniteb : Module.length A (A ⧸ Ideal.span {b}) ≠ ⊤)
    (I : ι → Ideal A)
    (hred : ∀ i, _root_.IsReduced (A ⧸ I i))
    (hdimI : ∀ i, ringKrullDim (A ⧸ I i) = 1)
    (c : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A} → ι)
    (hinc : ∀ (i : ι) (q : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A}),
      I i ≤ q.1.asIdeal ↔ c q = i)
    (m : ι → ℤ)
    (hm : ∀ q, ((Module.length (Localization.AtPrime q.1.asIdeal)
      (Localization.AtPrime q.1.asIdeal)).toNat : ℤ) = m (c q)) :
    ((Ring.ord A a).toNat : ℤ) - ((Ring.ord A b).toNat : ℤ) =
      ∑ᶠ i : ι, m i * (((Ring.ord (A ⧸ I i) (Ideal.Quotient.mk (I i) a)).toNat : ℤ) -
        ((Ring.ord (A ⧸ I i) (Ideal.Quotient.mk (I i) b)).toNat : ℤ)) := by
  refine natCast_ord_sub_eq_finsum_components_mul a b ha hb hdim hfinitea hfiniteb I
    (fun i => Ideal.Quotient.nontrivial_iff.mp ?_) hred hdimI c (fun i q => ?_) m hm
  · rw [← zero_le_ringKrullDim_iff_nontrivial, hdimI i]
    norm_num
  · rw [Ideal.minimalPrimes_eq_setOf_mem_minimalPrimes_of_ringKrullDim_eq_one hdim (I i)
      (hdimI i), Set.mem_setOf_eq]
    exact ⟨fun h => ⟨h.1, (hinc i ⟨q, h.1⟩).mp h.2⟩,
      fun h => ⟨h.choose, (hinc i ⟨q, h.choose⟩).mpr h.choose_spec⟩⟩

end AlgebraicGeometry

end
