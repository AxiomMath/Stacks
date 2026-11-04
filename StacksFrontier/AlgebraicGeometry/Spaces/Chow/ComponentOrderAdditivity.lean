module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartZeroCycleGrouping

/-!
# Additivity of the order of vanishing over the irreducible components, with multiplicities

Let `A` be a one-dimensional Noetherian local ring — the local ring, or the henselian local ring,
of an algebraic space at the generic point `ξ` of a prime divisor — and let `a` be a
nonzerodivisor of `A`. Let the *components through `ξ`* be indexed by `ι`, the `i`-th one cut out
by an ideal `I i ⊆ A` whose quotient `A ⧸ I i` is reduced, and let the *branches* at `ξ` be the
minimal primes of `A`. Each branch lies on exactly one component, which is the map
`c : minimalPrimes A → ι`; the map is surjective but **not injective**, a component having
several branches at a node, so the two index sets are not interchangeable
(`StacksFrontier.AlgebraicGeometry.Spaces.BranchesOverComponents`). Writing `m i` for the
multiplicity of the `i`-th component — the length of `A_q` over itself at any branch `q` on it —
this file proves

  `ord_A(a) = ∑_i m i · ord_{A ⧸ I i}(a)`,

and its difference form on a fraction `a / b` of nonzerodivisors,

  `ord_A(a) - ord_A(b) = ∑_i m i · (ord_{A ⧸ I i}(a) - ord_{A ⧸ I i}(b))`,

which is the order of vanishing of `a / b` read on `A` and on each component.

## Main results

* `AlgebraicGeometry.length_quotient_span_sup_eq_ord_quotient`: the colength of `(x, q)` is the
  order of vanishing of the image of `x` in `A ⧸ q`.
* `AlgebraicGeometry.natCast_length_quotient_span_eq_finsum_components_mul`: **the additivity.**
  The colength of `(a)` in `A` is the sum over the components of the multiplicity times the
  colength of `(a)` in the component.
* `AlgebraicGeometry.natCast_ord_sub_eq_finsum_components_mul`: the same identity for the
  difference of two colengths, which is the order of vanishing of the fraction `a / b`.

## References

* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 0EE2](https://stacks.math.columbia.edu/tag/0EE2)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0EQ2](https://stacks.math.columbia.edu/tag/0EQ2)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
* [Stacks Project, Tag 0EQB](https://stacks.math.columbia.edu/tag/0EQB)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
-/

@[expose] public section

open scoped nonZeroDivisors

namespace AlgebraicGeometry

/-- **The colength of `(x, q)` is an order of vanishing on the component cut out by `q`.** The
length over `A` of `A ⧸ ((x) + q)` is the order of vanishing of the image of `x` in `A ⧸ q`. -/
theorem length_quotient_span_sup_eq_ord_quotient {A : Type*} [CommRing A] (x : A) (q : Ideal A) :
    Module.length A (A ⧸ (Ideal.span {x} ⊔ q)) =
      Ring.ord (A ⧸ q) (Ideal.Quotient.mk q x) := by
  rw [sup_comm, length_quotient_sup_eq_length_quotient_map_mk q (Ideal.span {x}),
    Ideal.map_span, Set.image_singleton]
  rfl

/-- **Every component carries a branch, so the branch-to-component map is surjective.** If every
`I i` is a proper ideal and the minimal primes over `I i` are exactly the minimal primes of `A`
that `c` sends to `i`, then `c` is surjective. -/
theorem surjective_component_of_minimalPrimes {A : Type*} [CommRing A] {ι : Type*}
    (I : ι → Ideal A) (hItop : ∀ i, I i ≠ ⊤)
    (c : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A} → ι)
    (hc : ∀ (i : ι) (q : PrimeSpectrum A),
      q.asIdeal ∈ (I i).minimalPrimes ↔ ∃ h : q.asIdeal ∈ minimalPrimes A, c ⟨q, h⟩ = i) :
    Function.Surjective c := by
  intro i
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (hItop i)
  obtain ⟨h, hci⟩ := (hc i ⟨p, hp.1.1⟩).mp hp
  exact ⟨⟨⟨p, hp.1.1⟩, h⟩, hci⟩

/-- **A Noetherian ring has finitely many branches.** The minimal primes form a finite type. -/
private theorem finite_branches (A : Type*) [CommRing A] [IsNoetherianRing A] :
    Finite {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A} :=
  ((Ideal.finite_minimalPrimes_of_isNoetherianRing A ⊥).preimage
    (fun _ _ _ _ h => PrimeSpectrum.ext h)).to_subtype

/-- **Additivity of the order of vanishing over the irreducible components, with
multiplicities.** Let `A` be a one-dimensional Noetherian local ring, let `a` be a nonzerodivisor
of `A` of finite colength, let the components through the closed point be cut out by ideals
`I i` with `A ⧸ I i` reduced and one-dimensional, let `c` send each branch — each minimal prime
of `A` — to the component it lies on, and let `m i` be the multiplicity of the `i`-th component,
that is the length of `A_q` over itself at any branch `q` on it. Then

  `ord_A(a) = ∑_i m i · ord_{A ⧸ I i}(a)`. -/
theorem natCast_length_quotient_span_eq_finsum_components_mul
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {ι : Type*}
    (a : A) (ha : IsSMulRegular A a) (hdim : ringKrullDim A = 1)
    (hfinite : Module.length A (A ⧸ Ideal.span {a}) ≠ ⊤)
    (I : ι → Ideal A) (hItop : ∀ i, I i ≠ ⊤)
    (hred : ∀ i, _root_.IsReduced (A ⧸ I i))
    (hdimI : ∀ i, ringKrullDim (A ⧸ I i) = 1)
    (c : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A} → ι)
    (hc : ∀ (i : ι) (q : PrimeSpectrum A),
      q.asIdeal ∈ (I i).minimalPrimes ↔ ∃ h : q.asIdeal ∈ minimalPrimes A, c ⟨q, h⟩ = i)
    (m : ι → ℤ)
    (hm : ∀ q, ((Module.length (Localization.AtPrime q.1.asIdeal)
      (Localization.AtPrime q.1.asIdeal)).toNat : ℤ) = m (c q)) :
    ((Ring.ord A a).toNat : ℤ) =
      ∑ᶠ i : ι, m i * ((Ring.ord (A ⧸ I i) (Ideal.Quotient.mk (I i) a)).toNat : ℤ) := by
  classical
  have _ := finite_branches A
  have _ : Finite ι := Finite.of_surjective c (surjective_component_of_minimalPrimes I hItop c hc)
  let _ : Fintype {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A} := Fintype.ofFinite _
  let _ : Fintype ι := Fintype.ofFinite _
  have hanzd : a ∈ A⁰ := mem_nonZeroDivisors_iff_left.mpr fun r hr =>
    ha (by simpa only [smul_eq_mul, mul_zero] using hr)
  have hregI : ∀ i, IsSMulRegular (A ⧸ I i) (Ideal.Quotient.mk (I i) a) := by
    intro i
    have _ : _root_.IsReduced (A ⧸ I i) := hred i
    have hnzd : Ideal.Quotient.mk (I i) a ∈ (A ⧸ I i)⁰ :=
      Ring.nonZeroDivisors_le_comap_of_comap_mem_minimalPrimes (Ideal.Quotient.mk (I i))
        (fun q hq => by
          have hq' : Ideal.comap (Ideal.Quotient.mk (I i)) q ∈ (I i).minimalPrimes := by
            rw [Ideal.minimalPrimes_eq_comap]
            exact ⟨q, hq, rfl⟩
          exact ((hc i ⟨Ideal.comap (Ideal.Quotient.mk (I i)) q, hq'.1.1⟩).mp hq').choose)
        hanzd
    intro y z hyz
    exact sub_eq_zero.mp (mem_nonZeroDivisors_iff_left.mp hnzd (y - z)
      (by simpa only [mul_sub, sub_eq_zero, smul_eq_mul] using hyz))
  have hord : ∀ i : ι, ((Ring.ord (A ⧸ I i) (Ideal.Quotient.mk (I i) a)).toNat : ℤ) =
      ((Module.length A (A ⧸ (Ideal.span {a} ⊔ I i))).toNat : ℤ) := fun i => by
    rw [length_quotient_span_sup_eq_ord_quotient]
  have hcomp : ∀ i : ι, ((Module.length A (A ⧸ (Ideal.span {a} ⊔ I i))).toNat : ℤ) =
      ∑ q : {q : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A} // c q = i},
        ((Module.length A (A ⧸ (Ideal.span {a} ⊔ q.1.1.asIdeal))).toNat : ℤ) := by
    intro i
    have hfinI : Module.length A (A ⧸ (Ideal.span {a} ⊔ I i)) ≠ ⊤ :=
      ne_top_of_le_ne_top hfinite (Module.length_le_of_surjective
        (Submodule.mapQ (Ideal.span {a}) (Ideal.span {a} ⊔ I i) LinearMap.id
          (by simp))
        (fun z => by
          obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (Ideal.span {a} ⊔ I i) z
          exact ⟨(Ideal.span {a}).mkQ w, rfl⟩))
    rw [natCast_length_quotient_span_sup_eq_finsum_minimalPrimes_of_isReduced a (I i)
      (hItop i) (hred i) (hregI i) (hdimI i) hfinI, ← finsum_eq_sum_of_fintype]
    refine (finsum_eq_of_bijective
      (fun q : {q : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A} // c q = i} =>
        (⟨q.1.1, (hc i q.1.1).mpr ⟨q.1.2, q.2⟩⟩ :
          {q : PrimeSpectrum A // q.asIdeal ∈ (I i).minimalPrimes}))
      ⟨fun q q' h => Subtype.ext (Subtype.ext (by simpa [Subtype.ext_iff] using h)),
        fun q => ?_⟩
      fun q => rfl).symm
    obtain ⟨h, hci⟩ := (hc i q.1).mp q.2
    exact ⟨⟨⟨q.1, h⟩, hci⟩, rfl⟩
  rw [show ((Ring.ord A a).toNat : ℤ) = ((Module.length A (A ⧸ Ideal.span {a})).toNat : ℤ) from
      rfl,
    natCast_length_quotient_span_eq_sum_minimalPrimes a ha hdim hfinite,
    finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← Fintype.sum_fiberwise c (fun q : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A} =>
      ((Module.length (Localization.AtPrime q.1.asIdeal)
          (Localization.AtPrime q.1.asIdeal)).toNat : ℤ) *
        ((Module.length A (A ⧸ (Ideal.span {a} ⊔ q.1.asIdeal))).toNat : ℤ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hord i, hcomp i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hm q.1, q.2]

/-- **Additivity of the order of vanishing of a fraction over the irreducible components.** In
the situation of `AlgebraicGeometry.natCast_length_quotient_span_eq_finsum_components_mul`, for
two nonzerodivisors `a` and `b` of finite colength,

  `ord_A(a) - ord_A(b) = ∑_i m i · (ord_{A ⧸ I i}(a) - ord_{A ⧸ I i}(b))`.

The left-hand side is the order of vanishing of the fraction `a / b` on `A`, by
`Ring.ordTotalFracInt_mk'`, and each inner difference is its order of vanishing on the `i`-th
component. -/
theorem natCast_ord_sub_eq_finsum_components_mul
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {ι : Type*}
    (a b : A) (ha : IsSMulRegular A a) (hb : IsSMulRegular A b) (hdim : ringKrullDim A = 1)
    (hfinitea : Module.length A (A ⧸ Ideal.span {a}) ≠ ⊤)
    (hfiniteb : Module.length A (A ⧸ Ideal.span {b}) ≠ ⊤)
    (I : ι → Ideal A) (hItop : ∀ i, I i ≠ ⊤)
    (hred : ∀ i, _root_.IsReduced (A ⧸ I i))
    (hdimI : ∀ i, ringKrullDim (A ⧸ I i) = 1)
    (c : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A} → ι)
    (hc : ∀ (i : ι) (q : PrimeSpectrum A),
      q.asIdeal ∈ (I i).minimalPrimes ↔ ∃ h : q.asIdeal ∈ minimalPrimes A, c ⟨q, h⟩ = i)
    (m : ι → ℤ)
    (hm : ∀ q, ((Module.length (Localization.AtPrime q.1.asIdeal)
      (Localization.AtPrime q.1.asIdeal)).toNat : ℤ) = m (c q)) :
    ((Ring.ord A a).toNat : ℤ) - ((Ring.ord A b).toNat : ℤ) =
      ∑ᶠ i : ι, m i * (((Ring.ord (A ⧸ I i) (Ideal.Quotient.mk (I i) a)).toNat : ℤ) -
        ((Ring.ord (A ⧸ I i) (Ideal.Quotient.mk (I i) b)).toNat : ℤ)) := by
  classical
  have _ := finite_branches A
  have _ : Finite ι := Finite.of_surjective c (surjective_component_of_minimalPrimes I hItop c hc)
  let _ : Fintype ι := Fintype.ofFinite _
  rw [natCast_length_quotient_span_eq_finsum_components_mul a ha hdim hfinitea I hItop hred hdimI
      c hc m hm,
    natCast_length_quotient_span_eq_finsum_components_mul b hb hdim hfiniteb I hItop hred hdimI
      c hc m hm,
    finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end AlgebraicGeometry

end
