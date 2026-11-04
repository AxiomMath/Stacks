module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.OrderMinimalPrimes
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOrderOfVanishing

/-!
# The order of vanishing on a total ring of fractions, compared and split over minimal primes

This file collects the commutative algebra behind the computation of the order of vanishing
along a prime divisor of an algebraic space on an arbitrary étale chart, the input of the key
formula of Stacks 0EQV.

Let `O` be a reduced Noetherian local ring of dimension one, not necessarily a domain. For a
unit `f` of the total ring of fractions `Q(O)`,

`ord_O(f) = ∑_{𝔭 minimal} ord_{O/𝔭}(f mod 𝔭)`,

where `f mod 𝔭` is the image of `f` in the fraction field of the one-dimensional local domain
`O/𝔭`. This is the reduced case of Stacks 02QG for `I = 0`
(`Stacks.Chow.ord_toNat_eq_finsum_minimalPrimes`), extended to fractions.

The second ingredient is a transport principle: two total rings of fractions whose rings map to
a common ring `C` by maps carrying nonzerodivisors to nonzerodivisors and leaving `Ring.ord`
unchanged compute the same order of vanishing on two fractions with the same image in `Q(C)`.
No Noetherianness of `C` is needed, since `Ring.ord` is additive on products with a
nonzerodivisor in any ring. The maps arising in practice are flat local homomorphisms with
`𝔪_A B = 𝔪_B`, for which `Ring.ord` is unchanged by Stacks 02M1
(`Ring.ord_map_of_flatHom`).

## Main definitions

* `Ring.minimalPrimeFractionMap`: the map `Q(O) → Frac(O/𝔭)` at a minimal prime `𝔭`.
* `Ring.minimalPrimeOrd`: the order of vanishing of the image of a unit of `Q(O)` in
  `Frac(O/𝔭)`, along the one-dimensional local domain `O/𝔭`.

## Main results

* `Ring.ordTotalFracInt_eq_finsum_minimalPrimeOrd`: the displayed formula.
* `Ring.ordTotalFracInt_eq_of_map_eq`: the transport principle.
* `Ring.ord_map_of_flat_of_map_maximalIdeal`: a flat local homomorphism with `𝔪_A B = 𝔪_B`
  leaves `Ring.ord` unchanged.

## References

* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped nonZeroDivisors

universe u

namespace Ring

/-! ### Fractions of nonzerodivisors -/

/-- A unit of a total ring of fractions is a fraction of two nonzerodivisors. -/
theorem exists_mk'_eq_of_isUnit {A : Type*} [CommRing A] {K : Type*} [CommRing K] [Algebra A K]
    [IsFractionRing A K] {f : K} (hf : IsUnit f) :
    ∃ a b : A⁰, IsLocalization.mk' K (a : A) b = f := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective A⁰ f
  have hspec : f * algebraMap A K (b : A) = algebraMap A K a := by
    rw [← hab]
    exact IsLocalization.mk'_spec K a b
  have hu : IsUnit (algebraMap A K a) := hspec ▸ hf.mul (IsLocalization.map_units K b)
  have key : ∀ x : A, x * a = 0 → x = 0 := fun x hx ↦
    IsFractionRing.injective A K (by
      rw [map_zero]
      refine hu.mul_left_eq_zero.mp ?_
      rw [← map_mul, hx, map_zero])
  exact ⟨⟨a, mem_nonZeroDivisors_iff.mpr ⟨fun x hx ↦ key x (by rw [mul_comm]; exact hx), key⟩⟩,
    b, hab⟩

/-! ### Transport of the order of vanishing along maps preserving it -/

/-- **The order of vanishing is read off any ring the two local rings map to compatibly, up to
a unit.** Let `φ : A → C` and `φ' : A' → C` carry nonzerodivisors to nonzerodivisors and leave
`Ring.ord` unchanged, and let `f ∈ Q(A)^*`, `f' ∈ Q(A')^*` have images in `Q(C)` differing by a
unit of `C`. Then `ord_A(f) = ord_{A'}(f')`.

Writing `f = a / b` and `f' = a' / b'`, the hypothesis says `φ'(b') φ(a) = φ(b) (w φ'(a'))` in
`C`, and `Ring.ord` turns that into an identity of lengths, additive in any ring on products with
a nonzerodivisor (`Ring.ord_mul`) and blind to unit factors. No Noetherianness of `C` is
needed. -/
theorem ordTotalFracInt_eq_of_map_eq_mul
    {A : Type*} [CommRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Nontrivial A]
    {A' : Type*} [CommRing A'] [IsNoetherianRing A'] [Ring.KrullDimLE 1 A'] [Nontrivial A']
    {C : Type*} [CommRing C]
    {K : Type*} [CommRing K] [Algebra A K] [IsFractionRing A K]
    {K' : Type*} [CommRing K'] [Algebra A' K'] [IsFractionRing A' K']
    {L : Type*} [CommRing L] [Algebra C L] [IsFractionRing C L]
    (φ : A →+* C) (φ' : A' →+* C) (hφ : A⁰ ≤ C⁰.comap φ) (hφ' : A'⁰ ≤ C⁰.comap φ')
    (hord : ∀ x, Ring.ord C (φ x) = Ring.ord A x)
    (hord' : ∀ x, Ring.ord C (φ' x) = Ring.ord A' x)
    {f : K} (hf : IsUnit f) {f' : K'} (hf' : IsUnit f') {w : C} (hw : IsUnit w)
    (h : IsLocalization.map (S := K) L φ hφ f =
      algebraMap C L w * IsLocalization.map (S := K') L φ' hφ' f') :
    ordTotalFracInt A f hf = ordTotalFracInt A' f' hf' := by
  obtain ⟨a, b, rfl⟩ := exists_mk'_eq_of_isUnit (A := A) hf
  obtain ⟨a', b', rfl⟩ := exists_mk'_eq_of_isUnit (A := A') hf'
  rw [ordTotalFracInt_mk' A a b hf, ordTotalFracInt_mk' A' a' b' hf']
  rw [IsLocalization.map_mk', IsLocalization.map_mk', IsLocalization.mul_mk'_eq_mk'_of_mul,
    IsLocalization.mk'_eq_iff_eq] at h
  have hC : φ' (b' : A') * φ (a : A) = φ (b : A) * (w * φ' (a' : A')) :=
    IsFractionRing.injective C L h
  have hb : φ (b : A) ∈ C⁰ := hφ b.2
  have hb' : φ' (b' : A') ∈ C⁰ := hφ' b'.2
  have hlen := congrArg (Ring.ord C) hC
  rw [Ring.ord_mul' C hb', Ring.ord_mul' C hb, Ring.ord_mul_of_isUnit_left hw, hord, hord,
    hord', hord'] at hlen
  rw [← ENat.natCast_toNat (Ring.ord_ne_top a.2), ← ENat.natCast_toNat (Ring.ord_ne_top b.2),
    ← ENat.natCast_toNat (Ring.ord_ne_top a'.2),
    ← ENat.natCast_toNat (Ring.ord_ne_top b'.2)] at hlen
  norm_cast at hlen
  omega

/-- **The order of vanishing is read off any ring the two local rings map to compatibly.** Let
`φ : A → C` and `φ' : A' → C` carry nonzerodivisors to nonzerodivisors and leave `Ring.ord`
unchanged, and let `f ∈ Q(A)^*`, `f' ∈ Q(A')^*` have the same image in `Q(C)`. Then
`ord_A(f) = ord_{A'}(f')`. This is `Ring.ordTotalFracInt_eq_of_map_eq_mul` with the unit `1`. -/
theorem ordTotalFracInt_eq_of_map_eq
    {A : Type*} [CommRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Nontrivial A]
    {A' : Type*} [CommRing A'] [IsNoetherianRing A'] [Ring.KrullDimLE 1 A'] [Nontrivial A']
    {C : Type*} [CommRing C]
    {K : Type*} [CommRing K] [Algebra A K] [IsFractionRing A K]
    {K' : Type*} [CommRing K'] [Algebra A' K'] [IsFractionRing A' K']
    {L : Type*} [CommRing L] [Algebra C L] [IsFractionRing C L]
    (φ : A →+* C) (φ' : A' →+* C) (hφ : A⁰ ≤ C⁰.comap φ) (hφ' : A'⁰ ≤ C⁰.comap φ')
    (hord : ∀ x, Ring.ord C (φ x) = Ring.ord A x)
    (hord' : ∀ x, Ring.ord C (φ' x) = Ring.ord A' x)
    {f : K} (hf : IsUnit f) {f' : K'} (hf' : IsUnit f')
    (h : IsLocalization.map (S := K) L φ hφ f = IsLocalization.map (S := K') L φ' hφ' f') :
    ordTotalFracInt A f hf = ordTotalFracInt A' f' hf' :=
  ordTotalFracInt_eq_of_map_eq_mul φ φ' hφ hφ' hord hord' hf hf' isUnit_one
    (by rw [(algebraMap C L).map_one, one_mul]; exact h)

/-- **A flat local homomorphism with `𝔪_A B = 𝔪_B` leaves the order of vanishing unchanged.**
This is Stacks 02M1 (`Ring.ord_map_of_flatHom`): the order is multiplied by the colength of
`𝔪_A B`, which is one. -/
theorem ord_map_of_flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] {φ : A →+* B} (hloc : IsLocalHom φ) (hflat : φ.Flat)
    (hmax : (maximalIdeal A).map φ = maximalIdeal B) (x : A) :
    Ring.ord B (φ x) = Ring.ord A x := by
  rw [ord_map_of_flatHom hloc hflat, hmax]
  have : Module.length B (B ⧸ maximalIdeal B) = 1 :=
    Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_isCoatom.mpr (maximalIdeal.isMaximal B).out)
  rw [this, one_mul]

/-- The order of vanishing of the image in a total ring of fractions of a unit of the ring is
zero. -/
theorem ordTotalFracInt_algebraMap_of_isUnit {A : Type*} [CommRing A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] [Nontrivial A] {K : Type*} [CommRing K] [Algebra A K]
    [IsFractionRing A K] {u : A} (hu : IsUnit u) (hu' : IsUnit (algebraMap A K u)) :
    ordTotalFracInt A (algebraMap A K u) hu' = 0 := by
  rw [ordTotalFracInt_congr A hu' (IsLocalization.map_units K (⟨u, hu.mem_nonZeroDivisors⟩ : A⁰))
    rfl, ordTotalFracInt_algebraMap A u hu.mem_nonZeroDivisors, Ring.ord_of_isUnit hu]
  rfl

/-! ### The order of vanishing over the minimal primes -/

section MinimalPrimes

variable {O : Type u} [CommRing O]
variable {K : Type*} [CommRing K] [Algebra O K] [IsFractionRing O K]

/-- A nonzerodivisor of `O` has nonzerodivisor image in `O/𝔭` for a minimal prime `𝔭`: it lies
outside `𝔭`, minimal primes consisting of zerodivisors, and `O/𝔭` is a domain. -/
theorem nonZeroDivisors_le_comap_quotient_minimalPrimes (p : minimalPrimes O) :
    O⁰ ≤ (O ⧸ (p : Ideal O))⁰.comap (Ideal.Quotient.mk (p : Ideal O)) := by
  intro x hx
  have : (p : Ideal O).IsPrime := p.2.1.1
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact fun hxp ↦ notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hxp p.2 hx

/-- **The reading of a fraction modulo a minimal prime.** The map `Q(O) → Frac(O/𝔭)` induced by
the quotient map at a minimal prime `𝔭` of `O`. -/
def minimalPrimeFractionMap (p : minimalPrimes O) : K →+* FractionRing (O ⧸ (p : Ideal O)) :=
  IsLocalization.map _ (Ideal.Quotient.mk (p : Ideal O))
    (nonZeroDivisors_le_comap_quotient_minimalPrimes p)

/-- The map `Q(O) → Frac(O/𝔭)` sends `a / b` to `(a mod 𝔭) / (b mod 𝔭)`. -/
theorem minimalPrimeFractionMap_mk' (p : minimalPrimes O) (a : O) (b : O⁰) :
    minimalPrimeFractionMap (K := K) p (IsLocalization.mk' K a b) =
      IsLocalization.mk' (FractionRing (O ⧸ (p : Ideal O))) (Ideal.Quotient.mk (p : Ideal O) a)
        (⟨Ideal.Quotient.mk (p : Ideal O) (b : O),
          nonZeroDivisors_le_comap_quotient_minimalPrimes p b.2⟩ : (O ⧸ (p : Ideal O))⁰) :=
  IsLocalization.map_mk' ..

/-- The quotient of a ring of Krull dimension at most one is again of Krull dimension at most
one. -/
theorem krullDimLE_one_quotient [Ring.KrullDimLE 1 O] (I : Ideal O) :
    Ring.KrullDimLE 1 (O ⧸ I) :=
  Ring.krullDimLE_iff.mpr ((ringKrullDim_quotient_le I).trans (Ring.krullDimLE_iff.mp ‹_›))

variable [IsNoetherianRing O] [Ring.KrullDimLE 1 O]

/-- **The order of vanishing along the branch through a minimal prime.** For a unit `f` of the
total ring of fractions of `O` and a minimal prime `𝔭`, the order of vanishing of the image of
`f` in the fraction field of the Noetherian local domain `O/𝔭` of dimension at most one. -/
def minimalPrimeOrd (p : minimalPrimes O) (f : K) (hf : IsUnit f) : ℤ :=
  have : (p : Ideal O).IsPrime := p.2.1.1
  have := krullDimLE_one_quotient (O := O) (p : Ideal O)
  ordTotalFracInt (O ⧸ (p : Ideal O)) (minimalPrimeFractionMap p f) (hf.map _)

/-- On a fraction `a / b` of nonzerodivisors the order of vanishing along the branch through a
minimal prime is the difference of the lengths of `(O/𝔭)/(a)` and `(O/𝔭)/(b)`. -/
theorem minimalPrimeOrd_mk' (p : minimalPrimes O) (a b : O⁰)
    (hf : IsUnit (IsLocalization.mk' K (a : O) b)) :
    minimalPrimeOrd p (IsLocalization.mk' K (a : O) b) hf =
      ((Ring.ord (O ⧸ (p : Ideal O)) (Ideal.Quotient.mk (p : Ideal O) (a : O))).toNat : ℤ) -
        ((Ring.ord (O ⧸ (p : Ideal O)) (Ideal.Quotient.mk (p : Ideal O) (b : O))).toNat : ℤ) := by
  have : (p : Ideal O).IsPrime := p.2.1.1
  have := krullDimLE_one_quotient (O := O) (p : Ideal O)
  have hcongr := minimalPrimeFractionMap_mk' (K := K) p (a : O) b
  have hu' := hcongr ▸ hf.map (minimalPrimeFractionMap (K := K) p)
  unfold minimalPrimeOrd
  refine (ordTotalFracInt_congr _ _ hu' hcongr).trans ?_
  exact ordTotalFracInt_mk' (O ⧸ (p : Ideal O))
    ⟨_, nonZeroDivisors_le_comap_quotient_minimalPrimes p a.2⟩
    ⟨_, nonZeroDivisors_le_comap_quotient_minimalPrimes p b.2⟩ _

/-- The order of vanishing along the branch through a minimal prime depends neither on the
proof that the function is a unit nor on its representative. -/
theorem minimalPrimeOrd_congr (p : minimalPrimes O) {f g : K} (hf : IsUnit f) (hg : IsUnit g)
    (h : f = g) : minimalPrimeOrd p f hf = minimalPrimeOrd p g hg := by
  subst h
  rfl

/-- **The order of vanishing over the minimal primes of a reduced ring.** Let `O` be a reduced
Noetherian local ring of dimension one, and `f` a unit of its total ring of fractions. Then the
order of vanishing of `f` is the sum, over the minimal primes `𝔭` of `O`, of the order of
vanishing of the image of `f` in the fraction field of the one-dimensional local domain `O/𝔭`.

For a fraction `f = a / b` of nonzerodivisors this is the difference of two instances of the
reduced case of Stacks 02QG (`Stacks.Chow.ord_toNat_eq_finsum_minimalPrimes`), the sums being
finite because a Noetherian ring has finitely many minimal primes. -/
theorem ordTotalFracInt_eq_finsum_minimalPrimeOrd [IsLocalRing O] [IsReduced O]
    (hdim : ringKrullDim O = 1) (f : K) (hf : IsUnit f) :
    ordTotalFracInt O f hf = ∑ᶠ p : minimalPrimes O, minimalPrimeOrd p f hf := by
  obtain ⟨a, b, rfl⟩ := exists_mk'_eq_of_isUnit (A := O) hf
  rw [ordTotalFracInt_mk' O a b hf,
    Stacks.Chow.ord_toNat_eq_finsum_minimalPrimes hdim a.2,
    Stacks.Chow.ord_toNat_eq_finsum_minimalPrimes hdim b.2]
  have hfin := minimalPrimes.finite_of_isNoetherianRing O
  have : Fintype (minimalPrimes O) := hfin.fintype
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_eq_sum_of_fintype, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_coe_sort hfin.toFinset]
  refine Finset.sum_equiv (Equiv.subtypeEquivRight fun p ↦ by simp) (by simp) fun p _ ↦ ?_
  rw [minimalPrimeOrd_mk']
  rfl

end MinimalPrimes

end Ring

end
