module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.OrderMinimalPrimes
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MinimalPrimeOrderQuotientTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatChartSectionOrderTransport

/-!
# The order of vanishing of a fraction, summed over the components through a point

Let `O` be a one-dimensional Noetherian local ring, the local ring of an étale chart of a
possibly non-reduced algebraic space `X` at a point over the generic point of a prime divisor.
For a unit `f` of its total ring of fractions, Stacks 02QG with `I = 0` reads

  `ord_O(f) = ∑_{𝔭 ⊂ O minimal} length(O_𝔭) · ord_{O/𝔭}(f)`.

When the minimal primes of `O` are grouped according to the irreducible components `X_j` of `X`
on which their points lie — `O → O_j` being the surjection onto the local ring of the
corresponding chart of the reduced component, whose kernel is contained exactly in the minimal
primes lying on `X_j`, and `length(O_𝔭) = m_j` for those — this becomes

  `ord_O(f) = ∑_j m_j · ord_{O_j}(f)`,

which is the ring-theoretic content of the component sum in Stacks 0EQA and Stacks 0EQQ.

## Main definitions

* `Ring.minimalPrimeLength`: the length of the localization of `O` at a minimal prime, as an
  integer.

## Main results

* `Ring.ord_toNat_eq_finsum_minimalPrimeLength_mul`: Stacks 02QG with `I = 0`, for a
  nonzerodivisor.
* `Ring.ordTotalFracInt_eq_finsum_minimalPrimeLength_mul_minimalPrimeOrd`: the displayed form of
  Stacks 02QG with `I = 0`, for a fraction.
* `Ring.ordTotalFracInt_eq_finsum_mul_ordTotalFracInt_of_surjective`: the grouped form.
* `Ring.ordTotalFracInt_map_of_flatHom_toNat`: along a flat local homomorphism the order of a unit
  of the total ring of fractions multiplies by the colength, read through `ENat.toNat`.

## References

* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

universe u

namespace Ring

variable {O : Type u} [CommRing O]

/-- The length of the localization of `O` at a minimal prime, as an integer: the multiplicity of
the branch through that minimal prime. -/
def minimalPrimeLength (p : minimalPrimes O) : ℤ :=
  haveI : (p : Ideal O).IsPrime := p.2.1.1
  ((Module.length (Localization.AtPrime (p : Ideal O))
    (Localization.AtPrime (p : Ideal O))).toNat : ℤ)

variable [IsNoetherianRing O] [IsLocalRing O]

/-- **Stacks 02QG for `I = 0`, on an element, with integer orders.** For a nonzerodivisor `x` of a
one-dimensional Noetherian local ring, `ord_O(x) = ∑_𝔭 length(O_𝔭) · ord_{O/𝔭}(x)`, the sum over
the minimal primes. -/
theorem ord_toNat_eq_finsum_minimalPrimeLength_mul (hdim : ringKrullDim O = 1) {x : O}
    (hx : x ∈ O⁰) :
    ((Ring.ord O x).toNat : ℤ) =
      ∑ᶠ p : minimalPrimes O, minimalPrimeLength p *
        ((Ring.ord (O ⧸ (p : Ideal O)) (Ideal.Quotient.mk (p : Ideal O) x)).toNat : ℤ) := by
  classical
  have : Ring.KrullDimLE 1 O := Stacks.Chow.krullDimLE_one_of_ringKrullDim_eq_one hdim
  have : Fintype (minimalPrimes O) := (minimalPrimes.finite_of_isNoetherianRing O).fintype
  have h := Stacks.Chow.ord_eq_finsum_minimalPrimes_mul_length hdim hx
  let g : minimalPrimes O → PrimeSpectrum O := fun p => ⟨p, p.2.1.1⟩
  have hg : Function.Injective g := fun p q hpq =>
    Subtype.ext (congrArg PrimeSpectrum.asIdeal hpq)
  have himage : {q : PrimeSpectrum O | q.asIdeal ∈ minimalPrimes O} = g '' Set.univ := by
    ext q
    exact ⟨fun hq => ⟨⟨q.asIdeal, hq⟩, Set.mem_univ _, rfl⟩, by rintro ⟨p, -, rfl⟩; exact p.2⟩
  rw [himage, finsum_mem_image hg.injOn, finsum_mem_univ, finsum_eq_sum_of_fintype] at h
  have hne := Ring.ord_ne_top hx
  rw [h] at hne
  have htop := ENat.sum_ne_top.mp hne
  rw [h, ENat.toNat_sum htop, Nat.cast_sum, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ENat.toNat_mul, Nat.cast_mul, mul_comm]
  rfl

variable {K : Type u} [CommRing K] [Algebra O K] [IsFractionRing O K]

/-- **Stacks 02QG for `I = 0`, on a fraction.** For a unit `f` of the total ring of fractions of
a one-dimensional Noetherian local ring `O`,

`ord_O(f) = ∑_{𝔭 ⊂ O minimal} length(O_𝔭) · ord_{O/𝔭}(f)`. -/
theorem ordTotalFracInt_eq_finsum_minimalPrimeLength_mul_minimalPrimeOrd
    [Ring.KrullDimLE 1 O] (hdim : ringKrullDim O = 1) (f : K) (hf : IsUnit f) :
    ordTotalFracInt O f hf =
      ∑ᶠ p : minimalPrimes O, minimalPrimeLength p * minimalPrimeOrd p f hf := by
  classical
  obtain ⟨a, b, rfl⟩ := exists_mk'_eq_of_isUnit (A := O) hf
  have : Fintype (minimalPrimes O) := (minimalPrimes.finite_of_isNoetherianRing O).fintype
  rw [ordTotalFracInt_mk' O a b hf, ord_toNat_eq_finsum_minimalPrimeLength_mul hdim a.2,
    ord_toNat_eq_finsum_minimalPrimeLength_mul hdim b.2, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [minimalPrimeOrd_mk', mul_sub]

/-- **The order of vanishing of a fraction as a sum over the components through the point.** Let
`O` be a one-dimensional Noetherian local ring and let `π_j : O → O_j`, for `j` in a finite index
set, be surjections onto reduced one-dimensional Noetherian local rings, carrying nonzerodivisors
to nonzerodivisors and under which the minimal primes of `O_j` contract to minimal primes of `O`.
Suppose every minimal prime `𝔭` of `O` contains the kernel of exactly one `π_j`, and that then
`length(O_𝔭) = m_j`. Then for every unit `f` of the total ring of fractions of `O`

`ord_O(f) = ∑_j m_j · ord_{O_j}(π_j(f))`. -/
theorem ordTotalFracInt_eq_finsum_mul_ordTotalFracInt_of_surjective
    [Ring.KrullDimLE 1 O] (hdim : ringKrullDim O = 1)
    {J : Type*} [Finite J] (O' : J → Type u) [∀ j, CommRing (O' j)] [∀ j, IsLocalRing (O' j)]
    [∀ j, IsNoetherianRing (O' j)] [∀ j, IsReduced (O' j)]
    (hdim' : ∀ j, ringKrullDim (O' j) = 1)
    (π : ∀ j, O →+* O' j) (hsurj : ∀ j, Function.Surjective (π j))
    (hnzd : ∀ j, O⁰ ≤ (O' j)⁰.comap (π j))
    (hmin : ∀ j, ∀ I ∈ minimalPrimes (O' j), Ideal.comap (π j) I ∈ minimalPrimes O)
    (m : J → ℤ) (hcover : ∀ p : minimalPrimes O, ∃! j, RingHom.ker (π j) ≤ (p : Ideal O))
    (hlen : ∀ (p : minimalPrimes O) (j : J), RingHom.ker (π j) ≤ (p : Ideal O) →
      minimalPrimeLength p = m j)
    (f : K) (hf : IsUnit f) :
    haveI : ∀ j, Ring.KrullDimLE 1 (O' j) := fun j =>
      Ring.krullDimLE_iff.mpr (by rw [hdim' j]; exact_mod_cast le_rfl)
    ordTotalFracInt O f hf =
      ∑ᶠ j : J, m j * ordTotalFracInt (O' j)
        (IsLocalization.map (S := K) (FractionRing (O' j)) (π j) (hnzd j) f) (hf.map _) := by
  classical
  have : ∀ j, Ring.KrullDimLE 1 (O' j) := fun j =>
    Stacks.Chow.krullDimLE_one_of_ringKrullDim_eq_one (hdim' j)
  have : Fintype (minimalPrimes O) := (minimalPrimes.finite_of_isNoetherianRing O).fintype
  have : Fintype J := Fintype.ofFinite J
  have hterm : ∀ j : J, ordTotalFracInt (O' j)
        (IsLocalization.map (S := K) (FractionRing (O' j)) (π j) (hnzd j) f) (hf.map _) =
      ∑ p ∈ Finset.univ.filter (fun p : minimalPrimes O => RingHom.ker (π j) ≤ (p : Ideal O)),
        minimalPrimeOrd p f hf := by
    intro j
    rw [ordTotalFracInt_eq_finsum_minimalPrimeOrd (hdim' j),
      finsum_minimalPrimeOrd_map_of_surjective (K := K) (K' := FractionRing (O' j)) (π j)
        (hsurj j) (hnzd j) (hmin j) f hf]
    have : Fintype {p : minimalPrimes O // RingHom.ker (π j) ≤ (p : Ideal O)} :=
      Fintype.ofFinite _
    rw [finsum_eq_sum_of_fintype]
    exact (Finset.sum_subtype
      (Finset.univ.filter (fun p : minimalPrimes O => RingHom.ker (π j) ≤ (p : Ideal O)))
      (fun p => by simp) (fun p => minimalPrimeOrd p f hf)).symm
  choose jf hjf using hcover
  have hfilter : ∀ j : J,
      Finset.univ.filter (fun p : minimalPrimes O => RingHom.ker (π j) ≤ (p : Ideal O)) =
        Finset.univ.filter (fun p : minimalPrimes O => jf p = j) := by
    intro j
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ((hjf p).2 j h).symm, fun h => h ▸ (hjf p).1⟩
  rw [ordTotalFracInt_eq_finsum_minimalPrimeLength_mul_minimalPrimeOrd hdim,
    finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp_rw [hterm, hfilter, Finset.mul_sum]
  rw [← Finset.sum_fiberwise Finset.univ jf]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p hp => ?_
  rw [hlen p j ((Finset.mem_filter.1 hp).2 ▸ (hjf p).1)]

/-- **The order of vanishing of a unit multiplies by the colength along a flat local
homomorphism, with no finiteness hypothesis.** For a flat local homomorphism `φ : A ⟶ A'` of
one-dimensional Noetherian local rings and a unit `x` of `Q(A)`,

`ord_{A'}(φ x) = length_{A'}(A'/𝔪_A A') · ord_A(x)`,

the colength being read as a natural number through `ENat.toNat`. -/
theorem ordTotalFracInt_map_of_flatHom_toNat {A A' : Type*} [CommRing A] [CommRing A']
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    [IsNoetherianRing A'] [IsLocalRing A'] [Ring.KrullDimLE 1 A']
    {Q : Type*} [CommRing Q] [Algebra A Q] [IsFractionRing A Q]
    {Q' : Type*} [CommRing Q'] [Algebra A' Q'] [IsFractionRing A' Q']
    {φ : A →+* A'} (hloc : IsLocalHom φ) (hflat : φ.Flat) (x : Q) (hx : IsUnit x) :
    ordTotalFracInt A' (IsLocalization.map (M := A⁰) (T := A'⁰) Q' φ
        (nonZeroDivisors_le_comap_of_flatHom hflat) x)
        (hx.map (IsLocalization.map (M := A⁰) (T := A'⁰) Q' φ
          (nonZeroDivisors_le_comap_of_flatHom hflat))) =
      ((Module.length A' (A' ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A))).toNat : ℤ) *
        ordTotalFracInt A x hx := by
  obtain ⟨a, b, rfl⟩ := exists_mk'_eq_of_isUnit (A := A) hx
  have hmap : IsLocalization.map (M := A⁰) (T := A'⁰) Q' φ
        (nonZeroDivisors_le_comap_of_flatHom hflat) (IsLocalization.mk' Q (a : A) b) =
      IsLocalization.mk' Q' (φ (a : A))
        (⟨φ (b : A), map_mem_nonZeroDivisors_of_flatHom hflat b.2⟩ : A'⁰) :=
    IsLocalization.map_mk' ..
  rw [ordTotalFracInt_congr A' _ (hmap ▸ hx.map _) hmap,
    ordTotalFracInt_mk' A' ⟨_, map_mem_nonZeroDivisors_of_flatHom hflat a.2⟩
      ⟨_, map_mem_nonZeroDivisors_of_flatHom hflat b.2⟩ _, ordTotalFracInt_mk' A a b hx]
  have key (y : A⁰) : ((Ring.ord A' (φ (y : A))).toNat : ℤ) =
      ((Module.length A' (A' ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A))).toNat : ℤ) *
        ((Ring.ord A (y : A)).toNat : ℤ) := by
    rw [ord_map_of_flatHom hloc hflat, ENat.toNat_mul, Nat.cast_mul]
  rw [key a, key b, mul_sub]

end Ring

end
