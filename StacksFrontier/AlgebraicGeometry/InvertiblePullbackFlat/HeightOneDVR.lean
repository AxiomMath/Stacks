module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.Algebra
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.NormalDomain
public import StacksFrontier.RingTheory.Ideal.SymbolicPower
import StacksCore.Tactic.StacksAttribute

/-!
# The discrete valuation rings at the height-one primes over a principal ideal

The affine step in the proof of Stacks Tag 0BD7 chooses the minimal primes
`𝔭₁, …, 𝔭ₙ` over an element `r r'` of a Noetherian normal domain `R`, and reads valuations in
the local rings `R_{𝔭ᵢ}` and in the local rings `A_{𝔮ᵢ}` of the faithfully flat `R`-algebra `A`
at `𝔮ᵢ = 𝔭ᵢ A`. This file produces those two families of discrete valuation rings.

Downstairs this is the source's appeal to Algebra, Lemmas 00KV and 031S: Krull's principal ideal
theorem pins the height of a minimal prime over a nonzero principal ideal at `1`, and a
localization of a Noetherian normal domain is again a Noetherian normal domain, so item (5) of
Tag 00PD — a Noetherian local normal domain of Krull dimension one is a discrete valuation
ring — applies. Taking that route through item (5) rather than through regularity means Serre's
criterion (Tag 031S) is not needed at all; the height bound and normality suffice.

Upstairs this is the source's appeal to Algebra, Lemma 00PD together with its remark that
`R_{𝔭ᵢ} → A_{𝔮ᵢ}` has ramification index `1`. Faithful flatness gives
`(𝔭 A).comap = 𝔭`, hence a comparison map `R_𝔭 → A_{𝔭A}` of local rings, injective because `A`
is a domain; and the maximal ideal of `A_{𝔭A}` is the extension of the maximal ideal of `R_𝔭`
along it, which is the hypothesis of `isDiscreteValuationRing_of_maximalIdeal_eq_map`. The
unramifiedness the source records is then
`IsDiscreteValuationRing.addVal_algebraMap maximalIdeal_map_localizationAtPrimeMap`, with the
algebra structure `Ideal.localizationAtPrimeAlgebra`.

## Main definitions

* `Ideal.localizationAtPrimeMap`: the map `R_𝔭 → A_{𝔭A}` of local rings induced by a faithfully
  flat algebra, available when `𝔭 A` is prime.
* `Ideal.localizationAtPrimeAlgebra`: the same as an algebra structure, so that the lemmas of
  `StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/Algebra.lean` apply to it.

## Main results

* `Ideal.height_eq_one_of_mem_minimalPrimes_span_singleton`: a prime minimal over a nonzero
  principal ideal of a Noetherian domain has height one.
* `isDiscreteValuationRing_localizationAtPrime_of_height_eq_one`: the localization of a
  Noetherian normal domain at a prime of height one is a discrete valuation ring.
* `isDiscreteValuationRing_localizationAtPrime_map_of_height_eq_one`: and so is the localization
  of a faithfully flat algebra over it at the extension of that prime, when the extension is
  prime.
* `isDiscreteValuationRing_localizationAtPrime_of_mem_minimalPrimes_span_singleton` and
  `isDiscreteValuationRing_localizationAtPrime_map_of_mem_minimalPrimes_span_singleton`: the two
  families as the source selects them, at the minimal primes over a nonzero element.
* `addVal_algebraMap_localizationAtPrime`: the extension `R_𝔭 → A_{𝔭A}` is unramified, so a
  valuation of an element of `R` may be read upstairs or downstairs.
* `Ideal.finsetInf_symbolicPower_eq_span_singleton`: the intersection of the symbolic powers
  `𝔭ᵢ^(eᵢ)` of the minimal primes over a nonzero `f`, with `eᵢ` the valuation of `f` at `𝔭ᵢ`, is
  the principal ideal `(f)`. This is the equality
  `𝔭₁^(e₁ + e'₁) ∩ … ∩ 𝔭ₙ^(eₙ + e'ₙ) = (r r')` of the affine step of Tag 0BD7.

## Implementation notes

The exponents of `Ideal.finsetInf_symbolicPower_eq_span_singleton` are not given as valuations
but by the two conditions `f ∈ 𝔭ᵢ^(eᵢ)` and `f ∉ 𝔭ᵢ^(eᵢ + 1)`, which say the same thing by
`mem_symbolicPower_iff_le_addVal` and need no discrete valuation ring structure in the statement;
`Ideal.exists_mem_symbolicPower_and_notMem_symbolicPower` produces the exponent.

`Ideal.height_eq_one_of_mem_minimalPrimes_span_singleton` is a corollary of two Mathlib lemmas,
`Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes` and
`Ideal.height_eq_zero_iff_eq_bot`. The same statement is already proved in this repository, but
as a `private` theorem in `StacksFrontier/RingTheory/Ideal/PrincipalRadical/Basic.lean`, so it is
not reachable from here; that copy should be made public and this one deleted.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 00KV](https://stacks.math.columbia.edu/tag/00KV)
* [Stacks Project, Tag 00PD](https://stacks.math.columbia.edu/tag/00PD)
* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T)
-/

@[expose] public section

universe u

open IsLocalRing

namespace Ideal

/-- A prime minimal over a nonzero principal ideal of a Noetherian domain has height one: at most
one by Krull's principal ideal theorem, and at least one because it is nonzero. This is item (2)
of Stacks Tag 00KV in the form the affine step of Tag 0BD7 uses it. -/
@[ega "0 16.3.2" "special case", ega "IV 5.2.5" "more general"]
theorem height_eq_one_of_mem_minimalPrimes_span_singleton
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] {f : R} (hf : f ≠ 0)
    {p : Ideal R} (hp : p ∈ (Ideal.span {f}).minimalPrimes) : p.height = 1 := by
  have hprime : p.IsPrime := hp.isPrime
  refine le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {f}) p hp) ?_
  rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
  intro hbot
  exact hf (by simpa [hbot] using hp.1.2 (Ideal.mem_span_singleton_self f))

end Ideal

/-- The localization of a Noetherian normal domain at a prime of height one is a discrete
valuation ring. The localization is again Noetherian, local, a domain and integrally closed, and
its Krull dimension is the height of the prime, so item (5) of Stacks Tag 00PD applies. -/
theorem isDiscreteValuationRing_localizationAtPrime_of_height_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  have hic : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime p) p.primeCompl
      p.primeCompl_le_nonZeroDivisors
  have hdim : ringKrullDim (Localization.AtPrime p) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hp]
    rfl
  have hpack : IsNoetherianRing (Localization.AtPrime p) ∧ IsLocalRing (Localization.AtPrime p) ∧
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) ∧
      ringKrullDim (Localization.AtPrime p) = 1 :=
    ⟨inferInstance, inferInstance, inferInstance, hic, hdim⟩
  obtain ⟨_, hdvr⟩ := ((isDiscreteValuationRing_tfae (Localization.AtPrime p)).out 5 1).mp hpack
  exact hdvr

namespace Ideal

section FaithfullyFlat

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A]
  (p : Ideal R) [p.IsPrime] [(p.map (algebraMap R A)).IsPrime]

/-- Along a faithfully flat algebra the complement of a prime lands in the complement of the
extended prime, because the extension contracts back to the prime it came from. -/
theorem primeCompl_le_comap_primeCompl_map : p.primeCompl ≤
    Submonoid.comap (algebraMap R A) (p.map (algebraMap R A)).primeCompl :=
  Localization.le_comap_primeCompl_iff.mpr
    (ge_of_eq (Ideal.comap_map_eq_self_of_faithfullyFlat (B := A) p).symm)

/-- The map `R_𝔭 → A_{𝔭A}` of local rings induced by a faithfully flat algebra `A`, when the
extension `𝔭 A` is prime. This is the extension `R_{𝔭ᵢ} → A_{𝔮ᵢ}` of the affine step of Stacks
Tag 0BD7. -/
noncomputable def localizationAtPrimeMap :
    Localization.AtPrime p →+* Localization.AtPrime (p.map (algebraMap R A)) :=
  Localization.localRingHom p (p.map (algebraMap R A)) (algebraMap R A)
    (Ideal.comap_map_eq_self_of_faithfullyFlat (B := A) p).symm

/-- `Ideal.localizationAtPrimeMap` as an algebra structure. It is deliberately not an instance:
the extension `𝔭 A` being prime is a hypothesis, not something instance search should guess. -/
@[instance_reducible]
noncomputable def localizationAtPrimeAlgebra :
    Algebra (Localization.AtPrime p) (Localization.AtPrime (p.map (algebraMap R A))) :=
  (localizationAtPrimeMap (A := A) p).toAlgebra

/-- The comparison `R_𝔭 → A_{𝔭A}` is injective: a fraction killed upstairs is killed by an
element outside `𝔭 A`, which is nonzero because `A` is a domain, and `R → A` is injective. -/
theorem localizationAtPrimeMap_injective [IsDomain A] :
    Function.Injective (localizationAtPrimeMap (R := R) (A := A) p) :=
  IsLocalization.map_injective_of_injective' p.primeCompl A
    (Localization.AtPrime (p.map (algebraMap R A)))
    (primeCompl_le_comap_primeCompl_map (A := A) p)
    (fun hc => hc (p.map (algebraMap R A)).zero_mem) (FaithfulSMul.algebraMap_injective R A)

/-- The comparison `R_𝔭 → A_{𝔭A}` is compatible with the two localization maps out of `R`. -/
theorem localizationAtPrimeMap_comp_algebraMap :
    (localizationAtPrimeMap (R := R) (A := A) p).comp
        (algebraMap R (Localization.AtPrime p)) =
      (algebraMap A (Localization.AtPrime (p.map (algebraMap R A)))).comp (algebraMap R A) :=
  RingHom.ext fun x => Localization.localRingHom_to_map p (p.map (algebraMap R A))
    (algebraMap R A) (Ideal.comap_map_eq_self_of_faithfullyFlat (B := A) p).symm x

/-- The maximal ideal of `A_{𝔭A}` is the extension of the maximal ideal of `R_𝔭`. Both are the
extension of `𝔭` itself, along the two sides of the commuting square. -/
theorem maximalIdeal_map_localizationAtPrimeMap :
    (maximalIdeal (Localization.AtPrime p)).map (localizationAtPrimeMap (R := R) (A := A) p) =
      maximalIdeal (Localization.AtPrime (p.map (algebraMap R A))) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p), Ideal.map_map,
    localizationAtPrimeMap_comp_algebraMap, ← Ideal.map_map,
    Localization.AtPrime.map_eq_maximalIdeal (I := p.map (algebraMap R A))]

/-- The algebra structure `Ideal.localizationAtPrimeAlgebra` is faithful. -/
private theorem faithfulSMul_localizationAtPrimeAlgebra [IsDomain A] :
    letI := localizationAtPrimeAlgebra (A := A) p
    FaithfulSMul (Localization.AtPrime p) (Localization.AtPrime (p.map (algebraMap R A))) := by
  let := localizationAtPrimeAlgebra (A := A) p
  exact (faithfulSMul_iff_algebraMap_injective _ _).mpr (localizationAtPrimeMap_injective p)

end FaithfullyFlat

end Ideal

section Upstairs

variable {R A : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
  [CommRing A] [IsDomain A] [IsNoetherianRing A] [Algebra R A] [Module.FaithfullyFlat R A]
  (p : Ideal R) [p.IsPrime] [(p.map (algebraMap R A)).IsPrime]

/-- The localization of a Noetherian domain, faithfully flat over a Noetherian normal domain `R`,
at the extension of a height-one prime of `R`, is a discrete valuation ring — provided that
extension is prime, which in Stacks Tag 0BD7 comes from the fibres of the morphism being
integral. The maximal ideal upstairs is the extension of a uniformizer downstairs, so this is
item (4) implies item (1) of Stacks Tag 00PD, and the extension is unramified. -/
theorem isDiscreteValuationRing_localizationAtPrime_map_of_height_eq_one (hp : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime (p.map (algebraMap R A))) := by
  have : IsDiscreteValuationRing (Localization.AtPrime p) :=
    isDiscreteValuationRing_localizationAtPrime_of_height_eq_one p hp
  let _ := Ideal.localizationAtPrimeAlgebra (A := A) p
  have := Ideal.faithfulSMul_localizationAtPrimeAlgebra (A := A) p
  exact isDiscreteValuationRing_of_maximalIdeal_eq_map
    (Ideal.maximalIdeal_map_localizationAtPrimeMap p)

end Upstairs

section MinimalPrimes

variable {R A : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
  {f : R} {p : Ideal R}

/-- At a prime minimal over a nonzero principal ideal of a Noetherian normal domain, the local
ring is a discrete valuation ring. These are the rings `R_{𝔭ᵢ}` of the affine step of Stacks
Tag 0BD7, where `f = r r'`. -/
theorem isDiscreteValuationRing_localizationAtPrime_of_mem_minimalPrimes_span_singleton
    [p.IsPrime] (hf : f ≠ 0) (hp : p ∈ (Ideal.span {f}).minimalPrimes) :
    IsDiscreteValuationRing (Localization.AtPrime p) :=
  isDiscreteValuationRing_localizationAtPrime_of_height_eq_one p
    (Ideal.height_eq_one_of_mem_minimalPrimes_span_singleton hf hp)

/-- And so are the local rings `A_{𝔮ᵢ}` upstairs, at `𝔮ᵢ = 𝔭ᵢ A`. -/
theorem isDiscreteValuationRing_localizationAtPrime_map_of_mem_minimalPrimes_span_singleton
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [Algebra R A] [Module.FaithfullyFlat R A]
    [p.IsPrime] [(p.map (algebraMap R A)).IsPrime] (hf : f ≠ 0)
    (hp : p ∈ (Ideal.span {f}).minimalPrimes) :
    IsDiscreteValuationRing (Localization.AtPrime (p.map (algebraMap R A))) :=
  isDiscreteValuationRing_localizationAtPrime_map_of_height_eq_one p
    (Ideal.height_eq_one_of_mem_minimalPrimes_span_singleton hf hp)

end MinimalPrimes

section Valuations

/-- In a discrete valuation ring, membership in the `n`-th power of the maximal ideal is the
valuation bound `n ≤ v x`: the power is generated by `π ^ n`, and divisibility by `π ^ n` is that
bound. -/
theorem mem_maximalIdeal_pow_iff_le_addVal {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (n : ℕ) (x : R) :
    x ∈ maximalIdeal R ^ n ↔ (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal R x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, hπ.addVal_pow]

/-- At a prime whose local ring is a discrete valuation ring, the symbolic power `𝔭^{(n)}` is cut
out by the valuation: `x ∈ 𝔭^{(n)}` exactly when the valuation of `x` at `𝔭` is at least `n`.

This is what lets the affine step of Stacks Tag 0BD7 read its exponents `eᵢ`, `e'ᵢ` off the
valuations and conclude that `a` lies in the intersection of the symbolic powers. -/
theorem mem_symbolicPower_iff_le_addVal {R : Type u} [CommRing R] [IsDomain R] (p : Ideal R)
    [p.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime p)] (n : ℕ) (x : R) :
    x ∈ symbolicPower' p n ↔
      (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal (Localization.AtPrime p)
        (algebraMap R (Localization.AtPrime p) x) := by
  rw [mem_symbolicPower_iff_mem_pow_map, Localization.AtPrime.map_eq_maximalIdeal,
    mem_maximalIdeal_pow_iff_le_addVal]

/-- The extension `R_𝔭 → A_{𝔭A}` of discrete valuation rings produced by a faithfully flat
algebra is unramified: the valuation of an element of `R` is the same read in `A_{𝔭A}` as in
`R_𝔭`. This is the source's "of course `R_{𝔭ᵢ} → A_{𝔮ᵢ}` has ramification index `1`". -/
theorem addVal_algebraMap_localizationAtPrime
    {R A : Type u} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Algebra R A] [Module.FaithfullyFlat R A]
    (p : Ideal R) [p.IsPrime] [(p.map (algebraMap R A)).IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime p)]
    [IsDiscreteValuationRing (Localization.AtPrime (p.map (algebraMap R A)))]
    (z : R) :
    IsDiscreteValuationRing.addVal (Localization.AtPrime (p.map (algebraMap R A)))
        (algebraMap A (Localization.AtPrime (p.map (algebraMap R A))) (algebraMap R A z))
      = IsDiscreteValuationRing.addVal (Localization.AtPrime p)
        (algebraMap R (Localization.AtPrime p) z) := by
  let _ := Ideal.localizationAtPrimeAlgebra (A := A) p
  have := Ideal.faithfulSMul_localizationAtPrimeAlgebra (A := A) p
  have key := IsDiscreteValuationRing.addVal_algebraMap
    (Ideal.maximalIdeal_map_localizationAtPrimeMap (R := R) (A := A) p)
    (algebraMap R (Localization.AtPrime p) z)
  have hcomm : Ideal.localizationAtPrimeMap (A := A) p
      (algebraMap R (Localization.AtPrime p) z)
      = algebraMap A (Localization.AtPrime (p.map (algebraMap R A))) (algebraMap R A z) :=
    RingHom.congr_fun (Ideal.localizationAtPrimeMap_comp_algebraMap (R := R) (A := A) p) z
  rw [RingHom.algebraMap_toAlgebra, hcomm] at key
  exact key

end Valuations

section SymbolicPowers

namespace Ideal

/-- A prime of height one containing a nonzero element `f` of a Noetherian domain is one of the
minimal primes over `(f)`: it contains such a minimal prime, which already has height one, so the
two coincide. -/
theorem mem_minimalPrimes_span_singleton_of_height_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] {f : R} (hf : f ≠ 0)
    {p : Ideal R} [p.IsPrime] (hfp : f ∈ p) (hp : p.height = 1) :
    p ∈ (Ideal.span {f}).minimalPrimes := by
  obtain ⟨q, hq, hqp⟩ :=
    Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := p)
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfp))
  have := hq.isPrime
  have hq1 : q.height = 1 := Ideal.height_eq_one_of_mem_minimalPrimes_span_singleton hf hq
  have : q.FiniteHeight := q.finiteHeight_iff.mpr (Or.inr (by simp [hq1]))
  have hqe : q = p := Ideal.eq_of_le_of_height_le q hqp (by rw [hp, hq1])
  exact hqe ▸ hq

/-- Divisibility in the localization of a domain at a prime, written out over the ring: if `f`
divides `x` in `R_𝔭` then `s x = f y` for some `y ∈ R` and some `s ∉ 𝔭`. This is the shape in
which `Ideal.mem_span_singleton_iff_forall_height_one` asks for local divisibility. -/
theorem exists_mul_eq_of_dvd_algebraMap {R : Type u} [CommRing R] [IsDomain R]
    (p : Ideal R) [p.IsPrime] {f x : R}
    (h : algebraMap R (Localization.AtPrime p) f ∣ algebraMap R (Localization.AtPrime p) x) :
    ∃ y s : R, s ∉ p ∧ s * x = f * y := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨s, y, hy⟩ := IsLocalization.exists_integer_multiple p.primeCompl c
  refine ⟨y, s, s.2, IsLocalization.injective (Localization.AtPrime p)
    p.primeCompl_le_nonZeroDivisors ?_⟩
  rw [map_mul, map_mul, hc, hy, Algebra.smul_def]
  ring

/-- A nonzero element of a domain lies in a largest symbolic power of a prime whose local ring is
a discrete valuation ring, namely the one whose exponent is its valuation there. This is how the
affine step of Stacks Tag 0BD7 chooses its exponents `eᵢ`, `e'ᵢ`. -/
theorem exists_mem_symbolicPower_and_notMem_symbolicPower
    {R : Type u} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime p)] {f : R} (hf : f ≠ 0) :
    ∃ e : ℕ, f ∈ symbolicPower' p e ∧ f ∉ symbolicPower' p (e + 1) := by
  have hne : algebraMap R (Localization.AtPrime p) f ≠ 0 := fun hc =>
    hf (IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors
      (by simpa using hc))
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp
    (fun hc => hne (IsDiscreteValuationRing.addVal_eq_top_iff.mp hc))
  refine ⟨e, (mem_symbolicPower_iff_le_addVal p e f).mpr he.le, fun hc => ?_⟩
  have := (mem_symbolicPower_iff_le_addVal p (e + 1) f).mp hc
  rw [← he] at this
  exact absurd (by exact_mod_cast this) (by omega)

/-- The two conditions `x ∈ 𝔭^(n)` and `x ∉ 𝔭^(n + 1)` say that `n` is the valuation of `x` in
the discrete valuation ring `R_𝔭`. -/
theorem addVal_eq_of_mem_symbolicPower_of_notMem {R : Type u} [CommRing R] [IsDomain R]
    (p : Ideal R) [p.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime p)] {n : ℕ} {x : R}
    (hmem : x ∈ symbolicPower' p n) (hmax : x ∉ symbolicPower' p (n + 1)) :
    IsDiscreteValuationRing.addVal (Localization.AtPrime p)
      (algebraMap R (Localization.AtPrime p) x) = (n : ℕ∞) := by
  have hlow := (mem_symbolicPower_iff_le_addVal p n x).mp hmem
  have hnot : ¬ ((n + 1 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal (Localization.AtPrime p)
      (algebraMap R (Localization.AtPrime p) x) := fun hc =>
    hmax ((mem_symbolicPower_iff_le_addVal p (n + 1) x).mpr hc)
  push_cast at hnot
  exact le_antisymm (Order.le_of_lt_add_one (not_le.mp hnot)) hlow

/-- Symbolic powers of one prime multiply as the ordinary powers do. -/
theorem symbolicPower_mul_symbolicPower_le {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (m n : ℕ) :
    symbolicPower' p m * symbolicPower' p n ≤ symbolicPower' p (m + n) := by
  refine Ideal.mul_le.mpr fun x hx y hy => ?_
  rw [mem_symbolicPower_iff_mem_pow_map] at hx hy ⊢
  rw [map_mul, pow_add]
  exact Ideal.mul_mem_mul hx hy

/-- **The equality `𝔭₁^(e₁) ∩ … ∩ 𝔭ₙ^(eₙ) = (f)` of the affine step of Stacks Tag 0BD7.** In a
Noetherian normal domain, the intersection of the symbolic powers of the minimal primes over a
nonzero element `f`, taken with the exponents `eᵢ` at which `f` sits in `𝔭ᵢ`, is the principal
ideal generated by `f`.

The exponent condition is `f ∈ 𝔭ᵢ^(eᵢ)` together with `f ∉ 𝔭ᵢ^(eᵢ + 1)`, which by
`mem_symbolicPower_iff_le_addVal` says that `eᵢ` is the valuation of `f` in the discrete
valuation ring `R_{𝔭ᵢ}`; `Ideal.exists_mem_symbolicPower_and_notMem_symbolicPower` supplies it.

One inclusion is then the valuation bound. For the other, a height-one prime `𝔭` of `R` either
avoids `f`, so that `f` is already invertible at `𝔭`, or contains it and is therefore one of the
`𝔭ᵢ`, where the valuation bound gives the divisibility that
`Ideal.mem_span_singleton_iff_forall_height_one` asks for. That route avoids needing that `(f)`
has no embedded primes. -/
theorem finsetInf_symbolicPower_eq_span_singleton
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {ι : Type*} {f : R} (hf : f ≠ 0) (t : Finset ι) (p : ι → Ideal R) [∀ i, (p i).IsPrime]
    (hp : ∀ i ∈ t, p i ∈ (Ideal.span {f}).minimalPrimes)
    (hall : ∀ q ∈ (Ideal.span {f}).minimalPrimes, ∃ i ∈ t, p i = q)
    (e : ι → ℕ)
    (hmem : ∀ i ∈ t, f ∈ symbolicPower' (p i) (e i))
    (hmax : ∀ i ∈ t, f ∉ symbolicPower' (p i) (e i + 1)) :
    (t.inf fun i => symbolicPower' (p i) (e i)) = Ideal.span {f} := by
  refine le_antisymm (fun x hx => ?_)
    (Finset.le_inf fun i hi => Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hmem i hi)))
  rw [Ideal.mem_span_singleton_iff_forall_height_one hf]
  intro q hqprime hq1
  by_cases hfq : f ∈ q
  · obtain ⟨i, hit, rfl⟩ :=
      hall q (mem_minimalPrimes_span_singleton_of_height_eq_one hf hfq hq1)
    have : IsDiscreteValuationRing (Localization.AtPrime (p i)) :=
      isDiscreteValuationRing_localizationAtPrime_of_mem_minimalPrimes_span_singleton hf
        (hp i hit)
    have hfv : IsDiscreteValuationRing.addVal (Localization.AtPrime (p i))
        (algebraMap R (Localization.AtPrime (p i)) f) = (e i : ℕ∞) :=
      addVal_eq_of_mem_symbolicPower_of_notMem (p i) (hmem i hit) (hmax i hit)
    have hxi : x ∈ symbolicPower' (p i) (e i) :=
      Finset.inf_le (f := fun j => symbolicPower' (p j) (e j)) hit hx
    have hxv : (e i : ℕ∞) ≤ IsDiscreteValuationRing.addVal (Localization.AtPrime (p i))
        (algebraMap R (Localization.AtPrime (p i)) x) :=
      (mem_symbolicPower_iff_le_addVal (p i) (e i) x).mp hxi
    exact exists_mul_eq_of_dvd_algebraMap (p i)
      (IsDiscreteValuationRing.addVal_le_iff_dvd.mp (hfv.trans_le hxv))
  · exact ⟨x, f, hfq, by ring⟩

end Ideal

end SymbolicPowers

end
