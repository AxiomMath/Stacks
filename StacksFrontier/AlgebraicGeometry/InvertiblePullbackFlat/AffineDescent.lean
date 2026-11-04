module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.PicardGroup
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.HeightOneDVR
public import StacksFrontier.RingTheory.Ideal.Invertible
import StacksCore.Tactic.StacksAttribute

/-!
# The affine step of Stacks Tag 0BD7, descended from a faithfully flat algebra

Let `R` be a Noetherian normal domain, let `A` be a Noetherian domain which is faithfully flat
over `R`, and let `r r' ∈ R` be nonzero with `a a' ∈ A` satisfying `a a' = r r'`. In Stacks Tag
0BD7 this is the situation produced by a trivializing section `s = a / r` of an invertible module
on `Spec A`, trivial on the generic fibre, with inverse `s⁻¹ = a' / r'`.

Write `𝔭₁, …, 𝔭ₙ` for the minimal primes of `R` over `r r'` and `𝔮ᵢ = 𝔭ᵢ A` for their extensions,
assumed prime. Let `eᵢ` and `e'ᵢ` be the valuations of `a` and `a'` in the discrete valuation ring
`A_{𝔮ᵢ}`, and set

`I = 𝔭₁^(e₁) ∩ … ∩ 𝔭ₙ^(eₙ)` and `I' = 𝔭₁^(e'₁) ∩ … ∩ 𝔭ₙ^(e'ₙ)`.

This file proves the source's conclusion `I I' = (r r')`, that `I` is therefore an invertible
`R`-module, and — when `R` is local, which is how the last paragraph of the source applies the
affine step — that `I = (g)` is principal with `a = u g` for a unit `u` of `A`, so that
`s = u g / r`.

The argument is the source's. The valuations of `a` and `a'` add up to the valuation of `r r'`,
which by unramifiedness of `R_{𝔭ᵢ} → A_{𝔮ᵢ}` may be read downstairs; so
`I I' ⊆ 𝔭₁^(e₁ + e'₁) ∩ … ∩ 𝔭ₙ^(eₙ + e'ₙ) = (r r')` by
`Ideal.finsetInf_symbolicPower_eq_span_singleton`. Extension to `A` commutes with the
intersections and with the symbolic powers, so `a ∈ I A` and `a' ∈ I' A` and therefore
`I A · I' A = (r r') A`; faithful flatness descends both the equality and, by Tag 09ME, the
invertibility.

## Main results

* `IsLocalization.exists_mul_eq_algebraMap_of_isUnit`: the source's `s = a / r` and
  `s⁻¹ = a' / r'`, with `a a' = r r'`. The ring `A ⊗_R K` in which the source works is the
  localization of `A` at the nonzero elements of `R` (`IsLocalization.tensorRight`), so this is
  that step for an arbitrary model of it.
* `Ideal.mul_finsetInf_symbolicPower_eq_span_singleton`: the equality `I I' = (r r')`.
* `Ideal.invertible_finsetInf_symbolicPower`: `I` is an invertible `R`-module.
* `Ideal.isPrincipal_of_invertible_of_isLocalRing`: an invertible ideal of a local ring is
  principal, because the Picard group of a local ring is trivial.
* `Ideal.exists_isUnit_mul_of_finsetInf_symbolicPower`: over a local `R`, a generator `g` of `I`
  with `a = u g` for a unit `u` of `A`.
* `Ideal.exists_isUnit_mul_of_mul_eq_algebraMap`: the same with the exponents chosen rather than
  supplied, so that only the factorisation `a a' = r r'` has to be exhibited.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T)
* [Stacks Project, Tag 0BC0](https://stacks.math.columbia.edu/tag/0BC0)
* [Stacks Project, Tag 0BBY](https://stacks.math.columbia.edu/tag/0BBY)
* [Stacks Project, Tag 09ME](https://stacks.math.columbia.edu/tag/09ME)
-/

@[expose] public section

universe u

open IsLocalRing IsDiscreteValuationRing

namespace IsLocalization

/-- The nonzero elements of a domain `R` stay nonzerodivisors in a domain `A` containing it. -/
theorem algebraMapSubmonoid_le_nonZeroDivisors {R A : Type u} [CommRing R] [IsDomain R]
    [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] :
    Algebra.algebraMapSubmonoid A (nonZeroDivisors R) ≤ nonZeroDivisors A := by
  rintro x ⟨r, hr, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero fun hc =>
    (nonZeroDivisors.ne_zero hr) (FaithfulSMul.algebraMap_injective R A (by simpa using hc))

/-- **The first step of the affine argument of Stacks Tag 0BD7.** A unit `s` of the localization
of a domain `A` at the nonzero elements of a subdomain `R` is a fraction `a / r` with `a ∈ A` and
`0 ≠ r ∈ R`, its inverse is a fraction `a' / r'` of the same shape, and then `a a' = r r'`.

The source states this for `s ∈ A ⊗_R K` with `K` the fraction field of `R`; that ring is such a
localization by `IsLocalization.tensorRight`. -/
theorem exists_mul_eq_algebraMap_of_isUnit {R A B : Type u} [CommRing R] [IsDomain R]
    [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A]
    [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) B]
    {s : B} (hs : IsUnit s) :
    ∃ (a a' : A) (r r' : R), r ≠ 0 ∧ r' ≠ 0 ∧ a * a' = algebraMap R A (r * r') ∧
      algebraMap A B a = algebraMap R B r * s := by
  obtain ⟨⟨a, m, hm⟩, h1⟩ :=
    IsLocalization.surj (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) s
  obtain ⟨⟨a', m', hm'⟩, h2⟩ :=
    IsLocalization.surj (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) (↑hs.unit⁻¹ : B)
  obtain ⟨r, hr, rfl⟩ := hm
  obtain ⟨r', hr', rfl⟩ := hm'
  refine ⟨a, a', r, r', nonZeroDivisors.ne_zero hr, nonZeroDivisors.ne_zero hr', ?_, ?_⟩
  · refine IsLocalization.injective B
      (algebraMapSubmonoid_le_nonZeroDivisors (R := R) (A := A)) ?_
    have hprod : (s * ↑hs.unit⁻¹) * (algebraMap A B (algebraMap R A r) *
        algebraMap A B (algebraMap R A r')) = algebraMap A B a * algebraMap A B a' := by
      rw [← h1, ← h2]; ring
    rw [hs.mul_val_inv, one_mul] at hprod
    simp only [map_mul]
    exact hprod.symm
  · rw [← h1, ← IsScalarTower.algebraMap_apply]
    ring

end IsLocalization

namespace Ideal

/-- An element lying in each symbolic power `𝔭ᵢ^(eᵢ) A` of the extended primes lies in the
extension of `⋂ᵢ 𝔭ᵢ^(eᵢ)`. -/
private theorem mem_map_finsetInf_symbolicPower {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] {ι : Type*} (t : Finset ι) (p : ι → Ideal R)
    [∀ i, (p i).IsPrime] [∀ i, ((p i).map (algebraMap R A)).IsPrime] (e : ι → ℕ) {x : A}
    (h : ∀ i ∈ t, x ∈ symbolicPower' ((p i).map (algebraMap R A)) (e i)) :
    x ∈ (t.inf fun i => symbolicPower' (p i) (e i)).map (algebraMap R A) := by
  rw [map_finsetInf_symbolicPower_of_flat]
  exact (Finset.le_inf fun i hi => Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (h i hi)))
    (Ideal.mem_span_singleton_self x)

section Descent

variable {R A : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
  [CommRing A] [IsDomain A] [IsNoetherianRing A] [Algebra R A] [Module.FaithfullyFlat R A]
  {ι : Type*} {f : R} (t : Finset ι) (p : ι → Ideal R) [∀ i, (p i).IsPrime]
  [∀ i, ((p i).map (algebraMap R A)).IsPrime] {a a' : A} (e e' : ι → ℕ)

/-- The exponents of the affine step add up: if `eᵢ` is the valuation of `a` and `e'ᵢ` that of
`a'` in `A_{𝔮ᵢ}`, and `a a' = f`, then `eᵢ + e'ᵢ` is the valuation of `f` in `R_{𝔭ᵢ}`, because the
extension `R_{𝔭ᵢ} → A_{𝔮ᵢ}` is unramified. -/
theorem mem_symbolicPower_add_and_notMem (hf : f ≠ 0)
    (hp : ∀ i ∈ t, p i ∈ (Ideal.span {f}).minimalPrimes)
    (haa' : a * a' = algebraMap R A f)
    (hea : ∀ i ∈ t, a ∈ symbolicPower' ((p i).map (algebraMap R A)) (e i))
    (hea' : ∀ i ∈ t, a ∉ symbolicPower' ((p i).map (algebraMap R A)) (e i + 1))
    (hfa : ∀ i ∈ t, a' ∈ symbolicPower' ((p i).map (algebraMap R A)) (e' i))
    (hfa' : ∀ i ∈ t, a' ∉ symbolicPower' ((p i).map (algebraMap R A)) (e' i + 1))
    (i : ι) (hi : i ∈ t) :
    f ∈ symbolicPower' (p i) (e i + e' i) ∧
      f ∉ symbolicPower' (p i) (e i + e' i + 1) := by
  have _ : IsDiscreteValuationRing (Localization.AtPrime (p i)) :=
    isDiscreteValuationRing_localizationAtPrime_of_mem_minimalPrimes_span_singleton hf (hp i hi)
  have _ : IsDiscreteValuationRing (Localization.AtPrime ((p i).map (algebraMap R A))) :=
    isDiscreteValuationRing_localizationAtPrime_map_of_mem_minimalPrimes_span_singleton
      (A := A) hf (hp i hi)
  have hvf : addVal (Localization.AtPrime (p i)) (algebraMap R (Localization.AtPrime (p i)) f)
      = ((e i + e' i : ℕ) : ℕ∞) := by
    rw [← addVal_algebraMap_localizationAtPrime (A := A) (p i) f, ← haa', map_mul,
      AddValuation.map_mul,
      addVal_eq_of_mem_symbolicPower_of_notMem _ (hea i hi) (hea' i hi),
      addVal_eq_of_mem_symbolicPower_of_notMem _ (hfa i hi) (hfa' i hi)]
    push_cast
    ring
  refine ⟨(mem_symbolicPower_iff_le_addVal (p i) _ f).mpr (by rw [hvf]), fun hc => ?_⟩
  have hlt := (mem_symbolicPower_iff_le_addVal (p i) (e i + e' i + 1) f).mp hc
  rw [hvf] at hlt
  exact absurd (by exact_mod_cast hlt) (by omega)

/-- **The equality `I I' = (r r')` of the affine step of Stacks Tag 0BD7.** With `I` and `I'` the
intersections of the symbolic powers of the minimal primes over `f` at the valuations of `a` and
`a'`, and `a a' = f`, the product `I I'` is the principal ideal generated by `f`.

The inclusion `I I' ⊆ (f)` is `Ideal.finsetInf_symbolicPower_eq_span_singleton` together with
`mem_symbolicPower_add_and_notMem`. The reverse inclusion is proved upstairs, where
`a ∈ I A` and `a' ∈ I' A` give `f = a a' ∈ I A · I' A`, and descended by faithful flatness. -/
theorem mul_finsetInf_symbolicPower_eq_span_singleton (hf : f ≠ 0)
    (hp : ∀ i ∈ t, p i ∈ (Ideal.span {f}).minimalPrimes)
    (hall : ∀ q ∈ (Ideal.span {f}).minimalPrimes, ∃ i ∈ t, p i = q)
    (haa' : a * a' = algebraMap R A f)
    (hea : ∀ i ∈ t, a ∈ symbolicPower' ((p i).map (algebraMap R A)) (e i))
    (hea' : ∀ i ∈ t, a ∉ symbolicPower' ((p i).map (algebraMap R A)) (e i + 1))
    (hfa : ∀ i ∈ t, a' ∈ symbolicPower' ((p i).map (algebraMap R A)) (e' i))
    (hfa' : ∀ i ∈ t, a' ∉ symbolicPower' ((p i).map (algebraMap R A)) (e' i + 1)) :
    (t.inf fun i => symbolicPower' (p i) (e i)) *
        (t.inf fun i => symbolicPower' (p i) (e' i)) = Ideal.span {f} := by
  have hsum := mem_symbolicPower_add_and_notMem (A := A) t p e e' hf hp haa' hea hea' hfa hfa'
  have hstep6 : (t.inf fun i => symbolicPower' (p i) (e i + e' i)) = Ideal.span {f} :=
    finsetInf_symbolicPower_eq_span_singleton hf t p hp hall (fun i => e i + e' i)
      (fun i hi => (hsum i hi).1) (fun i hi => (hsum i hi).2)
  have hle : (t.inf fun i => symbolicPower' (p i) (e i)) *
      (t.inf fun i => symbolicPower' (p i) (e' i)) ≤ Ideal.span {f} := by
    rw [← hstep6]
    refine Finset.le_inf fun i hi => le_trans (Ideal.mul_mono
      (Finset.inf_le (f := fun j => symbolicPower' (p j) (e j)) hi)
      (Finset.inf_le (f := fun j => symbolicPower' (p j) (e' j)) hi))
      (symbolicPower_mul_symbolicPower_le (p i) (e i) (e' i))
  refine Ideal.map_injective_of_faithfullyFlat (B := A) (le_antisymm ?_ ?_)
  · exact Ideal.map_mono hle
  · rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff,
      Ideal.map_mul, ← haa']
    exact Ideal.mul_mem_mul (mem_map_finsetInf_symbolicPower t p e hea)
      (mem_map_finsetInf_symbolicPower t p e' hfa)

/-- **The ideal `I` of the affine step of Stacks Tag 0BD7 is invertible.** This is the source's
appeal to Algebra, Lemma 09ME, descended from `A` to `R` by faithful flatness. -/
theorem invertible_finsetInf_symbolicPower (hf : f ≠ 0)
    (hp : ∀ i ∈ t, p i ∈ (Ideal.span {f}).minimalPrimes)
    (hall : ∀ q ∈ (Ideal.span {f}).minimalPrimes, ∃ i ∈ t, p i = q)
    (haa' : a * a' = algebraMap R A f)
    (hea : ∀ i ∈ t, a ∈ symbolicPower' ((p i).map (algebraMap R A)) (e i))
    (hea' : ∀ i ∈ t, a ∉ symbolicPower' ((p i).map (algebraMap R A)) (e i + 1))
    (hfa : ∀ i ∈ t, a' ∈ symbolicPower' ((p i).map (algebraMap R A)) (e' i))
    (hfa' : ∀ i ∈ t, a' ∉ symbolicPower' ((p i).map (algebraMap R A)) (e' i + 1)) :
    Module.Invertible R ↥(t.inf fun i => symbolicPower' (p i) (e i)) :=
  Ideal.invertible_of_mul_eq_span_singleton (mem_nonZeroDivisors_of_ne_zero hf)
    (mul_finsetInf_symbolicPower_eq_span_singleton (A := A) t p e e' hf hp hall haa' hea hea'
      hfa hfa')

end Descent

/-- An invertible ideal of a local ring is principal: the Picard group of a local ring is
trivial, so the ideal is free, hence isomorphic to the ring, and a generator is the image of
`1`. This is the source's "Zariski locally on `R` we can write `I = (g)`", in the local form in
which the last paragraph of Stacks Tag 0BD7 uses it. -/
theorem isPrincipal_of_invertible_of_isLocalRing {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) [Module.Invertible R I] : I.IsPrincipal := by
  obtain ⟨φ⟩ := Module.Invertible.free_iff_linearEquiv.mp (inferInstance : Module.Free R I)
  refine ⟨(φ.symm 1 : R), le_antisymm (fun x hx => ?_) ?_⟩
  · have hx' : (⟨x, hx⟩ : I) = φ ⟨x, hx⟩ • φ.symm 1 := by
      rw [← map_smul, smul_eq_mul, mul_one, φ.symm_apply_apply]
    exact Ideal.mem_span_singleton.mpr ⟨φ ⟨x, hx⟩, by
      simpa [mul_comm] using congrArg (Subtype.val (p := fun y => y ∈ I)) hx'⟩
  · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (φ.symm 1).2)

section Local

variable {R A : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
  [IsLocalRing R] [CommRing A] [IsDomain A] [IsNoetherianRing A] [Algebra R A]
  [Module.FaithfullyFlat R A]
  {ι : Type*} {f : R} (t : Finset ι) (p : ι → Ideal R) [∀ i, (p i).IsPrime]
  [∀ i, ((p i).map (algebraMap R A)).IsPrime] {a a' : A} (e e' : ι → ℕ)

/-- **The conclusion of the affine step of Stacks Tag 0BD7 over a local base.** The ideal
`I = 𝔭₁^(e₁) ∩ … ∩ 𝔭ₙ^(eₙ)` is generated by a single element `g`, and `a = u g` for a unit `u`
of `A`; so with `s = a / r` one has `s = u g / r` as the source concludes.

That `u` is a unit is the source's argument: writing `I' = (g')` as well, `g g'` generates `(f)`,
so `a a' = u u' g g'` forces `u u'` to be a unit times `1`. -/
theorem exists_isUnit_mul_of_finsetInf_symbolicPower (hf : f ≠ 0)
    (hp : ∀ i ∈ t, p i ∈ (Ideal.span {f}).minimalPrimes)
    (hall : ∀ q ∈ (Ideal.span {f}).minimalPrimes, ∃ i ∈ t, p i = q)
    (haa' : a * a' = algebraMap R A f)
    (hea : ∀ i ∈ t, a ∈ symbolicPower' ((p i).map (algebraMap R A)) (e i))
    (hea' : ∀ i ∈ t, a ∉ symbolicPower' ((p i).map (algebraMap R A)) (e i + 1))
    (hfa : ∀ i ∈ t, a' ∈ symbolicPower' ((p i).map (algebraMap R A)) (e' i))
    (hfa' : ∀ i ∈ t, a' ∉ symbolicPower' ((p i).map (algebraMap R A)) (e' i + 1)) :
    ∃ (g : R) (u : A), IsUnit u ∧
      (t.inf fun i => symbolicPower' (p i) (e i)) = Ideal.span {g} ∧
      a = u * algebraMap R A g := by
  have hmul := mul_finsetInf_symbolicPower_eq_span_singleton (A := A) t p e e' hf hp hall haa'
    hea hea' hfa hfa'
  have _ := invertible_finsetInf_symbolicPower (A := A) t p e e' hf hp hall haa' hea hea'
    hfa hfa'
  have _ : Module.Invertible R ↥(t.inf fun i => symbolicPower' (p i) (e' i)) :=
    Ideal.invertible_of_mul_eq_span_singleton
      (I := t.inf fun i => symbolicPower' (p i) (e' i))
      (J := t.inf fun i => symbolicPower' (p i) (e i))
      (mem_nonZeroDivisors_of_ne_zero hf) (by rw [mul_comm]; exact hmul)
  obtain ⟨g, hg⟩ := isPrincipal_of_invertible_of_isLocalRing
    (t.inf fun i => symbolicPower' (p i) (e i))
  obtain ⟨g', hg'⟩ := isPrincipal_of_invertible_of_isLocalRing
    (t.inf fun i => symbolicPower' (p i) (e' i))
  rw [hg, hg', Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_eq_span_singleton] at hmul
  obtain ⟨v, hv⟩ := hmul
  have hdiv : ∀ (x : A) (h : R) (J : Ideal R), x ∈ J.map (algebraMap R A) → J = Ideal.span {h} →
      ∃ u : A, x = u * algebraMap R A h := by
    intro x h J hx hJ
    rw [hJ, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hx
    obtain ⟨u, hu⟩ := hx
    exact ⟨u, hu.symm⟩
  obtain ⟨u, hu⟩ := hdiv a g _ (mem_map_finsetInf_symbolicPower t p e hea) hg
  obtain ⟨u', hu'⟩ := hdiv a' g' _ (mem_map_finsetInf_symbolicPower t p e' hfa) hg'
  refine ⟨g, u, ?_, hg, hu⟩
  have hgg' : g * g' ≠ 0 := fun hc => hf (by rw [← hv, hc, zero_mul])
  have hgg'A : algebraMap R A (g * g') ≠ 0 := fun hc =>
    hgg' (FaithfulSMul.algebraMap_injective R A (by simpa using hc))
  have hL : u * u' * algebraMap R A (g * g') = algebraMap R A f := by
    rw [map_mul, ← haa', hu, hu']
    ring
  have hR : algebraMap R A (v : R) * algebraMap R A (g * g') = algebraMap R A f := by
    rw [← map_mul]
    exact congrArg _ (by rw [← hv]; ring)
  have hunit : IsUnit (u * u') := by
    rw [mul_right_cancel₀ hgg'A (hL.trans hR.symm)]
    exact (Units.map (algebraMap R A : R →* A) v).isUnit
  exact isUnit_of_mul_isUnit_left hunit

/-- `Ideal.exists_isUnit_mul_of_finsetInf_symbolicPower` with the exponents chosen rather than
supplied: in the source they are *defined* as the valuations of `a` and `a'`, which
`Ideal.exists_mem_symbolicPower_and_notMem_symbolicPower` produces from `a ≠ 0` and `a' ≠ 0`
alone. This is the affine step of Stacks Tag 0BD7 over a local base in the form a consumer can
apply: all that has to be exhibited is the factorisation `a a' = r r'`. -/
theorem exists_isUnit_mul_of_mul_eq_algebraMap (hf : f ≠ 0) (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hp : ∀ i ∈ t, p i ∈ (Ideal.span {f}).minimalPrimes)
    (hall : ∀ q ∈ (Ideal.span {f}).minimalPrimes, ∃ i ∈ t, p i = q)
    (haa' : a * a' = algebraMap R A f) :
    ∃ (e : ι → ℕ) (g : R) (u : A), IsUnit u ∧
      (t.inf fun i => symbolicPower' (p i) (e i)) = Ideal.span {g} ∧
      a = u * algebraMap R A g := by
  have key : ∀ x : A, x ≠ 0 → ∀ i ∈ t, ∃ n : ℕ,
      x ∈ symbolicPower' ((p i).map (algebraMap R A)) n ∧
      x ∉ symbolicPower' ((p i).map (algebraMap R A)) (n + 1) := by
    intro x hx i hi
    have _ : IsDiscreteValuationRing (Localization.AtPrime ((p i).map (algebraMap R A))) :=
      isDiscreteValuationRing_localizationAtPrime_map_of_mem_minimalPrimes_span_singleton
        (A := A) hf (hp i hi)
    exact exists_mem_symbolicPower_and_notMem_symbolicPower _ hx
  choose! e hea hea' using key a ha
  choose! e' hfa hfa' using key a' ha'
  obtain ⟨g, u, hu, hg, hug⟩ := exists_isUnit_mul_of_finsetInf_symbolicPower (A := A) t p e e'
    hf hp hall haa' hea hea' hfa hfa'
  exact ⟨e, g, u, hu, hg, hug⟩

end Local

end Ideal

end
