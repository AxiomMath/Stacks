module

public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange
public import StacksFrontier.RingTheory.Ideal.SymbolicPower
public import StacksFrontier.RingTheory.Serre.Defs

/-!
# Descent of powers along flat local maps of normal domains

Let `A → B` be a flat local homomorphism of Noetherian local normal domains. If every
height-one prime of `A` has a weakly unramified height-one prime of `B` lying over it, then an
element of `A` which becomes an `n`th power up to a unit in `B` was already an `n`th power up to
a unit in `A`, provided `n > 1`.

## Main definitions

There are no new definitions.

## Main results

* `ValuationRing.exists_eq_unit_mul_pow_of_flat_local`: descent of being an `n`th power up to a
  unit.

## Implementation notes

For primes `p` and `q` with `q` lying over `p`, the algebra structure on the local rings is the
canonical one supplied by `Localization.AtPrime.algebraOfLiesOver`. Weak unramifiedness is written
as the equality of its ramification index with one. Under the normal Noetherian domain and
height-one hypotheses, both local rings are discrete valuation rings, so this is exactly weak
unramifiedness of the resulting extension of discrete valuation rings.

## References

* [Stacks, Tag 0ASI](https://stacks.math.columbia.edu/tag/0ASI)
-/

@[expose] public section

namespace ValuationRing

/-- A height-one localization of a Noetherian normal domain is a discrete valuation ring. -/
private theorem isDiscreteValuationRing_at_height_one
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  let R := Localization.AtPrime p
  have : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isLocalization R p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hdim : ringKrullDim R = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p R, hp]
    rfl
  have hnormal : IsNoetherianRing R ∧ IsLocalRing R ∧ IsDomain R ∧
      IsIntegrallyClosed R ∧ ringKrullDim R = 1 :=
    ⟨inferInstance, inferInstance, inferInstance, inferInstance, hdim⟩
  obtain ⟨_, hdvr⟩ := ((isDiscreteValuationRing_tfae R).out 5 1).mp hnormal
  exact hdvr

/-- For an extension of discrete valuation rings, the length-theoretic ramification index of the
maximal ideal of `B` over `A` agrees with the largest power of the maximal ideal of `B` containing
the extension of the maximal ideal of `A`. -/
private theorem ramificationIdx_eq_ramificationIdx'
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)] :
    (IsLocalRing.maximalIdeal B).ramificationIdx A =
      Stacks.DiscreteValuationRing.Ramification.ramificationIdx A B := by
  have : IsDedekindDomain B :=
    ((IsDiscreteValuationRing.TFAE B (IsDiscreteValuationRing.not_isField B)).out 1 3).mp ‹_›
  have : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_prime A
  have hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≠ ⊥ := by
    intro hbot
    have hmem : algebraMap A B π ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B) :=
      Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal π).mpr hπ.irreducible.not_isUnit)
    rw [hbot, Ideal.mem_bot] at hmem
    exact hπ.ne_zero (FaithfulSMul.algebraMap_injective A B (by simpa using hmem))
  rw [Stacks.DiscreteValuationRing.Ramification.ramificationIdx_def]
  exact (Ideal.ramificationIdx'_eq_ramificationIdx' _ _ hmap).symm

/-- When the ramification index is one, a uniformizer of `A` maps to a unit multiple of any
uniformizer of `B`. -/
private theorem exists_unit_mul_uniformizer_of_ramificationIdx_eq_one
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)]
    (he : (IsLocalRing.maximalIdeal B).ramificationIdx A = 1)
    {π : A} (hπ : Irreducible π) {ρ : B} (hρ : Irreducible ρ) :
    ∃ t : Bˣ, algebraMap A B π = (t : B) * ρ := by
  have hval : IsDiscreteValuationRing.addVal B (algebraMap A B π) =
      IsDiscreteValuationRing.addVal B ρ := by
    rw [Stacks.DiscreteValuationRing.Ramification.addVal_algebraMap_eq_ramificationIdx A B π hπ,
      ← ramificationIdx_eq_ramificationIdx' A B, he,
      IsDiscreteValuationRing.addVal_uniformizer hρ, Nat.cast_one]
  obtain ⟨u, hu⟩ := (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mp hval
  exact ⟨u⁻¹, by rw [← hu, mul_comm]; simp⟩

/-- If a nonzero element maps to a unit times an `n`th power, `n ≠ 0`, the base of the power is
nonzero. -/
private theorem ne_zero_of_map_eq_unit_mul_pow
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [FaithfulSMul A B]
    {f : A} (hf : f ≠ 0) {n : ℕ} (hn : n ≠ 0) {h : B} {w : Bˣ}
    (hfh : algebraMap A B f = (w : B) * h ^ n) : h ≠ 0 := by
  rintro rfl
  exact hf (FaithfulSMul.algebraMap_injective A B (by simpa [hn] using hfh))

/-- Powers up to units descend along extensions of DVRs with ramification index one. -/
private theorem exists_associated_pow_of_ramificationIdx_eq_one
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)]
    (he : (IsLocalRing.maximalIdeal B).ramificationIdx A = 1)
    (n : ℕ) (hn : 0 < n) (f : A) (h : B) (w : Bˣ)
    (hfh : algebraMap A B f = (w : B) * h ^ n) :
    ∃ a : A, Associated f (a ^ n) := by
  by_cases hf : f = 0
  · exact ⟨0, by simp [hf, Nat.ne_of_gt hn]⟩
  have hh : h ≠ 0 := ne_zero_of_map_eq_unit_mul_pow hf (Nat.ne_of_gt hn) hfh
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_prime A
  obtain ⟨ρ, hρ⟩ := IsDiscreteValuationRing.exists_prime B
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf hπ.irreducible
  obtain ⟨k, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hh hρ.irreducible
  obtain ⟨t, ht'⟩ := exists_unit_mul_uniformizer_of_ramificationIdx_eq_one A B he
    hπ.irreducible hρ.irreducible
  have hm : m = k * n := by
    have hval := congrArg (IsDiscreteValuationRing.addVal B) hfh
    rw [hu, map_mul, map_pow, ht', hv] at hval
    simp only [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit,
      IsDiscreteValuationRing.addVal_uniformizer hρ.irreducible,
      nsmul_eq_mul, zero_add, mul_one] at hval
    have humap : IsDiscreteValuationRing.addVal B (algebraMap A B (u : A)) = 0 :=
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (u.isUnit.map (algebraMap A B))
    rw [humap, zero_add] at hval
    exact_mod_cast (hval.trans (mul_comm _ _))
  refine ⟨π ^ k, ?_⟩
  rw [hu, hm, pow_mul]
  exact associated_unit_mul_left _ _ u.isUnit

/-- Divisibility by a nonzero element is detected at height-one localizations. -/
private theorem dvd_of_forall_height_one
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {f a : A} (hf : f ≠ 0)
    (hd : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
      algebraMap A (Localization.AtPrime p) f ∣ algebraMap A (Localization.AtPrime p) a) :
    f ∣ a := by
  by_contra h
  have ha : Ideal.Quotient.mk (Ideal.span {f}) a ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using h
  obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ ha
  have : p.IsPrime := hp.isPrime
  have hheight := (associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot
    (FractionRing A)).1 f hf p hp |>.2
  have hamem : algebraMap A (Localization.AtPrime p) a ∈
      (Ideal.span {f}).map (algebraMap A (Localization.AtPrime p)) := by
    simpa only [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] using hd p hheight
  obtain ⟨s, hs, hsa⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
    (Localization.AtPrime p) (Ideal.span {f}) a).mp hamem
  exact hs (hle (by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    change Ideal.Quotient.mk (Ideal.span {f}) (s * a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hsa))

/-- Flat extension preserves intersections indexed by an arbitrary finite type. -/
private theorem map_iInf_of_flat_of_finite
    {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Finite ι] (I : ι → Ideal A) :
    (⨅ i, I i).map (algebraMap A B) = ⨅ i, (I i).map (algebraMap A B) := by
  classical
  let := Fintype.ofFinite ι
  rw [← (Fintype.equivFin ι).symm.iInf_comp (g := I), Ideal.map_iInf_of_flat]
  exact (Fintype.equivFin ι).symm.iInf_comp (g := fun i => (I i).map (algebraMap A B))

/-- An ideal whose faithfully flat extension to a local domain is nonzero and principal
is itself principal. -/
private theorem exists_eq_span_singleton_of_map_eq_span_singleton
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain B] [IsLocalRing B]
    [Algebra A B] [Module.FaithfullyFlat A B]
    (I : Ideal A) {h : B} (hh : h ≠ 0)
    (hI : I.map (algebraMap A B) = Ideal.span {h}) :
    ∃ g : A, I = Ideal.span {g} := by
  have hmem : h ∈ I.map (algebraMap A B) := hI.symm ▸ Ideal.mem_span_singleton_self h
  have hcoeff : ∀ b ∈ I.map (algebraMap A B),
      ∃ c : B, b = h * c ∧
        (IsUnit c → ∃ g ∈ I, Associated (algebraMap A B g) h) := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨g, hg, rfl⟩ := hb
      obtain ⟨c, hc⟩ : h ∣ algebraMap A B g := Ideal.mem_span_singleton.mp
        (hI ▸ Ideal.mem_map_of_mem (algebraMap A B) hg)
      exact ⟨c, hc, fun hunit => ⟨g, hg, hc ▸ associated_mul_unit_left h c hunit⟩⟩
    | zero => exact ⟨0, (mul_zero h).symm, fun hzero => (not_isUnit_zero hzero).elim⟩
    | add x y hx hy hx' hy' =>
      obtain ⟨c, hc, hcu⟩ := hx'
      obtain ⟨d, hd, hdu⟩ := hy'
      exact ⟨c + d, by rw [hc, hd, mul_add],
        fun hunit => (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hunit).elim hcu hdu⟩
    | smul r x hx hx' =>
      obtain ⟨c, hc, hcu⟩ := hx'
      exact ⟨r * c, by rw [smul_eq_mul, hc, mul_left_comm],
        fun hunit => hcu (isUnit_of_mul_isUnit_right hunit)⟩
  obtain ⟨c, hc, hcu⟩ := hcoeff h hmem
  have hc1 : c = 1 := mul_left_cancel₀ hh (hc.symm.trans (mul_one h).symm)
  obtain ⟨g, hg, hassoc⟩ := hcu (hc1 ▸ isUnit_one)
  refine ⟨g, Ideal.map_injective_of_faithfullyFlat (B := B) ?_⟩
  rw [hI, Ideal.map_span, Set.image_singleton]
  exact (Ideal.span_singleton_eq_span_singleton.mpr hassoc).symm

/-- A root upstairs belongs to the extension of a contracted local root ideal. -/
private theorem root_mem_extended_local_ideal
    {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [Algebra A B] [FaithfulSMul A B] [Module.Flat A B]
    (p : Ideal A) [p.IsPrime] (n : ℕ) (hn : n ≠ 0)
    (f : A) (h : B) (w : Bˣ) (hfh : algebraMap A B f = (w : B) * h ^ n)
    (a : Localization.AtPrime p)
    (ha : Associated (algebraMap A (Localization.AtPrime p) f) (a ^ n)) :
    h ∈ ((Ideal.span {a}).comap (algebraMap A (Localization.AtPrime p))).map
      (algebraMap A B) := by
  let M := Algebra.algebraMapSubmonoid B p.primeCompl
  let C := Localization M
  have hM : M ≤ nonZeroDivisors B := by
    rintro _ ⟨r, hr, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro hzero
    have hr0 : r = 0 := FaithfulSMul.algebraMap_injective A B (by simpa using hzero)
    exact hr (hr0 ▸ p.zero_mem)
  have : IsDomain C := IsLocalization.isDomain_of_le_nonZeroDivisors C hM
  have : IsIntegrallyClosed C := isIntegrallyClosed_of_isLocalization C M hM
  rw [map_comap_eq_comap_map_of_flat (A := Localization.AtPrime p) (B := C)
      p.primeCompl (inferInstance : Module.Flat A B),
    Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  have ha' := ha.map (algebraMap (Localization.AtPrime p) C)
  have heq : algebraMap (Localization.AtPrime p) C
      (algebraMap A (Localization.AtPrime p) f) =
      algebraMap B C ((w : B) * h ^ n) := by
    rw [← IsScalarTower.algebraMap_apply A (Localization.AtPrime p) C,
      IsScalarTower.algebraMap_apply A B C, hfh]
  rw [heq, map_mul, map_pow, map_pow] at ha'
  exact ((Associated.pow_iff hn).mp
    ((associated_isUnit_mul_left_iff (w.isUnit.map (algebraMap B C))).mp ha')).symm.dvd

/-- Only finitely many height-one primes contain a fixed nonzero element. -/
private theorem finite_height_one_support
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {f : A} (hf : f ≠ 0) :
    {p : Ideal A | p.IsPrime ∧ p.height = 1 ∧ f ∈ p}.Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {f})).subset ?_
  intro p hp
  have : p.IsPrime := hp.1
  apply Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).mpr hp.2.2)
  rw [hp.2.1]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hf)

/-- The intersection of the contracted local root ideals extends to the principal root ideal. -/
private theorem map_intersection_local_root_ideals
    {A B ι : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [FaithfulSMul A B] [Module.Flat A B] [Finite ι]
    (n : ℕ) (hn : n ≠ 0) (f : A) (hf : f ≠ 0) (h : B) (w : Bˣ)
    (hfh : algebraMap A B f = (w : B) * h ^ n)
    (primes : ι → Ideal A) [∀ i, (primes i).IsPrime]
    (hprimes : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → f ∈ p →
      ∃ i, primes i = p)
    (roots : ∀ i, Localization.AtPrime (primes i))
    (hroots : ∀ i, Associated (algebraMap A (Localization.AtPrime (primes i)) f)
      (roots i ^ n)) :
    (⨅ i, (Ideal.span {roots i}).comap
      (algebraMap A (Localization.AtPrime (primes i)))).map (algebraMap A B) =
      Ideal.span {h} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    apply (IsIntegrallyClosed.pow_dvd_pow_iff hn).mp
    have hfa : f ∣ a ^ n := dvd_of_forall_height_one hf fun p hp hheight => by
      by_cases hfp : f ∈ p
      · obtain ⟨i, rfl⟩ := hprimes p hheight hfp
        have hai : roots i ∣ algebraMap A (Localization.AtPrime (primes i)) a :=
          Ideal.mem_span_singleton.mp ((Ideal.mem_iInf.mp ha) i)
        rw [map_pow]
        exact (hroots i).dvd_iff_dvd_left.mpr (pow_dvd_pow_of_dvd hai n)
      · exact (IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p) ⟨f, hfp⟩).dvd
    have hfa' := map_dvd (algebraMap A B) hfa
    rw [map_pow, hfh] at hfa'
    exact (dvd_mul_left (h ^ n) (w : B)).trans hfa'
  · rw [Ideal.span_singleton_le_iff_mem, map_iInf_of_flat_of_finite, Ideal.mem_iInf]
    intro i
    exact root_mem_extended_local_ideal (primes i) n hn f h w hfh (roots i) (hroots i)

/-- Faithfully flat extension reflects association of elements. -/
private theorem associated_of_associated_map
    {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.FaithfullyFlat A B] {f g : A}
    (h : Associated (algebraMap A B f) (algebraMap A B g)) : Associated f g := by
  apply Ideal.span_singleton_eq_span_singleton.mp
  apply Ideal.map_injective_of_faithfullyFlat (B := B)
  simpa only [Ideal.map_span, Set.image_singleton] using
    Ideal.span_singleton_eq_span_singleton.mpr h


/-- Let `A → B` be a flat local homomorphism of Noetherian local normal domains. Suppose every
height-one prime of `A` has a weakly unramified height-one prime of `B` lying over it. If an
element of `A` becomes an `n`th power times a unit in `B`, for `n > 1`, then it is already an
`n`th power times a unit in `A`. -/
@[stacks 0ASI]
theorem exists_eq_unit_mul_pow_of_flat_local
    (A B : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsLocalRing B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Flat A B] [IsLocalHom (algebraMap A B)]
    (n : ℕ) (hn : 1 < n) (f : A) (h : B) (w : Bˣ)
    (hfh : algebraMap A B f = (w : B) * h ^ n)
    (hunramified : ∀ (p : Ideal A) (hp : p.IsPrime), p.height = 1 →
      ∃ (q : Ideal B) (hq : q.IsPrime), q.height = 1 ∧
        ∃ hlo : q.LiesOver p,
          (letI : p.IsPrime := hp
           letI : q.IsPrime := hq
           letI : q.LiesOver p := hlo
           letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
             Localization.AtPrime.algebraOfLiesOver p q
           (IsLocalRing.maximalIdeal (Localization.AtPrime q)).ramificationIdx
             (Localization.AtPrime p) = 1)) :
    ∃ (g : A) (u : Aˣ), f = (u : A) * g ^ n := by
  classical
  have hn0 : n ≠ 0 := by omega
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  by_cases hf : f = 0
  · exact ⟨0, 1, by simp [hf, hn0]⟩
  have hh : h ≠ 0 := ne_zero_of_map_eq_unit_mul_pow hf hn0 hfh
  let P := {p : Ideal A // p.IsPrime ∧ p.height = 1 ∧ f ∈ p}
  have : Finite P := (finite_height_one_support hf).to_subtype
  let primes : P → Ideal A := Subtype.val
  have (i : P) : (primes i).IsPrime := i.property.1
  have hlocal : ∀ i : P, ∃ a : Localization.AtPrime (primes i),
      Associated (algebraMap A (Localization.AtPrime (primes i)) f) (a ^ n) := by
    intro i
    let p := primes i
    obtain ⟨q, hq, hqh, hlo, he⟩ := hunramified p inferInstance i.property.2.1
    have : q.IsPrime := hq
    have : q.LiesOver p := hlo
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
    have : IsDiscreteValuationRing (Localization.AtPrime p) :=
      isDiscreteValuationRing_at_height_one p i.property.2.1
    have : IsDiscreteValuationRing (Localization.AtPrime q) :=
      isDiscreteValuationRing_at_height_one q hqh
    have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
      change IsLocalHom (Localization.localRingHom p q (algebraMap A B) Ideal.LiesOver.over)
      infer_instance
    have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
      RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr ‹Module.Flat A B›)
        q p Ideal.LiesOver.over
    have : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime q) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    apply exists_associated_pow_of_ramificationIdx_eq_one
      (Localization.AtPrime p) (Localization.AtPrime q) he n
      (by omega) (algebraMap A (Localization.AtPrime p) f)
      (algebraMap B (Localization.AtPrime q) h)
      (Units.map (algebraMap B (Localization.AtPrime q)).toMonoidHom w)
    change algebraMap (Localization.AtPrime p) (Localization.AtPrime q)
      (algebraMap A (Localization.AtPrime p) f) =
        algebraMap B (Localization.AtPrime q) (w : B) *
          (algebraMap B (Localization.AtPrime q) h) ^ n
    rw [← IsScalarTower.algebraMap_apply A (Localization.AtPrime p) (Localization.AtPrime q),
      IsScalarTower.algebraMap_apply A B (Localization.AtPrime q), hfh, map_mul, map_pow]
  choose roots hroots using hlocal
  let I : Ideal A := ⨅ i, (Ideal.span {roots i}).comap
    (algebraMap A (Localization.AtPrime (primes i)))
  have hI : I.map (algebraMap A B) = Ideal.span {h} :=
    map_intersection_local_root_ideals n hn0 f hf h w hfh primes
      (fun p hp hheight hfp => ⟨⟨p, hp, hheight, hfp⟩, rfl⟩) roots hroots
  obtain ⟨g, hg⟩ := exists_eq_span_singleton_of_map_eq_span_singleton I hh hI
  have hgh : Associated (algebraMap A B g) h := by
    apply Ideal.span_singleton_eq_span_singleton.mp
    simpa only [hg, Ideal.map_span, Set.image_singleton] using hI
  have hfg : Associated f (g ^ n) := by
    apply associated_of_associated_map (B := B)
    rw [map_pow, hfh]
    exact (associated_unit_mul_left (h ^ n) (w : B) w.isUnit).trans (hgh.pow_pow (n := n)).symm
  obtain ⟨u, hu⟩ := hfg.symm
  exact ⟨g, u, hu.symm.trans (mul_comm _ _)⟩

end ValuationRing
