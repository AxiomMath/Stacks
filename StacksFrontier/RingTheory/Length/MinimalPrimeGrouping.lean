module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf

/-!
# The colength of a principal ideal, grouped along a partition of the minimal primes

Let `R` be a one-dimensional Noetherian local ring and `a ∈ 𝔪_R` a nonzerodivisor. By
Stacks 02QG the colength of `(a)` is the sum, over the minimal primes `𝔮` of `R`, of
`length(R_𝔮) · length(R ⧸ (a, 𝔮))`. Suppose the minimal primes are partitioned into finitely
many blocks, the block of index `i` being the set of minimal primes of a *radical* ideal `I_i`,
and that `length(R_𝔮)` depends only on the block of `𝔮`, with value `n_i`. Then

  `length(R ⧸ (a)) = ∑_i n_i · length(R ⧸ (a, I_i))`.

## Main results

* `Ideal.IsRadical.isSMulRegular_quotient`: a nonzerodivisor of `R` stays a nonzerodivisor modulo
  a radical ideal all of whose minimal primes are minimal primes of `R`.
* `Ideal.IsRadical.length_localizedModule_quotient_eq_one`: localizing `R ⧸ I` at a minimal prime
  of a radical ideal `I` gives a module of length one.
* `AlgebraicGeometry.natCast_length_quotient_span_sup_eq_finsum_of_isRadical`: Stacks 02QG for
  `R ⧸ I`, with `I` a radical ideal whose minimal primes are minimal primes of `R`.
* `AlgebraicGeometry.natCast_length_quotient_span_eq_finsum_length_quotient_sup`: the grouped form
  of Stacks 02QG.

## References

* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
-/

public section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- The set of primes of `Spec R` which are minimal over an ideal of a Noetherian ring is finite. -/
private theorem finite_setOf_asIdeal_mem_minimalPrimes {R : Type*} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) :
    {q : PrimeSpectrum R | q.asIdeal ∈ I.minimalPrimes}.Finite :=
  (finite_minimalPrimes_of_isNoetherianRing R I).preimage fun _ _ _ _ h => PrimeSpectrum.ext h

/-- A scalar acting injectively on an `R`-algebra has a nonzerodivisor image in it. -/
private theorem algebraMap_mem_nonZeroDivisors_of_isSMulRegular {S : Type*} [CommRing S]
    [Algebra R S] {a : R} (h : IsSMulRegular S a) : algebraMap R S a ∈ nonZeroDivisors S :=
  mem_nonZeroDivisors_iff_left.mpr fun r hr => h (by simpa [Algebra.smul_def, mul_comm] using hr)

/-- **A nonzerodivisor stays a nonzerodivisor modulo a radical ideal whose minimal primes are
minimal primes of the ring.** -/
theorem IsRadical.isSMulRegular_quotient {I : Ideal R} (hI : I.IsRadical)
    (hmin : I.minimalPrimes ⊆ minimalPrimes R) {a : R} (ha : IsSMulRegular R a) :
    IsSMulRegular (R ⧸ I) a := by
  have hmem : ∀ r : R, a * r ∈ I → r ∈ I := by
    intro r hr
    rw [← hI.radical, ← Ideal.sInf_minimalPrimes]
    refine Submodule.mem_sInf.2 fun q hq => ?_
    have hqmin : q ∈ (Module.annihilator R R).minimalPrimes := by
      rw [Module.annihilator_eq_bot.mpr
        ((faithfulSMul_iff_algebraMap_injective R R).mpr fun {_ _} h ↦ h)]
      exact hmin hq
    exact (hq.1.1.mem_or_mem (hq.1.2 hr)).resolve_left (ha.notMem_of_mem_minimalPrimes hqmin)
  intro x y hxy
  induction x using Quotient.inductionOn' with | h x => ?_
  induction y using Quotient.inductionOn' with | h y => ?_
  change Submodule.Quotient.mk (p := I) (a • x) = Submodule.Quotient.mk (p := I) (a • y) at hxy
  refine (Submodule.Quotient.eq I).2 (hmem _ ?_)
  simpa only [smul_eq_mul, mul_sub] using (Submodule.Quotient.eq I).1 hxy

/-- **Localizing `R ⧸ I` at a minimal prime of a radical ideal `I` gives a module of length
one.** -/
theorem IsRadical.length_localizedModule_quotient_eq_one {I : Ideal R} (hI : I.IsRadical)
    {q : Ideal R} (hq : q ∈ I.minimalPrimes) :
    haveI := hq.1.1
    Module.length (Localization.AtPrime q) (LocalizedModule q.primeCompl (R ⧸ I)) = 1 := by
  have := hq.1.1
  set S := Localization.AtPrime q
  set J : Ideal S := I.map (algebraMap R S) with hJ
  have hmaxmin : IsLocalRing.maximalIdeal S ∈ J.minimalPrimes := by
    rw [hJ, IsLocalization.minimalPrimes_map q.primeCompl S I, Set.mem_preimage,
      IsLocalization.AtPrime.comap_maximalIdeal S q]
    exact hq
  have hJmax : J = IsLocalRing.maximalIdeal S := by
    have hrad : J.radical = J := by
      rw [hJ, ← IsLocalization.map_radical q.primeCompl S I, hI.radical]
    rw [← hrad, ← Ideal.sInf_minimalPrimes]
    exact le_antisymm (sInf_le hmaxmin)
      (le_sInf fun P hP => hmaxmin.2 hP.1 (IsLocalRing.le_maximalIdeal hP.1.1.ne_top))
  have hloc : I.localized' S q.primeCompl (Algebra.linearMap R S) = J := by
    rw [Submodule.localized'_eq_span, hJ, Ideal.map]
    rfl
  have e : (S ⧸ I.localized' S q.primeCompl (Algebra.linearMap R S)) ≃ₗ[R]
      LocalizedModule q.primeCompl (R ⧸ I) :=
    IsLocalizedModule.linearEquiv q.primeCompl
      (I.toLocalizedQuotient' S q.primeCompl (Algebra.linearMap R S))
      (LocalizedModule.mkLinearMap q.primeCompl (R ⧸ I))
  rw [← (e.extendScalarsOfIsLocalization q.primeCompl S).length_eq, hloc, hJmax]
  exact Module.length_eq_one_iff.mpr (isSimpleModule_iff_quot_maximal.mpr
    ⟨_, IsLocalRing.maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩)

end Ideal

namespace AlgebraicGeometry

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- **Stacks 02QG for a radical ideal whose minimal primes are minimal primes of `R`.** Let `R` be
a one-dimensional Noetherian local ring, `a ∈ 𝔪_R` a nonzerodivisor of `R` and `I` a radical
ideal whose minimal primes are minimal primes of `R`. Then the colength of `(a) + I` is the sum,
over the minimal primes `𝔮` of `I`, of the colengths of `(a) + 𝔮`. -/
theorem natCast_length_quotient_span_sup_eq_finsum_of_isRadical (a : R)
    (ha : IsSMulRegular R a) (ham : a ∈ IsLocalRing.maximalIdeal R)
    (hdim : ringKrullDim R = 1) (hfinite : Module.length R (R ⧸ Ideal.span {a}) ≠ ⊤)
    (I : Ideal R) (hI : I.IsRadical) (hmin : I.minimalPrimes ⊆ minimalPrimes R) :
    ((Module.length R (R ⧸ (Ideal.span {a} ⊔ I))).toNat : ℤ) =
      ∑ᶠ q : {q : PrimeSpectrum R // q.asIdeal ∈ I.minimalPrimes},
        ((Module.length R (R ⧸ (Ideal.span {a} ⊔ q.1.asIdeal))).toNat : ℤ) := by
  classical
  by_cases htop : I = ⊤
  · subst htop
    have hempty : IsEmpty {q : PrimeSpectrum R // q.asIdeal ∈ (⊤ : Ideal R).minimalPrimes} :=
      ⟨fun q => by simpa [Ideal.minimalPrimes_top] using q.2⟩
    have : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [finsum_of_isEmpty, sup_top_eq, Module.length_eq_zero]
    rfl
  have hreg : IsSMulRegular (R ⧸ I) a := hI.isSMulRegular_quotient hmin ha
  have hdimI : ringKrullDim (R ⧸ I) = 1 := by
    refine le_antisymm ((ringKrullDim_quotient_le I).trans hdim.le) ?_
    have hb : Ideal.Quotient.mk I a ∈ nonZeroDivisors (R ⧸ I) :=
      Ideal.algebraMap_mem_nonZeroDivisors_of_isSMulRegular hreg
    have hle : I ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal htop
    have hproper : Ideal.span {Ideal.Quotient.mk I a} ≠ ⊤ := by
      intro h
      rw [Ideal.span_singleton_eq_top] at h
      obtain ⟨u, hu⟩ := h
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : R ⧸ I)
      have h1 : Ideal.Quotient.mk I (a * b) = 1 := by
        rw [map_mul, hb, ← hu, Units.mul_inv]
      have h2 : a * b - 1 ∈ I := Ideal.Quotient.eq.mp (h1.trans (map_one _).symm)
      have h3 : a * b - 1 ∈ IsLocalRing.maximalIdeal R := hle h2
      have h4 : a * b ∈ IsLocalRing.maximalIdeal R := Ideal.mul_mem_right _ _ ham
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
        ((Ideal.eq_top_iff_one _).mpr (by simpa using Ideal.sub_mem _ h4 h3))
    have : Nontrivial ((R ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I a}) :=
      Ideal.Quotient.nontrivial_iff.mpr hproper
    refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hb)
    simpa only [zero_add, add_comm] using add_le_add_right
      (ringKrullDim_nonneg_of_nontrivial (R := (R ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I a})) 1
  have h := length_quotient_span_sup_eq_sum_minimalPrimes a I hreg hdimI
  have hone : ∀ q ∈ {q : PrimeSpectrum R | q.asIdeal ∈ I.minimalPrimes},
      Module.length R (R ⧸ (Ideal.span {a} ⊔ q.asIdeal)) *
        Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl (R ⧸ I)) =
      Module.length R (R ⧸ (Ideal.span {a} ⊔ q.asIdeal)) := fun q hq => by
    rw [hI.length_localizedModule_quotient_eq_one hq, mul_one]
  rw [finsum_mem_congr rfl hone, ← finsum_set_coe_eq_finsum_mem] at h
  let : Fintype {q : PrimeSpectrum R // q.asIdeal ∈ I.minimalPrimes} :=
    (Ideal.finite_setOf_asIdeal_mem_minimalPrimes I).fintype
  change Module.length R (R ⧸ (Ideal.span {a} ⊔ I)) =
    ∑ᶠ q : {q : PrimeSpectrum R // q.asIdeal ∈ I.minimalPrimes},
      Module.length R (R ⧸ (Ideal.span {a} ⊔ q.1.asIdeal)) at h
  rw [finsum_eq_sum_of_fintype] at h ⊢
  have htot : Module.length R (R ⧸ (Ideal.span {a} ⊔ I)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (Module.length_le_of_surjective
      (Submodule.factor (le_sup_left : Ideal.span {a} ≤ Ideal.span {a} ⊔ I))
      (Submodule.factor_surjective _))
  have hterms : ∀ q ∈ (Finset.univ : Finset {q : PrimeSpectrum R // q.asIdeal ∈ I.minimalPrimes}),
      Module.length R (R ⧸ (Ideal.span {a} ⊔ q.1.asIdeal)) ≠ ⊤ := fun q hq => by
    refine ne_top_of_le_ne_top htot ?_
    rw [h]
    exact Finset.single_le_sum (f := fun q : {q : PrimeSpectrum R // q.asIdeal ∈ I.minimalPrimes} =>
      Module.length R (R ⧸ (Ideal.span {a} ⊔ q.1.asIdeal))) (fun _ _ => zero_le) hq
  rw [h, ENat.toNat_sum hterms, Nat.cast_sum]

/-- **Stacks 02QG, grouped along a partition of the minimal primes.** Let `R` be a
one-dimensional Noetherian local ring and `a ∈ 𝔪_R` a nonzerodivisor. Let `c` assign to each
minimal prime of `R` an index, let `I_i` be radical ideals whose minimal primes are exactly the
minimal primes of index `i`, and suppose `length(R_𝔮) = n_{c(𝔮)}`. Then

  `length(R ⧸ (a)) = ∑_i n_i · length(R ⧸ (a, I_i))`.

An index outside the image of `c` contributes nothing: the corresponding ideal has no minimal
prime, hence is the unit ideal. -/
theorem natCast_length_quotient_span_eq_finsum_length_quotient_sup (a : R)
    (ha : IsSMulRegular R a) (ham : a ∈ IsLocalRing.maximalIdeal R)
    (hdim : ringKrullDim R = 1) {ι : Type*} (c : minimalPrimes R → ι) (I : ι → Ideal R)
    (hrad : ∀ i, (I i).IsRadical)
    (hmin : ∀ i, (I i).minimalPrimes = {q | ∃ h : q ∈ minimalPrimes R, c ⟨q, h⟩ = i})
    (n : ι → ℤ)
    (hn : ∀ q : minimalPrimes R,
      haveI := q.2.1.1
      ((Module.length (Localization.AtPrime q.1) (Localization.AtPrime q.1)).toNat : ℤ) = n (c q)) :
    ((Module.length R (R ⧸ Ideal.span {a})).toNat : ℤ) =
      ∑ᶠ i, n i * ((Module.length R (R ⧸ (Ideal.span {a} ⊔ I i))).toNat : ℤ) := by
  classical
  have hfinite : Module.length R (R ⧸ Ideal.span {a}) ≠ ⊤ := by
    have hb : a ∈ nonZeroDivisors R := by
      simpa using Ideal.algebraMap_mem_nonZeroDivisors_of_isSMulRegular ha
    have hdim0 : ringKrullDim (R ⧸ Ideal.span {a}) ≤ 0 := by
      have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hb
      rw [hdim] at h
      cases hk : ringKrullDim (R ⧸ Ideal.span {a}) with
      | bot => exact bot_le
      | coe d =>
        rw [hk] at h
        have h' : d + 1 ≤ 1 := by exact_mod_cast h
        have hd : d = 0 := by
          have h0 : d + 1 ≤ 0 + 1 := by simpa using h'
          exact nonpos_iff_eq_zero.mp ((ENat.add_le_add_iff_right ENat.one_ne_top).mp h0)
        rw [hd]
        rfl
    have : Ring.KrullDimLE 0 (R ⧸ Ideal.span {a}) := Ring.krullDimLE_iff.mpr hdim0
    have : IsArtinianRing (R ⧸ Ideal.span {a}) := isArtinianRing_iff_krullDimLE_zero.mpr this
    have hfl : IsFiniteLength (R ⧸ Ideal.span {a}) (R ⧸ Ideal.span {a}) :=
      isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
    have h := Module.length_ne_top_iff.mpr hfl
    rwa [← Module.length_eq_of_surjective (R := R ⧸ Ideal.span {a}) (S := R)
      (M := R ⧸ Ideal.span {a}) Ideal.Quotient.mk_surjective] at h
  rw [natCast_length_quotient_span_eq_sum_minimalPrimes a ha hdim hfinite]
  let T := {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R}
  let : Fintype T := (Ideal.finite_setOf_asIdeal_mem_minimalPrimes (⊥ : Ideal R)).fintype
  let c' : T → ι := fun p => c ⟨p.1.asIdeal, p.2⟩
  let L : T → ℤ := fun p => ((Module.length R (R ⧸ (Ideal.span {a} ⊔ p.1.asIdeal))).toNat : ℤ)
  have hleft : (∑ᶠ p : T, ((Module.length (Localization.AtPrime p.1.asIdeal)
        (Localization.AtPrime p.1.asIdeal)).toNat : ℤ) *
        ((Module.length R (R ⧸ (Ideal.span {a} ⊔ p.1.asIdeal))).toNat : ℤ)) =
      ∑ p : T, n (c' p) * L p := by
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hn ⟨p.1.asIdeal, p.2⟩]
  have hblock : ∀ i, ((Module.length R (R ⧸ (Ideal.span {a} ⊔ I i))).toNat : ℤ) =
      ∑ p ∈ Finset.univ.filter (fun p : T => c' p = i), L p := by
    intro i
    have hsub : (I i).minimalPrimes ⊆ minimalPrimes R := by
      rw [hmin i]
      exact fun q hq => hq.1
    rw [natCast_length_quotient_span_sup_eq_finsum_of_isRadical a ha ham hdim hfinite (I i)
      (hrad i) hsub]
    let e : {q : PrimeSpectrum R // q.asIdeal ∈ (I i).minimalPrimes} ≃
        {p : T // c' p = i} :=
      { toFun := fun q => ⟨⟨q.1, hsub q.2⟩, ((Set.ext_iff.mp (hmin i) q.1.asIdeal).mp q.2).snd⟩
        invFun := fun p => ⟨p.1.1, (Set.ext_iff.mp (hmin i) p.1.1.asIdeal).mpr ⟨p.1.2, p.2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← finsum_comp_equiv e.symm]
    show (∑ᶠ p : ({p : T | c' p = i} : Set T), L p.1) = _
    rw [finsum_set_coe_eq_finsum_mem {p : T | c' p = i}, finsum_mem_eq_toFinset_sum]
    congr 1
    ext p
    simp
  have hsupp : (Function.support fun i => n i *
      ((Module.length R (R ⧸ (Ideal.span {a} ⊔ I i))).toNat : ℤ)) ⊆
      ↑(Finset.univ.image c') := by
    intro i hi
    by_contra hni
    refine hi ?_
    show n i * _ = 0
    rw [hblock i, Finset.sum_eq_zero fun p hp => absurd (Finset.mem_image.mpr
      ⟨p, Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩) hni, mul_zero]
  rw [hleft, finsum_eq_sum_of_support_subset _ hsupp]
  simp_rw [hblock, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image c') (g := c')
    (fun p _ => Finset.mem_image_of_mem c' (Finset.mem_univ p)) (fun p => n (c' p) * L p)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p hp => ?_
  rw [(Finset.mem_filter.mp hp).2]

end AlgebraicGeometry
