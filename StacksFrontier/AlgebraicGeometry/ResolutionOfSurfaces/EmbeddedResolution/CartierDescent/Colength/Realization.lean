module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.ChartOverlap
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.ColengthSteps
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.Colength.ChartIdealTransfer
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.FiniteColength
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.FiniteLengthLocalization

/-!
# Realising prescribed residual values by a global section divisible by the divisor

Let `R` be a commutative ring embedded in a field `K`, let `x y : R` and let `t s : K` satisfy
`t * s = 1` and `x * t = y`, so that `B = Algebra.adjoin R {t}` and `C = Algebra.adjoin R {s}`
are the two standard affine blowup charts `R[𝔪/x]`, `R[𝔪/y]` read inside `K`. Let `L` be an ideal
of `R`, let `d` be a natural number and let `Rx`, `Ry` be the residual ideals on the two charts,
so that `(ξ ^ d)·Rx = L·B` and `(η ^ d)·Ry = L·C` with `ξ`, `η` the images of `x` in `B` and of
`y` in `C`; assume the two residual quotients `B ⧸ Rx` and `C ⧸ Ry` are Artinian rings.

Given arbitrary prescribed values in the localizations of `B ⧸ Rx` at all the primes above `Rx`,
and in the localizations of `C ⧸ Ry` at some of the primes above `Ry` containing `s`, there is a
single element `a` of `R`, divisible by `x ^ d` on the first chart and by `y ^ d` on the second,
whose two cofactors realise all the prescribed values (cf. [Stacks, Tag 0AGT]).

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.exists_mem_gluedIdeal_realizing`: the realisation
  statement above.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.ResolutionOfSurfaces.CartierDescent

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]

/-- If the class of `b` vanishes in the localization of `B ⧸ J` at `p`, then the image of `b` in
the localization of `B` at `p` lies in the extension of `J`. -/
private theorem mem_map_algebraMap_of_localizedModule_eq_zero {B : Type u} [CommRing B]
    (J : Ideal B) (p : PrimeSpectrum B) {b : B}
    (h : (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (B ⧸ J))
      (Ideal.Quotient.mk J b) = 0) :
    (algebraMap B (Localization.AtPrime p.asIdeal)) b ∈
      Ideal.map (algebraMap B (Localization.AtPrime p.asIdeal)) J := by
  obtain ⟨u, hu⟩ := (IsLocalizedModule.eq_zero_iff p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (B ⧸ J))).mp h
  refine (IsLocalization.algebraMap_mem_map_algebraMap_iff p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal) J b).mpr ⟨(u : B), u.2, ?_⟩
  have hu' : (u : B) • (Ideal.Quotient.mk J b) = 0 := hu
  rwa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at hu'

/-- Dividing by a member of the localizing submonoid: `u • (m / u) = m`. -/
private theorem smul_localizedModule_mk_self {B : Type u} [CommRing B] {S : Submonoid B}
    (M : Type u) [AddCommGroup M] [Module B M] (u : B) (hu : u ∈ S) (m : M) :
    u • LocalizedModule.mk m ⟨u, hu⟩ = LocalizedModule.mk m 1 := by
  rw [LocalizedModule.smul'_mk]
  exact LocalizedModule.mk_eq.mpr ⟨1, by simp⟩

/-- Let `Ry` be an ideal of a ring `C` with `C ⧸ Ry` Artinian, let `Sy` be the set of all primes
above `Ry` and `Sy'` a subset of it consisting of primes containing a fixed element `sc`, and let
`b : C` and `k : ℕ`. Then prescribed values along `Sy'` are realised by some `γ : C` for which, in
addition, a power of `sc` carries `b - sc ^ k γ` into `Ry`. -/
private theorem exists_realizing_and_pow_mul_sub_mem {C : Type u} [CommRing C] (Ry : Ideal C)
    [IsArtinianRing (C ⧸ Ry)] (Sy Sy' : Finset (PrimeSpectrum C))
    (hSy : ∀ p : PrimeSpectrum C, p ∈ Sy ↔ Ry ≤ p.asIdeal) (hSy'le : Sy' ⊆ Sy)
    (sc : C) (hSy'mem : ∀ v ∈ Sy', sc ∈ v.asIdeal) (b : C) (k : ℕ)
    (ζ' : ∀ v : Sy', LocalizedModule (v : PrimeSpectrum C).asIdeal.primeCompl (C ⧸ Ry)) :
    ∃ (γ : C) (m : ℕ), sc ^ m * (b - sc ^ k * γ) ∈ Ry ∧
      ∀ v : Sy', (LocalizedModule.mkLinearMap (v : PrimeSpectrum C).asIdeal.primeCompl (C ⧸ Ry))
        (Ideal.Quotient.mk Ry γ) = ζ' v := by
  classical
  obtain ⟨γ, hγ⟩ := surjective_pi_localizedModule_quotient Ry Sy hSy
    (fun v : Sy => if hv : sc ∈ (v : PrimeSpectrum C).asIdeal then
        (if hv' : (v : PrimeSpectrum C) ∈ Sy' then ζ' ⟨(v : PrimeSpectrum C), hv'⟩ else 0)
      else LocalizedModule.mk (Ideal.Quotient.mk Ry b)
        ⟨sc ^ k, pow_mem (Ideal.mem_primeCompl_iff.mpr hv) k⟩)
  have hcloc : ∀ v : PrimeSpectrum C, Ry ≤ v.asIdeal → sc ∉ v.asIdeal →
      (algebraMap C (Localization.AtPrime v.asIdeal)) (b - sc ^ k * γ) ∈
        Ideal.map (algebraMap C (Localization.AtPrime v.asIdeal)) Ry := by
    intro v hv hsv
    refine mem_map_algebraMap_of_localizedModule_eq_zero Ry v ?_
    have hval := congrFun hγ ⟨v, (hSy v).mpr hv⟩
    simp only [dif_neg hsv] at hval
    have hsmulq : (Ideal.Quotient.mk Ry (sc ^ k * γ) : C ⧸ Ry) =
        sc ^ k • Ideal.Quotient.mk Ry γ := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
    have hlin : (LocalizedModule.mkLinearMap v.asIdeal.primeCompl (C ⧸ Ry))
          (Ideal.Quotient.mk Ry (sc ^ k * γ)) =
        (LocalizedModule.mkLinearMap v.asIdeal.primeCompl (C ⧸ Ry))
          (Ideal.Quotient.mk Ry b) := by
      rw [hsmulq, map_smul, hval, smul_localizedModule_mk_self]
      rfl
    rw [map_sub, map_sub, hlin, sub_self]
  obtain ⟨m, hm⟩ := exists_pow_smul_mem_of_forall_localization Ry sc (b - sc ^ k * γ) hcloc
  refine ⟨γ, m, hm, fun v => ?_⟩
  have hval := congrFun hγ ⟨(v : PrimeSpectrum C), hSy'le v.2⟩
  simpa only [dif_pos (hSy'mem _ v.2), dif_pos v.2] using hval

/-- If `(x ^ d)·J` is the extension of `L` to the chart `S`, every element of `chartIdealSpan L S`
is `x ^ d` times an element of `J`. -/
private theorem exists_mem_ideal_eq_pow_mul_of_mem_chartIdealSpan (L : Ideal R) (S : Subalgebra R K)
    (x : R) (d : ℕ) (J : Ideal S)
    (hJ : Ideal.span {algebraMap R S x ^ d} * J = Ideal.map (algebraMap R S) L)
    {z : K} (hz : z ∈ chartIdealSpan L S) : ∃ r ∈ J, z = algebraMap R K x ^ d * r := by
  obtain ⟨r, hr, hreq⟩ := mem_span_singleton_mul_iff.1
    (hJ.symm ▸ (coe_mem_chartIdealSpan_iff L S ⟨_, mem_of_mem_chartIdealSpan hz⟩).1 hz)
  exact ⟨r, hr, by simpa using congrArg Subtype.val hreq⟩

/-- In the two-chart situation of [Stacks, Tag 0AGT], let `Rx` and `Ry` be the residual ideals on
the charts `B = Algebra.adjoin R {t}` and `C = Algebra.adjoin R {s}`, let `Sx` be the set of all
primes of `B` above `Rx`, and let `Sy'` be any set of primes of `C` above `Ry` containing `s`. Then
any prescription of values in the localizations of `B ⧸ Rx` along `Sx` and of `C ⧸ Ry` along `Sy'`
is realised by the two cofactors of a single element `a` of the glued ideal. -/
public theorem exists_mem_gluedIdeal_realizing
    (hinj : Function.Injective (algebraMap R K)) {x y : R} {t s : K} (hts : t * s = 1)
    (hxt : algebraMap R K x * t = algebraMap R K y) (hx : x ≠ 0)
    (hreg : ∀ a : R, a * y ∈ Ideal.span ({x} : Set R) → a ∈ Ideal.span ({x} : Set R))
    {B C : Subalgebra R K} (hB : B = Algebra.adjoin R ({t} : Set K))
    (hC : C = Algebra.adjoin R ({s} : Set K)) (hsC : s ∈ C)
    (L : Ideal R) (d : ℕ) (Rx : Ideal ↥B) (Ry : Ideal ↥C)
    [IsArtinianRing (↥B ⧸ Rx)] [IsArtinianRing (↥C ⧸ Ry)]
    (hRx : Ideal.span {algebraMap R ↥B x ^ d} * Rx = Ideal.map (algebraMap R ↥B) L)
    (hRy : Ideal.span {algebraMap R ↥C y ^ d} * Ry = Ideal.map (algebraMap R ↥C) L)
    (Sx : Finset (PrimeSpectrum ↥B))
    (hSx : ∀ p : PrimeSpectrum ↥B, p ∈ Sx ↔ Rx ≤ p.asIdeal)
    (Sy Sy' : Finset (PrimeSpectrum ↥C))
    (hSy : ∀ p : PrimeSpectrum ↥C, p ∈ Sy ↔ Ry ≤ p.asIdeal) (hSy'le : Sy' ⊆ Sy)
    (hSy'mem : ∀ v ∈ Sy', (⟨s, hsC⟩ : ↥C) ∈ v.asIdeal)
    (ζ : ∀ w : Sx, LocalizedModule (w : PrimeSpectrum ↥B).asIdeal.primeCompl (↥B ⧸ Rx))
    (ζ' : ∀ v : Sy', LocalizedModule (v : PrimeSpectrum ↥C).asIdeal.primeCompl (↥C ⧸ Ry)) :
    ∃ a : R, a ∈ gluedIdeal (algebraMap R K x) (algebraMap R K y) d B C ∧
      ∃ (β : ↥B) (γ : ↥C),
        algebraMap R K a = algebraMap R K x ^ d * (β : K) ∧
        algebraMap R K a = algebraMap R K y ^ d * (γ : K) ∧
        (∀ w : Sx, (LocalizedModule.mkLinearMap (w : PrimeSpectrum ↥B).asIdeal.primeCompl
            (↥B ⧸ Rx)) (Ideal.Quotient.mk Rx β) = ζ w) ∧
        (∀ v : Sy', (LocalizedModule.mkLinearMap (v : PrimeSpectrum ↥C).asIdeal.primeCompl
            (↥C ⧸ Ry)) (Ideal.Quotient.mk Ry γ) = ζ' v) := by
  obtain ⟨β₀, hβ₀⟩ := surjective_pi_localizedModule_quotient Rx Sx hSx ζ
  have hβ₀D : (β₀ : K) ∈ Algebra.adjoin R ({t, s} : Set K) :=
    adjoin_le_adjoin_pair t s (hB ▸ β₀.2)
  obtain ⟨k, hk⟩ := exists_pow_mul_mem_adjoin_symm hts (β₀ : K) hβ₀D
  have hkC : s ^ k * (β₀ : K) ∈ C := by rwa [hC]
  obtain ⟨γ₀, m, hm, hγ₀⟩ := exists_realizing_and_pow_mul_sub_mem Ry Sy Sy' hSy hSy'le
    (⟨s, hsC⟩ : ↥C) hSy'mem ((⟨s, hsC⟩ : ↥C) ^ d * ⟨s ^ k * (β₀ : K), hkC⟩) k ζ'
  have hmul : (algebraMap R ↥C y) ^ d *
      ((⟨s, hsC⟩ : ↥C) ^ m * ((⟨s, hsC⟩ : ↥C) ^ d * ⟨s ^ k * (β₀ : K), hkC⟩ -
        (⟨s, hsC⟩ : ↥C) ^ k * γ₀)) ∈ Ideal.map (algebraMap R ↥C) L := by
    rw [← hRy]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hm
  have hxyd : algebraMap R K x ^ d = algebraMap R K y ^ d * s ^ d := by
    rw [← mul_pow, algebraMap_mul_eq_of_mul_eq_one hts hxt]
  have hcoe : (((algebraMap R ↥C y) ^ d *
        ((⟨s, hsC⟩ : ↥C) ^ m * ((⟨s, hsC⟩ : ↥C) ^ d * ⟨s ^ k * (β₀ : K), hkC⟩ -
          (⟨s, hsC⟩ : ↥C) ^ k * γ₀)) : ↥C) : K) =
      s ^ (m + k) * (algebraMap R K x ^ d * (β₀ : K) - algebraMap R K y ^ d * (γ₀ : K)) := by
    have h1 : ((algebraMap R ↥C y : ↥C) : K) = algebraMap R K y := rfl
    push_cast [h1]
    rw [hxyd]
    ring
  have hdiffC : s ^ (m + k) *
      (algebraMap R K x ^ d * (β₀ : K) - algebraMap R K y ^ d * (γ₀ : K)) ∈
      chartIdealSpan L C := hcoe ▸ coe_mem_chartIdealSpan_of_mem_map L C hmul
  have hbc : algebraMap R K x ^ d * (β₀ : K) - algebraMap R K y ^ d * (γ₀ : K) ∈
      chartIdealSpan L (Algebra.adjoin R ({t, s} : Set K)) := by
    have hts' : t ^ (m + k) * s ^ (m + k) = 1 := by rw [← mul_pow, hts, one_pow]
    have hrw : algebraMap R K x ^ d * (β₀ : K) - algebraMap R K y ^ d * (γ₀ : K) =
        t ^ (m + k) * (s ^ (m + k) *
          (algebraMap R K x ^ d * (β₀ : K) - algebraMap R K y ^ d * (γ₀ : K))) := by
      rw [← mul_assoc, hts', one_mul]
    rw [hrw]
    exact mul_mem_chartIdealSpan (pow_mem (Algebra.subset_adjoin (by simp)) _)
      (chartIdealSpan_mono_right L
        (hC ▸ (Algebra.adjoin_mono (by simp) : Algebra.adjoin R ({s} : Set K) ≤ _)) hdiffC)
  have hIB : ∀ z ∈ chartIdealSpan L (Algebra.adjoin R ({t} : Set K)),
      ∃ β' ∈ Algebra.adjoin R ({t} : Set K), z = algebraMap R K x ^ d * β' := by
    rw [← hB]
    exact exists_eq_mul_pow_of_mem_chartIdealSpan L B (algebraMap R ↥B x) d
      (hRx ▸ Ideal.mul_le_left)
  have hIC : ∀ z ∈ chartIdealSpan L (Algebra.adjoin R ({s} : Set K)),
      ∃ γ' ∈ Algebra.adjoin R ({s} : Set K), z = algebraMap R K y ^ d * γ' := by
    rw [← hC]
    exact exists_eq_mul_pow_of_mem_chartIdealSpan L C (algebraMap R ↥C y) d
      (hRy ▸ Ideal.mul_le_left)
  obtain ⟨a, ha, h1, h2⟩ := exists_mem_gluedIdeal_sub_mem hinj hts hxt hx hreg L d
    (β₀ : K) (γ₀ : K) (hB ▸ β₀.2) (hC ▸ γ₀.2) hIB hIC hbc
  rw [← hB, ← hC] at ha
  rw [← hB] at h1
  rw [← hC] at h2
  obtain ⟨r, hr, hreq⟩ := exists_mem_ideal_eq_pow_mul_of_mem_chartIdealSpan L B x d Rx hRx h1
  obtain ⟨r', hr', hreq'⟩ := exists_mem_ideal_eq_pow_mul_of_mem_chartIdealSpan L C y d Ry hRy h2
  refine ⟨a, ha, β₀ + r, γ₀ + r', ?_, ?_, fun w => ?_, fun v => ?_⟩
  · push_cast
    linear_combination hreq
  · push_cast
    linear_combination hreq'
  · rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hr, add_zero]
    exact congrFun hβ₀ w
  · rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hr', add_zero]
    exact hγ₀ v

end Stacks.ResolutionOfSurfaces.CartierDescent

end
