module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorConstructionsAgree
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistDegreeOne
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorPowerGenerator
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Trivialization
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Scheme
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.PicardChart.Basic

/-!
# Units on the standard charts and their overlaps in projective space

Grade `R[T₀, …, Tₙ]` by total degree, with `R` a domain. On the standard chart `D₊(Tᵢ)` of
`Proj R[T₀, …, Tₙ]` the ring of functions is a polynomial ring in `n` variables over `R`, so its
units are exactly the units of `R`; on an overlap `D₊(Tᵢ) ∩ D₊(Tⱼ) = D₊(TᵢTⱼ)` the ratio
`Tⱼ / Tᵢ` becomes invertible and the units become `R\* × (Tⱼ / Tᵢ)ᶻ`. This file proves both,
together with the ring-theoretic statement they rest on: in a localization `A[1/p]` of a domain
at a prime element, every unit is a unit of `A` times an integer power of `p`, and the integer is
determined.

## Main results

* `Stacks.PicardUFD.exists_eq_unit_mul_awayUnit_zpow` and
  `Stacks.PicardUFD.eq_zero_of_map_mul_awayUnit_zpow_eq_one`: the units of `A[1/p]` for `p` a
  prime element of a domain `A` are `A\* × pᶻ`, and the exponent is unique.
* `Stacks.PicardUFD.prime_algebraMap_of_not_dvd_pow`: a prime of `A` dividing no power of `p`
  stays prime in `A[1/p]`, which is what lets the previous statement be iterated at a second
  prime.
* `Stacks.PicardUFD.prime_ratio`: the ratio `T_k / Tᵢ` is a prime element of the `i`-th chart
  ring, for `k ≠ i`, and `Stacks.PicardUFD.not_dvd_pow_ratio`: two such ratios with distinct
  numerators divide no power of one another.
* `Stacks.PicardUFD.isLocalizationAway_ratio`: the ring of functions on the overlap
  `D₊(TᵢTⱼ)` is the localization of the `i`-th chart ring at `Tⱼ / Tᵢ`; and
  `Stacks.PicardUFD.prime_algebraMap_ratio`: a third ratio stays prime there.
* `Stacks.PicardUFD.isUnit_chartRing_iff`: the units of the `i`-th chart ring are the units
  of `R`.
* `Stacks.PicardUFD.exists_eq_unit_mul_ratio_zpow` and
  `Stacks.PicardUFD.eq_zero_of_map_mul_ratio_zpow_eq_one`: the units of the overlap ring are
  the units of the chart ring times a unique integer power of `Tⱼ / Tᵢ`.
* `Stacks.PicardUFD.bijective_smul_trivializingFun`: multiplication by the trivializing section
  `f ^ m` of `𝒪(m)` is bijective on every open of `D₊(f)`, for `f` of degree one, with the twist
  degree `m` rather than `m * (1 : ℕ)`.
* `Stacks.PicardUFD.twistChartGenerator` and `Stacks.PicardUFD.chartGenerator`: the local
  generator `Tᵢ ^ m` of `𝒪(m)` on the standard chart `D₊(Tᵢ)`, and the local generator of an
  arbitrary invertible sheaf there.
* `Stacks.PicardUFD.generatorRatioUnit_twistChartGenerator`: **the Čech `1`-cocycle of `𝒪(m)`
  for the standard covering is `(Tᵢ / Tⱼ) ^ m`.**
* `Stacks.PicardUFD.twistPicardHom`: the homomorphism `ℤ ⟶ Pic(ℙⁿ_R)`, `m ↦ 𝒪(m)`, of
  Tag 0BXJ.
* `Stacks.PicardUFD.twistPicardHom_injective`: **that homomorphism is injective** for `R` a
  domain and `0 < n`.
* `Stacks.PicardUFD.exists_iso_twistingSheaf`: **every invertible module on the projective line
  over a unique factorization domain is a twist `𝒪(m)`**, and
  `Stacks.PicardUFD.twistPicardHom_surjective`: **the homomorphism is surjective for `n = 1`**,
  hence bijective there by `Stacks.PicardUFD.twistPicardHom_bijective`.
* `Stacks.SheafOfModules.isoOfTransitionEqPair`: two modules with local generators on a
  two-element covering family and the same transition unit over the single overlap are
  isomorphic, and `Stacks.SheafOfModules.generatorSmulUnit`: a unit multiple of a local
  generator is a local generator.
* `Stacks.PicardUFD.exists_eq_restrict_mul_overlapRatioUnit`: every invertible function on an
  overlap `D₊(TᵢTⱼ)` is the restriction of an invertible function on `D₊(Tᵢ)` times the
  transition unit of a twist.
* `Stacks.PicardUFD.sectionsInfEquiv` and `Stacks.PicardUFD.sectionsInfEquiv_algebraMap`: the
  overlap ring read on the sections over `D₊(Tᵢ) ⊓ D₊(Tⱼ)`, and the compatibility of the two
  presentations of the sections with restriction.

## Implementation notes

The chart ring is `Stacks.ProjectiveChart.ChartRing R n i`, Mathlib's degree-zero homogeneous
localization at `Tᵢ`, identified with `R[Y₁, …, Yₙ]` by
`Stacks.ProjectiveChart.chartRingEquiv`, which carries the `j`-th variable to the ratio
`T_{σ j} / Tᵢ`. Primality of a ratio is therefore primality of a variable, transported along
that isomorphism, and the unit group of a chart is the unit group of a polynomial ring over a
reduced ring, `MvPolynomial.isUnit_iff_eq_C_of_isReduced`.

That the overlap ring is a localization of the chart ring at the ratio is Mathlib's
`HomogeneousLocalization.Away.isLocalization_mul`, whose distinguished element
`HomogeneousLocalization.Away.isLocalizationElem` is literally
`Stacks.ProjectiveChart.ratio`; the algebra structure it localizes along is the chart
restriction `HomogeneousLocalization.awayMap`, so no comparison of localization models is
needed.

The trivializing section of `𝒪(m)` on `D₊(Tᵢ)` is stated at the twist degree `m` and not at
`m * ((1 : ℕ) : ℤ)`, which is the degree Tag 01MS produces. The two are propositionally but not
definitionally equal — `Nat.mul` recurses on its second argument — and a transport along that
equality is an equality of *sheaves*, through which a transition unit cannot be computed. So the
whole fraction calculus of
`StacksFrontier/AlgebraicGeometry/ProjTrivialization/Basic.lean` is rerun here at degree `m`
(`Stacks.PicardUFD.exists_isFraction_of_mem_degree_one` onwards); only
`Stacks.AlgebraicGeometry.ProjTrivialization.eq_of_val_mul_eq`, which never mentions the twist
degree, is reused verbatim.

The transition unit `(Tᵢ / Tⱼ) ^ m` is built as the single homogeneous fraction
`Tᵢ^{m⁺} Tⱼ^{m⁻} / (Tᵢ^{m⁻} Tⱼ^{m⁺})`, whose numerator and denominator both have degree
`m⁺ + m⁻`; it is therefore a section of the structure sheaf on any open inside both charts, and
the ratio law is a one-line cross-multiplication rather than a passage through the overlap ring.

Injectivity is proved at a single point rather than over the overlap ring. A trivialization of
`𝒪(m)` exhibits the transition unit `(Tᵢ / Tⱼ) ^ m` as a ratio of invertible functions on the two
charts (`Stacks.PicardUFD.exists_isUnit_mul_generatorRatioUnit`), those functions are units of
`R` (`Stacks.PicardUFD.exists_eq_sectionsChartEquiv_C_of_isUnit`), and evaluating at the generic
point `Stacks.PicardUFD.zeroPoint` — the zero ideal, which is prime because `R` is a domain and
lies on every chart — turns the identity into an equation between monomials of `R[T₀, …, Tₙ]`.
So only `IsDomain R` is used, and only the surjectivity of the chart identification at one
point, not its compatibility with restriction.

Tag 0BXJ is stated here with the hypothesis `0 < n`. The source states no restriction, but at
`n = 0` the map `m ↦ 𝒪(m)` is the zero map into the Picard group of
`ℙ⁰_R = Proj R[T₀] ≅ Spec R`, which is trivial for a unique factorization domain, so the map is
not injective. The hypothesis is exactly what supplies two distinct coordinates, which is where
the monomial identity above becomes a constraint on `m`.

Surjectivity is proved here by the two-chart route, available at `n = 1`. An
invertible module is trivial on each standard chart by Tag 0BDA, so it is described by the single
transition unit of `Stacks.PicardUFD.chartGenerator` on the one overlap; that unit is a unit of
the chart ring times an integer power of the ratio by
`Stacks.PicardUFD.exists_eq_unit_mul_ratio_zpow`, read on sections through
`Stacks.PicardUFD.sectionsInfEquiv_algebraMap`; rescaling the generator on `D₊(T₀)` by the chart
unit (`Stacks.SheafOfModules.generatorSmulUnit`) leaves exactly the transition unit of a twist,
and `Stacks.SheafOfModules.isoOfTransitionEqPair` glues that comparison back to an isomorphism of
modules.

Surjectivity for an arbitrary `n`, and with it the isomorphism `ℤ ≃+ Pic(ℙⁿ_R)` of Tag 0BXJ, is
in `StacksFrontier/AlgebraicGeometry/PicardUFD/ProjectiveSpaceCocycle.lean`: it runs the cocycle
argument over all `n + 1` charts on top of the overlap-unit calculus of this file, comparing the
exponents of the ratios on the triple overlaps. The `n = 1` case here is the one in which there
are no triple overlaps to compare.

## References

* [Stacks Project, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)
* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.PicardUFD

/-! ### Units of a localization at a prime element -/

section Away

variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]

/-- The image in `A[1/p]` of the inverted element `p`, as a unit. -/
def awayUnit (p : A) [IsLocalization.Away p S] : Sˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := S) p).unit

/-- The underlying element of `awayUnit p` is the image of `p` in `A[1/p]`. -/
@[simp] theorem awayUnit_val (p : A) [IsLocalization.Away p S] :
    (awayUnit (S := S) p : S) = algebraMap A S p :=
  IsUnit.unit_spec _

/-- **Every unit of `A[1/p]` is a unit of `A` times an integer power of `p`**, for `p` a prime
element of a domain `A`. The numerator of a unit divides a power of `p`, hence is a unit times a
power of `p` because `p` is prime. -/
theorem exists_eq_unit_mul_awayUnit_zpow [IsDomain A] {p : A} (hp : Prime p)
    [IsLocalization.Away p S] (w : Sˣ) :
    ∃ (v : Aˣ) (k : ℤ),
      w = Units.map (algebraMap A S).toMonoidHom v * awayUnit (S := S) p ^ k := by
  classical
  set P := awayUnit (S := S) p with hP
  set V := Units.map (algebraMap A S).toMonoidHom with hV
  set s := IsLocalization.Away.sec p (w : S) with hsdef
  have hs : (w : S) * algebraMap A S p ^ s.2 = algebraMap A S s.1 := by
    simpa [map_pow] using IsLocalization.Away.sec_spec (S := S) p (w : S)
  have hunit : IsUnit (algebraMap A S s.1) := by
    rw [← hs]
    exact w.isUnit.mul ((IsLocalization.Away.algebraMap_isUnit (S := S) p).pow _)
  obtain ⟨m, hm⟩ := (IsLocalization.Away.algebraMap_isUnit_iff (S := S) p).mp hunit
  obtain ⟨i, -, u, hu⟩ := (dvd_prime_pow hp m).mp hm
  have hA : ((u⁻¹ : Aˣ) : A) * p ^ i = s.1 := by
    rw [← hu, mul_comm s.1 (u : A), ← mul_assoc]
    simp
  have key : w * P ^ (s.2 : ℤ) = V u⁻¹ * P ^ (i : ℤ) := by
    apply Units.ext
    simp only [Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val, hP, awayUnit_val, hV,
      Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [hs, ← map_pow, ← map_mul, hA]
  exact ⟨u⁻¹, (i : ℤ) - s.2, by rwa [zpow_sub, ← mul_assoc, eq_mul_inv_iff_mul_eq]⟩

/-- The structure map of a localization at the powers of a nonzero element of a domain is
injective. -/
theorem algebraMap_away_injective [IsDomain A] {p : A} (hp : p ≠ 0)
    [IsLocalization.Away p S] : Function.Injective (algebraMap A S) :=
  IsLocalization.injective (S := S) (M := Submonoid.powers p) <| by
    rintro _ ⟨m, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero m hp)

/-- **The exponent in `A[1/p]` is determined**: a unit of `A` times a power of `p` is `1` only
when the power is the zeroth. -/
theorem eq_zero_of_map_mul_awayUnit_zpow_eq_one [IsDomain A] {p : A} (hp : Prime p)
    [IsLocalization.Away p S] (v : Aˣ) (k : ℤ)
    (h : Units.map (algebraMap A S).toMonoidHom v * awayUnit (S := S) p ^ k = 1) :
    k = 0 := by
  have hinj := algebraMap_away_injective (S := S) hp.ne_zero
  have hpow : ∀ m : ℕ, IsUnit (p ^ m) → m = 0 := fun m hm =>
    Decidable.byContradiction fun hm0 => hp.not_isUnit ((isUnit_pow_iff hm0).mp hm)
  -- reduce to an equation between images of elements of `A`
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    have h' : algebraMap A S ((v : A) * p ^ m) = algebraMap A S 1 := by
      simpa [map_mul, map_pow, zpow_natCast] using congrArg (fun z : Sˣ => (z : S)) h
    have hv : (v : A) * p ^ m = 1 := hinj h'
    simpa using hpow m (isUnit_of_dvd_one ⟨(v : A), by rw [← hv]; ring⟩)
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
    have h' : algebraMap A S (v : A) = algebraMap A S (p ^ m) := by
      have h2 : Units.map (algebraMap A S).toMonoidHom v
          = awayUnit (S := S) p ^ (m : ℤ) := by
        rw [mul_eq_one_iff_eq_inv.mp h, zpow_neg, inv_inv]
      simpa [map_pow, zpow_natCast] using congrArg (fun z : Sˣ => (z : S)) h2
    have hv : (v : A) = p ^ m := hinj h'
    simp [hpow m (hv ▸ v.isUnit)]

/-- **A prime element of `A` dividing no power of `p` stays prime in `A[1/p]`.** The ideal it
generates is prime and disjoint from the powers of `p`, so its image is prime. This is what lets
the unit computation above be iterated at a second prime, as the triple overlaps of the standard
covering of projective space require. -/
theorem prime_algebraMap_of_not_dvd_pow [IsDomain A] {p q : A} (hp : p ≠ 0) (hq : Prime q)
    [IsLocalization.Away p S] (h : ∀ m : ℕ, ¬ q ∣ p ^ m) :
    Prime (algebraMap A S q) := by
  have hinj := algebraMap_away_injective (S := S) hp
  have hq0 : algebraMap A S q ≠ 0 := fun hz => hq.ne_zero (hinj (by simpa using hz))
  have hmap : Ideal.span {algebraMap A S q} = Ideal.map (algebraMap A S) (Ideal.span {q}) := by
    simp [Ideal.map_span]
  rw [← Ideal.span_singleton_prime hq0, hmap]
  refine IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers p) S _
    ((Ideal.span_singleton_prime hq.ne_zero).mpr hq) ?_
  rw [Set.disjoint_left]
  rintro x ⟨m, rfl⟩ hx
  exact h m (Ideal.mem_span_singleton.mp hx)

end Away

/-! ### The standard charts of projective space -/

section Charts

open Stacks.ProjectiveChart MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] {n : ℕ}

/-- The `j`-th affine coordinate of the `i`-th standard chart is the ratio `T_{σ j} / Tᵢ`. -/
theorem chartRingEquiv_X (i : Fin (n + 1)) (j : Fin n) :
    chartRingEquiv R i (MvPolynomial.X j) = ratio R i (i.succAbove j) := by
  simp [chartRingEquiv, chartRingEquivDeg0, chartHom]

/-- **The ratio `T_k / Tᵢ` is a prime element of the `i`-th chart ring** when `k ≠ i`: the chart
ring is a polynomial ring over `R` in which that ratio is one of the variables. -/
theorem prime_ratio [IsDomain R] {i k : Fin (n + 1)} (h : k ≠ i) :
    Prime (ratio R i k) := by
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq h
  rw [← chartRingEquiv_X]
  exact (MulEquiv.prime_iff (chartRingEquiv R i).toMulEquiv).mpr MvPolynomial.X_prime

/-- A variable of a polynomial ring over a nontrivial ring divides no power of a different
variable. Setting the first variable to `0` and all the others to `1` would make `0` divide
`1`. -/
theorem not_dvd_pow_X {ι : Type*} [Nontrivial R] {a b : ι} (hab : a ≠ b)
    (m : ℕ) : ¬ (MvPolynomial.X a : MvPolynomial ι R) ∣ MvPolynomial.X b ^ m := by
  classical
  intro h
  have h' := map_dvd (MvPolynomial.eval (fun k => if k = a then (0 : R) else 1)) h
  have e1 : MvPolynomial.eval (fun k => if k = a then (0 : R) else 1) (MvPolynomial.X a) = 0 := by
    simp
  have e2 : MvPolynomial.eval (fun k => if k = a then (0 : R) else 1) (MvPolynomial.X b) = 1 := by
    simp [Ne.symm hab]
  exact one_ne_zero (by rwa [e1, map_pow, e2, one_pow, zero_dvd_iff] at h')

/-- **The ratio `T_j / Tᵢ` divides no power of the ratio `T_k / Tᵢ`** for `j`, `k` distinct and
both different from `i`: they are distinct variables of a polynomial ring over `R`. -/
theorem not_dvd_pow_ratio [Nontrivial R] {i j k : Fin (n + 1)} (hj : j ≠ i) (hk : k ≠ i)
    (hjk : j ≠ k) (m : ℕ) : ¬ ratio R i j ∣ ratio R i k ^ m := by
  classical
  obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hj
  obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hk
  have hab : a ≠ b := fun h => hjk (by rw [h])
  rw [← chartRingEquiv_X, ← chartRingEquiv_X]
  intro hdvd
  refine not_dvd_pow_X R hab m ?_
  simpa [map_pow] using map_dvd (chartRingEquiv R i).symm.toRingHom hdvd

/-- **The units of the `i`-th chart ring are the units of `R`**: the chart ring is a polynomial
ring over `R`, and `R` is reduced. -/
theorem isUnit_chartRing_iff [IsDomain R] (i : Fin (n + 1)) (x : ChartRing R n i) :
    IsUnit x ↔ ∃ r : R, IsUnit r ∧ x = chartRingEquiv R i (MvPolynomial.C r) := by
  constructor
  · intro hx
    obtain ⟨r, hr, hrx⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced
      (P := (chartRingEquiv R i).symm x)).mp
        (hx.map (chartRingEquiv R i).symm.toRingHom)
    exact ⟨r, hr, by rw [← hrx]; simp⟩
  · rintro ⟨r, hr, rfl⟩
    exact (hr.map (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)).map
      (chartRingEquiv R i).toRingHom

/-! ### The overlap of two standard charts -/

/-- A power of a homogeneous coordinate is homogeneous of that degree. -/
theorem pow_X_mem_degree (i : Fin (n + 1)) (p : ℕ) :
    (MvPolynomial.X i ^ p : MvPolynomial (Fin (n + 1)) R) ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R p := by
  simpa using Stacks.AlgebraicGeometry.ProjTrivialization.pow_toNat_mem
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (X_mem_degree_one R i) p

/-- A monomial in two homogeneous coordinates is homogeneous of the total degree. -/
theorem X_pow_mul_X_pow_mem {p q N : ℕ} (hN : p + q = N) (i j : Fin (n + 1)) :
    (MvPolynomial.X i ^ p * MvPolynomial.X j ^ q : MvPolynomial (Fin (n + 1)) R) ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R N := by
  subst hN
  exact SetLike.mul_mem_graded (pow_X_mem_degree R i p) (pow_X_mem_degree R j q)

/-- The product of two homogeneous coordinates has degree two. -/
theorem X_mul_X_mem_degree_two (i j : Fin (n + 1)) :
    (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 2 :=
  SetLike.mul_mem_graded (X_mem_degree_one R i) (X_mem_degree_one R j)

/-- The ring of functions on the overlap `D₊(TᵢTⱼ)` of the `i`-th and `j`-th standard charts of
projective `n`-space over `R`. -/
abbrev OverlapRing (R : Type u) [CommRing R] (n : ℕ) (i j : Fin (n + 1)) :=
  HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (MvPolynomial.X i * MvPolynomial.X j)

/-- Restriction of functions from the `i`-th chart to the overlap with the `j`-th makes the
overlap ring an algebra over the chart ring. -/
instance algebraChartRingOverlapRing (i j : Fin (n + 1)) :
    Algebra (ChartRing R n i) (OverlapRing R n i j) :=
  (HomogeneousLocalization.awayMap _ (X_mem_degree_one R j)
    (rfl : (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) =
      MvPolynomial.X i * MvPolynomial.X j)).toAlgebra

/-- **The functions on the overlap `D₊(TᵢTⱼ)` are the functions on `D₊(Tᵢ)` with the ratio
`Tⱼ / Tᵢ` inverted.** The overlap is the standard open of the affine chart `D₊(Tᵢ)` cut out by
that ratio. -/
instance isLocalizationAway_ratio (i j : Fin (n + 1)) :
    IsLocalization.Away (ratio R i j) (OverlapRing R n i j) :=
  HomogeneousLocalization.Away.isLocalization_mul (X_mem_degree_one R i)
    (X_mem_degree_one R j) rfl one_ne_zero

/-- **Every function invertible on the overlap `D₊(TᵢTⱼ)` is a unit of the `i`-th chart times an
integer power of the ratio `Tⱼ / Tᵢ`.** With `Stacks.PicardUFD.isUnit_chartRing_iff` this is the
computation `𝒪^*(D₊(TᵢTⱼ)) = R^* × (Tⱼ / Tᵢ)ᶻ` of Tag 0BXJ. -/
theorem exists_eq_unit_mul_ratio_zpow [IsDomain R] {i j : Fin (n + 1)} (hij : j ≠ i)
    (w : (OverlapRing R n i j)ˣ) :
    ∃ (v : (ChartRing R n i)ˣ) (k : ℤ),
      w = Units.map (algebraMap (ChartRing R n i) (OverlapRing R n i j)).toMonoidHom v *
        awayUnit (S := OverlapRing R n i j) (ratio R i j) ^ k :=
  have := isDomain_chartRing (R := R) i
  exists_eq_unit_mul_awayUnit_zpow (prime_ratio R hij) w

/-- **The exponent of the ratio is determined.** A unit of the `i`-th chart times a power of
`Tⱼ / Tᵢ` is the identity only when the power is the zeroth, so the decomposition of
`Stacks.PicardUFD.exists_eq_unit_mul_ratio_zpow` has a unique exponent. -/
theorem eq_zero_of_map_mul_ratio_zpow_eq_one [IsDomain R] {i j : Fin (n + 1)} (hij : j ≠ i)
    (v : (ChartRing R n i)ˣ) (k : ℤ)
    (h : Units.map (algebraMap (ChartRing R n i) (OverlapRing R n i j)).toMonoidHom v *
      awayUnit (S := OverlapRing R n i j) (ratio R i j) ^ k = 1) : k = 0 :=
  have := isDomain_chartRing (R := R) i
  eq_zero_of_map_mul_awayUnit_zpow_eq_one (prime_ratio R hij) v k h

/-- The ring of functions on the overlap `D₊(TᵢTⱼ)`, as the sections of the structure sheaf of
projective space over that open. -/
def sectionsOverlapEquiv (i j : Fin (n + 1)) :
    OverlapRing R n i j ≃+*
      Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (MvPolynomial.X i * MvPolynomial.X j)) :=
  (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (MvPolynomial.X i * MvPolynomial.X j) (X_mul_X_mem_degree_two R i j)
    (by omega)).commRingCatIsoToRingEquiv

/-- **The ratio `T_k / Tᵢ` stays prime on the overlap `D₊(TᵢTⱼ)`** when `k` differs from both
`i` and `j`. This is the input the triple overlaps of the standard covering need: the functions
on `D₊(TᵢTⱼT_k)` are those on `D₊(TᵢTⱼ)` with this second prime inverted. -/
theorem prime_algebraMap_ratio [IsDomain R] {i j k : Fin (n + 1)} (hj : j ≠ i) (hk : k ≠ i)
    (hjk : j ≠ k) :
    Prime (algebraMap (ChartRing R n i) (OverlapRing R n i j) (ratio R i k)) :=
  have := isDomain_chartRing (R := R) i
  prime_algebraMap_of_not_dvd_pow (prime_ratio R hj).ne_zero (prime_ratio R hk)
    (not_dvd_pow_ratio R hk hj (Ne.symm hjk))

/-- The overlap of two standard charts is the standard open at the product of the two
homogeneous coordinates. -/
theorem basicOpen_X_inf (i j : Fin (n + 1)) :
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j) =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i * MvPolynomial.X j) :=
  (Proj.basicOpen_mul _ _ _).symm

end Charts

/-! ### The two presentations of the sections, compatibly with restriction -/

section OverlapSections

open Stacks.ProjectiveChart TopologicalSpace Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] {n : ℕ}

/-- The ring of functions on the overlap of the `i`-th and `j`-th standard charts, read on the
sections of the structure sheaf over `D₊(Tᵢ) ⊓ D₊(Tⱼ)` rather than over `D₊(TᵢTⱼ)`. This is
`Stacks.PicardUFD.sectionsOverlapEquiv` transported along
`Stacks.PicardUFD.basicOpen_X_inf`; the transport is confined to this definition and to the
proof of `Stacks.PicardUFD.sectionsInfEquiv_algebraMap`, so consumers never see it. -/
def sectionsInfEquiv (i j : Fin (n + 1)) :
    OverlapRing R n i j ≃+*
      Γ(AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
            (MvPolynomial.X j)) :=
  (sectionsOverlapEquiv R i j).trans
    ((AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf.mapIso
      (eqToIso (congrArg op (basicOpen_X_inf R i j).symm))).commRingCatIsoToRingEquiv

/-- **The restriction `Γ(D₊(Tᵢ), 𝒪) ⟶ Γ(D₊(Tᵢ) ⊓ D₊(Tⱼ), 𝒪)` of the structure sheaf is the
algebra map of `Stacks.PicardUFD.algebraChartRingOverlapRing`**, read through the chart
identifications. This is the compatibility with restriction of the two presentations of the
sections: Mathlib's `AlgebraicGeometry.Proj.awayMap_awayToSection`, with the comparison of
`D₊(TᵢTⱼ)` and `D₊(Tᵢ) ⊓ D₊(Tⱼ)` absorbed. -/
theorem sectionsInfEquiv_algebraMap (i j : Fin (n + 1)) (p : MvPolynomial (Fin n) R) :
    sectionsInfEquiv R i j
        (algebraMap (ChartRing R n i) (OverlapRing R n i j) (chartRingEquiv R i p)) =
      (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf.map
        (homOfLE (inf_le_left : Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
            (MvPolynomial.X j) ≤ _)).op (sectionsChartEquiv R i p) := by
  have hmap := Proj.awayMap_awayToSection
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (X_mem_degree_one R j)
    (rfl : (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) =
      MvPolynomial.X i * MvPolynomial.X j)
  have key : CommRingCat.ofHom (HomogeneousLocalization.awayMap
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (X_mem_degree_one R j) rfl) ≫
        Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (MvPolynomial.X i * MvPolynomial.X j) ≫
        (AlgebraicGeometry.Proj
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf.map
          (eqToHom (congrArg op (basicOpen_X_inf R i j).symm)) =
      Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ≫
        (AlgebraicGeometry.Proj
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf.map
          (homOfLE (inf_le_left : Proj.basicOpen
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
            Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
              (MvPolynomial.X j) ≤ _)).op := by
    rw [← Category.assoc, hmap, Category.assoc, ← Functor.map_comp]
    congr 1
  have h3 := RingHom.congr_fun (CommRingCat.hom_ext_iff.mp key) (chartRingEquiv R i p)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at h3
  show (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf.map
        (eqToHom (congrArg op (basicOpen_X_inf R i j).symm))
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i * MvPolynomial.X j)
        (HomogeneousLocalization.awayMap _ (X_mem_degree_one R j) rfl
          (chartRingEquiv R i p))) = _
  exact h3

end OverlapSections

/-! ### Sections of a twist on a standard chart, at the twist degree on the nose -/

section DegreeOneSections

open Stacks.AlgebraicGeometry.ProjTrivialization TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

universe w

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] {f : S}

/-- Two fractions are equal when their numerators and denominators cross-multiply equally. -/
private theorem mk_eq_mk_of_mul_eq {M : Type*} [CommMonoid M] {T : Submonoid M} {a c : M}
    {b d : T} (h : (d : M) * a = b * c) : Localization.mk a b = Localization.mk c d :=
  Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq h)

/-- **Locally on `D₊(f)`, with `f` of degree one, a section of `𝒪(m)` is the trivializing value
`f ^ m` times a fraction of equal degrees.** This is
`Stacks.AlgebraicGeometry.ProjTrivialization.exists_isFraction_of_mem` at `d = 1`, with the twist
degree `m` rather than `m * (1 : ℕ)`, so that no transport enters the sections it speaks of. -/
theorem exists_isFraction_of_mem_degree_one (hf : f ∈ 𝒮 1) (m : ℤ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (a : moduleSections 𝒮 (twistGrading 𝒮 m) W) (x : W) :
    ∃ (V : Opens (ProjectiveSpectrum.top 𝒮)) (_ : x.1 ∈ V) (i : V ⟶ W) (N : ℕ) (u v : S)
      (_ : u ∈ 𝒮 N) (_ : v ∈ 𝒮 N) (hv : ∀ y : V, v ∉ y.1.asHomogeneousIdeal),
      ∀ y : V, Localization.mk u ⟨v, hv y⟩ * trivializingFun 𝒮 m hW (i y) = a.1 (i y) := by
  obtain ⟨V, hxV, i, k, num, den, hnum, hden, hnin, heq⟩ := a.2 x
  refine ⟨V, hxV, i, k + m.toNat, num * f ^ (-m).toNat, den * f ^ m.toNat,
    mul_pow_mem_of_mem_integerGrading 𝒮 hf hnum (by push_cast; omega),
    SetLike.mul_mem_graded hden (by simpa using pow_toNat_mem 𝒮 hf m.toNat),
    fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hnin y)
      (y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hW (i y).2) _), fun y => ?_⟩
  have hy : a.1 (i y) = Localization.mk num ⟨den, hnin y⟩ := heq y
  rw [trivializingFun, Localization.mk_mul, hy]
  exact mk_eq_mk_of_mul_eq (by simp only [Submonoid.coe_mul]; ring)

/-- Pointwise, every section of `𝒪(m)` on an open of `D₊(f)` is the trivializing value `f ^ m`
times an element of the local ring. -/
theorem exists_val_mul_eq_degree_one (hf : f ∈ 𝒮 1) (m : ℤ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (a : moduleSections 𝒮 (twistGrading 𝒮 m) W) (x : W) :
    ∃ ρ : HomogeneousLocalization.AtPrime 𝒮 x.1.asHomogeneousIdeal.toIdeal,
      HomogeneousLocalization.val ρ * trivializingFun 𝒮 m hW x = a.1 x := by
  obtain ⟨V, hxV, i, N, u, v, hu, hv, hvn, heq⟩ :=
    exists_isFraction_of_mem_degree_one 𝒮 hf m hW a x
  exact ⟨HomogeneousLocalization.mk ⟨N, ⟨u, hu⟩, ⟨v, hv⟩, hvn ⟨x.1, hxV⟩⟩, heq ⟨x.1, hxV⟩⟩

/-- **Multiplication by the trivializing section `f ^ m` is a bijection
`Γ(W, 𝒪) → Γ(W, 𝒪(m))`** on every open `W` of the standard chart `D₊(f)` of a degree-one
element `f`. The section is supplied together with the identification of its value, so that the
twist degree is `m` on the nose and no transport along `m * (1 : ℕ) = m` is involved. -/
theorem bijective_smul_trivializingFun (hf : f ∈ 𝒮 1) (m : ℤ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (s : moduleSections 𝒮 (twistGrading 𝒮 m) W) (hs : s.1 = trivializingFun 𝒮 m hW) :
    Function.Bijective
      (fun r : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W) => r • s) := by
  have hval : ∀ (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)) (x : W),
      (r • s).1 x = HomogeneousLocalization.val (r.1 x) * trivializingFun 𝒮 m hW x :=
    fun r x => congrArg (fun z => HomogeneousLocalization.val (r.1 x) * z)
      (congrFun hs x)
  refine ⟨fun r r' h => Subtype.ext (funext fun x => eq_of_val_mul_eq 𝒮 m hW x <|
    (hval r x).symm.trans ((congrFun (congrArg Subtype.val h) x).trans (hval r' x))), fun a => ?_⟩
  choose ρ hρ using exists_val_mul_eq_degree_one 𝒮 hf m hW a
  have hmem : (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒮).pred ρ := by
    intro x
    obtain ⟨V, hxV, i, N, u, v, hu, hv, hvn, heq⟩ :=
      exists_isFraction_of_mem_degree_one 𝒮 hf m hW a x
    refine ⟨V, hxV, i, N, ⟨u, hu⟩, ⟨v, hv⟩, hvn, fun y => eq_of_val_mul_eq 𝒮 m hW (i y) ?_⟩
    rw [hρ, HomogeneousLocalization.val_mk]
    exact (heq y).symm
  exact ⟨⟨ρ, hmem⟩, Subtype.ext (funext fun x => (hval _ x).trans (hρ x))⟩

end DegreeOneSections

/-! ### Local generators on the standard charts -/

section Generators

open Stacks.ProjectiveChart Stacks.SheafOfModules TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] {n : ℕ}

/-- The fraction `Tᵢ ^ m` is a section of `𝒪(m)` on every open of the standard chart `D₊(Tᵢ)`,
with the twist degree written as `m` rather than as `m * (1 : ℕ)`. This is
`Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun_mem` at `d = 1`, restated so that
no transport along `m * ((1 : ℕ) : ℤ) = m` enters the sections it describes. -/
theorem trivializingFun_mem_degree_one (m : ℤ) (i : Fin (n + 1))
    {W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))}
    (hW : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)) :
    Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m hW ∈
      moduleSections (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (twistGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m) W := by
  intro x
  refine ⟨W, x.2, 𝟙 _, (-m).toNat, MvPolynomial.X i ^ m.toNat,
    MvPolynomial.X i ^ (-m).toNat, ?_, pow_X_mem_degree R i _,
    fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hW y.2) _, fun _ => rfl⟩
  show (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ^ m.toNat ∈
    integerGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      ((((-m).toNat : ℕ) : ℤ) + m)
  rw [show ((((-m).toNat : ℕ) : ℤ) + m) = ((m.toNat : ℕ) : ℤ) by omega]
  exact Stacks.AlgebraicGeometry.ProjTrivialization.mem_integerGrading_natCast _
    (pow_X_mem_degree R i _)

/-- The trivializing section `Tᵢ ^ m` of `𝒪(m)` over an open of the standard chart `D₊(Tᵢ)`,
at twist degree `m` on the nose. -/
def trivializingSectionDegreeOne (m : ℤ) (i : Fin (n + 1))
    {W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))}
    (hW : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)) :
    moduleSections (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (twistGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m) W :=
  ⟨Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m hW,
    trivializingFun_mem_degree_one R m i hW⟩

/-- **The twisting sheaf `𝒪(m)` has a local generator on every standard chart `D₊(Tᵢ)` of
projective `n`-space**, namely the trivializing section `Tᵢ ^ m`. -/
def twistChartGenerator (m : ℤ) (i : Fin (n + 1)) :
    GeneratorSections
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace
      (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)) :=
  ⟨trivializingSectionDegreeOne R m i le_rfl,
    fun _ h => bijective_smul_trivializingFun _ (X_mem_degree_one R i) m (h.trans le_rfl) _ rfl⟩

/-! ### The transition units of the twisting sheaves -/

/-- The fraction `Tᵢ ^ m / Tⱼ ^ m`, written with numerator and denominator of the common degree
`m⁺ + m⁻`, as an element of the local ring at a point where both coordinates are invertible. -/
def ratioFun (m : ℤ) (i j : Fin (n + 1))
    {W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))}
    (hWi : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i))
    (hWj : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)) (x : W) :
    HomogeneousLocalization.AtPrime (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      x.1.asHomogeneousIdeal.toIdeal :=
  HomogeneousLocalization.mk
    ⟨m.toNat + (-m).toNat,
      ⟨MvPolynomial.X i ^ m.toNat * MvPolynomial.X j ^ (-m).toNat,
        X_pow_mul_X_pow_mem R rfl i j⟩,
      ⟨MvPolynomial.X i ^ (-m).toNat * MvPolynomial.X j ^ m.toNat,
        X_pow_mul_X_pow_mem R (Nat.add_comm _ _) i j⟩,
      x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
        (x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hWi x.2) _)
        (x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hWj x.2) _)⟩

/-- The fraction `Tᵢ ^ m / Tⱼ ^ m` is a section of the structure sheaf: it is a single
homogeneous fraction of equal numerator and denominator degrees. -/
theorem ratioFun_mem (m : ℤ) (i j : Fin (n + 1))
    {W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))}
    (hWi : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i))
    (hWj : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)) :
    (ProjectiveSpectrum.StructureSheaf.isLocallyFraction
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).pred (ratioFun R m i j hWi hWj) :=
  fun x => ⟨W, x.2, 𝟙 _, m.toNat + (-m).toNat,
    ⟨MvPolynomial.X i ^ m.toNat * MvPolynomial.X j ^ (-m).toNat,
      X_pow_mul_X_pow_mem R rfl i j⟩,
    ⟨MvPolynomial.X i ^ (-m).toNat * MvPolynomial.X j ^ m.toNat,
      X_pow_mul_X_pow_mem R (Nat.add_comm _ _) i j⟩,
    (fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hWi y.2) _)
      (y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hWj y.2) _)), fun _ => rfl⟩

/-- The section `Tᵢ ^ m / Tⱼ ^ m` of the structure sheaf of projective `n`-space, on an open
contained in both standard charts `D₊(Tᵢ)` and `D₊(Tⱼ)`. -/
def ratioSection (m : ℤ) (i j : Fin (n + 1))
    {W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))}
    (hWi : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i))
    (hWj : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)) :
    (ProjectiveSpectrum.Proj.structureSheaf
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).obj.obj (op W) :=
  ⟨ratioFun R m i j hWi hWj, ratioFun_mem R m i j hWi hWj⟩

/-- The two fractions `Tᵢ ^ m / Tⱼ ^ m` and `Tⱼ ^ m / Tᵢ ^ m` are inverse in the local ring. -/
theorem ratioFun_mul (m : ℤ) (i j : Fin (n + 1))
    {W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))}
    (hWi : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i))
    (hWj : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j))
    (x : W) :
    ratioFun R m i j hWi hWj x * ratioFun R m j i hWj hWi x = 1 := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one, ratioFun, ratioFun,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk, Localization.mk_mul,
    ← Localization.mk_one]
  exact mk_eq_mk_of_mul_eq (by simp only [Submonoid.coe_mul, Submonoid.coe_one, one_mul]; ring)

/-- The two fractions `Tᵢ ^ m / Tⱼ ^ m` and `Tⱼ ^ m / Tᵢ ^ m` are inverse to one another. -/
theorem ratioSection_mul (m : ℤ) (i j : Fin (n + 1))
    {W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))}
    (hWi : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i))
    (hWj : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)) :
    ratioSection R m i j hWi hWj * ratioSection R m j i hWj hWi = 1 :=
  Subtype.ext (funext fun x => ratioFun_mul R m i j hWi hWj x)

/-- The unit `(Tᵢ / Tⱼ) ^ m` of the ring of functions on an open contained in both standard
charts `D₊(Tᵢ)` and `D₊(Tⱼ)`. -/
def ratioUnit (m : ℤ) (i j : Fin (n + 1))
    {W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))}
    (hWi : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i))
    (hWj : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)) :
    ((ProjectiveSpectrum.Proj.structureSheaf
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).obj.obj (op W))ˣ :=
  ⟨ratioSection R m i j hWi hWj, ratioSection R m j i hWj hWi,
    ratioSection_mul R m i j hWi hWj, ratioSection_mul R m j i hWj hWi⟩

/-- The fraction `Tᵢ ^ m / Tⱼ ^ m` carries the trivializing value `Tⱼ ^ m` of `𝒪(m)` to the
trivializing value `Tᵢ ^ m`. -/
theorem ratioFun_mul_trivializingFun (m : ℤ) (i j : Fin (n + 1))
    {W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))}
    (hWi : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i))
    (hWj : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j))
    (x : W) :
    HomogeneousLocalization.val (ratioFun R m i j hWi hWj x) *
        Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m hWj x =
      Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m hWi x := by
  rw [ratioFun, HomogeneousLocalization.val_mk,
    Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun,
    Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun, Localization.mk_mul]
  exact mk_eq_mk_of_mul_eq (by simp only [Submonoid.coe_mul]; ring)

/-- **The transition unit of the trivializing sections `Tᵢ ^ m` and `Tⱼ ^ m` of `𝒪(m)` is
`(Tᵢ / Tⱼ) ^ m`.** This is the Čech `1`-cocycle of `𝒪(m)` for the standard covering of
projective `n`-space, and it is the computation Tag 0BXJ turns into the exponent. -/
theorem generatorRatioUnit_twistChartGenerator (m : ℤ) (i j : Fin (n + 1)) :
    generatorRatioUnit
        (X := (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace)
        (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m)
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j))
        (generatorRestrict _ inf_le_right (twistChartGenerator R m j))
        (generatorRestrict _ inf_le_left (twistChartGenerator R m i)) =
      ratioUnit R m i j inf_le_left inf_le_right := by
  refine generatorRatioUnit_eq
    (X := (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace)
    (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m)
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j))
    _ _ (ratioUnit R m i j inf_le_left inf_le_right) ?_
  exact Subtype.ext (funext fun x =>
    (ratioFun_mul_trivializingFun R m i j inf_le_left inf_le_right x).symm)

/-- **Every invertible sheaf on projective `n`-space over a unique factorization domain has a
local generator on every standard chart `D₊(Tᵢ)`**: the Picard group of the chart is trivial by
Tag 0BDA, so the sheaf is trivial there. This is the opening move of Tag 0BXJ. -/
def chartGenerator [IsDomain R] [UniqueFactorizationMonoid R]
    (L : (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
    [IsInvertible
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf
      (structureSheafRing (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace).property L]
    (i : Fin (n + 1)) :
    GeneratorSections
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace
      L (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)) :=
  generatorOfOverIso _
    (Stacks.PicardGroup.overIsoUnitOfSubsingleton L _
      (Stacks.ProjectiveSpace.PicardChart.subsingleton_picardGroup_basicOpen_X R i))

end Generators

/-! ### The homomorphism `ℤ ⟶ Pic(ℙⁿ_R)` -/

section PicardMap

open Stacks.ProjectiveChart Stacks.SheafOfModules TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The polynomial ring in `n + 1` variables is generated in degree one over its degree-zero
part. -/
theorem adjoin_degree_one_eq_top :
    Algebra.adjoin (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0)
        ((MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 1 :
          Set (MvPolynomial (Fin (n + 1)) R))) = ⊤ :=
  top_unique ((Stacks.AlgebraicGeometry.ProjPolyChart.adjoin_range_X_eq_top R n).ge.trans
    (Algebra.adjoin_mono (Set.range_subset_iff.mpr fun i => X_mem_degree_one R i)))

/-- **Projective `n`-space is covered by the standard opens of the degree-one elements**, which
is Tag 01MT's hypothesis. -/
theorem degreeOneCover :
    Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.DegreeOneCover
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) :=
  Stacks.AlgebraicGeometry.ProjDegreeOne.iSup_basicOpen_degreeOne_eq_top _
    (adjoin_degree_one_eq_top R n)

/-- **Every twisting sheaf `𝒪(m)` on projective `n`-space over `R` is invertible.** -/
theorem isInvertible_twistingSheaf (m : ℤ) :
    Stacks.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf
      (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).ringCatIsSheaf
      (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m) :=
  Stacks.AlgebraicGeometry.ProjDegreeOne.isInvertible_twistingSheaf _
    (adjoin_degree_one_eq_top R n) m

/-- **The class of `𝒪(m)` in `Pic(ℙⁿ_R)` is additive in `m`**: the multiplication map of
Equation 01MO is an isomorphism `𝒪(m) ⊗ 𝒪(m') ≅ 𝒪(m + m')`. -/
theorem picardClass_twistingSheaf_add (m m' : ℤ) :
    (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).picardClass
        (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (m + m'))
        (isInvertible_twistingSheaf R n (m + m')) =
      (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).picardClass
        (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m)
        (isInvertible_twistingSheaf R n m) +
      (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).picardClass
        (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m')
        (isInvertible_twistingSheaf R n m') := by
  have := isInvertible_twistingSheaf R n m
  have := isInvertible_twistingSheaf R n m'
  have htens := Stacks.SheafOfModules.isInvertible_tensorSheaf
    (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf
    (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).ringCatIsSheaf
    (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m)
    (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m')
  refine Eq.trans ?_ (AlgebraicGeometry.Scheme.picardClass_tensorSheaf _ _ _ _ _ htens).symm
  refine (AlgebraicGeometry.Scheme.picardClass_eq_iff _ _ _
    (isInvertible_twistingSheaf R n (m + m')) htens).mpr ⟨?_⟩
  exact (Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.twistMultiplicationIso
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (degreeOneCover R n) m m').symm

/-- **The homomorphism `ℤ ⟶ Pic(ℙⁿ_R)`, `m ↦ 𝒪(m)`.** It is additive because the multiplication
map `𝒪(m) ⊗ 𝒪(m') ⟶ 𝒪(m + m')` of Equation 01MO is an isomorphism. That it is injective, or
surjective, is not proved. -/
noncomputable def twistPicardHom :
    ℤ →+ (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).picardGroup :=
  AddMonoidHom.mk'
    (fun m => (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).picardClass
        (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m)
        (isInvertible_twistingSheaf R n m))
    (picardClass_twistingSheaf_add R n)

/-- The homomorphism `twistPicardHom R n` sends `m` to the class of `𝒪(m)` in `Pic(ℙⁿ_R)`. -/
@[simp]
theorem twistPicardHom_apply (m : ℤ) :
    twistPicardHom R n m =
      (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).picardClass
        (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m)
        (isInvertible_twistingSheaf R n m) :=
  rfl

end PicardMap

/-! ### Injectivity of `m ↦ 𝒪(m)` -/

section Injectivity

open Stacks.ProjectiveChart Stacks.SheafOfModules TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- **On the overlap of two opens, the transition unit of two local generators of a trivial
invertible sheaf is a ratio of invertible functions**, one on each of the two opens: compare
both generators with the global generator supplied by the trivialization. -/
theorem exists_isUnit_mul_generatorRatioUnit {X : RingedSpace.{u, u}}
    (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))
    (e : L ≅ _root_.SheafOfModules.unit (structureSheaf X.sheaf))
    {U V : Opens X.carrier} (s : GeneratorSections X L U) (t : GeneratorSections X L V) :
    ∃ (a : (structureSheaf X.sheaf).obj.obj (op U))
        (b : (structureSheaf X.sheaf).obj.obj (op V)), IsUnit a ∧ IsUnit b ∧
      (generatorRatioUnit L (U ⊓ V) (generatorRestrict L inf_le_right t)
            (generatorRestrict L inf_le_left s)).val *
          (structureSheaf X.sheaf).obj.map (homOfLE inf_le_right).op b =
        (structureSheaf X.sheaf).obj.map (homOfLE inf_le_left).op a := by
  refine ⟨(generatorRatioUnit L U (generatorOfIso L e) s).val,
    (generatorRatioUnit L V (generatorOfIso L e) t).val, Units.isUnit _, Units.isUnit _, ?_⟩
  have key : ∀ {W : Opens X.carrier} (h : U ⊓ V ≤ W) (g : GeneratorSections X L W),
      generatorRatioUnit L (U ⊓ V) (generatorOfIso L e) (generatorRestrict L h g) =
        Units.map ((structureSheaf X.sheaf).obj.map (homOfLE h).op).hom
          (generatorRatioUnit L W (generatorOfIso L e) g) := fun h g =>
    (congrArg (fun g' => generatorRatioUnit L (U ⊓ V) g' (generatorRestrict L h g))
      (generatorOfIso_restrict L e h)).symm.trans
    (generatorRatioUnit_restrict L h (generatorOfIso L e) g)
  have hcomp := generatorRatioUnit_comp L (U ⊓ V) (generatorOfIso L e)
    (generatorRestrict L inf_le_right t) (generatorRestrict L inf_le_left s)
  rw [key inf_le_right t, key inf_le_left s] at hcomp
  exact congrArg Units.val hcomp

variable (R : Type u) [CommRing R] (n : ℕ)

/-- A constant is homogeneous of degree zero. -/
theorem C_mem_degree_zero (r : R) :
    (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) R) ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0 :=
  (MvPolynomial.mem_homogeneousSubmodule 0 _).2 (MvPolynomial.isHomogeneous_C _ r)

/-- The chart identification carries a constant `r` of `R` to the fraction `C r / 1`. -/
theorem chartRingEquiv_C (i : Fin (n + 1)) (r : R) :
    chartRingEquiv R i (MvPolynomial.C r) =
      HomogeneousLocalization.mk ⟨0, ⟨MvPolynomial.C r, C_mem_degree_zero R n r⟩,
        1, one_mem _⟩ := by
  simp [chartRingEquiv, chartRingEquivDeg0, chartHom, HomogeneousLocalization.algebraMap_eq,
    HomogeneousLocalization.fromZeroRingHom]
  rfl

/-- At every point of the standard chart `D₊(Tᵢ)`, the function corresponding to a constant `r`
of `R` takes the value `C r / 1`. -/
theorem sectionsChartEquiv_C_apply (i : Fin (n + 1)) (r : R)
    (x : (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X i) : Opens (ProjectiveSpectrum.top
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)))) :
    (sectionsChartEquiv R i (MvPolynomial.C r)).1 x =
      HomogeneousLocalization.mk ⟨0, ⟨MvPolynomial.C r, C_mem_degree_zero R n r⟩,
        1, one_mem _⟩ := by
  show ((Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X i) (X_mem_degree_one R i)
      (by omega)).commRingCatIsoToRingEquiv (chartRingEquiv R i (MvPolynomial.C r))).1 x = _
  rw [chartRingEquiv_C]
  rfl

/-- **Every invertible function on the standard chart `D₊(Tᵢ)` is a unit of `R`**, which is
`Stacks.PicardUFD.isUnit_chartRing_iff` read on sections. -/
theorem exists_eq_sectionsChartEquiv_C_of_isUnit [IsDomain R] (i : Fin (n + 1))
    {a : Γ(AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i))}
    (ha : IsUnit a) :
    ∃ r : R, IsUnit r ∧ a = sectionsChartEquiv R i (MvPolynomial.C r) := by
  obtain ⟨p, hp, hpa⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced
    (P := (sectionsChartEquiv R i).symm a)).mp (ha.map (sectionsChartEquiv R i).symm.toRingHom)
  exact ⟨p, hp, by rw [← hpa]; simp⟩

/-- **The generic point of projective `n`-space over a domain**: the zero ideal, which is prime
because `R` is a domain and relevant because the coordinates are nonzero. -/
noncomputable def zeroPoint [IsDomain R] :
    ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) where
  asHomogeneousIdeal := ⊥
  isPrime := by rw [HomogeneousIdeal.toIdeal_bot]; infer_instance
  not_irrelevant_le := fun h =>
    MvPolynomial.X_ne_zero (0 : Fin (n + 1))
      ((Submodule.mem_bot _).mp
        (h (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos (X_mem_degree_one R 0))))

/-- The generic point lies on every standard chart. -/
theorem zeroPoint_mem_basicOpen [IsDomain R] (k : Fin (n + 1)) :
    zeroPoint R n ∈ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X k) :=
  fun hmem => MvPolynomial.X_ne_zero k ((Submodule.mem_bot _).mp hmem)

/-- **A trivialization of `𝒪(m)` forces a monomial identity.** The transition unit
`(Tᵢ / Tⱼ) ^ m` is a ratio of invertible functions on the two charts, those functions are units
of `R`, and evaluating at the generic point turns the identity into an equation between
monomials of `R[T₀, …, Tₙ]`. -/
theorem exists_isUnit_X_pow_mul_X_pow_mul_C_eq [IsDomain R] {m : ℤ}
    (h : twistPicardHom R n m = 0) (i j : Fin (n + 1)) :
    ∃ r s : R, IsUnit s ∧
      (MvPolynomial.X i ^ m.toNat * MvPolynomial.X j ^ (-m).toNat * MvPolynomial.C s :
          MvPolynomial (Fin (n + 1)) R) =
        MvPolynomial.C r * (MvPolynomial.X i ^ (-m).toNat * MvPolynomial.X j ^ m.toNat) := by
  rw [twistPicardHom_apply] at h
  obtain ⟨e⟩ := (AlgebraicGeometry.Scheme.picardClass_eq_zero_iff _ _
    (isInvertible_twistingSheaf R n m)).mp h
  obtain ⟨a, b, ha, hb, hab⟩ := exists_isUnit_mul_generatorRatioUnit
    (X := (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace)
    (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) m) e
    (twistChartGenerator R m i) (twistChartGenerator R m j)
  rw [generatorRatioUnit_twistChartGenerator] at hab
  have hpt : ratioFun R m i j inf_le_left inf_le_right
        ⟨zeroPoint R n, ⟨zeroPoint_mem_basicOpen R n i, zeroPoint_mem_basicOpen R n j⟩⟩ *
      b.1 ⟨zeroPoint R n, zeroPoint_mem_basicOpen R n j⟩ =
        a.1 ⟨zeroPoint R n, zeroPoint_mem_basicOpen R n i⟩ :=
    congrArg (fun z => z.1 (⟨zeroPoint R n,
      ⟨zeroPoint_mem_basicOpen R n i, zeroPoint_mem_basicOpen R n j⟩⟩ : _)) hab
  have hconst : ∀ (k : Fin (n + 1)) (c : Γ(AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X k))),
      IsUnit c → ∃ r : R, IsUnit r ∧ c.1 ⟨zeroPoint R n, zeroPoint_mem_basicOpen R n k⟩ =
        HomogeneousLocalization.mk ⟨0, ⟨MvPolynomial.C r, C_mem_degree_zero R n r⟩, 1, one_mem _⟩ :=
    fun k c hc => by
      obtain ⟨r, hr, hv⟩ := exists_eq_sectionsChartEquiv_C_of_isUnit R n k hc
      exact ⟨r, hr,
        (congrArg (fun z => z.1 ⟨zeroPoint R n, zeroPoint_mem_basicOpen R n k⟩) hv).trans
          (sectionsChartEquiv_C_apply R n k r _)⟩
  obtain ⟨ri, -, hai⟩ := hconst i _ ha
  obtain ⟨rj, hrj, haj⟩ := hconst j _ hb
  have hkey := (congrArg (fun z => ratioFun R m i j inf_le_left inf_le_right
      ⟨zeroPoint R n, ⟨zeroPoint_mem_basicOpen R n i,
        zeroPoint_mem_basicOpen R n j⟩⟩ * z) haj).symm.trans (hpt.trans hai)
  have hval := congrArg HomogeneousLocalization.val hkey
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk, ratioFun,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hval
  obtain ⟨c, hc⟩ := hval
  have hc0 : (c : MvPolynomial (Fin (n + 1)) R) ≠ 0 := fun h0 =>
    c.2 (by rw [h0]; exact Ideal.zero_mem _)
  refine ⟨ri, rj, hrj, mul_left_cancel₀ hc0 ?_⟩
  simp only [Submonoid.coe_mul, SetLike.GradeZero.coe_one, one_mul, mul_one] at hc
  linear_combination hc

/-- Two monomials in two distinct coordinates, with a unit constant coefficient, agree only when
their exponents do. -/
theorem eq_of_X_pow_mul_X_pow_mul_C_eq [IsDomain R] {i j : Fin (n + 1)} (hij : i ≠ j) {p q : ℕ}
    {r s : R} (hs : IsUnit s)
    (h : (MvPolynomial.X i ^ p * MvPolynomial.X j ^ q * MvPolynomial.C s :
        MvPolynomial (Fin (n + 1)) R) =
      MvPolynomial.C r * (MvPolynomial.X i ^ q * MvPolynomial.X j ^ p)) : p = q := by
  simp only [MvPolynomial.X_pow_eq_monomial, ← MvPolynomial.monomial_zero',
    MvPolynomial.monomial_mul_monomial, one_mul, mul_one, zero_add, add_zero,
    MvPolynomial.monomial_eq_monomial_iff] at h
  rcases h with ⟨he, -⟩ | ⟨h1, -⟩
  · have hi := congrArg (fun f : Fin (n + 1) →₀ ℕ => f i) he
    simpa [Finsupp.single_apply, hij, Ne.symm hij] using hi
  · exact absurd h1 hs.ne_zero

/-- **The homomorphism `ℤ ⟶ Pic(ℙⁿ_R)`, `m ↦ 𝒪(m)`, is injective** for `R` a domain and
`0 < n`. A trivialization of `𝒪(m)` makes the transition unit `(T₀ / T₁) ^ m` a ratio of
constants, which at the generic point reads `T₀^{m⁺} T₁^{m⁻} · s = r · T₀^{m⁻} T₁^{m⁺}` and
forces `m⁺ = m⁻`, hence `m = 0`. -/
@[stacks 0BXJ "injectivity of m ↦ 𝒪(m), for 0 < n; the source states no restriction, but at \
  n = 0 the map is the zero map into the trivial Picard group of ℙ⁰_R ≅ Spec R and is not \
  injective"]
theorem twistPicardHom_injective [IsDomain R] (hn : 0 < n) :
    Function.Injective (twistPicardHom R n) := by
  refine (injective_iff_map_eq_zero (twistPicardHom R n)).mpr fun m hm => ?_
  have hij : (0 : Fin (n + 1)) ≠ ⟨1, by omega⟩ := by
    intro hEq
    simpa using congrArg Fin.val hEq
  obtain ⟨r, s, hs, hrs⟩ :=
    exists_isUnit_X_pow_mul_X_pow_mul_C_eq R n hm (0 : Fin (n + 1)) ⟨1, by omega⟩
  have := eq_of_X_pow_mul_X_pow_mul_C_eq R n hij hs hrs
  omega

end Injectivity

end Stacks.PicardUFD

namespace Stacks.SheafOfModules

/-! ### Scaling a local generator, and comparison on a two-element covering family -/

section Pair

open Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

variable {X : RingedSpace.{u, u}}
  (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))

/-- **A unit multiple of a local generator is a local generator.** Multiplication by the
rescaled section is multiplication by the original one precomposed with multiplication by the
restricted unit, which is bijective. -/
noncomputable def generatorSmulUnit {U : Opens X.carrier}
    (f : ((structureSheaf X.sheaf).obj.obj (op U))ˣ) (s : GeneratorSections X L U) :
    GeneratorSections X L U := by
  refine ⟨f.val • s.val, fun V h => ?_⟩
  have hfun : (fun r : (structureSheaf X.sheaf).obj.obj (op V) =>
        r • L.val.restrictₛₗ (homOfLE h).op (f.val • s.val)) =
      (fun r : (structureSheaf X.sheaf).obj.obj (op V) =>
        r • L.val.restrictₛₗ (homOfLE h).op s.val) ∘
        (· * (Units.map ((structureSheaf X.sheaf).obj.map (homOfLE h).op).hom f).val) := by
    funext r
    change r • L.val.map (homOfLE h).op (f.val • s.val) =
      (r * (Units.map ((structureSheaf X.sheaf).obj.map (homOfLE h).op).hom f).val) •
        L.val.map (homOfLE h).op s.val
    rw [PresheafOfModules.map_smul, smul_smul]
    rfl
  rw [hfun]
  exact (s.property V h).comp (Units.mulRight_bijective _)

/-- The section of a rescaled generator is the rescaled section. -/
@[simp]
theorem generatorSmulUnit_val {U : Opens X.carrier}
    (f : ((structureSheaf X.sheaf).obj.obj (op U))ˣ) (s : GeneratorSections X L U) :
    (generatorSmulUnit L f s).val = f.val • s.val :=
  rfl

/-- The transition unit of two generators over an open contained in both their opens is the
restriction of their transition unit over the intersection of those opens. -/
theorem generatorRatioUnit_restrict_inf {U₀ U₁ V : Opens X.carrier} (h₀ : V ≤ U₀) (h₁ : V ≤ U₁)
    (s : GeneratorSections X L U₀) (t : GeneratorSections X L U₁) :
    generatorRatioUnit L V (generatorRestrict L h₁ t) (generatorRestrict L h₀ s) =
      Units.map ((structureSheaf X.sheaf).obj.map (homOfLE (le_inf h₀ h₁)).op).hom
        (generatorRatioUnit L (U₀ ⊓ U₁) (generatorRestrict L inf_le_right t)
          (generatorRestrict L inf_le_left s)) :=
  (congrArg₂ (generatorRatioUnit L V)
        (generatorRestrict_trans L (inf_le_right : U₀ ⊓ U₁ ≤ U₁) (le_inf h₀ h₁) t)
        (generatorRestrict_trans L (inf_le_left : U₀ ⊓ U₁ ≤ U₀) (le_inf h₀ h₁) s)).symm.trans
    (generatorRatioUnit_restrict L (le_inf h₀ h₁) _ _)

/-- **Two modules with local generators on a two-element covering family and the same
transition unit over the overlap are isomorphic.** With two charts the only transition to compare
is the one over the single overlap: the diagonal transitions are `1` and the reversed one is the
inverse of the compared one. -/
noncomputable def isoOfTransitionEqPair
    {M : _root_.SheafOfModules.{u} (structureSheaf X.sheaf)} {U₀ U₁ : Opens X.carrier}
    (g₀ : GeneratorSections X L U₀) (g₁ : GeneratorSections X L U₁)
    (k₀ : GeneratorSections X M U₀) (k₁ : GeneratorSections X M U₁)
    (hU : (⊤ : Opens X.carrier) ≤ U₀ ⊔ U₁)
    (heq : generatorRatioUnit L (U₀ ⊓ U₁) (generatorRestrict L inf_le_right g₁)
          (generatorRestrict L inf_le_left g₀) =
        generatorRatioUnit M (U₀ ⊓ U₁) (generatorRestrict M inf_le_right k₁)
          (generatorRestrict M inf_le_left k₀)) :
    L ≅ M := by
  refine isoOfTransitionEq L (U := fun b : ULift.{u} Bool => cond b.down U₁ U₀)
    (fun b => match b with | ⟨false⟩ => g₀ | ⟨true⟩ => g₁)
    (fun b => match b with | ⟨false⟩ => k₀ | ⟨true⟩ => k₁)
    (hU.trans (sup_le (le_iSup_of_le ⟨false⟩ le_rfl) (le_iSup_of_le ⟨true⟩ le_rfl))) ?_
  rintro ⟨a⟩ ⟨b⟩ V ha hb
  cases a <;> cases b
  · exact (generatorRatioUnit_self L V _).trans (generatorRatioUnit_self M V _).symm
  · exact (generatorRatioUnit_restrict_inf L ha hb g₀ g₁).trans
      ((congrArg _ heq).trans (generatorRatioUnit_restrict_inf M ha hb k₀ k₁).symm)
  · have hpair : generatorRatioUnit L V (generatorRestrict L ha g₁)
          (generatorRestrict L hb g₀) =
        generatorRatioUnit M V (generatorRestrict M ha k₁) (generatorRestrict M hb k₀) :=
      (generatorRatioUnit_restrict_inf L hb ha g₀ g₁).trans
        ((congrArg _ heq).trans (generatorRatioUnit_restrict_inf M hb ha k₀ k₁).symm)
    exact ((generatorRatioUnit_symm L V (generatorRestrict L ha g₁)
          (generatorRestrict L hb g₀)).trans (congrArg Inv.inv hpair)).trans
      (generatorRatioUnit_symm M V (generatorRestrict M ha k₁)
        (generatorRestrict M hb k₀)).symm
  · exact (generatorRatioUnit_self L V _).trans (generatorRatioUnit_self M V _).symm

end Pair

end Stacks.SheafOfModules

namespace Stacks.PicardUFD

/-! ### The transition fractions of the twists compose -/

section RatioPowers

open Stacks.ProjectiveChart TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- Two products of powers of two commuting elements agree as soon as the exponents of the
first balance; the exponents of the second then balance too. -/
theorem pow_mul_pow_eq_of_add_eq {A : Type*} [CommMonoid A] (a b : A) {p q p' q' P Q : ℕ}
    (h : q + q' + P = Q + p + p') :
    a ^ q * b ^ p * (a ^ q' * b ^ p') * (a ^ P * b ^ Q) =
      a ^ Q * b ^ P * (a ^ p * b ^ q * (a ^ p' * b ^ q')) := by
  have h' : p + p' + Q = P + q + q' := by omega
  calc a ^ q * b ^ p * (a ^ q' * b ^ p') * (a ^ P * b ^ Q)
      = a ^ (q + q' + P) * b ^ (p + p' + Q) := by simp only [pow_add]; ac_rfl
    _ = a ^ (Q + p + p') * b ^ (P + q + q') := by rw [h, h']
    _ = a ^ Q * b ^ P * (a ^ p * b ^ q * (a ^ p' * b ^ q')) := by simp only [pow_add]; ac_rfl

variable {R : Type u} [CommRing R] {n : ℕ} {i j : Fin (n + 1)}
  {W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))}
  (hWi : W ≤ ProjectiveSpectrum.basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i))
  (hWj : W ≤ ProjectiveSpectrum.basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j))

variable (R)

/-- **The fraction `Tᵢ ^ m / Tⱼ ^ m` is multiplicative in the exponent**, pointwise on an open
inside both standard charts. -/
theorem ratioFun_add (m m' : ℤ) (x : W) :
    ratioFun R (m + m') i j hWi hWj x =
      ratioFun R m i j hWi hWj x * ratioFun R m' i j hWi hWj x := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [HomogeneousLocalization.val_mul, ratioFun, ratioFun, ratioFun,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_mk, Localization.mk_mul]
  refine mk_eq_mk_of_mul_eq ?_
  simp only [Submonoid.coe_mul]
  exact pow_mul_pow_eq_of_add_eq _ _ (by omega)

/-- The fraction `Tᵢ ^ 0 / Tⱼ ^ 0` is the unit of the local ring. -/
theorem ratioFun_zero (x : W) : ratioFun R 0 i j hWi hWj x = 1 := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [HomogeneousLocalization.val_one, ratioFun, HomogeneousLocalization.val_mk,
    ← Localization.mk_one]
  refine mk_eq_mk_of_mul_eq ?_
  simp

end RatioPowers

/-! ### The transition units of the twists are the powers of one of them -/

section OverlapRatio

open Stacks.ProjectiveChart TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] {n : ℕ}

/-- The unit `(Tᵢ / Tⱼ) ^ m` of the ring of functions on the overlap `D₊(Tᵢ) ⊓ D₊(Tⱼ)` of two
standard charts, typed at the sections of the structure sheaf rather than at the `RingCat`
spelling of `Stacks.PicardUFD.ratioUnit`. -/
noncomputable def overlapRatioUnit (m : ℤ) (i j : Fin (n + 1)) :
    (Γ(AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (MvPolynomial.X j)))ˣ :=
  ratioUnit R m i j inf_le_left inf_le_right

/-- The two spellings of the transition unit of `𝒪(m)` on an overlap of standard charts agree. -/
theorem overlapRatioUnit_eq (m : ℤ) (i j : Fin (n + 1)) :
    overlapRatioUnit R m i j = ratioUnit R m i j inf_le_left inf_le_right :=
  rfl

/-- Restriction of invertible functions from the standard chart `D₊(Tᵢ)` to its overlap with
`D₊(Tⱼ)`. -/
noncomputable def overlapResUnits (i j : Fin (n + 1)) :
    (Γ(AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i)))ˣ →*
      (Γ(AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
            (MvPolynomial.X j)))ˣ :=
  Units.map ((AlgebraicGeometry.Proj
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf.map
      (homOfLE (inf_le_left : Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (MvPolynomial.X j) ≤ _)).op).hom

variable {R}

/-- **The unit `(Tᵢ / Tⱼ) ^ m` is multiplicative in `m`.** -/
theorem overlapRatioUnit_add (m m' : ℤ) (i j : Fin (n + 1)) :
    overlapRatioUnit R (m + m') i j = overlapRatioUnit R m i j * overlapRatioUnit R m' i j :=
  Units.ext (Subtype.ext (funext fun x => ratioFun_add R inf_le_left inf_le_right m m' x))

/-- The unit `(Tᵢ / Tⱼ) ^ 0` is the identity. -/
theorem overlapRatioUnit_zero (i j : Fin (n + 1)) : overlapRatioUnit R 0 i j = 1 :=
  Units.ext (Subtype.ext (funext fun x => ratioFun_zero R inf_le_left inf_le_right x))

/-- Negating the exponent inverts the unit `(Tᵢ / Tⱼ) ^ m`. -/
theorem overlapRatioUnit_neg (m : ℤ) (i j : Fin (n + 1)) :
    overlapRatioUnit R (-m) i j = (overlapRatioUnit R m i j)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by
    rw [← overlapRatioUnit_add, neg_add_cancel, overlapRatioUnit_zero]

/-- **The transition unit of `𝒪(m)` is the `m`-th power of the transition unit of `𝒪(1)`.** This
is what turns the exponent of the ratio in a unit of the overlap ring into a twist degree. -/
theorem overlapRatioUnit_zpow (m : ℤ) (i j : Fin (n + 1)) :
    overlapRatioUnit R m i j = overlapRatioUnit R 1 i j ^ m := by
  induction m using Int.induction_on with
  | zero => simpa using overlapRatioUnit_zero (R := R) i j
  | succ k ih =>
      rw [overlapRatioUnit_add, ih]
      group
  | pred k ih =>
      rw [show (-(k : ℤ) - 1) = -(k : ℤ) + -1 by ring, overlapRatioUnit_add, ih,
        overlapRatioUnit_neg]
      group

end OverlapRatio

/-! ### The units of an overlap, read as a twist times a unit of one chart -/

section OverlapUnits

open Stacks.ProjectiveChart TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] {n : ℕ}

/-- At a point of the chart `D₊(Tᵢ)` lying also on `D₊(T_{σ k})`, the function attached to the
`k`-th affine coordinate takes the value of the fraction `Tᵢ ^ (-1) / T_{σ k} ^ (-1)`. -/
theorem sectionsChartEquiv_X_apply (i : Fin (n + 1)) (k : Fin n)
    {W : Opens (ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))}
    (hWi : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i))
    (hWj : W ≤ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X (i.succAbove k))) (x : W) :
    (sectionsChartEquiv R i (MvPolynomial.X k)).1 ⟨x.1, hWi x.2⟩ =
      ratioFun R (-1) i (i.succAbove k) hWi hWj x := by
  refine HomogeneousLocalization.val_injective _ ?_
  have hL : ((sectionsChartEquiv R i (MvPolynomial.X k)).1 ⟨x.1, hWi x.2⟩).val =
      Localization.mk (MvPolynomial.X (i.succAbove k) ^ 1)
        ⟨MvPolynomial.X i ^ 1, Submonoid.pow_mem _ (hWi x.2) 1⟩ := by
    show (((Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i) (X_mem_degree_one R i)
        (by omega)).commRingCatIsoToRingEquiv
          (chartRingEquiv R i (MvPolynomial.X k))).1 _).val = _
    rw [chartRingEquiv_X]
    rfl
  rw [hL, ratioFun, HomogeneousLocalization.val_mk]
  refine mk_eq_mk_of_mul_eq ?_
  simp

/-- `Stacks.PicardUFD.sectionsInfEquiv_algebraMap` for an arbitrary element of the chart ring
rather than for the image of a polynomial. -/
theorem sectionsInfEquiv_algebraMap_eq (i j : Fin (n + 1)) (c : ChartRing R n i) :
    sectionsInfEquiv R i j (algebraMap (ChartRing R n i) (OverlapRing R n i j) c) =
      (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf.map
        (homOfLE (inf_le_left : Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
            (MvPolynomial.X j) ≤ _)).op
        (sectionsChartEquiv R i ((chartRingEquiv R i).symm c)) := by
  have h := sectionsInfEquiv_algebraMap R i j ((chartRingEquiv R i).symm c)
  rwa [RingEquiv.apply_symm_apply] at h

/-- **The ratio `T_{σ k} / Tᵢ`, read on the sections over the overlap `D₊(Tᵢ T_{σ k})`, is the
transition section of `𝒪(-1)`.** -/
theorem sectionsInfEquiv_ratio (i : Fin (n + 1)) (k : Fin n) :
    sectionsInfEquiv R i (i.succAbove k)
        (algebraMap (ChartRing R n i) (OverlapRing R n i (i.succAbove k))
          (ratio R i (i.succAbove k))) =
      ratioSection R (-1) i (i.succAbove k) inf_le_left inf_le_right := by
  rw [← chartRingEquiv_X, sectionsInfEquiv_algebraMap]
  exact Subtype.ext (funext fun x =>
    sectionsChartEquiv_X_apply R i k inf_le_left inf_le_right x)

/-- **Every invertible function on the overlap `D₊(TᵢTⱼ)` is the restriction of an invertible
function on `D₊(Tᵢ)` times the transition unit of a twist.** This is
`Stacks.PicardUFD.exists_eq_unit_mul_ratio_zpow` read on sections, with the exponent of the ratio
turned into the twist degree. -/
theorem exists_eq_restrict_mul_overlapRatioUnit [IsDomain R] {i j : Fin (n + 1)}
    (hij : j ≠ i)
    (t : (Γ(AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ⊓
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
            (MvPolynomial.X j)))ˣ) :
    ∃ (m : ℤ) (a : (Γ(AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)))ˣ),
      t = overlapResUnits R i j a * overlapRatioUnit R m i j := by
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
  set Φ := Units.mapEquiv (sectionsInfEquiv R i (i.succAbove k)).toMulEquiv
  obtain ⟨v, κ, hv⟩ := exists_eq_unit_mul_ratio_zpow R hij (Φ.symm t)
  have hA : Φ (Units.map (algebraMap (ChartRing R n i)
        (OverlapRing R n i (i.succAbove k))).toMonoidHom v) =
      overlapResUnits R i (i.succAbove k)
        (Units.map (((chartRingEquiv R i).symm.trans
          (sectionsChartEquiv R i)).toRingHom).toMonoidHom v) :=
    Units.ext (sectionsInfEquiv_algebraMap_eq R i (i.succAbove k) v.val)
  have hB : Φ (awayUnit (S := OverlapRing R n i (i.succAbove k)) (ratio R i (i.succAbove k))) =
      overlapRatioUnit R (-1) i (i.succAbove k) :=
    Units.ext (sectionsInfEquiv_ratio R i k)
  refine ⟨-κ, Units.map (((chartRingEquiv R i).symm.trans
    (sectionsChartEquiv R i)).toRingHom).toMonoidHom v, ?_⟩
  calc t = Φ (Φ.symm t) := (Φ.apply_symm_apply t).symm
    _ = Φ (Units.map (algebraMap (ChartRing R n i)
          (OverlapRing R n i (i.succAbove k))).toMonoidHom v *
        awayUnit (S := OverlapRing R n i (i.succAbove k)) (ratio R i (i.succAbove k)) ^ κ) :=
        congrArg Φ hv
    _ = Φ (Units.map (algebraMap (ChartRing R n i)
          (OverlapRing R n i (i.succAbove k))).toMonoidHom v) *
        Φ (awayUnit (S := OverlapRing R n i (i.succAbove k))
          (ratio R i (i.succAbove k))) ^ κ := by
        rw [map_mul, map_zpow]
    _ = _ := by
        rw [hA, hB, overlapRatioUnit_neg 1, inv_zpow, ← zpow_neg,
          ← overlapRatioUnit_zpow (-κ)]

end OverlapUnits

/-! ### Surjectivity of `m ↦ 𝒪(m)` for the projective line -/

section Surjectivity

open Stacks.ProjectiveChart Stacks.SheafOfModules TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R]

/-- **The projective line is covered by its two standard charts.** -/
theorem le_sup_basicOpen_X :
    (⊤ : Opens (ProjectiveSpectrum.top
        (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R))) ≤
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R)
          (MvPolynomial.X (0 : Fin (1 + 1))) ⊔
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R)
          (MvPolynomial.X (1 : Fin (1 + 1))) := by
  refine le_trans (le_of_eq (iSup_basicOpen_X_eq_top R 1).symm) (iSup_le fun i => ?_)
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

/-- **Every invertible module on the projective line over a unique factorization domain is a
twist `𝒪(m)`.** Each standard chart has trivial Picard group, so the module has a generator there;
the transition unit of the two generators is the restriction of a unit of `D₊(T₀)` times an
integer power of `T₁ / T₀`, and rescaling the generator on `D₊(T₀)` by that unit leaves exactly
the transition unit `(T₀ / T₁) ^ m` of `𝒪(m)`. -/
theorem exists_iso_twistingSheaf [IsDomain R] [UniqueFactorizationMonoid R]
    (L : (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R)).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R)).presheaf
        (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R)).ringCatIsSheaf L) :
    ∃ m : ℤ, Nonempty
      (L ≅ twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R) m) := by
  have hLi := hL
  set U₀ := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R)
    (MvPolynomial.X (0 : Fin (1 + 1)))
  set U₁ := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R)
    (MvPolynomial.X (1 : Fin (1 + 1)))
  obtain ⟨m, a, hma⟩ := exists_eq_restrict_mul_overlapRatioUnit R
    (i := (0 : Fin (1 + 1))) (j := (1 : Fin (1 + 1))) (by decide)
    (generatorRatioUnit L (U₀ ⊓ U₁)
      (generatorRestrict L (inf_le_right : U₀ ⊓ U₁ ≤ U₁)
        (chartGenerator R L (1 : Fin (1 + 1))))
      (generatorRestrict L (inf_le_left : U₀ ⊓ U₁ ≤ U₀)
        (chartGenerator R L (0 : Fin (1 + 1)))))
  refine ⟨m, ⟨isoOfTransitionEqPair L
    (generatorSmulUnit L a⁻¹ (chartGenerator R L (0 : Fin (1 + 1))))
    (chartGenerator R L (1 : Fin (1 + 1)))
    (twistChartGenerator R m (0 : Fin (1 + 1))) (twistChartGenerator R m (1 : Fin (1 + 1)))
    (le_sup_basicOpen_X R) ?_⟩⟩
  have hsmul := generatorRatio_smul L (U₀ ⊓ U₁)
    (generatorRestrict L (inf_le_right : U₀ ⊓ U₁ ≤ U₁)
      (chartGenerator R L (1 : Fin (1 + 1))))
    (generatorRestrict L (inf_le_left : U₀ ⊓ U₁ ≤ U₀)
      (chartGenerator R L (0 : Fin (1 + 1))))
    (generatorRestrict L (inf_le_left : U₀ ⊓ U₁ ≤ U₀)
      (generatorSmulUnit L a⁻¹ (chartGenerator R L (0 : Fin (1 + 1)))))
    (overlapResUnits R (0 : Fin (1 + 1)) 1 a)⁻¹.val
    (PresheafOfModules.map_smul L.val (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).op a⁻¹.val
      (chartGenerator R L (0 : Fin (1 + 1))).val)
  have hcancel : ((overlapResUnits R (0 : Fin (1 + 1)) 1 a)⁻¹ *
        (overlapResUnits R (0 : Fin (1 + 1)) 1 a *
          overlapRatioUnit R m (0 : Fin (1 + 1)) 1)).val =
      (overlapRatioUnit R m (0 : Fin (1 + 1)) 1).val :=
    congrArg Units.val (inv_mul_cancel_left _ _)
  refine Eq.trans (Units.ext ?_) (generatorRatioUnit_twistChartGenerator R m 0 1).symm
  refine hsmul.trans (Eq.trans ?_ hcancel)
  exact congrArg (fun z => (overlapResUnits R (0 : Fin (1 + 1)) 1 a)⁻¹.val * z)
    (congrArg Units.val hma)

/-- **Stacks Project, Tag 0BXJ.** The homomorphism `ℤ ⟶ Pic(ℙ¹_R)`, `m ↦ 𝒪(m)`, is surjective for
`R` a unique factorization domain: every invertible module on the projective line is a twist. -/
@[stacks 0BXJ "surjectivity of m ↦ 𝒪(m) for the projective line, i.e. for n = 1"]
theorem twistPicardHom_surjective [IsDomain R] [UniqueFactorizationMonoid R] :
    Function.Surjective (twistPicardHom R 1) := by
  intro x
  obtain ⟨L, hL, hLx⟩ := Stacks.SheafOfModules.exists_picardClass_eq
    (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R)).presheaf
    (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) R)).ringCatIsSheaf x
  obtain ⟨m, ⟨e⟩⟩ := exists_iso_twistingSheaf R L hL
  refine ⟨m, ?_⟩
  rw [twistPicardHom_apply, ← hLx]
  exact (AlgebraicGeometry.Scheme.picardClass_eq_iff _ _ _
    (isInvertible_twistingSheaf R 1 m) hL).mpr ⟨e.symm⟩

/-- **The homomorphism `ℤ ⟶ Pic(ℙ¹_R)`, `m ↦ 𝒪(m)`, is bijective** for `R` a unique
factorization domain, which is the isomorphism `Pic(ℙ¹_R) ≅ ℤ` of Tag 0BXJ. -/
theorem twistPicardHom_bijective [IsDomain R] [UniqueFactorizationMonoid R] :
    Function.Bijective (twistPicardHom R 1) :=
  ⟨twistPicardHom_injective R 1 Nat.one_pos, twistPicardHom_surjective R⟩

end Surjectivity

end Stacks.PicardUFD

end
