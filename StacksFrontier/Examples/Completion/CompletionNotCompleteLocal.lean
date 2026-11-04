module

public import StacksFrontier.Examples.Completion.CountableVarLocalization
public import StacksFrontier.RingTheory.MvPolynomial.FermatSumOfProducts
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
# The completion of a local ring need not be a complete local ring

Let `k` be the field with two elements, `A` the localization of the polynomial ring in countably
many variables over `k` at its ideal `n` of variables, and `S` the `n`-adic completion of `A`,
a local ring whose maximal ideal `m'` consists of the series with zero constant term. Then `S` is
not `m'`-adically complete.

The witness is the series `z = ∑ᵢ ∑_{j < nᵢ} xⱼ ^ dᵢ` with `dᵢ = 2i + 3` and
`nᵢ = i (dᵢ + 1) dᵢ + 1`. The sums of its first blocks are polynomials all of whose monomials have
degree at least `dᵢ`, hence an `m'`-adic Cauchy sequence, and a limit of that sequence has the same
coefficients as `z`, so completeness would put `z` into `(m')²`. Restricting to the first `nᵢ`
variables and taking homogeneous parts of degree `dᵢ` turns a representation of `z` as a sum of
`t` products of elements of `m'` into a representation of the Fermat polynomial
`∑_{j < nᵢ} Xⱼ ^ dᵢ` as a sum of `t (dᵢ + 1)` products of polynomials without constant term whose
total degrees sum to `t (dᵢ + 1) dᵢ`. For `i = t` that is less than `nᵢ`, which is impossible.

## Main results

* `Stacks.Examples.CountableVarLocalization.completion_not_isPrecomplete_maximalIdeal`: the
  completion of the localization over the field with two elements has a Cauchy sequence for its
  own maximal ideal with no limit.
* `Stacks.Examples.CountableVarLocalization.completion_not_isAdicComplete_maximalIdeal`: the
  completion of the localization over the field with two elements is not complete for its own
  maximal ideal.

## Implementation notes

The degrees `dᵢ` are odd, hence prime to the characteristic, and strictly increasing, so the
witness has finitely many nonzero coefficients in each total degree and is therefore the series
of an element of `S`. Restriction to the first `nᵢ` variables is `MvPowerSeries.killCompl`, which
is multiplicative, so the reduction to a polynomial identity is a ring homomorphism followed by
taking a homogeneous part.

## References

* [Stacks Project, Tag 05JC](https://stacks.math.columbia.edu/tag/05JC)
-/

@[expose] public noncomputable section

namespace Stacks.Examples

namespace CountableVarLocalization

section Monomials

private lemma single_ne_single {α : Type*} {d : ℕ} (hd : d ≠ 0) {j j' : α} (hjj : j ≠ j') :
    (Finsupp.single j d : α →₀ ℕ) ≠ Finsupp.single j' d :=
  fun h => hjj (Finsupp.single_left_injective hd h)

/-- A sum of `d`-th powers of distinct variables has coefficient `1` at the `d`-th power of each
of them and `0` elsewhere. -/
private lemma coeff_sum_X_pow {α R : Type*} [CommRing R] [DecidableEq α] (s : Finset α)
    {d : ℕ} (hd : d ≠ 0) (μ : α →₀ ℕ) :
    ∑ j ∈ s, MvPolynomial.coeff μ ((MvPolynomial.X j : MvPolynomial α R) ^ d) =
      if ∃ j ∈ s, μ = Finsupp.single j d then 1 else 0 := by
  classical
  by_cases h : ∃ j ∈ s, μ = Finsupp.single j d
  · obtain ⟨j, hjs, rfl⟩ := h
    have hzero : ∀ b ∈ s, b ≠ j →
        MvPolynomial.coeff (Finsupp.single j d)
          ((MvPolynomial.X b : MvPolynomial α R) ^ d) = 0 := by
      intro b _ hb
      rw [MvPolynomial.coeff_X_pow]
      exact if_neg (single_ne_single hd hb)
    rw [Finset.sum_eq_single_of_mem j hjs hzero, MvPolynomial.coeff_X_pow, if_pos rfl,
      if_pos ⟨j, hjs, rfl⟩]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun j hjs => ?_
    rw [MvPolynomial.coeff_X_pow]
    exact if_neg fun hh => h ⟨j, hjs, hh.symm⟩

end Monomials

section HomPart

variable {R : Type*} [CommRing R] {N : ℕ}

/-- The degree-`a` homogeneous part of a power series in finitely many variables. -/
private def homPart (a : ℕ) :
    MvPowerSeries (Fin N) R →ₗ[R] MvPolynomial (Fin N) R :=
  (MvPolynomial.homogeneousComponent a).comp (MvPowerSeries.truncTotal (a + 1))

private lemma coeff_homPart (a : ℕ) (φ : MvPowerSeries (Fin N) R) (μ : Fin N →₀ ℕ) :
    MvPolynomial.coeff μ (homPart a φ) =
      if Finsupp.degree μ = a then MvPowerSeries.coeff μ φ else 0 := by
  rw [homPart, LinearMap.comp_apply, MvPolynomial.coeff_homogeneousComponent]
  by_cases h : Finsupp.degree μ = a
  · rw [if_pos h, if_pos h, MvPowerSeries.coeff_truncTotal _ (by omega)]
  · rw [if_neg h, if_neg h]

private lemma totalDegree_homPart_le (a : ℕ) (φ : MvPowerSeries (Fin N) R) :
    (homPart a φ).totalDegree ≤ a :=
  (MvPolynomial.homogeneousComponent_isHomogeneous a _).totalDegree_le

private lemma constantCoeff_homPart (a : ℕ) (φ : MvPowerSeries (Fin N) R)
    (hφ : MvPowerSeries.coeff 0 φ = 0) :
    MvPolynomial.constantCoeff (homPart a φ) = 0 := by
  rw [MvPolynomial.constantCoeff_eq, coeff_homPart]
  by_cases h : a = 0
  · subst h
    rw [if_pos (by simp), hφ]
  · rw [if_neg (by simp; omega)]

/-- The degrees of the two factors of a pair in the antidiagonal of `μ` add up to that of `μ`. -/
private lemma degree_add_of_mem_antidiagonal {α : Type*} [DecidableEq α] {μ : α →₀ ℕ}
    {x : (α →₀ ℕ) × (α →₀ ℕ)} (hx : x ∈ Finset.antidiagonal μ) :
    Finsupp.degree x.1 + Finsupp.degree x.2 = Finsupp.degree μ := by
  rw [← Finset.mem_antidiagonal.mp hx, map_add]

/-- Taking the degree-`d` part of a product collects the products of homogeneous parts of
complementary degrees. -/
private lemma homPart_mul (d : ℕ) (φ ψ : MvPowerSeries (Fin N) R) :
    homPart d (φ * ψ) = ∑ a ∈ Finset.range (d + 1), homPart a φ * homPart (d - a) ψ := by
  classical
  ext μ
  rw [coeff_homPart, MvPolynomial.coeff_sum]
  have hterm : ∀ a ∈ Finset.range (d + 1),
      MvPolynomial.coeff μ (homPart a φ * homPart (d - a) ψ) =
        ∑ x ∈ Finset.antidiagonal μ,
          (if Finsupp.degree x.1 = a then MvPowerSeries.coeff x.1 φ else 0) *
            (if Finsupp.degree x.2 = d - a then MvPowerSeries.coeff x.2 ψ else 0) := by
    intro a _
    rw [MvPolynomial.coeff_mul]
    exact Finset.sum_congr rfl fun x _ => by rw [coeff_homPart, coeff_homPart]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  by_cases hμ : Finsupp.degree μ = d
  · rw [if_pos hμ, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hdeg := degree_add_of_mem_antidiagonal hx
    have hzero : ∀ b ∈ Finset.range (d + 1), b ≠ Finsupp.degree x.1 →
        (if Finsupp.degree x.1 = b then MvPowerSeries.coeff x.1 φ else 0) *
          (if Finsupp.degree x.2 = d - b then MvPowerSeries.coeff x.2 ψ else 0) = 0 := by
      intro b _ hb
      rw [if_neg fun h => hb h.symm, zero_mul]
    rw [Finset.sum_eq_single_of_mem (Finsupp.degree x.1)
      (Finset.mem_range.mpr (by omega)) hzero, if_pos rfl, if_pos (by omega)]
  · rw [if_neg hμ]
    symm
    refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun a ha => ?_
    have hdeg := degree_add_of_mem_antidiagonal hx
    have ha' : a ≤ d := Finset.mem_range_succ_iff.mp ha
    by_cases h1 : Finsupp.degree x.1 = a
    · have h2 : Finsupp.degree x.2 ≠ d - a := fun hcon => hμ (by omega)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

end HomPart

section Blocks

/-- The degree of the `i`-th homogeneous block of the witness. -/
private def blockDeg (i : ℕ) : ℕ := 2 * i + 3

/-- The number of variables of the `i`-th homogeneous block of the witness. -/
private def blockNum (i : ℕ) : ℕ := i * (blockDeg i + 1) * blockDeg i + 1

private lemma two_le_blockDeg (i : ℕ) : 2 ≤ blockDeg i := by
  simp only [blockDeg]
  omega

private lemma blockDeg_ne_zero (i : ℕ) : blockDeg i ≠ 0 := by
  have := two_le_blockDeg i
  omega

private lemma lt_blockDeg (i : ℕ) : i < blockDeg i := by
  simp only [blockDeg]
  omega

private lemma blockDeg_injective : Function.Injective blockDeg := by
  intro a b h
  simp only [blockDeg] at h
  omega

private lemma blockNum_mono : Monotone blockNum := by
  intro a b hab
  simp only [blockNum, blockDeg]
  have h : 2 * a + 3 ≤ 2 * b + 3 := by omega
  gcongr

/-- The multidegrees carrying the witness: the `dᵢ`-th power of the `j`-th variable for
`j < nᵢ`. -/
private def blockMonomials : Set (ℕ →₀ ℕ) :=
  {ν | ∃ i, ∃ j < blockNum i, ν = Finsupp.single j (blockDeg i)}

variable (T : CountableVarLocalization)

/-- The witness series: coefficient `1` at the `dᵢ`-th power of the `j`-th variable for every
`i` and every `j < nᵢ`, and `0` elsewhere. -/
private def blockSeries : MvPowerSeries ℕ T.k := Set.indicator blockMonomials 1

private lemma coeff_blockSeries_of_mem {ν : ℕ →₀ ℕ} (hν : ν ∈ blockMonomials) :
    MvPowerSeries.coeff ν (blockSeries T) = 1 := by
  rw [MvPowerSeries.coeff_apply, blockSeries, Set.indicator_of_mem hν]
  rfl

private lemma coeff_blockSeries_of_notMem {ν : ℕ →₀ ℕ} (hν : ν ∉ blockMonomials) :
    MvPowerSeries.coeff ν (blockSeries T) = 0 := by
  rw [MvPowerSeries.coeff_apply, blockSeries, Set.indicator_of_notMem hν]

private lemma blockSeries_degreewise_finite (D : ℕ) :
    {ν : ℕ →₀ ℕ | Finsupp.degree ν = D ∧
      MvPowerSeries.coeff ν (blockSeries T) ≠ 0}.Finite := by
  classical
  refine Set.Finite.subset
    (((Finset.range (blockNum D)).image (fun j => Finsupp.single j D)).finite_toSet) ?_
  rintro ν ⟨hdeg, hcoeff⟩
  by_cases hν : ν ∈ blockMonomials
  · obtain ⟨i, j, hj, rfl⟩ := hν
    have hD : blockDeg i = D := by rw [← hdeg, Finsupp.degree_single]
    have hiD : i ≤ D := hD ▸ (lt_blockDeg i).le
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range]
    exact ⟨j, lt_of_lt_of_le hj (blockNum_mono hiD), by rw [hD]⟩
  · exact absurd (coeff_blockSeries_of_notMem T hν) hcoeff

/-- The sum of the blocks of the witness of index below `M`. -/
private def blockPoly (M : ℕ) : T.P :=
  ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range (blockNum i),
    (MvPolynomial.X j : T.P) ^ blockDeg i

private lemma coeff_blockPoly (M : ℕ) (ν : ℕ →₀ ℕ) :
    MvPolynomial.coeff ν (blockPoly T M) =
      ∑ i ∈ Finset.range M,
        if ∃ j ∈ Finset.range (blockNum i), ν = Finsupp.single j (blockDeg i)
          then (1 : T.k) else 0 := by
  classical
  rw [blockPoly, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.coeff_sum]
  exact coeff_sum_X_pow _ (blockDeg_ne_zero i) _

private lemma coeff_blockPoly_single {M i j : ℕ} (hi : i < M) (hj : j < blockNum i) :
    MvPolynomial.coeff (Finsupp.single j (blockDeg i)) (blockPoly T M) = 1 := by
  classical
  have hother : ∀ b ∈ Finset.range M, b ≠ i →
      (if ∃ c ∈ Finset.range (blockNum b),
          (Finsupp.single j (blockDeg i) : ℕ →₀ ℕ) = Finsupp.single c (blockDeg b)
        then (1 : T.k) else 0) = 0 := by
    intro b _ hb
    refine if_neg ?_
    rintro ⟨c, -, hc⟩
    refine hb (blockDeg_injective ?_).symm
    rw [← Finsupp.degree_single j (blockDeg i), hc, Finsupp.degree_single]
  rw [coeff_blockPoly T M, Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hi) hother,
    if_pos ⟨j, Finset.mem_range.mpr hj, rfl⟩]

private lemma coeff_blockPoly_eq_zero {M : ℕ} {ν : ℕ →₀ ℕ} (hν : ν ∉ blockMonomials) :
    MvPolynomial.coeff ν (blockPoly T M) = 0 := by
  classical
  rw [coeff_blockPoly T M]
  refine Finset.sum_eq_zero fun i _ => if_neg ?_
  rintro ⟨j, hj, rfl⟩
  exact hν ⟨i, j, Finset.mem_range.mp hj, rfl⟩

/-- Below degree `M` the sum of the first `M` blocks has the coefficients of the witness. -/
private lemma coeff_blockPoly_eq_coeff_blockSeries (M : ℕ) {ν : ℕ →₀ ℕ}
    (hν : Finsupp.degree ν < M) :
    MvPolynomial.coeff ν (blockPoly T M) = MvPowerSeries.coeff ν (blockSeries T) := by
  by_cases h : ν ∈ blockMonomials
  · obtain ⟨i, j, hj, rfl⟩ := h
    have hdeg : Finsupp.degree (Finsupp.single j (blockDeg i)) = blockDeg i :=
      Finsupp.degree_single _ _
    have hiM : i < M := by
      have := lt_blockDeg i
      omega
    rw [coeff_blockPoly_single T hiM hj, coeff_blockSeries_of_mem T ⟨i, j, hj, rfl⟩]
  · rw [coeff_blockPoly_eq_zero T h, coeff_blockSeries_of_notMem T h]

private lemma blockPoly_mem_pow (M : ℕ) : blockPoly T M ∈ T.m ^ 2 := by
  refine (MvPolynomial.mem_pow_idealOfVars_iff' 2 _).2 fun ν hν => ?_
  refine coeff_blockPoly_eq_zero T ?_
  rintro ⟨i, j, -, rfl⟩
  have := two_le_blockDeg i
  rw [Finsupp.degree_single] at hν
  omega

end Blocks

section Witness

variable (T : CountableVarLocalization)

/-- The element of the completion whose series is the witness. -/
private def blockElt : T.S :=
  (T.existsUnique_series_of_degreewise_finite (blockSeries T)
    (blockSeries_degreewise_finite T)).choose

private lemma series_blockElt : T.series (blockElt T) = blockSeries T :=
  (T.existsUnique_series_of_degreewise_finite (blockSeries T)
    (blockSeries_degreewise_finite T)).choose_spec.1

private lemma eq_blockElt_of_series {x : T.S} (hx : T.series x = blockSeries T) :
    x = blockElt T :=
  (T.existsUnique_series_of_degreewise_finite (blockSeries T)
    (blockSeries_degreewise_finite T)).choose_spec.2 x hx

/-- The image in the completion of the sum of the first `M` blocks. -/
private def blockApprox (M : ℕ) : T.S :=
  AdicCompletion.of T.n T.A (algebraMap T.P T.A (blockPoly T M))

private lemma series_blockApprox (M : ℕ) :
    T.series (blockApprox T M) = (blockPoly T M : MvPowerSeries ℕ T.k) :=
  T.series_of_mvPolynomial _

/-- The image of a polynomial all of whose monomials have degree at least `M` lies in the `M`-th
power of the maximal ideal of the completion. -/
private lemma mem_pow_m'_of_mem_pow_m {M : ℕ} {p : T.P} (hp : p ∈ T.m ^ M) :
    AdicCompletion.of T.n T.A (algebraMap T.P T.A p) ∈ T.m' ^ M := by
  set ψ : T.P →+* T.S := (algebraMap T.A T.S).comp (algebraMap T.P T.A) with hψ
  have hψ_apply : ∀ q : T.P, ψ q = AdicCompletion.of T.n T.A (algebraMap T.P T.A q) := by
    intro q
    rw [hψ, RingHom.comp_apply, AdicCompletion.algebraMap_apply]
    simp
  have hm : Ideal.map ψ T.m ≤ T.m' := by
    rw [Ideal.map_le_iff_le_comap]
    intro q hq
    rw [Ideal.mem_comap, T.mem_m'_iff_coeff_zero, hψ_apply q, T.series_of_mvPolynomial,
      MvPolynomial.coeff_coe]
    have hq' : q ∈ MvPolynomial.idealOfVars ℕ T.k ^ 1 := by
      rw [pow_one]
      exact hq
    exact (MvPolynomial.mem_pow_idealOfVars_iff' 1 q).mp hq' 0 (by simp)
  have hle : Ideal.map ψ (T.m ^ M) ≤ T.m' ^ M := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hm M
  rw [← hψ_apply p]
  exact hle (Ideal.mem_map_of_mem ψ hp)

/-- An element of the `M`-th power of the maximal ideal has a series whose coefficients vanish
below degree `M`. -/
private lemma coeff_series_eq_zero_of_mem_pow :
    ∀ (M : ℕ) (x : T.S), x ∈ T.m' ^ M →
      ∀ ν : ℕ →₀ ℕ, Finsupp.degree ν < M → MvPowerSeries.coeff ν (T.series x) = 0 := by
  intro M
  induction M with
  | zero => exact fun _ _ _ hν => absurd hν (Nat.not_lt_zero _)
  | succ M ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb ν hν
        classical
        rw [T.series_mul, MvPowerSeries.coeff_mul]
        refine Finset.sum_eq_zero fun x hx => ?_
        have hdeg := degree_add_of_mem_antidiagonal hx
        rcases Nat.eq_zero_or_pos (Finsupp.degree x.2) with hb2 | hb2
        · have hb0 : x.2 = 0 := by rwa [Finsupp.degree_eq_zero_iff] at hb2
          rw [hb0, (T.mem_m'_iff_coeff_zero b).mp hb, mul_zero]
        · rw [ih a ha x.1 (by omega), zero_mul]
      · intro p q hp hq ν hν
        rw [T.series_add, map_add, hp ν hν, hq ν hν, add_zero]

/-- An element of the square of the maximal ideal is a finite sum of products of elements with
zero constant term. -/
private lemma exists_sum_repr {x : T.S} (hx : x ∈ T.m' ^ 2) :
    ∃ (M : ℕ) (f g : ℕ → T.S), (∀ i ∈ Finset.range M, f i ∈ T.m' ∧ g i ∈ T.m') ∧
      x = ∑ i ∈ Finset.range M, f i * g i := by
  classical
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    exact ⟨1, fun _ => a, fun _ => b, by simp [ha, hb], by simp⟩
  · rintro x y ⟨M₁, f₁, g₁, h₁, rfl⟩ ⟨M₂, f₂, g₂, h₂, rfl⟩
    refine ⟨M₁ + M₂, fun i => if i < M₁ then f₁ i else f₂ (i - M₁),
      fun i => if i < M₁ then g₁ i else g₂ (i - M₁), ?_, ?_⟩
    · intro i hi
      by_cases h : i < M₁
      · simpa [h] using h₁ i (Finset.mem_range.mpr h)
      · have hi' : i - M₁ < M₂ := by
          have := Finset.mem_range.mp hi
          omega
        simpa [h] using h₂ (i - M₁) (Finset.mem_range.mpr hi')
    · rw [Finset.sum_range_add]
      congr 1
      · exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
      · exact Finset.sum_congr rfl fun i _ => by simp

end Witness

section Restriction

variable (T : CountableVarLocalization)

/-- Restriction of a series to its first `N` variables. -/
private def restrictFin (N : ℕ) :
    MvPowerSeries ℕ T.k →ₐ[T.k] MvPowerSeries (Fin N) T.k :=
  MvPowerSeries.killCompl (Fin.valEmbedding)

private lemma coeff_restrictFin (N : ℕ) (φ : MvPowerSeries ℕ T.k) (μ : Fin N →₀ ℕ) :
    MvPowerSeries.coeff μ (restrictFin T N φ) =
      MvPowerSeries.coeff (Finsupp.embDomain Fin.valEmbedding μ) φ :=
  MvPowerSeries.coeff_killCompl _ _

private lemma degree_embDomain_val {N : ℕ} (μ : Fin N →₀ ℕ) :
    Finsupp.degree (Finsupp.embDomain (Fin.valEmbedding (n := N)) μ) = Finsupp.degree μ := by
  rw [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]

private lemma embDomain_val_eq_single_iff {N : ℕ} {μ : Fin N →₀ ℕ} {j c : ℕ} (hc : c ≠ 0) :
    Finsupp.embDomain (Fin.valEmbedding (n := N)) μ = Finsupp.single j c ↔
      ∃ h : j < N, μ = Finsupp.single ⟨j, h⟩ c := by
  classical
  constructor
  · intro h
    have hsupp : (Finsupp.embDomain (Fin.valEmbedding (n := N)) μ).support = {j} := by
      rw [h, Finsupp.support_single_ne_zero _ hc]
    rw [Finsupp.support_embDomain] at hsupp
    have hj : j ∈ μ.support.map (Fin.valEmbedding (n := N)) := by simp [hsupp]
    obtain ⟨j₀, -, hval⟩ := Finset.mem_map.mp hj
    have hlt : j < N := hval ▸ j₀.isLt
    refine ⟨hlt, Finsupp.embDomain_injective (Fin.valEmbedding (n := N)) ?_⟩
    rw [h, Finsupp.embDomain_single]
    congr 1
  · rintro ⟨hlt, rfl⟩
    rw [Finsupp.embDomain_single]
    rfl

/-- Every homogeneous part of the restriction of an element of the maximal ideal has zero
constant coefficient. -/
private lemma constantCoeff_homPart_restrictFin (N a : ℕ) {x : T.S} (hx : x ∈ T.m') :
    MvPolynomial.constantCoeff (homPart a (restrictFin T N (T.series x))) = 0 :=
  constantCoeff_homPart _ _ (by
    rw [coeff_restrictFin, Finsupp.embDomain_zero]
    exact (T.mem_m'_iff_coeff_zero x).mp hx)

/-- Restricting the witness to the first `nᵢ` variables and taking its degree-`dᵢ` part leaves
the Fermat polynomial of degree `dᵢ` in `nᵢ` variables. -/
private lemma homPart_restrictFin_blockSeries (i : ℕ) :
    homPart (blockDeg i) (restrictFin T (blockNum i) (blockSeries T)) =
      ∑ j : Fin (blockNum i),
        (MvPolynomial.X j : MvPolynomial (Fin (blockNum i)) T.k) ^ blockDeg i := by
  classical
  ext μ
  rw [coeff_homPart, MvPolynomial.coeff_sum,
    coeff_sum_X_pow Finset.univ (blockDeg_ne_zero i) μ]
  by_cases hμ : ∃ j ∈ (Finset.univ : Finset (Fin (blockNum i))),
      μ = Finsupp.single j (blockDeg i)
  · obtain ⟨j, -, rfl⟩ := hμ
    rw [if_pos (Finsupp.degree_single _ _), coeff_restrictFin, Finsupp.embDomain_single,
      if_pos ⟨j, Finset.mem_univ j, rfl⟩]
    exact coeff_blockSeries_of_mem T ⟨i, j, j.isLt, rfl⟩
  · rw [if_neg hμ]
    by_cases hdeg : Finsupp.degree μ = blockDeg i
    · rw [if_pos hdeg, coeff_restrictFin]
      refine coeff_blockSeries_of_notMem T ?_
      rintro ⟨i', j', hj', hsingle⟩
      have hdd : blockDeg i' = blockDeg i := by
        rw [← Finsupp.degree_single j' (blockDeg i'), ← hsingle, degree_embDomain_val, hdeg]
      rw [hdd] at hsingle
      obtain ⟨hlt, rfl⟩ := (embDomain_val_eq_single_iff (blockDeg_ne_zero i)).mp hsingle
      exact hμ ⟨⟨j', hlt⟩, Finset.mem_univ _, rfl⟩
    · rw [if_neg hdeg]

end Restriction

section NotComplete

variable (T : CountableVarLocalization)

/-- A representation of the witness as a sum of `M` products becomes a representation of the
Fermat polynomial of degree `d_M` in `n_M` variables as a sum of `M (d_M + 1)` products. -/
private lemma fermat_eq_sum_homPart (M : ℕ) (f g : ℕ → T.S)
    (hsum : blockElt T = ∑ i ∈ Finset.range M, f i * g i) :
    (∑ j : Fin (blockNum M),
        (MvPolynomial.X j : MvPolynomial (Fin (blockNum M)) T.k) ^ blockDeg M) =
      ∑ x ∈ Finset.range M ×ˢ Finset.range (blockDeg M + 1),
        homPart x.2 (restrictFin T (blockNum M) (T.series (f x.1))) *
          homPart (blockDeg M - x.2) (restrictFin T (blockNum M) (T.series (g x.1))) := by
  have hseries : T.series (blockElt T) =
      ∑ i ∈ Finset.range M, T.series (f i) * T.series (g i) := by
    rw [hsum, ← T.seriesHom_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_mul, T.seriesHom_apply, T.seriesHom_apply]
  have hdouble : homPart (blockDeg M)
        (restrictFin T (blockNum M) (T.series (blockElt T))) =
      ∑ i ∈ Finset.range M, ∑ a ∈ Finset.range (blockDeg M + 1),
        homPart a (restrictFin T (blockNum M) (T.series (f i))) *
          homPart (blockDeg M - a) (restrictFin T (blockNum M) (T.series (g i))) := by
    rw [hseries, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, homPart_mul]
  simp only [Finset.sum_product]
  rw [← hdouble, series_blockElt, homPart_restrictFin_blockSeries]

variable [Fintype T.k]

/-- The witness is not a finite sum of products of elements with zero constant term. -/
private lemma blockElt_notMem_sq (hchar : ∀ i : ℕ, ((blockDeg i : ℕ) : T.k) ≠ 0) :
    blockElt T ∉ T.m' ^ 2 := by
  classical
  intro hmem
  obtain ⟨M, f, g, hfg, hsum⟩ := exists_sum_repr T hmem
  have hkey := fermat_eq_sum_homPart T M f g hsum
  refine MvPolynomial.sum_X_pow_ne_sum_mul (K := T.k) (n := blockNum M) (d := blockDeg M)
    (s := Finset.range M ×ˢ Finset.range (blockDeg M + 1))
    (fun x : ℕ × ℕ => homPart x.2 (restrictFin T (blockNum M) (T.series (f x.1))))
    (fun x : ℕ × ℕ =>
      homPart (blockDeg M - x.2) (restrictFin T (blockNum M) (T.series (g x.1))))
    (hchar M) (two_le_blockDeg M) ?_ ?_ ?_ hkey
  · exact fun x hx => constantCoeff_homPart_restrictFin T _ _
      (hfg x.1 (Finset.mem_product.mp hx).1).1
  · exact fun x hx => constantCoeff_homPart_restrictFin T _ _
      (hfg x.1 (Finset.mem_product.mp hx).1).2
  · refine lt_of_le_of_lt (Finset.sum_le_sum (g := fun _ => blockDeg M) fun x hx => ?_) ?_
    · have := Finset.mem_range.mp (Finset.mem_product.mp hx).2
      exact (Nat.add_le_add (totalDegree_homPart_le _ _) (totalDegree_homPart_le _ _)).trans
        (by omega)
    · rw [Finset.sum_const, Finset.card_product, Finset.card_range, Finset.card_range,
        smul_eq_mul, blockNum]
      exact Nat.lt_succ_self _

/-- The completion is not precomplete for its own maximal ideal. -/
private lemma not_isPrecomplete_m' (hchar : ∀ i : ℕ, ((blockDeg i : ℕ) : T.k) ≠ 0) :
    ¬ IsPrecomplete T.m' T.S := by
  intro hprec
  have hcauchy : ∀ {M M' : ℕ}, M ≤ M' →
      blockApprox T M ≡ blockApprox T M'
        [SMOD T.m' ^ M • (⊤ : Submodule T.S T.S)] := by
    intro M M' hMM'
    rw [SModEq.sub_mem]
    have hdif : blockPoly T M - blockPoly T M' ∈ T.m ^ M := by
      refine (MvPolynomial.mem_pow_idealOfVars_iff' M _).2 fun ν hν => ?_
      rw [MvPolynomial.coeff_sub, coeff_blockPoly_eq_coeff_blockSeries T M hν,
        coeff_blockPoly_eq_coeff_blockSeries T M' (by omega), sub_self]
    have hsub : blockApprox T M - blockApprox T M' =
        AdicCompletion.of T.n T.A
          (algebraMap T.P T.A (blockPoly T M - blockPoly T M')) := by
      rw [blockApprox, blockApprox, map_sub, map_sub]
    rw [hsub]
    simpa [smul_eq_mul, Ideal.mul_top] using mem_pow_m'_of_mem_pow_m T hdif
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hprec (f := blockApprox T) hcauchy
  have hmem : ∀ M : ℕ, L - blockApprox T M ∈ T.m' ^ M := by
    intro M
    have h : blockApprox T M - L ∈ T.m' ^ M := by
      simpa [smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.1 (hL M)
    simpa using neg_mem h
  have hLseries : T.series L = blockSeries T := by
    ext ν
    have h0 : MvPowerSeries.coeff ν
        (T.series (L - blockApprox T (Finsupp.degree ν + 1))) = 0 :=
      coeff_series_eq_zero_of_mem_pow T (Finsupp.degree ν + 1) _
        (hmem (Finsupp.degree ν + 1)) ν (by omega)
    rw [← T.seriesHom_apply, map_sub, T.seriesHom_apply, T.seriesHom_apply, map_sub,
      series_blockApprox, sub_eq_zero] at h0
    rw [h0, MvPolynomial.coeff_coe,
      coeff_blockPoly_eq_coeff_blockSeries T (Finsupp.degree ν + 1) (by omega)]
  have hL2 : L ∈ T.m' ^ 2 := by
    have h2 : blockApprox T 2 ∈ T.m' ^ 2 :=
      mem_pow_m'_of_mem_pow_m T (blockPoly_mem_pow T 2)
    simpa using add_mem (hmem 2) h2
  exact blockElt_notMem_sq T hchar (eq_blockElt_of_series T hLseries ▸ hL2)

end NotComplete

/-- The situation of Stacks 110.7 over the field with two elements. -/
def binary : CountableVarLocalization := ⟨ZMod 2⟩

/-- The witness is an `m'`-adic Cauchy sequence in the completion with no limit: the completion
is not even precomplete for its own maximal ideal. -/
theorem completion_not_isPrecomplete_maximalIdeal :
    ¬ IsPrecomplete (IsLocalRing.maximalIdeal binary.S) binary.S := by
  have : Fintype binary.k := inferInstanceAs (Fintype (ZMod 2))
  rw [binary.maximalIdeal_eq_ker_constantTerm]
  refine not_isPrecomplete_m' binary fun i h => ?_
  have h2 : (2 : ℕ) ∣ blockDeg i := (ZMod.natCast_eq_zero_iff (blockDeg i) 2).mp h
  rw [blockDeg] at h2
  omega

/-- The completion of `A` at its maximal ideal is not a complete local ring: it is not complete
for the topology of its own maximal ideal (Stacks 05JC, part (2)). -/
theorem completion_not_isAdicComplete_maximalIdeal :
    ¬ IsAdicComplete (IsLocalRing.maximalIdeal binary.S) binary.S :=
  fun hc => completion_not_isPrecomplete_maximalIdeal hc.toIsPrecomplete

end CountableVarLocalization

end Stacks.Examples

end
