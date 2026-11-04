module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Power series that are rational modulo every power of an ideal

Let `R` be a domain and `f ∈ R⟦T⟧`. Suppose that for a family of ideals `Iₙ` of `R` with
`⋂ₙ Iₙ = 0` (for instance the powers of a maximal ideal of a Noetherian domain, by Krull's
intersection theorem), `f` agrees modulo `Iₙ` with a quotient `P / Q` of polynomials of degrees at
most `a` and `b` whose coefficients in degrees `a` and `b` are units modulo `Iₙ`. Then `f` is a
rational function, `B f = A` with `B ≠ 0`, and for *every* such expression
`deg A - deg B = a - b`. In particular the integer `a - b` is determined by `f` alone: two such
families of approximations of `f`, for two different families of ideals, have the same `a - b`.

This is how the degree of an L-function is pinned down by the trace formula at finite levels. If
`L(X, ℱ) ∈ R⟦T⟧` reduces modulo every `𝔪ⁿ` to `det(1 - π^* T | RΓ_c(X_k̄, ℱ ⊗ R/𝔪ⁿ))⁻¹`, a quotient
of characteristic polynomials of invertible endomorphisms of a minimal perfect complex, then
`a - b = -χ(X_k̄, ℱ ⊗ R/𝔪)`. So this Euler characteristic does not depend on `𝔪`, and it is
unchanged when the coefficients are moved by a ring automorphism `σ` of `R`
(`Stacks.Drinfeld.HasRationalApprox.of_map`). That Galois symmetry is the input to the computation
of the Euler characteristic of a rank one sheaf of finite order on a curve.

## Main definitions

* `Stacks.Drinfeld.HasRationalApprox f I a b`: modulo every `I n`, `Q f ≡ P` with
  `deg P ≤ a`, `deg Q ≤ b` and the coefficients of `P` in degree `a` and of `Q` in degree `b`
  units modulo `I n`.

## Main results

* `Stacks.Drinfeld.exists_mul_eq_polynomial_of_hasRationalApprox`: if `⋂ I n = 0`, then
  `B f = A` for polynomials `A`, `B ≠ 0` with `deg A ≤ a`, `deg B ≤ b`.
* `Stacks.Drinfeld.natDegree_add_eq_of_hasRationalApprox`: for every `B ≠ 0` with `B f = A`,
  `deg A + b = deg B + a`.
* `Stacks.Drinfeld.sub_eq_of_hasRationalApprox`: two families of approximations of `f` have the
  same `a - b`.
* `Stacks.Drinfeld.sub_eq_of_hasRationalApprox_map`: the same for `f` and its image under a
  ring automorphism of `R`.
* `Stacks.Drinfeld.hasRationalApprox_of_quotient`: the approximations may be given by polynomials
  over the quotient rings `R ⧸ I n`.
-/

@[expose] public noncomputable section

open Polynomial PowerSeries

namespace Stacks.Drinfeld

variable {R : Type*} [CommRing R]

/-- **`f` is approximately `P / Q` with `deg P ≤ a`, `deg Q ≤ b`, modulo every `I n`.** For every
`n` there are polynomials `P`, `Q` over `R` with `deg P ≤ a`, `deg Q ≤ b`, whose coefficients in
degrees `a` and `b` are units modulo `I n`, such that every coefficient of `Q f - P` lies in
`I n`. -/
def HasRationalApprox (f : R⟦X⟧) (I : ℕ → Ideal R) (a b : ℕ) : Prop :=
  ∀ n, ∃ P Q : R[X], P.natDegree ≤ a ∧ Q.natDegree ≤ b ∧
    IsUnit (Ideal.Quotient.mk (I n) (P.coeff a)) ∧ IsUnit (Ideal.Quotient.mk (I n) (Q.coeff b)) ∧
      ∀ i, PowerSeries.coeff i ((Q : R⟦X⟧) * f - (P : R⟦X⟧)) ∈ I n

/-- A unit modulo `I` can be cancelled from a product lying in `I`. -/
theorem mem_of_mul_mem_of_isUnit {I : Ideal R} {c u : R} (hu : IsUnit (Ideal.Quotient.mk I u))
    (h : c * u ∈ I) : c ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem] at h ⊢
  rw [map_mul] at h
  exact hu.mul_left_eq_zero.1 h

/-- `x` is a unit modulo `I` exactly when `x y - 1 ∈ I` for some `y`. -/
theorem isUnit_quotientMk_iff {I : Ideal R} {x : R} :
    IsUnit (Ideal.Quotient.mk I x) ↔ ∃ y, x * y - 1 ∈ I := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_right_inv
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective v
    refine ⟨y, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hv, map_one, sub_self]
  · rintro ⟨y, hy⟩
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I y) ?_
    rwa [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]

/-- If every coefficient of `h` lies in `I`, so does every coefficient of `g h`. -/
theorem coeff_mul_mem_of_forall_coeff_mem {I : Ideal R} (g h : R⟦X⟧)
    (hh : ∀ i, PowerSeries.coeff i h ∈ I) (i : ℕ) : PowerSeries.coeff i (g * h) ∈ I := by
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ => I.mul_mem_left _ (hh _)

/-- An element which, for every `n`, becomes zero in `I n` after multiplication by a unit modulo
`I n`, is zero when `⋂ I n = 0`. -/
theorem eq_zero_of_forall_mul_mem {I : ℕ → Ideal R} (hI : ⨅ n, I n = ⊥) {c : R}
    (hc : ∀ n, ∃ u, IsUnit (Ideal.Quotient.mk (I n) u) ∧ c * u ∈ I n) : c = 0 := by
  have : c ∈ ⨅ n, I n := Ideal.mem_iInf.2 fun n => by
    obtain ⟨u, hu, h⟩ := hc n
    exact mem_of_mul_mem_of_isUnit hu h
  rwa [hI, Ideal.mem_bot] at this

/-- **The degree of `f` is `a - b`.** If `f` is approximately `P / Q` with `deg P ≤ a`,
`deg Q ≤ b` modulo every `I n` and `⋂ I n = 0`, then for every expression `B f = A` with
`B ≠ 0`, `deg A + b = deg B + a`. The coefficient of `A Q - B P = B (Q f - P)` in degree
`max (deg A + b) (deg B + a)` is the product of a leading coefficient and a unit modulo `I n`,
and it lies in every `I n`. -/
theorem natDegree_add_eq_of_hasRationalApprox [IsDomain R] {f : R⟦X⟧} {I : ℕ → Ideal R}
    {a b : ℕ} (hI : ⨅ n, I n = ⊥) (hf : HasRationalApprox f I a b) {A B : R[X]} (hB : B ≠ 0)
    (hAB : (B : R⟦X⟧) * f = A) : A.natDegree + b = B.natDegree + a := by
  have key : ∀ n, ∃ P Q : R[X], P.natDegree ≤ a ∧ Q.natDegree ≤ b ∧
      IsUnit (Ideal.Quotient.mk (I n) (P.coeff a)) ∧
        IsUnit (Ideal.Quotient.mk (I n) (Q.coeff b)) ∧ ∀ i, (A * Q - B * P).coeff i ∈ I n := by
    intro n
    obtain ⟨P, Q, hP, hQ, hPu, hQu, hc⟩ := hf n
    refine ⟨P, Q, hP, hQ, hPu, hQu, fun i => ?_⟩
    have h : ((A * Q - B * P : R[X]) : R⟦X⟧) = (B : R⟦X⟧) * ((Q : R⟦X⟧) * f - P) := by
      rw [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_mul, ← hAB]
      ring
    rw [← Polynomial.coeff_coe, h]
    exact coeff_mul_mem_of_forall_coeff_mem _ _ hc i
  have hA : ¬ (A = 0 ∨ A.natDegree + b < B.natDegree + a) := by
    intro h
    apply hB
    apply leadingCoeff_eq_zero.1
    refine eq_zero_of_forall_mul_mem hI fun n => ?_
    obtain ⟨P, Q, hP, hQ, hPu, -, hc⟩ := key n
    refine ⟨P.coeff a, hPu, ?_⟩
    have h1 : (A * Q).coeff (B.natDegree + a) = 0 := by
      rcases h with rfl | h
      · simp
      · exact coeff_eq_zero_of_natDegree_lt
          ((natDegree_mul_le.trans (Nat.add_le_add_left hQ _)).trans_lt h)
    have h2 : (B * P).coeff (B.natDegree + a) = B.leadingCoeff * P.coeff a :=
      coeff_mul_add_eq_of_natDegree_le le_rfl hP
    have := hc (B.natDegree + a)
    rwa [coeff_sub, h1, h2, zero_sub, neg_mem_iff] at this
  obtain ⟨hA, hle⟩ := not_or.1 hA
  refine le_antisymm ?_ (not_lt.1 hle)
  by_contra! hlt
  apply hA
  apply leadingCoeff_eq_zero.1
  refine eq_zero_of_forall_mul_mem hI fun n => ?_
  obtain ⟨P, Q, hP, hQ, -, hQu, hc⟩ := key n
  refine ⟨Q.coeff b, hQu, ?_⟩
  have h1 : (B * P).coeff (A.natDegree + b) = 0 :=
    coeff_eq_zero_of_natDegree_lt
      ((natDegree_mul_le.trans (Nat.add_le_add_left hP _)).trans_lt hlt)
  have h2 : (A * Q).coeff (A.natDegree + b) = A.leadingCoeff * Q.coeff b :=
    coeff_mul_add_eq_of_natDegree_le le_rfl hQ
  have := hc (A.natDegree + b)
  rwa [coeff_sub, h1, h2, sub_zero] at this

section Truncation

variable {K : Type*} [Field K]

/-- The coefficients of `p f` in degrees `a + 1, …, a + N`, as a linear map on the polynomials
`p` of degree `≤ b`. -/
def tailCoeffs (fK : K⟦X⟧) (a b N : ℕ) : degreeLT K (b + 1) →ₗ[K] (Fin N → K) :=
  LinearMap.pi fun t : Fin N => (PowerSeries.coeff (a + 1 + t)) ∘ₗ (LinearMap.mulRight K fK) ∘ₗ
    (coeToPowerSeries.algHom K).toLinearMap ∘ₗ (degreeLT K (b + 1)).subtype

/-- The `t`-th entry of `tailCoeffs fK a b N p` is the coefficient of `p fK` in degree
`a + 1 + t`. -/
theorem tailCoeffs_apply (fK : K⟦X⟧) (a b N : ℕ) (p : degreeLT K (b + 1)) (t : Fin N) :
    tailCoeffs fK a b N p t = PowerSeries.coeff (a + 1 + t) (((p : K[X]) : K⟦X⟧) * fK) := by
  simp [tailCoeffs]

/-- The polynomials of degree `< b` form a finite-dimensional vector space. -/
instance (b : ℕ) : FiniteDimensional K (degreeLT K b) :=
  LinearEquiv.finiteDimensional (degreeLTEquiv K b).symm

/-- The kernels of the maps `tailCoeffs fK a b N` shrink as `N` grows. -/
theorem ker_tailCoeffs_antitone (fK : K⟦X⟧) (a b : ℕ) {N N' : ℕ} (h : N ≤ N') :
    LinearMap.ker (tailCoeffs fK a b N') ≤ LinearMap.ker (tailCoeffs fK a b N) := by
  intro p hp
  rw [LinearMap.mem_ker] at hp ⊢
  funext t
  simpa [tailCoeffs_apply] using congrFun hp (Fin.castLE h t)

/-- If no `tailCoeffs fK a b N` is injective, then some nonzero `p` of degree `≤ b` makes every
coefficient of `p fK` above degree `a` vanish. -/
theorem exists_polynomial_coeff_mul_eq_zero (fK : K⟦X⟧) (a b : ℕ)
    (hker : ∀ N, LinearMap.ker (tailCoeffs fK a b N) ≠ ⊥) :
    ∃ p : K[X], p ≠ 0 ∧ p.natDegree ≤ b ∧
      ∀ i, a < i → PowerSeries.coeff i ((p : K⟦X⟧) * fK) = 0 := by
  classical
  have hex : ∃ m, ∃ N, Module.finrank K (LinearMap.ker (tailCoeffs fK a b N)) = m :=
    ⟨_, 0, rfl⟩
  obtain ⟨N₀, hN₀⟩ := Nat.find_spec hex
  have hle : ∀ N, LinearMap.ker (tailCoeffs fK a b N₀) ≤ LinearMap.ker (tailCoeffs fK a b N) := by
    intro N
    have h : LinearMap.ker (tailCoeffs fK a b (max N N₀)) =
        LinearMap.ker (tailCoeffs fK a b N₀) :=
      Submodule.eq_of_le_of_finrank_le (ker_tailCoeffs_antitone fK a b (le_max_right _ _))
        (hN₀ ▸ Nat.find_min' hex ⟨_, rfl⟩)
    rw [← h]
    exact ker_tailCoeffs_antitone fK a b (le_max_left _ _)
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hker N₀)
  have hp0' : (p : K[X]) ≠ 0 := fun h => hp0 (Subtype.ext h)
  refine ⟨p, hp0', ?_, fun i hi => ?_⟩
  · have := p.2
    rw [mem_degreeLT] at this
    have h := (natDegree_lt_iff_degree_lt hp0').2 this
    omega
  · have := congrFun (LinearMap.mem_ker.1 (hle (i - a) hp)) ⟨i - a - 1, by omega⟩
    rwa [tailCoeffs_apply, show a + 1 + (i - a - 1) = i by omega] at this

end Truncation

/-- If `f` is approximately `P / Q` with `deg P ≤ a`, `deg Q ≤ b` modulo every `I n` and
`⋂ I n = 0`, then no `tailCoeffs (f ⊗ K) a b N` over the fraction field `K` is injective. -/
theorem ker_tailCoeffs_ne_bot_of_hasRationalApprox [IsDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] {f : R⟦X⟧} {I : ℕ → Ideal R} {a b : ℕ}
    (hI : ⨅ n, I n = ⊥) (hf : HasRationalApprox f I a b) (N : ℕ) :
    LinearMap.ker (tailCoeffs (PowerSeries.map (algebraMap R K) f) a b N) ≠ ⊥ := by
  classical
  set fK := PowerSeries.map (algebraMap R K) f
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  intro hN
  obtain ⟨L, hL⟩ := (tailCoeffs fK a b N).exists_leftInverse_of_injective hN
  let ℓ : (Fin N → K) →ₗ[K] K := (lcoeff K b) ∘ₗ (degreeLT K (b + 1)).subtype ∘ₗ L
  let e : Fin N → (Fin N → K) := fun t j => if t = j then 1 else 0
  obtain ⟨⟨d, hd⟩, hdint⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors R) (Finset.univ.image fun t => ℓ (e t))
  have hz : ∀ t, ∃ z : R, algebraMap R K z = d • ℓ (e t) := fun t =>
    hdint _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))
  choose z hz using hz
  have hdmem : ∀ n, d ∈ I n := by
    intro n
    obtain ⟨P, Q, hP, hQ, -, hQu, hc⟩ := hf n
    have hQK : Q.map (algebraMap R K) ∈ degreeLT K (b + 1) := by
      rw [mem_degreeLT]
      refine degree_le_natDegree.trans_lt ?_
      rw [natDegree_map_eq_of_injective hinj]
      exact_mod_cast Nat.lt_succ_of_le hQ
    let q : degreeLT K (b + 1) := ⟨_, hQK⟩
    have h1 : ℓ (tailCoeffs fK a b N q) = algebraMap R K (Q.coeff b) := by
      have : L (tailCoeffs fK a b N q) = q := by
        rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
      simp only [ℓ, LinearMap.comp_apply, this]
      simp [q]
    have hcoeff : ∀ t : Fin N, PowerSeries.coeff (a + 1 + t) ((Q : R⟦X⟧) * f) ∈ I n := by
      intro t
      have h := hc (a + 1 + t)
      rwa [LinearMap.map_sub, Polynomial.coeff_coe,
        coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < a + 1 + t), sub_zero] at h
    have h2 : ∀ t, tailCoeffs fK a b N q t =
        algebraMap R K (PowerSeries.coeff (a + 1 + t) ((Q : R⟦X⟧) * f)) := by
      intro t
      have hm : PowerSeries.map (algebraMap R K) ((Q : R⟦X⟧) * f) =
          ((Q.map (algebraMap R K) : K[X]) : K⟦X⟧) * fK := by
        rw [map_mul, Polynomial.polynomial_map_coe]
      rw [tailCoeffs_apply, ← PowerSeries.coeff_map, hm]
    have hsum : d * Q.coeff b =
        ∑ t : Fin N, PowerSeries.coeff (a + 1 + (t : ℕ)) ((Q : R⟦X⟧) * f) * z t := by
      apply hinj
      rw [map_mul, ← h1, LinearMap.pi_apply_eq_sum_univ, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_mul, hz, h2, smul_eq_mul, Algebra.smul_def]
      ring
    refine mem_of_mul_mem_of_isUnit hQu ?_
    rw [hsum]
    exact sum_mem fun t _ => (I n).mul_mem_right _ (hcoeff t)
  exact nonZeroDivisors.ne_zero hd (by simpa [hI] using Ideal.mem_iInf.2 hdmem)

/-- **`f` is rational.** If `f` is approximately `P / Q` with `deg P ≤ a`, `deg Q ≤ b` modulo
every `I n` and `⋂ I n = 0`, then `B f = A` for polynomials `A`, `B ≠ 0` over `R` with
`deg A ≤ a`, `deg B ≤ b`. Over the fraction field, the polynomials `Q` of degree `≤ b` such that
`Q f` has no coefficient in degrees `a + 1, …, a + N` form a nonzero subspace for every `N`: were
it zero, a left inverse of the truncated coefficient map, with its denominators cleared by
`d ≠ 0`, would put `d` in every `I n`. These subspaces decrease, so they stabilise and meet in a
nonzero `Q`, whose denominators are then cleared. -/
theorem exists_mul_eq_polynomial_of_hasRationalApprox [IsDomain R] {f : R⟦X⟧} {I : ℕ → Ideal R}
    {a b : ℕ} (hI : ⨅ n, I n = ⊥) (hf : HasRationalApprox f I a b) :
    ∃ A B : R[X], B ≠ 0 ∧ B.natDegree ≤ b ∧ A.natDegree ≤ a ∧ (B : R⟦X⟧) * f = A := by
  classical
  have hinj := IsFractionRing.injective R (FractionRing R)
  obtain ⟨p, hp0, hpdeg, hpcoeff⟩ := exists_polynomial_coeff_mul_eq_zero _ a b
    (ker_tailCoeffs_ne_bot_of_hasRationalApprox (K := FractionRing R) hI hf)
  -- clear denominators
  obtain ⟨d, hd, hB⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  set B := IsLocalization.integerNormalization (nonZeroDivisors R) p
  have hdK : algebraMap R (FractionRing R) d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hB' : B.map (algebraMap R (FractionRing R)) =
      Polynomial.C (algebraMap R (FractionRing R) d) * p := by
    rw [hB, ← algebraMap_smul (FractionRing R) d p, Polynomial.smul_eq_C_mul]
  have hBne : B ≠ 0 := by
    intro h
    rw [h, Polynomial.map_zero] at hB'
    exact (mul_ne_zero (C_ne_zero.2 hdK) hp0) hB'.symm
  have hBdeg : B.natDegree ≤ b := by
    rwa [← natDegree_map_eq_of_injective hinj, hB', natDegree_C_mul hdK]
  have hBf : ∀ i, a < i → PowerSeries.coeff i ((B : R⟦X⟧) * f) = 0 := by
    intro i hi
    apply hinj
    rw [map_zero, ← PowerSeries.coeff_map, map_mul, ← Polynomial.polynomial_map_coe, hB',
      Polynomial.coe_mul, Polynomial.coe_C, mul_assoc, PowerSeries.coeff_C_mul, hpcoeff i hi,
      mul_zero]
  refine ⟨trunc (a + 1) ((B : R⟦X⟧) * f), B, hBne, hBdeg,
    Nat.lt_succ_iff.1 (natDegree_trunc_lt _ a), ?_⟩
  ext i
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs with h
  · rfl
  · exact hBf i (by omega)

/-- **Two families of approximations of `f` have the same `a - b`.** -/
theorem sub_eq_of_hasRationalApprox [IsDomain R] {f : R⟦X⟧} {I I' : ℕ → Ideal R}
    {a b a' b' : ℕ} (hI : ⨅ n, I n = ⊥) (hI' : ⨅ n, I' n = ⊥) (hf : HasRationalApprox f I a b)
    (hf' : HasRationalApprox f I' a' b') : (a : ℤ) - b = a' - b' := by
  obtain ⟨A, B, hB, -, -, hAB⟩ := exists_mul_eq_polynomial_of_hasRationalApprox hI hf
  have h1 := natDegree_add_eq_of_hasRationalApprox hI hf hB hAB
  have h2 := natDegree_add_eq_of_hasRationalApprox hI' hf' hB hAB
  omega

/-- **Transport along a ring automorphism.** If `σ f` is approximately `P / Q` modulo every `I n`,
then `f` is approximately `σ⁻¹ P / σ⁻¹ Q` modulo every `σ⁻¹ (I n)`, with the same degrees. -/
theorem HasRationalApprox.of_map (σ : R ≃+* R) {f : R⟦X⟧} {I : ℕ → Ideal R} {a b : ℕ}
    (h : HasRationalApprox (PowerSeries.map (σ : R →+* R) f) I a b) :
    HasRationalApprox f (fun n => (I n).comap (σ : R →+* R)) a b := by
  intro n
  obtain ⟨P, Q, hP, hQ, hPu, hQu, hc⟩ := h n
  have hunit : ∀ x : R, IsUnit (Ideal.Quotient.mk (I n) x) →
      IsUnit (Ideal.Quotient.mk ((I n).comap (σ : R →+* R)) (σ.symm x)) := by
    intro x hx
    obtain ⟨y, hy⟩ := isUnit_quotientMk_iff.1 hx
    refine isUnit_quotientMk_iff.2 ⟨σ.symm y, ?_⟩
    rw [Ideal.mem_comap]
    simpa using hy
  have hmap : ∀ p : R[X], (p.map (σ.symm : R →+* R)).map (σ : R →+* R) = p := fun p => by
    simp [Polynomial.map_map]
  refine ⟨P.map (σ.symm : R →+* R), Q.map (σ.symm : R →+* R),
    (natDegree_map_le).trans hP, (natDegree_map_le).trans hQ, ?_, ?_, fun i => ?_⟩
  · rw [Polynomial.coeff_map]
    exact hunit _ hPu
  · rw [Polynomial.coeff_map]
    exact hunit _ hQu
  · rw [Ideal.mem_comap, ← PowerSeries.coeff_map (σ : R →+* R) i, map_sub, map_mul,
      ← Polynomial.polynomial_map_coe, ← Polynomial.polynomial_map_coe, hmap, hmap]
    exact hc i

/-- `⋂ σ⁻¹(I n) = 0` when `⋂ I n = 0`. -/
theorem iInf_comap_eq_bot (σ : R ≃+* R) {I : ℕ → Ideal R} (hI : ⨅ n, I n = ⊥) :
    ⨅ n, (I n).comap (σ : R →+* R) = ⊥ := by
  rw [← Ideal.comap_iInf, hI]
  exact Ideal.comap_bot_of_injective _ σ.injective

/-- **Galois symmetry of the degree.** If `f` is approximately `P / Q` with degrees `a`, `b`
modulo every `I n`, and its image under a ring automorphism `σ` of `R` is approximately `P' / Q'`
with degrees `a'`, `b'` modulo every `I' n`, then `a - b = a' - b'`. -/
theorem sub_eq_of_hasRationalApprox_map [IsDomain R] (σ : R ≃+* R) {f : R⟦X⟧}
    {I I' : ℕ → Ideal R} {a b a' b' : ℕ} (hI : ⨅ n, I n = ⊥) (hI' : ⨅ n, I' n = ⊥)
    (hf : HasRationalApprox f I a b)
    (hf' : HasRationalApprox (PowerSeries.map (σ : R →+* R) f) I' a' b') :
    (a : ℤ) - b = a' - b' :=
  sub_eq_of_hasRationalApprox hI (iInf_comap_eq_bot σ hI') hf hf'.of_map

/-- **Approximations over the quotient rings.** It suffices to give, for every `n`, polynomials
`P`, `Q` over `R ⧸ I n` with `deg P ≤ a`, `deg Q ≤ b`, unit coefficients in degrees `a` and `b`,
and `Q · (f mod I n) = P`: lifts of the same degrees approximate `f`. -/
theorem hasRationalApprox_of_quotient {f : R⟦X⟧} {I : ℕ → Ideal R} {a b : ℕ}
    (h : ∀ n, ∃ P Q : (R ⧸ I n)[X], P.natDegree ≤ a ∧ Q.natDegree ≤ b ∧ IsUnit (P.coeff a) ∧
      IsUnit (Q.coeff b) ∧
        (Q : (R ⧸ I n)⟦X⟧) * PowerSeries.map (Ideal.Quotient.mk (I n)) f = P) :
    HasRationalApprox f I a b := by
  intro n
  obtain ⟨P, Q, hP, hQ, hPu, hQu, hc⟩ := h n
  obtain ⟨P', hP'map, hP'deg⟩ := exists_natDegree_eq_of_mem_lifts
    (mem_lifts_of_surjective Ideal.Quotient.mk_surjective P)
  obtain ⟨Q', hQ'map, hQ'deg⟩ := exists_natDegree_eq_of_mem_lifts
    (mem_lifts_of_surjective Ideal.Quotient.mk_surjective Q)
  refine ⟨P', Q', hP'deg ▸ hP, hQ'deg ▸ hQ, ?_, ?_, fun i => ?_⟩
  · rwa [← Polynomial.coeff_map, hP'map]
  · rwa [← Polynomial.coeff_map, hQ'map]
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← PowerSeries.coeff_map (Ideal.Quotient.mk (I n)) i,
      map_sub, map_mul, ← Polynomial.polynomial_map_coe, ← Polynomial.polynomial_map_coe,
      hP'map, hQ'map, hc, sub_self, map_zero]

end Stacks.Drinfeld

end
