module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.TotallySplit

/-!
# The cotangent space of a finite-type algebra at a maximal ideal

Let $k$ be an algebraically closed field, let $S$ be a $k$-algebra of finite type, and let
$\mathfrak{m} \subset S$ be a maximal ideal, with residue field
$\kappa(\mathfrak{m}) = S/\mathfrak{m}$. Then
$$
\dim_{\kappa(\mathfrak{m})}\bigl(\Omega_{S/k} \otimes_S \kappa(\mathfrak{m})\bigr)
=
\dim_{\kappa(\mathfrak{m})}\bigl(\mathfrak{m}/\mathfrak{m}^2\bigr).
$$

This file also proves that if `R → S` is a map of `ℚ`-algebras and `f ∈ S` is such that
`Ω[S⁄R] = S df ⊕ C` with `S df` free on `df`, then `f` is not nilpotent, and `f` is a
nonzerodivisor when `S` is moreover a Noetherian local ring.

## Main definitions

* `cotangentDerivationOfSection`: for a `k`-algebra section `σ` of `S → S ⧸ I`, the
  `k`-derivation `s ↦ (s - σ (s mod I)) mod I²` into `I/I²`.
* `HasFreeSummandDifferential`: there is an `S`-linear map `π : Ω[S⁄R] → S` with `π (d f) = 1`.
* `HasDerivationOne`: there is an `R`-derivation `θ : S → S` with `θ f = 1`.

## Main results

* `finrank_kaehler_baseChange_eq_finrank_cotangent`: the dimension of the cotangent space
  $\Omega_{S/k} \otimes_S \kappa(\mathfrak{m})$ over $\kappa(\mathfrak{m})$ is that of
  $\mathfrak{m}/\mathfrak{m}^2$.
* `not_isNilpotent_of_hasFreeSummandDifferential`: an `f` whose differential generates a free
  summand is not nilpotent.
* `nonzerodivisor_of_hasFreeSummandDifferential`: over a Noetherian local ring, such an `f` is a
  nonzerodivisor.

## Implementation notes

The residue field $\kappa(\mathfrak{m})$ is `S ⧸ 𝔪`, the module of Kähler differentials
$\Omega_{S/k}$ is `KaehlerDifferential k S`, written `Ω[S⁄k]`, and the cotangent space
$\Omega_{S/k} \otimes_S \kappa(\mathfrak{m})$ is realized as the base change
`(S ⧸ 𝔪) ⊗[S] Ω[S⁄k]`, a `(S ⧸ 𝔪)`-module. The Zariski cotangent space
$\mathfrak{m}/\mathfrak{m}^2$ is `𝔪.Cotangent`, definitionally `↥𝔪 ⧸ 𝔪 • ⊤` and again a
`(S ⧸ 𝔪)`-module, and dimensions over the residue field are `Module.finrank (S ⧸ 𝔪) (-)`.

The direct-sum hypothesis `Ω[S⁄R] = S df ⊕ C` is phrased as the existence of an `S`-linear
retraction `π : Ω[S⁄R] → S` with `π (d f) = 1`, equivalently of an `R`-derivation `θ : S → S`
with `θ f = 1`. The `ℚ`-algebra map is encoded by `[Algebra ℚ R] [Algebra ℚ S] [Algebra R S]`
together with `[IsScalarTower ℚ R S]`.

## References

* [Stacks 00TR](https://stacks.math.columbia.edu/tag/00TR), Lemma 10.140.1
* [Stacks 00TW](https://stacks.math.columbia.edu/tag/00TW)
-/

@[expose] public section

open scoped TensorProduct

/-- For `k` algebraically closed and `S` a finite-type `k`-algebra with maximal ideal `𝔪`, the
structure map `k → S/𝔪` to the residue field is surjective. -/
theorem residue_algebraMap_surjective
    (k S : Type*) [Field k] [IsAlgClosed k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (𝔪 : Ideal S) [𝔪.IsMaximal] :
    Function.Surjective (algebraMap k (S ⧸ 𝔪)) := by
  let := Ideal.Quotient.field 𝔪
  have : Algebra.FiniteType k (S ⧸ 𝔪) :=
    Algebra.FiniteType.trans (S := S) inferInstance
      (Algebra.FiniteType.of_surjective (Algebra.ofId S (S ⧸ 𝔪)) Ideal.Quotient.mk_surjective)
  have : Module.Finite k (S ⧸ 𝔪) :=
    finite_of_finite_type_of_isJacobsonRing k (S ⧸ 𝔪)
  have : Algebra.IsIntegral k (S ⧸ 𝔪) := Algebra.IsIntegral.of_finite k (S ⧸ 𝔪)
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := S ⧸ 𝔪)).surjective

/-- If `σ` is a `k`-algebra section of `S → S ⧸ I`, then `s - σ (s mod I)` lies in `I`. -/
theorem sub_quotientSection_mem {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]
    {I : Ideal S} (σ : (S ⧸ I) →ₐ[k] S) (hσ : ∀ c, Ideal.Quotient.mk I (σ c) = c) (s : S) :
    s - σ (Ideal.Quotient.mk I s) ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hσ, sub_self]

/-- The `k`-derivation `s ↦ (s - σ (s mod I)) mod I²` into `I/I²` attached to a `k`-algebra
section `σ` of `S → S ⧸ I`. -/
def cotangentDerivationOfSection {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]
    {I : Ideal S} (σ : (S ⧸ I) →ₐ[k] S) (hσ : ∀ c, Ideal.Quotient.mk I (σ c) = c) :
    Derivation k S I.Cotangent :=
  Derivation.mk' ((I.toCotangent.restrictScalars k).comp
      ((LinearMap.id - σ.toLinearMap.comp (Ideal.Quotient.mkₐ k I).toLinearMap).codRestrict
        (I.restrictScalars k) (sub_quotientSection_mem σ hσ))) fun a b => by
    change I.toCotangent _ = a • I.toCotangent _ + b • I.toCotangent _
    rw [← map_smul, ← map_smul, ← map_add, Ideal.toCotangent_eq, pow_two]
    convert neg_mem (Ideal.mul_mem_mul (sub_quotientSection_mem σ hσ a)
      (sub_quotientSection_mem σ hσ b)) using 1
    change a * b - σ (Ideal.Quotient.mk I (a * b)) -
      (a * (b - σ (Ideal.Quotient.mk I b)) + b * (a - σ (Ideal.Quotient.mk I a))) = _
    rw [map_mul, map_mul]
    ring

/-- The value of `cotangentDerivationOfSection σ hσ` at `s` is the class of `s - σ (s mod I)`. -/
theorem cotangentDerivationOfSection_apply {k S : Type*} [CommRing k] [CommRing S]
    [Algebra k S] {I : Ideal S} (σ : (S ⧸ I) →ₐ[k] S)
    (hσ : ∀ c, Ideal.Quotient.mk I (σ c) = c) (s : S) :
    cotangentDerivationOfSection σ hσ s = I.toCotangent ⟨_, sub_quotientSection_mem σ hσ s⟩ :=
  rfl

/-- For `k` algebraically closed and `S` of finite type over `k`, the residue map
`S → S ⧸ 𝔪` at a maximal ideal has a `k`-algebra section. -/
theorem exists_algHom_section_residue
    (k S : Type*) [Field k] [IsAlgClosed k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (𝔪 : Ideal S) [𝔪.IsMaximal] :
    ∃ σ : (S ⧸ 𝔪) →ₐ[k] S, ∀ c, Ideal.Quotient.mk 𝔪 (σ c) = c := by
  let e := AlgEquiv.ofBijective (Algebra.ofId k (S ⧸ 𝔪))
    ⟨(algebraMap k (S ⧸ 𝔪)).injective, residue_algebraMap_surjective k S 𝔪⟩
  exact ⟨(Algebra.ofId k S).comp e.symm.toAlgHom, e.apply_symm_apply⟩

/-- For `k` algebraically closed, `S` a finite-type `k`-algebra and `𝔪` a maximal ideal of `S`,
the map `KaehlerDifferential.kerCotangentToTensor k S (S ⧸ 𝔪)` from the conormal module of
`S → S ⧸ 𝔪` to `(S ⧸ 𝔪) ⊗_S Ω[S⁄k]` is injective. -/
@[sga "1 II 4.10" "(i)⇒(iv), (iv)", sga "1 II 5.9" "(ii)", sga "3 III 4.25" "(ii), special case"]
theorem kerCotangentToTensor_injective
    (k S : Type*) [Field k] [IsAlgClosed k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (𝔪 : Ideal S) [𝔪.IsMaximal] :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k S (S ⧸ 𝔪)) := by
  obtain ⟨σ, hσ⟩ := exists_algHom_section_residue k S 𝔪
  let D := cotangentDerivationOfSection σ hσ
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ x
  have := congr(D.liftKaehlerDifferential.liftBaseChange (S ⧸ 𝔪) $hx)
  rw [map_zero, KaehlerDifferential.kerCotangentToTensor_toCotangent,
    LinearMap.liftBaseChange_tmul, one_smul, D.liftKaehlerDifferential_comp_D,
    cotangentDerivationOfSection_apply, Ideal.toCotangent_eq_zero] at this
  have hy : Ideal.Quotient.mk 𝔪 (y : S) = 0 := RingHom.mem_ker.mp y.2
  rw [Ideal.toCotangent_eq_zero, show RingHom.ker (algebraMap S (S ⧸ 𝔪)) ^ 2 = 𝔪 ^ 2 by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]]
  simpa [hy] using this

/-- For `k` algebraically closed, `S` a finite-type `k`-algebra and `𝔪` a maximal ideal of `S`,
the map `KaehlerDifferential.kerCotangentToTensor k S (S ⧸ 𝔪)` from the conormal module of
`S → S ⧸ 𝔪` to `(S ⧸ 𝔪) ⊗_S Ω[S⁄k]` is surjective. -/
@[ega "0 20.6.22" "partial"]
theorem kerCotangentToTensor_surjective
    (k S : Type*) [Field k] [IsAlgClosed k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (𝔪 : Ideal S) [𝔪.IsMaximal] :
    Function.Surjective (KaehlerDifferential.kerCotangentToTensor k S (S ⧸ 𝔪)) := by
  have : Subsingleton (Ω[(S ⧸ 𝔪)⁄k]) :=
    KaehlerDifferential.subsingleton_of_surjective k _ (residue_algebraMap_surjective k S 𝔪)
  rw [← LinearMap.range_eq_top, KaehlerDifferential.range_kerCotangentToTensor (R := k) (A := S)
    (B := S ⧸ 𝔪) Ideal.Quotient.mk_surjective, (LinearMap.ker _).eq_top_iff'.mpr fun _ =>
    Subsingleton.elim _ _, Submodule.restrictScalars_top]

/-- For an algebraically closed field $k$, a finite type $k$-algebra $S$, and a maximal ideal
$\mathfrak{m} \subset S$, the dimension over the residue field
$\kappa(\mathfrak{m}) = S/\mathfrak{m}$ of the cotangent space
$\Omega_{S/k} \otimes_S \kappa(\mathfrak{m})$ equals the dimension of
$\mathfrak{m}/\mathfrak{m}^2$. -/
@[stacks 00TR]
theorem finrank_kaehler_baseChange_eq_finrank_cotangent
    (k S : Type*) [Field k] [IsAlgClosed k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (𝔪 : Ideal S) [𝔪.IsMaximal] :
    Module.finrank (S ⧸ 𝔪) ((S ⧸ 𝔪) ⊗[S] KaehlerDifferential k S) =
      Module.finrank (S ⧸ 𝔪) 𝔪.Cotangent := by
  have hker : RingHom.ker (algebraMap S (S ⧸ 𝔪)) = 𝔪 := by
    simp [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  obtain e₀ := LinearEquiv.ofBijective _
    ⟨kerCotangentToTensor_injective k S 𝔪, kerCotangentToTensor_surjective k S 𝔪⟩
  rw [hker] at e₀
  exact (LinearEquiv.extendScalarsOfSurjective (R := S) (S := S ⧸ 𝔪)
    Ideal.Quotient.mk_surjective e₀).symm.finrank_eq

/-! ### An element whose differential generates a free summand -/

@[expose] public section

open KaehlerDifferential

/-- There is an `S`-linear map `π : Ω[S⁄R] → S` with `π (d f) = 1`; equivalently,
`Ω[S⁄R] = S·df ⊕ C` for some `S`-submodule `C`, with `df` a free generator of `S·df`. -/
def HasFreeSummandDifferential
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (f : S) : Prop :=
  ∃ π : Ω[S⁄R] →ₗ[S] S, π (D R S f) = 1

/-- There is an `R`-derivation `θ : S → S` with `θ f = 1`. -/
def HasDerivationOne
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (f : S) : Prop :=
  ∃ θ : Derivation R S S, θ f = 1

/-- There is an `S`-linear map `π : Ω[S⁄R] → S` with `π (d f) = 1` if and only if there is an
`R`-derivation `θ : S → S` with `θ f = 1`. -/
theorem hasFreeSummandDifferential_iff_hasDerivationOne
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (f : S) :
    HasFreeSummandDifferential R S f ↔ HasDerivationOne R S f :=
  ⟨fun ⟨π, hπ⟩ => ⟨π.compDer (D R S), by simpa using hπ⟩,
    fun ⟨θ, hθ⟩ =>
      ⟨θ.liftKaehlerDifferential, by rwa [Derivation.liftKaehlerDifferential_comp_D]⟩⟩

/-- In a `ℚ`-algebra, the image of every positive natural number is a unit. -/
theorem isUnit_natCast_succ_of_algebra_rat (S : Type*) [CommRing S] [Algebra ℚ S] (k : ℕ) :
    IsUnit ((k + 1 : ℕ) : S) := by
  simpa using (isUnit_iff_ne_zero.mpr (Nat.cast_add_one_ne_zero k : (k : ℚ) + 1 ≠ 0)).map
    (algebraMap ℚ S)

/-- If `θ f = 1` in a `ℚ`-algebra and `f ^ (k + 1) * b = 0`, then `f ^ k * b ∈ (f ^ (k + 1))`. -/
private theorem pow_mul_mem_span_pow_succ {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ S] [Algebra R S] {θ : Derivation R S S} {f : S} (hθ : θ f = 1) (b : S) (k : ℕ)
    (hb : f ^ (k + 1) * b = 0) : f ^ k * b ∈ Ideal.span {f ^ (k + 1)} := by
  have hd := congrArg θ hb
  rw [Derivation.leibniz, θ.leibniz_pow, hθ, map_zero, Nat.add_sub_cancel] at hd
  simp only [smul_eq_mul, mul_one, nsmul_eq_mul] at hd
  obtain ⟨v, hv⟩ := (isUnit_natCast_succ_of_algebra_rat S k).exists_left_inv
  exact Ideal.mem_span_singleton.mpr ⟨v * -θ b, by linear_combination v * hd - f ^ k * b * hv⟩

/-- Let `R → S` be a map of `ℚ`-algebras with `S` nonzero, and let `f ∈ S` be such that
`Ω[S⁄R] = S·df ⊕ C` with `df` a free generator of `S·df`. Then `f` is not nilpotent. -/
@[stacks 00TW "(1)"]
theorem not_isNilpotent_of_hasFreeSummandDifferential
    (R S : Type*) [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] [Algebra R S] [IsScalarTower ℚ R S] [Nontrivial S]
    (f : S) (hf : HasFreeSummandDifferential R S f) :
    ¬ IsNilpotent f := by
  obtain ⟨θ, hθ⟩ := (hasFreeSummandDifferential_iff_hasDerivationOne R S f).mp hf
  rintro ⟨n, hn⟩
  induction n with
  | zero => simp at hn
  | succ k ih =>
    have := pow_mul_mem_span_pow_succ hθ 1 k (by rw [mul_one, hn])
    rw [hn, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot, mul_one] at this
    exact ih this

/-- In a `ℚ`-algebra, if an `R`-derivation `θ` satisfies `θ f = 1` and `f * a = 0`, then
`a` lies in every power of the ideal `(f)`. -/
theorem mem_span_pow_of_derivation_eq_one {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ S] [Algebra R S] {θ : Derivation R S S} {f a : S} (hθ : θ f = 1)
    (ha : f * a = 0) (n : ℕ) : a ∈ Ideal.span {f ^ n} := by
  induction n with
  | zero => simp
  | succ k ih =>
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ih
    exact pow_mul_mem_span_pow_succ hθ b k (by rw [pow_succ', mul_assoc, ha])

/-- Let `R → S` be a map of `ℚ`-algebras with `S` a Noetherian local ring, and let `f ∈ S` be such
that `Ω[S⁄R] = S·df ⊕ C` with `df` a free generator of `S·df`. Then `f` is a nonzerodivisor:
`f * a = 0 → a = 0`. -/
@[stacks 00TW "(2)"]
theorem nonzerodivisor_of_hasFreeSummandDifferential
    (R S : Type*) [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] [Algebra R S] [IsScalarTower ℚ R S]
    [IsNoetherianRing S] [IsLocalRing S]
    (f : S) (hf : HasFreeSummandDifferential R S f) :
    ∀ a : S, f * a = 0 → a = 0 := by
  obtain ⟨θ, hθ⟩ := (hasFreeSummandDifferential_iff_hasDerivationOne R S f).mp hf
  intro a ha
  by_cases hfu : IsUnit f
  · exact hfu.mul_right_eq_zero.mp ha
  have hain : a ∈ ⨅ n : ℕ, Ideal.span {f} ^ n := Ideal.mem_iInf.mpr fun n => by
    simpa only [Ideal.span_singleton_pow] using mem_span_pow_of_derivation_eq_one hθ ha n
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ fun hc => hfu (Ideal.span_singleton_eq_top.mp hc),
    Ideal.mem_bot] at hain
