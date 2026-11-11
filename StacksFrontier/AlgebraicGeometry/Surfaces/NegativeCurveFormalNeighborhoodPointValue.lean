module

public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveFormalNeighborhoodLeadingCoeff

/-!
# Generation of the formal neighbourhood of a curve of genus one with conormal bundle `𝒪(p)`

Let `D` be an effective Cartier divisor on a scheme `X` whose subscheme `C` is integral with
`Γ(C, 𝒪_C)` a field, let `A = lim Γ(Cₙ, 𝒪)` be the ring of compatible functions on its
thickenings with filtration `Fₙ`, and assume the transition maps of the thickenings are surjective,
so that `Fₙ₊₁ / Fₙ₊₂ ≅ H⁰(C, Lⁿ⁺¹)` for the conormal sheaf `L`
(`AlgebraicGeometry.Scheme.IdealSheafData.gradedPieceEquiv`).

Fix a point `p` of `C`, given by a prime `𝔭 ⊇ D(V)` of the ring `B` of an affine chart `V` on which
`D` is cut out by a nonzerodivisor `t`. The *value at `p`* of `a ∈ Fₘ`
(`AlgebraicGeometry.Scheme.IdealSheafData.chartPointValue`) is the leading coefficient of `a` in
degree `m` reduced modulo `𝔭`; it is multiplicative, and it is the value at `p` of the section of
`Lᵐ` that `a` represents, read in the trivialisation `tᵐ`.

This file proves, by a dimension count, that the graded ring is generated in degrees `1, 2, 3` when
`dim H⁰(C, Lⁿ) = n` for `n ≥ 1`, every section of `L` vanishes at `p`, and `L²`, `L³` have sections
not vanishing at `p` — the situation of a curve of genus one with `L ≅ 𝒪_C(p)`:

* in degree `1`, `H⁰(L)` is spanned by the symbol of one element `a`;
* in degree `n ≥ 2`, the products `a · Fₙ₋₁` give an `(n - 1)`-dimensional subspace of
  `H⁰(Lⁿ)` (multiplication by `a` is injective on the graded ring, which has no zero divisors),
  on which the value at `p` vanishes, and the monomial `x^i y^j`, `2 i + 3 j = n`, has nonzero
  value at `p`; so they span the `n`-dimensional `H⁰(Lⁿ)`.

The output is the bounded-degree generation `Fₙ ⊆ (a, x, y) · F_{n-3} + Fₙ₊₁` that
`Stacks.IsCompleteFiltration.isNoetherianCompleteLocalRing_of_le_mul_sup` consumes.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.exists_le_mul_sup_three_of_chartPointValue`.
* `AlgebraicGeometry.Scheme.IdealSheafData.isNoetherianCompleteLocalRing_of_chartPointValue`.
* `AlgebraicGeometry.Scheme.IdealSheafData`
  `.ringKrullDim_formalNeighborhoodRing_eq_two_of_chartPointValue` — **`dim A = 2`**:
  `𝔪⁴ ⊆ (a, x)` bounds the height of `𝔪` by Krull's height theorem
  (`Stacks.height_maximalIdeal_le_two_of_pow_le_span_pair`), and no power of `𝔪` lies in `(a)`, so
  a minimal prime over `(a)` sits strictly between `0` and `𝔪`
  (`Stacks.two_le_height_maximalIdeal`).
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Divisors

universe u

namespace Stacks

variable {R : Type*} [CommRing R]

/-- **Closedness of ideals in a Noetherian local ring** (Krull's intersection theorem): an element
lying in `K + Iⁱ` for every `i`, for a proper ideal `I`, lies in `K`. -/
public theorem mem_of_forall_mem_sup_pow [IsNoetherianRing R] [IsLocalRing R] {K : Ideal R}
    (I : Ideal R) (hI : I ≠ ⊤) {z : R} (h : ∀ i, z ∈ K ⊔ I ^ i) : z ∈ K := by
  have hmem : (Submodule.Quotient.mk z : R ⧸ K) ∈ ⨅ i : ℕ, (I ^ i • (⊤ : Submodule R (R ⧸ K))) := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 (h i)
    rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hu, zero_add,
      show (Submodule.Quotient.mk w : R ⧸ K) = w • Submodule.Quotient.mk 1 by
        rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]]
    exact Submodule.smul_mem_smul hw Submodule.mem_top
  rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ hI, Submodule.mem_bot,
    Submodule.Quotient.mk_eq_zero] at hmem
  exact hmem

/-- **Krull's height theorem, for an ideal of definition with two generators**: if a power of
the maximal ideal of a Noetherian local ring lies in an ideal `(a, x) ⊆ 𝔪`, the maximal ideal has
height `≤ 2`. -/
public theorem height_maximalIdeal_le_two_of_pow_le_span_pair [IsNoetherianRing R]
    [IsLocalRing R] {a x : R} (hK : Ideal.span {a, x} ≤ IsLocalRing.maximalIdeal R) {k : ℕ}
    (h : IsLocalRing.maximalIdeal R ^ k ≤ Ideal.span {a, x}) :
    (IsLocalRing.maximalIdeal R).height ≤ 2 := by
  have hrad : IsLocalRing.maximalIdeal R ≤ (Ideal.span {a, x}).radical := fun z hz =>
    ⟨k, h (Ideal.pow_mem_pow hz k)⟩
  have hKtop : Ideal.span {a, x} ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hK
  have hmin : ∀ J ∈ (Ideal.span {a, x}).minimalPrimes, J = IsLocalRing.maximalIdeal R := by
    intro J hJ
    have hJp : J.IsPrime := hJ.1.1
    exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hJp.ne_top
      (hrad.trans ((Ideal.IsPrime.radical_le_iff hJp).2 hJ.1.2))).symm
  have hKh : (Ideal.span {a, x}).height = (IsLocalRing.maximalIdeal R).height := by
    rw [Ideal.height_eq_inf_minimalPrimes]
    obtain ⟨⟨J, hJ⟩⟩ := Ideal.nonempty_minimalPrimes hKtop
    refine le_antisymm ((iInf₂_le J hJ).trans (congrArg Ideal.height (hmin J hJ)).le) ?_
    exact le_iInf₂ fun J hJ => (congrArg Ideal.height (hmin J hJ)).ge
  have hspan : (Ideal.span {a, x}).spanFinrank ≤ ({a, x} : Set R).ncard :=
    Submodule.spanFinrank_span_le_ncard_of_finite ((Set.finite_singleton x).insert a)
  have hn : ({a, x} : Set R).ncard ≤ 2 :=
    (Set.ncard_insert_le a {x}).trans (by rw [Set.ncard_singleton])
  rw [← hKh]
  exact (Ideal.height_le_spanFinrank _ hKtop).trans
    (((Nat.cast_le (α := ℕ∞)).2 (hspan.trans hn)).trans_eq Nat.cast_ofNat)

/-- **A lower bound for the height of the maximal ideal of a Noetherian local domain**: if
`0 ≠ a ∈ 𝔪` and no power of `𝔪` lies in `(a)`, the maximal ideal has height `≥ 2`. A minimal prime
`Q` over `(a)` other than `𝔪` exists, and `0 < Q < 𝔪`. -/
public theorem two_le_height_maximalIdeal [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    {a : R} (ha0 : a ≠ 0) (haM : a ∈ IsLocalRing.maximalIdeal R)
    (h : ∀ N, ¬ IsLocalRing.maximalIdeal R ^ N ≤ Ideal.span {a}) :
    2 ≤ (IsLocalRing.maximalIdeal R).height := by
  have hspan : Ideal.span {a} ≠ ⊤ := fun hs =>
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (top_le_iff.1 (hs ▸ Ideal.span_le.2 (Set.singleton_subset_iff.2 haM)))
  obtain ⟨Q, hQ, hQm⟩ : ∃ Q ∈ (Ideal.span {a}).minimalPrimes, Q ≠ IsLocalRing.maximalIdeal R := by
    by_contra hcon
    push Not at hcon
    have hrad : (Ideal.span {a}).radical = IsLocalRing.maximalIdeal R := by
      rw [← Ideal.sInf_minimalPrimes]
      obtain ⟨⟨Q₀, hQ₀⟩⟩ := Ideal.nonempty_minimalPrimes hspan
      exact le_antisymm ((sInf_le hQ₀).trans (hcon Q₀ hQ₀).le)
        (le_sInf fun Q hQ => (hcon Q hQ).ge)
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad.ge
      (IsNoetherian.noetherian _)
    exact h N hN
  have hQp : Q.IsPrime := hQ.1.1
  have haQ : a ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self a)
  have hQlt : Q < IsLocalRing.maximalIdeal R :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQp.ne_top) hQm
  have hbot : (⊥ : Ideal R) < Q :=
    bot_lt_iff_ne_bot.2 fun hb => ha0 (by rw [hb] at haQ; exact (Submodule.mem_bot _).1 haQ)
  have h1Q := Ideal.height_strict_mono_of_isPrime hbot
  have h2Q := Ideal.height_strict_mono_of_isPrime hQlt
  rw [Ideal.height_bot] at h1Q
  have h3 := Order.add_one_le_of_lt h2Q
  have h1' : (1 : ℕ∞) ≤ Q.height := Order.one_le_iff_pos.2 h1Q
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ Q.height + 1 := by gcongr
    _ ≤ _ := h3

end Stacks

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {D : X.IdealSheafData} {V : X.affineOpens} {t : Γ(X, V.1)}

/-! ### Leading coefficients: sums and degree bookkeeping -/

/-- `AlgebraicGeometry.Scheme.IdealSheafData.chartLeadingCoeff_mul` with the degree of the product
a free variable. -/
public theorem chartLeadingCoeff_mul_of_eq (ht : t ∈ nonZeroDivisors Γ(X, V.1))
    (hVt : D.ideal V = Ideal.span {t}) {m n k : ℕ} (hk : m + n = k)
    {a b : formalNeighborhoodRing D} (ha : a ∈ formalNeighborhoodFiltration D m)
    (hb : b ∈ formalNeighborhoodFiltration D n) :
    chartLeadingCoeff D V t k (a * b) = chartLeadingCoeff D V t m a * chartLeadingCoeff D V t n b :=
  hk ▸ chartLeadingCoeff_mul ht hVt ha hb

/-- The leading coefficient of a finite sum of elements of `Fₘ`. -/
public theorem chartLeadingCoeff_sum (ht : t ∈ nonZeroDivisors Γ(X, V.1))
    (hVt : D.ideal V = Ideal.span {t}) {ι : Type*} (s : Finset ι) {m : ℕ}
    (f : ι → formalNeighborhoodRing D) (hf : ∀ i ∈ s, f i ∈ formalNeighborhoodFiltration D m) :
    chartLeadingCoeff D V t m (∑ i ∈ s, f i) = ∑ i ∈ s, chartLeadingCoeff D V t m (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact chartLeadingCoeff_eq_zero_of_mem ht hVt (zero_mem _)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      chartLeadingCoeff_add ht hVt (hf i (Finset.mem_insert_self i s))
        (Submodule.sum_mem _ fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

/-- The leading coefficient of `1` in degree `0` is `1`. -/
public theorem chartLeadingCoeff_one (ht : t ∈ nonZeroDivisors Γ(X, V.1))
    (hVt : D.ideal V = Ideal.span {t}) :
    chartLeadingCoeff D V t 0 (1 : formalNeighborhoodRing D) = 1 := by
  rw [chartLeadingCoeff_eq ht hVt le_rfl (h := 1) (by rw [map_one, pow_zero, mul_one, map_one]),
    map_one]

/-! ### The value at a point -/

variable (D V t) in
/-- The *value at `p`* of an element of `Fₘ`: its leading coefficient in degree `m` over the
chart `V` with local equation `t`, reduced modulo the prime `𝔭 ⊇ D(V)` of the point `p`. -/
public def chartPointValue {P : Ideal Γ(X, V.1)} (hP : D.ideal V ≤ P) (m : ℕ)
    (a : formalNeighborhoodRing D) : Γ(X, V.1) ⧸ P :=
  Ideal.Quotient.factor hP (chartLeadingCoeff D V t m a)

variable {P : Ideal Γ(X, V.1)} (hP : D.ideal V ≤ P)

/-- The value at a point is multiplicative. -/
public theorem chartPointValue_mul (ht : t ∈ nonZeroDivisors Γ(X, V.1))
    (hVt : D.ideal V = Ideal.span {t}) {m n k : ℕ} (hk : m + n = k)
    {a b : formalNeighborhoodRing D} (ha : a ∈ formalNeighborhoodFiltration D m)
    (hb : b ∈ formalNeighborhoodFiltration D n) :
    chartPointValue D V t hP k (a * b) =
      chartPointValue D V t hP m a * chartPointValue D V t hP n b := by
  rw [chartPointValue, chartLeadingCoeff_mul_of_eq ht hVt hk ha hb, map_mul]; rfl

/-- The value at a point is additive on `Fₘ`. -/
public theorem chartPointValue_sum (ht : t ∈ nonZeroDivisors Γ(X, V.1))
    (hVt : D.ideal V = Ideal.span {t}) {ι : Type*} (s : Finset ι) {m : ℕ}
    (f : ι → formalNeighborhoodRing D) (hf : ∀ i ∈ s, f i ∈ formalNeighborhoodFiltration D m) :
    chartPointValue D V t hP m (∑ i ∈ s, f i) = ∑ i ∈ s, chartPointValue D V t hP m (f i) := by
  rw [chartPointValue, chartLeadingCoeff_sum ht hVt s f hf, map_sum]; rfl

/-- The value at a point is additive on `Fₘ`. -/
public theorem chartPointValue_add (ht : t ∈ nonZeroDivisors Γ(X, V.1))
    (hVt : D.ideal V = Ideal.span {t}) {m : ℕ} {a b : formalNeighborhoodRing D}
    (ha : a ∈ formalNeighborhoodFiltration D m) (hb : b ∈ formalNeighborhoodFiltration D m) :
    chartPointValue D V t hP m (a + b) =
      chartPointValue D V t hP m a + chartPointValue D V t hP m b := by
  rw [chartPointValue, chartLeadingCoeff_add ht hVt ha hb, map_add]; rfl

/-- The value at a point vanishes on the next step of the filtration. -/
public theorem chartPointValue_eq_zero_of_mem (ht : t ∈ nonZeroDivisors Γ(X, V.1))
    (hVt : D.ideal V = Ideal.span {t}) {m : ℕ} {a : formalNeighborhoodRing D}
    (ha : a ∈ formalNeighborhoodFiltration D (m + 1)) : chartPointValue D V t hP m a = 0 := by
  rw [chartPointValue, chartLeadingCoeff_eq_zero_of_mem ht hVt ha, map_zero]

/-- The value of a power. -/
public theorem chartPointValue_pow (ht : t ∈ nonZeroDivisors Γ(X, V.1))
    (hVt : D.ideal V = Ideal.span {t}) {k : ℕ} {a : formalNeighborhoodRing D}
    (ha : a ∈ formalNeighborhoodFiltration D k) (i : ℕ) :
    a ^ i ∈ formalNeighborhoodFiltration D (k * i) ∧
      chartPointValue D V t hP (k * i) (a ^ i) = chartPointValue D V t hP k a ^ i := by
  induction i with
  | zero =>
    refine ⟨by simp [formalNeighborhoodFiltration_zero], ?_⟩
    rw [pow_zero, pow_zero, mul_zero, chartPointValue, chartLeadingCoeff_one ht hVt, map_one]
  | succ i ih =>
    have hF := isCompleteFiltration_formalNeighborhoodFiltration D
    refine ⟨?_, ?_⟩
    · rw [pow_succ, Nat.mul_succ]
      exact hF.mul_le _ _ (Ideal.mul_mem_mul ih.1 ha)
    · rw [pow_succ, chartPointValue_mul hP ht hVt (Nat.mul_succ k i).symm ih.1 ha, ih.2, pow_succ]

/-! ### Symbols of combinations -/

/-- The symbol of `c a` is the residue of `c` times the symbol of `a`, in the form of
`gradedSectionsHom`. -/
public theorem gradedSectionsHom_residue_smul [IsEffectiveCartierDivisor D] (n : ℕ)
    (c : formalNeighborhoodRing D) (x : conormalPowSections D n) :
    gradedSectionsHom D n (formalNeighborhoodResidueMap D c • x) =
      formalNeighborhoodProjection D (n + 1) c * gradedSectionsHom D n x := by
  rw [← inclusion_appTop_formalNeighborhoodProjection D (n + 1) c, gradedSectionsHom_smul]

/-! ### The dimension count -/

section Count

variable [IsEffectiveCartierDivisor D] [IsIntegral D.subscheme]
  (hsurj : ∀ m, Function.Surjective (thickeningRestriction D m))
  (hfield : IsField Γ(D.subscheme, ⊤))
  (hdim : ∀ n, Module.finrank Γ(D.subscheme, ⊤) (conormalPowSections D n) = n + 1)
  (ht : t ∈ nonZeroDivisors Γ(X, V.1)) (hVt : D.ideal V = Ideal.span {t})
  [P.IsPrime]

omit [IsIntegral D.subscheme] in
/-- Every element of `Fₙ₊₁` is the lift of its symbol. -/
private theorem exists_section_eq (n : ℕ) {z : formalNeighborhoodRing D}
    (hz : z ∈ formalNeighborhoodFiltration D (n + 1)) :
    ∃ x : conormalPowSections D n,
      gradedSectionsHom D n x = formalNeighborhoodProjection D (n + 1) z :=
  (gradedSectionsHom_eq_iff D n _).1 (thickeningRestriction_projection_eq_zero D n hz)

omit [IsIntegral D.subscheme] in
include hsurj in
/-- Every section of `Lⁿ⁺¹` is the symbol of an element of `Fₙ₊₁`. -/
private theorem exists_lift (n : ℕ) (x : conormalPowSections D n) :
    ∃ z ∈ formalNeighborhoodFiltration D (n + 1),
      formalNeighborhoodProjection D (n + 1) z = gradedSectionsHom D n x :=
  exists_projection_eq_of_thickeningRestriction_eq_zero D n hsurj
    ((gradedSectionsHom_eq_iff D n _).2 ⟨x, rfl⟩)

omit [IsIntegral D.subscheme] in
/-- A symbol vanishes exactly when the element it comes from lies in the next step. -/
private theorem eq_zero_iff_of_gradedSectionsHom_eq (n : ℕ) {x : conormalPowSections D n}
    {z : formalNeighborhoodRing D}
    (h : gradedSectionsHom D n x = formalNeighborhoodProjection D (n + 1) z) :
    x = 0 ↔ z ∈ formalNeighborhoodFiltration D (n + 2) := by
  change _ ↔ formalNeighborhoodProjection D (n + 1) z = 0
  rw [← h]
  exact ⟨fun hx => by rw [hx, map_zero], fun hx =>
    gradedSectionsHom_injective D n (by rw [hx, map_zero])⟩

omit [IsIntegral D.subscheme] in
/-- The symbol of a combination `∑ cᵢ zᵢ`. -/
private theorem gradedSectionsHom_sum (n : ℕ) {ι : Type*} (s : Finset ι)
    (c : ι → formalNeighborhoodRing D) (x : ι → conormalPowSections D n)
    (z : ι → formalNeighborhoodRing D)
    (hz : ∀ i, gradedSectionsHom D n (x i) = formalNeighborhoodProjection D (n + 1) (z i)) :
    gradedSectionsHom D n (∑ i ∈ s, formalNeighborhoodResidueMap D (c i) • x i) =
      formalNeighborhoodProjection D (n + 1) (∑ i ∈ s, c i * z i) := by
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gradedSectionsHom_residue_smul, hz, map_mul]

omit [IsEffectiveCartierDivisor D] [IsIntegral D.subscheme] in
include hsurj hfield ht hVt in
/-- An element of `A` whose value at `p` in degree `0` vanishes lies in `F₁`. -/
private theorem mem_one_of_chartPointValue_zero_eq_zero {c : formalNeighborhoodRing D}
    (hc : chartPointValue D V t hP 0 c = 0) : c ∈ formalNeighborhoodFiltration D 1 := by
  have hA := isField_quotient_formalNeighborhoodFiltration_one_of_isField D
    (surjective_formalNeighborhoodProjection D hsurj 0) hfield
  by_contra hc1
  have hne : Ideal.Quotient.mk (formalNeighborhoodFiltration D 1) c ≠ 0 := fun h =>
    hc1 (Ideal.Quotient.eq_zero_iff_mem.1 h)
  obtain ⟨d', hd'⟩ := hA.mul_inv_cancel hne
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d'
  rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at hd'
  have h0 := chartPointValue_eq_zero_of_mem hP ht hVt (m := 0) hd'
  have htop : ∀ e : formalNeighborhoodRing D, e ∈ formalNeighborhoodFiltration D 0 := fun e => by
    rw [formalNeighborhoodFiltration_zero]; exact Submodule.mem_top
  rw [sub_eq_add_neg, chartPointValue_add hP ht hVt (htop _) (htop _),
    chartPointValue_mul hP ht hVt (zero_add 0) (htop _) (htop _), hc, zero_mul, zero_add] at h0
  have h1 : chartPointValue D V t hP 0 (1 + -1) = 0 := by
    rw [add_neg_cancel]
    exact chartPointValue_eq_zero_of_mem hP ht hVt (zero_mem _)
  rw [chartPointValue_add hP ht hVt (htop _) (htop _), h0, add_zero, chartPointValue,
    chartLeadingCoeff_one ht hVt, map_one] at h1
  exact one_ne_zero h1

include hsurj hfield hdim ht hVt in
/-- **The count in degree `n + 1 ≥ 2`.** If `a ∈ F₁ \ F₂` has value `0` at `p` and `e ∈ Fₙ₊₁` has
nonzero value at `p`, every element of `Fₙ₊₁` is `c e + a w` modulo `Fₙ₊₂`, with `w ∈ Fₙ`. -/
private theorem exists_eq_mul_add_mul {n : ℕ} (hn : 1 ≤ n) {a e : formalNeighborhoodRing D}
    (ha : a ∈ formalNeighborhoodFiltration D 1) (ha' : a ∉ formalNeighborhoodFiltration D 2)
    (ha0 : chartPointValue D V t hP 1 a = 0)
    (he : e ∈ formalNeighborhoodFiltration D (n + 1))
    (he0 : chartPointValue D V t hP (n + 1) e ≠ 0) {z : formalNeighborhoodRing D}
    (hz : z ∈ formalNeighborhoodFiltration D (n + 1)) :
    ∃ w ∈ formalNeighborhoodFiltration D n, ∃ c : formalNeighborhoodRing D,
      z - (c * e + a * w) ∈ formalNeighborhoodFiltration D (n + 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let _ := hfield.toField
  have hF := isCompleteFiltration_formalNeighborhoodFiltration D
  have hres := surjective_formalNeighborhoodResidueMap D
    (surjective_formalNeighborhoodProjection D hsurj 0)
  have : Module.Finite Γ(D.subscheme, ⊤) (conormalPowSections D m) :=
    Module.finite_of_finrank_pos (by rw [hdim]; omega)
  let b := Module.finBasisOfFinrankEq Γ(D.subscheme, ⊤) (conormalPowSections D m) (hdim m)
  choose zz hzzF hzzP using fun i => exists_lift hsurj m (b i)
  have hazz : ∀ i, a * zz i ∈ formalNeighborhoodFiltration D (m + 1 + 1) := fun i =>
    (show 1 + (m + 1) = m + 1 + 1 by omega) ▸ hF.mul_le 1 (m + 1) (Ideal.mul_mem_mul ha (hzzF i))
  choose f hf using fun i => exists_section_eq (m + 1) (hazz i)
  obtain ⟨e', he'⟩ := exists_section_eq (m + 1) he
  let v : Fin (m + 1 + 1) → conormalPowSections D (m + 1) := Fin.cons e' f
  let zv : Fin (m + 1 + 1) → formalNeighborhoodRing D := Fin.cons e fun i => a * zz i
  have hv : ∀ i, gradedSectionsHom D (m + 1) (v i) =
      formalNeighborhoodProjection D (m + 1 + 1) (zv i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact he'
    · exact hf j
  -- The combination `∑ cᵢ zvᵢ` splits as `c₀ e + a ∑ c_{j+1} zz_j`.
  have hsplit : ∀ c : Fin (m + 1 + 1) → formalNeighborhoodRing D,
      ∑ i, c i * zv i = c 0 * e + a * ∑ j, c j.succ * zz j := by
    intro c
    rw [Fin.sum_univ_succ, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by simp only [zv, Fin.cons_succ]; ring
  have hlin : LinearIndependent Γ(D.subscheme, ⊤) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    choose cc hcc using fun i => hres (g i)
    have hW : ∑ i, cc i * zv i ∈ formalNeighborhoodFiltration D (m + 1 + 2) := by
      have h := gradedSectionsHom_sum (m + 1) Finset.univ cc v zv hv
      simp only [hcc] at h
      rw [hg, map_zero] at h
      exact h.symm
    rw [hsplit] at hW
    have hw : ∑ j, cc j.succ * zz j ∈ formalNeighborhoodFiltration D (m + 1) :=
      Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hzzF j)
    have htop : cc 0 ∈ formalNeighborhoodFiltration D 0 := by
      rw [formalNeighborhoodFiltration_zero]; exact Submodule.mem_top
    -- The value at `p` of the combination kills the coefficient of `e`.
    have hval := chartPointValue_eq_zero_of_mem hP ht hVt (m := m + 1 + 1) hW
    have hm1 : cc 0 * e ∈ formalNeighborhoodFiltration D (m + 1 + 1) := by
      have := hF.mul_le 0 (m + 1 + 1) (Ideal.mul_mem_mul htop he)
      rwa [zero_add] at this
    have hm2 : a * ∑ j, cc j.succ * zz j ∈ formalNeighborhoodFiltration D (m + 1 + 1) := by
      have := hF.mul_le 1 (m + 1) (Ideal.mul_mem_mul ha hw)
      rwa [show 1 + (m + 1) = m + 1 + 1 by omega] at this
    rw [chartPointValue_add hP ht hVt hm1 hm2,
      chartPointValue_mul hP ht hVt (zero_add _) htop he,
      chartPointValue_mul hP ht hVt (by omega : 1 + (m + 1) = m + 1 + 1) ha hw, ha0, zero_mul,
      add_zero, mul_eq_zero] at hval
    have hc0 : cc 0 ∈ formalNeighborhoodFiltration D 1 :=
      mem_one_of_chartPointValue_zero_eq_zero hP hsurj hfield ht hVt
        (hval.resolve_right he0)
    have hg0 : g 0 = 0 := by
      rw [← hcc 0, ← RingHom.mem_ker, ker_formalNeighborhoodResidueMap]; exact hc0
    -- Then `a ∑ c_{j+1} zz_j ∈ F_{m+3}`, so `∑ c_{j+1} zz_j ∈ F_{m+2}`.
    have hce : cc 0 * e ∈ formalNeighborhoodFiltration D (m + 1 + 2) :=
      (show 1 + (m + 1 + 1) = m + 1 + 2 by omega) ▸ hF.mul_le 1 (m + 1 + 1)
        (Ideal.mul_mem_mul hc0 he)
    have haw : a * ∑ j, cc j.succ * zz j ∈ formalNeighborhoodFiltration D (1 + (m + 1) + 1) := by
      have := sub_mem hW hce
      rw [add_sub_cancel_left] at this
      exact (show m + 1 + 2 = 1 + (m + 1) + 1 by omega) ▸ this
    have hw2 : ∑ j, cc j.succ * zz j ∈ formalNeighborhoodFiltration D (m + 1 + 1) := by
      by_contra hw2
      exact mul_notMem_formalNeighborhoodFiltration ha ha' hw hw2 haw
    have hb0 : ∑ j, g j.succ • b j = 0 := by
      refine (eq_zero_iff_of_gradedSectionsHom_eq m ?_).2 hw2
      have h := gradedSectionsHom_sum m Finset.univ (fun j => cc j.succ) b zz
        (fun j => (hzzP j).symm)
      simpa only [hcc] using h
    have hbj := (Fintype.linearIndependent_iff.1 b.linearIndependent) _ hb0
    intro i
    refine Fin.cases hg0 (fun j => hbj j) i
  have hspan : Submodule.span Γ(D.subscheme, ⊤) (Set.range v) = ⊤ :=
    hlin.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hdim])
  obtain ⟨x, hx⟩ := exists_section_eq (m + 1) hz
  have hxm : x ∈ Submodule.span Γ(D.subscheme, ⊤) (Set.range v) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hxm
  choose cc hcc using fun i => hres (g i)
  refine ⟨∑ j, cc j.succ * zz j, Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hzzF j),
    cc 0, ?_⟩
  have h := gradedSectionsHom_sum (m + 1) Finset.univ cc v zv hv
  simp only [hcc] at h
  rw [hg, hx, hsplit] at h
  change formalNeighborhoodProjection D (m + 1 + 1) _ = 0
  rw [map_sub, h, sub_self]

include hsurj hfield hdim ht hVt in
/-- **Generation in degrees `1, 2, 3`.** Let `p` be a point of `C` (the prime `𝔭 ⊇ D(V)`) at which
every section of `L` vanishes, while `x ∈ F₂` and `y ∈ F₃` have nonzero values. If
`dim H⁰(C, Lⁿ) = n` for `n ≥ 1`, then for some `a ∈ F₁`,
`Fₙ ⊆ (a, x, y) · F_{n-3} + Fₙ₊₁` for every `n ≥ 1`. -/
public theorem exists_le_mul_sup_three_of_chartPointValue
    (h1 : ∀ a ∈ formalNeighborhoodFiltration D 1, chartPointValue D V t hP 1 a = 0)
    {x y : formalNeighborhoodRing D} (hx : x ∈ formalNeighborhoodFiltration D 2)
    (hx0 : chartPointValue D V t hP 2 x ≠ 0) (hy : y ∈ formalNeighborhoodFiltration D 3)
    (hy0 : chartPointValue D V t hP 3 y ≠ 0) :
    ∃ g : Fin 3 → formalNeighborhoodRing D, (∀ i, g i ∈ formalNeighborhoodFiltration D 1) ∧
      ∀ n, 1 ≤ n → formalNeighborhoodFiltration D n ≤
        Ideal.span (Set.range g) * formalNeighborhoodFiltration D (n - 3) ⊔
          formalNeighborhoodFiltration D (n + 1) := by
  let _ := hfield.toField
  have hF := isCompleteFiltration_formalNeighborhoodFiltration D
  have hres := surjective_formalNeighborhoodResidueMap D
    (surjective_formalNeighborhoodProjection D hsurj 0)
  have : Module.Finite Γ(D.subscheme, ⊤) (conormalPowSections D 0) :=
    Module.finite_of_finrank_pos (by rw [hdim]; omega)
  obtain ⟨σ, hσ⟩ := Module.finrank_pos_iff_exists_ne_zero.1
    (show 0 < Module.finrank Γ(D.subscheme, ⊤) (conormalPowSections D 0) by rw [hdim]; omega)
  obtain ⟨a, ha, haσ⟩ := exists_lift hsurj 0 σ
  have ha' : a ∉ formalNeighborhoodFiltration D 2 := fun h =>
    hσ ((eq_zero_iff_of_gradedSectionsHom_eq 0 haσ.symm).2 h)
  let g : Fin 3 → formalNeighborhoodRing D := ![a, x, y]
  have hgJ : a ∈ Ideal.span (Set.range g) ∧ x ∈ Ideal.span (Set.range g) ∧
      y ∈ Ideal.span (Set.range g) :=
    ⟨Ideal.subset_span ⟨0, rfl⟩, Ideal.subset_span ⟨1, rfl⟩, Ideal.subset_span ⟨2, rfl⟩⟩
  refine ⟨g, fun i => ?_, fun n hn => ?_⟩
  · fin_cases i
    · exact ha
    · exact hF.antitone (by omega) hx
    · exact hF.antitone (by omega) hy
  intro z hz
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · -- Degree one: `H⁰(L)` is spanned by the symbol of `a`.
    obtain rfl : n = 1 := by omega
    obtain ⟨x0, hx0'⟩ := exists_section_eq (n := 0) hz
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' σ hσ).1 (hdim 0) x0
    obtain ⟨c', rfl⟩ := hres c
    refine Submodule.mem_sup.2 ⟨c' * a, ?_, z - c' * a, ?_, by ring⟩
    · rw [show (1 : ℕ) - 3 = 0 by rfl, formalNeighborhoodFiltration_zero, Ideal.mul_top]
      exact Ideal.mul_mem_left _ _ hgJ.1
    · change formalNeighborhoodProjection D (0 + 1) (z - c' * a) = 0
      rw [map_sub, map_mul, haσ, ← gradedSectionsHom_residue_smul, hc, hx0', sub_self]
  · -- Degree `n ≥ 2`: a monomial in `x, y` with nonzero value at `p`.
    have hdom : IsDomain (Γ(X, V.1) ⧸ P) := Ideal.Quotient.isDomain P
    obtain ⟨e, he, he0, heJ⟩ : ∃ e ∈ formalNeighborhoodFiltration D n,
        chartPointValue D V t hP n e ≠ 0 ∧
          e ∈ Ideal.span (Set.range g) * formalNeighborhoodFiltration D (n - 3) := by
      rcases Nat.even_or_odd n with ⟨i, hi⟩ | ⟨i, hi⟩
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        have hp := chartPointValue_pow hP ht hVt hx (j + 1)
        have hpj := chartPointValue_pow hP ht hVt hx j
        rw [show 2 * (j + 1) = n by omega] at hp
        refine ⟨x ^ (j + 1), hp.1, by rw [hp.2]; exact pow_ne_zero _ hx0, ?_⟩
        rw [pow_succ']
        exact Ideal.mul_mem_mul hgJ.2.1 (hF.antitone (by omega) hpj.1)
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        have hpj := chartPointValue_pow hP ht hVt hx j
        have hyx : y * x ^ j ∈ formalNeighborhoodFiltration D n :=
          (show 3 + 2 * j = n by omega) ▸ hF.mul_le 3 (2 * j) (Ideal.mul_mem_mul hy hpj.1)
        refine ⟨y * x ^ j, hyx, ?_, ?_⟩
        · rw [chartPointValue_mul hP ht hVt (show 3 + 2 * j = n by omega) hy hpj.1, hpj.2]
          exact mul_ne_zero hy0 (pow_ne_zero _ hx0)
        · exact Ideal.mul_mem_mul hgJ.2.2 (by rw [show n - 3 = 2 * j by omega]; exact hpj.1)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨w, hw, c, hc⟩ := exists_eq_mul_add_mul hP hsurj hfield hdim ht hVt (n := k)
      (by omega) ha ha' (h1 a ha) he he0 hz
    refine Submodule.mem_sup.2 ⟨c * e + a * w, add_mem (Ideal.mul_mem_left _ _ heJ)
      (Ideal.mul_mem_mul hgJ.1 (hF.antitone (by omega) hw)), z - (c * e + a * w), hc, by ring⟩

include hsurj hfield hdim ht hVt in
/-- **The formal neighbourhood of a curve of genus one with conormal bundle `𝒪(p)` is a complete
Noetherian local ring**, in the form: `C` integral, `Γ(C, 𝒪_C)` a field, surjective transition
maps, `dim H⁰(C, Lⁿ) = n` for `n ≥ 1`, every section of `L` vanishing at the point `p` and
elements of `F₂`, `F₃` with nonzero value at `p`. -/
public theorem isNoetherianCompleteLocalRing_of_chartPointValue
    (h1 : ∀ a ∈ formalNeighborhoodFiltration D 1, chartPointValue D V t hP 1 a = 0)
    {x y : formalNeighborhoodRing D} (hx : x ∈ formalNeighborhoodFiltration D 2)
    (hx0 : chartPointValue D V t hP 2 x ≠ 0) (hy : y ∈ formalNeighborhoodFiltration D 3)
    (hy0 : chartPointValue D V t hP 3 y ≠ 0) :
    IsNoetherianCompleteLocalRing (formalNeighborhoodRing D) := by
  obtain ⟨g, hg, hstep⟩ := exists_le_mul_sup_three_of_chartPointValue hP hsurj hfield hdim ht
    hVt h1 hx hx0 hy hy0
  exact (isCompleteFiltration_formalNeighborhoodFiltration D)
    |>.isNoetherianCompleteLocalRing_of_le_mul_sup g 3 (by omega) hg hstep
      (isField_quotient_formalNeighborhoodFiltration_one_of_isField D
        (surjective_formalNeighborhoodProjection D hsurj 0) hfield)

omit [IsIntegral D.subscheme] in
include hsurj hfield hdim in
/-- An element of `F₁ \ F₂`, the lift of a nonzero section of `L`. -/
private theorem exists_mem_one_notMem_two :
    ∃ a ∈ formalNeighborhoodFiltration D 1, a ∉ formalNeighborhoodFiltration D 2 := by
  let _ := hfield.toField
  have : Module.Finite Γ(D.subscheme, ⊤) (conormalPowSections D 0) :=
    Module.finite_of_finrank_pos (by rw [hdim]; omega)
  obtain ⟨σ, hσ⟩ := Module.finrank_pos_iff_exists_ne_zero.1
    (show 0 < Module.finrank Γ(D.subscheme, ⊤) (conormalPowSections D 0) by rw [hdim]; omega)
  obtain ⟨a, ha, haσ⟩ := exists_lift hsurj 0 σ
  exact ⟨a, ha, fun h => hσ ((eq_zero_iff_of_gradedSectionsHom_eq 0 haσ.symm).2 h)⟩

include hsurj hfield hdim ht hVt in
/-- In degrees `n ≥ 4` the filtration is generated by `a` and `x` alone:
`Fₙ ⊆ (a, x) + Fₙ₊₁`. -/
private theorem le_span_pair_sup {n : ℕ} (hn : 4 ≤ n) {a x y : formalNeighborhoodRing D}
    (ha : a ∈ formalNeighborhoodFiltration D 1) (ha' : a ∉ formalNeighborhoodFiltration D 2)
    (ha0 : chartPointValue D V t hP 1 a = 0) (hx : x ∈ formalNeighborhoodFiltration D 2)
    (hx0 : chartPointValue D V t hP 2 x ≠ 0) (hy : y ∈ formalNeighborhoodFiltration D 3)
    (hy0 : chartPointValue D V t hP 3 y ≠ 0) :
    formalNeighborhoodFiltration D n ≤
      Ideal.span {a, x} ⊔ formalNeighborhoodFiltration D (n + 1) := by
  have hF := isCompleteFiltration_formalNeighborhoodFiltration D
  have hdom : IsDomain (Γ(X, V.1) ⧸ P) := Ideal.Quotient.isDomain P
  have hxK : x ∈ Ideal.span {a, x} := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have haK : a ∈ Ideal.span {a, x} := Ideal.subset_span (Set.mem_insert _ _)
  obtain ⟨e, he, he0, heK⟩ : ∃ e ∈ formalNeighborhoodFiltration D n,
      chartPointValue D V t hP n e ≠ 0 ∧ e ∈ Ideal.span {a, x} := by
    rcases Nat.even_or_odd n with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hp := chartPointValue_pow hP ht hVt hx i
      rw [show 2 * i = n by omega] at hp
      refine ⟨x ^ i, hp.1, by rw [hp.2]; exact pow_ne_zero _ hx0, ?_⟩
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [pow_succ']
      exact Ideal.mul_mem_right _ _ hxK
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hpj := chartPointValue_pow hP ht hVt hx j
      have hyx : y * x ^ j ∈ formalNeighborhoodFiltration D n :=
        (show 3 + 2 * j = n by omega) ▸ hF.mul_le 3 (2 * j) (Ideal.mul_mem_mul hy hpj.1)
      refine ⟨y * x ^ j, hyx, ?_, ?_⟩
      · rw [chartPointValue_mul hP ht hVt (show 3 + 2 * j = n by omega) hy hpj.1, hpj.2]
        exact mul_ne_zero hy0 (pow_ne_zero _ hx0)
      · obtain ⟨l, rfl⟩ : ∃ l, j = l + 1 := ⟨j - 1, by omega⟩
        rw [pow_succ', mul_left_comm]
        exact Ideal.mul_mem_right _ _ hxK
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  intro z hz
  obtain ⟨w, -, c, hc⟩ := exists_eq_mul_add_mul hP hsurj hfield hdim ht hVt (n := k)
    (by omega) ha ha' ha0 he he0 hz
  exact Submodule.mem_sup.2 ⟨c * e + a * w, add_mem (Ideal.mul_mem_left _ _ heK)
    (Ideal.mul_mem_right _ _ haK), z - (c * e + a * w), hc, by ring⟩

include hsurj hfield hdim ht hVt in
/-- `F₄ ⊆ (a, x)`: in degrees `≥ 4` the filtration is generated by `a` and `x`, and `(a, x)` is
closed (Krull's intersection theorem in the complete Noetherian local ring `A`). -/
private theorem formalNeighborhoodFiltration_four_le_span_pair
    (h1 : ∀ a ∈ formalNeighborhoodFiltration D 1, chartPointValue D V t hP 1 a = 0)
    {a x y : formalNeighborhoodRing D}
    (ha : a ∈ formalNeighborhoodFiltration D 1) (ha' : a ∉ formalNeighborhoodFiltration D 2)
    (hx : x ∈ formalNeighborhoodFiltration D 2)
    (hx0 : chartPointValue D V t hP 2 x ≠ 0) (hy : y ∈ formalNeighborhoodFiltration D 3)
    (hy0 : chartPointValue D V t hP 3 y ≠ 0) :
    formalNeighborhoodFiltration D 4 ≤ Ideal.span {a, x} := by
  have hN := isNoetherianCompleteLocalRing_of_chartPointValue hP hsurj hfield hdim ht hVt h1 hx
    hx0 hy hy0
  have hNoeth := hN.isNoetherian
  have hLoc := hN.isLocal
  have hF := isCompleteFiltration_formalNeighborhoodFiltration D
  obtain ⟨g, hg, hstep⟩ := exists_le_mul_sup_three_of_chartPointValue hP hsurj hfield hdim ht
    hVt h1 hx hx0 hy hy0
  have hgF : Ideal.span (Set.range g) ≤ formalNeighborhoodFiltration D 1 :=
    Ideal.span_le.2 (Set.range_subset_iff.2 hg)
  have hKN : ∀ N, formalNeighborhoodFiltration D 4 ≤
      Ideal.span {a, x} ⊔ formalNeighborhoodFiltration D (4 + N) := by
    intro N
    induction N with
    | zero => exact le_sup_right
    | succ N ih =>
      exact ih.trans (sup_le le_sup_left
        (le_span_pair_sup hP hsurj hfield hdim ht hVt (by omega) ha ha' (h1 a ha) hx hx0 hy hy0))
  have h1top : formalNeighborhoodFiltration D 1 ≠ ⊤ := by
    intro h
    have h11 : (1 : formalNeighborhoodRing D) ∈ formalNeighborhoodFiltration D 1 :=
      h ▸ Submodule.mem_top
    have h2 := hF.mul_le 1 1 (Ideal.mul_mem_mul h11 h11)
    rw [mul_one] at h2
    exact ha' (by simpa using Ideal.mul_mem_left _ a h2)
  intro z hz
  refine Stacks.mem_of_forall_mem_sup_pow _ h1top fun i => ?_
  have := hKN (3 * i) hz
  exact (sup_le_sup_left ((hF.antitone (by omega)).trans
    ((hF.le_pow_of_le_mul_sup g 3 (by omega) hstep i).trans (Ideal.pow_right_mono hgF i))) _)
    this

include ht hVt in
/-- No power of `F₁` lies in `(a)`: otherwise `xᴺ = a w`, and comparing degrees with the
filtration, the value at `p` of `xᴺ` would be that of `a w`, which is `0`. -/
private theorem not_pow_le_span_singleton
    (h1 : ∀ a ∈ formalNeighborhoodFiltration D 1, chartPointValue D V t hP 1 a = 0)
    {a x : formalNeighborhoodRing D}
    (ha : a ∈ formalNeighborhoodFiltration D 1) (ha' : a ∉ formalNeighborhoodFiltration D 2)
    (hx : x ∈ formalNeighborhoodFiltration D 2)
    (hx0 : chartPointValue D V t hP 2 x ≠ 0) (N : ℕ) :
    ¬ formalNeighborhoodFiltration D 1 ^ N ≤ Ideal.span {a} := by
  intro hNle
  have hF := isCompleteFiltration_formalNeighborhoodFiltration D
  have hdomP : IsDomain (Γ(X, V.1) ⧸ P) := Ideal.Quotient.isDomain P
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1
    (hNle (Ideal.pow_mem_pow (hF.antitone (show 1 ≤ 2 by omega) hx) N))
  have hxN := chartPointValue_pow hP ht hVt hx N
  have hxN0 : chartPointValue D V t hP (2 * N) (x ^ N) ≠ 0 := by
    rw [hxN.2]; exact pow_ne_zero _ hx0
  have hxNnot : x ^ N ∉ formalNeighborhoodFiltration D (2 * N + 1) := fun h =>
    hxN0 (chartPointValue_eq_zero_of_mem hP ht hVt h)
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hw
    exact hxNnot (hw ▸ zero_mem _)
  obtain ⟨j, hwj, hwj'⟩ := exists_mem_formalNeighborhoodFiltration_notMem_succ hw0
  have haw : a * w ∉ formalNeighborhoodFiltration D (1 + j + 1) :=
    mul_notMem_formalNeighborhoodFiltration ha ha' hwj hwj'
  have haw' : a * w ∈ formalNeighborhoodFiltration D (1 + j) :=
    hF.mul_le 1 j (Ideal.mul_mem_mul ha hwj)
  rw [mul_comm] at hw
  rcases lt_trichotomy (1 + j) (2 * N) with hlt | heq | hgt
  · exact haw (hw ▸ hF.antitone (by omega) hxN.1)
  · apply hxN0
    rw [← hw, chartPointValue_mul hP ht hVt heq ha hwj, h1 a ha, zero_mul]
  · exact hxNnot (hw ▸ hF.antitone (by omega) haw')

include hsurj hfield hdim ht hVt in
/-- **The formal neighbourhood of a curve of genus one with conormal bundle `𝒪(p)` has Krull
dimension two**, under the hypotheses of
`AlgebraicGeometry.Scheme.IdealSheafData.isNoetherianCompleteLocalRing_of_chartPointValue`.

`dim A ≤ 2`: in degrees `≥ 4` the filtration is generated by `a ∈ F₁` and `x ∈ F₂`, so
`𝔪⁴ ⊆ F₄ ⊆ (a, x)` by Krull's intersection theorem, and Krull's height theorem bounds the height
of `𝔪` by `2`. `dim A ≥ 2`: `A` is a domain, and a minimal prime over `(a)` is not `𝔪`, for
otherwise `xᴺ ∈ (a)` for some `N`, which the value at `p` forbids. -/
public theorem ringKrullDim_formalNeighborhoodRing_eq_two_of_chartPointValue
    (h1 : ∀ a ∈ formalNeighborhoodFiltration D 1, chartPointValue D V t hP 1 a = 0)
    {x y : formalNeighborhoodRing D} (hx : x ∈ formalNeighborhoodFiltration D 2)
    (hx0 : chartPointValue D V t hP 2 x ≠ 0) (hy : y ∈ formalNeighborhoodFiltration D 3)
    (hy0 : chartPointValue D V t hP 3 y ≠ 0) :
    ringKrullDim (formalNeighborhoodRing D) = 2 := by
  have hN := isNoetherianCompleteLocalRing_of_chartPointValue hP hsurj hfield hdim ht hVt h1 hx
    hx0 hy hy0
  have hNoeth := hN.isNoetherian
  have hLoc := hN.isLocal
  have hDom : IsDomain (formalNeighborhoodRing D) := isDomain_formalNeighborhoodRing
  have hF := isCompleteFiltration_formalNeighborhoodFiltration D
  have hA := isField_quotient_formalNeighborhoodFiltration_one_of_isField D
    (surjective_formalNeighborhoodProjection D hsurj 0) hfield
  have hm : IsLocalRing.maximalIdeal (formalNeighborhoodRing D) =
      formalNeighborhoodFiltration D 1 :=
    (IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField _ hA)).symm
  obtain ⟨a, ha, ha'⟩ := exists_mem_one_notMem_two hsurj hfield hdim
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  refine le_antisymm ?_ ?_
  · have h4 : IsLocalRing.maximalIdeal (formalNeighborhoodRing D) ^ 4 ≤ Ideal.span {a, x} := by
      rw [hm]
      exact (hF.pow_le _ le_rfl 4).trans (formalNeighborhoodFiltration_four_le_span_pair hP hsurj
        hfield hdim ht hVt h1 ha ha' hx hx0 hy hy0)
    have hK : Ideal.span {a, x} ≤ IsLocalRing.maximalIdeal (formalNeighborhoodRing D) := by
      rw [hm, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨ha, hF.antitone (show 1 ≤ 2 by omega) hx⟩
    have h := Stacks.height_maximalIdeal_le_two_of_pow_le_span_pair hK h4
    rw [show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl]
    exact WithBot.coe_le_coe.2 h
  · have h2 := Stacks.two_le_height_maximalIdeal (R := formalNeighborhoodRing D) (a := a)
      (fun h => ha' (h ▸ zero_mem _)) (hm ▸ ha) fun N => by
        rw [hm]; exact not_pow_le_span_singleton hP ht hVt h1 ha ha' hx hx0 N
    rw [show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl]
    exact WithBot.coe_le_coe.2 h2

end Count

end AlgebraicGeometry.Scheme.IdealSheafData

end
