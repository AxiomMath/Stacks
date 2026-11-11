module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.DeterminantNormLength
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.SymbolOnNormalization
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.PairSymbol
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Independence
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolPreparationValue
public import StacksFrontier.RingTheory.Length.SemilocalDecomposition
public import StacksFrontier.RingTheory.Length.FiniteModification

/-!
# The tame symbol of Stacks 0EAQ is the symbol `d_A` of Stacks 02PZ

Let `(A, 𝔪)` be a Noetherian local ring of dimension one. Section 42.5 (Stacks 0EAH) defines the
tame symbol `∂_A(a, b)` of two nonzerodivisors by the recipe of Stacks 0EAQ: choose a finite
extension `A ⊆ B` as in Stacks 0EAG with local factorizations `a = u_𝔮 π_𝔮^{e_𝔮}`,
`b = v_𝔮 π_𝔮^{f_𝔮}` at the maximal ideals `𝔮` of `B`, and set

`∂_A(a, b) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}((-1)^{e_𝔮 f_𝔮} ū_𝔮^{f_𝔮} v̄_𝔮^{-e_𝔮})^{m_𝔮}`,
`m_𝔮 = length_{B_𝔮}(B_𝔮/π_𝔮 B_𝔮)`

(`Stacks.Chow.tameSymbolValue`). Appendix A of the chapter defines instead the symbol
`d_A(a, b) = det_κ(A/abA, a, b)` of Stacks 02PZ, a periodic determinant
(`Stacks.Chow.regularModuleSymbol`), whose extension to the fraction field is the tame symbol of
Stacks 02Q1. This file proves that the two agree:

`d_A(a, b) = ∂_A(a, b)` (`Stacks.Chow.regularModuleSymbol_eq_tameSymbolValue`),

for every one-dimensional Noetherian local ring and every pair of nonzerodivisors, and
consequently that the extensions of the two to `Q(A)^*` agree
(`Stacks.Chow.tameSymbolOfKrullDimOne_eq_formulaTameSymbol`).

## The argument

If `a` and `b` are both units, both sides are `1`. Otherwise Stacks 0EAG supplies a finite
extension `A ⊆ B` with a power of `𝔪` killing `B/A`, and local factorizations of `a` and `b`.

* By Stacks 02Q4 the symbol `d_A(a, b)` may be computed on the finite `A`-module `B`; it is the
  periodic determinant `d^A_B(a, b)` over `A` of `(B/abB, a, b)`, which is defined, and
  bimultiplicative, for any two nonzerodivisors of `B` (`Stacks.Chow.regularAlgebraSymbol`).
* The local parameters can be chosen *global*: for each maximal ideal `𝔮` there is `t_𝔮 ∈ B`, a
  unit multiple of `π_𝔮` in `B_𝔮` and a unit at every other maximal ideal, by approximating
  `π_𝔮` modulo a high power of `𝔮` (`Stacks.Chow.exists_globalParameter`). Then `a` is a unit of
  `B` times `∏_𝔮 t_𝔮^{e_𝔮}`, because the two generate the same ideal at every maximal ideal
  (`Stacks.Chow.exists_isUnit_mul_prod_globalParameter`), and similarly for `b`.
* On the other side, the recipe of Stacks 0EAQ is the product over `𝔮` of the norms of the
  symbols `d_{B_𝔮}` of the one-dimensional local rings `B_𝔮`
  (`Stacks.Chow.tameSymbol_apply_eq_of_tameSymbolPreparation`); this product,
  `Stacks.Chow.localSymbolProduct`, is also bimultiplicative on the nonzerodivisors of `B`.
* So it suffices to compare `d^A_B` with the product on the units of `B` and the `t_𝔮`. For two
  coprime elements `d^A_B` is a ratio of residue-field determinants of multiplications on `B/sB`
  and `B/tB` (Stacks 02PN); for `t = t_𝔮` the quotient `B/tB` is `B_𝔮/tB_𝔮`, and the
  determinant over `κ(𝔪)` of multiplication by a unit `s` there is `Norm(s̄)^{length}`
  (Stacks 0GSZ, `Stacks.Chow.determinantAutomorphism_eq_norm_pow_length`). The symbol
  `d_{B_𝔮}` takes the same values by Stacks 0EAM and 0EAN.

## Main results

* `Stacks.Chow.regularModuleSymbol_eq_tameSymbolValue` — `d_A = ∂_A` on nonzerodivisors.
* `Stacks.Chow.regularTameSymbolOfKrullDimOne_eq_formulaRegularTameSymbol`,
  `Stacks.Chow.tameSymbolOfKrullDimOne_eq_formulaTameSymbol` — the same as tame symbols, on
  nonzerodivisors and on `Q(A)^*`.

## References

* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
* [Stacks Project, Tag 02PZ](https://stacks.math.columbia.edu/tag/02PZ)
* [Stacks Project, Tag 02Q4](https://stacks.math.columbia.edu/tag/02Q4)
* [Stacks Project, Tag 0GSZ](https://stacks.math.columbia.edu/tag/0GSZ)
-/

@[expose] public noncomputable section

open IsLocalRing Module.FiniteLength AlgebraicGeometry

universe u v

namespace Stacks.Chow

/-! ### Elements avoiding all maximal ideals but one -/

section Coprime

variable {B : Type v} [CommRing B]

/-- An element outside the maximal ideal `𝔮` is coprime to an element lying in no other maximal
ideal. -/
theorem isCoprime_of_notMem_of_forall_ne (q : MaximalSpectrum B) {s t : B}
    (hs : s ∉ q.asIdeal) (ht : ∀ q' : MaximalSpectrum B, q' ≠ q → t ∉ q'.asIdeal) :
    IsCoprime s t := by
  rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq]
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  have hsm : s ∈ m := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self s))
  have htm : t ∈ m := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self t))
  by_cases hmq : (⟨m, hm⟩ : MaximalSpectrum B) = q
  · exact hs (by rw [← hmq]; exact hsm)
  · exact ht _ hmq htm

/-- Two elements, each lying in no maximal ideal but its own, for two different maximal ideals,
are coprime. -/
theorem isCoprime_of_forall_ne_of_forall_ne {q q' : MaximalSpectrum B} (hne : q ≠ q') {s t : B}
    (hs : ∀ q'' : MaximalSpectrum B, q'' ≠ q → s ∉ q''.asIdeal)
    (ht : ∀ q'' : MaximalSpectrum B, q'' ≠ q' → t ∉ q''.asIdeal) : IsCoprime s t :=
  isCoprime_of_notMem_of_forall_ne q' (hs q' (Ne.symm hne)) ht

end Coprime

/-! ### The principal quotient at the only maximal ideal containing its generator -/

section QuotientLocalization

variable (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  (q : MaximalSpectrum B) {t : B}

/-- The localization map `B / tB → B_𝔮 / t B_𝔮`. -/
def quotientLocalizationAlgHom (t : B) :
    (B ⧸ Ideal.span {t}) →ₐ[A]
      (Localization.AtPrime q.asIdeal ⧸
        Ideal.span {algebraMap B (Localization.AtPrime q.asIdeal) t}) :=
  Ideal.quotientMapₐ _ (IsScalarTower.toAlgHom A B (Localization.AtPrime q.asIdeal)) (by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self _))

/-- If `t` lies in no maximal ideal other than `𝔮`, the localization map `B / tB → B_𝔮 / t B_𝔮`
is bijective: every element outside `𝔮` already acts invertibly on `B / tB`. -/
theorem quotientLocalizationAlgHom_bijective
    (ht : ∀ q' : MaximalSpectrum B, q' ≠ q → t ∉ q'.asIdeal) :
    Function.Bijective (quotientLocalizationAlgHom A q t) := by
  set Bq := Localization.AtPrime q.asIdeal
  have hdvd : ∀ {c b : B}, c ∉ q.asIdeal → t ∣ b * c → t ∣ b := fun hc h ↦
    (isCoprime_of_notMem_of_forall_ne q hc ht).symm.dvd_of_dvd_mul_right h
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hb : algebraMap B Bq b ∈ Ideal.map (algebraMap B Bq) (Ideal.span {t}) := by
      rw [Ideal.map_span, Set.image_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
      exact hz
    obtain ⟨⟨⟨i, hi⟩, c⟩, hic⟩ := (IsLocalization.mem_map_algebraMap_iff
      q.asIdeal.primeCompl Bq).mp hb
    rw [← map_mul, IsLocalization.eq_iff_exists q.asIdeal.primeCompl Bq] at hic
    obtain ⟨d, hd⟩ := hic
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    refine hdvd (c := (d : B) * c) (Submonoid.mul_mem _ d.2 c.2) ?_
    have h' : b * ((d : B) * c) = d * i := by rw [← hd]; ring
    rw [h']
    exact Dvd.dvd.mul_left (Ideal.mem_span_singleton.mp hi) _
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl z
    simp only at hbc
    subst hbc
    obtain ⟨x, y, hxy⟩ := isCoprime_of_notMem_of_forall_ne q c.2 ht
    refine ⟨Ideal.Quotient.mk _ (b * x), ?_⟩
    change Ideal.Quotient.mk _ (algebraMap B Bq (b * x)) = _
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    refine ⟨-(algebraMap B Bq b * algebraMap B Bq y *
      IsLocalization.mk' Bq (1 : B) c), ?_⟩
    have h1 := IsLocalization.mk'_spec Bq (1 : B) c
    have h2 := congrArg (algebraMap B Bq) hxy
    rw [map_one] at h1
    simp only [map_add, map_mul, map_one] at h2
    rw [IsLocalization.mk'_eq_mul_mk'_one (S := Bq) b c, map_mul]
    linear_combination (algebraMap B Bq b * algebraMap B Bq x) * h1 +
      (-(algebraMap B Bq b * IsLocalization.mk' Bq (1 : B) c)) * h2

/-- The localization map `B / tB ≃ B_𝔮 / t B_𝔮`, for `t` lying in no maximal ideal other than
`𝔮`. -/
def quotientLocalizationAlgEquiv (ht : ∀ q' : MaximalSpectrum B, q' ≠ q → t ∉ q'.asIdeal) :
    (B ⧸ Ideal.span {t}) ≃ₐ[A]
      (Localization.AtPrime q.asIdeal ⧸
        Ideal.span {algebraMap B (Localization.AtPrime q.asIdeal) t}) :=
  AlgEquiv.ofBijective _ (quotientLocalizationAlgHom_bijective A q ht)

end QuotientLocalization

/-! ### The determinant of a multiplication on `B / tB` -/

section Determinant

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]

omit [IsNoetherianRing A] in
/-- **The residue-field determinant of multiplication by `s` on `B / tB`**, for `t` lying in no
maximal ideal other than `𝔮` and `s` outside `𝔮`, is `Norm_{κ(𝔮)/κ(𝔪)}(s̄)^{m}` with
`m = length_{B_𝔮}(B_𝔮 / t B_𝔮)`. -/
theorem determinantAutomorphism_singletonQuotientMulEquiv_eq_norm_pow (q : MaximalSpectrum B)
    {t s : B} (ht : ∀ q' : MaximalSpectrum B, q' ≠ q → t ∉ q'.asIdeal) (hs : s ∉ q.asIdeal)
    (h : IsCoprime t s) (hL : IsFiniteLength A (singletonQuotient B t)) :
    letI := Stacks.Length.isLocalHom_algebraMap_localization (A := A) q
    (determinantAutomorphism (singletonQuotientMulEquiv (R := A) t s h) hL : ResidueField A) =
      Algebra.norm (ResidueField A)
          (residue (Localization.AtPrime q.asIdeal)
            (algebraMap B (Localization.AtPrime q.asIdeal) s)) ^
        (Ring.ord (Localization.AtPrime q.asIdeal)
          (algebraMap B (Localization.AtPrime q.asIdeal) t)).toNat := by
  let := Stacks.Length.isLocalHom_algebraMap_localization (A := A) q
  let := Stacks.Length.finite_residueField A q
  set Bq := Localization.AtPrime q.asIdeal
  let Φ := quotientLocalizationAlgEquiv A q ht
  let φ := Φ.toLinearEquiv
  have hu : IsUnit (algebraMap B Bq s) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff Bq q.asIdeal s).mpr hs
  have hL' : IsFiniteLength A (Bq ⧸ Ideal.span {algebraMap B Bq t}) :=
    hL.of_surjective (f := φ.toLinearMap) φ.surjective
  have hM' : IsFiniteLength Bq (Bq ⧸ Ideal.span {algebraMap B Bq t}) := by
    obtain ⟨hn, ha⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hL'
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_of_tower A hn, isArtinian_of_tower A ha⟩
  let e : (Bq ⧸ Ideal.span {algebraMap B Bq t}) ≃ₗ[A] (Bq ⧸ Ideal.span {algebraMap B Bq t}) :=
    (LinearEquiv.smulOfUnit hu.unit).restrictScalars A
  rw [determinantAutomorphism_eq_of_linearEquiv _ e φ ?_ hL hL']
  · exact determinantAutomorphism_eq_norm_pow_length A Bq hu.unit _ hM' e (fun _ ↦ rfl) hL'
  · intro x
    rw [singletonQuotientMulEquiv_apply]
    change Φ (Ideal.Quotient.mk _ s * x) = (algebraMap B Bq s) • Φ x
    rw [map_mul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    rfl

end Determinant

/-! ### The symbol `d^A_B` on the nonzerodivisors of a finite algebra -/

section AlgebraSymbol

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]
  (hdim : Module.supportDim A B = 1)

/-- **The symbol `d^A_B(x, y)`** of two nonzerodivisors of a finite `A`-algebra of support
dimension one: the periodic determinant over `A` of the two-periodic complex `(B/xyB, x, y)`. -/
def regularAlgebraSymbol (x y : nonZeroDivisors B) : (ResidueField A)ˣ :=
  finiteAlgebraSymbol (R := A) (x : B) (y : B) (isRegular_iff_mem_nonZeroDivisors.mpr x.2)
    (isRegular_iff_mem_nonZeroDivisors.mpr y.2)
    (isFiniteLength_singletonQuotient hdim ((x : B) * y)
      ((isRegular_iff_mem_nonZeroDivisors.mpr x.2).mul (isRegular_iff_mem_nonZeroDivisors.mpr y.2)))

/-- The symbol `d^A_B` is multiplicative in its second argument. -/
theorem regularAlgebraSymbol_mul_right (x y z : nonZeroDivisors B) :
    regularAlgebraSymbol A hdim x (y * z) =
      regularAlgebraSymbol A hdim x y * regularAlgebraSymbol A hdim x z :=
  finiteAlgebraSymbol_mul_right (R := A) (x : B) (y : B) (z : B) _ _ _ _ _ _

/-- The symbol `d^A_B` is antisymmetric. -/
theorem regularAlgebraSymbol_swap (x y : nonZeroDivisors B) :
    regularAlgebraSymbol A hdim x y * regularAlgebraSymbol A hdim y x = 1 :=
  finiteAlgebraSymbol_swap (R := A) hdim (x : B) (y : B) _ _ _ _

/-- The symbol `d^A_B` is multiplicative in its first argument. -/
theorem regularAlgebraSymbol_mul_left (x y z : nonZeroDivisors B) :
    regularAlgebraSymbol A hdim (x * y) z =
      regularAlgebraSymbol A hdim x z * regularAlgebraSymbol A hdim y z := by
  rw [eq_inv_of_mul_eq_one_left (regularAlgebraSymbol_swap A hdim (x * y) z),
    regularAlgebraSymbol_mul_right,
    eq_inv_of_mul_eq_one_left (regularAlgebraSymbol_swap A hdim x z),
    eq_inv_of_mul_eq_one_left (regularAlgebraSymbol_swap A hdim y z), mul_inv]

/-- For two coprime nonzerodivisors, `d^A_B(x, y)` is the ratio of the residue-field determinants
of multiplication by `y` on `B/xB` and by `x` on `B/yB`. -/
theorem regularAlgebraSymbol_eq_of_isCoprime (x y : nonZeroDivisors B)
    (h : IsCoprime (x : B) (y : B)) :
    regularAlgebraSymbol A hdim x y =
      (determinantAutomorphism (singletonQuotientMulEquiv (R := A) (x : B) (y : B) h)
        (isFiniteLength_singletonQuotient hdim _ (isRegular_iff_mem_nonZeroDivisors.mpr x.2)))⁻¹ *
      determinantAutomorphism (singletonQuotientMulEquiv (R := A) (y : B) (x : B) h.symm)
        (isFiniteLength_singletonQuotient hdim _ (isRegular_iff_mem_nonZeroDivisors.mpr y.2)) :=
  finiteAlgebraSymbol_of_isCoprime _ _ _ _ h _ _ _

/-- The symbol `d^A_B(x, x)` is the sign `(-1)^{length_A(B/xB)}`. -/
theorem regularAlgebraSymbol_self (x : nonZeroDivisors B) :
    regularAlgebraSymbol A hdim x x =
      (-1 : (ResidueField A)ˣ) ^ moduleLength A (singletonQuotient B (x : B)) :=
  finiteAlgebraSymbol_self (R := A) (x : B) _ _

/-- The symbol `d^A_B` of two units is `1`. -/
theorem regularAlgebraSymbol_of_isUnit (x y : nonZeroDivisors B) (hx : IsUnit (x : B))
    (hy : IsUnit (y : B)) : regularAlgebraSymbol A hdim x y = 1 := by
  rw [regularAlgebraSymbol_eq_of_isCoprime A hdim x y (isCoprime_of_isUnit_left hx _),
    determinantAutomorphism_singletonQuotientMulEquiv_of_isUnit _ _ _ _ hx,
    determinantAutomorphism_singletonQuotientMulEquiv_of_isUnit _ _ _ _ hy, inv_one, one_mul]

end AlgebraSymbol

/-! ### The product of the symbols of the local rings of a finite algebra -/

section LocalProduct

variable {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B] [Algebra A B]

/-- A nonzerodivisor of `B` stays a nonzerodivisor in each localization at a maximal ideal. -/
def toLocalizationNonZeroDivisors (q : MaximalSpectrum B) :
    nonZeroDivisors B →* nonZeroDivisors (Localization.AtPrime q.asIdeal) where
  toFun x := ⟨algebraMap B _ x,
    IsLocalization.map_nonZeroDivisors_le q.asIdeal.primeCompl _ ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

@[simp]
theorem coe_toLocalizationNonZeroDivisors (q : MaximalSpectrum B) (x : nonZeroDivisors B) :
    (toLocalizationNonZeroDivisors q x : Localization.AtPrime q.asIdeal) =
      algebraMap B _ (x : B) := rfl

variable [Fintype (MaximalSpectrum B)]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
  [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
  (hdimq : ∀ q : MaximalSpectrum B, ringKrullDim (Localization.AtPrime q.asIdeal) = 1)

variable (A) in
/-- **The product of the norms of the local symbols**: for nonzerodivisors `x, y` of `B`,
`∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}(d_{B_𝔮}(x, y))`, the product over the maximal ideals of `B` of the norms
of the symbols of Stacks 02PZ of the one-dimensional local rings `B_𝔮`. -/
def localSymbolProduct (x y : nonZeroDivisors B) : (ResidueField A)ˣ :=
  ∏ q : MaximalSpectrum B,
    Units.map (Algebra.norm (ResidueField A) :
        ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
      (regularModuleSymbol (hdimq q) (toLocalizationNonZeroDivisors q x)
        (toLocalizationNonZeroDivisors q y))

variable (A) in
/-- The product of the local symbols is multiplicative in its first argument. -/
theorem localSymbolProduct_mul_left (x x' y : nonZeroDivisors B) :
    localSymbolProduct A hdimq (x * x') y =
      localSymbolProduct A hdimq x y * localSymbolProduct A hdimq x' y := by
  simp only [localSymbolProduct, map_mul, regularModuleSymbol_mul_left, Finset.prod_mul_distrib]

variable (A) in
/-- The product of the local symbols is multiplicative in its second argument. -/
theorem localSymbolProduct_mul_right (x y y' : nonZeroDivisors B) :
    localSymbolProduct A hdimq x (y * y') =
      localSymbolProduct A hdimq x y * localSymbolProduct A hdimq x y' := by
  simp only [localSymbolProduct, map_mul, regularModuleSymbol_mul_right, Finset.prod_mul_distrib]

variable (A) in
/-- The product of the local symbols is antisymmetric. -/
theorem localSymbolProduct_swap (x y : nonZeroDivisors B) :
    localSymbolProduct A hdimq x y * localSymbolProduct A hdimq y x = 1 := by
  simp only [localSymbolProduct, ← Finset.prod_mul_distrib, ← map_mul, regularModuleSymbol_swap,
    map_one, Finset.prod_const_one]

end LocalProduct

/-! ### Two bimultiplicative pairings agreeing on generators -/

/-- Two pairings on a monoid with values in a commutative group, multiplicative in each argument,
agree on the submonoid generated by a set as soon as they agree on that set. -/
theorem eq_of_mem_closure_of_mul {M G : Type*} [Monoid M] [CommGroup G] (D F : M → M → G)
    (hDl : ∀ a b c, D (a * b) c = D a c * D b c) (hDr : ∀ a b c, D a (b * c) = D a b * D a c)
    (hFl : ∀ a b c, F (a * b) c = F a c * F b c) (hFr : ∀ a b c, F a (b * c) = F a b * F a c)
    (S : Set M) (h : ∀ a ∈ S, ∀ b ∈ S, D a b = F a b) {a b : M}
    (ha : a ∈ Submonoid.closure S) (hb : b ∈ Submonoid.closure S) : D a b = F a b := by
  have hD1 : ∀ c, D 1 c = 1 := fun c ↦ by simpa using hDl 1 1 c
  have hF1 : ∀ c, F 1 c = 1 := fun c ↦ by simpa using hFl 1 1 c
  have hD1' : ∀ c, D c 1 = 1 := fun c ↦ by simpa using hDr c 1 1
  have hF1' : ∀ c, F c 1 = 1 := fun c ↦ by simpa using hFr c 1 1
  have key : ∀ a ∈ S, ∀ b ∈ Submonoid.closure S, D a b = F a b := by
    intro a ha b hb
    induction hb using Submonoid.closure_induction with
    | mem b hb => exact h a ha b hb
    | one => rw [hD1', hF1']
    | mul b c _ _ hb hc => rw [hDr, hFr, hb, hc]
  induction ha using Submonoid.closure_induction with
  | mem a ha => exact key a ha b hb
  | one => rw [hD1, hF1]
  | mul a c _ _ ha hc => rw [hDl, hFl, ha, hc]

/-! ### The comparison on generators -/

section Generators

/-- The symbol of Stacks 02PZ of a unit against any nonzerodivisor of a one-dimensional local
ring: `d(u, b) = ū^{ord(b)}` (Stacks 0EAN). -/
theorem coe_regularModuleSymbol_of_isUnit_left {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (hd : ringKrullDim R = 1) (a b : nonZeroDivisors R) (ha : IsUnit (a : R)) :
    (regularModuleSymbol hd a b : ResidueField R) =
      residue R (a : R) ^ (Ring.ord R (b : R)).toNat := by
  rw [regularModuleSymbol_unit_left hd a b ha.unit ha.unit_spec.symm]
  simp

/-- The symbol of Stacks 02PZ of two units is `1`. -/
theorem regularModuleSymbol_eq_one_of_isUnit {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (hd : ringKrullDim R = 1) (a b : nonZeroDivisors R) (ha : IsUnit (a : R))
    (hb : IsUnit (b : R)) : regularModuleSymbol hd a b = 1 := by
  rw [regularModuleSymbol_unit_left hd a b ha.unit ha.unit_spec.symm, Ring.ord_of_isUnit hb]
  simp

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]
  (hdim : Module.supportDim A B = 1)
  [Fintype (MaximalSpectrum B)]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
  [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
  (hdimq : ∀ q : MaximalSpectrum B, ringKrullDim (Localization.AtPrime q.asIdeal) = 1)
  (t : MaximalSpectrum B → nonZeroDivisors B)
  (ht : ∀ q q' : MaximalSpectrum B, q' ≠ q → (t q : B) ∉ q'.asIdeal)

omit [Fintype (MaximalSpectrum B)]
  [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)] in
include ht in
/-- The image of a global parameter `t_𝔮` is a unit at every other maximal ideal. -/
theorem isUnit_algebraMap_globalParameter {q q' : MaximalSpectrum B} (hne : q' ≠ q) :
    IsUnit (algebraMap B (Localization.AtPrime q'.asIdeal) (t q : B)) :=
  (IsLocalization.AtPrime.isUnit_to_map_iff _ q'.asIdeal _).mpr (ht q q' hne)

/-- If `d^A_B` agrees with the product of the local symbols on `(x, y)`, it does on `(y, x)`. -/
theorem regularAlgebraSymbol_eq_localSymbolProduct_swap {x y : nonZeroDivisors B}
    (h : regularAlgebraSymbol A hdim x y = localSymbolProduct A hdimq x y) :
    regularAlgebraSymbol A hdim y x = localSymbolProduct A hdimq y x := by
  rw [eq_inv_of_mul_eq_one_left (regularAlgebraSymbol_swap A hdim y x),
    eq_inv_of_mul_eq_one_left (localSymbolProduct_swap A hdimq y x), h]

/-- On two units, `d^A_B` and the product of the local symbols are both `1`. -/
theorem regularAlgebraSymbol_eq_localSymbolProduct_of_isUnit (x y : nonZeroDivisors B)
    (hx : IsUnit (x : B)) (hy : IsUnit (y : B)) :
    regularAlgebraSymbol A hdim x y = localSymbolProduct A hdimq x y := by
  rw [regularAlgebraSymbol_of_isUnit A hdim x y hx hy, localSymbolProduct]
  refine (Finset.prod_eq_one fun q _ ↦ ?_).symm
  rw [regularModuleSymbol_eq_one_of_isUnit _ _ _ (hx.map (algebraMap B _))
    (hy.map (algebraMap B _)), map_one]

include ht in
/-- On a unit and a global parameter, `d^A_B` and the product of the local symbols agree: both are
`Norm_{κ(𝔮)/κ(𝔪)}(ū)^{m_𝔮}`. -/
theorem regularAlgebraSymbol_eq_localSymbolProduct_of_isUnit_left (u : nonZeroDivisors B)
    (hu : IsUnit (u : B)) (q : MaximalSpectrum B) :
    regularAlgebraSymbol A hdim u (t q) = localSymbolProduct A hdimq u (t q) := by
  have huq : (u : B) ∉ q.asIdeal := fun h ↦ q.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  apply Units.ext
  rw [regularAlgebraSymbol_eq_of_isCoprime A hdim u (t q) (isCoprime_of_isUnit_left hu _),
    determinantAutomorphism_singletonQuotientMulEquiv_of_isUnit _ _ _ _ hu, inv_one, one_mul,
    determinantAutomorphism_singletonQuotientMulEquiv_eq_norm_pow q (ht q) huq, localSymbolProduct,
    Fintype.prod_eq_single q fun q' hq' ↦ by
      rw [regularModuleSymbol_eq_one_of_isUnit _ _ _ (hu.map _)
        (isUnit_algebraMap_globalParameter t ht hq'), map_one],
    Units.coe_map, coe_regularModuleSymbol_of_isUnit_left _ _ _ (hu.map (algebraMap B _)),
    map_pow]
  rfl

include ht in
/-- On a global parameter against itself, `d^A_B` and the product of the local symbols agree:
both are the sign `(-1)^{[κ(𝔮) : κ(𝔪)] m_𝔮}`. -/
theorem regularAlgebraSymbol_eq_localSymbolProduct_self (q : MaximalSpectrum B) :
    regularAlgebraSymbol A hdim (t q) (t q) = localSymbolProduct A hdimq (t q) (t q) := by
  set Bq := Localization.AtPrime q.asIdeal
  let := Stacks.Length.finite_residueField A q
  have hlen : moduleLength A (singletonQuotient B (t q : B)) =
      Module.finrank (ResidueField A) (ResidueField Bq) *
        (Ring.ord Bq (algebraMap B Bq (t q : B))).toNat := by
    have hL := isFiniteLength_singletonQuotient hdim (t q : B)
      (isRegular_iff_mem_nonZeroDivisors.mpr (t q).2)
    let φ := (quotientLocalizationAlgEquiv A q (ht q)).toLinearEquiv
    have hL' : IsFiniteLength A (Bq ⧸ Ideal.span {algebraMap B Bq (t q : B)}) :=
      hL.of_surjective (f := φ.toLinearMap) φ.surjective
    have hM' : Module.length Bq (Bq ⧸ Ideal.span {algebraMap B Bq (t q : B)}) ≠ ⊤ := by
      obtain ⟨hn, ha⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hL'
      exact Module.length_ne_top_iff.mpr (isFiniteLength_iff_isNoetherian_isArtinian.mpr
        ⟨isNoetherian_of_tower A hn, isArtinian_of_tower A ha⟩)
    change (Module.length A (singletonQuotient B (t q : B))).toNat = _
    rw [φ.length_eq, Stacks.Length.length_restrictScalars_eq_finrank_mul q _ hM', ENat.toNat_mul,
      ENat.toNat_natCast]
    rfl
  apply Units.ext
  rw [regularAlgebraSymbol_self, hlen, localSymbolProduct,
    Fintype.prod_eq_single q fun q' hq' ↦ by
      rw [regularModuleSymbol_eq_one_of_isUnit _ _ _ (isUnit_algebraMap_globalParameter t ht hq')
        (isUnit_algebraMap_globalParameter t ht hq'), map_one],
    regularModuleSymbol_self, map_pow, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    Units.coe_map, Units.val_neg, Units.val_one, Units.val_neg, Units.val_one,
    coe_toLocalizationNonZeroDivisors,
    show (-1 : ResidueField Bq) = algebraMap (ResidueField A) (ResidueField Bq) (-1) by simp,
    Algebra.norm_algebraMap, pow_mul]

include ht in
/-- On two global parameters at different maximal ideals, `d^A_B` and the product of the local
symbols agree. -/
theorem regularAlgebraSymbol_eq_localSymbolProduct_of_ne {q q' : MaximalSpectrum B} (hne : q ≠ q') :
    regularAlgebraSymbol A hdim (t q) (t q') = localSymbolProduct A hdimq (t q) (t q') := by
  have hcop : IsCoprime (t q : B) (t q' : B) :=
    isCoprime_of_forall_ne_of_forall_ne hne (fun q'' h ↦ ht q q'' h) (fun q'' h ↦ ht q' q'' h)
  have hq'q : (t q' : B) ∉ q.asIdeal := ht q' q hne
  have hqq' : (t q : B) ∉ q'.asIdeal := ht q q' (Ne.symm hne)
  apply Units.ext
  rw [regularAlgebraSymbol_eq_of_isCoprime A hdim (t q) (t q') hcop, Units.val_mul,
    Units.val_inv_eq_inv_val,
    determinantAutomorphism_singletonQuotientMulEquiv_eq_norm_pow q (ht q) hq'q,
    determinantAutomorphism_singletonQuotientMulEquiv_eq_norm_pow q' (ht q') hqq',
    localSymbolProduct, Fintype.prod_eq_mul q q' hne fun q'' ⟨h1, h2⟩ ↦ by
      rw [regularModuleSymbol_eq_one_of_isUnit _ _ _ (isUnit_algebraMap_globalParameter t ht h1)
        (isUnit_algebraMap_globalParameter t ht h2), map_one],
    eq_inv_of_mul_eq_one_left (regularModuleSymbol_swap (hdimq q) _ _), map_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, Units.coe_map, Units.coe_map,
    coe_regularModuleSymbol_of_isUnit_left _ _ _ (isUnit_algebraMap_globalParameter t ht hne),
    coe_regularModuleSymbol_of_isUnit_left _ _ _ (isUnit_algebraMap_globalParameter t ht
      (Ne.symm hne)),
    map_pow, map_pow]
  rfl

include ht in
/-- **`d^A_B` is the product of the local symbols on the submonoid generated by the units of `B`
and the global parameters.** -/
theorem regularAlgebraSymbol_eq_localSymbolProduct_of_mem_closure {x y : nonZeroDivisors B}
    (hx : x ∈ Submonoid.closure ({u : nonZeroDivisors B | IsUnit (u : B)} ∪ Set.range t))
    (hy : y ∈ Submonoid.closure ({u : nonZeroDivisors B | IsUnit (u : B)} ∪ Set.range t)) :
    regularAlgebraSymbol A hdim x y = localSymbolProduct A hdimq x y := by
  refine eq_of_mem_closure_of_mul _ _ (regularAlgebraSymbol_mul_left A hdim)
    (regularAlgebraSymbol_mul_right A hdim) (localSymbolProduct_mul_left A hdimq)
    (localSymbolProduct_mul_right A hdimq) _ ?_ hx hy
  rintro a (ha | ⟨q, rfl⟩) b (hb | ⟨q', rfl⟩)
  · exact regularAlgebraSymbol_eq_localSymbolProduct_of_isUnit hdim hdimq a b ha hb
  · exact regularAlgebraSymbol_eq_localSymbolProduct_of_isUnit_left hdim hdimq t ht a ha q'
  · exact regularAlgebraSymbol_eq_localSymbolProduct_swap hdim hdimq
      (regularAlgebraSymbol_eq_localSymbolProduct_of_isUnit_left hdim hdimq t ht b hb q)
  · by_cases hqq : q = q'
    · subst hqq
      exact regularAlgebraSymbol_eq_localSymbolProduct_self hdim hdimq t ht q
    · exact regularAlgebraSymbol_eq_localSymbolProduct_of_ne hdim hdimq t ht hqq

end Generators

/-! ### Global parameters -/

section GlobalParameter

/-- In a one-dimensional Noetherian local ring a power of the maximal ideal lies in the ideal
generated by any nonzerodivisor. -/
theorem exists_maximalIdeal_pow_le_span {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [Ring.KrullDimLE 1 R] {π : R} (hπ : π ∈ nonZeroDivisors R) :
    ∃ n : ℕ, maximalIdeal R ^ n ≤ Ideal.span {π} := by
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun J ⟨hJ, hJp⟩ ↦ ?_
  have : J.IsPrime := hJp
  rw [Stacks.Length.eq_maximalIdeal_of_mem_of_isPrime J hπ (hJ (Ideal.mem_span_singleton_self π))]

variable {B : Type v} [CommRing B] [Finite (MaximalSpectrum B)]

/-- **A global parameter.** Given a maximal ideal `𝔮` of a ring with finitely many maximal ideals
and a nonzerodivisor `π` of the one-dimensional Noetherian local ring `B_𝔮`, there is `t ∈ B`
lying in no other maximal ideal whose image in `B_𝔮` is a unit multiple of `π`: approximate `π`
modulo a high power of `𝔮` and `1` modulo the other maximal ideals. -/
theorem exists_globalParameter (q : MaximalSpectrum B)
    [IsNoetherianRing (Localization.AtPrime q.asIdeal)]
    [Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)] {π : Localization.AtPrime q.asIdeal}
    (hπ : π ∈ nonZeroDivisors (Localization.AtPrime q.asIdeal)) :
    ∃ t : B, (∀ q' : MaximalSpectrum B, q' ≠ q → t ∉ q'.asIdeal) ∧
      ∃ w : (Localization.AtPrime q.asIdeal)ˣ, algebraMap B _ t = π * w := by
  classical
  let := Fintype.ofFinite (MaximalSpectrum B)
  obtain ⟨⟨b, c⟩, hbc⟩ :=
    IsLocalization.mk'_surjective q.asIdeal.primeCompl (S := (Localization.AtPrime q.asIdeal)) π
  simp only at hbc
  have hcu : IsUnit (algebraMap B (Localization.AtPrime q.asIdeal) c) :=
    IsLocalization.map_units (Localization.AtPrime q.asIdeal) c
  have hb : algebraMap B (Localization.AtPrime q.asIdeal) b =
      π * algebraMap B (Localization.AtPrime q.asIdeal) c := by
    rw [← IsLocalization.mk'_spec (Localization.AtPrime q.asIdeal) b c]
    exact congrArg (· * algebraMap B (Localization.AtPrime q.asIdeal) c) hbc
  have hbreg : algebraMap B (Localization.AtPrime q.asIdeal) b ∈
      nonZeroDivisors (Localization.AtPrime q.asIdeal) := by
    rw [hb]
    exact mul_mem hπ hcu.mem_nonZeroDivisors
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_span hbreg
  have := q.isMaximal
  have hcop : IsCoprime (q.asIdeal ^ (N + 1)) (∏ q' ∈ Finset.univ.erase q, q'.asIdeal) :=
    IsCoprime.prod_right fun q' hq' ↦ by
      have := q'.isMaximal
      exact (Ideal.isCoprime_of_isMaximal fun h ↦
        (Finset.ne_of_mem_erase hq') (MaximalSpectrum.ext h).symm).pow_left
  obtain ⟨i₁, hi₁, i₂, hi₂, hsum⟩ := Ideal.isCoprime_iff_exists.mp hcop
  refine ⟨b * i₂ + i₁, fun q' hq' hmem ↦ ?_, ?_⟩
  · have hi₂q' : i₂ ∈ q'.asIdeal :=
      (Finset.inf_le (f := fun q'' : MaximalSpectrum B ↦ q''.asIdeal)
        (Finset.mem_erase.mpr ⟨hq', Finset.mem_univ _⟩) : _ ≤ q'.asIdeal) (Ideal.prod_le_inf hi₂)
    apply q'.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : B) = (b * i₂ + i₁) - b * i₂ + i₂ := by rw [← hsum]; ring
    rw [h1]
    exact q'.asIdeal.add_mem (q'.asIdeal.sub_mem hmem (q'.asIdeal.mul_mem_left _ hi₂q')) hi₂q'
  · have hi₁' : algebraMap B (Localization.AtPrime q.asIdeal) i₁ ∈
        maximalIdeal (Localization.AtPrime q.asIdeal) *
          maximalIdeal (Localization.AtPrime q.asIdeal) ^ N := by
      have h := Ideal.mem_map_of_mem (algebraMap B (Localization.AtPrime q.asIdeal)) hi₁
      rwa [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal, pow_succ'] at h
    have hi₁'' : algebraMap B (Localization.AtPrime q.asIdeal) i₁ ∈
        Ideal.span {algebraMap B (Localization.AtPrime q.asIdeal) b} *
          maximalIdeal (Localization.AtPrime q.asIdeal) := by
      rw [mul_comm]
      exact Ideal.mul_mono_right hN hi₁'
    obtain ⟨μ, hμ, hμeq⟩ := Ideal.mem_span_singleton_mul.mp hi₁''
    have hi₁m : algebraMap B (Localization.AtPrime q.asIdeal) i₁ ∈
        maximalIdeal (Localization.AtPrime q.asIdeal) := by
      rw [← hμeq]
      exact Ideal.mul_mem_left _ _ hμ
    have hv : IsUnit (algebraMap B (Localization.AtPrime q.asIdeal) i₂ + μ) := by
      have h2 : algebraMap B (Localization.AtPrime q.asIdeal) i₂ + μ =
          1 - (algebraMap B (Localization.AtPrime q.asIdeal) i₁ - μ) := by
        rw [← map_one (algebraMap B (Localization.AtPrime q.asIdeal)), ← hsum, map_add]
        ring
      rw [h2]
      exact isUnit_one_sub_self_of_mem_nonunits _
        ((mem_maximalIdeal _).mp
          ((maximalIdeal (Localization.AtPrime q.asIdeal)).sub_mem hi₁m hμ))
    refine ⟨hcu.unit * hv.unit, ?_⟩
    rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, map_add, map_mul, ← hμeq, hb]
    ring

omit [Finite (MaximalSpectrum B)] in
/-- An element whose image in the localization at every maximal ideal is a nonzerodivisor is a
nonzerodivisor. -/
theorem mem_nonZeroDivisors_of_forall_localization {t : B}
    (h : ∀ q : MaximalSpectrum B,
      algebraMap B (Localization.AtPrime q.asIdeal) t ∈ nonZeroDivisors _) :
    t ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff_right]
  intro z hz
  have : Ideal.span {z} = ⊥ := ideal_eq_bot_of_localization' _ fun P hP ↦ by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_bot]
    exact (mul_right_mem_nonZeroDivisors_eq_zero_iff (h ⟨P, hP⟩)).mp
      (by rw [← map_mul, hz, map_zero])
  exact Ideal.span_singleton_eq_bot.mp this

omit [Finite (MaximalSpectrum B)] in
/-- **A nonzerodivisor which is, at every maximal ideal `𝔮`, a unit multiple of `t_𝔮^{e_𝔮}`**, the
`t_𝔮` lying in no other maximal ideal, is a unit of `B` times `∏_𝔮 t_𝔮^{e_𝔮}`: the two generate
the same ideal at every maximal ideal. -/
theorem exists_isUnit_mul_prod_globalParameter [Fintype (MaximalSpectrum B)]
    (t : MaximalSpectrum B → B) (ht : ∀ q q' : MaximalSpectrum B, q' ≠ q → t q ∉ q'.asIdeal)
    (e : MaximalSpectrum B → ℕ) {a : B} (ha : a ∈ nonZeroDivisors B)
    (hloc : ∀ q : MaximalSpectrum B, ∃ u : (Localization.AtPrime q.asIdeal)ˣ,
      algebraMap B (Localization.AtPrime q.asIdeal) a =
        (u : Localization.AtPrime q.asIdeal) *
          algebraMap B (Localization.AtPrime q.asIdeal) (t q) ^ e q) :
    ∃ U : B, IsUnit U ∧ a = U * ∏ q, t q ^ e q := by
  classical
  have hspan : Ideal.span {a} = Ideal.span {∏ q, t q ^ e q} :=
    Ideal.eq_of_localization_maximal fun P hP ↦ by
      let q : MaximalSpectrum B := ⟨P, hP⟩
      rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
      obtain ⟨u, hu⟩ := hloc q
      have hrest : IsUnit (∏ q' ∈ Finset.univ \ {q},
          algebraMap B (Localization.AtPrime q.asIdeal) (t q') ^ e q') :=
        Finset.prod_induction _ IsUnit (fun _ _ ↦ IsUnit.mul) isUnit_one fun q' hq' ↦
          ((IsLocalization.AtPrime.isUnit_to_map_iff _ q.asIdeal _).mpr
            (ht q' q fun h ↦ (Finset.mem_sdiff.mp hq').2 (Finset.mem_singleton.mpr h.symm))).pow _
      have hw : algebraMap B (Localization.AtPrime q.asIdeal) (∏ q, t q ^ e q) =
          (∏ q' ∈ Finset.univ \ {q}, algebraMap B (Localization.AtPrime q.asIdeal) (t q') ^ e q') *
            algebraMap B _ (t q) ^ e q := by
        rw [map_prod, Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ q), mul_comm]
        simp only [map_pow]
      change Ideal.span {algebraMap B (Localization.AtPrime q.asIdeal) a} =
        Ideal.span {algebraMap B (Localization.AtPrime q.asIdeal) (∏ q, t q ^ e q)}
      rw [hu, hw, Ideal.span_singleton_mul_left_unit u.isUnit,
        Ideal.span_singleton_mul_left_unit hrest]
  obtain ⟨U, hU⟩ := Ideal.mem_span_singleton'.mp (hspan ▸ Ideal.mem_span_singleton_self a)
  obtain ⟨V, hV⟩ := Ideal.mem_span_singleton'.mp
    (hspan.symm ▸ Ideal.mem_span_singleton_self (∏ q, t q ^ e q))
  have h0 : (U * V - 1) * a = 0 := by
    calc (U * V - 1) * a = U * (V * a) - a := by ring
      _ = 0 := by rw [hV, hU, sub_self]
  have hUV : U * V = 1 := sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff ha).mp h0)
  exact ⟨U, IsUnit.of_mul_eq_one V hUV, hU.symm⟩

end GlobalParameter

/-! ### The comparison -/

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- A faithful algebra over a one-dimensional local ring has support dimension one. -/
theorem supportDim_eq_one_of_injective {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]
    (hdim : ringKrullDim A = 1) (hinj : Function.Injective (algebraMap A B)) :
    Module.supportDim A B = 1 := by
  have he : Module.annihilator A B = Module.annihilator A A := by
    ext a
    simp only [Module.mem_annihilator]
    refine ⟨fun h b ↦ ?_, fun h c ↦ ?_⟩
    · have h1 := h 1
      rw [Algebra.smul_def, mul_one] at h1
      rw [smul_eq_mul, hinj (h1.trans (map_zero _).symm), zero_mul]
    · rw [show a = 0 by simpa using h 1, zero_smul]
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator, he,
    ← Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    Module.supportDim_self_eq_ringKrullDim, hdim]

/-- **Stacks 02Q4 for a finite modification.** For a finite extension `A ⊆ B` with `B/A` killed
by a power of `𝔪`, the symbol `d_A(x, y)` of Stacks 02PZ is the symbol `d^A_B(x, y)` computed on
the finite `A`-module `B`. -/
theorem regularModuleSymbol_eq_regularAlgebraSymbol {B : Type v} [CommRing B] [Algebra A B]
    [Module.Finite A B] (hdim : ringKrullDim A = 1) (hinj : Function.Injective (algebraMap A B))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    (hdimB : Module.supportDim A B = 1) (x y : nonZeroDivisors A)
    (hx : algebraMap A B (x : A) ∈ nonZeroDivisors B)
    (hy : algebraMap A B (y : A) ∈ nonZeroDivisors B) {z : A} (hzm : z ∈ maximalIdeal A)
    (hz : algebraMap A B z ∈ nonZeroDivisors B) :
    regularModuleSymbol hdim x y = regularAlgebraSymbol A hdimB ⟨_, hx⟩ ⟨_, hy⟩ := by
  have hsm : ∀ {c : A}, algebraMap A B c ∈ nonZeroDivisors B → IsSMulRegular B c :=
    fun hc a b h ↦ (isRegular_iff_mem_nonZeroDivisors.mpr hc).left
      (by simpa only [Algebra.smul_def] using h)
  have hker : Module.supportDim A (LinearMap.ker (Algebra.linearMap A B)) ≤ 0 := by
    rw [LinearMap.ker_eq_bot.mpr hinj, Module.supportDim_eq_bot_of_subsingleton]
    exact bot_le
  have hcoker : Module.supportDim A (B ⧸ LinearMap.range (Algebra.linearMap A B)) ≤ 0 := by
    obtain ⟨n, hn⟩ := hquot
    have hzn : algebraMap A B (z ^ n) ∈ nonZeroDivisors B := by
      rw [map_pow]
      exact pow_mem hz n
    have hL := (Module.isFiniteLength_quotient_range_of_injective
      (LinearMap.lsmul A B (z ^ n)) (hsm hzn) hdimB).of_surjective
      (f := Submodule.mapQ _ (LinearMap.range (Algebra.linearMap A B))
        LinearMap.id (by
          rintro _ ⟨w, rfl⟩
          exact hn (Submodule.smul_mem_smul (Ideal.pow_mem_pow hzm n) Submodule.mem_top)))
      fun w ↦ Submodule.Quotient.induction_on _ w fun w ↦ ⟨Submodule.Quotient.mk w, rfl⟩
    nontriviality (B ⧸ LinearMap.range (Algebra.linearMap A B))
    rw [Module.supportDim, support_of_isFiniteLength hL]
    exact Order.krullDim_nonpos_of_subsingleton
  rw [regularModuleSymbol_eq_moduleSymbol hdim x y
      (isRegular_iff_mem_nonZeroDivisors.mpr x.2).isSMulRegular
      (isRegular_iff_mem_nonZeroDivisors.mpr y.2).isSMulRegular
      ((Module.supportDim_self_eq_ringKrullDim A).trans hdim),
    moduleSymbol_eq_of_ker_coker_supportDim_le_zero (Algebra.linearMap A B) x y _ _ (hsm hx)
      (hsm hy) _ hdimB hker hcoker,
    moduleSymbol_eq_finiteAlgebraSymbol hdimB x y (hsm hx) (hsm hy)
      (isRegular_iff_mem_nonZeroDivisors.mpr hx) (isRegular_iff_mem_nonZeroDivisors.mpr hy)]
  rfl

/-- **The tame symbol of Stacks 0EAQ is the symbol of Stacks 02PZ.** For a one-dimensional
Noetherian local ring `A` and nonzerodivisors `x, y` of `A`,

`d_A(x, y) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}((-1)^{e_𝔮 f_𝔮} ū_𝔮^{f_𝔮} v̄_𝔮^{-e_𝔮})^{m_𝔮}`,

the right-hand side being the recipe of Stacks 0EAQ (`Stacks.Chow.tameSymbolValue`) and the
left-hand side the periodic determinant `det_κ(A/xyA, x, y)` of Stacks 02PZ. -/
theorem regularModuleSymbol_eq_tameSymbolValue (hdim : ringKrullDim A = 1)
    (x y : nonZeroDivisors A) : regularModuleSymbol hdim x y = tameSymbolValue x y := by
  by_cases hu : IsUnit (x : A) ∧ IsUnit (y : A)
  · rw [tameSymbolValue_eq_one_of_isUnit hu.1 hu.2,
      regularModuleSymbol_eq_one_of_isUnit hdim x y hu.1 hu.2]
  have hnu : ¬ ∀ i, IsUnit (![(x : A), (y : A)] i) := fun h ↦
    hu ⟨by simpa using h 0, by simpa using h 1⟩
  obtain ⟨B, _, _, ⟨P⟩⟩ := exists_tameSymbolPreparation_of_ringKrullDim_eq_one (le_refl 2)
    ![(x : A), (y : A)]
    (fun k ↦ by fin_cases k <;> simpa using isRegular_iff_mem_nonZeroDivisors.mpr (by simp))
    hnu hdim
  let := P.finite
  let : Finite (MaximalSpectrum B) := P.finite_maximalSpectrum
  let : Fintype (MaximalSpectrum B) := @Fintype.ofFinite _ P.finite_maximalSpectrum
  let : ∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) :=
    P.isLocalHom
  let : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (by simpa using hdim.le)
  let : ∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal) := fun q ↦
    isNoetherianRing_localization_of_moduleFinite (A := A) q
  let : ∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal) := fun q ↦
    krullDimLE_one_localization_of_moduleFinite (A := A) q
  have hxB : algebraMap A B (x : A) ∈ nonZeroDivisors B := by
    simpa using P.algebraMap_mem_nonZeroDivisors 0
  have hyB : algebraMap A B (y : A) ∈ nonZeroDivisors B := by
    simpa using P.algebraMap_mem_nonZeroDivisors 1
  obtain ⟨z, hzm, hzB⟩ : ∃ z : A, z ∈ maximalIdeal A ∧ algebraMap A B z ∈ nonZeroDivisors B := by
    by_cases hx : IsUnit (x : A)
    · exact ⟨y, (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun h ↦ hu ⟨hx, h⟩), hyB⟩
    · exact ⟨x, (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hx), hxB⟩
  have hdimq : ∀ q : MaximalSpectrum B, ringKrullDim (Localization.AtPrime q.asIdeal) = 1 :=
    fun q ↦ ringKrullDim_localization_eq_one_of_nonZeroDivisor (A := A) hzm hzB q
  have hdimB : Module.supportDim A B = 1 :=
    supportDim_eq_one_of_injective hdim P.algebraMap_injective
  rw [tameSymbolValue_eq_symbolValue hdim P 0 1 x y (by simp) (by simp),
    regularModuleSymbol_eq_regularAlgebraSymbol hdim P.algebraMap_injective
      P.quotient_annihilated_by_maximalIdeal_power hdimB x y hxB hyB hzm hzB]
  -- global parameters at the maximal ideals of `B`
  choose t ht w hw using fun q : MaximalSpectrum B ↦ exists_globalParameter q
    (isRegular_iff_mem_nonZeroDivisors.mp (P.parameter_isRegular q.asIdeal))
  have htreg : ∀ q, t q ∈ nonZeroDivisors B := fun q ↦
    mem_nonZeroDivisors_of_forall_localization fun q' ↦ by
      by_cases hq : q' = q
      · subst hq
        rw [hw]
        exact mul_mem (isRegular_iff_mem_nonZeroDivisors.mp (P.parameter_isRegular q'.asIdeal))
          (w q').isUnit.mem_nonZeroDivisors
      · exact ((IsLocalization.AtPrime.isUnit_to_map_iff _ q'.asIdeal _).mpr
          (ht q q' hq)).mem_nonZeroDivisors
  let T : MaximalSpectrum B → nonZeroDivisors B := fun q ↦ ⟨t q, htreg q⟩
  have hmem : ∀ i : Fin 2, (⟨algebraMap A B (![(x : A), (y : A)] i),
      P.algebraMap_mem_nonZeroDivisors i⟩ : nonZeroDivisors B) ∈
      Submonoid.closure ({u : nonZeroDivisors B | IsUnit (u : B)} ∪ Set.range T) := fun i ↦ by
    obtain ⟨U, hU, hUeq⟩ := exists_isUnit_mul_prod_globalParameter t ht
      (fun q ↦ P.exponent q.asIdeal i) (P.algebraMap_mem_nonZeroDivisors i) fun q ↦
        ⟨P.factorUnit q.asIdeal i * (w q)⁻¹ ^ P.exponent q.asIdeal i, by
          rw [P.factorization, hw q, mul_pow, Units.val_mul,
            Units.val_pow_eq_pow_val]
          calc _ = (P.factorUnit q.asIdeal i : Localization.AtPrime q.asIdeal) *
                P.parameter q.asIdeal ^ P.exponent q.asIdeal i *
                (((w q)⁻¹ : (Localization.AtPrime q.asIdeal)ˣ) * (w q)) ^
                  P.exponent q.asIdeal i := by rw [Units.inv_mul, one_pow, mul_one]
            _ = _ := by ring⟩
    have heq : (⟨algebraMap A B (![(x : A), (y : A)] i), P.algebraMap_mem_nonZeroDivisors i⟩ :
        nonZeroDivisors B) = ⟨U, hU.mem_nonZeroDivisors⟩ * ∏ q, T q ^ P.exponent q.asIdeal i :=
      Subtype.ext (by simp [hUeq, T])
    rw [heq]
    have hT : ∀ q, T q ∈
        Submonoid.closure ({u : nonZeroDivisors B | IsUnit (u : B)} ∪ Set.range T) := fun q ↦
      Submonoid.subset_closure (Or.inr (Set.mem_range_self q))
    exact mul_mem (Submonoid.subset_closure (Or.inl hU))
      (prod_mem fun q _ ↦ pow_mem (hT q) _)
  have hxmem : (⟨_, hxB⟩ : nonZeroDivisors B) ∈
      Submonoid.closure ({u : nonZeroDivisors B | IsUnit (u : B)} ∪ Set.range T) := by
    simpa using hmem 0
  have hymem : (⟨_, hyB⟩ : nonZeroDivisors B) ∈
      Submonoid.closure ({u : nonZeroDivisors B | IsUnit (u : B)} ∪ Set.range T) := by
    simpa using hmem 1
  rw [regularAlgebraSymbol_eq_localSymbolProduct_of_mem_closure hdimB hdimq T
    (fun q q' h ↦ ht q q' h) hxmem hymem, localSymbolProduct]
  refine Finset.prod_congr rfl fun q _ ↦ congrArg _ ?_
  exact tameSymbol_apply_eq_of_tameSymbolPreparation P q.asIdeal
    (regularTameSymbolOfKrullDimOne (hdimq q)) 0 1 _ _
    (by simp [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q.asIdeal)])
    (by simp [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q.asIdeal)])

/-- **The tame symbol of Stacks 0EAH on nonzerodivisors given by the recipe of Stacks 0EAQ is the
symbol of Stacks 02PZ**, as tame symbols on nonzerodivisors. -/
theorem regularTameSymbolOfKrullDimOne_eq_formulaRegularTameSymbol (hdim : ringKrullDim A = 1) :
    regularTameSymbolOfKrullDimOne hdim = formulaRegularTameSymbol hdim := by
  unfold regularTameSymbolOfKrullDimOne formulaRegularTameSymbol
  congr 1
  funext x y
  exact regularModuleSymbol_eq_tameSymbolValue hdim x y

/-- **The tame symbol of Stacks 0EAQ on `Q(A)^*` is the extension of the symbol of Stacks
02PZ**: `Stacks.Chow.formulaTameSymbol`, the map `∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*` that the
recipe of Stacks 0EAQ defines, is `Stacks.Chow.tameSymbolOfKrullDimOne`. -/
theorem tameSymbolOfKrullDimOne_eq_formulaTameSymbol (hdim : ringKrullDim A = 1) (Q : Type*)
    [CommRing Q] [Algebra A Q] [IsFractionRing A Q] :
    tameSymbolOfKrullDimOne hdim Q = formulaTameSymbol hdim Q := by
  unfold tameSymbolOfKrullDimOne formulaTameSymbol
  rw [regularTameSymbolOfKrullDimOne_eq_formulaRegularTameSymbol hdim]

end Main

end Stacks.Chow

end
