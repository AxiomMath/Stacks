module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.TwoPeriodic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Comparison
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicLengthDeterminantFormula
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Multiplicativity
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.PeriodicExactness
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.ReciprocityCommon
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.TameSymbol
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Unit
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.FiniteLength
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reciprocity for the tame symbol on a two-dimensional local domain

Let `A` be a two-dimensional Noetherian local domain with fraction field `K`. Every height-one
prime `𝔮` of `A` has one-dimensional localization `A_𝔮`, so it carries a tame symbol on `Kˣ`
with values in the units of the residue field of `𝔮`. Taking the order of vanishing of that
value along `A / 𝔮` gives an integer at each height-one prime, and these integers sum to zero.

## Main definitions

* `AlgebraicGeometry.localTameSymbol` is the tame symbol of two units of the fraction field at a
  height-one prime, a unit of the residue field of that prime.

## Main results

* `AlgebraicGeometry.localTameSymbol_ne_one_finite`: the tame symbol is trivial at all but
  finitely many height-one primes.
* `AlgebraicGeometry.sum_ord_localTameSymbol_eq_zero`: the orders of the tame symbols at the
  height-one primes sum to zero.

## Implementation notes

The fraction field is an arbitrary realization `K`, transported to `FractionRing A` to form the
local symbols. The sum is a `finsum` over all height-one primes; at a prime where both
arguments are units of `A_𝔮` the symbol is trivial, so this agrees with the sum over the
finitely many primes at which one of the two arguments fails to be a local unit. The
one-dimensionality of each quotient `A / 𝔮`, needed to speak of the order of vanishing, is a
consequence of the hypotheses and so appears as an existential in the conclusion.

Multiplicativity of the symbol and additivity of the order reduce the statement to a pair of
nonzero elements `a, b` of `A`. There the sum of orders of periodic determinants on the
localizations of `A / (ab)` is minus the multiplicity of the two-periodic complex given by
multiplication by `a` and by `b` on `A / (ab)`, and that complex is exact, so the multiplicity
vanishes.

## References

* [Stacks Project, Tag 02QJ](https://stacks.math.columbia.edu/tag/02QJ)
* [K. Kato, *Milnor K-theory and the Chow group of zero cycles*, Proposition 1]
-/

@[expose] public section

noncomputable section

namespace AlgebraicGeometry

universe u v

/-- At a prime, the periodic determinant of multiplication by `a` and by `b` on the localization
of `A / (ab)` is the symbol of the images of `a` and `b` in the localized ring. -/
private theorem periodicDeterminant_localized_quotient_eq_moduleSymbol
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {q : PrimeSpectrum A} [q.1.IsPrime] (a b : A) (_hab : a * b ≠ 0)
    (hdim : ringKrullDim (Localization.AtPrime q.1) = 1)
    (haR : IsSMulRegular (Localization.AtPrime q.1)
      (algebraMap A (Localization.AtPrime q.1) a))
    (hbR : IsSMulRegular (Localization.AtPrime q.1)
      (algebraMap A (Localization.AtPrime q.1) b))
    (hfinite : IsFiniteLength (Localization.AtPrime q.1)
      (LocalizedModule q.1.primeCompl (A ⧸ Ideal.span {a * b})))
    (hexactab : Function.Exact
      (LocalizedModule.map q.1.primeCompl
        (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) a))
      (LocalizedModule.map q.1.primeCompl
        (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) b)))
    (hexactba : Function.Exact
      (LocalizedModule.map q.1.primeCompl
        (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) b))
      (LocalizedModule.map q.1.primeCompl
        (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) a))) :
    periodicDeterminant
      (LocalizedModule.map q.1.primeCompl
        (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) a))
      (LocalizedModule.map q.1.primeCompl
        (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) b))
      hexactab hexactba hfinite =
    AlgebraicGeometry.moduleSymbol (M := Localization.AtPrime q.1)
      (algebraMap A (Localization.AtPrime q.1) a)
      (algebraMap A (Localization.AtPrime q.1) b) haR hbR
      ((Module.supportDim_self_eq_ringKrullDim _).trans hdim) := by
  let R := Localization.AtPrime q.1
  let M := A ⧸ Ideal.span {a * b}
  let p := q.1.primeCompl
  let φR : R →ₗ[R] R := LinearMap.lsmul R R (algebraMap A R a)
  let ψR : R →ₗ[R] R := LinearMap.lsmul R R (algebraMap A R b)
  have hcomm : LinearMap.range (φR.comp ψR) = LinearMap.range (ψR.comp φR) := by
    apply congrArg LinearMap.range
    ext
    simp [φR, ψR, LinearMap.comp_apply, LinearMap.lsmul_apply]
    ring
  let Q := R ⧸ LinearMap.range (φR.comp ψR)
  let Iq : Ideal R := Ideal.span {algebraMap A R (a * b)}
  have hmap : (Ideal.span {a * b} : Ideal A).map (algebraMap A R) = Iq := by
    rw [Ideal.map_span]
    simp [Iq, map_mul]
  have hrange : LinearMap.range (φR.comp ψR) = Iq := by
    simpa [Iq, φR, ψR, LinearMap.lsmul_apply, map_mul] using
      (range_mul_lsmul_eq_span (algebraMap A R a) (algebraMap A R b))
  let eRange : Q ≃ₗ[R] R ⧸ Iq :=
    Submodule.Quotient.equiv _ _ (LinearEquiv.refl R R) (by
      simpa [Submodule.map_id] using hrange)
  let e0 : LocalizedModule p M ≃ₗ[R]
      R ⧸ (Ideal.span {a * b} : Ideal A).map (algebraMap A R) :=
    localizedQuotientIdealEquiv p (Ideal.span {a * b})
  have hmapid :
      Submodule.map (LinearEquiv.refl R R).toLinearMap
          (Ideal.map (algebraMap A R) (Ideal.span {a * b})) = Iq := by
    simpa [Submodule.map_id] using hmap
  let eLocalized : LocalizedModule p M ≃ₗ[R] R ⧸ Iq :=
    e0.trans (Submodule.Quotient.equiv _ _ (LinearEquiv.refl R R) hmapid)
  let e : Q ≃ₗ[R] LocalizedModule p M := eRange.trans eLocalized.symm
  have hqmk :
      (localizedQuotientEquiv p (Ideal.span {a * b})).symm
        ((LocalizedModule.mkLinearMap p M)
          ((Ideal.Quotient.mk (Ideal.span {a * b})) (1 : A))) =
      Submodule.Quotient.mk (LocalizedModule.mkLinearMap p A (1 : A)) := by
    rw [localizedQuotientEquiv]
    change (IsLocalizedModule.linearEquiv p
        ((Ideal.span {a * b}).toLocalizedQuotient p)
        (LocalizedModule.mkLinearMap p M)).symm
        ((LocalizedModule.mkLinearMap p M) (Submodule.Quotient.mk (1 : A))) = _
    rw [IsLocalizedModule.linearEquiv_symm_apply]
    rfl
  let φQ := periodicQuotientPhi φR ψR hcomm
  let ψQ := periodicQuotientPsi φR ψR hcomm
  have hφψQ : Function.Exact φQ ψQ :=
    AlgebraicGeometry.exact_periodicQuotient_phi_psi φR ψR hbR hcomm
  have hψφQ : Function.Exact ψQ φQ :=
    AlgebraicGeometry.exact_periodicQuotient_psi_phi φR ψR haR hcomm
  have hMQ : IsFiniteLength R Q :=
    Module.isFiniteLength_quotient_range_of_injective
      (φR.comp ψR) (haR.comp hbR)
      ((Module.supportDim_self_eq_ringKrullDim R).trans hdim)
  have hlocal : eLocalized (LocalizedModule.mkLinearMap p M
      (Submodule.Quotient.mk (1 : A))) = Submodule.Quotient.mk (1 : R) := by
    dsimp [eLocalized, e0, localizedQuotientIdealEquiv]
    rw [hqmk, Submodule.mapQ_apply]
    simp only [localizedRingModuleEquiv, LocalizedModule.mkLinearMap_apply,
      LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LocalizedModule.equivTensorProduct_apply_mk, LinearEquiv.ofBijective_apply,
      LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.rid_tmul, one_smul,
      Ideal.Quotient.mk_eq_mk, map_one, Iq]
    simp only [Localization.mk_one_eq_algebraMap, map_one]
    unfold Submodule.quotEquivOfEq
    rfl
  have he_one : e (Submodule.Quotient.mk (1 : R)) =
      LocalizedModule.mkLinearMap p M (Submodule.Quotient.mk (1 : A)) := by
    apply eLocalized.injective
    calc
      eLocalized (e (Submodule.Quotient.mk (1 : R))) =
          eRange (Submodule.Quotient.mk (1 : R)) := by simp [e]
      _ = Submodule.Quotient.mk (1 : R) := by
        dsimp [eRange]
        rfl
      _ = eLocalized (LocalizedModule.mkLinearMap p M
          (Submodule.Quotient.mk (1 : A))) := hlocal.symm
  have hr : ∀ r : R, e (Submodule.Quotient.mk r) = r • e (Submodule.Quotient.mk (1 : R)) := by
    intro r
    have hmk' : (Submodule.Quotient.mk r : Q) =
        r • (Submodule.Quotient.mk (1 : R) : Q) := by
      simpa using (Submodule.Quotient.mk_smul (φR.comp ψR).range r (1 : R))
    rw [hmk', e.map_smul]
  have hmul : ∀ (c : A) (r : R), e (Submodule.Quotient.mk ((algebraMap A R c) * r)) =
      LocalizedModule.map p (LinearMap.lsmul A M c) (e (Submodule.Quotient.mk r)) := by
    intro c r
    have hmk : Submodule.Quotient.mk ((algebraMap A R c) * r) =
        (algebraMap A R c) • (Submodule.Quotient.mk r : Q) := by
      simpa only [smul_eq_mul] using
        (Submodule.Quotient.mk_smul (φR.comp ψR).range (algebraMap A R c) r)
    rw [hmk, e.map_smul, hr, he_one, map_smul]
    simp only [LocalizedModule.mkLinearMap_apply]
    rw [LocalizedModule.map_mk]
    simp [LinearMap.lsmul_apply, LocalizedModule.smul'_mk, algebraMap_smul, smul_comm]
  have hφ : ∀ x : Q, e (φQ x) =
      LocalizedModule.map p (LinearMap.lsmul A M a) (e x) := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ r =>
      change e (Submodule.Quotient.mk ((algebraMap A R a) * r)) = _
      exact hmul a r
  have hψ : ∀ x : Q, e (ψQ x) =
      LocalizedModule.map p (LinearMap.lsmul A M b) (e x) := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ r =>
      change e (Submodule.Quotient.mk ((algebraMap A R b) * r)) = _
      exact hmul b r
  have hsymbol : AlgebraicGeometry.moduleSymbol (M := R)
      (algebraMap A R a) (algebraMap A R b) haR hbR
      ((Module.supportDim_self_eq_ringKrullDim R).trans hdim) =
      periodicDeterminant φQ ψQ hφψQ hψφQ hMQ := by
    unfold AlgebraicGeometry.moduleSymbol
    rfl
  exact (periodicDeterminant_eq_of_linearEquiv φQ ψQ hφψQ hψφQ
    (LocalizedModule.map p (LinearMap.lsmul A M a))
    (LocalizedModule.map p (LinearMap.lsmul A M b))
    hexactab hexactba e (LinearMap.ext hφ) (LinearMap.ext hψ)
    hMQ hfinite).symm.trans hsymbol

/-- On `A / (ab)` the kernel of multiplication by `b` is the image of multiplication by `a`. -/
private theorem exact_mul_quotient_ab
    {A : Type u} [CommRing A] [IsDomain A]
    (a b : A) (hb : b ≠ 0) :
    Function.Exact
      (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) a)
      (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) b) := by
  intro x
  constructor
  · intro hx
    induction x using Submodule.Quotient.induction_on with
    | _ z =>
      rw [LinearMap.lsmul_apply] at hx
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)
      have hzw : z = a * w := mul_left_cancel₀ hb (hw.trans (by ring))
      refine ⟨Submodule.Quotient.mk w, ?_⟩
      rw [LinearMap.lsmul_apply, hzw]
      change (algebraMap A (A ⧸ Ideal.span {a * b}) a) *
          (Ideal.Quotient.mk (Ideal.span {a * b}) w) = _
      rw [Ideal.Quotient.algebraMap_eq]
      exact (map_mul (Ideal.Quotient.mk (Ideal.span {a * b})) a w).symm
  · rintro ⟨y, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | _ z =>
      rw [LinearMap.lsmul_apply, LinearMap.lsmul_apply]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [Ideal.mem_span_singleton]
      exact ⟨z, by ring⟩

/-- On `A / (ab)` the kernel of multiplication by `a` is the image of multiplication by `b`. -/
private theorem exact_mul_quotient_ab_reverse
    {A : Type u} [CommRing A] [IsDomain A]
    (a b : A) (ha : a ≠ 0) :
    Function.Exact
      (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) b)
      (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) a) := by
  have h := exact_mul_quotient_ab b a ha
  rwa [mul_comm b a] at h

/-- The tame symbol of a one-dimensional Noetherian local domain is trivial on a pair of units
of the ring. -/
private theorem tameSymbol_of_units_eq_one
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (hdim : ringKrullDim R = 1) (x y : Rˣ) :
    AlgebraicGeometry.tameSymbol (K := K) hdim
      (IsLocalization.map_units K
        ⟨(x : R), x.isUnit.mem_nonZeroDivisors⟩).unit
      (IsLocalization.map_units K
        ⟨(y : R), y.isUnit.mem_nonZeroDivisors⟩).unit = 1 := by
  apply Units.ext
  calc
    _ = ((AlgebraicGeometry.moduleSymbol (M := R) (x : R) (y : R)
          (Units.isSMulRegular R x) (Units.isSMulRegular R y)
          ((Module.supportDim_self_eq_ringKrullDim R).trans hdim) :
          (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R) :=
      congrArg Units.val <| (AlgebraicGeometry.tameSymbol (K := K) hdim).eq_moduleSymbol
        (x : R) (y : R)
        (isRegular_iff_mem_nonZeroDivisors.mpr x.isUnit.mem_nonZeroDivisors)
        (isRegular_iff_mem_nonZeroDivisors.mpr y.isUnit.mem_nonZeroDivisors)
    _ = IsLocalRing.residue R x ^ (Ring.ord R (y : R)).toNat :=
      AlgebraicGeometry.moduleSymbol_unit_left_ring x y
        (Units.isSMulRegular R y) hdim
    _ = 1 := by simp

/-- The tame symbol of two units of the fraction field at a height-one prime `𝔮`, a unit of the
residue field of `𝔮`, formed from the one-dimensional local domain `A_𝔮`. -/
noncomputable def localTameSymbol {A : Type u} {K : Type v}
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsNoetherianRing A] (q : {q : Ideal A // q.IsPrime ∧ q.height = 1})
    (f g : Kˣ) :
    letI : q.1.IsPrime := q.2.1
    q.1.ResidueFieldˣ := by
  letI : q.1.IsPrime := q.2.1
  have hdim : ringKrullDim (Localization.AtPrime q.1) = 1 :=
    (IsLocalization.AtPrime.ringKrullDim_eq_height q.1 (Localization.AtPrime q.1)).trans
      (congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) q.2.2)
  let e := (FractionRing.algEquiv A K).symm.toRingHom.toMonoidHom
  exact AlgebraicGeometry.tameSymbol (A := Localization.AtPrime q.1)
    (K := FractionRing A) hdim (Units.map e f) (Units.map e g)

/-- The localization of a ring at a height-one prime has Krull dimension one. -/
private theorem ringKrullDim_atPrime_heightOne {A : Type u} [CommRing A]
    (q : {q : Ideal A // q.IsPrime ∧ q.height = 1}) [q.1.IsPrime] :
    ringKrullDim (Localization.AtPrime q.1) = 1 :=
  (IsLocalization.AtPrime.ringKrullDim_eq_height q.1 _).trans
    (congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) q.2.2)

/-- The tame symbol at a height-one prime is trivial on two fractions that admit numerators and
denominators outside that prime. -/
private theorem localTameSymbol_eq_one_of_fraction_rep
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (q : {q : Ideal A // q.IsPrime ∧ q.height = 1})
    [q.1.IsPrime]
    (a b c d : A) (ha : a ∉ q.1) (hb : b ∉ q.1)
    (hc : c ∉ q.1) (hd : d ∉ q.1) (f g : Kˣ)
    (hf : (f : K) = algebraMap A K a / algebraMap A K b)
    (hg : (g : K) = algebraMap A K c / algebraMap A K d) :
    localTameSymbol q f g = 1 := by
  let : q.1.IsPrime := q.2.1
  let R := Localization.AtPrime q.1
  let e := (FractionRing.algEquiv A K).symm
  have hunit : ∀ (a b : A) (ha : a ∉ q.1) (hb : b ∉ q.1) (f : Kˣ),
      (f : K) = algebraMap A K a / algebraMap A K b →
      ∃ x : Rˣ, Units.map e.toRingEquiv.toMonoidHom f =
        (IsLocalization.map_units (FractionRing A)
          ⟨(x : R), x.isUnit.mem_nonZeroDivisors⟩).unit := by
    intro a b ha hb f hf
    let ua : Rˣ := (IsLocalization.map_units (M := q.1.primeCompl) R ⟨a, ha⟩).unit
    let ub : Rˣ := (IsLocalization.map_units (M := q.1.primeCompl) R ⟨b, hb⟩).unit
    have hmap : ∀ u : Rˣ, ∀ c : A, (u : R) = algebraMap A R c →
        algebraMap R (FractionRing A) (u : R) = algebraMap A (FractionRing A) c := fun u c hu => by
      rw [hu, IsScalarTower.algebraMap_apply A R (FractionRing A) c]
    refine ⟨ua / ub, Units.ext ?_⟩
    change e (f : K) = algebraMap R (FractionRing A) ((ua * ub⁻¹ : Rˣ) : R)
    rw [hf, map_div₀, e.commutes, e.commutes, Units.val_mul, map_mul, hmap ua a rfl,
      map_units_inv, hmap ub b rfl, div_eq_mul_inv]
  obtain ⟨x, hxf⟩ := hunit a b ha hb f hf
  obtain ⟨y, hyg⟩ := hunit c d hc hd g hg
  change AlgebraicGeometry.tameSymbol
    (A := Localization.AtPrime q.1) (K := FractionRing A) (ringKrullDim_atPrime_heightOne q)
    (Units.map e.toRingEquiv.toMonoidHom f)
    (Units.map e.toRingEquiv.toMonoidHom g) = 1
  rw [hxf, hyg]
  exact tameSymbol_of_units_eq_one _ x y

/-- A minimal prime of the ideal generated by a nonzero nonunit of a Noetherian domain has
height one. -/
private theorem height_eq_one_of_mem_minimalPrimes_span
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {a : A} (ha0 : a ≠ 0) (hau : ¬ IsUnit a) {p : Ideal A}
    (hp : p ∈ (Ideal.span {a}).minimalPrimes) : p.height = 1 := by
  have : p.IsPrime := hp.isPrime
  have hI : (Ideal.span {a}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha0) hau
  refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp)
    (hI.symm.le.trans ?_)
  rw [Ideal.height_eq_inf_minimalPrimes]
  exact iInf₂_le p hp

/-- A height-one prime containing a nonzero element is a minimal prime of the ideal that element
generates. -/
@[ega "0 16.3.1" "special case"]
private theorem heightOne_mem_minimalPrimes_span
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (a : A) (ha0 : a ≠ 0)
    (q : {q : Ideal A // q.IsPrime ∧ q.height = 1}) (haq : a ∈ q.1) :
    q.1 ∈ (Ideal.span {a}).minimalPrimes := by
  let : q.1.IsPrime := q.2.1
  by_cases hau : IsUnit a
  · exact (q.2.1.ne_top (Ideal.eq_top_of_isUnit_mem q.1 haq hau)).elim
  · obtain ⟨p, hp, hpI⟩ := Ideal.exists_minimalPrimes_le
      (q.1.span_singleton_le_iff_mem.mpr haq)
    let : p.IsPrime := hp.isPrime
    have hpq : p = q.1 :=
      p.eq_of_le_of_height_le hpI
        (by simp [q.2.2, height_eq_one_of_mem_minimalPrimes_span ha0 hau hp])
    exact hpq ▸ hp

/-- A nonzero element of a Noetherian domain lies in only finitely many height-one primes. -/
private theorem finite_heightOne_primes_containing
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (a : A) (ha0 : a ≠ 0) :
    Set.Finite {q : {q : Ideal A // q.IsPrime ∧ q.height = 1} | a ∈ q.1} := by
  refine Set.Finite.of_finite_image
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})).subset ?_)
    Subtype.val_injective.injOn
  rintro p ⟨q, hq, rfl⟩
  exact heightOne_mem_minimalPrimes_span a ha0 q hq

/-- The quotient of a two-dimensional Noetherian local domain by a height-one prime has Krull
dimension at most one. -/
private theorem quotient_heightOne_krullDimLE
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 2)
    (q : Ideal A) [q.IsPrime] (hq : q.height = 1) :
    Ring.KrullDimLE 1 (A ⧸ q) := by
  rw [Ring.krullDimLE_one_iff]
  intro J hJ
  let p := J.comap (Ideal.Quotient.mk q)
  have hp : p.IsPrime := hJ.comap (Ideal.Quotient.mk q)
  have hqp : q ≤ p := by
    intro x hx
    change Ideal.Quotient.mk q x ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact J.zero_mem
  by_cases hJbot : J = ⊥
  · left
    rw [IsDomain.minimalPrimes_eq_singleton_bot (A ⧸ q)]
    simp [hJbot]
  · right
    have hne : p ≠ q := by
      intro heq
      apply hJbot
      apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk q)
        Ideal.Quotient.mk_surjective
      calc
        J.comap (Ideal.Quotient.mk q) = q := by simpa [p] using heq
        _ = (⊥ : Ideal (A ⧸ q)).comap (Ideal.Quotient.mk q) := Ideal.mk_ker.symm
    have hqp' : q < p := lt_of_le_of_ne hqp (ne_comm.mp hne)
    have hplt : q.height < p.height :=
      Ideal.height_strict_mono_of_isPrime_of_isPrime hqp'
    have hp_le : p.height ≤ ringKrullDim A := Ideal.height_le_ringKrullDim_of_isPrime
    have hpeq : p.height = ringKrullDim A := by
      have hpgeE : (2 : ℕ∞) ≤ p.height := by
        cases hheight : p.height with
        | top => simp
        | coe n =>
          have hn' : 1 < n := by
            have := hplt
            rw [hq, hheight] at this
            exact_mod_cast this
          have hn2 : 2 ≤ n := by omega
          exact_mod_cast hn2
      have hpge : (2 : WithBot ℕ∞) ≤ p.height :=
        WithBot.coe_le_coe.mpr hpgeE
      rw [hdim]
      exact le_antisymm (by simpa [hdim] using hp_le) hpge
    have hfinite : FiniteRingKrullDim A := by
      rw [finiteRingKrullDim_iff_ne_bot_and_top, hdim]
      refine ⟨by norm_num, ?_⟩
      exact ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top 2))
    let := hfinite
    have hpmax : p = IsLocalRing.maximalIdeal A :=
      (Ideal.height_eq_ringKrullDim_iff).mp hpeq
    let : Nontrivial (A ⧸ q) := Ideal.Quotient.nontrivial_iff.mpr
      (show q ≠ ⊤ from (inferInstance : q.IsPrime).ne_top)
    let : IsLocalRing (A ⧸ q) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
    let : IsLocalHom (Ideal.Quotient.mk q) :=
      IsLocalHom.of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
    have hJmax : J = IsLocalRing.maximalIdeal (A ⧸ q) := by
      apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk q)
        Ideal.Quotient.mk_surjective
      change p = (IsLocalRing.maximalIdeal (A ⧸ q)).comap (Ideal.Quotient.mk q)
      rw [hpmax, IsLocalRing.maximalIdeal_comap]
    simpa [hJmax] using (IsLocalRing.maximalIdeal.isMaximal (A ⧸ q))

/-- For two nonunits with nonzero product in a two-dimensional Noetherian local domain, the
quotient by the ideal generated by their product has support of dimension one. -/
private theorem quotient_principal_supportDim_one
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 2) (a b : A)
    (hab0 : a * b ≠ 0) (ha : ¬ IsUnit a) (_hb : ¬ IsUnit b) :
    Module.supportDim A (A ⧸ Ideal.span {a * b}) = 1 := by
  have haM : a ∈ IsLocalRing.maximalIdeal A := by
    by_contra h
    exact ha (IsLocalRing.notMem_maximalIdeal.mp h)
  have habM : a * b ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.maximalIdeal A).mul_mem_right b haM
  have hdrop : ringKrullDim (A ⧸ Ideal.span {a * b}) + 1 = ringKrullDim A :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hab0) habM
  have hdimQ : ringKrullDim (A ⧸ Ideal.span {a * b}) = 1 := by
    have htwo : ringKrullDim A = (1 : WithBot ℕ∞) + 1 := by
      rw [hdim]
      norm_num
    have h' : ringKrullDim (A ⧸ Ideal.span {a * b}) + 1 = 1 + 1 :=
      hdrop.trans htwo
    exact ENat.WithBot.add_one_cancel.mp h'
  rw [Module.supportDim_quotient_eq_ringKrullDim]
  exact hdimQ

/-- The order of vanishing along `A / 𝔮` of a unit of the residue field of a height-one prime
`𝔮`, as an integer. -/
private noncomputable def localSymbolOrder
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    {q : {q : Ideal A // q.IsPrime ∧ q.height = 1}} [hqp : q.1.IsPrime]
    (hquot : Ring.KrullDimLE 1 (A ⧸ q.1))
    (d : q.1.ResidueFieldˣ) : ℤ := by
  letI := hquot
  exact Multiplicative.toAdd (WithZero.unzero
    (x := Ring.ordFrac (A ⧸ q.1) (d : q.1.ResidueField))
    ((Units.isUnit d).map (Ring.ordFrac (A ⧸ q.1))).ne_zero)

/-- The order of the trivial residue-field unit is zero. -/
private theorem localSymbolOrder_one
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    {q : {q : Ideal A // q.IsPrime ∧ q.height = 1}} [hqp : q.1.IsPrime]
    (hquot : Ring.KrullDimLE 1 (A ⧸ q.1)) :
    localSymbolOrder (q := q) hquot 1 = 0 := by
  simp only [localSymbolOrder, Ring.ordFrac, Units.val_one, map_one]
  rfl

/-- The order of a product of residue-field units is the sum of their orders. -/
private theorem localSymbolOrder_mul
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    {q : {q : Ideal A // q.IsPrime ∧ q.height = 1}} [hqp : q.1.IsPrime]
    (hquot : Ring.KrullDimLE 1 (A ⧸ q.1)) (x y : q.1.ResidueFieldˣ) :
    localSymbolOrder (q := q) hquot (x * y) =
      localSymbolOrder (q := q) hquot x + localSymbolOrder (q := q) hquot y := by
  simp [localSymbolOrder, map_mul, Units.val_mul, WithZero.unzero_mul]

/-- A nonzero element of the fraction field is a quotient of a nonzero element of the ring by a
nonzerodivisor. -/
private theorem exists_ne_zero_div_eq
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {x : K} (hx : x ≠ 0) :
    ∃ a b : A, a ≠ 0 ∧ b ∈ nonZeroDivisors A ∧ algebraMap A K a / algebraMap A K b = x := by
  obtain ⟨a, b, hb, h⟩ := IsFractionRing.div_surjective A x
  refine ⟨a, b, ?_, hb, h⟩
  rintro rfl
  simp at h
  exact hx h.symm

/-- **Stacks Project, Tag 02QJ.** Two units of the fraction field have trivial tame symbol at
all but finitely many height-one primes, so the reciprocity sum below is a finite sum. -/
@[stacks 02QJ "finiteness of the set of contributing primes, which makes the sum finite"]
theorem localTameSymbol_ne_one_finite
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (f g : Kˣ) :
    Set.Finite {q : {q : Ideal A // q.IsPrime ∧ q.height = 1} |
      localTameSymbol q f g ≠ 1} := by
  classical
  obtain ⟨a, b, ha0, hb, hf⟩ := exists_ne_zero_div_eq (A := A) f.ne_zero
  obtain ⟨c, d, hc0, hd, hg⟩ := exists_ne_zero_div_eq (A := A) g.ne_zero
  let U : Set {q : Ideal A // q.IsPrime ∧ q.height = 1} :=
    {q | a ∈ q.1} ∪ {q | b ∈ q.1} ∪ {q | c ∈ q.1} ∪ {q | d ∈ q.1}
  have hU : U.Finite := by
    have hA := finite_heightOne_primes_containing a ha0
    have hB := finite_heightOne_primes_containing b
      (mem_nonZeroDivisors_iff_ne_zero.mp hb)
    have hC := finite_heightOne_primes_containing c hc0
    have hD := finite_heightOne_primes_containing d
      (mem_nonZeroDivisors_iff_ne_zero.mp hd)
    simpa [U] using ((hA.union hB).union hC).union hD
  apply hU.subset
  intro q hsupport
  by_contra hnotU
  simp only [U, Set.mem_union, not_or] at hnotU
  let : q.1.IsPrime := q.2.1
  exact hsupport (localTameSymbol_eq_one_of_fraction_rep q a b c d
    hnotU.1.1.1 hnotU.1.1.2 hnotU.1.2 hnotU.2 f g hf.symm hg.symm)

/-- The order of the tame symbol is nonzero at only finitely many height-one primes. -/
private theorem localSymbolOrder_support_finite
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hquot : ∀ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
      Ring.KrullDimLE 1 (A ⧸ q.1)) (f g : Kˣ) :
    {q : {q : Ideal A // q.IsPrime ∧ q.height = 1} |
      letI : q.1.IsPrime := q.2.1
      localSymbolOrder (q := q) (hquot q) (localTameSymbol q f g) ≠ 0}.Finite := by
  classical
  apply (localTameSymbol_ne_one_finite f g).subset
  intro q hs
  let : q.1.IsPrime := q.2.1
  intro heq
  apply hs
  rw [heq, localSymbolOrder_one (q := q) (hquot q)]

/-- The sum over all height-one primes of the orders of the local tame symbols. -/
private noncomputable def globalSymbolOrder
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hquot : ∀ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
      Ring.KrullDimLE 1 (A ⧸ q.1)) (f g : Kˣ) : ℤ :=
  ∑ᶠ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
    letI : q.1.IsPrime := q.2.1
    localSymbolOrder (q := q) (hquot q) (localTameSymbol q f g)

/-- The reciprocity sum is additive as soon as the local orders are. -/
private theorem globalSymbolOrder_add_of_local
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hquot : ∀ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
      Ring.KrullDimLE 1 (A ⧸ q.1)) (f₁ g₁ f₂ g₂ f g : Kˣ)
    (h : ∀ q : {q : Ideal A // q.IsPrime ∧ q.height = 1}, ∀ _ : q.1.IsPrime,
      localSymbolOrder (q := q) (hquot q) (localTameSymbol q f g) =
        localSymbolOrder (q := q) (hquot q) (localTameSymbol q f₁ g₁) +
          localSymbolOrder (q := q) (hquot q) (localTameSymbol q f₂ g₂)) :
    globalSymbolOrder hquot f g =
      globalSymbolOrder hquot f₁ g₁ + globalSymbolOrder hquot f₂ g₂ := by
  classical
  simp only [globalSymbolOrder]
  rw [← finsum_add_distrib (localSymbolOrder_support_finite hquot f₁ g₁)
    (localSymbolOrder_support_finite hquot f₂ g₂)]
  exact finsum_congr fun q => h q q.2.1

/-- The reciprocity sum is additive in its first argument. -/
private theorem globalSymbolOrder_mul_left
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hquot : ∀ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
      Ring.KrullDimLE 1 (A ⧸ q.1)) (f f' g : Kˣ) :
    globalSymbolOrder hquot (f * f') g =
      globalSymbolOrder hquot f g + globalSymbolOrder hquot f' g := by
  refine globalSymbolOrder_add_of_local hquot f g f' g _ _ fun q _ => ?_
  simp only [localTameSymbol, map_mul]
  rw [(AlgebraicGeometry.tameSymbol (A := Localization.AtPrime q.1)
    (K := FractionRing A) (ringKrullDim_atPrime_heightOne q)).map_mul_left,
    localSymbolOrder_mul]

/-- The reciprocity sum is additive in its second argument. -/
private theorem globalSymbolOrder_mul_right
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hquot : ∀ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
      Ring.KrullDimLE 1 (A ⧸ q.1)) (f g g' : Kˣ) :
    globalSymbolOrder hquot f (g * g') =
      globalSymbolOrder hquot f g + globalSymbolOrder hquot f g' := by
  refine globalSymbolOrder_add_of_local hquot f g f g' _ _ fun q _ => ?_
  simp only [localTameSymbol, map_mul]
  rw [(AlgebraicGeometry.tameSymbol (A := Localization.AtPrime q.1)
    (K := FractionRing A) (ringKrullDim_atPrime_heightOne q)).map_mul_right,
    localSymbolOrder_mul]

/-- The reciprocity sum vanishes when its first argument is `1`. -/
private theorem globalSymbolOrder_one_left
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hquot : ∀ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
      Ring.KrullDimLE 1 (A ⧸ q.1)) (g : Kˣ) :
    globalSymbolOrder hquot 1 g = 0 := by
  have h := globalSymbolOrder_mul_left hquot (1 : Kˣ) 1 g
  have h' : globalSymbolOrder hquot 1 g =
      globalSymbolOrder hquot 1 g + globalSymbolOrder hquot 1 g := by simpa using h
  omega

/-- Inverting the first argument negates the reciprocity sum. -/
private theorem globalSymbolOrder_inv_left
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hquot : ∀ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
      Ring.KrullDimLE 1 (A ⧸ q.1)) (f g : Kˣ) :
    globalSymbolOrder hquot f⁻¹ g = -globalSymbolOrder hquot f g := by
  have h := globalSymbolOrder_mul_left hquot f f⁻¹ g
  rw [mul_inv_cancel, globalSymbolOrder_one_left] at h
  omega

/-- The reciprocity sum vanishes when its second argument is `1`. -/
private theorem globalSymbolOrder_one_right
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hquot : ∀ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
      Ring.KrullDimLE 1 (A ⧸ q.1)) (f : Kˣ) :
    globalSymbolOrder hquot f 1 = 0 := by
  have h := globalSymbolOrder_mul_right hquot f (1 : Kˣ) 1
  have h' : globalSymbolOrder hquot f 1 =
      globalSymbolOrder hquot f 1 + globalSymbolOrder hquot f 1 := by simpa using h
  omega

/-- Inverting the second argument negates the reciprocity sum. -/
private theorem globalSymbolOrder_inv_right
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hquot : ∀ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
      Ring.KrullDimLE 1 (A ⧸ q.1)) (f g : Kˣ) :
    globalSymbolOrder hquot f g⁻¹ = -globalSymbolOrder hquot f g := by
  have h := globalSymbolOrder_mul_right hquot f g g⁻¹
  rw [mul_inv_cancel, globalSymbolOrder_one_right] at h
  omega

/-- A biadditive function of two units of the fraction field that vanishes on pairs of nonzero
elements of the ring vanishes identically. -/
private theorem globalSymbolOrder_eq_zero_of_eq_zero_on_ring
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hquot : ∀ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
      Ring.KrullDimLE 1 (A ⧸ q.1))
    (hring : ∀ a b : A, ∀ ha : a ≠ 0, ∀ hb : b ≠ 0,
      globalSymbolOrder hquot
        (IsLocalization.map_units K ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩).unit
        (IsLocalization.map_units K ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩).unit = 0) :
    ∀ f g : Kˣ, globalSymbolOrder hquot f g = 0 := by
  intro f g
  have hexpand : ∀ ua ub uc ud : Kˣ, globalSymbolOrder hquot (ua / ub) (uc / ud) =
      globalSymbolOrder hquot ua uc - globalSymbolOrder hquot ua ud -
        globalSymbolOrder hquot ub uc + globalSymbolOrder hquot ub ud := by
    intro ua ub uc ud
    rw [div_eq_mul_inv, div_eq_mul_inv, globalSymbolOrder_mul_left hquot ua (ub⁻¹) (uc * ud⁻¹),
      globalSymbolOrder_mul_right hquot ua uc (ud⁻¹),
      globalSymbolOrder_mul_right hquot (ub⁻¹) uc (ud⁻¹),
      globalSymbolOrder_inv_right hquot ua ud, globalSymbolOrder_inv_left hquot ub uc,
      globalSymbolOrder_inv_right hquot (ub⁻¹) ud, globalSymbolOrder_inv_left hquot ub ud]
    omega
  have hunit : ∀ x : Kˣ, ∃ (a b : A) (ha : a ≠ 0) (hb : b ≠ 0), x =
      (IsLocalization.map_units K ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩).unit /
        (IsLocalization.map_units K ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩).unit := by
    intro x
    obtain ⟨a, b, ha, hb, h⟩ := exists_ne_zero_div_eq (A := A) x.ne_zero
    refine ⟨a, b, ha, mem_nonZeroDivisors_iff_ne_zero.mp hb, Units.ext ?_⟩
    rw [Units.val_div_eq_div_val]
    exact h.symm
  obtain ⟨a, b, ha, hb, rfl⟩ := hunit f
  obtain ⟨c, d, hc, hd, rfl⟩ := hunit g
  rw [hexpand, hring a c ha hc, hring a d ha hd, hring b c hb hc, hring b d hb hd]
  omega

/-- For two nonzero nonunits of a two-dimensional Noetherian local domain, the orders of the
periodic determinants of multiplication by them on the localizations of the quotient by their
product sum to zero. -/
private theorem quotient_periodicDeterminant_sum_zero
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 2) (a b : A) (ha : a ≠ 0) (hb : b ≠ 0)
    (haunit : ¬ IsUnit a) (hbunit : ¬ IsUnit b) :
    ∃ (hdim' : ∀ q : {q : PrimeSpectrum A //
        Minimal (· ∈ Module.support A (A ⧸ Ideal.span {a * b})) q},
          Ring.KrullDimLE 1 (A ⧸ q.1.asIdeal)),
    ∃ (hfinite : ∀ q : {q : PrimeSpectrum A //
        Minimal (· ∈ Module.support A (A ⧸ Ideal.span {a * b})) q},
          IsFiniteLength (Localization.AtPrime q.1.asIdeal)
            (LocalizedModule q.1.asIdeal.primeCompl (A ⧸ Ideal.span {a * b}))),
    ∃ hexactab : ∀ q : {q : PrimeSpectrum A //
        Minimal (· ∈ Module.support A (A ⧸ Ideal.span {a * b})) q},
          Function.Exact
            (LocalizedModule.map q.1.asIdeal.primeCompl
              (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) a))
            (LocalizedModule.map q.1.asIdeal.primeCompl
              (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) b)),
    ∃ hexactba : ∀ q : {q : PrimeSpectrum A //
        Minimal (· ∈ Module.support A (A ⧸ Ideal.span {a * b})) q},
          Function.Exact
            (LocalizedModule.map q.1.asIdeal.primeCompl
              (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) b))
            (LocalizedModule.map q.1.asIdeal.primeCompl
              (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) a)),
      (∑ᶠ q : {q : PrimeSpectrum A //
          Minimal (· ∈ Module.support A (A ⧸ Ideal.span {a * b})) q},
        letI := hdim' q
        let d := periodicDeterminant
          (LocalizedModule.map q.1.asIdeal.primeCompl
            (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) a))
          (LocalizedModule.map q.1.asIdeal.primeCompl
            (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) b))
          (hexactab q) (hexactba q) (hfinite q)
        Multiplicative.toAdd (WithZero.unzero
          (x := Ring.ordFrac (A ⧸ q.1.asIdeal) (d : q.1.asIdeal.ResidueField))
          ((Units.isUnit d).map (Ring.ordFrac (A ⧸ q.1.asIdeal))).ne_zero)) = 0 := by
  classical
  let M := A ⧸ Ideal.span {a * b}
  let φ : Module.End A M := LinearMap.lsmul A M a
  let ψ : Module.End A M := LinearMap.lsmul A M b
  have hab : Function.Exact φ ψ := exact_mul_quotient_ab a b hb
  have hba : Function.Exact ψ φ := by
    simpa only [φ, ψ, M] using exact_mul_quotient_ab_reverse a b ha
  have hdimM : Module.supportDim A M = 1 :=
    quotient_principal_supportDim_one hdim a b (mul_ne_zero ha hb) haunit hbunit
  have hcoh := periodic_homology_finite_of_exact φ ψ hab hba
  obtain ⟨hdim', hfinite, hexactab, hexactba, hformula⟩ :=
    neg_periodicLength_eq_finsum_ordFrac_periodicDeterminant
      φ ψ (exact_comp_zero hba) (exact_comp_zero hab) hcoh (by simpa [M] using hdimM)
  have hper := periodicLength_zero_of_exact φ ψ hab hba
  refine ⟨hdim', hfinite, hexactab, hexactba, ?_⟩
  simpa [M, φ, ψ, hper] using hformula.symm

/-- The support of `A / I` over a domain `A` is the zero locus of `I`. -/
private theorem quotient_support_eq
    {A : Type u} [CommRing A] [IsDomain A] (I : Ideal A) :
    Module.support A (A ⧸ I) = Module.support A A ∩ PrimeSpectrum.zeroLocus I := by
  have htop : I • (⊤ : Submodule A A) = I := by
    simp
  calc
    Module.support A (A ⧸ I) =
        Module.support A (A ⧸ (I • (⊤ : Submodule A A))) := by rw [htop]
    _ = Module.support A A ∩ PrimeSpectrum.zeroLocus I :=
      Module.support_quotient (R := A) (M := A) I

/-- A point of the support of `A / I` over a domain `A` is a prime containing `I`. -/
private theorem le_of_mem_quotient_support
    {A : Type u} [CommRing A] [IsDomain A] {I : Ideal A} {p : PrimeSpectrum A}
    (hp : p ∈ Module.support A (A ⧸ I)) : I ≤ p.asIdeal := by
  have hz : p ∈ PrimeSpectrum.zeroLocus I := ((Set.ext_iff.mp (quotient_support_eq I) p).mp hp).2
  rw [PrimeSpectrum.mem_zeroLocus] at hz
  exact SetLike.coe_subset_coe.mp hz

/-- A prime containing `I` lies in the support of `A / I`. -/
private theorem prime_mem_quotient_support
    {A : Type u} [CommRing A] [IsDomain A] (I q : Ideal A) [q.IsPrime]
    (hIq : I ≤ q) :
    (⟨q, inferInstance⟩ : PrimeSpectrum A) ∈ Module.support A (A ⧸ I) := by
  rw [quotient_support_eq]
  constructor
  · rw [Module.support_eq_zeroLocus]
    change RingHom.ker (Module.toAddMonoidEnd A A) ≤ q
    intro x hx
    have hx0 := RingHom.mem_ker.mp hx
    have hxeq : x = 0 := by
      have h1 := congrArg (fun e : AddMonoid.End A => e 1) hx0
      change x • (1 : A) = 0 at h1
      simpa using h1
    simp [hxeq]
  · rw [PrimeSpectrum.mem_zeroLocus]
    exact SetLike.coe_subset_coe.mpr hIq

/-- A minimal point of the support of `A / I` is a minimal prime of `I`. -/
private theorem min_support_quotient_mem_minimalPrimes
    {A : Type u} [CommRing A] [IsDomain A]
    (I : Ideal A) (q : {q : PrimeSpectrum A //
      Minimal (· ∈ Module.support A (A ⧸ I)) q}) :
    q.1.asIdeal ∈ I.minimalPrimes := by
  change I.IsMinimalPrime q.1.asIdeal
  refine ⟨⟨q.1.isPrime, le_of_mem_quotient_support q.2.1⟩, ?_⟩
  intro J hJlt hJ
  have := hJlt.1
  have hrle : (⟨J, hJlt.1⟩ : PrimeSpectrum A) ≤ q.1 :=
    (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hJ
  exact (PrimeSpectrum.asIdeal_le_asIdeal q.1 _).mp
    (q.2.2 (prime_mem_quotient_support I J hJlt.2) hrle)

/-- For two nonunits with nonzero product, every minimal point of the support of the quotient by
the ideal generated by their product has height one. -/
private theorem min_support_quotient_height_one
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (a b : A) (hab : a * b ≠ 0) (ha : ¬ IsUnit a) (_hb : ¬ IsUnit b)
    (q : {q : PrimeSpectrum A //
      Minimal (· ∈ Module.support A (A ⧸ Ideal.span {a * b})) q}) :
    q.1.asIdeal.height = 1 := by
  have hmin := min_support_quotient_mem_minimalPrimes (Ideal.span {a * b}) q
  exact height_eq_one_of_mem_minimalPrimes_span hab (fun hu => ha (IsUnit.mul_iff.mp hu).1) hmin

/-- A height-one prime containing `a * b` is a minimal point of the support of the quotient by
the ideal generated by `a * b`. -/
private theorem heightOne_mem_minimal_support
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (a b : A) (hab : a * b ≠ 0)
    (q : {q : Ideal A // q.IsPrime ∧ q.height = 1}) (habq : a * b ∈ q.1) :
    Minimal (· ∈ Module.support A (A ⧸ Ideal.span {a * b}))
      (⟨q.1, q.2.1⟩ : PrimeSpectrum A) := by
  let I : Ideal A := Ideal.span {a * b}
  let : q.1.IsPrime := q.2.1
  have hqmin : q.1 ∈ I.minimalPrimes := heightOne_mem_minimalPrimes_span (a * b) hab q habq
  refine ⟨prime_mem_quotient_support I q.1 (q.1.span_singleton_le_iff_mem.mpr habq),
    fun p hpSupport hpq => ?_⟩
  exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr
    (hqmin.2 ⟨p.isPrime, le_of_mem_quotient_support hpSupport⟩ hpq)

/-- The minimal points of the support of the quotient by `a * b` are the height-one primes
containing `a * b`. -/
private noncomputable def minSupportEquivHeightOneContaining
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (a b : A) (hab : a * b ≠ 0) (ha : ¬ IsUnit a) (hb : ¬ IsUnit b) :
    {q : PrimeSpectrum A // Minimal (· ∈ Module.support A
      (A ⧸ Ideal.span {a * b})) q} ≃
      {q : {q : Ideal A // q.IsPrime ∧ q.height = 1} | a * b ∈ q.1} where
  toFun x := ⟨⟨x.1.asIdeal, x.1.isPrime,
      min_support_quotient_height_one a b hab ha hb x⟩,
    x.1.asIdeal.span_singleton_le_iff_mem.mp
      (min_support_quotient_mem_minimalPrimes (Ideal.span {a * b}) x).le⟩
  invFun q := ⟨⟨q.1.1, q.1.2.1⟩,
    heightOne_mem_minimal_support a b hab q.1 q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The image of a nonzero element of a domain in its localization at a prime is regular. -/
private theorem isRegular_algebraMap_atPrime {A : Type u} [CommRing A] [IsDomain A]
    (q : Ideal A) [q.IsPrime] {a : A} (ha : a ≠ 0) :
    IsRegular (algebraMap A (Localization.AtPrime q) a) :=
  isRegular_iff_mem_nonZeroDivisors.mpr <| mem_nonZeroDivisors_iff_ne_zero.mpr fun hz =>
    ha (FaithfulSMul.algebraMap_injective A (Localization.AtPrime q) (by simpa using hz))

/-- On a pair of nonzero elements of the ring the tame symbol at a height-one prime is the
symbol of their images in the localization at that prime. -/
private theorem localTameSymbol_eq_moduleSymbol_of_ring_elements
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (q : {q : Ideal A // q.IsPrime ∧ q.height = 1})
    [q.1.IsPrime]
    (a b : A) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdim : ringKrullDim (Localization.AtPrime q.1) = 1)
    (haR : IsRegular (algebraMap A (Localization.AtPrime q.1) a))
    (hbR : IsRegular (algebraMap A (Localization.AtPrime q.1) b)) :
    localTameSymbol q
      (IsLocalization.map_units K ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩).unit
      (IsLocalization.map_units K ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩).unit =
    AlgebraicGeometry.moduleSymbol (M := Localization.AtPrime q.1)
      (algebraMap A (Localization.AtPrime q.1) a)
      (algebraMap A (Localization.AtPrime q.1) b)
      haR.isSMulRegular hbR.isSMulRegular
      ((Module.supportDim_self_eq_ringKrullDim _).trans hdim) := by
  let : q.1.IsPrime := q.2.1
  let R := Localization.AtPrime q.1
  let K' := FractionRing A
  let e : K ≃ₐ[A] K' := (FractionRing.algEquiv A K).symm
  let ua : K'ˣ := (IsLocalization.map_units K'
    ⟨algebraMap A R a, isRegular_iff_mem_nonZeroDivisors.mp haR⟩).unit
  let ub : K'ˣ := (IsLocalization.map_units K'
    ⟨algebraMap A R b, isRegular_iff_mem_nonZeroDivisors.mp hbR⟩).unit
  have hUa : Units.map e.toRingEquiv.toMonoidHom
      (IsLocalization.map_units K ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩).unit = ua := by
    apply Units.ext
    change e (algebraMap A K a) = algebraMap R K' (algebraMap A R a)
    calc
      e (algebraMap A K a) = algebraMap A K' a := e.commutes a
      _ = algebraMap R K' (algebraMap A R a) := by
        rw [IsScalarTower.algebraMap_apply A R K' a]
  have hUb : Units.map e.toRingEquiv.toMonoidHom
      (IsLocalization.map_units K ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩).unit = ub := by
    apply Units.ext
    change e (algebraMap A K b) = algebraMap R K' (algebraMap A R b)
    calc
      e (algebraMap A K b) = algebraMap A K' b := e.commutes b
      _ = algebraMap R K' (algebraMap A R b) := by
        rw [IsScalarTower.algebraMap_apply A R K' b]
  change AlgebraicGeometry.tameSymbol (A := R) (K := K') hdim
      (Units.map e.toRingEquiv.toMonoidHom
        (IsLocalization.map_units K ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩).unit)
      (Units.map e.toRingEquiv.toMonoidHom
        (IsLocalization.map_units K ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩).unit) = _
  rw [hUa, hUb]
  exact (AlgebraicGeometry.tameSymbol (A := R) (K := K') hdim).eq_moduleSymbol
    (algebraMap A R a) (algebraMap A R b) haR hbR

/-- The order of the tame symbol vanishes at every height-one prime when its first argument is
a unit of the ring. -/
private theorem localSymbolOrder_zero_of_left_unit
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (q : {q : Ideal A // q.IsPrime ∧ q.height = 1})
    (hquot : Ring.KrullDimLE 1 (A ⧸ q.1))
    (a b : A) (ha : IsUnit a) (hb : b ≠ 0) :
    letI : q.1.IsPrime := q.2.1
    localSymbolOrder (q := q) hquot
      (localTameSymbol q
        (IsLocalization.map_units K ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha.ne_zero⟩).unit
        (IsLocalization.map_units K ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩).unit) = 0 := by
  let : q.1.IsPrime := q.2.1
  let R := Localization.AtPrime q.1
  have hdim := ringKrullDim_atPrime_heightOne q
  have haR := isRegular_algebraMap_atPrime q.1 ha.ne_zero
  have hbR := isRegular_algebraMap_atPrime q.1 hb
  have haUnitR : IsUnit (algebraMap A R a) := ha.map (algebraMap A R)
  let u : Rˣ := haUnitR.unit
  have hu : (u : R) = algebraMap A R a := haUnitR.unit_spec
  have hsymbol := localTameSymbol_eq_moduleSymbol_of_ring_elements (K := K) q a b
    ha.ne_zero hb hdim haR hbR
  have hformula := AlgebraicGeometry.moduleSymbol_unit_left_ring
    (A := R) u (algebraMap A R b) hbR.isSMulRegular hdim
  have hmodule : AlgebraicGeometry.moduleSymbol (M := R) (algebraMap A R a)
      (algebraMap A R b) haR.isSMulRegular hbR.isSMulRegular
      ((Module.supportDim_self_eq_ringKrullDim R).trans hdim) =
    AlgebraicGeometry.moduleSymbol (M := R) (u : R) (algebraMap A R b)
      (Units.isSMulRegular R u) hbR.isSMulRegular
      ((Module.supportDim_self_eq_ringKrullDim R).trans hdim) := by
    congr 1
  have hval : (localTameSymbol q
      (IsLocalization.map_units K ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha.ne_zero⟩).unit
      (IsLocalization.map_units K ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩).unit :
      q.1.ResidueField) =
      (IsLocalRing.residue R u) ^ (Ring.ord R (algebraMap A R b)).toNat := by
    calc
      _ = (AlgebraicGeometry.moduleSymbol (M := R) (algebraMap A R a)
          (algebraMap A R b) haR.isSMulRegular hbR.isSMulRegular
          ((Module.supportDim_self_eq_ringKrullDim R).trans hdim) :
          IsLocalRing.ResidueField R) := congrArg Units.val hsymbol
      _ = (AlgebraicGeometry.moduleSymbol (M := R) (u : R) (algebraMap A R b)
          (Units.isSMulRegular R u) hbR.isSMulRegular
          ((Module.supportDim_self_eq_ringKrullDim R).trans hdim) :
          IsLocalRing.ResidueField R) := congrArg Units.val hmodule
      _ = _ := hformula
  have hresidue : IsLocalRing.residue R u =
      algebraMap (A ⧸ q.1) q.1.ResidueField (Ideal.Quotient.mk q.1 a) := by
    calc
      IsLocalRing.residue R u = IsLocalRing.residue R (algebraMap A R a) := by rw [hu]
      _ = algebraMap R q.1.ResidueField (algebraMap A R a) := by
        rw [IsLocalRing.ResidueField.algebraMap_eq]
      _ = algebraMap (A ⧸ q.1) q.1.ResidueField (Ideal.Quotient.mk q.1 a) := by
        rw [← IsScalarTower.algebraMap_apply A R q.1.ResidueField a,
          Ideal.algebraMap_quotient_residueField_mk]
  have hunitQ : IsUnit (Ideal.Quotient.mk q.1 a) := ha.map (Ideal.Quotient.mk q.1)
  have hbase : Ring.ordFrac (A ⧸ q.1)
      (algebraMap (A ⧸ q.1) q.1.ResidueField (Ideal.Quotient.mk q.1 a)) = 1 := by
    rw [Ring.ordFrac_eq_ord _ hunitQ.ne_zero]
    have hnd : Ideal.Quotient.mk q.1 a ∈ nonZeroDivisors (A ⧸ q.1) :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hunitQ.ne_zero
    rw [Ring.ordMonoidWithZeroHom_eq_ord hnd, Ring.ord_of_isUnit hunitQ]
    simp
  have hord : Ring.ordFrac (A ⧸ q.1)
      (localTameSymbol q
        (IsLocalization.map_units K ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha.ne_zero⟩).unit
        (IsLocalization.map_units K ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩).unit :
        q.1.ResidueField) = 1 := by
    rw [hval, hresidue, map_pow, hbase, one_pow]
  simp [localSymbolOrder, hord]
  rfl

/-- The order of the tame symbol vanishes at every height-one prime when its second argument is
a unit of the ring. -/
private theorem localSymbolOrder_zero_of_right_unit
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (q : {q : Ideal A // q.IsPrime ∧ q.height = 1})
    (hquot : Ring.KrullDimLE 1 (A ⧸ q.1))
    (a b : A) (ha : a ≠ 0) (hb : IsUnit b) :
    letI : q.1.IsPrime := q.2.1
    localSymbolOrder (q := q) hquot
      (localTameSymbol q
        (IsLocalization.map_units K
          ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩).unit
        (IsLocalization.map_units K
          ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb.ne_zero⟩).unit) = 0 := by
  let : q.1.IsPrime := q.2.1
  let R := Localization.AtPrime q.1
  have hdim := ringKrullDim_atPrime_heightOne q
  have haR := isRegular_algebraMap_atPrime q.1 ha
  have hbR := isRegular_algebraMap_atPrime q.1 hb.ne_zero
  have hsymbolAB := localTameSymbol_eq_moduleSymbol_of_ring_elements (K := K) q a b
    ha hb.ne_zero hdim haR hbR
  have hsymbolBA := localTameSymbol_eq_moduleSymbol_of_ring_elements (K := K) q b a
    hb.ne_zero ha hdim hbR haR
  have hswap := AlgebraicGeometry.moduleSymbol_mul_swap
    (M := R) (algebraMap A R a) (algebraMap A R b)
    haR.isSMulRegular hbR.isSMulRegular
    ((Module.supportDim_self_eq_ringKrullDim R).trans hdim)
  have hprod :
      localTameSymbol q
          (IsLocalization.map_units K ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩).unit
          (IsLocalization.map_units K ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb.ne_zero⟩).unit *
        localTameSymbol q
          (IsLocalization.map_units K ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb.ne_zero⟩).unit
          (IsLocalization.map_units K ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩).unit = 1 := by
    rw [hsymbolAB, hsymbolBA]
    exact hswap
  have hleft := localSymbolOrder_zero_of_left_unit (K := K) q hquot b a hb ha
  have hmul := localSymbolOrder_mul (q := q) hquot
    (localTameSymbol q
      (IsLocalization.map_units K ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩).unit
      (IsLocalization.map_units K ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb.ne_zero⟩).unit)
    (localTameSymbol q
      (IsLocalization.map_units K ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb.ne_zero⟩).unit
      (IsLocalization.map_units K ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩).unit)
  have hone := localSymbolOrder_one (q := q) hquot
  rw [hprod, hone] at hmul
  omega

/-- The reciprocity sum vanishes on a pair of nonzero elements of the ring. -/
private theorem globalSymbolOrder_eq_zero_on_ring_elements
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hdim : ringKrullDim A = 2)
    (hquot : ∀ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
      Ring.KrullDimLE 1 (A ⧸ q.1))
    (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    globalSymbolOrder hquot
      (IsLocalization.map_units K ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩).unit
      (IsLocalization.map_units K ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩).unit = 0 := by
  classical
  let ua := (IsLocalization.map_units K
    ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩).unit
  let ub := (IsLocalization.map_units K
    ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩).unit
  by_cases haunit : IsUnit a
  · change (∑ᶠ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
      let : q.1.IsPrime := q.2.1
      localSymbolOrder (q := q) (hquot q) (localTameSymbol q ua ub)) = 0
    refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
    let : q.1.IsPrime := q.2.1
    exact localSymbolOrder_zero_of_left_unit q (hquot q) a b haunit hb
  by_cases hbunit : IsUnit b
  · change (∑ᶠ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
      let : q.1.IsPrime := q.2.1
      localSymbolOrder (q := q) (hquot q) (localTameSymbol q ua ub)) = 0
    refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
    let : q.1.IsPrime := q.2.1
    exact localSymbolOrder_zero_of_right_unit q (hquot q) a b ha hbunit
  obtain ⟨hdim', hfinite, hexactab, hexactba, hdetSum⟩ :=
    quotient_periodicDeterminant_sum_zero hdim a b ha hb haunit hbunit
  let minSupp : Type u := {q : PrimeSpectrum A //
    Minimal (· ∈ Module.support A (A ⧸ Ideal.span {a * b})) q}
  let supported : Type u := {q : {q : Ideal A // q.IsPrime ∧ q.height = 1} |
    a * b ∈ q.1}
  let supportedFinite : {q : Ideal A // q.IsPrime ∧ q.height = 1} → ℤ := fun q =>
    let : q.1.IsPrime := q.2.1
    localSymbolOrder (q := q) (hquot q) (localTameSymbol q ua ub)
  have hfiniteSupport :
      {q : {q : Ideal A // q.IsPrime ∧ q.height = 1} | a * b ∈ q.1}.Finite :=
    finite_heightOne_primes_containing (a * b) (mul_ne_zero ha hb)
  let e : minSupp ≃ supported :=
    minSupportEquivHeightOneContaining a b (mul_ne_zero ha hb) haunit hbunit
  have houtside (q : {q : Ideal A // q.IsPrime ∧ q.height = 1})
      (hnot : a * b ∉ q.1) :
      let : q.1.IsPrime := q.2.1
      localSymbolOrder (q := q) (hquot q) (localTameSymbol q ua ub) = 0 := by
    let : q.1.IsPrime := q.2.1
    have haq : a ∉ q.1 := by
      intro h
      apply hnot
      simpa [mul_comm] using q.1.mul_mem_left b h
    have hbq : b ∉ q.1 := by
      intro h
      apply hnot
      simpa [mul_comm] using q.1.mul_mem_right a h
    have hsymbol : localTameSymbol q ua ub = 1 := by
      apply localTameSymbol_eq_one_of_fraction_rep q a 1 b 1
        haq (fun h => q.2.1.ne_top (Ideal.eq_top_of_isUnit_mem q.1 h isUnit_one))
        hbq (fun h => q.2.1.ne_top (Ideal.eq_top_of_isUnit_mem q.1 h isUnit_one)) ua ub
      · change (ua : K) = algebraMap A K a / algebraMap A K 1
        calc
          (ua : K) = algebraMap A K a :=
            (IsLocalization.map_units K ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩).unit_spec
          _ = algebraMap A K a / algebraMap A K 1 := by simp
      · change (ub : K) = algebraMap A K b / algebraMap A K 1
        calc
          (ub : K) = algebraMap A K b :=
            (IsLocalization.map_units K ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩).unit_spec
          _ = algebraMap A K b / algebraMap A K 1 := by simp
    rw [hsymbol]
    exact localSymbolOrder_one (q := q) (hquot q)
  have hglobal : globalSymbolOrder hquot ua ub =
      ∑ᶠ q : supported,
        let : q.1.1.IsPrime := q.1.2.1
        localSymbolOrder (q := q.1) (hquot q.1)
        (localTameSymbol q.1 ua ub) := by
    change (∑ᶠ q : {q : Ideal A // q.IsPrime ∧ q.height = 1}, supportedFinite q) = _
    calc
      _ = ∑ᶠ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
          if a * b ∈ q.1 then supportedFinite q else 0 := by
        apply finsum_congr
        intro q
        by_cases hq : a * b ∈ q.1
        · simp [hq]
        · rw [ite_eq_right hq]
          exact houtside q hq
      _ = ∑ q ∈ hfiniteSupport.toFinset,
          (if a * b ∈ q.1 then supportedFinite q else 0) := by
        apply finsum_eq_sum_of_support_subset
        intro q hq
        by_cases hmem : a * b ∈ q.1
        · exact hfiniteSupport.mem_toFinset.mpr hmem
        · simp [hmem] at hq
      _ = ∑ q ∈ hfiniteSupport.toFinset, supportedFinite q := by
        apply Finset.sum_congr rfl
        intro q hq
        have hmem : a * b ∈ q.1 := hfiniteSupport.mem_toFinset.mp hq
        simp [hmem]
      _ = ∑ᶠ q : supported, supportedFinite q.1 := by
        rw [finsum_subtype_eq_finsum_cond]
        symm
        exact finsum_cond_eq_sum_of_cond_iff _ fun {q} hq =>
          ⟨hfiniteSupport.mem_toFinset.mpr,
            fun _ => Classical.byContradiction fun hnot => hq (houtside q hnot)⟩
  have hreindex :
      (∑ᶠ q : supported,
        let : q.1.1.IsPrime := q.1.2.1
        localSymbolOrder (q := q.1) (hquot q.1)
        (localTameSymbol q.1 ua ub)) =
      ∑ᶠ x : minSupp,
        let := hdim' x
        let d := periodicDeterminant
          (LocalizedModule.map x.1.asIdeal.primeCompl
            (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) a))
          (LocalizedModule.map x.1.asIdeal.primeCompl
            (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) b))
          (hexactab x) (hexactba x) (hfinite x)
        Multiplicative.toAdd (WithZero.unzero
          (x := Ring.ordFrac (A ⧸ x.1.asIdeal) (d : x.1.asIdeal.ResidueField))
          ((Units.isUnit d).map (Ring.ordFrac (A ⧸ x.1.asIdeal))).ne_zero) := by
    rw [← finsum_comp_equiv e]
    apply finsum_congr
    intro x
    let q : {q : Ideal A // q.IsPrime ∧ q.height = 1} :=
      ⟨x.1.asIdeal, x.1.isPrime,
        min_support_quotient_height_one a b (mul_ne_zero ha hb) haunit hbunit x⟩
    have hmin := min_support_quotient_mem_minimalPrimes
      (Ideal.span {a * b}) x
    have hmem : a * b ∈ q.1 := q.1.span_singleton_le_iff_mem.mp hmin.le
    have heq : e x = ⟨q, hmem⟩ := by
      apply Subtype.ext
      rfl
    let : q.1.IsPrime := q.2.1
    have hdimR := ringKrullDim_atPrime_heightOne q
    have haR := isRegular_algebraMap_atPrime q.1 ha
    have hbR := isRegular_algebraMap_atPrime q.1 hb
    have hdet :
        periodicDeterminant
          (LocalizedModule.map q.1.primeCompl
            (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) a))
          (LocalizedModule.map q.1.primeCompl
            (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) b))
          (hexactab x) (hexactba x) (hfinite x) =
        localTameSymbol q ua ub := by
      calc
        _ = AlgebraicGeometry.moduleSymbol (M := Localization.AtPrime q.1)
            (algebraMap A (Localization.AtPrime q.1) a)
            (algebraMap A (Localization.AtPrime q.1) b)
            haR.isSMulRegular hbR.isSMulRegular
            ((Module.supportDim_self_eq_ringKrullDim _).trans hdimR) :=
          periodicDeterminant_localized_quotient_eq_moduleSymbol a b
            (mul_ne_zero ha hb) hdimR haR.isSMulRegular hbR.isSMulRegular
            (hfinite x) (hexactab x) (hexactba x)
        _ = localTameSymbol q ua ub :=
          (localTameSymbol_eq_moduleSymbol_of_ring_elements q a b ha hb hdimR haR hbR).symm
    rw [heq]
    change localSymbolOrder (q := q) (hquot q) (localTameSymbol q ua ub) = _
    rw [← hdet]
    rfl
  exact hglobal.trans (hreindex.trans hdetSum)

/-- **Stacks Project, Tags 02QJ and 0EAX.** Let `A` be a two-dimensional Noetherian local domain
with fraction field `K` and let `f, g` be units of `K`. The orders of vanishing of the tame
symbols `∂_{A_𝔮}(f, g)` along `A / 𝔮`, summed over the height-one primes `𝔮` of `A`, give zero. -/
@[stacks 02QJ "the reciprocity formula, second displayed form: all height-one primes",
  stacks 0EAX "the second displayed form, the sum over all height-one primes"]
theorem sum_ord_localTameSymbol_eq_zero
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [IsLocalRing A] (hdim : ringKrullDim A = 2)
    (f g : Kˣ) :
    ∃ (hquot : ∀ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
        Ring.KrullDimLE 1 (A ⧸ q.1)),
    (∑ᶠ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
        letI : q.1.IsPrime := q.2.1
        letI := hquot q
        let d := localTameSymbol q f g
        Multiplicative.toAdd (WithZero.unzero
          (x := Ring.ordFrac (A ⧸ q.1) (d : q.1.ResidueField))
          ((Units.isUnit d).map (Ring.ordFrac (A ⧸ q.1))).ne_zero)) = 0 := by
  let hquot : ∀ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
      Ring.KrullDimLE 1 (A ⧸ q.1) := fun q => by
    let : q.1.IsPrime := q.2.1
    exact quotient_heightOne_krullDimLE hdim q.1 q.2.2
  refine ⟨hquot, ?_⟩
  change globalSymbolOrder hquot f g = 0
  exact globalSymbolOrder_eq_zero_of_eq_zero_on_ring hquot
    (globalSymbolOrder_eq_zero_on_ring_elements hdim hquot) f g

end AlgebraicGeometry
