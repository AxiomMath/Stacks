module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Basic
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
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Unit
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.FiniteLength
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reciprocity for the symbol on a two-dimensional Noetherian local ring

Let `A` be a two-dimensional Noetherian local ring and let `a, b` be nonzerodivisors of `A`. At
every height-one prime `𝔮` of `A` the localization `A_𝔮` is a one-dimensional Noetherian local
ring on which the images of `a` and `b` act injectively, so it carries the symbol
`d_{A_𝔮}(a, b)`, a unit of the residue field of `𝔮`. Taking the order of vanishing of that value
along `A / 𝔮` gives an integer at each height-one prime, and these integers sum to zero.

## Main definitions

* `AlgebraicGeometry.heightOneSymbol` is the symbol of the images of `a` and `b` in the
  localization at a height-one prime.

## Main results

* `AlgebraicGeometry.sum_ord_heightOneSymbol_eq_zero`: the orders of these symbols at the
  height-one primes sum to zero.

## Implementation notes

The one-dimensionality of each quotient `A / 𝔮`, needed to speak of the order of vanishing, is a
consequence of the hypotheses and so appears as an existential in the conclusion. The sum is a
`finsum` over all height-one primes; at a prime containing neither `a` nor `b` the symbol is
trivial, so the sum is supported on the finitely many height-one primes containing `a * b`.
There the sum of orders of periodic determinants on the localizations of `A / (ab)` is minus the
multiplicity of the two-periodic complex given by multiplication by `a` and by `b` on `A / (ab)`,
and that complex is exact, so the multiplicity vanishes.

## References

* [Stacks Project, Tag 0EAW](https://stacks.math.columbia.edu/tag/0EAW)
-/

@[expose] public section

noncomputable section

namespace AlgebraicGeometry

universe u v

/-- At a prime, the periodic determinant of multiplication by `a` and by `b` on the localization
of `A / (ab)` is the symbol of the images of `a` and `b` in the localized ring. -/
private theorem periodicDeterminant_localized_quotient_eq_moduleSymbol
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {q : PrimeSpectrum A} [q.1.IsPrime] (a b : A)
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
  let hcomm : LinearMap.range (φR.comp ψR) = LinearMap.range (ψR.comp φR) := by
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
          (Ideal.map (algebraMap A R) (Ideal.span {a * b})) = Iq :=
    (Submodule.map_id _).trans hmap
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
    rw [hqmk]
    rw [Submodule.mapQ_apply]
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
  have hmul : ∀ (c : A) (r : R), e (Submodule.Quotient.mk (algebraMap A R c * r)) =
      LocalizedModule.map p (LinearMap.lsmul A M c) (e (Submodule.Quotient.mk r)) := by
    intro c r
    have hmk : Submodule.Quotient.mk ((algebraMap A R c) * r) =
        (algebraMap A R c) • (Submodule.Quotient.mk r : Q) := by
      simpa only [smul_eq_mul] using
        (Submodule.Quotient.mk_smul (φR.comp ψR).range (algebraMap A R c) r)
    rw [hmk, e.map_smul]
    have hr : e (Submodule.Quotient.mk r) = r • e (Submodule.Quotient.mk (1 : R)) := by
      have hmk' : (Submodule.Quotient.mk r : Q) =
          r • (Submodule.Quotient.mk (1 : R) : Q) := by
        simpa using (Submodule.Quotient.mk_smul (φR.comp ψR).range r (1 : R))
      rw [hmk', e.map_smul]
    rw [hr, he_one, map_smul]
    simp only [LocalizedModule.mkLinearMap_apply]
    rw [LocalizedModule.map_mk]
    simp [LinearMap.lsmul_apply, LocalizedModule.smul'_mk, algebraMap_smul, smul_comm]
  have hφ : ∀ x : Q, e (φQ x) =
      LocalizedModule.map p (LinearMap.lsmul A M a) (e x) := fun x => by
    induction x using Submodule.Quotient.induction_on with
    | _ r => exact hmul a r
  have hψ : ∀ x : Q, e (ψQ x) =
      LocalizedModule.map p (LinearMap.lsmul A M b) (e x) := fun x => by
    induction x using Submodule.Quotient.induction_on with
    | _ r => exact hmul b r
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

/-- On `A / (ab)` the kernel of multiplication by `b` is the image of multiplication by `a`,
for `b` a nonzerodivisor. -/
private theorem exact_mul_quotient_ab
    {A : Type u} [CommRing A] (a b : A) (hb : b ∈ nonZeroDivisors A) :
    Function.Exact
      (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) a)
      (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) b) := by
  intro x
  constructor
  · intro hx
    induction x using Submodule.Quotient.induction_on with
    | _ z =>
      rw [LinearMap.lsmul_apply] at hx
      have hmem : b * z ∈ Ideal.span {a * b} :=
        Ideal.Quotient.eq_zero_iff_mem.mp hx
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hmem
      have h0 : (z - a * w) * b = 0 := by linear_combination hw
      have hzw : z = a * w :=
        sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hb).2 _ h0)
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

/-- On `A / (ab)` the kernel of multiplication by `a` is the image of multiplication by `b`,
for `a` a nonzerodivisor. -/
private theorem exact_mul_quotient_ab_reverse
    {A : Type u} [CommRing A] (a b : A) (ha : a ∈ nonZeroDivisors A) :
    Function.Exact
      (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) b)
      (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) a) := by
  have h := exact_mul_quotient_ab b a ha
  rwa [mul_comm b a] at h

/-- The localization at a height-one prime has Krull dimension one. -/
private theorem ringKrullDim_atPrime_eq_one
    {A : Type u} [CommRing A] (q : Ideal A) [q.IsPrime] (hq : q.height = 1) :
    ringKrullDim (Localization.AtPrime q) = 1 :=
  (IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)).trans
    (congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) hq)

/-- A nonzerodivisor of `A` acts injectively on the localization of `A` at a prime, since that
localization is a flat `A`-algebra. -/
private theorem isSMulRegular_algebraMap_atPrime
    {A : Type u} [CommRing A] (q : Ideal A) [q.IsPrime] {a : A}
    (ha : a ∈ nonZeroDivisors A) :
    IsSMulRegular (Localization.AtPrime q) (algebraMap A (Localization.AtPrime q) a) :=
  IsSMulRegular.of_flat (isRegular_iff_mem_nonZeroDivisors.mpr ha).isSMulRegular

/-- The symbol `d_{A_𝔮}(a, b)` of Stacks 02PZ at a height-one prime, formed on the
one-dimensional local ring `A_𝔮` from the images of two nonzerodivisors of `A`. -/
noncomputable def heightOneSymbol {A : Type u} [CommRing A] [IsNoetherianRing A]
    (q : {q : Ideal A // q.IsPrime ∧ q.height = 1}) {a b : A}
    (ha : a ∈ nonZeroDivisors A) (hb : b ∈ nonZeroDivisors A) :
    letI : q.1.IsPrime := q.2.1
    q.1.ResidueFieldˣ :=
  letI : q.1.IsPrime := q.2.1
  AlgebraicGeometry.moduleSymbol (M := Localization.AtPrime q.1)
    (algebraMap A (Localization.AtPrime q.1) a)
    (algebraMap A (Localization.AtPrime q.1) b)
    (IsSMulRegular.of_flat (isRegular_iff_mem_nonZeroDivisors.mpr ha).isSMulRegular)
    (IsSMulRegular.of_flat (isRegular_iff_mem_nonZeroDivisors.mpr hb).isSMulRegular)
    ((Module.supportDim_self_eq_ringKrullDim _).trans
      ((IsLocalization.AtPrime.ringKrullDim_eq_height q.1 (Localization.AtPrime q.1)).trans
        (congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) q.2.2)))

/-- The quotient of a two-dimensional Noetherian local ring by a height-one prime has Krull
dimension at most one. -/
private theorem quotient_heightOne_krullDimLE
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 2)
    (q : Ideal A) [q.IsPrime] (hq : q.height = 1) :
    Ring.KrullDimLE 1 (A ⧸ q) := by
  rw [Ring.krullDimLE_one_iff]
  intro J hJ
  let p := J.comap (Ideal.Quotient.mk q)
  have hp : p.IsPrime := by
    dsimp [p]
    exact hJ.comap (Ideal.Quotient.mk q)
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
      rw [finiteRingKrullDim_iff_ne_bot_and_top]
      constructor
      · rw [hdim]
        norm_num
      · rw [hdim]
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

/-- For two nonunits whose product is a nonzerodivisor in a two-dimensional Noetherian local
ring, the quotient by the ideal generated by their product has support of dimension one. -/
private theorem quotient_principal_supportDim_one
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 2) (a b : A)
    (hab : a * b ∈ nonZeroDivisors A) (ha : ¬ IsUnit a) (_hb : ¬ IsUnit b) :
    Module.supportDim A (A ⧸ Ideal.span {a * b}) = 1 := by
  have haM : a ∈ IsLocalRing.maximalIdeal A := by
    by_contra h
    exact ha (IsLocalRing.notMem_maximalIdeal.mp h)
  have habM : a * b ∈ IsLocalRing.maximalIdeal A := by
    rw [mul_comm]
    exact (IsLocalRing.maximalIdeal A).mul_mem_left b haM
  have hdrop : ringKrullDim (A ⧸ Ideal.span {a * b}) + 1 = ringKrullDim A :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      hab habM
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
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {q : {q : Ideal A // q.IsPrime ∧ q.height = 1}} [hqp : q.1.IsPrime]
    (hquot : Ring.KrullDimLE 1 (A ⧸ q.1))
    (d : q.1.ResidueFieldˣ) : ℤ := by
  letI := hquot
  exact Multiplicative.toAdd (WithZero.unzero
    (x := Ring.ordFrac (A ⧸ q.1) (d : q.1.ResidueField))
    ((Units.isUnit d).map (Ring.ordFrac (A ⧸ q.1))).ne_zero)

/-- The order of the trivial residue-field unit is zero. -/
private theorem localSymbolOrder_one
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {q : {q : Ideal A // q.IsPrime ∧ q.height = 1}} [hqp : q.1.IsPrime]
    (hquot : Ring.KrullDimLE 1 (A ⧸ q.1)) :
    localSymbolOrder (q := q) hquot 1 = 0 := by
  simp only [localSymbolOrder, Ring.ordFrac, Units.val_one, map_one]
  rfl

/-- The order of a product of residue-field units is the sum of their orders. -/
private theorem localSymbolOrder_mul
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {q : {q : Ideal A // q.IsPrime ∧ q.height = 1}} [hqp : q.1.IsPrime]
    (hquot : Ring.KrullDimLE 1 (A ⧸ q.1)) (x y : q.1.ResidueFieldˣ) :
    localSymbolOrder (q := q) hquot (x * y) =
      localSymbolOrder (q := q) hquot x + localSymbolOrder (q := q) hquot y := by
  simp [localSymbolOrder, map_mul, Units.val_mul, WithZero.unzero_mul]

/-- A height-one prime containing a nonzerodivisor is a minimal prime of the ideal that element
generates. -/
@[ega "0 16.3.1" "special case"]
private theorem heightOne_mem_minimalPrimes_span
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {a : A} (ha : a ∈ nonZeroDivisors A)
    (q : {q : Ideal A // q.IsPrime ∧ q.height = 1}) (haq : a ∈ q.1) :
    q.1 ∈ (Ideal.span {a}).minimalPrimes := by
  let : q.1.IsPrime := q.2.1
  by_cases hau : IsUnit a
  · exact (q.2.1.ne_top (Ideal.eq_top_of_isUnit_mem q.1 haq hau)).elim
  · let I : Ideal A := Ideal.span {a}
    have hI : I.height = 1 :=
      Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors ha hau
    obtain ⟨p, hp, hpI⟩ := Ideal.exists_minimalPrimes_le
      (q.1.span_singleton_le_iff_mem.mpr haq)
    let : p.IsPrime := hp.isPrime
    have hple : p.height ≤ 1 :=
      Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I p hp
    have hIle : I.height ≤ p.height := by
      rw [Ideal.height_eq_inf_minimalPrimes]
      exact iInf₂_le p hp
    have hpheight : p.height = 1 := le_antisymm hple (hI ▸ hIle)
    have hpq : p = q.1 :=
      p.eq_of_le_of_height_le hpI (by simp [q.2.2, hpheight])
    exact hpq ▸ hp

/-- A nonzerodivisor lies in only finitely many height-one primes. -/
private theorem finite_heightOne_primes_containing
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {a : A} (ha : a ∈ nonZeroDivisors A) :
    Set.Finite {q : {q : Ideal A // q.IsPrime ∧ q.height = 1} | a ∈ q.1} := by
  let s : Set {q : Ideal A // q.IsPrime ∧ q.height = 1} := {q | a ∈ q.1}
  have himage : Subtype.val '' s ⊆ (Ideal.span {a}).minimalPrimes := by
    rintro p ⟨q, hq, rfl⟩
    exact heightOne_mem_minimalPrimes_span ha q hq
  have hminfin : (Ideal.span {a}).minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})
  exact Set.Finite.of_finite_image (hminfin.subset himage)
    (Set.injOn_of_injective Subtype.val_injective)

/-- The support of `A / I` is the zero locus of `I` inside the support of `A`. -/
private theorem quotient_support_eq
    {A : Type u} [CommRing A] (I : Ideal A) :
    Module.support A (A ⧸ I) = Module.support A A ∩ PrimeSpectrum.zeroLocus I := by
  have htop : I • (⊤ : Submodule A A) = I := by
    simp
  calc
    Module.support A (A ⧸ I) =
        Module.support A (A ⧸ (I • (⊤ : Submodule A A))) := by rw [htop]
    _ = Module.support A A ∩ PrimeSpectrum.zeroLocus I :=
      Module.support_quotient (R := A) (M := A) I

/-- Every prime lies in the support of `A` itself. -/
private theorem mem_support_self
    {A : Type u} [CommRing A] (q : PrimeSpectrum A) :
    q ∈ Module.support A A := by
  rw [Module.support_eq_zeroLocus]
  change RingHom.ker (Module.toAddMonoidEnd A A) ≤ q.asIdeal
  intro x hx
  have hx0 := RingHom.mem_ker.mp hx
  have hxeq : x = 0 := by
    have h1 := congrArg (fun e : AddMonoid.End A => e 1) hx0
    change x • (1 : A) = 0 at h1
    simpa using h1
  simp [hxeq]

/-- A prime containing `I` lies in the support of `A / I`. -/
private theorem prime_mem_quotient_support
    {A : Type u} [CommRing A] (I q : Ideal A) [q.IsPrime]
    (hIq : I ≤ q) :
    (⟨q, inferInstance⟩ : PrimeSpectrum A) ∈ Module.support A (A ⧸ I) := by
  rw [quotient_support_eq]
  refine ⟨mem_support_self _, ?_⟩
  rw [PrimeSpectrum.mem_zeroLocus]
  exact SetLike.coe_subset_coe.mpr hIq

/-- A minimal point of the support of `A / I` is a minimal prime of `I`. -/
private theorem min_support_quotient_mem_minimalPrimes
    {A : Type u} [CommRing A]
    (I : Ideal A) (q : {q : PrimeSpectrum A //
      Minimal (· ∈ Module.support A (A ⧸ I)) q}) :
    q.1.asIdeal ∈ I.minimalPrimes := by
  have hsupport : q.1 ∈ Module.support A (A ⧸ I) := q.2.1
  have hsuppEq := quotient_support_eq (A := A) I
  have hIq : I ≤ q.1.asIdeal := by
    have hz := (Set.ext_iff.mp hsuppEq q.1).mp hsupport
    have hz' : q.1 ∈ PrimeSpectrum.zeroLocus I := hz.2
    rw [PrimeSpectrum.mem_zeroLocus] at hz'
    exact SetLike.coe_subset_coe.mp hz'
  change I.IsMinimalPrime q.1.asIdeal
  refine ⟨⟨q.1.isPrime, hIq⟩, ?_⟩
  intro J hJlt hJ
  let r : PrimeSpectrum A := ⟨J, hJlt.1⟩
  have hrsupport : r ∈ Module.support A (A ⧸ I) := by
    apply (Set.ext_iff.mp hsuppEq r).mpr
    refine ⟨mem_support_self _, ?_⟩
    rw [PrimeSpectrum.mem_zeroLocus]
    exact SetLike.coe_subset_coe.mpr hJlt.2
  have hrle : r ≤ q.1 := (PrimeSpectrum.asIdeal_le_asIdeal r q.1).mp hJ
  exact (PrimeSpectrum.asIdeal_le_asIdeal q.1 r).mp (q.2.2 hrsupport hrle)

/-- For two nonunits whose product is a nonzerodivisor, every minimal point of the support of the
quotient by the ideal generated by their product has height one. -/
private theorem min_support_quotient_height_one
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (a b : A) (hab : a * b ∈ nonZeroDivisors A) (ha : ¬ IsUnit a) (_hb : ¬ IsUnit b)
    (q : {q : PrimeSpectrum A //
      Minimal (· ∈ Module.support A (A ⧸ Ideal.span {a * b})) q}) :
    q.1.asIdeal.height = 1 := by
  have hmin := min_support_quotient_mem_minimalPrimes (Ideal.span {a * b}) q
  let : q.1.asIdeal.IsPrime := q.1.isPrime
  have hI : (Ideal.span {a * b}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors hab (by
      intro hu
      exact ha (IsUnit.mul_iff.mp hu).1)
  have hqle : q.1.asIdeal.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span {a * b}) q.1.asIdeal hmin
  have hIle : (Ideal.span {a * b}).height ≤ q.1.asIdeal.height := by
    rw [Ideal.height_eq_inf_minimalPrimes]
    exact iInf₂_le q.1.asIdeal hmin
  exact le_antisymm hqle (by simpa [hI] using hIle)

/-- A height-one prime containing `a * b` is a minimal point of the support of the quotient by
the ideal generated by `a * b`. -/
private theorem heightOne_mem_minimal_support
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (a b : A) (hab : a * b ∈ nonZeroDivisors A)
    (q : {q : Ideal A // q.IsPrime ∧ q.height = 1}) (habq : a * b ∈ q.1) :
    Minimal (· ∈ Module.support A (A ⧸ Ideal.span {a * b}))
      (⟨q.1, q.2.1⟩ : PrimeSpectrum A) := by
  let I : Ideal A := Ideal.span {a * b}
  let : q.1.IsPrime := q.2.1
  have hIq : I ≤ q.1 := q.1.span_singleton_le_iff_mem.mpr habq
  have hqmin : q.1 ∈ I.minimalPrimes :=
    heightOne_mem_minimalPrimes_span hab q habq
  have hsupport := prime_mem_quotient_support I q.1 hIq
  refine ⟨hsupport, ?_⟩
  intro p hpSupport hpq
  have hpI : I ≤ p.asIdeal := by
    have hp' := (Set.ext_iff.mp (quotient_support_eq I) p).mp hpSupport
    have hpI : p ∈ PrimeSpectrum.zeroLocus I := hp'.2
    rw [PrimeSpectrum.mem_zeroLocus] at hpI
    exact SetLike.coe_subset_coe.mp hpI
  have hqle : q.1 ≤ p.asIdeal := by
    by_contra hnot
    have hne : q.1 ≠ p.asIdeal := by
      intro heq
      exact hnot (heq ▸ le_rfl)
    have hlt : p.asIdeal < q.1 := lt_of_le_of_ne hpq (Ne.symm hne)
    exact (not_le_of_gt hlt) (hqmin.2 ⟨p.isPrime, hpI⟩ hlt.le)
  exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hqle

/-- The minimal points of the support of the quotient by `a * b` are the height-one primes
containing `a * b`. -/
private noncomputable def minSupportEquivHeightOneContaining
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (a b : A) (hab : a * b ∈ nonZeroDivisors A) (ha : ¬ IsUnit a) (hb : ¬ IsUnit b) :
    {q : PrimeSpectrum A // Minimal (· ∈ Module.support A
      (A ⧸ Ideal.span {a * b})) q} ≃
      {q : {q : Ideal A // q.IsPrime ∧ q.height = 1} | a * b ∈ q.1} where
  toFun x := ⟨⟨x.1.asIdeal, x.1.isPrime,
      min_support_quotient_height_one a b hab ha hb x⟩, by
        have hmin := min_support_quotient_mem_minimalPrimes
          (Ideal.span {a * b}) x
        exact x.1.asIdeal.span_singleton_le_iff_mem.mp hmin.le⟩
  invFun q := ⟨⟨q.1.1, q.1.2.1⟩,
    heightOne_mem_minimal_support a b hab q.1 q.2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv q := by apply Subtype.ext; rfl

/-- For two nonunit nonzerodivisors of a two-dimensional Noetherian local ring, the orders of the
periodic determinants of multiplication by them on the localizations of the quotient by their
product sum to zero. -/
private theorem quotient_periodicDeterminant_sum_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 2) (a b : A)
    (ha : a ∈ nonZeroDivisors A) (hb : b ∈ nonZeroDivisors A)
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
    quotient_principal_supportDim_one hdim a b (mul_mem ha hb) haunit hbunit
  have hcoh := periodic_homology_finite_of_exact φ ψ hab hba
  obtain ⟨hdim', hfinite, hexactab, hexactba, hformula⟩ :=
    neg_periodicLength_eq_finsum_ordFrac_periodicDeterminant
      φ ψ (exact_comp_zero hba) (exact_comp_zero hab) hcoh (by simpa [M] using hdimM)
  have hper := periodicLength_zero_of_exact φ ψ hab hba
  refine ⟨?_, hfinite, hexactab, hexactba, ?_⟩
  · intro q
    exact hdim' q
  · simpa [M, φ, ψ, hper] using hformula.symm

/-- If the image of `a` in `A_𝔮` is a unit, the symbol at a height-one prime `𝔮` is the power
of the residue of `a` given by the order of `b`. -/
private theorem val_heightOneSymbol_of_isUnit_left
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (q : {q : Ideal A // q.IsPrime ∧ q.height = 1}) [q.1.IsPrime] {a b : A}
    (ha : a ∈ nonZeroDivisors A) (hb : b ∈ nonZeroDivisors A)
    (haU : IsUnit (algebraMap A (Localization.AtPrime q.1) a)) :
    (heightOneSymbol q ha hb : q.1.ResidueField) =
      IsLocalRing.residue (Localization.AtPrime q.1) (algebraMap A _ a) ^
        (Ring.ord (Localization.AtPrime q.1) (algebraMap A _ b)).toNat := by
  have hdimR := ringKrullDim_atPrime_eq_one q.1 q.2.2
  have hbR := isSMulRegular_algebraMap_atPrime q.1 hb
  have hrewrite : heightOneSymbol q ha hb =
      AlgebraicGeometry.moduleSymbol (M := Localization.AtPrime q.1)
        (haU.unit : Localization.AtPrime q.1) (algebraMap A _ b)
        (Units.isSMulRegular _ haU.unit) hbR
        ((Module.supportDim_self_eq_ringKrullDim _).trans hdimR) := by
    change AlgebraicGeometry.moduleSymbol (M := Localization.AtPrime q.1) (algebraMap A _ a)
      (algebraMap A _ b) _ _ _ = _
    congr 1
  rw [hrewrite, moduleSymbol_unit_left_ring haU.unit (algebraMap A _ b) hbR hdimR,
    haU.unit_spec]

/-- At a height-one prime containing neither argument, the symbol is trivial. -/
private theorem heightOneSymbol_eq_one_of_notMem
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (q : {q : Ideal A // q.IsPrime ∧ q.height = 1}) {a b : A}
    (ha : a ∈ nonZeroDivisors A) (hb : b ∈ nonZeroDivisors A)
    (haq : a ∉ q.1) (hbq : b ∉ q.1) :
    heightOneSymbol q ha hb = 1 := by
  let : q.1.IsPrime := q.2.1
  have haU : IsUnit (algebraMap A (Localization.AtPrime q.1) a) :=
    IsLocalization.map_units _ (⟨a, haq⟩ : q.1.primeCompl)
  have hbU : IsUnit (algebraMap A (Localization.AtPrime q.1) b) :=
    IsLocalization.map_units _ (⟨b, hbq⟩ : q.1.primeCompl)
  apply Units.ext
  rw [val_heightOneSymbol_of_isUnit_left q ha hb haU, Ring.ord_of_isUnit hbU]
  simp

/-- The order of the symbol vanishes at every height-one prime when its first argument is a unit
of the ring. -/
private theorem localSymbolOrder_heightOneSymbol_zero_of_left_unit
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (q : {q : Ideal A // q.IsPrime ∧ q.height = 1})
    (hquot : Ring.KrullDimLE 1 (A ⧸ q.1))
    {a b : A} (ha : a ∈ nonZeroDivisors A) (hb : b ∈ nonZeroDivisors A)
    (haunit : IsUnit a) :
    letI : q.1.IsPrime := q.2.1
    localSymbolOrder (q := q) hquot (heightOneSymbol q ha hb) = 0 := by
  let : q.1.IsPrime := q.2.1
  let R := Localization.AtPrime q.1
  have haUnitR : IsUnit (algebraMap A R a) := haunit.map (algebraMap A R)
  have hval := val_heightOneSymbol_of_isUnit_left q ha hb haUnitR
  have hresidue : IsLocalRing.residue R (algebraMap A R a) =
      algebraMap (A ⧸ q.1) q.1.ResidueField (Ideal.Quotient.mk q.1 a) := by
    calc
      IsLocalRing.residue R (algebraMap A R a) =
          algebraMap R q.1.ResidueField (algebraMap A R a) := by
        rw [IsLocalRing.ResidueField.algebraMap_eq]
      _ = algebraMap (A ⧸ q.1) q.1.ResidueField (Ideal.Quotient.mk q.1 a) := by
        rw [← IsScalarTower.algebraMap_apply A R q.1.ResidueField a,
          Ideal.algebraMap_quotient_residueField_mk]
  have hunitQ : IsUnit (Ideal.Quotient.mk q.1 a) := haunit.map (Ideal.Quotient.mk q.1)
  let : Ring.KrullDimLE 1 (A ⧸ q.1) := hquot
  have hbase : Ring.ordFrac (A ⧸ q.1)
      (algebraMap (A ⧸ q.1) q.1.ResidueField (Ideal.Quotient.mk q.1 a)) = 1 := by
    rw [Ring.ordFrac_eq_ord _ hunitQ.ne_zero]
    have hnd : Ideal.Quotient.mk q.1 a ∈ nonZeroDivisors (A ⧸ q.1) :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hunitQ.ne_zero
    rw [Ring.ordMonoidWithZeroHom_eq_ord hnd, Ring.ord_of_isUnit hunitQ]
    simp
  have hord : Ring.ordFrac (A ⧸ q.1)
      (heightOneSymbol q ha hb : q.1.ResidueField) = 1 := by
    rw [hval, hresidue, map_pow, hbase, one_pow]
  simp [localSymbolOrder, hord]
  rfl

/-- The order of the symbol vanishes at every height-one prime when its second argument is a unit
of the ring. -/
private theorem localSymbolOrder_heightOneSymbol_zero_of_right_unit
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (q : {q : Ideal A // q.IsPrime ∧ q.height = 1})
    (hquot : Ring.KrullDimLE 1 (A ⧸ q.1))
    {a b : A} (ha : a ∈ nonZeroDivisors A) (hb : b ∈ nonZeroDivisors A)
    (hbunit : IsUnit b) :
    letI : q.1.IsPrime := q.2.1
    localSymbolOrder (q := q) hquot (heightOneSymbol q ha hb) = 0 := by
  let : q.1.IsPrime := q.2.1
  let R := Localization.AtPrime q.1
  have hdimR : ringKrullDim R = 1 := ringKrullDim_atPrime_eq_one q.1 q.2.2
  have hsd : Module.supportDim R R = 1 :=
    (Module.supportDim_self_eq_ringKrullDim R).trans hdimR
  have haR : IsSMulRegular R (algebraMap A R a) :=
    isSMulRegular_algebraMap_atPrime q.1 ha
  have hbR : IsSMulRegular R (algebraMap A R b) :=
    isSMulRegular_algebraMap_atPrime q.1 hb
  have hab : heightOneSymbol q ha hb =
      AlgebraicGeometry.moduleSymbol (M := R) (algebraMap A R a) (algebraMap A R b)
        haR hbR hsd := rfl
  have hba : heightOneSymbol q hb ha =
      AlgebraicGeometry.moduleSymbol (M := R) (algebraMap A R b) (algebraMap A R a)
        hbR haR hsd := rfl
  have hprod : heightOneSymbol q ha hb * heightOneSymbol q hb ha = 1 := by
    rw [hab, hba]
    exact moduleSymbol_mul_swap (algebraMap A R a) (algebraMap A R b) haR hbR hsd
  have hleft := localSymbolOrder_heightOneSymbol_zero_of_left_unit q hquot hb ha hbunit
  have hmul := localSymbolOrder_mul (q := q) hquot
    (heightOneSymbol q ha hb) (heightOneSymbol q hb ha)
  have hone := localSymbolOrder_one (q := q) hquot
  rw [hprod, hone] at hmul
  omega

/-- **Stacks Project, Tag 0EAW.** Let `A` be a two-dimensional Noetherian local ring and let
`a, b` be nonzerodivisors of `A`. The orders of vanishing of the symbols `d_{A_𝔮}(a, b)` along
`A / 𝔮`, summed over the height-one primes `𝔮` of `A`, give zero. -/
@[stacks 0EAW]
theorem sum_ord_heightOneSymbol_eq_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 2) {a b : A}
    (ha : a ∈ nonZeroDivisors A) (hb : b ∈ nonZeroDivisors A) :
    ∃ hquot : ∀ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
        Ring.KrullDimLE 1 (A ⧸ q.1),
    (∑ᶠ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
        letI : q.1.IsPrime := q.2.1
        letI := hquot q
        let d := heightOneSymbol q ha hb
        Multiplicative.toAdd (WithZero.unzero
          (x := Ring.ordFrac (A ⧸ q.1) (d : q.1.ResidueField))
          ((Units.isUnit d).map (Ring.ordFrac (A ⧸ q.1))).ne_zero)) = 0 := by
  classical
  let hquot : ∀ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
      Ring.KrullDimLE 1 (A ⧸ q.1) := fun q => by
    let : q.1.IsPrime := q.2.1
    exact quotient_heightOne_krullDimLE hdim q.1 q.2.2
  refine ⟨hquot, ?_⟩
  change (∑ᶠ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
      let : q.1.IsPrime := q.2.1
      localSymbolOrder (q := q) (hquot q) (heightOneSymbol q ha hb)) = 0
  by_cases haunit : IsUnit a
  · calc
      _ = ∑ᶠ _q : {q : Ideal A // q.IsPrime ∧ q.height = 1}, (0 : ℤ) := finsum_congr fun q =>
        let : q.1.IsPrime := q.2.1
        localSymbolOrder_heightOneSymbol_zero_of_left_unit q (hquot q) ha hb haunit
      _ = 0 := by simp
  by_cases hbunit : IsUnit b
  · calc
      _ = ∑ᶠ _q : {q : Ideal A // q.IsPrime ∧ q.height = 1}, (0 : ℤ) := finsum_congr fun q =>
        let : q.1.IsPrime := q.2.1
        localSymbolOrder_heightOneSymbol_zero_of_right_unit q (hquot q) ha hb hbunit
      _ = 0 := by simp
  obtain ⟨hdim', hfinite, hexactab, hexactba, hdetSum⟩ :=
    quotient_periodicDeterminant_sum_zero hdim a b ha hb haunit hbunit
  let minSupp : Type u := {q : PrimeSpectrum A //
    Minimal (· ∈ Module.support A (A ⧸ Ideal.span {a * b})) q}
  let supported : Type u := {q : {q : Ideal A // q.IsPrime ∧ q.height = 1} |
    a * b ∈ q.1}
  let term : {q : Ideal A // q.IsPrime ∧ q.height = 1} → ℤ := fun q =>
    let : q.1.IsPrime := q.2.1
    localSymbolOrder (q := q) (hquot q) (heightOneSymbol q ha hb)
  have hfiniteSupport :
      {q : {q : Ideal A // q.IsPrime ∧ q.height = 1} | a * b ∈ q.1}.Finite :=
    finite_heightOne_primes_containing (mul_mem ha hb)
  let e : minSupp ≃ supported :=
    minSupportEquivHeightOneContaining a b (mul_mem ha hb) haunit hbunit
  have houtside (q : {q : Ideal A // q.IsPrime ∧ q.height = 1})
      (hnot : a * b ∉ q.1) : term q = 0 := by
    let : q.1.IsPrime := q.2.1
    have haq : a ∉ q.1 := by
      intro h
      apply hnot
      simpa [mul_comm] using q.1.mul_mem_left b h
    have hbq : b ∉ q.1 := by
      intro h
      apply hnot
      simpa [mul_comm] using q.1.mul_mem_right a h
    change localSymbolOrder (q := q) (hquot q) (heightOneSymbol q ha hb) = 0
    rw [heightOneSymbol_eq_one_of_notMem q ha hb haq hbq]
    exact localSymbolOrder_one (q := q) (hquot q)
  have hglobal : (∑ᶠ q : {q : Ideal A // q.IsPrime ∧ q.height = 1}, term q) =
      ∑ᶠ q : supported, term q.1 := by
    calc
      _ = ∑ᶠ q : {q : Ideal A // q.IsPrime ∧ q.height = 1},
          if a * b ∈ q.1 then term q else 0 := by
        apply finsum_congr
        intro q
        by_cases hq : a * b ∈ q.1
        · simp [hq]
        · rw [ite_eq_right hq]
          exact houtside q hq
      _ = ∑ q ∈ hfiniteSupport.toFinset,
          (if a * b ∈ q.1 then term q else 0) := by
        apply finsum_eq_sum_of_support_subset
        intro q hq
        by_cases hmem : a * b ∈ q.1
        · exact hfiniteSupport.mem_toFinset.mpr hmem
        · simp [hmem] at hq
      _ = ∑ q ∈ hfiniteSupport.toFinset, term q := by
        apply Finset.sum_congr rfl
        intro q hq
        have hmem : a * b ∈ q.1 := hfiniteSupport.mem_toFinset.mp hq
        simp [hmem]
      _ = ∑ᶠ q : supported, term q.1 := by
        rw [finsum_subtype_eq_finsum_cond]
        symm
        apply finsum_cond_eq_sum_of_cond_iff
        intro q hq
        constructor
        · intro hmem
          exact hfiniteSupport.mem_toFinset.mpr hmem
        · intro hmem
          by_contra hnot
          exact hq (houtside q hnot)
  have hreindex : (∑ᶠ q : supported, term q.1) =
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
        min_support_quotient_height_one a b (mul_mem ha hb) haunit hbunit x⟩
    have hmin := min_support_quotient_mem_minimalPrimes
      (Ideal.span {a * b}) x
    have hmem : a * b ∈ q.1 := q.1.span_singleton_le_iff_mem.mp hmin.le
    have heq : e x = ⟨q, hmem⟩ := by
      apply Subtype.ext
      rfl
    let : q.1.IsPrime := q.2.1
    have hdimR : ringKrullDim (Localization.AtPrime q.1) = 1 :=
      ringKrullDim_atPrime_eq_one q.1 q.2.2
    have haR : IsSMulRegular (Localization.AtPrime q.1)
        (algebraMap A (Localization.AtPrime q.1) a) :=
      isSMulRegular_algebraMap_atPrime q.1 ha
    have hbR : IsSMulRegular (Localization.AtPrime q.1)
        (algebraMap A (Localization.AtPrime q.1) b) :=
      isSMulRegular_algebraMap_atPrime q.1 hb
    have hdet :
        periodicDeterminant
          (LocalizedModule.map q.1.primeCompl
            (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) a))
          (LocalizedModule.map q.1.primeCompl
            (LinearMap.lsmul A (A ⧸ Ideal.span {a * b}) b))
          (hexactab x) (hexactba x) (hfinite x) =
        heightOneSymbol q ha hb := by
      calc
        _ = AlgebraicGeometry.moduleSymbol (M := Localization.AtPrime q.1)
            (algebraMap A (Localization.AtPrime q.1) a)
            (algebraMap A (Localization.AtPrime q.1) b)
            haR hbR
            ((Module.supportDim_self_eq_ringKrullDim _).trans hdimR) :=
          periodicDeterminant_localized_quotient_eq_moduleSymbol a b
            hdimR haR hbR (hfinite x) (hexactab x) (hexactba x)
        _ = heightOneSymbol q ha hb := rfl
    rw [heq]
    change localSymbolOrder (q := q) (hquot q) (heightOneSymbol q ha hb) = _
    rw [← hdet]
    rfl
  calc
    _ = ∑ᶠ q : supported, term q.1 := hglobal
    _ = _ := hreindex
    _ = 0 := hdetSum

end AlgebraicGeometry
