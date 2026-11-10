module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitLocalCohomology
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.IsolatedPrime
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Depth, dimension and regular elements for the algebraization comparison

This file collects the commutative-algebra inputs of the induction of Stacks 0EFL: the
computation of the relative dimension `dim((A/p)_q)` through a dimension function, the behaviour
of depth and support dimension under dividing by a nonzerodivisor, the existence of a
nonzerodivisor inside a prescribed ideal, the reduction of a finite module to one all of whose
associated primes lie outside `V(I) ∪ T`, and the arithmetic of the extended integers in which
the depth and dimension bounds of the source are compared.

## Main results

* `Stacks.Algebraization.krullDimToEInt_localizedQuotient_eq` — for a dimension function `δ` and
  primes `p ≤ q`, the relative dimension `dim((A/p)_q)` is `δ(p) - δ(q)`.
* `Stacks.Algebraization.exists_specialization_dimension_le_of_le_jacobson` and
  `Stacks.Algebraization.exists_specialization_dimension_le` — Stacks 0DXF in the form used
  here: a prime of a ring whose ideal `I` lies in the Jacobson radical — in particular of a ring
  complete along `I` — has a specialization in `V(I)` along which the relative dimension is at
  most `cd(A, I)`.
* `Stacks.Algebraization.depth_supportDim_succ_of_regular_quotient` — dividing by a
  nonzerodivisor drops depth and support dimension by exactly one.
* `Stacks.Algebraization.exists_isSMulRegular_mem_mul_pow` — a nonzerodivisor on `M` inside
  `a * (J₀ I) ^ t`, when all associated primes of `M` avoid `V(I)` and `T`.
* `Stacks.Algebraization.exists_reduced_quotient_submodule` — the maximal submodule supported in
  `V(I) ∪ T ∪ (the primes with no specialization in V(J) ∩ V(I))`, whose local cohomology is
  derived complete after shrinking.

## Implementation notes

The dimension function of the source is a bare map `δ : Spec(A) → ℤ` together with the property
`IsDimensionFunctionProp` of Stacks 02I9, which is how `Stacks.Algebraization`'s hypothesis
structures carry it. Depth values live in `ℕ∞` and Krull dimensions in `WithBot ℕ∞`; both are
compared in `EInt` through `Stacks.Algebraization.enatToEInt` and
`Stacks.Algebraization.krullDimToEInt`.

## References

* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
* [Stacks Project, Tag 02I9](https://stacks.math.columbia.edu/tag/02I9)
* [Stacks Project, Tag 0DXF](https://stacks.math.columbia.edu/tag/0DXF)
* [Stacks Project, Tag 0EFG](https://stacks.math.columbia.edu/tag/0EFG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u v w

namespace Stacks.Algebraization

/-- **The arithmetic of condition (5).** Each of the three alternatives of condition (5) of
Stacks 0EFL, combined with condition (4) at an associated prime and the strict drop of the
dimension function along a nontrivial specialization, gives the bound `d + s < depth + dim`. -/
public theorem depth_add_dimension_gt_of_supplemental
    {s d depth δa δb δp δq δq' δmin δmax dim : ℤ}
    (hs : 0 < s) (hdepth : s ≤ depth) (hstep : δp < δb)
    (hsupportDim : δa - δp ≤ dim)
    (hassociated : d + s < δa - δq')
    (hqmin : δmin ≤ δq) (hqmax : δq' ≤ δmax)
    (hsupplemental : dim < s + 2 ∨ d + δmax - 1 < δp ∨
      d + s + δmax - δmin - 2 < δp - δq) :
    d + s < depth + δb - δq' := by
  rcases hsupplemental with h | h | h <;> omega

private theorem krullDim_eq_of_bounded_grade
    {α : Type*} [PartialOrder α] [BoundedOrder α] [FiniteDimensionalOrder α]
    (δ : α → ℤ)
    (hstep : ∀ {a b : α}, a ⋖ b → δ a = δ b + 1) :
    Order.krullDim α = (((δ ⊥ - δ ⊤).toNat : ℕ∞) : WithBot ℕ∞) := by
  have : WellFoundedLT α :=
    SetRel.IsWellFounded.of_finiteDimensional {(a, b) : α × α | a < b}
  have : WellFoundedGT α :=
    SetRel.IsWellFounded.inv_of_finiteDimensional {(a, b) : α × α | a < b}
  let s := LTSeries.longestOf α
  obtain ⟨t, e, _, ht₀, ht₁⟩ :=
    s.exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot
  have hlen : (t.length : ℤ) = δ ⊥ - δ ⊤ := by
    have hf (i : Fin (t.length + 1)) : δ (t i) = δ t.head - i.val := by
      induction i using Fin.induction with
      | zero =>
        simp only [Fin.val_zero, Nat.cast_zero, sub_zero]
        rfl
      | succ i ih =>
        have h : δ (t i.castSucc) = δ (t i.succ) + 1 := hstep (t.step i)
        change δ (t i.castSucc) = δ t.head - (i.val : ℤ) at ih
        change δ (t i.succ) = δ t.head - ((i.val + 1 : ℕ) : ℤ)
        omega
    have h : δ t.last = δ t.head - (t.length : ℤ) := hf (Fin.last t.length)
    rw [ht₀, ht₁] at h
    omega
  have hl : t.length = s.length := by
    apply Nat.le_antisymm
    · let t' : LTSeries α :=
        { length := t.length, toFun := t, step := fun i => (t.step i).lt }
      exact t'.longestOf_is_longest
    · have h := Fintype.card_le_of_injective e e.injective
      simpa only [Fintype.card_fin, Nat.add_le_add_iff_right] using h
  rw [Order.krullDim_eq_length_of_finiteDimensionalOrder]
  have h : (δ ⊥ - δ ⊤).toNat = s.length := by omega
  rw [h]
  rfl

/-- The spectrum of `(A_𝔮)/(𝔭 A_𝔮)` is the interval of primes between `𝔭` and `𝔮`. -/
noncomputable def primeSpectrumLocalizedQuotientOrderIso
    {A : Type*} [CommRing A] (p q : PrimeSpectrum A) :
    PrimeSpectrum ((Localization.AtPrime q.asIdeal) ⧸
      p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal))) ≃o Set.Icc p q := by
  let B := Localization.AtPrime q.asIdeal
  let f := algebraMap A B
  let e₁ := (p.asIdeal.map f).primeSpectrumQuotientOrderIsoZeroLocus
  let e₂ := IsLocalization.AtPrime.primeSpectrumOrderIso B q.asIdeal
  have he₂ (x : PrimeSpectrum B) : (e₂ x).val.asIdeal = x.asIdeal.comap f := rfl
  refine
    { toFun := fun x => ⟨(e₂ (e₁ x).val).val,
        ⟨?_, (e₂ (e₁ x).val).property⟩⟩
      invFun := fun y => e₁.symm ⟨e₂.symm ⟨y.val, y.property.2⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }
  · change p.asIdeal ≤ ((e₂ (e₁ x).val).val).asIdeal
    rw [he₂]
    exact Ideal.map_le_iff_le_comap.mp (e₁ x).property
  · change p.asIdeal.map f ≤ (e₂.symm ⟨y.val, y.property.2⟩).asIdeal
    rw [Ideal.map_le_iff_le_comap, ← he₂, e₂.apply_symm_apply]
    exact y.property.1
  · intro x
    apply e₁.injective
    rw [e₁.apply_symm_apply]
    apply Subtype.ext
    exact e₂.symm_apply_apply _
  · intro y
    apply Subtype.ext
    dsimp only
    rw [e₁.apply_symm_apply, e₂.apply_symm_apply]
  · intro a b
    change e₂ (e₁ a).val ≤ e₂ (e₁ b).val ↔ a ≤ b
    rw [e₂.le_iff_le]
    exact e₁.le_iff_le

private theorem dimensionFunction_step_of_covBy
    {A : Type*} [CommRing A] {δ : PrimeSpectrum A → ℤ} (hδ : IsDimensionFunctionProp δ)
    {p q : PrimeSpectrum A} (hpq : p ⋖ q) : δ p = δ q + 1 := by
  refine hδ.2 p q ⟨(PrimeSpectrum.le_iff_specializes _ _).mp hpq.le, hpq.ne, ?_⟩
  intro r hpr hrq
  have hpr' := (PrimeSpectrum.le_iff_specializes _ _).mpr hpr
  have hrq' := (PrimeSpectrum.le_iff_specializes _ _).mpr hrq
  rcases eq_or_lt_of_le hpr' with h | h
  · exact Or.inl h.symm
  rcases eq_or_lt_of_le hrq' with h2 | h2
  · exact Or.inr h2
  · exact absurd h2 (hpq.2 h)

private theorem ringKrullDim_localizedQuotient_eq_dimensionFunction
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {δ : PrimeSpectrum A → ℤ} (hδ : IsDimensionFunctionProp δ)
    (p q : PrimeSpectrum A) (hpq : p ≤ q) :
    ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
      p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal))) =
        (((δ p - δ q).toNat : ℕ∞) : WithBot ℕ∞) := by
  let E := Set.Icc p q
  let e := primeSpectrumLocalizedQuotientOrderIso p q
  let : BoundedOrder E :=
    { top := ⟨q, hpq, le_rfl⟩
      bot := ⟨p, le_rfl, hpq⟩
      le_top := fun a => a.property.2
      bot_le := fun a => a.property.1 }
  have hdim : Order.krullDim E < ⊤ := by
    rw [← Order.krullDim_eq_of_orderIso e]
    exact (ringKrullDim_quotient_le _).trans_lt
      (ringKrullDim_lt_top (R := Localization.AtPrime q.asIdeal))
  have : FiniteDimensionalOrder E :=
    Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mpr
      ⟨Order.bot_lt_krullDim.ne', hdim.ne⟩
  rw [ringKrullDim, Order.krullDim_eq_of_orderIso e]
  apply krullDim_eq_of_bounded_grade (fun x : E => δ x.val)
  intro a b hab
  apply dimensionFunction_step_of_covBy hδ
  exact hab.image (OrderEmbedding.subtype (· ∈ Set.Icc p q)) (by
    simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype, Set.ofPred_mem_eq] using
      (Set.ordConnected_Icc : (Set.Icc p q).OrdConnected))

/-- The passage from Krull dimensions to extended integers is monotone. -/
public theorem krullDimToEInt_mono : Monotone krullDimToEInt := by
  intro a b hab
  cases a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    cases b using WithBot.recBotCoe with
    | bot => exact False.elim (WithBot.not_coe_le_bot _ hab)
    | coe b =>
      have hab : a ≤ b := WithBot.coe_le_coe.mp hab
      cases a using ENat.recTopCoe with
      | top =>
        obtain rfl := top_le_iff.mp hab
        exact le_rfl
      | coe a =>
        cases b using ENat.recTopCoe with
        | top => exact le_top
        | coe b =>
          change ((a : ℤ) : EInt) ≤ ((b : ℤ) : EInt)
          exact WithBotTop.coe_le_coe.mpr (by exact_mod_cast hab)

/-- The residue field of a local ring has Krull dimension zero. -/
private theorem ringKrullDim_quotient_maximalIdeal_eq_zero
    (R : Type*) [CommRing R] [IsLocalRing R] :
    ringKrullDim (R ⧸ maximalIdeal R) = 0 :=
  ringKrullDim_eq_zero_of_isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance)

/-- A module has depth zero at an associated prime. -/
@[ega "0 16.4.6" "(i)"]
public theorem depth_localization_eq_zero_of_mem_associatedPrimes
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (hp : p.asIdeal ∈ associatedPrimes A M) :
    Module.depth (Localization.AtPrime p.asIdeal) (maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl M) = 0 := by
  have h := Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes
    (Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hp)
  rw [ringKrullDim_quotient_maximalIdeal_eq_zero] at h
  exact le_antisymm (WithBot.coe_le_coe.mp h) bot_le

private theorem associatedPrime_map_localization
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    (p q : PrimeSpectrum A) (hp : p.asIdeal ∈ associatedPrimes A M) (hpq : p ≤ q) :
    p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)) ∈
      associatedPrimes (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) := by
  open Module.associatedPrimes in
  apply mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
    q.asIdeal.primeCompl (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)
  have he := IsLocalization.under_map_of_isPrime_disjoint q.asIdeal.primeCompl
    (Localization.AtPrime q.asIdeal) p.isPrime
    (Set.disjoint_left.mpr fun x hx hxp => hx (hpq hxp))
  change (p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal))).under A ∈
    associatedPrimes A M
  rw [he]
  exact hp

/-- For an associated prime `p` of `M` and a specialization `q` of `p`, the relative dimension
`dim((A/p)_q)` is at most the dimension of the support of `M_q`. -/
public theorem ringKrullDim_localizedQuotient_le_supportDim
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p q : PrimeSpectrum A) (hp : p.asIdeal ∈ associatedPrimes A M) (hpq : p ≤ q) :
    ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
      p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal))) ≤
      Module.supportDim (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) := by
  rw [ringKrullDim_quotient, Module.supportDim, Module.support_eq_zeroLocus]
  have h := (associatedPrime_map_localization p q hp hpq).annihilator_le
  rw [Submodule.annihilator_top] at h
  exact Order.krullDim_le_of_orderEmbedding
    (Subtype.orderEmbedding (fun t ht => by
      change Module.annihilator _ _ ≤ t.asIdeal
      exact h.trans ht))

/-- Every prime in the support of a finite module contains an associated prime. -/
public theorem exists_associatedPrime_le_of_mem_support
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (hp : p ∈ Module.support A M) :
    ∃ q : PrimeSpectrum A, q.asIdeal ∈ associatedPrimes A M ∧ q ≤ p := by
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (Module.annihilator_le_of_mem_support hp)
  exact ⟨⟨q, hq.isPrime⟩,
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A M hq, hqp⟩

private theorem dimensionFunction_sub_nonneg
    {A : Type*} [CommRing A] {δ : PrimeSpectrum A → ℤ} (hδ : IsDimensionFunctionProp δ)
    (p q : PrimeSpectrum A) (hpq : p ≤ q) : 0 ≤ δ p - δ q := by
  by_cases h : p = q
  · simp [h]
  · have := hδ.1 p q ((PrimeSpectrum.le_iff_specializes _ _).mp hpq) h
    omega

/-- **The relative dimension through a dimension function.** For a dimension function `δ` in the
sense of Stacks 02I9 and primes `p ≤ q`, the relative dimension `dim((A/p)_q)` equals
`δ(p) - δ(q)`. -/
public theorem krullDimToEInt_localizedQuotient_eq
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {δ : PrimeSpectrum A → ℤ} (hδ : IsDimensionFunctionProp δ)
    (p q : PrimeSpectrum A) (hpq : p ≤ q) :
    krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
      p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) =
        ((δ p - δ q : ℤ) : EInt) := by
  rw [ringKrullDim_localizedQuotient_eq_dimensionFunction hδ p q hpq]
  change ((((δ p - δ q).toNat : ℕ) : ℤ) : EInt) = _
  rw [Int.toNat_of_nonneg (dimensionFunction_sub_nonneg hδ p q hpq)]

/-- Comparing a sum of two integers with a third, inside the extended integers. -/
public theorem eint_int_lt_add_iff_int (a b c : ℤ) :
    (a : EInt) < (b : EInt) + (c : EInt) ↔ a < b + c := by
  simp only [WithBotTop.coe, Function.comp_apply, ← WithBot.coe_add,
    ← WithTop.coe_add, WithBot.coe_lt_coe, WithTop.coe_lt_coe]

private theorem eint_top_add_intCast (a : ℤ) : (⊤ : EInt) + (a : EInt) = ⊤ :=
  congrArg (fun z : WithTop ℤ => (z : WithBot (WithTop ℤ))) (WithTop.top_add (a : WithTop ℤ))

/-- Moving an integer across a strict inequality of extended integers, on the left. -/
public theorem eint_add_int_lt_iff (x : EInt) (a b : ℤ) :
    x + (a : EInt) < (b : EInt) ↔ x < ((b - a : ℤ) : EInt) := by
  induction x using WithBotTop.rec with
  | bot => simp [WithBotTop.coe]
  | top =>
    rw [eint_top_add_intCast]
    simp [WithBotTop.coe]
  | coe x =>
    simp only [WithBotTop.coe, Function.comp_apply, ← WithBot.coe_add,
      ← WithTop.coe_add, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
    omega

/-- Moving an integer across a strict inequality of extended integers, on the right. -/
public theorem eint_int_lt_add_iff (x : EInt) (a b : ℤ) :
    (b : EInt) < x + (a : EInt) ↔ ((b - a : ℤ) : EInt) < x := by
  induction x using WithBotTop.rec with
  | bot => simp [WithBotTop.coe]
  | top =>
    rw [eint_top_add_intCast]
    constructor <;> intro _ <;> exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
  | coe x =>
    simp only [WithBotTop.coe, Function.comp_apply, ← WithBot.coe_add,
      ← WithTop.coe_add, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
    omega

open scoped Pointwise in
private noncomputable def localizedQuotSMulTopEquiv
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    (p : PrimeSpectrum A) (a : A) :
    LocalizedModule p.asIdeal.primeCompl (QuotSMulTop a M) ≃ₗ[Localization.AtPrime p.asIdeal]
      QuotSMulTop (algebraMap A (Localization.AtPrime p.asIdeal) a)
        (LocalizedModule p.asIdeal.primeCompl M) := by
  let S := Localization.AtPrime p.asIdeal
  let f := LocalizedModule.mkLinearMap p.asIdeal.primeCompl M
  have h : Submodule.localized' S p.asIdeal.primeCompl f (a • (⊤ : Submodule A M)) =
      (algebraMap A S a) • (⊤ : Submodule S (LocalizedModule p.asIdeal.primeCompl M)) := by
    rw [← Submodule.ideal_span_singleton_smul, Submodule.localized'_smul,
      Submodule.localized'_top, ← Submodule.ideal_span_singleton_smul (algebraMap A S a) ⊤]
    congr 1
    rw [Ideal.span, Submodule.localized'_span]
    simp
  let e := Submodule.quotEquivOfEq _ _ h
  let g := e.restrictScalars A |>.toLinearMap.comp
    (Submodule.toLocalizedQuotient' S p.asIdeal.primeCompl f (a • (⊤ : Submodule A M)))
  have : IsLocalizedModule p.asIdeal.primeCompl g :=
    IsLocalizedModule.of_linearEquiv _ _ (e.restrictScalars A)
  have := IsLocalization.linearMap_compatibleSMul p.asIdeal.primeCompl (S := S)
  exact (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (QuotSMulTop a M)) g).restrictScalars S

/-- **Dividing by a nonzerodivisor drops depth and support dimension by one.** If the depth of
`(M/aM)_p` is less than `s` — in particular if `(M/aM)_p` is nonzero — then the depth and the
support dimension of `M_p` exceed those of `(M/aM)_p` by exactly one. -/
public theorem depth_supportDim_succ_of_regular_quotient
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (a : A) (ha : IsSMulRegular M a) (s : ℤ)
    (hdepth : enatToEInt
      (Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl (QuotSMulTop a M))) < (s : EInt)) :
    enatToEInt
        (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M)) =
      enatToEInt
        (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl (QuotSMulTop a M))) + 1 ∧
    krullDimToEInt
        (Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M)) =
      krullDimToEInt
        (Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl (QuotSMulTop a M))) + 1 := by
  have hnontrivial : Nontrivial (LocalizedModule p.asIdeal.primeCompl (QuotSMulTop a M)) := by
    by_contra! h
    have hd : Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl (QuotSMulTop a M)) = ⊤ := by
      simp [Module.depth, Submodule.eq_bot_of_subsingleton]
    rw [hd] at hdepth
    change (⊤ : EInt) < (s : EInt) at hdepth
    exact not_lt_of_ge le_top hdepth
  have hap : a ∈ p.asIdeal := Module.annihilator_le_of_mem_support
    (Module.mem_support_iff.mpr hnontrivial) (QuotSMulTop.mem_annihilator M a)
  have ham : algebraMap A (Localization.AtPrime p.asIdeal) a ∈
      maximalIdeal (Localization.AtPrime p.asIdeal) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p.asIdeal a).2 hap
  have hreg := ha.of_isLocalizedModule (Localization.AtPrime p.asIdeal)
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
  let e := localizedQuotSMulTopEquiv (M := M) p a
  constructor
  · rw [Module.depth_eq_depth_of_linearEquiv _ e, ← enatToEInt_add_one]
    congr 1
    exact (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append _ _).1
      _ ham hreg |>.symm
  · rw [Module.supportDim_eq_of_equiv e, ← krullDimToEInt_add_one]
    congr 1
    exact (Module.supportDim_quotSMulTop_succ_eq_supportDim hreg ham).symm

private theorem cohomologicalDimension_localization_le
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (d : ℤ) (hcd : Stacks.LocalCohomology.cohomologicalDimension A I hI ≤ d)
    (q : PrimeSpectrum A) :
    Stacks.LocalCohomology.cohomologicalDimension (Localization.AtPrime q.asIdeal)
        (I.map (algebraMap A (Localization.AtPrime q.asIdeal)))
        (hI.map (algebraMap A (Localization.AtPrime q.asIdeal))) ≤ d :=
  (Stacks.LocalCohomology.cohomologicalDimension_map_le
    (algebraMap A (Localization.AtPrime q.asIdeal)) I hI).trans hcd

/-- A value of `WithBot ℕ∞` that is neither `⊥` nor `⊤` is the natural number it looks like. -/
private theorem eq_natCast_of_ne_bot_of_lt_top {x : WithBot ℕ∞} (hbot : x ≠ ⊥) (htop : x < ⊤) :
    x = (((x.unbotD 0).toNat : ℕ) : ℕ∞) := by
  lift x to ℕ∞ using hbot
  have htop' : x ≠ ⊤ := by
    intro h
    exact htop.ne (by rw [h]; rfl)
  lift x to ℕ using htop'
  simp

private theorem krullDimToEInt_le_of_toNat_le
    {x : WithBot ℕ∞} (hx : x < ⊤) {d : ℤ}
    (hd : ((x.unbotD 0).toNat : ℤ) ≤ d) : krullDimToEInt x ≤ (d : EInt) := by
  rcases eq_or_ne x ⊥ with rfl | hbot
  · simp [krullDimToEInt]
  rw [eq_natCast_of_ne_bot_of_lt_top hbot hx]
  simpa only [krullDimToEInt, WithBot.unbotD_coe, ENat.toNat_natCast,
    WithBotTop.coe_le_coe] using hd

/-- **The cohomological dimension of a proper ideal is nonnegative.** If `V(I)` is nonempty,
then `0 ≤ cd(A, I)`: localizing at a prime of `V(I)` makes `I` land in the maximal ideal, where
Stacks 0DXF bounds the dimension of the residue field, namely `0`, by the cohomological
dimension. -/
public theorem nonneg_cohomologicalDimension_of_mem_zeroLocus
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (q : PrimeSpectrum A) (hq : q ∈ PrimeSpectrum.zeroLocus (I : Set A)) :
    0 ≤ Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing := by
  have hIP : I.map (algebraMap A (Localization.AtPrime q.asIdeal)) ≤
      maximalIdeal (Localization.AtPrime q.asIdeal) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal
      (Localization.AtPrime q.asIdeal)]
    exact Ideal.map_mono hq
  have hV : PrimeSpectrum.zeroLocus
        ((maximalIdeal (Localization.AtPrime q.asIdeal) :
          Ideal (Localization.AtPrime q.asIdeal)) : Set (Localization.AtPrime q.asIdeal)) ∩
      PrimeSpectrum.zeroLocus
        ((I.map (algebraMap A (Localization.AtPrime q.asIdeal)) :
          Ideal (Localization.AtPrime q.asIdeal)) : Set (Localization.AtPrime q.asIdeal)) =
      {closedPoint (Localization.AtPrime q.asIdeal)} := by
    rw [PrimeSpectrum.zeroLocus_eq_singleton]
    exact Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hIP)
  have hdim : ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
      maximalIdeal (Localization.AtPrime q.asIdeal)) = ((0 : ℕ) : WithBot ℕ∞) := by
    rw [ringKrullDim_quotient_maximalIdeal_eq_zero]
    simp
  have hprime : (maximalIdeal (Localization.AtPrime q.asIdeal)).IsPrime :=
    (maximalIdeal.isMaximal (Localization.AtPrime q.asIdeal)).isPrime
  have hbound := Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension'
    (Localization.AtPrime q.asIdeal) (maximalIdeal (Localization.AtPrime q.asIdeal))
    (I.map (algebraMap A (Localization.AtPrime q.asIdeal)))
    (I.fg_of_isNoetherianRing.map (algebraMap A (Localization.AtPrime q.asIdeal))) hV 0 hdim
  exact le_trans (by simpa using hbound) <| Stacks.LocalCohomology.cohomologicalDimension_map_le
    (algebraMap A (Localization.AtPrime q.asIdeal)) I I.fg_of_isNoetherianRing

/-- **Stacks 0DXF, in the form used here.** Over a Noetherian ring whose ideal `I` lies in the
Jacobson radical and satisfies `cd(A, I) ≤ d`, every prime `p` has a specialization `q ∈ V(I)`
along which the relative dimension `dim((A/p)_q)` is at most `d`: take for `q` a minimal prime
over `p + I` inside a maximal ideal containing `p`, and apply Stacks 0DXF on the localization
at `q`.

The Jacobson hypothesis is what makes `V(p) ∩ V(I)` nonempty; it holds in particular when `A`
is `I`-adically complete, which is the case
`Stacks.Algebraization.exists_specialization_dimension_le`. -/
public theorem exists_specialization_dimension_le_of_le_jacobson
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hjac : I ≤ (⊥ : Ideal A).jacobson)
    (p : PrimeSpectrum A) (d : ℤ)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing ≤ d) :
    ∃ q : PrimeSpectrum A,
      p.asIdeal ≤ q.asIdeal ∧ I ≤ q.asIdeal ∧
      krullDimToEInt
        (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
          p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) ≤ (d : EInt) := by
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  have hIm : I ≤ m := hjac.trans (sInf_le ⟨bot_le, hm⟩)
  have : m.IsMaximal := hm
  obtain ⟨q, hq, _⟩ := Ideal.exists_minimalPrimes_le (sup_le hpm hIm)
  have : q.IsPrime := hq.isPrime
  let Q : PrimeSpectrum A := ⟨q, hq.isPrime⟩
  have hpq : p.asIdeal ≤ q := le_sup_left.trans hq.le
  have hIq : I ≤ q := le_sup_right.trans hq.le
  refine ⟨Q, hpq, hIq, ?_⟩
  let B := Localization.AtPrime q
  let f := algebraMap A B
  have hpB : (p.asIdeal.map f).IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime q hpq
  have hV : PrimeSpectrum.zeroLocus (p.asIdeal.map f : Set B) ∩
      PrimeSpectrum.zeroLocus (I.map f : Set B) = {closedPoint B} := by
    rw [← PrimeSpectrum.zeroLocus_sup, ← Ideal.map_sup, ← PrimeSpectrum.zeroLocus_radical,
      IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes B q (p.asIdeal ⊔ I) hq,
      IsLocalization.AtPrime.map_eq_maximalIdeal q B]
    exact PrimeSpectrum.zeroLocus_eq_singleton (maximalIdeal B)
  have hlt : ringKrullDim (B ⧸ p.asIdeal.map f) < ⊤ :=
    (ringKrullDim_quotient_le (p.asIdeal.map f)).trans_lt (ringKrullDim_lt_top (R := B))
  have hnt : Nontrivial (B ⧸ p.asIdeal.map f) := Ideal.Quotient.nontrivial_iff.mpr hpB.ne_top
  have hbot : ringKrullDim (B ⧸ p.asIdeal.map f) ≠ ⊥ := Order.bot_lt_krullDim.ne'
  have hdim := Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension' B
    (p.asIdeal.map f) (I.map f) (I.fg_of_isNoetherianRing.map f) hV
    _ (eq_natCast_of_ne_bot_of_lt_top hbot hlt)
  exact krullDimToEInt_le_of_toNat_le hlt
    (hdim.trans (cohomologicalDimension_localization_le I I.fg_of_isNoetherianRing d hcd Q))

/-- **Stacks 0DXF, in the form used here**, for a ring complete along `I`: completeness puts `I`
inside the Jacobson radical, so
`Stacks.Algebraization.exists_specialization_dimension_le_of_le_jacobson` applies. -/
public theorem exists_specialization_dimension_le
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    (p : PrimeSpectrum A) (d : ℤ)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing ≤ d) :
    ∃ q : PrimeSpectrum A,
      p.asIdeal ≤ q.asIdeal ∧ I ≤ q.asIdeal ∧
      krullDimToEInt
        (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
          p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) ≤ (d : EInt) :=
  exists_specialization_dimension_le_of_le_jacobson I
    (IsAdicComplete.le_jacobson_bot I) p d hcd

private theorem exists_isSMulRegular_mem_of_not_le_associatedPrimes
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a : Ideal A) (ha : ∀ p ∈ associatedPrimes A M, ¬ a ≤ p) :
    ∃ f ∈ a, IsSMulRegular M f := by
  have hnot : ¬ (a : Set A) ⊆ ⋃ p ∈ associatedPrimes A M, (p : Set A) := by
    intro h
    obtain ⟨p, hp, hap⟩ :=
      (a.subset_union_prime_finite (associatedPrimes.finite A M)
        (f := id) 0 0 (fun p hp _ _ => hp.1)).1 h
    exact ha p hp hap
  obtain ⟨f, hfa, hf⟩ := Set.not_subset.mp hnot
  refine ⟨f, hfa, IsSMulRegular.of_right_eq_zero_of_smul ?_⟩
  rw [biUnion_associatedPrimes_eq_zero_divisors A M] at hf
  intro m hm
  by_contra hne
  exact hf ⟨m, hne, hm⟩

private theorem not_le_of_not_mem_associatedSubset
    {A : Type u} [CommRing A] (I J J₀ : Ideal A)
    (hV : PrimeSpectrum.zeroLocus (J₀ : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (p : PrimeSpectrum A) (hp : p ∉ associatedSubset I J) :
    ¬ J₀ ≤ p.asIdeal := by
  intro hJ₀
  apply hp
  intro q hq
  rw [← hV]
  exact ⟨hJ₀.trans hq.1, hq.2⟩

/-- **A nonzerodivisor in a prescribed ideal.** If every associated prime of `M` lies outside
`V(I)` and outside `T`, and no associated prime contains `a`, then `a * (J₀ I) ^ t` contains a
nonzerodivisor on `M`. -/
public theorem exists_isSMulRegular_mem_mul_pow
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a I J J₀ : Ideal A) (t : ℕ)
    (hV : PrimeSpectrum.zeroLocus (J₀ : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (hass : ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M →
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) ∧
        p ∉ associatedSubset I J)
    (ha : ∀ p ∈ associatedPrimes A M, ¬ a ≤ p) :
    ∃ f ∈ a * (J₀ * I) ^ t, IsSMulRegular M f := by
  apply exists_isSMulRegular_mem_of_not_le_associatedPrimes
  intro p hp hle
  have : p.IsPrime := hp.1
  rcases (Ideal.IsPrime.mul_le hp.1).mp hle with h | h
  · exact ha p hp h
  have hprod : ¬ J₀ * I ≤ p := by
    intro hprod
    rcases (Ideal.IsPrime.mul_le hp.1).mp hprod with hJ | hI
    · exact not_le_of_not_mem_associatedSubset I J J₀ hV ⟨p, hp.1⟩
        (hass ⟨p, hp.1⟩ hp).2 hJ
    · exact (hass ⟨p, hp.1⟩ hp).1 hI
  cases t with
  | zero => simpa using (hp.1.ne_top (top_le_iff.mp (by simpa using h)))
  | succ t => exact hprod ((Ideal.IsPrime.pow_le_iff (Nat.succ_ne_zero t)).mp h)

/-- **The maximal submodule supported in a specialization-closed set.** For a finite module `M`
over a Noetherian ring and a set `S` of primes closed under specialization, there is a submodule
`N` with support inside `S` such that no associated prime of `M/N` lies in `S`. -/
public theorem exists_submodule_support_subset_and_associatedPrimes_quotient
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (S : Set (PrimeSpectrum A))
    (hS : ∀ p ∈ S, ∀ q : PrimeSpectrum A, p ≤ q → q ∈ S) :
    ∃ N : Submodule A M, Module.support A N ⊆ S ∧
      ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A (M ⧸ N) → p ∉ S := by
  have hb : Module.support A (⊥ : Submodule A M) ⊆ S := by
    rw [Module.support_eq_empty_iff.mpr (inferInstance : Subsingleton (⊥ : Submodule A M))]
    exact Set.empty_subset _
  obtain ⟨N, hN, hmax⟩ := (set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian A M))
    {N : Submodule A M | Module.support A N ⊆ S} ⟨⊥, hb⟩
  refine ⟨N, hN, ?_⟩
  intro p hp hpS
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp
  obtain ⟨hp, y, hy⟩ := hp
  obtain ⟨x, rfl⟩ := N.mkQ_surjective y
  let P := N ⊔ Submodule.span A {x}
  have hNP : N ≤ P := le_sup_left
  have hQ : Module.support A (P ⧸ N.submoduleOf P) ⊆ S := by
    have hh : (⊥ : Submodule A (M ⧸ N)).colon {N.mkQ x} =
        Module.annihilator A (P ⧸ N.submoduleOf P) := by
      ext a
      simp only [Submodule.mem_colon_singleton, Submodule.mem_bot,
        Module.mem_annihilator]
      constructor
      · intro ha z
        obtain ⟨z, rfl⟩ := (N.submoduleOf P).mkQ_surjective z
        obtain ⟨n, hn, z', hz', he⟩ := Submodule.mem_sup.mp z.property
        obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hz'
        change (N.submoduleOf P).mkQ (a • z) = 0
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        change a • z.val ∈ N
        rw [← he, smul_add]
        apply N.add_mem (N.smul_mem a hn)
        rw [smul_comm]
        exact N.smul_mem b ((Submodule.Quotient.mk_eq_zero _).mp (by
          simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_smul] using ha))
      · intro ha
        have h := ha ((N.submoduleOf P).mkQ
          ⟨x, (le_sup_right : Submodule.span A {x} ≤ P)
            (Submodule.mem_span_singleton_self x)⟩)
        rw [← map_smul] at h
        have hx : a • x ∈ N := (Submodule.Quotient.mk_eq_zero (N.submoduleOf P)).mp h
        simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_smul] using
          ((Submodule.Quotient.mk_eq_zero N).mpr hx)
    rw [Module.support_eq_zeroLocus, ← hh, ← hy]
    exact fun q hq => hS p hpS q hq
  have hP : Module.support A P ⊆ S := by
    rw [Module.support_of_exact (LinearMap.exact_subtype_mkQ (N.submoduleOf P))
      (N.submoduleOf P).injective_subtype (N.submoduleOf P).mkQ_surjective,
      (Submodule.submoduleOfEquivOfLe hNP).support_eq]
    exact Set.union_subset hN hQ
  have hx : x ∉ N := by
    intro hx
    have hz : N.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hx
    apply hp.ne_top
    rw [hy, hz]
    simp
  exact hmax P hP (lt_of_le_of_ne hNP (fun he => hx (he.symm ▸
    ((le_sup_right : Submodule.span A {x} ≤ P) (Submodule.mem_span_singleton_self x) : x ∈ P))))

/-- At a prime outside the support of `N`, the localizations of `M` and of `M/N` agree. -/
public noncomputable def localizedQuotientEquivOfNotMemSupport
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    (N : Submodule A M) (p : PrimeSpectrum A) (hp : p ∉ Module.support A N) :
    LocalizedModule p.asIdeal.primeCompl M ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule p.asIdeal.primeCompl (M ⧸ N) := by
  let S := p.asIdeal.primeCompl
  have : Subsingleton (LocalizedModule S N) := Module.notMem_support_iff.mp hp
  let f := IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S (M ⧸ N)) N.mkQ
  have hf : Function.Bijective f := by
    refine ⟨?_, IsLocalizedModule.map_surjective S _ _ N.mkQ N.mkQ_surjective⟩
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    change x = 0
    obtain ⟨y, hy⟩ := (LocalizedModule.map_exact S N.subtype N.mkQ
      (LinearMap.exact_subtype_mkQ N) x).mp hx
    rw [← hy, Subsingleton.elim y 0, map_zero]
  have := IsLocalization.linearMap_compatibleSMul S (S := Localization.AtPrime p.asIdeal)
  exact (LinearEquiv.ofBijective f hf).restrictScalars (Localization.AtPrime p.asIdeal)

private theorem zeroLocus_inter_eq_empty_of_adic_trace_eq
    {A : Type*} [CommRing A] (I J J' p : Ideal A) [IsAdicComplete I A]
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (hp : ¬ ∃ q : PrimeSpectrum A,
      q ∈ (PrimeSpectrum.zeroLocus (p : Set A) ∩ PrimeSpectrum.zeroLocus (J : Set A)) ∩
        PrimeSpectrum.zeroLocus (I : Set A)) :
    PrimeSpectrum.zeroLocus (p : Set A) ∩ PrimeSpectrum.zeroLocus (J' : Set A) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
  have hIm : I ≤ m := (IsAdicComplete.le_jacobson_bot I).trans (sInf_le ⟨bot_le, hm⟩)
  let Q : PrimeSpectrum A := ⟨m, hm.isPrime⟩
  have hQ : Q ∈ PrimeSpectrum.zeroLocus (J' : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A) := ⟨hq.2.trans hqm, hIm⟩
  rw [hV] at hQ
  exact hp ⟨Q, ⟨⟨hq.1.trans hqm, hQ.1⟩, hQ.2⟩⟩

/-- **Local cohomology of a module supported in the bad locus is derived complete.** If every
prime in the support of `M` lies in `V(I)`, or in `T`, or has no specialization in
`V(J) ∩ V(I)`, then after shrinking `J` the local cohomology `RΓ_{V(J')}(M)` is derived
`I`-complete. This is the part of the inductive step of Stacks 0EFL that discards the submodule
of `M` supported in the bad locus. -/
public theorem exists_ideal_isDerivedComplete_localCohomology_of_support
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) [IsAdicComplete I A]
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hM : ∀ p ∈ Module.support A M,
      p ∈ PrimeSpectrum.zeroLocus (I : Set A) ∨ p ∈ associatedSubset I J ∨
        ¬ ∃ q : PrimeSpectrum A,
          q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
            PrimeSpectrum.zeroLocus (J : Set A)) ∩ PrimeSpectrum.zeroLocus (I : Set A)) :
    ∃ J₀ : Ideal A, J₀ ≤ J ∧
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ∧
      ∀ J' : Ideal A, J' ≤ J₀ →
        PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) →
        IsDerivedComplete I ((Dualizing.localCohomologyFunctor A J'
          J'.fg_of_isNoetherianRing).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj := by
  let good (p : PrimeSpectrum A) : Prop :=
    p ∈ PrimeSpectrum.zeroLocus (I : Set A) ∨ p ∈ associatedSubset I J ∨
      ¬ ∃ q : PrimeSpectrum A,
        q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
          PrimeSpectrum.zeroLocus (J : Set A)) ∩ PrimeSpectrum.zeroLocus (I : Set A)
  let motive (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N] : Prop :=
    (∀ p ∈ Module.support A N, good p) →
    ∃ J₀ : Ideal A, J₀ ≤ J ∧
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ∧
      ∀ J' : Ideal A, J' ≤ J₀ →
        PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) →
        IsDerivedComplete I ((Dualizing.localCohomologyFunctor A J'
          J'.fg_of_isNoetherianRing).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A N))).obj
  apply IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime
    (motive := motive) A (inferInstance : Module.Finite A M) ?_ ?_ ?_ hM
  · intro N _ _ _ _ _
    refine ⟨J, le_rfl, rfl, fun J' _ _ => ?_⟩
    exact isDerivedComplete_localCohomology_of_le_annihilator I J' J'.fg_of_isNoetherianRing
      (ModuleCat.of A N) fun _ _ => Module.mem_annihilator.mpr fun _ => Subsingleton.elim _ _
  · intro N _ _ _ p e hs
    have hann : Module.annihilator A N = p.asIdeal :=
      e.annihilator_eq.trans Ideal.annihilator_quotient
    have hp : p ∈ Module.support A N := by
      rw [Module.mem_support_iff_of_finite, hann]
    rcases hs p hp with hpI | hpT | hpU
    · refine ⟨J, le_rfl, rfl, fun J' _ _ => ?_⟩
      apply isDerivedComplete_localCohomology_of_le_annihilator I J'
        J'.fg_of_isNoetherianRing (ModuleCat.of A N)
      change I ≤ p.asIdeal at hpI
      simpa only [hann] using hpI
    · refine ⟨J ⊓ p.asIdeal, inf_le_left, ?_, fun J' hJ' _ => ?_⟩
      · rw [PrimeSpectrum.zeroLocus_inf, Set.union_inter_distrib_right]
        exact Set.union_eq_left.mpr hpT
      · apply isDerivedComplete_localCohomology_of_isIPowerTorsion I J'
          (ModuleCat.of A N) ?_
        intro n
        refine ⟨1, by omega, fun a ha => ?_⟩
        have ha' : a ∈ Module.annihilator A N := by
          rw [hann]
          exact (hJ'.trans inf_le_right) (by simpa only [pow_one] using ha)
        exact Module.mem_annihilator.mp ha' n
    · refine ⟨J, le_rfl, rfl, fun J' _ hV => ?_⟩
      apply isDerivedComplete_localCohomology_of_disjoint_support I J'
        J'.fg_of_isNoetherianRing (ModuleCat.of A N)
      rw [hann]
      exact zeroLocus_inter_eq_empty_of_adic_trace_eq I J J' p.asIdeal hV hpU
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hex h₁ h₃ hs
    obtain ⟨J₁, hJ₁, hV₁, hc₁⟩ := h₁ fun p hp =>
      hs p (Module.support_subset_of_injective f hf hp)
    obtain ⟨J₃, hJ₃, hV₃, hc₃⟩ := h₃ fun p hp =>
      hs p (Module.support_subset_of_surjective g hg hp)
    refine ⟨J₁ ⊓ J₃, inf_le_left.trans hJ₁, ?_, fun J' hJ' hV => ?_⟩
    · rw [PrimeSpectrum.zeroLocus_inf, Set.union_inter_distrib_right, hV₁, hV₃,
        Set.union_self]
    · let S := ModuleCat.shortComplexOfCompEqZero f g (by
        ext x
        exact hex.apply_apply_eq_zero x)
      exact isDerivedComplete_localCohomology_of_shortExact I J'
        J'.fg_of_isNoetherianRing S (ModuleCat.shortComplex_shortExact S hex hf hg)
        (hc₁ J' (hJ'.trans inf_le_left) hV) (hc₃ J' (hJ'.trans inf_le_right) hV)

end Stacks.Algebraization

end
