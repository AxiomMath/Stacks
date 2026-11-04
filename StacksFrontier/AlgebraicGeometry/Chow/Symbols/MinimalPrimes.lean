module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.SupportLength
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Invariance
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.ShortExact
public import StacksFrontier.RingTheory.CohenMacaulay.Dimension
public import StacksFrontier.RingTheory.Length.Additivity

/-!
# The symbol of a module from its minimal support primes

For a finite module of one-dimensional support over a Noetherian local ring, the symbol of two
nonzerodivisors is the product of the symbols of the quotient rings at the minimal points of its
support, each raised to the length of the localized module there.

## Main results

* `AlgebraicGeometry.moduleSymbol_eq_finprod_minimal_support` computes the module symbol from
  the symbols of its minimal support primes.

## Implementation notes

The quotient-ring regularity and dimension witnesses are included in the conclusion. They
follow from the hypotheses and are needed to form each quotient-ring symbol; they are not
additional assumptions. The product is indexed by the subtype of minimal points of the support.
Localization length, valued in `ℕ∞`, is converted to a natural-number exponent.

## References

* [Stacks Project, Tag 02Q5](https://stacks.math.columbia.edu/tag/02Q5)
-/

@[expose] public section

noncomputable section

namespace AlgebraicGeometry

universe u v

/-- The quotient by a minimal support prime has one-dimensional support. -/
private lemma supportDim_quotient_eq_one_of_minimal_support
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Module.supportDim R M = 1) (q : PrimeSpectrum R)
    (hq : Minimal (· ∈ Module.support R M) q) :
    Module.supportDim R (R ⧸ q.asIdeal) = 1 := by
  have hsub : Module.support R (R ⧸ q.asIdeal) ⊆ Module.support R M := by
    intro r hr
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient] at hr
    exact Module.mem_support_mono hr hq.1
  have hle : Module.supportDim R (R ⧸ q.asIdeal) ≤ 1 := by
    show Order.krullDim (Module.support R (R ⧸ q.asIdeal)) ≤ 1
    exact (Order.krullDim_le_of_strictMono (Set.inclusion hsub) (fun _ _ h => h)).trans hM.le
  have hlt : q < IsLocalRing.closedPoint R :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal q.isPrime.ne_top)
      ((Set.ext_iff.mp (minimal_support_eq_nonclosed hM) q).mp hq).2
  have hpos : 0 < Module.supportDim R (R ⧸ q.asIdeal) := by
    show 0 < Order.krullDim (Module.support R (R ⧸ q.asIdeal))
    apply Order.krullDim_pos_iff.mpr
    have hqQ : q ∈ Module.support R (R ⧸ q.asIdeal) := by
      rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
      exact (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl
    exact ⟨⟨q, hqQ⟩,
      ⟨IsLocalRing.closedPoint R, Module.mem_support_mono hlt.le hqQ⟩, hlt⟩
  cases hdimQ : Module.supportDim R (R ⧸ q.asIdeal) with
  | bot =>
    rw [hdimQ] at hpos
    exact False.elim (not_lt_of_ge (show (0 : WithBot ℕ∞) ≥ ⊥ by simp) hpos)
  | coe d =>
    cases d with
    | top =>
      have htople : (⊤ : WithBot ℕ∞) ≤ 1 := by
        simpa only [hdimQ, WithBot.coe_top] using hle
      have hEq : (⊤ : WithBot ℕ∞) = 1 := le_antisymm htople le_top
      exact False.elim (ENat.one_ne_top (WithBot.coe_eq_top.mp hEq.symm))
    | coe n =>
      have hle' : ((n : ℕ∞) : WithBot ℕ∞) ≤ 1 := by
        simpa only [hdimQ] using hle
      have hpos' : (0 : WithBot ℕ∞) < ((n : ℕ∞) : WithBot ℕ∞) := by
        simpa only [hdimQ] using hpos
      have hnle : n ≤ 1 := by exact_mod_cast hle'
      have hnpos : 0 < n := by exact_mod_cast hpos'
      have hn : n = 1 := by omega
      show ((n : ℕ∞) : WithBot ℕ∞) = ((1 : ℕ) : WithBot ℕ∞)
      exact congrArg (fun k : ℕ => ((k : ℕ∞) : WithBot ℕ∞)) hn

/-- The residue field has zero-dimensional support. -/
private lemma supportDim_residueField_eq_zero (R : Type*) [CommRing R] [IsLocalRing R] :
    Module.supportDim R (R ⧸ IsLocalRing.maximalIdeal R) = 0 := by
  rw [Module.supportDim_quotient_eq_ringKrullDim, ringKrullDim_quotient,
    PrimeSpectrum.zeroLocus_eq_singleton]
  apply Order.krullDim_eq_zero

/-- An element acting regularly acts regularly on the quotient by a minimal support prime. -/
private lemma regular_quotient_of_minimal_support
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) (hx : IsSMulRegular M x) (q : PrimeSpectrum R)
    (hq : Minimal (· ∈ Module.support R M) q) :
    IsSMulRegular (R ⧸ q.asIdeal) x := by
  have hxq : x ∉ q.asIdeal :=
    hx.notMem_of_mem_minimalPrimes ((minimal_support_iff q).mp hq)
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro z hz
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hmul : x * r ∈ q.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul] using hz
  exact (q.isPrime.mem_or_mem hmul).resolve_left hxq

/-- A module whose support has dimension at most zero is supported at the closed point. -/
private lemma support_subset_closed_of_supportDim_le_zero
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : Module.supportDim R M ≤ 0) :
    Module.support R M ⊆ {IsLocalRing.closedPoint R} := by
  intro q hq
  have hmax : IsMax (⟨q, hq⟩ : Module.support R M) :=
    (Order.krullDim_nonpos_iff_forall_isMax.mp hM) ⟨q, hq⟩
  have hqle : q ≤ IsLocalRing.closedPoint R :=
    IsLocalRing.le_maximalIdeal q.isPrime.ne_top
  have hclosed : IsLocalRing.closedPoint R ∈ Module.support R M :=
    Module.mem_support_mono hqle hq
  have hle : (⟨q, hq⟩ : Module.support R M) ≤ ⟨IsLocalRing.closedPoint R, hclosed⟩ := hqle
  have hge : (⟨IsLocalRing.closedPoint R, hclosed⟩ : Module.support R M) ≤ ⟨q, hq⟩ := hmax hle
  exact Set.mem_singleton_iff.mpr (congrArg Subtype.val (le_antisymm hle hge))

/-- Support dimension at most zero passes to the middle term of a short exact sequence. -/
private lemma supportDim_le_zero_of_exact
    {R A B C : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hA : Module.supportDim R A ≤ 0) (hC : Module.supportDim R C ≤ 0) :
    Module.supportDim R B ≤ 0 := by
  have hsup : Module.support R B ⊆ {IsLocalRing.closedPoint R} := by
    rw [Module.support_of_exact hfg hf hg]
    exact Set.union_subset
      (support_subset_closed_of_supportDim_le_zero hA)
      (support_subset_closed_of_supportDim_le_zero hC)
  show Order.krullDim (Module.support R B) ≤ 0
  have : Subsingleton (Module.support R B) := ⟨fun x y => Subtype.ext <|
    (Set.mem_singleton_iff.mp (hsup x.property)).trans
      (Set.mem_singleton_iff.mp (hsup y.property)).symm⟩
  exact Order.krullDim_nonpos_of_subsingleton

/-- Regularity of a scalar transfers along an isomorphism. -/
private lemma regular_of_linearEquiv
    {R M N : Type*} [CommSemiring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) {x : R}
    (h : IsSMulRegular M x) : IsSMulRegular N x := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro y hy
  have hy' : x • e.symm y = 0 := by
    simpa only [map_smul, map_zero] using congrArg e.symm hy
  have hz0 : e.symm y = 0 := h.right_eq_zero_of_smul hy'
  exact e.symm.injective (by simpa using hz0)

/-- The kernel of an injective linear map has support dimension at most zero. -/
private lemma supportDim_ker_le_zero_of_injective
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Module.supportDim R (LinearMap.ker f) ≤ 0 := by
  have : Subsingleton (LinearMap.ker f) := by
    rw [LinearMap.ker_eq_bot.mpr hf]
    infer_instance
  rw [Module.supportDim_eq_bot_of_subsingleton]
  exact bot_le

/-- The cokernel of a surjective linear map has support dimension at most zero. -/
private lemma supportDim_coker_le_zero_of_surjective
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.supportDim R (N ⧸ LinearMap.range f) ≤ 0 := by
  have : Subsingleton (N ⧸ LinearMap.range f) := by
    rw [LinearMap.range_eq_top.mpr hf]
    infer_instance
  rw [Module.supportDim_eq_bot_of_subsingleton]
  exact bot_le

/-- Isomorphic modules have the same symbol. -/
private lemma moduleSymbol_eq_of_linearEquiv
    {A M N : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (e : M ≃ₗ[A] N) (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (ha' : IsSMulRegular N a) (hb' : IsSMulRegular N b)
    (hdim : Module.supportDim A M = 1) (hdim' : Module.supportDim A N = 1) :
    moduleSymbol a b ha hb hdim = moduleSymbol a b ha' hb' hdim' := by
  apply moduleSymbol_eq_of_ker_coker_supportDim_le_zero e.toLinearMap a b
    ha hb ha' hb' hdim hdim'
  · exact supportDim_ker_le_zero_of_injective _ e.injective
  · exact supportDim_coker_le_zero_of_surjective _ e.surjective

/-- Regularity of a scalar restricts to a submodule. -/
private lemma regular_submodule
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (N : Submodule A M) {a : A} (ha : IsSMulRegular M a) :
    IsSMulRegular N a := by
  let : AddCommGroup N := N.toAddSubgroup.toAddCommGroup
  refine IsSMulRegular.of_right_eq_zero_of_smul (R := A) (M := N) (r := a) ?_
  exact fun x hx => Subtype.ext <|
    ha.right_eq_zero_of_smul (by simpa using congrArg (fun y : N => (y : M)) hx)

/-- A dimension at most one that is not one is at most zero. -/
private lemma supportDim_le_zero_of_le_one_of_ne_one {d : WithBot ℕ∞}
    (hd : d ≤ 1) (hne : d ≠ 1) : d ≤ 0 := by
  cases h : d with
  | bot => exact bot_le
  | coe e =>
    cases e with
    | top =>
      have htop : (⊤ : WithBot ℕ∞) ≤ 1 := by simpa only [h, WithBot.coe_top] using hd
      have heq : (⊤ : WithBot ℕ∞) = 1 := le_antisymm htop le_top
      exact False.elim (hne (by simpa only [h, WithBot.coe_top] using heq))
    | coe n =>
      rw [h] at hd
      have hnle : n ≤ 1 := by exact_mod_cast hd
      have hnne : n ≠ 1 := by
        intro heq
        apply hne
        simp [h, heq]
      have hn : n = 0 := by omega
      simp [hn]

/-- The symbol of a module, or one when its support is not one-dimensional. -/
private noncomputable def moduleSymbolIfOne
    {A N : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (a b : A) (ha : IsSMulRegular N a) (hb : IsSMulRegular N b) :
    (IsLocalRing.ResidueField A)ˣ :=
  if hdim : Module.supportDim A N = 1 then moduleSymbol a b ha hb hdim else 1

/-- The symbol of the quotient by a prime, or one when that prime is not minimal in the support. -/
private noncomputable def primeFactorSymbol
    {A M : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hdim : Module.supportDim A M = 1) (q : PrimeSpectrum A) :
    (IsLocalRing.ResidueField A)ˣ := by
  classical
  exact if hq : Minimal (· ∈ Module.support A M) q then
    moduleSymbol a b
      (regular_quotient_of_minimal_support a ha q hq)
      (regular_quotient_of_minimal_support b hb q hq)
      (supportDim_quotient_eq_one_of_minimal_support hdim q hq)
  else 1

/-- One step of a prime filtration: enlarging a submodule by a prime quotient multiplies the
symbol by that prime's factor. -/
private theorem moduleSymbol_subquotient_step
    {A M : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N₁ N₂ : Submodule A M) (hle : N₁ ≤ N₂) (q : PrimeSpectrum A)
    (e : (↥N₂ ⧸ N₁.submoduleOf N₂) ≃ₗ[A] A ⧸ q.asIdeal)
    (hqM : q ∈ Module.support A M)
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hdimM : Module.supportDim A M = 1)
    (hdimN₂ : Module.supportDim A ↥N₂ ≤ 1) :
    moduleSymbolIfOne a b (regular_submodule N₂ ha) (regular_submodule N₂ hb) =
      moduleSymbolIfOne a b (regular_submodule N₁ ha) (regular_submodule N₁ hb) *
        primeFactorSymbol a b ha hb hdimM q := by
  classical
  let U : Submodule A ↥N₂ := N₁.submoduleOf N₂
  let eU : ↥U ≃ₗ[A] ↥N₁ := Submodule.comapSubtypeEquivOfLe hle
  let T := ↥N₂ ⧸ U
  have ha₁ := regular_submodule N₁ ha
  have hb₁ := regular_submodule N₁ hb
  have ha₂ := regular_submodule N₂ ha
  have hb₂ := regular_submodule N₂ hb
  have hdimN₁ : Module.supportDim A ↥N₁ ≤ 1 :=
    (Module.supportDim_le_of_injective N₁.subtype N₁.subtype_injective).trans hdimM.le
  have hdimUle : Module.supportDim A ↥U ≤ 1 := by
    rw [Module.supportDim_eq_of_equiv eU]
    exact hdimN₁
  have hdimT : Module.supportDim A T =
      Module.supportDim A (A ⧸ q.asIdeal) := Module.supportDim_eq_of_equiv e
  by_cases hq : Minimal (· ∈ Module.support A M) q
  · have hdimT' : Module.supportDim A T = 1 :=
      hdimT.trans (supportDim_quotient_eq_one_of_minimal_support hdimM q hq)
    have haQ := regular_quotient_of_minimal_support a ha q hq
    have hbQ := regular_quotient_of_minimal_support b hb q hq
    have haT := regular_of_linearEquiv e.symm haQ
    have hbT := regular_of_linearEquiv e.symm hbQ
    have hTeq := moduleSymbol_eq_of_linearEquiv e a b haT hbT haQ hbQ
      hdimT' (supportDim_quotient_eq_one_of_minimal_support hdimM q hq)
    have hdimN₂' : Module.supportDim A ↥N₂ = 1 := by
      apply le_antisymm hdimN₂
      rw [← hdimT']
      exact Module.supportDim_le_of_surjective U.mkQ U.mkQ_surjective
    by_cases hdimN₁' : Module.supportDim A ↥N₁ = 1
    · have hdimU : Module.supportDim A ↥U = 1 :=
        (Module.supportDim_eq_of_equiv eU).trans hdimN₁'
      have hseq := moduleSymbol_short_exact U.subtype U.mkQ
        U.subtype_injective U.mkQ_surjective (LinearMap.exact_subtype_mkQ U)
        a b (regular_submodule U ha₂) (regular_submodule U hb₂) ha₂ hb₂ haT hbT
        hdimU hdimN₂' hdimT'
      have hUeq := moduleSymbol_eq_of_linearEquiv eU a b
        (regular_submodule U ha₂) (regular_submodule U hb₂) ha₁ hb₁ hdimU hdimN₁'
      simpa [moduleSymbolIfOne, primeFactorSymbol, hq, hdimN₁', hdimN₂',
        hdimU, hdimT', hUeq, hTeq] using hseq
    · have hdimU₀ : Module.supportDim A ↥U ≤ 0 :=
        supportDim_le_zero_of_le_one_of_ne_one hdimUle
          (by
            intro h
            exact hdimN₁' ((Module.supportDim_eq_of_equiv eU).symm.trans h))
      have hker : Module.supportDim A (LinearMap.ker U.mkQ) ≤ 0 := by
        rw [U.ker_mkQ]
        exact hdimU₀
      have hcmp := moduleSymbol_eq_of_ker_coker_supportDim_le_zero
        U.mkQ a b ha₂ hb₂ haT hbT hdimN₂' hdimT' hker
        (supportDim_coker_le_zero_of_surjective _ U.mkQ_surjective)
      simpa [moduleSymbolIfOne, primeFactorSymbol, hq, hdimN₂', hdimN₁', hdimT', hTeq]
        using hcmp.trans hTeq
  · have hqclosed : q = IsLocalRing.closedPoint A := by
      by_contra hne
      exact hq ((Set.ext_iff.mp (minimal_support_eq_nonclosed hdimM) q).mpr ⟨hqM, hne⟩)
    have hdimT' : Module.supportDim A T = 0 := by
      rw [hdimT, hqclosed]
      exact supportDim_residueField_eq_zero A
    by_cases hdimN₂' : Module.supportDim A ↥N₂ = 1
    · have hdimN₁' : Module.supportDim A ↥N₁ = 1 := by
        by_contra hne
        have hdimN₁₀ := supportDim_le_zero_of_le_one_of_ne_one hdimN₁ hne
        have hdimU₀ : Module.supportDim A ↥U ≤ 0 := by
          rw [Module.supportDim_eq_of_equiv eU]
          exact hdimN₁₀
        have hdimN₂₀ := supportDim_le_zero_of_exact U.subtype U.mkQ
          U.subtype_injective U.mkQ_surjective (LinearMap.exact_subtype_mkQ U)
          hdimU₀ (le_of_eq hdimT')
        rw [hdimN₂'] at hdimN₂₀
        norm_num at hdimN₂₀
      have hdimU : Module.supportDim A ↥U = 1 :=
        (Module.supportDim_eq_of_equiv eU).trans hdimN₁'
      have eC : (↥N₂ ⧸ LinearMap.range U.subtype) ≃ₗ[A] T :=
        Submodule.quotEquivOfEq (LinearMap.range U.subtype) U U.range_subtype
      have hcoker : Module.supportDim A (↥N₂ ⧸ LinearMap.range U.subtype) ≤ 0 := by
        rw [Module.supportDim_eq_of_equiv eC]
        exact le_of_eq hdimT'
      have hcmp := moduleSymbol_eq_of_ker_coker_supportDim_le_zero
        U.subtype a b (regular_submodule U ha₂) (regular_submodule U hb₂) ha₂ hb₂
        hdimU hdimN₂' (supportDim_ker_le_zero_of_injective _ U.subtype_injective) hcoker
      have hUeq := moduleSymbol_eq_of_linearEquiv eU a b
        (regular_submodule U ha₂) (regular_submodule U hb₂) ha₁ hb₁ hdimU hdimN₁'
      simpa [moduleSymbolIfOne, primeFactorSymbol, hq, hdimN₁', hdimN₂', hdimU,
        hUeq] using hcmp.symm
    · have hdimN₂₀ := supportDim_le_zero_of_le_one_of_ne_one hdimN₂ hdimN₂'
      have hU₀ : Module.supportDim A ↥U ≤ 0 :=
        (Module.supportDim_le_of_injective U.subtype U.subtype_injective).trans hdimN₂₀
      have hN₁' : Module.supportDim A ↥N₁ ≠ 1 := by
        intro heq
        have hUone : Module.supportDim A ↥U = 1 :=
          (Module.supportDim_eq_of_equiv eU).trans heq
        exact (not_le_of_gt (by rw [hUone]; norm_num)) hU₀
      simp [moduleSymbolIfOne, primeFactorSymbol, hq, hN₁', hdimN₂']

/-- The symbol of the top of a prime filtration is the product of the factors of its steps. -/
private theorem moduleSymbol_filtration_product
    {A M : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] {n : ℕ}
    (N : Fin (n + 1) → Submodule A M) (p : Fin n → PrimeSpectrum A)
    (hle : ∀ i : Fin n, N i.castSucc ≤ N i.succ)
    (hquot : ∀ i : Fin n,
      Nonempty ((↥(N i.succ) ⧸ (N i.castSucc).submoduleOf (N i.succ)) ≃ₗ[A]
        A ⧸ (p i).asIdeal))
    (hbot : N 0 = ⊥)
    (hp : ∀ i : Fin n, p i ∈ Module.support A M)
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hdim : Module.supportDim A M = 1) :
    moduleSymbolIfOne a b
        (regular_submodule (N (Fin.last n)) ha)
        (regular_submodule (N (Fin.last n)) hb) =
      ∏ i : Fin n, primeFactorSymbol a b ha hb hdim (p i) := by
  classical
  induction n with
  | zero =>
      have hbot0 : N (Fin.last 0) = ⊥ := by simpa using hbot
      rw [moduleSymbolIfOne, hbot0]
      have hdimNe : Module.supportDim A ↥(⊥ : Submodule A M) ≠ 1 := by
        rw [Module.supportDim_eq_bot_of_subsingleton]
        norm_num
      simp [hdimNe]
  | succ n ih =>
      let N' : Fin (n + 1) → Submodule A M := fun i => N i.castSucc
      let p' : Fin n → PrimeSpectrum A := fun i => p i.castSucc
      have hprev := ih N' p' (fun i => hle i.castSucc) (fun i => hquot i.castSucc)
        (by simpa [N'] using hbot) (fun i => hp i.castSucc)
      let j : Fin (n + 1) := Fin.last n
      have hstep := moduleSymbol_subquotient_step (N j.castSucc) (N j.succ)
        (hle j) (p j) (Classical.choice (hquot j)) (hp j) a b ha hb hdim
        ((Module.supportDim_le_of_injective (N j.succ).subtype
          (N j.succ).subtype_injective).trans hdim.le)
      have hrec :
          moduleSymbolIfOne a b
            (regular_submodule (N j.castSucc) ha)
            (regular_submodule (N j.castSucc) hb) =
          ∏ i : Fin n, primeFactorSymbol a b ha hb hdim (p i.castSucc) := by
        simpa [N', p', j] using hprev
      simpa only [Fin.prod_univ_castSucc, j] using hstep.trans (by rw [hrec])

/-- **Stacks Project, Tag 02Q5.** The symbol of a finite one-dimensional module is the product
of the symbols of its minimal support quotients, weighted by localization lengths. -/
@[stacks 02Q5]
theorem moduleSymbol_eq_finprod_minimal_support
    {A : Type u} {M : Type v} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hdim : Module.supportDim A M = 1) :
    ∃ (haq : ∀ q : {q : PrimeSpectrum A // Minimal (· ∈ Module.support A M) q},
        IsSMulRegular (A ⧸ q.1.asIdeal) a),
    ∃ (hbq : ∀ q : {q : PrimeSpectrum A // Minimal (· ∈ Module.support A M) q},
        IsSMulRegular (A ⧸ q.1.asIdeal) b),
    ∃ (hdimq : ∀ q : {q : PrimeSpectrum A // Minimal (· ∈ Module.support A M) q},
        Module.supportDim A (A ⧸ q.1.asIdeal) = 1),
      moduleSymbol a b ha hb hdim =
        ∏ᶠ q : {q : PrimeSpectrum A // Minimal (· ∈ Module.support A M) q},
          (moduleSymbol (M := A ⧸ q.1.asIdeal) a b
            (haq q) (hbq q) (hdimq q)) ^
            (Module.length (Localization.AtPrime q.1.asIdeal)
              (LocalizedModule q.1.asIdeal.primeCompl M)).toNat := by
  classical
  let Q := {q : PrimeSpectrum A // Minimal (· ∈ Module.support A M) q}
  let haq : ∀ q : Q, IsSMulRegular (A ⧸ q.1.asIdeal) a :=
    fun q => regular_quotient_of_minimal_support a ha q.1 q.2
  let hbq : ∀ q : Q, IsSMulRegular (A ⧸ q.1.asIdeal) b :=
    fun q => regular_quotient_of_minimal_support b hb q.1 q.2
  let hdimq : ∀ q : Q, Module.supportDim A (A ⧸ q.1.asIdeal) = 1 :=
    fun q => supportDim_quotient_eq_one_of_minimal_support hdim q.1 q.2
  refine ⟨haq, hbq, hdimq, ?_⟩
  obtain ⟨s, hhead, hlast⟩ :=
    IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime A M
  choose p hp using fun i => (s.step i).2
  let N : Fin (s.length + 1) → Submodule A M := s.toFun
  have hle : ∀ i : Fin s.length, N i.castSucc ≤ N i.succ := fun i => (s.step i).1
  have hbot : N 0 = ⊥ := by simpa [N, RelSeries.head] using hhead
  have htop : N (Fin.last s.length) = ⊤ := by simpa [N, RelSeries.last] using hlast
  have hpSupport : ∀ i : Fin s.length, p i ∈ Module.support A M :=
    mem_support_of_isQuotientEquivQuotientPrime_series A M s hhead hlast p hp
  have hterms := moduleSymbol_filtration_product N p hle hp hbot hpSupport a b ha hb hdim
  have hdimTop : Module.supportDim A ↥(⊤ : Submodule A M) = 1 :=
    (Module.supportDim_eq_of_equiv Submodule.topEquiv).trans hdim
  have htopSym := moduleSymbol_eq_of_linearEquiv Submodule.topEquiv a b
    (regular_submodule (⊤ : Submodule A M) ha)
    (regular_submodule (⊤ : Submodule A M) hb) ha hb hdimTop hdim
  have hindex : moduleSymbol a b ha hb hdim =
      ∏ i : Fin s.length, primeFactorSymbol a b ha hb hdim (p i) := by
    calc
      moduleSymbol a b ha hb hdim =
          moduleSymbol a b
            (regular_submodule (⊤ : Submodule A M) ha)
            (regular_submodule (⊤ : Submodule A M) hb) hdimTop := htopSym.symm
      _ = moduleSymbolIfOne a b
            (regular_submodule (N (Fin.last s.length)) ha)
            (regular_submodule (N (Fin.last s.length)) hb) := by
          rw [htop]
          simp [moduleSymbolIfOne, hdimTop]
      _ = ∏ i : Fin s.length, primeFactorSymbol a b ha hb hdim (p i) := hterms
  let : Finite Q := Set.finite_coe_iff.mpr (finite_minimal_support (R := A) (M := M))
  let : Fintype Q := Fintype.ofFinite Q
  let φ : Fin s.length → Option Q := fun i =>
    if hq : Minimal (· ∈ Module.support A M) (p i) then some ⟨p i, hq⟩ else none
  let f : Fin s.length → (IsLocalRing.ResidueField A)ˣ :=
    fun i => primeFactorSymbol a b ha hb hdim (p i)
  let qSym : Q → (IsLocalRing.ResidueField A)ˣ := fun q =>
    moduleSymbol a b (haq q) (hbq q) (hdimq q)
  have hfiber (q : Q) :
      ∏ i ∈ Finset.univ.filter (fun i : Fin s.length => φ i = some q), f i =
        qSym q ^ (Module.length (Localization.AtPrime q.1.asIdeal)
          (LocalizedModule q.1.asIdeal.primeCompl M)).toNat := by
    have hpq : ∀ i, φ i = some q → p i = q.1 := by
      intro i hφ
      by_cases hmin : Minimal (· ∈ Module.support A M) (p i)
      · simp only [φ, dite_eq_left hmin] at hφ
        injection hφ with hsub
        exact congrArg Subtype.val hsub
      · simp [φ, hmin] at hφ
    let F : Finset (Fin s.length) := Finset.univ.filter (fun i => φ i = some q)
    let S : Set (Fin s.length) := {i | p i = q.1}
    let : Fintype S := Fintype.ofFinite S
    have hFS : F = S.toFinset := by
      ext i
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset, S]
      constructor
      · exact hpq i
      · intro hEq
        have hmin : Minimal (· ∈ Module.support A M) (p i) := hEq ▸ q.2
        dsimp [φ]
        rw [dite_eq_left hmin]
        exact congrArg some (Subtype.ext hEq)
    have hcard : F.card = S.ncard := (congrArg Finset.card hFS).trans
      (Set.ncard_eq_toFinset_card' S).symm
    have hlength := (Module.setOf_minimal_range_eq_setOf_minimal_support_and_ncard_eq_length
      N p hle hp hbot htop).2 q.1 q.2
    have hcount : S.ncard =
        (Module.length (Localization.AtPrime q.1.asIdeal)
          (LocalizedModule q.1.asIdeal.primeCompl M)).toNat := by
      simpa only [ENat.toNat_natCast] using congrArg ENat.toNat hlength
    calc
      ∏ i ∈ Finset.univ.filter (fun i : Fin s.length => φ i = some q), f i =
          ∏ i ∈ F, qSym q := by
            apply Finset.prod_congr rfl
            intro i hi
            have hpi := hpq i (Finset.mem_filter.mp hi).2
            unfold f qSym
            rw [hpi]
            unfold primeFactorSymbol
            rw [dite_eq_left q.2]
      _ = qSym q ^ S.ncard := by simp [F, hcard]
      _ = qSym q ^
          (Module.length (Localization.AtPrime q.1.asIdeal)
            (LocalizedModule q.1.asIdeal.primeCompl M)).toNat := by rw [hcount]
  have hnone :
      ∏ i ∈ Finset.univ.filter (fun i : Fin s.length => φ i = none), f i = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hφ : φ i = none := (Finset.mem_filter.mp hi).2
    by_cases hmin : Minimal (· ∈ Module.support A M) (p i)
    · simp [φ, hmin] at hφ
    · simp [f, primeFactorSymbol, hmin]
  have hfiberwise := Finset.prod_fiberwise (Finset.univ : Finset (Fin s.length)) φ f
  have hgroup :
      (∏ i : Fin s.length, f i) =
        ∏ q : Q, qSym q ^
          (Module.length (Localization.AtPrime q.1.asIdeal)
            (LocalizedModule q.1.asIdeal.primeCompl M)).toNat := by
    rw [← hfiberwise, Fintype.prod_option]
    simp only [hnone, one_mul]
    apply Finset.prod_congr rfl
    intro q hq
    exact hfiber q
  exact hindex.trans (hgroup.trans (finprod_eq_prod_of_fintype _).symm)

end AlgebraicGeometry
