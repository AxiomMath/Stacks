module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.RingTheory.Dualizing.Depth
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationSituation
public import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.Catenary.Localization
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.DimensionFormula
public import StacksFrontier.RingTheory.Dualizing.UbiquityCompleteLocal
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.Serre.Criterion

/-!
# The algebraization conditions over a complete normal local domain

Let `(A, 𝔪)` be a complete Noetherian normal local domain — a domain integrally closed in its
fraction field, so `IsNormalDomain A` in the vocabulary of this library, spelled out here as
`IsDomain A` together with `IsIntegrallyClosed A` — of Krull dimension at least four, and let
`f ∈ 𝔪` be nonzero. This file records that such data satisfies the numbered assumptions
(1), (2), (3), (5) and (6) of [Stacks, Tag 0DXU], the algebraization criterion for a coherent
formal vector bundle along a principal divisor:

1. `A` is local and the ideal `𝔞` of the algebraization situation is the maximal ideal `𝔪`;
2. `A` has a dualizing complex;
3. the ideal `I` of the situation is `(f)` for a nonzerodivisor `f ∈ 𝔪`;
5. `depth((A/f)_𝔭) + dim(A/𝔭) > 1` for every `𝔭 ∈ V(f)` other than `𝔪`;
6. `depth(A_𝔭) + dim(A/𝔭) > 3` for every `𝔭 ∉ V(f)` with `V(𝔭) ∩ V(f) ≠ {𝔪}`.

Assumptions (1) and the ideal half of (3) are the choice of data `𝔞 = 𝔪`, `I = (f)`, which is
what `completeNormalSituation` makes, and `completeNormalSituation_a`,
`completeNormalSituation_I` read off. Assumption (2) is [Stacks, Tag 0BFR] for a Noetherian
complete local ring. The nonzerodivisor half of (3) is `f ≠ 0` in a domain.

## Main results

* `Stacks.Algebraization.CompleteNormalDomain.one_lt_depth_quotient_add_ringKrullDim_quotient`
  is assumption (5).
* `Stacks.Algebraization.CompleteNormalDomain.three_lt_depth_add_ringKrullDim_quotient`
  is assumption (6).
* `Stacks.Algebraization.CompleteNormalDomain.satisfiesAssumptions` collects (1), (2), (3), (5)
  and (6) for the situation `completeNormalSituation`.

[Stacks, Tag 0DXV] itself, these assumptions together with the algebraization of vector bundles
on the formal completion of `U` along `U ∩ V(f)` that follows from them, is
`satisfiesAssumptions_and_isCompletion_of_isFiniteLocallyFreeAdic` in the same namespace, in
`StacksFrontier.AlgebraicGeometry.Algebraization.CompleteNormalDomainAlgebraization`.

## Implementation notes

The depth of `(A/f)_𝔭` is read, as in the statement of [Stacks, Tag 0DXU], as the depth over
`A_𝔭` of the localization of `A/fA`; the two agree because depth is computed from the maximal
ideal, which acts through `A_𝔭`.

## References

* [Stacks Project, Tag 0DXV](https://stacks.math.columbia.edu/tag/0DXV)
* [Stacks Project, Tag 0DXU](https://stacks.math.columbia.edu/tag/0DXU)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped Pointwise

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization.CompleteNormalDomain

/-! ### The dimension formula and Serre's `(S_2)` bound -/

/-- A prime strictly below the maximal ideal has `dim(A/𝔭) ≥ 1`. -/
private lemma one_le_ringKrullDim_quotient {A : Type u} [CommRing A] [IsLocalRing A]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ IsLocalRing.maximalIdeal A) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p) := by
  have hidlt : p < IsLocalRing.maximalIdeal A :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹p.IsPrime›)) hp
  have hplt : (⟨p, inferInstance⟩ : PrimeSpectrum A) <
      ⟨IsLocalRing.maximalIdeal A, (IsLocalRing.maximalIdeal.isMaximal A).isPrime⟩ :=
    (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp hidlt
  have hco : (1 : ℕ∞) ≤ Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum A) :=
    le_trans le_add_self (Order.coheight_add_one_le hplt)
  rw [← coheight_eq_ringKrullDim_quotient ⟨p, inferInstance⟩]
  exact_mod_cast hco

/-- The dimension formula `dim A = height 𝔭 + dim(A/𝔭)` over a Noetherian complete local
domain. -/
private lemma ringKrullDim_eq_height_add_ringKrullDim_quotient (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsPrecomplete (IsLocalRing.maximalIdeal A) A] (p : Ideal A) [p.IsPrime] :
    ringKrullDim A = (p.height : WithBot ℕ∞) + ringKrullDim (A ⧸ p) := by
  have hcat : IsUniversallyCatenary A :=
    Ring.isUniversallyCatenary_iff_isUniversallyCatenary.mp
      (isUniversallyCatenary_of_isPrecomplete_maximalIdeal A)
  have hple : p ≤ IsLocalRing.maximalIdeal A :=
    IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹p.IsPrime›)
  have hadd := catenary_height_add hcat p (IsLocalRing.maximalIdeal A) hple
  rw [← FlatLocalCatenary.fibre_height_eq p hple,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast hadd

/-- Serre's condition `(S_2)` for a normal domain: `depth(A_𝔭) ≥ min(2, height 𝔭)` at every
prime `𝔭`. -/
private lemma min_two_height_le_depth_atPrime (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A] (p : Ideal A) [p.IsPrime] :
    min 2 (p.height : WithBot ℕ∞) ≤
      (Module.depth (Localization.AtPrime p)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p) : WithBot ℕ∞) := by
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height (I := p)
    (A := Localization.AtPrime p)]
  refine (isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth.mp
    ?_).2 p
  intro q hq
  let _ : q.IsPrime := hq
  exact ⟨IsLocalization.isDomain_of_local_atPrime hq,
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q) q.primeCompl
      q.primeCompl_le_nonZeroDivisors⟩

/-! ### The depth drop along a principal divisor -/

/-- A nonzero element of a domain is a nonzerodivisor. -/
private lemma isSMulRegular_of_ne_zero {A : Type u} [CommRing A] [IsDomain A] {f : A}
    (hf : f ≠ 0) : IsSMulRegular A f :=
  fun _ _ h => mul_left_cancel₀ hf h

/-- Localizing `A ⧸ fA` at a prime `𝔭` containing the nonzero element `f` of a domain drops the
depth by exactly one: `depth((A/f)_𝔭) + 1 = depth(A_𝔭)`. -/
private lemma depth_localizedModule_quotient_span_succ (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsDomain A] (f : A) (hf : f ≠ 0) (p : PrimeSpectrum A)
    (hfp : f ∈ p.asIdeal) :
    Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule.AtPrime p.asIdeal (A ⧸ Ideal.span {f})) + 1 =
      Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (Localization.AtPrime p.asIdeal) := by
  let R := Localization.AtPrime p.asIdeal
  let x : R := algebraMap A R f
  let g : A →ₗ[A] R := Algebra.linearMap A R
  let e : LocalizedModule.AtPrime p.asIdeal (A ⧸ Ideal.span {f}) ≃ₗ[A]
      QuotSMulTop x R := by
    let I : Ideal A := Ideal.span {f}
    let J : Ideal R := Ideal.span {x}
    have hJ : Submodule.localized' R p.asIdeal.primeCompl g (I : Submodule A A) =
        (J : Submodule R R) := by
      rw [Ideal.localized'_eq_map, Ideal.map_span]
      simp [J, x]
    let q0 : A ⧸ (I : Submodule A A) →ₗ[A]
        R ⧸ (Submodule.localized' R p.asIdeal.primeCompl g (I : Submodule A A)) :=
      Submodule.toLocalizedQuotient' R p.asIdeal.primeCompl g I
    let eJ := Submodule.quotEquivOfEq
      (Submodule.localized' R p.asIdeal.primeCompl g (I : Submodule A A))
      (J : Submodule R R) hJ
    have hJ' : (J : Submodule R R) = x • (⊤ : Submodule R R) := by
      simpa [J] using (Submodule.ideal_span_singleton_smul x (⊤ : Submodule R R))
    let eJ' := Submodule.quotEquivOfEq (J : Submodule R R) (x • (⊤ : Submodule R R)) hJ'
    let e' := eJ.trans eJ'
    have hloc : IsLocalizedModule p.asIdeal.primeCompl
        ((e'.restrictScalars A).toLinearMap.comp q0) :=
      IsLocalizedModule.of_linearEquiv p.asIdeal.primeCompl q0 (e'.restrictScalars A)
    simpa [QuotSMulTop] using
      (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (A ⧸ Ideal.span {f}))
        ((e'.restrictScalars A).toLinearMap.comp q0))
  have hx0 : x ≠ 0 := fun hx => hf (IsLocalization.injective R
    p.asIdeal.primeCompl_le_nonZeroDivisors (by simpa [x] using hx))
  rw [Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal R)
    (e.extendScalarsOfIsLocalization p.asIdeal.primeCompl R)]
  exact (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
    (IsLocalRing.maximalIdeal R) R).1 x
    ((IsLocalization.AtPrime.to_map_mem_maximal_iff R p.asIdeal f).2 hfp)
    (isSMulRegular_of_ne_zero hx0)

/-! ### Assumption (5) of Tag 0DXU -/

/-- Let `(A, 𝔪)` be a complete Noetherian normal local domain of dimension at least four and let
`f ∈ A` be nonzero. Then `depth((A/f)_𝔭) + dim(A/𝔭) > 1` for every prime `𝔭` containing `f` other
than `𝔪`. -/
theorem one_lt_depth_quotient_add_ringKrullDim_quotient (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsDomain A] [IsIntegrallyClosed A] (hdim : (4 : WithBot ℕ∞) ≤ ringKrullDim A)
    (f : A) (hf : f ≠ 0) (p : PrimeSpectrum A) (hfp : f ∈ p.asIdeal)
    (hp : p.asIdeal ≠ IsLocalRing.maximalIdeal A) :
    (1 : WithBot ℕ∞) <
      (Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule.AtPrime p.asIdeal (A ⧸ Ideal.span {f})) : WithBot ℕ∞) +
        ringKrullDim (A ⧸ p.asIdeal) := by
  have hheightPos : 1 ≤ p.asIdeal.height := Order.one_le_iff_ne_zero.mpr fun hzero =>
    hf (by simpa [Ideal.height_eq_zero_iff_eq_bot.mp hzero] using hfp)
  have hdimAdd := ringKrullDim_eq_height_add_ringKrullDim_quotient A p.asIdeal
  have hquotDimPos : (1 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal) :=
    one_le_ringKrullDim_quotient p.asIdeal hp
  by_cases htwo : 2 ≤ p.asIdeal.height
  · have hdepthA : (2 : ℕ∞) ≤
        Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (Localization.AtPrime p.asIdeal) := by
      have h := min_two_height_le_depth_atPrime A p.asIdeal
      rw [min_eq_left (by simpa using WithBot.coe_le_coe.mpr htwo)] at h
      exact WithBot.coe_le_coe.mp h
    have hdepthQ : (1 : ℕ∞) ≤
        Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule.AtPrime p.asIdeal (A ⧸ Ideal.span {f})) :=
      (ENat.add_le_add_iff_right ENat.one_ne_top).mp
        (by rwa [depth_localizedModule_quotient_span_succ A f hf p hfp, one_add_one_eq_two])
    calc
      (1 : WithBot ℕ∞) < (2 : WithBot ℕ∞) := by norm_num
      _ ≤ _ := add_le_add (WithBot.coe_le_coe.mpr hdepthQ) hquotDimPos
  · have hheightOne : p.asIdeal.height = 1 := by
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
        (Ideal.height_ne_top_of_isPrime (I := p.asIdeal))
      rw [← hn] at hheightPos htwo ⊢
      norm_cast at hheightPos htwo ⊢
      lia
    have hquotDimThree : (3 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal) := by
      rw [hdimAdd, hheightOne] at hdim
      have hdimE : (4 : WithBot ℕ∞) ≤ (1 : WithBot ℕ∞) + ringKrullDim (A ⧸ p.asIdeal) := by
        exact_mod_cast hdim
      cases hq : ringKrullDim (A ⧸ p.asIdeal) with
      | bot => simp [hq] at hdimE
      | coe d =>
        rw [hq] at hdimE
        have hdimENat : (4 : ℕ∞) ≤ 1 + d := WithBot.coe_le_coe.mp hdimE
        refine WithBot.coe_le_coe.mpr ?_
        apply (ENat.add_le_add_iff_left ENat.one_ne_top).mp
        convert hdimENat using 1
        norm_num
    calc
      (1 : WithBot ℕ∞) < (3 : WithBot ℕ∞) := by norm_num
      _ ≤ _ := le_add_of_nonneg_of_le (by simp) hquotDimThree

/-! ### Assumption (6) of Tag 0DXU -/

/-- Let `(A, 𝔪)` be a complete Noetherian normal local domain of dimension at least four and let
`f ∈ 𝔪`. Then `depth(A_𝔭) + dim(A/𝔭) > 3` for every prime `𝔭` not containing `f` whose closure
meets `V(f)` outside the closed point. -/
theorem three_lt_depth_add_ringKrullDim_quotient (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsDomain A]
    [IsIntegrallyClosed A] (hdim : (4 : WithBot ℕ∞) ≤ ringKrullDim A)
    (f : A) (hfm : f ∈ IsLocalRing.maximalIdeal A) (p : PrimeSpectrum A)
    (hfp : f ∉ p.asIdeal)
    (hp : ({q : PrimeSpectrum A | p.asIdeal ≤ q.asIdeal} ∩
      {q : PrimeSpectrum A | f ∈ q.asIdeal}) ≠
      {⟨IsLocalRing.maximalIdeal A, (IsLocalRing.maximalIdeal.isMaximal A).isPrime⟩}) :
    (3 : WithBot ℕ∞) <
      (Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (Localization.AtPrime p.asIdeal) : WithBot ℕ∞) +
        ringKrullDim (A ⧸ p.asIdeal) := by
  classical
  let m : PrimeSpectrum A :=
    ⟨IsLocalRing.maximalIdeal A, (IsLocalRing.maximalIdeal.isMaximal A).isPrime⟩
  have hm : m ∈ {q : PrimeSpectrum A | p.asIdeal ≤ q.asIdeal} ∩
      {q : PrimeSpectrum A | f ∈ q.asIdeal} :=
    ⟨IsLocalRing.le_maximalIdeal p.isPrime.ne_top, hfm⟩
  obtain ⟨q, hpq, hfq, hqm⟩ : ∃ q : PrimeSpectrum A,
      p.asIdeal ≤ q.asIdeal ∧ f ∈ q.asIdeal ∧ q ≠ m := by
    by_contra! h
    exact hp (Set.eq_singleton_iff_unique_mem.mpr ⟨hm, fun q hq => h q hq.1 hq.2⟩)
  have hpq' : p < q := lt_of_le_of_ne hpq fun h => hfp (by simpa only [h] using hfq)
  have hqm' : q < m :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal q.isPrime.ne_top) hqm
  have hpco : (2 : ℕ∞) ≤ Order.coheight p :=
    calc
      2 = (1 : ℕ∞) + 1 := by norm_num
      _ ≤ Order.coheight q + 1 :=
        add_le_add (le_trans le_add_self (Order.coheight_add_one_le hqm')) le_rfl
      _ ≤ Order.coheight p := Order.coheight_add_one_le hpq'
  have hquot : (2 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal) := by
    rw [← coheight_eq_ringKrullDim_quotient p]
    simpa using WithBot.coe_le_coe.mpr hpco
  have hdepth := min_two_height_le_depth_atPrime A p.asIdeal
  by_cases htwo : (2 : WithBot ℕ∞) ≤ (p.asIdeal.height : WithBot ℕ∞)
  · rw [min_eq_left htwo] at hdepth
    calc
      (3 : WithBot ℕ∞) < 4 := by norm_num
      _ ≤ _ := add_le_add hdepth hquot
  · rw [min_eq_right (le_of_not_ge htwo)] at hdepth
    calc
      (3 : WithBot ℕ∞) < 4 := by norm_num
      _ ≤ ringKrullDim A := hdim
      _ = _ := ringKrullDim_eq_height_add_ringKrullDim_quotient A p.asIdeal
      _ ≤ _ := add_le_add hdepth le_rfl

/-! ### The algebraization situation, and assumptions (1), (2) and (3) of Tag 0DXU -/

/-- The algebraization situation of [Stacks, Tag 0EHC] attached to a Noetherian local ring `A`
and an element `f` of its maximal ideal: the ideal `𝔞` is the maximal ideal `𝔪` and the ideal
`I` is the principal ideal `(f)`. -/
def completeNormalSituation (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A) : AlgebraizationSituation.{u} where
  A := A
  I := Ideal.span {f}
  a := IsLocalRing.maximalIdeal A
  I_le_a := by rwa [Ideal.span_le, Set.singleton_subset_iff]

/-- The ideal `𝔞` of `completeNormalSituation` is the maximal ideal. -/
lemma completeNormalSituation_a (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A) :
    (completeNormalSituation A f hf).a = IsLocalRing.maximalIdeal A := rfl

/-- The ideal `I` of `completeNormalSituation` is `(f)`. -/
lemma completeNormalSituation_I (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A) :
    (completeNormalSituation A f hf).I = Ideal.span {f} := rfl

/-! ### The remark -/

/-- Let `(A, 𝔪)` be a complete Noetherian normal local domain of dimension at least four and let
`f ∈ 𝔪` be nonzero. Then the algebraization situation with `𝔞 = 𝔪` and `I = (f)` satisfies
assumptions (1), (2), (3), (5) and (6) of [Stacks, Tag 0DXU]: `𝔞` is the maximal ideal, `A` has a
dualizing complex, `I` is generated by the nonzerodivisor `f`, and the two depth-dimension
inequalities hold off the closed point. -/
theorem satisfiesAssumptions (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsDomain A] [IsIntegrallyClosed A]
    (hdim : (4 : WithBot ℕ∞) ≤ ringKrullDim A) (f : A)
    (hfm : f ∈ IsLocalRing.maximalIdeal A) (hf : f ≠ 0) :
    (completeNormalSituation A f hfm).a = IsLocalRing.maximalIdeal A ∧
      (∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) ∧
      ((completeNormalSituation A f hfm).I = Ideal.span {f} ∧ IsSMulRegular A f) ∧
      (∀ p : PrimeSpectrum A, f ∈ p.asIdeal →
        p.asIdeal ≠ IsLocalRing.maximalIdeal A →
        (1 : WithBot ℕ∞) <
          (Module.depth (Localization.AtPrime p.asIdeal)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule.AtPrime p.asIdeal (A ⧸ Ideal.span {f})) : WithBot ℕ∞) +
            ringKrullDim (A ⧸ p.asIdeal)) ∧
      (∀ p : PrimeSpectrum A, f ∉ p.asIdeal →
        ({q : PrimeSpectrum A | p.asIdeal ≤ q.asIdeal} ∩
          {q : PrimeSpectrum A | f ∈ q.asIdeal}) ≠
          {⟨IsLocalRing.maximalIdeal A, (IsLocalRing.maximalIdeal.isMaximal A).isPrime⟩} →
        (3 : WithBot ℕ∞) <
          (Module.depth (Localization.AtPrime p.asIdeal)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
            (Localization.AtPrime p.asIdeal) : WithBot ℕ∞) +
            ringKrullDim (A ⧸ p.asIdeal)) :=
  ⟨completeNormalSituation_a A f hfm,
    Dualizing.exists_isDualizingComplex_of_isPrecomplete_maximalIdeal A,
    ⟨completeNormalSituation_I A f hfm, isSMulRegular_of_ne_zero hf⟩,
    fun p hfp hp => one_lt_depth_quotient_add_ringKrullDim_quotient A hdim f hf p hfp hp,
    fun p hfp hp => three_lt_depth_add_ringKrullDim_quotient A hdim f hfm p hfp hp⟩

end Stacks.Algebraization.CompleteNormalDomain

end
