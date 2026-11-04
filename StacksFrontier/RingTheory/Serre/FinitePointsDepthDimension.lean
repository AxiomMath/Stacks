module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.QuotSMulTop
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayRings
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Basic
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
public import StacksFrontier.RingTheory.Serre.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finitely many primes where the depth equals `k` and the support is bigger

Let `R` be a Noetherian ring admitting a dualizing complex and let `M` be a finite `R`-module
satisfying Serre's condition `(Sₖ)`. There are only finitely many primes `𝔭` with

`depth(M_𝔭) = k` and `dim Supp(M_𝔭) > k`.

This is the affine content of [Stacks, Tag 0ECN], whose scheme-level statement is
`AlgebraicGeometry.finite_setOf_depth_eq_and_lt_supportDim`.

The proof is an induction on `k`.  For `k = 0` the condition `depth(M_𝔭) = 0` says that `𝔭` is
an associated prime of `M` (Lemma 00LL), and a finite module over a Noetherian ring has only
finitely many associated primes.  For `k > 0`, Serre's condition forces `M` to localize to a
Cohen--Macaulay module at each of its associated primes: the depth there is `0`, so
`min(k, dim Supp(M_𝔭)) = 0` with `k > 0` forces `dim Supp(M_𝔭) = 0` as well.  Since the
Cohen--Macaulay locus is open in the support ([Stacks, Tag 0EHS]) and misses no associated
prime, the complementary closed set is cut out by an ideal avoiding every associated prime, and
such an ideal contains a nonzerodivisor `f` on `M` ([Stacks, Tag 00LD]).  At a prime not
containing `f` the exceptional condition is then impossible, because depth and dimension agree
there; and at a prime containing `f`, dividing by `f` drops both the depth and the dimension of
the support by exactly one ([Stacks, Tag 090R] and [Stacks, Tag 0B52]).  So the exceptional set
for `(M, k)` is contained in the exceptional set for `(M/fM, k - 1)`, which is finite by
induction.  This replaces the source's localization `A ↝ A_f` by the observation that primes
outside `V(f)` contribute nothing.

## Main results

* `Module.finite_setOf_depth_eq_and_lt_supportDim_localization` — the finiteness statement, with
  Serre's condition in the `WithBot ℕ∞` spelling that `AlgebraicGeometry.SheafHasPropertySk`
  uses.

## Implementation notes

Depth takes values in `ℕ∞` and the dimension of a support in `WithBot ℕ∞`, the zero module
having depth `⊤` and support dimension `⊥`; the two conditions of the conclusion are therefore
compared in their own types, and Serre's condition is read in `WithBot ℕ∞`, exactly as
`AlgebraicGeometry.SheafHasPropertySk` reads it.  The ring-level predicate
`PropertySkModule` of Definition 031P instead truncates the dimension of the support to `0` and
measures depth with `moduleDepth`; it is equivalent, but the sheaf-level consumer of this file
produces the `WithBot ℕ∞` form directly and no translation is needed.

The dualizing complex is an object of the *standard* derived category of `ModuleCat R`, the
model at which [Stacks, Tag 0EHS] is proved and at which `Stacks.Duality.HasDualizingModelOn`
produces a dualizing complex over the sections of an affine open.

## References

* [Stacks Project, Tag 0ECN](https://stacks.math.columbia.edu/tag/0ECN)
* [Stacks Project, Tag 0EHS](https://stacks.math.columbia.edu/tag/0EHS)
* [Stacks Project, Tag 090R](https://stacks.math.columbia.edu/tag/090R)
* [Stacks Project, Tag 0B52](https://stacks.math.columbia.edu/tag/0B52)
* [Stacks Project, Tag 00LD](https://stacks.math.columbia.edu/tag/00LD)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped Pointwise

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Serre.DepthDimension

/-! ### Arithmetic in `ℕ∞` and `WithBot ℕ∞` -/

/-- Cancelling `1` on the right of an equality in `ℕ∞`. -/
private lemma enat_eq_of_add_one_eq_add_one {a b : ℕ∞} (h : a + 1 = b + 1) : a = b :=
  le_antisymm ((ENat.add_le_add_iff_right ENat.one_ne_top).mp h.le)
    ((ENat.add_le_add_iff_right ENat.one_ne_top).mp h.ge)

/-- From `min (a + 1) (b + 1) ≤ c + 1` in `WithBot ℕ∞` conclude `min a b ≤ c`. -/
private lemma min_le_of_min_add_one_le_add_one {a b c : WithBot ℕ∞}
    (h : min (a + 1) (b + 1) ≤ c + 1) : min a b ≤ c := by
  rcases min_le_iff.mp h with hc | hc
  · exact le_trans (min_le_left _ _) (ENat.WithBot.add_le_add_one_right_iff.mp hc)
  · exact le_trans (min_le_right _ _) (ENat.WithBot.add_le_add_one_right_iff.mp hc)

/-- Cancelling `1` on the right of a strict inequality in `WithBot ℕ∞`. -/
private lemma lt_of_add_one_lt_add_one {a b : WithBot ℕ∞} (h : a + 1 < b + 1) : a < b := by
  by_contra hle
  exact absurd h (not_lt_of_ge
    (ENat.WithBot.add_le_add_one_right_iff.mpr (le_of_not_gt hle)))

/-! ### Depth and the associated primes of a localization -/

/-- An associated prime of a module lies in its support. -/
private lemma mem_support_of_mem_associatedPrimes {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] {p : PrimeSpectrum R} (hp : p.asIdeal ∈ associatedPrimes R M) :
    p ∈ Module.support R M := by
  obtain ⟨m, hm⟩ := hp.2
  rw [Submodule.bot_colon'] at hm
  exact Module.mem_support_iff_exists_annihilator.mpr ⟨m, hm ▸ Ideal.le_radical⟩

/-! ### Localizing a quotient by a nonzerodivisor -/

/-- Localizing `M/xM` gives the quotient of the localization of `M` by the image of `x`. -/
private def localizedQuotSMulTopEquiv {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : Submonoid R) (x : R) :
    LocalizedModule p (QuotSMulTop x M) ≃ₗ[Localization p]
      QuotSMulTop (algebraMap R (Localization p) x) (LocalizedModule p M) := by
  have hJ : x • (⊤ : Submodule R M) = Ideal.span ({x} : Set R) • (⊤ : Submodule R M) :=
    (Submodule.ideal_span_singleton_smul x (⊤ : Submodule R M)).symm
  have hloc : (x • (⊤ : Submodule R M)).localized p =
      (algebraMap R (Localization p) x) •
        (⊤ : Submodule (Localization p) (LocalizedModule p M)) := by
    change (x • (⊤ : Submodule R M)).localized' (Localization p) p
      (LocalizedModule.mkLinearMap p M) = _
    rw [← Submodule.ideal_span_singleton_smul (algebraMap R (Localization p) x)
      (⊤ : Submodule (Localization p) (LocalizedModule p M)), hJ, Submodule.localized'_smul,
      Submodule.localized'_span]
    simp only [Set.image_singleton, Submodule.localized'_top]
    rfl
  exact (localizedQuotientEquiv p (x • (⊤ : Submodule R M))).symm.trans
    (Submodule.quotEquivOfEq _ _ hloc)

/-- A nonzerodivisor stays a nonzerodivisor after localization. -/
private lemma isSMulRegular_localizedModule {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (p : Submonoid R) (x : R) (hreg : IsSMulRegular M x) :
    IsSMulRegular (LocalizedModule p M) (algebraMap R (Localization p) x) := by
  let f := LocalizedModule.mkLinearMap p M
  let g : M →ₗ[R] M := LinearMap.lsmul R M x
  let g' := IsLocalizedModule.map p f f g
  have hker : LinearMap.ker g = ⊥ :=
    LinearMap.ker_eq_bot.mpr fun a b hab => hreg (show x • a = x • b from hab)
  have hinj : Function.Injective g' := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_localizedMap_eq_localized₀_ker p f f g]
    simp [hker]
  have heqfun : g'.toFun = fun z : LocalizedModule p M =>
      (LinearMap.lsmul (Localization p) (LocalizedModule p M)
        (algebraMap R (Localization p) x)) z := by
    funext z
    induction z using LocalizedModule.induction_on with
    | h m s =>
      show ((IsLocalizedModule.map p (LocalizedModule.mkLinearMap p M)
        (LocalizedModule.mkLinearMap p M)) g) (LocalizedModule.mk m s) = _
      rw [IsLocalizedModule.map_LocalizedModules]
      show LocalizedModule.mk (x • m) s =
        (algebraMap R (Localization p) x) • LocalizedModule.mk m s
      rw [show algebraMap R (Localization p) x = Localization.mk x (1 : p) from rfl]
      simpa using (LocalizedModule.mk_smul_mk x m (1 : p) s).symm
  show Function.Injective fun z : LocalizedModule p M =>
    (LinearMap.lsmul (Localization p) (LocalizedModule p M)
      (algebraMap R (Localization p) x)) z
  intro a b hab
  exact hinj (show g'.toFun a = g'.toFun b by simpa only [← heqfun] using hab)

/-- The image of a nonzerodivisor in the localization at a prime containing it lies in the
maximal ideal. -/
private lemma algebraMap_mem_maximalIdeal {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {f : R} (hfp : f ∈ p.asIdeal) :
    algebraMap R (Localization.AtPrime p.asIdeal) f ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) := by
  have hp : p.asIdeal.IsPrime := p.isPrime
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.mem_map_of_mem _ hfp

/-! ### Serre's condition in the `WithBot ℕ∞` spelling -/

/-- Serre's condition `(Sₖ)` for a module over a Noetherian ring, read at every prime in
`WithBot ℕ∞`, as `AlgebraicGeometry.SheafHasPropertySk` reads it at every point of a scheme. -/
@[ega "IV 5.7.2" "special case", ega "IV 5.7.3"]
private def MinSupportDimLeDepth (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M]
    [Module R M] (k : ℕ) : Prop :=
  ∀ p : PrimeSpectrum R,
    min (k : WithBot ℕ∞)
        (Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M)) ≤
      (Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule.AtPrime p.asIdeal M) : WithBot ℕ∞)

/-- At a prime containing a nonzerodivisor `f` on `M`, dividing by `f` drops both the depth and the
dimension of the support of the localization by exactly one. -/
private lemma depth_supportDim_localization_quotSMulTop {R M : Type u} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] (f : R)
    (hf : IsSMulRegular M f) {p : PrimeSpectrum R} (hfp : f ∈ p.asIdeal) :
    Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule.AtPrime p.asIdeal (QuotSMulTop f M)) + 1 =
      Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule.AtPrime p.asIdeal M) ∧
    Module.supportDim (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal (QuotSMulTop f M)) + 1 =
      Module.supportDim (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) := by
  have hp : p.asIdeal.IsPrime := p.isPrime
  have e : LocalizedModule.AtPrime p.asIdeal (QuotSMulTop f M) ≃ₗ[Localization.AtPrime p.asIdeal]
      QuotSMulTop (algebraMap R (Localization.AtPrime p.asIdeal) f)
        (LocalizedModule.AtPrime p.asIdeal M) :=
    localizedQuotSMulTopEquiv p.asIdeal.primeCompl f
  have hfm := algebraMap_mem_maximalIdeal (p := p) hfp
  have hreg : IsSMulRegular (LocalizedModule.AtPrime p.asIdeal M)
      (algebraMap R (Localization.AtPrime p.asIdeal) f) :=
    isSMulRegular_localizedModule _ f hf
  rw [Module.supportDim_eq_of_equiv e, Module.depth_eq_depth_of_linearEquiv _ e]
  exact ⟨(Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
    (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
    (LocalizedModule.AtPrime p.asIdeal M)).1 _ hfm hreg,
    Module.supportDim_quotSMulTop_succ_eq_supportDim hreg hfm⟩

/-- Dividing by a nonzerodivisor on a module with `(S_{k+1})` gives a module with `(Sₖ)`: at a
prime containing the element both the depth and the dimension of the support drop by exactly
one, and at a prime not containing it the localization vanishes. -/
private lemma minSupportDimLeDepth_quotSMulTop {R M : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (k : ℕ)
    (hM : MinSupportDimLeDepth R M (k + 1)) (f : R) (hf : IsSMulRegular M f) :
    MinSupportDimLeDepth R (QuotSMulTop f M) k := by
  intro p
  have hp : p.asIdeal.IsPrime := p.isPrime
  by_cases hfp : f ∈ p.asIdeal
  · obtain ⟨hddrop, hdrop⟩ := depth_supportDim_localization_quotSMulTop f hf hfp
    have hSk := hM p
    rw [← hdrop, ← hddrop] at hSk
    refine min_le_of_min_add_one_le_add_one ?_
    convert hSk using 2 <;> push_cast <;> rfl
  · have e : LocalizedModule.AtPrime p.asIdeal (QuotSMulTop f M) ≃ₗ[Localization.AtPrime p.asIdeal]
        QuotSMulTop (algebraMap R (Localization.AtPrime p.asIdeal) f)
          (LocalizedModule.AtPrime p.asIdeal M) :=
      localizedQuotSMulTopEquiv p.asIdeal.primeCompl f
    rw [Module.supportDim_eq_of_equiv e, Module.depth_eq_depth_of_linearEquiv _ e]
    have hunit : IsUnit (algebraMap R (Localization.AtPrime p.asIdeal) f) :=
      IsLocalization.map_units _ ⟨f, Ideal.mem_primeCompl_iff.mpr hfp⟩
    have htop : (algebraMap R (Localization.AtPrime p.asIdeal) f) •
        (⊤ : Submodule (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M)) = ⊤ := by
      obtain ⟨u, hu⟩ := hunit
      refine top_unique fun n _ => ?_
      rw [← hu, Submodule.mem_smul_pointwise_iff_exists]
      refine ⟨(↑u⁻¹ : Localization.AtPrime p.asIdeal) • n, trivial, ?_⟩
      rw [smul_smul, show (↑u : Localization.AtPrime p.asIdeal) *
        (↑u⁻¹ : Localization.AtPrime p.asIdeal) = 1 by simp, one_smul]
    have hsub : Subsingleton (QuotSMulTop (algebraMap R (Localization.AtPrime p.asIdeal) f)
        (LocalizedModule.AtPrime p.asIdeal M)) := by
      rw [Submodule.Quotient.subsingleton_iff]
      exact htop
    rw [Module.supportDim_eq_bot_of_subsingleton]
    simp

/-! ### Prime avoidance against the Cohen--Macaulay locus -/

/-- Over a Noetherian ring, a finite module satisfying `(S_{k+1})` localizes to a
Cohen--Macaulay module at each of its associated primes: the depth there is `0`, and Serre's
condition then forces the dimension of the support to be `0` too. -/
private lemma isCohenMacaulay_localization_of_mem_associatedPrimes {R M : Type u} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] (k : ℕ)
    (hM : MinSupportDimLeDepth R M (k + 1)) (p : PrimeSpectrum R)
    (hp : p.asIdeal ∈ associatedPrimes R M) :
    Module.IsCohenMacaulayAtMaximalIdeal (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) := by
  have hp' : p.asIdeal.IsPrime := p.isPrime
  have hsupp : p ∈ Module.support R M := mem_support_of_mem_associatedPrimes hp
  have hnt : Nontrivial (LocalizedModule.AtPrime p.asIdeal M) := Module.mem_support_iff.mp hsupp
  have hdepth : Module.depth (Localization.AtPrime p.asIdeal)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule.AtPrime p.asIdeal M) = 0 :=
    (Module.depth_localized_eq_zero_iff p).mpr hp
  have hSk := hM p
  rw [hdepth] at hSk
  have hle0 : Module.supportDim (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) ≤ 0 := by
    rcases min_le_iff.mp hSk with hcase | hcase
    · exact absurd hcase (by simp)
    · simpa using hcase
  have hdim : Module.supportDim (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) = 0 := by
    cases hv : Module.supportDim (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M) with
    | bot =>
      exact absurd hv (Module.supportDim_ne_bot_of_nontrivial _ _)
    | coe c =>
      rw [hv] at hle0
      have hc : c ≤ 0 := by exact_mod_cast hle0
      simpa using hc
  show (Module.depth (Localization.AtPrime p.asIdeal)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule.AtPrime p.asIdeal M) : WithBot ℕ∞) =
    Module.supportDim (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M)
  rw [hdepth, hdim]
  rfl

/-- **Prime avoidance against the Cohen--Macaulay locus.**  Over a Noetherian ring with a
dualizing complex, a finite module satisfying `(S_{k+1})` admits a nonzerodivisor `f` such that
`M` localizes to a Cohen--Macaulay module at every prime of its support not containing `f`. -/
private lemma exists_isSMulRegular_cohenMacaulay_of_notMem {R M : Type u} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (ω : DerivedCategory (ModuleCat.{u} R)) (hω : Dualizing.IsDualizingComplex ω) (k : ℕ)
    (hM : MinSupportDimLeDepth R M (k + 1)) :
    ∃ f : R, IsSMulRegular M f ∧ ∀ p : PrimeSpectrum R, f ∉ p.asIdeal →
      p ∈ Module.support R M →
        Module.IsCohenMacaulayAtMaximalIdeal (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M) := by
  classical
  have hCopen : IsOpen {q : ↥(Module.support R M) |
      Module.IsCohenMacaulayAtMaximalIdeal (Localization.AtPrime q.1.asIdeal)
        (LocalizedModule.AtPrime q.1.asIdeal M)} :=
    Dualizing.isOpen_cohenMacaulayLocus ω hω
  obtain ⟨V, hV, hVC⟩ := isOpen_induced_iff.mp hCopen
  have hmemV : ∀ q : ↥(Module.support R M), q.1 ∈ V ↔
      Module.IsCohenMacaulayAtMaximalIdeal (Localization.AtPrime q.1.asIdeal)
        (LocalizedModule.AtPrime q.1.asIdeal M) := fun q => Set.ext_iff.mp hVC q
  have hZclosed : IsClosed (Module.support R M ∩ Vᶜ) :=
    Module.isClosed_support.inter hV.isClosed_compl
  obtain ⟨I, hIZ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hZclosed
  have hnotle : ∀ q ∈ associatedPrimes R M, ¬ I ≤ q := by
    intro q hq hIq
    have hqp : q.IsPrime := hq.isPrime
    have hrs : (⟨q, hqp⟩ : PrimeSpectrum R) ∈ Module.support R M :=
      mem_support_of_mem_associatedPrimes hq
    have hrV : (⟨q, hqp⟩ : PrimeSpectrum R) ∈ V :=
      (hmemV ⟨⟨q, hqp⟩, hrs⟩).mpr
        (isCohenMacaulay_localization_of_mem_associatedPrimes k hM ⟨q, hqp⟩ hq)
    have hrZ : (⟨q, hqp⟩ : PrimeSpectrum R) ∈ Module.support R M ∩ Vᶜ :=
      hIZ.symm ▸ (PrimeSpectrum.mem_zeroLocus _ _).mpr hIq
    exact hrZ.2 hrV
  obtain ⟨f, hfI, hreg⟩ :=
    (Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrimes_not_le I M
      (associatedPrimes.finite R M)).mpr hnotle
  refine ⟨f, hreg, fun p hfp hps => ?_⟩
  by_contra hnotCM
  have hpZ : p ∈ Module.support R M ∩ Vᶜ :=
    ⟨hps, fun hpV => hnotCM ((hmemV ⟨p, hps⟩).mp hpV)⟩
  exact hfp ((PrimeSpectrum.mem_zeroLocus _ _).mp (hIZ ▸ hpZ) hfI)

/-! ### The exceptional set and its finiteness -/

/-- The exceptional set of [Stacks, Tag 0ECN] over a ring: the primes at which the localization
of `M` has depth exactly `k` and support of dimension strictly bigger than `k`. -/
private def exceptionalSet (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
    (k : ℕ) : Set (PrimeSpectrum R) :=
  {p | Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule.AtPrime p.asIdeal M) = (k : ℕ∞) ∧
      (k : WithBot ℕ∞) < Module.supportDim (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M)}

/-- The inductive step: the exceptional set for `(M, k + 1)` is contained in the exceptional set
for `(M/fM, k)`, for `f` a nonzerodivisor on `M` whose nonvanishing locus meets the support of
`M` only inside the Cohen--Macaulay locus. -/
private lemma exceptionalSet_subset {R M : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (k : ℕ) (f : R) (hf : IsSMulRegular M f)
    (hCM : ∀ p : PrimeSpectrum R, f ∉ p.asIdeal → p ∈ Module.support R M →
      Module.IsCohenMacaulayAtMaximalIdeal (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M)) :
    exceptionalSet R M (k + 1) ⊆ exceptionalSet R (QuotSMulTop f M) k := by
  intro p hp
  have hp' : p.asIdeal.IsPrime := p.isPrime
  have hfp : f ∈ p.asIdeal := by
    by_contra hn
    have hs : p ∈ Module.support R M := by
      rw [Module.mem_support_iff]
      by_contra hz
      have : Subsingleton (LocalizedModule.AtPrime p.asIdeal M) :=
        not_nontrivial_iff_subsingleton.mp hz
      refine absurd hp.2 (not_lt_of_ge ?_)
      rw [Module.supportDim_eq_bot_of_subsingleton]
      exact bot_le
    have he := hCM p hn hs
    rw [Module.IsCohenMacaulayAtMaximalIdeal, hp.1] at he
    exact (ne_of_lt hp.2) he
  obtain ⟨hddrop, hdrop⟩ := depth_supportDim_localization_quotSMulTop f hf hfp
  refine ⟨?_, ?_⟩
  · rw [hp.1] at hddrop
    refine enat_eq_of_add_one_eq_add_one (hddrop.trans ?_)
    push_cast
    rfl
  · refine lt_of_add_one_lt_add_one ?_
    rw [hdrop]
    refine lt_of_le_of_lt (le_of_eq ?_) hp.2
    push_cast
    rfl

/-- **Stacks, Tag 0ECN, affine case.**  The exceptional set is finite, by induction on `k`. -/
private theorem finite_exceptionalSet {R : Type u} [CommRing R] [IsNoetherianRing R]
    (ω : DerivedCategory (ModuleCat.{u} R)) (hω : Dualizing.IsDualizingComplex ω) (k : ℕ)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : MinSupportDimLeDepth R M k) : (exceptionalSet R M k).Finite := by
  induction k generalizing M with
  | zero =>
    refine ((associatedPrimes.finite R M).preimage (f := PrimeSpectrum.asIdeal)
      (fun a _ b _ h => PrimeSpectrum.ext h)).subset fun p hp => ?_
    exact (Module.depth_localized_eq_zero_iff p).mp hp.1
  | succ k ih =>
    obtain ⟨f, hf, hCM⟩ := exists_isSMulRegular_cohenMacaulay_of_notMem ω hω k hM
    exact (ih (QuotSMulTop f M) (minSupportDimLeDepth_quotSMulTop k hM f hf)).subset
      (exceptionalSet_subset k f hf hCM)

end Stacks.Serre.DepthDimension

namespace Module

open Stacks.Serre.DepthDimension

/-- **Stacks, Tag 0ECN, affine case.**  Let `R` be a Noetherian ring with a dualizing complex
`ω` and let `M` be a finite `R`-module satisfying Serre's condition `(Sₖ)`, in the form

`min(k, dim Supp(M_𝔭)) ≤ depth(M_𝔭)` for every prime `𝔭`,

read in `WithBot ℕ∞`.  Then only finitely many primes `𝔭` of `R` satisfy

`depth(M_𝔭) = k` and `dim Supp(M_𝔭) > k`. -/
public theorem finite_setOf_depth_eq_and_lt_supportDim_localization {R : Type u} [CommRing R]
    [IsNoetherianRing R] (ω : DerivedCategory (ModuleCat.{u} R))
    (hω : Dualizing.IsDualizingComplex ω) (k : ℕ)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : ∀ p : PrimeSpectrum R,
      min (k : WithBot ℕ∞)
          (Module.supportDim (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M)) ≤
        (Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule.AtPrime p.asIdeal M) : WithBot ℕ∞)) :
    {p : PrimeSpectrum R |
        Module.depth (Localization.AtPrime p.asIdeal)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule.AtPrime p.asIdeal M) = (k : ℕ∞) ∧
          (k : WithBot ℕ∞) < Module.supportDim (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M)}.Finite :=
  finite_exceptionalSet ω hω k M hM

end Module

end
