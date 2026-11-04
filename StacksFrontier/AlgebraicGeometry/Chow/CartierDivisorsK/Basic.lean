module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Data.ENat.BigOperators
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.RestrictedDivisors
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Embedded
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Basic
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
public import StacksFrontier.RingTheory.Support.Finite
public import StacksFrontier.RingTheory.Lattice.Distance
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Length.Comparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Lengths after multiplying by a fraction

Let `A` be a one-dimensional Noetherian local ring and let `M` be a finite `A`-module with
full support and without embedded associated primes. For nonzerodivisors `a` and `b`, the
denominator ideal `I = (b) : (a)` of the fraction `a / b` and its fractional product
`(a / b) I = (a) : (b)` give two quotients of `M`, and the difference of their colengths is
the sum over the minimal primes of the generic lengths of `M` weighted by the orders of
`a / b`.

## Main definitions

* `Ideal.denominatorIdeal` is the ideal of `x` for which `x * (a / b)` lies in the ring.
* `Ideal.fractionalProductIdeal` is the ideal `(a / b) I` obtained from that denominator
  ideal.

## Main results

* `Ideal.fraction_smul_denominatorIdeal_le` states that `(a / b) I M` lies in `M`.
* `Ideal.length_fractionalProduct_quotient_sub_length_denominator_quotient` gives the
  resulting difference of lengths as a sum over the minimal primes.

## Implementation notes

The ideal `I` is written as the colon ideal `(b) : (a)`; its fractional product by `a / b` is
`(a) : (b)`. The containment is expressed inside the localization of `M` at the
nonzerodivisors. Orders of `a / b` on the domain `A / q` are written additively as
`ord(a mod q) - ord(b mod q)`. Lengths and orders are finite under the hypotheses, and their
values in `ℕ∞` are therefore converted to integers with `ENat.toNat`.

## References

* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
-/

@[expose] public section

open Pointwise

namespace Ideal

/-- An associated prime of a module with no embedded associated primes is minimal in the
support. -/
private lemma associated_is_minimal_support
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : HasNoEmbeddedAssociatedPrimes R M) {p : Ideal R}
    (hp : p ∈ associatedPrimes R M) :
    Minimal (· ∈ Module.support R M) ⟨p, hp.isPrime⟩ := by
  have hmin : Minimal (· ∈ PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M)
      (⟨p, hp.isPrime⟩ : PrimeSpectrum R) := by
    refine ⟨hp, ?_⟩
    intro q hq hqp
    have hqp' : q.asIdeal ≤ p := (PrimeSpectrum.asIdeal_le_asIdeal q _).2 hqp
    have heq : q.asIdeal = p := hM hp hq hqp'
    exact (PrimeSpectrum.ext
      (show (⟨q, hq.isPrime⟩ : PrimeSpectrum R).asIdeal =
        (⟨p, hp.isPrime⟩ : PrimeSpectrum R).asIdeal from heq)).symm.le
  have hset := Module.setOf_minimal_support_eq_setOf_minimal_associatedPrimes (R := R) (M := M)
  exact (Set.ext_iff.mp hset ⟨p, hp.isPrime⟩).mpr hmin

/-- A nonzerodivisor of the ring avoids every associated prime of a module with full support
and no embedded associated primes. -/
private lemma associated_avoids_nonZeroDivisor
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : HasNoEmbeddedAssociatedPrimes R M)
    (hsupp : Module.support R M = Set.univ) {x : R}
    (hx : x ∈ nonZeroDivisors R) {p : Ideal R} (hp : p ∈ associatedPrimes R M) : x ∉ p := by
  have hps := associated_is_minimal_support hM hp
  have hpmin : p ∈ minimalPrimes R := by
    refine ⟨⟨hp.isPrime, bot_le⟩, ?_⟩
    intro q hq hqp
    let q' : PrimeSpectrum R := ⟨q, hq.1⟩
    have hqSupp : q' ∈ Module.support R M := hsupp ▸ Set.mem_univ _
    have hle : q' ≤ (⟨p, hp.isPrime⟩ : PrimeSpectrum R) :=
      (PrimeSpectrum.asIdeal_le_asIdeal q' _).mpr hqp
    have hback := hps.2 hqSupp hle
    exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hback
  exact fun hxp => notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hxp hpmin hx

/-- A nonzerodivisor of the ring acts regularly on a module with full support and no embedded
associated primes. -/
private lemma regular_on_module_of_nonZeroDivisor
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : HasNoEmbeddedAssociatedPrimes R M)
    (hsupp : Module.support R M = Set.univ) {x : R}
    (hx : x ∈ nonZeroDivisors R) : IsSMulRegular M x := by
  have hnot : x ∉ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    intro h
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp h
    exact associated_avoids_nonZeroDivisor hM hsupp hx hp hxp
  rw [biUnion_associatedPrimes_eq_compl_regular R M] at hnot
  exact not_not.mp hnot

/-- A module with full support has the Krull dimension of the ring as its support
dimension. -/
private lemma supportDim_eq_ringKrullDim_of_support_eq_univ
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (hsupp : Module.support R M = Set.univ) :
    Module.supportDim R M = ringKrullDim R :=
  le_antisymm (Module.supportDim_le_ringKrullDim R M)
    (Order.krullDim_le_of_strictMono
      (fun p => (⟨p, hsupp ▸ Set.mem_univ p⟩ : Module.support R M)) fun _ _ hlt => hlt)

/-- The maximal ideal is not an associated prime of a module with full support and no embedded
associated primes over a one-dimensional ring: otherwise the support would be a single
point. -/
private lemma maximalIdeal_notMem_associatedPrimes
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hdim : ringKrullDim R = 1) (hM : HasNoEmbeddedAssociatedPrimes R M)
    (hsupp : Module.support R M = Set.univ) :
    IsLocalRing.maximalIdeal R ∉ associatedPrimes R M := by
  have hsd : Module.supportDim R M = 1 :=
    (supportDim_eq_ringKrullDim_of_support_eq_univ hsupp).trans hdim
  intro hp
  let p : PrimeSpectrum R := ⟨IsLocalRing.maximalIdeal R, hp.isPrime⟩
  have hmin := associated_is_minimal_support hM hp
  have hpM : p ∈ Module.support R M := hsupp ▸ Set.mem_univ p
  have hkey : ∀ c : Module.support R M, c = ⟨p, hpM⟩ := fun c =>
    Subtype.ext (le_antisymm le_top (hmin.2 c.2 le_top))
  have hdimzero : Module.supportDim R M = 0 := by
    show Order.krullDim (Module.support R M) = 0
    have : Nonempty (Module.support R M) := ⟨⟨p, hpM⟩⟩
    have : Subsingleton (Module.support R M) := ⟨fun x y => by rw [hkey x, hkey y]⟩
    exact Order.krullDim_eq_zero
  rw [hsd] at hdimzero
  norm_num at hdimzero

/-- A module with full support and no embedded associated primes over a one-dimensional
Noetherian local ring is Cohen–Macaulay: the maximal ideal contains a regular element, so the
depth is one, which is the dimension of the support. -/
private lemma cm_of_no_embedded_full_support_one_dim
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hdim : ringKrullDim R = 1) (hM : HasNoEmbeddedAssociatedPrimes R M)
    (hsupp : Module.support R M = Set.univ) :
    Module.IsCohenMacaulayAtMaximalIdeal R M := by
  have hsd : Module.supportDim R M = 1 :=
    (supportDim_eq_ringKrullDim_of_support_eq_univ hsupp).trans hdim
  have hmax := maximalIdeal_notMem_associatedPrimes hdim hM hsupp
  have havoid : ∀ q ∈ associatedPrimes R M, ¬ IsLocalRing.maximalIdeal R ≤ q :=
    fun q hq hle => hmax (le_antisymm (IsLocalRing.le_maximalIdeal hq.isPrime.ne_top) hle ▸ hq)
  obtain ⟨c, hc, hcreg⟩ :=
    (Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrimes_not_le
      (IsLocalRing.maximalIdeal R) M (associatedPrimes.finite R M)).2 havoid
  have hdrop := (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
    (IsLocalRing.maximalIdeal R) M).1 c hc hcreg
  have hlo : (1 : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) M :=
    le_add_self.trans_eq hdrop
  have htopneq : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ := by
    have : Nontrivial M := (Module.supportDim_ne_bot_iff_nontrivial R M).mp (by
      rw [hsd]
      norm_num)
    exact (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  have hup := Module.depth_le_supportDim R (IsLocalRing.maximalIdeal R) M htopneq
  show (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) = Module.supportDim R M
  rw [hsd] at hup ⊢
  exact le_antisymm hup (by exact_mod_cast hlo)

/-- A unit acts invertibly, so the quotient by its action is zero. -/
private lemma smul_top_eq_top_of_isUnit
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {x : R} (hx : IsUnit x) :
    x • (⊤ : Submodule R M) = ⊤ := by
  have hrange : LinearMap.range (LinearMap.lsmul R M x) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro m
    obtain ⟨u, hu⟩ := hx.exists_left_inv
    refine ⟨u • m, ?_⟩
    show x • (u • m) = m
    rw [smul_smul, mul_comm x u, hu, one_smul]
  simpa only [LinearMap.range_lsmul] using hrange

/-- Killing a regular element in the maximal ideal of a one-dimensional ring leaves a module
whose support has dimension zero. -/
private lemma supportDim_quotSMulTop_eq_zero
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hdim : ringKrullDim R = 1) (hsupp : Module.support R M = Set.univ)
    {x : R} (hx : IsSMulRegular M x) (hxmax : x ∈ IsLocalRing.maximalIdeal R) :
    Module.supportDim R (QuotSMulTop x M) = 0 := by
  have hsd : Module.supportDim R M = 1 :=
    (supportDim_eq_ringKrullDim_of_support_eq_univ hsupp).trans hdim
  have hdrop := Module.supportDim_quotSMulTop_succ_eq_supportDim hx hxmax
  rw [hsd] at hdrop
  exact ENat.WithBot.add_one_cancel.1 hdrop

/-- The quotient of `M` by a nonzerodivisor has finite length, under the hypotheses of the
length formula: the support of the quotient is the closed point. -/
private lemma length_quotSMulTop_ne_top_of_one_dim
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hdim : ringKrullDim R = 1) (hM : HasNoEmbeddedAssociatedPrimes R M)
    (hsupp : Module.support R M = Set.univ) {x : R}
    (hx : x ∈ nonZeroDivisors R) : Module.length R (QuotSMulTop x M) ≠ ⊤ := by
  classical
  by_cases hxmax : x ∈ IsLocalRing.maximalIdeal R
  · have hdimq := supportDim_quotSMulTop_eq_zero hdim hsupp
      (regular_on_module_of_nonZeroDivisor hM hsupp hx) hxmax
    have hcp : IsLocalRing.closedPoint R ∈ Module.support R (QuotSMulTop x M) := by
      rw [Module.support_quotSMulTop, hsupp]
      refine ⟨Set.mem_univ _, (PrimeSpectrum.mem_zeroLocus _ _).2
        (Set.singleton_subset_iff.mpr (by simpa [IsLocalRing.closedPoint] using hxmax))⟩
    have : OrderTop (Module.support R (QuotSMulTop x M)) :=
      { top := ⟨IsLocalRing.closedPoint R, hcp⟩
        le_top := fun q => by
          show q.1 ≤ IsLocalRing.closedPoint R
          exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr
            (IsLocalRing.le_maximalIdeal_of_isPrime q.1.asIdeal) }
    have hsub : Subsingleton (Module.support R (QuotSMulTop x M)) :=
      (Order.krullDim_eq_zero_iff_of_orderTop).mp (by simpa [Module.supportDim] using hdimq)
    have hsupport : Module.support R (QuotSMulTop x M) = {IsLocalRing.closedPoint R} :=
      Set.eq_singleton_iff_unique_mem.mpr ⟨hcp, fun p hp => congrArg Subtype.val
        (Subsingleton.elim (⟨p, hp⟩ : Module.support R (QuotSMulTop x M)) ⟨_, hcp⟩)⟩
    exact Module.length_ne_top_iff.mpr (isFiniteLength_of_support hsupport)
  · have hunit : IsUnit x := by
      by_contra h
      exact hxmax ((IsLocalRing.mem_maximalIdeal x).2 (by simpa [nonunits] using h))
    show Module.length R (M ⧸ (x • (⊤ : Submodule R M))) ≠ ⊤
    rw [smul_top_eq_top_of_isUnit hunit]
    simp

/-- The image of a principal submodule under a quotient map is the principal submodule
generated by the image. -/
private lemma map_span_through_ideal_quotient
    {R : Type*} [CommRing R] (I : Ideal R) (x : R) :
    Submodule.map (Submodule.mkQ I) (Ideal.span {x} : Submodule R R) =
      (Ideal.span {Ideal.Quotient.mk I x} : Submodule (R ⧸ I) (R ⧸ I)).restrictScalars R := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    rw [Ideal.mem_span_singleton] at hz
    rcases hz with ⟨c, hc⟩
    rw [← hzy]
    show Ideal.Quotient.mk I z ∈ Ideal.span {Ideal.Quotient.mk I x}
    rw [Ideal.mem_span_singleton]
    exact ⟨Ideal.Quotient.mk I c, by rw [hc, map_mul]⟩
  · intro hy
    change y ∈ Ideal.span {Ideal.Quotient.mk I x} at hy
    rw [Ideal.mem_span_singleton] at hy
    rcases hy with ⟨d, hd⟩
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (I := I) d
    exact ⟨x * c, Ideal.mem_span_singleton.mpr ⟨c, rfl⟩,
      (map_mul (Ideal.Quotient.mk I) x c).trans (by rw [hc, hd])⟩

/-- The colength of the ideal generated by `x` and a prime `q` is the order of vanishing of
`x` on the domain `R / q`. -/
private lemma length_span_sup_eq_ord_quotient
    {R : Type*} [CommRing R] (I : Ideal R) [I.IsPrime] (x : R) :
    Module.length R (R ⧸ (Ideal.span {x} ⊔ I)) =
      Ring.ord (R ⧸ I) (Ideal.Quotient.mk I x) := by
  let D := R ⧸ I
  let T : Submodule R R := Ideal.span {x}
  let E := Submodule.quotientQuotientEquivQuotientSup (M := R) I T
  let N : Submodule D D := Ideal.span {Ideal.Quotient.mk I x}
  let X := D ⧸ N
  have hm : T.map (Submodule.mkQ I) = N.restrictScalars R := by
    simpa [T, N] using map_span_through_ideal_quotient I x
  have hres : Module.length R X = Module.length D X :=
    length_restrictScalars_eq_of_surjective R D (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective X
  have e' : (D ⧸ T.map (Submodule.mkQ I)) ≃ₗ[R] X :=
    Submodule.quotEquivOfEq (T.map (Submodule.mkQ I)) (N.restrictScalars R) hm
  calc
    Module.length R (R ⧸ (Ideal.span {x} ⊔ I)) = Module.length R (R ⧸ (I ⊔ T)) := by
      rw [show Ideal.span {x} ⊔ I = I ⊔ T by simp [T, sup_comm]]
    _ = Module.length R (D ⧸ T.map (Submodule.mkQ I)) := E.length_eq.symm
    _ = Module.length R X := e'.length_eq
    _ = Module.length D X := hres
    _ = Ring.ord D (Ideal.Quotient.mk I x) := rfl

/-- Every term of a finite sum in `ℕ∞` is finite if the sum is. -/
private lemma finsum_mem_term_ne_top {α : Type*} {S : Set α} (hS : S.Finite)
    (f : α → ℕ∞) (hfin : (∑ᶠ x ∈ S, f x) ≠ ⊤) : ∀ x ∈ S, f x ≠ ⊤ := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS] at hfin
  exact fun x hx => ENat.sum_ne_top.mp hfin x (hS.mem_toFinset.mpr hx)

/-- `ENat.toNat` commutes with a finite sum of finite terms. -/
private lemma toNat_finsum_mem {α : Type*} {S : Set α} (hS : S.Finite)
    (f : α → ℕ∞) (hfin : ∀ x ∈ S, f x ≠ ⊤) :
    (∑ᶠ x ∈ S, f x).toNat = ∑ᶠ x ∈ S, (f x).toNat := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS,
    finsum_mem_eq_finite_toFinset_sum (fun x => (f x).toNat) hS, ENat.toNat_sum]
  exact fun x hx => hfin x (hS.mem_toFinset.mp hx)

/-- Multiplying a submodule by a regular scalar adds the colength of that scalar's action on
the whole module. -/
private lemma length_quotient_smul_eq
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (x : R) (N : Submodule R M) (hx : IsSMulRegular M x) :
    Module.length R (M ⧸ (x • N)) =
      Module.length R (M ⧸ N) + Module.length R (M ⧸ (x • (⊤ : Submodule R M))) := by
  have hcomap : (x • N).comap (LinearMap.lsmul R M x) = N := by
    ext m
    refine ⟨fun hm => ?_, Submodule.smul_mem_pointwise_smul _ _ _⟩
    change x • m ∈ x • N at hm
    obtain ⟨n, hn, hnm⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm
    rw [← hx hnm]
    exact hn
  have hcompat : N ≤ (x • N).comap (LinearMap.lsmul R M x) := hcomap.ge
  have hcompatG : x • N ≤ (x • (⊤ : Submodule R M)).comap LinearMap.id := by
    simpa only [Submodule.comap_id] using
      (smul_mono_right x (show N ≤ (⊤ : Submodule R M) from le_top))
  let f := Submodule.mapQ N (x • N) (LinearMap.lsmul R M x) hcompat
  let g := Submodule.mapQ (x • N) (x • (⊤ : Submodule R M)) LinearMap.id hcompatG
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    show (Submodule.mapQ N (x • N) (LinearMap.lsmul R M x) hcompat).ker = ⊥
    rw [Submodule.ker_mapQ, hcomap]
    exact Submodule.mkQ_map_self N
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk m, rfl⟩
  have hex : Function.Exact f g := by
    apply LinearMap.exact_iff.mpr
    have hker : LinearMap.ker g =
        (x • (⊤ : Submodule R M)).map (Submodule.mkQ (x • N)) := by
      show (Submodule.mapQ (x • N) (x • (⊤ : Submodule R M))
        LinearMap.id hcompatG).ker = _
      rw [Submodule.ker_mapQ]
      simp only [Submodule.comap_id]
    have hrange : LinearMap.range f =
        (x • (⊤ : Submodule R M)).map (Submodule.mkQ (x • N)) := by
      show (Submodule.mapQ N (x • N) (LinearMap.lsmul R M x) hcompat).range = _
      rw [Submodule.range_mapQ]
      simp only [LinearMap.range_lsmul]
    exact hker.trans hrange.symm
  exact Module.length_eq_add_of_exact f g hf hg hex

/-- A quotient by a larger submodule has finite length if a quotient by a smaller one does. -/
private lemma quotient_length_ne_top_of_le
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K N : Submodule R M) (hKN : K ≤ N)
    (hK : Module.length R (M ⧸ K) ≠ ⊤) : Module.length R (M ⧸ N) ≠ ⊤ :=
  Module.length_ne_top_iff.mpr <| IsFiniteLength.of_surjective
    (f := Submodule.mapQ K N LinearMap.id hKN) (Module.length_ne_top_iff.mp hK) fun y => by
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk m, rfl⟩

/-- A scalar in an ideal acts inside the submodule generated by that ideal. -/
private lemma smul_top_le_ideal_smul_top
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (x : R) (I : Ideal R) (hx : x ∈ I) :
    x • (⊤ : Submodule R M) ≤ I • (⊤ : Submodule R M) := by
  simpa [Submodule.ideal_span_singleton_smul] using Submodule.set_smul_mono_left
    (N := (⊤ : Submodule R M)) (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx))

/-- Scalar multiplication of a submodule is the image under the multiplication map. -/
private lemma map_lsmul_eq_pointwise_smul
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (x : R) (N : Submodule R M) :
    Submodule.map (LinearMap.lsmul R M x) N = x • N := by
  ext m
  simp only [Submodule.mem_map, LinearMap.lsmul_apply,
    Submodule.mem_smul_pointwise_iff_exists]

/-- For a module with full support, the minimal points of the support are the minimal primes
of the ring. -/
private lemma minimal_support_eq_minimal_primes_of_full_support
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (hsupp : Module.support R M = Set.univ) :
    {q : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q} =
      {q : PrimeSpectrum R | q.asIdeal ∈ minimalPrimes R} := by
  ext q
  rw [minimalPrimes_eq_minimals]
  show Minimal (· ∈ Module.support R M) q ↔ Minimal Ideal.IsPrime q.asIdeal
  rw [hsupp]
  constructor
  · intro hq
    change Minimal (fun _ : PrimeSpectrum R => True) q at hq
    refine ⟨q.isPrime, fun p hp hpq => ?_⟩
    exact (PrimeSpectrum.asIdeal_le_asIdeal q ⟨p, hp⟩).mp
      (hq.2 trivial ((PrimeSpectrum.asIdeal_le_asIdeal ⟨p, hp⟩ q).mpr hpq))
  · intro hq
    show Minimal (fun _ : PrimeSpectrum R => True) q
    refine ⟨trivial, fun p hp hpq => ?_⟩
    exact (PrimeSpectrum.asIdeal_le_asIdeal q p).mpr
      (hq.2 p.isPrime ((PrimeSpectrum.asIdeal_le_asIdeal p q).mp hpq))

/-- A Noetherian ring has finitely many minimal primes. -/
@[ega "0 1.1.1" "the ideal a = (0)"]
private lemma finite_minimal_primes_spectrum {R : Type*} [CommRing R] [IsNoetherianRing R] :
    {q : PrimeSpectrum R | q.asIdeal ∈ minimalPrimes R}.Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing R (⊥ : Ideal R)).preimage
    (fun _ _ _ _ h => PrimeSpectrum.ext h)

/-- The denominator ideal of the fraction `a / b`: the elements `x` such that `x * a` is a
multiple of `b`. -/
def denominatorIdeal {R : Type*} [CommRing R] (a b : R) : Ideal R :=
  (Ideal.span {b}).colon (Ideal.span {a})

/-- Membership in the denominator ideal, in equation form. -/
theorem mem_denominatorIdeal_iff {R : Type*} [CommRing R] {a b x : R} :
    x ∈ denominatorIdeal a b ↔ ∃ y : R, x * a = y * b := by
  rw [denominatorIdeal, Ideal.mem_colon_span_singleton, Ideal.mem_span_singleton]
  constructor <;> rintro ⟨y, hy⟩ <;> exact ⟨y, by simpa [mul_comm] using hy⟩

/-- The ideal `(a / b) I`, where `I` is the denominator ideal of `a / b`. Concretely it is the
ideal of `y` such that `y * b` is a multiple of `a`. -/
def fractionalProductIdeal {R : Type*} [CommRing R] (a b : R) : Ideal R :=
  (Ideal.span {a}).colon (Ideal.span {b})

/-- Membership in the fractional product ideal, in equation form. -/
theorem mem_fractionalProductIdeal_iff {R : Type*} [CommRing R] {a b y : R} :
    y ∈ fractionalProductIdeal a b ↔ ∃ x : R, y * b = x * a := by
  rw [fractionalProductIdeal, Ideal.mem_colon_span_singleton, Ideal.mem_span_singleton]
  constructor <;> rintro ⟨x, hx⟩ <;> exact ⟨x, by simpa [mul_comm] using hx⟩

/-- Multiplication by `b` carries `(a / b) I M` into `a I M`. -/
private lemma map_fractionalProduct_module_le
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (a b : R) :
    (fractionalProductIdeal a b • (⊤ : Submodule R M)).map (LinearMap.lsmul R M b) ≤
      (denominatorIdeal a b • (⊤ : Submodule R M)).map (LinearMap.lsmul R M a) := by
  intro z hz
  simp only [Submodule.mem_map] at hz ⊢
  rcases hz with ⟨m, hm, rfl⟩
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro r hr v hv
    obtain ⟨x, hx⟩ := mem_fractionalProductIdeal_iff.mp hr
    have hI : x ∈ denominatorIdeal a b := mem_denominatorIdeal_iff.mpr ⟨r, hx.symm⟩
    refine ⟨x • v, Submodule.smul_mem_smul hI Submodule.mem_top, ?_⟩
    show a • (x • v) = b • (r • v)
    rw [smul_smul, smul_smul, show a * x = b * r by linear_combination hx.symm]
  · intro u v hu hv
    rcases hu with ⟨u', hu', hU⟩
    rcases hv with ⟨v', hv', hV⟩
    refine ⟨u' + v', Submodule.add_mem _ hu' hv', ?_⟩
    rw [map_add, map_add, hU, hV]

/-- Multiplication by `b` carries `(a / b) I M` exactly onto `a I M`. -/
private lemma map_fractionalProduct_module_eq
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (a b : R) :
    (fractionalProductIdeal a b • (⊤ : Submodule R M)).map (LinearMap.lsmul R M b) =
      (denominatorIdeal a b • (⊤ : Submodule R M)).map (LinearMap.lsmul R M a) := by
  apply le_antisymm (map_fractionalProduct_module_le a b)
  simpa only [denominatorIdeal, fractionalProductIdeal] using
    (map_fractionalProduct_module_le (M := M) b a)

/-- **Stacks Project, Tag 02QH, containment assertion.** Multiplying `I M` by `a / b` in the
localization of `M` at the nonzerodivisors lands back in the image of `M`. -/
@[stacks 02QH "containment"]
theorem fraction_smul_denominatorIdeal_le
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a b : R) (hb : b ∈ nonZeroDivisors R) :
    ∀ x ∈ denominatorIdeal a b • (⊤ : Submodule R M),
      IsLocalization.mk' (FractionRing R) a ⟨b, hb⟩ •
          LocalizedModule.mkLinearMap (nonZeroDivisors R) M x ∈
        Set.range (LocalizedModule.mkLinearMap (nonZeroDivisors R) M) := by
  intro x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr m hm
    obtain ⟨y, hy⟩ := mem_denominatorIdeal_iff.mp hr
    refine ⟨y • m, ?_⟩
    show LocalizedModule.mk (y • m) 1 =
      IsLocalization.mk' (FractionRing R) a ⟨b, hb⟩ •
        LocalizedModule.mkLinearMap (nonZeroDivisors R) M (r • m)
    rw [LocalizedModule.mkLinearMap_apply]
    have hsmul : IsLocalization.mk' (FractionRing R) a ⟨b, hb⟩ •
        LocalizedModule.mk (r • m) (1 : nonZeroDivisors R) =
          LocalizedModule.mk (a • (r • m)) ⟨b, hb⟩ := by
      rw [← Localization.mk_eq_mk', LocalizedModule.mk_smul_mk]
      simp
    rw [hsmul]
    apply LocalizedModule.mk_eq.mpr
    refine ⟨1, ?_⟩
    simp only [one_smul]
    show b • (y • m) = a • (r • m)
    rw [smul_smul, smul_smul, show b * y = a * r by linear_combination hy.symm]
  · intro x y hx hy
    rcases hx with ⟨u, hu⟩
    rcases hy with ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    show LocalizedModule.mkLinearMap (nonZeroDivisors R) M (u + v) =
      IsLocalization.mk' (FractionRing R) a ⟨b, hb⟩ •
        LocalizedModule.mkLinearMap (nonZeroDivisors R) M (x + y)
    rw [map_add, map_add, hu, hv, smul_add]

/-- **Stacks Project, Tag 02QH, length formula.** The difference between the colength of
`(a / b) I M` and that of `I M` is the sum of the generic lengths of `M`, weighted by the
orders of `a / b` on the irreducible components. -/
@[stacks 02QH "length formula"]
theorem length_fractionalProduct_quotient_sub_length_denominator_quotient
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a b : R) (ha : a ∈ nonZeroDivisors R) (hb : b ∈ nonZeroDivisors R)
    (hRdim : ringKrullDim R = 1)
    (hMembedded : HasNoEmbeddedAssociatedPrimes R M)
    (hMsupport : Module.support R M = Set.univ) :
    ((Module.length R
        (M ⧸ fractionalProductIdeal a b • (⊤ : Submodule R M))).toNat : ℤ) -
      ((Module.length R
        (M ⧸ denominatorIdeal a b • (⊤ : Submodule R M))).toNat : ℤ) =
      ∑ᶠ q ∈ {q : PrimeSpectrum R | q.asIdeal ∈ minimalPrimes R},
        ((Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) *
          (((Ring.ord (R ⧸ q.asIdeal)
            (Ideal.Quotient.mk q.asIdeal a)).toNat : ℤ) -
            ((Ring.ord (R ⧸ q.asIdeal)
              (Ideal.Quotient.mk q.asIdeal b)).toNat : ℤ)) := by
  classical
  let I : Ideal R := denominatorIdeal a b
  let J : Ideal R := fractionalProductIdeal a b
  let QI : Submodule R M := I • (⊤ : Submodule R M)
  let QJ : Submodule R M := J • (⊤ : Submodule R M)
  let S : Set (PrimeSpectrum R) := {q | q.asIdeal ∈ minimalPrimes R}
  have hMdim : Module.supportDim R M = 1 :=
    (supportDim_eq_ringKrullDim_of_support_eq_univ hMsupport).trans hRdim
  have hCM := cm_of_no_embedded_full_support_one_dim hRdim hMembedded hMsupport
  have hregA := regular_on_module_of_nonZeroDivisor hMembedded hMsupport ha
  have hregB := regular_on_module_of_nonZeroDivisor hMembedded hMsupport hb
  have hfiniteS : S.Finite := finite_minimal_primes_spectrum
  have hminset : {q : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q} = S :=
    minimal_support_eq_minimal_primes_of_full_support hMsupport
  have hsum (x : R) (hx : IsSMulRegular M x) :
      Module.length R (QuotSMulTop x M) =
        ∑ᶠ q ∈ S, Ring.ord (R ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal x) *
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M) := by
    by_cases haunit : IsUnit x
    · have hzero : Module.length R (QuotSMulTop x M) = 0 := by
        show Module.length R (M ⧸ (x • (⊤ : Submodule R M))) = 0
        rw [smul_top_eq_top_of_isUnit haunit]
        simp
      rw [hzero]
      simp only [Ring.ord_of_isUnit (RingHom.isUnit_map (Ideal.Quotient.mk _) haunit),
        zero_mul, finsum_zero]
    · have hamax : x ∈ IsLocalRing.maximalIdeal R :=
        (IsLocalRing.mem_maximalIdeal x).2 (by simpa [nonunits] using haunit)
      have hdimA := supportDim_quotSMulTop_eq_zero hRdim hMsupport hx hamax
      have hform := AlgebraicGeometry.length_quotSMulTop_eq_sum_minimal_support
        x hCM hMdim hdimA
      rw [hminset] at hform
      have hsumRewrite :
          (∑ᶠ q ∈ S,
            Module.length R (R ⧸ (Ideal.span {x} ⊔ q.asIdeal)) *
              Module.length (Localization.AtPrime q.asIdeal)
                (LocalizedModule q.asIdeal.primeCompl M)) =
          ∑ᶠ q ∈ S,
            Ring.ord (R ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal x) *
              Module.length (Localization.AtPrime q.asIdeal)
                (LocalizedModule q.asIdeal.primeCompl M) := by
        rw [finsum_mem_eq_finite_toFinset_sum _ hfiniteS,
          finsum_mem_eq_finite_toFinset_sum _ hfiniteS]
        apply Finset.sum_congr rfl
        intro q hq
        have : q.asIdeal.IsPrime := q.isPrime
        rw [length_span_sup_eq_ord_quotient]
      exact hform.trans hsumRewrite
  have hFin (x : R) (hx : x ∈ nonZeroDivisors R) :
      Module.length R (M ⧸ (x • (⊤ : Submodule R M))) ≠ ⊤ :=
    length_quotSMulTop_ne_top_of_one_dim hRdim hMembedded hMsupport hx
  have hNat (x : R) (hx : x ∈ nonZeroDivisors R) :
      ((Module.length R (M ⧸ (x • (⊤ : Submodule R M)))).toNat : ℤ) =
        ∑ q ∈ hfiniteS.toFinset,
          ((Module.length (Localization.AtPrime q.asIdeal)
              (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) *
            ((Ring.ord (R ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal x)).toNat : ℤ) := by
    have hs := hsum x (regular_on_module_of_nonZeroDivisor hMembedded hMsupport hx)
    have h := congrArg ENat.toNat hs
    rw [toNat_finsum_mem hfiniteS _
      (finsum_mem_term_ne_top hfiniteS _ (by rw [← hs]; exact hFin x hx)),
      finsum_mem_eq_finite_toFinset_sum _ hfiniteS] at h
    simp only [ENat.toNat_mul] at h
    change ((Module.length R (QuotSMulTop x M)).toNat : ℤ) = _
    rw [h]
    norm_cast
    exact Finset.sum_congr rfl fun q hq => by ring
  have hbI : b ∈ I := mem_denominatorIdeal_iff.mpr ⟨a, by ring⟩
  have haJ : a ∈ J := mem_fractionalProductIdeal_iff.mpr ⟨b, by ring⟩
  have hlenI : Module.length R (M ⧸ QI) ≠ ⊤ :=
    quotient_length_ne_top_of_le _ _ (smul_top_le_ideal_smul_top b I hbI) (hFin b hb)
  have hlenJ : Module.length R (M ⧸ QJ) ≠ ⊤ :=
    quotient_length_ne_top_of_le _ _ (smul_top_le_ideal_smul_top a J haJ) (hFin a ha)
  have hprod : b • QJ = a • QI := by
    simpa only [QI, QJ, map_lsmul_eq_pointwise_smul] using
      map_fractionalProduct_module_eq (R := R) (M := M) a b
  have hadd :
      Module.length R (M ⧸ QJ) + Module.length R (M ⧸ (b • (⊤ : Submodule R M))) =
      Module.length R (M ⧸ QI) + Module.length R (M ⧸ (a • (⊤ : Submodule R M))) := by
    rw [← length_quotient_smul_eq b QJ hregB, ← length_quotient_smul_eq a QI hregA, hprod]
  have haddInt :
      ((Module.length R (M ⧸ QJ)).toNat : ℤ) +
          ((Module.length R (M ⧸ (b • (⊤ : Submodule R M)))).toNat : ℤ) =
        ((Module.length R (M ⧸ QI)).toNat : ℤ) +
          ((Module.length R (M ⧸ (a • (⊤ : Submodule R M)))).toNat : ℤ) := by
    have h := congrArg ENat.toNat hadd
    rw [ENat.toNat_add hlenJ (hFin b hb), ENat.toNat_add hlenI (hFin a ha)] at h
    exact_mod_cast h
  have hfiniteSum :
      (∑ q ∈ hfiniteS.toFinset,
        ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) *
          (((Ring.ord (R ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal a)).toNat : ℤ) -
            ((Ring.ord (R ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal b)).toNat : ℤ))) =
      (∑ q ∈ hfiniteS.toFinset,
        ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) *
          ((Ring.ord (R ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal a)).toNat : ℤ)) -
      (∑ q ∈ hfiniteS.toFinset,
        ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) *
          ((Ring.ord (R ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal b)).toNat : ℤ)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfiniteS, hfiniteSum, ← hNat a ha, ← hNat b hb]
  linear_combination haddInt
end Ideal
