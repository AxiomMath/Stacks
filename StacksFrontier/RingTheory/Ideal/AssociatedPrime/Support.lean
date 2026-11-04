module

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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Regular.IsSMulRegular
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
public import Mathlib.Topology.Sheaves.Init

import StacksCore.Tactic.StacksAttribute

/-!
# Associated primes and the support

Let `R` be a Noetherian ring and `M` an `R`-module. This file shows that the primes minimal in
`Supp(M)` are associated primes of `M`, and, for `M` finite, that they are exactly the minimal
elements of `Ass(M)`. It also shows that the canonical map `M → ∏_{𝔭 ∈ Ass(M)} M_𝔭` is injective.

## Main definitions

* `assMap`: the canonical map from `M` to the product of its localizations at the associated primes
  of `M`.

## Main results

* `Module.setOf_minimal_support_eq_setOf_minimal_associatedPrimes`: for `M` finite, the minimal
  points of `Supp(M)` are exactly the minimal elements of `Ass(M)`.
* `zero_at_ass_zero`: the map `assMap R M` is injective.
* `Module.mem_associatedPrimes_of_minimal_mem_support`: a prime minimal in `Supp(M)` lies in
  `Ass(M)`.

## References

* [Stacks Project, Tag 02CE](https://stacks.math.columbia.edu/tag/02CE)
* [Stacks Project, Tag 0311](https://stacks.math.columbia.edu/tag/0311)
* [Stacks Project, Tag 05BV](https://stacks.math.columbia.edu/tag/05BV)
* [Stacks Project, Tag 00LD](https://stacks.math.columbia.edu/tag/00LD)

## Tags

associated prime, support, minimal prime, Noetherian ring
-/

@[expose] public section

section

namespace Stacks.AssociatedPrimes.MinimalSupport

/-- If `s ⊆ t`, every minimal element of `t` lies in `s`, and every element of `t` lies above some
minimal element of `t`, then `s` and `t` have the same minimal elements. -/
private theorem setOfPred_minimal_eq_of_setOfPred_minimal_subset {α : Type*} [Preorder α]
    {s t : Set α} (hst : s ⊆ t) (hts : {x | Minimal (· ∈ t) x} ⊆ s)
    (hex : ∀ x ∈ t, ∃ y, Minimal (· ∈ t) y ∧ y ≤ x) :
    {x | Minimal (· ∈ t) x} = {x | Minimal (· ∈ s) x} := by
  ext x
  refine ⟨fun hx ↦ hx.mono hst (hts hx), fun hx ↦ ?_⟩
  obtain ⟨y, hy, hyx⟩ := hex x (hst hx.1)
  have hxy : x ≤ y := hx.2 (hts hy) hyx
  exact ⟨hst hx.1, fun z hz hzx ↦ hxy.trans (hy.2 hz (hzx.trans hxy))⟩

/-- A point of `Spec R` is minimal in the closed set `V(I)` exactly when its ideal is a minimal
prime over `I`. -/
private theorem minimal_mem_zeroLocus_iff {R : Type*} [CommRing R] {I : Ideal R}
    {q : PrimeSpectrum R} :
    Minimal (· ∈ PrimeSpectrum.zeroLocus (I : Set R)) q ↔ q.asIdeal ∈ I.minimalPrimes := by
  show Minimal (fun p : PrimeSpectrum R ↦ I ≤ p.asIdeal) q ↔
    Minimal (fun J : Ideal R ↦ J.IsPrime ∧ I ≤ J) q.asIdeal
  exact ⟨fun hq ↦ ⟨⟨q.isPrime, hq.1⟩, fun p hp hpq ↦ hq.2 (y := ⟨p, hp.1⟩) hp.2 hpq⟩,
    fun hq ↦ ⟨hq.1.2, fun r hr hrq ↦ hq.2 ⟨r.isPrime, hr⟩ hrq⟩⟩

section Support

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- An associated prime of `M` lies in the support of `M`. -/
private theorem preimage_associatedPrimes_subset_support :
    PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M ⊆ Module.support R M := by
  rintro q ⟨-, x, hx⟩
  refine Module.mem_support_iff_exists_annihilator.mpr ⟨x, ?_⟩
  rw [hx, ← Submodule.bot_colon']
  exact Ideal.le_radical

variable [Module.Finite R M]

/-- The primes minimal in `Supp(M)`, for `M` a finite module, are the minimal primes over
`Ann(M)`. -/
private theorem minimal_mem_support_iff {q : PrimeSpectrum R} :
    Minimal (· ∈ Module.support R M) q ↔ q.asIdeal ∈ (Module.annihilator R M).minimalPrimes := by
  rw [Module.support_eq_zeroLocus, minimal_mem_zeroLocus_iff]

/-- Every point of the support of a finite module lies above a minimal point of the support. -/
private theorem exists_minimal_mem_support_le {q : PrimeSpectrum R}
    (hq : q ∈ Module.support R M) : ∃ p, Minimal (· ∈ Module.support R M) p ∧ p ≤ q := by
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (Module.annihilator_le_of_mem_support hq)
  exact ⟨⟨p, hp.isPrime⟩, minimal_mem_support_iff.mpr hp, hpq⟩

end Support

end Stacks.AssociatedPrimes.MinimalSupport

namespace Module

open Stacks.AssociatedPrimes.MinimalSupport in
/-- Let `R` be a Noetherian ring and `M` a finite `R`-module. The primes minimal in `Supp(M)` are
exactly the primes minimal in `Ass(M)`. -/
@[stacks 02CE "Parts (1) and (2); the equality with part (3) is the first conclusion of \
  Stacks 00L7, which the source's own proof cites for that step."]
public theorem setOf_minimal_support_eq_setOf_minimal_associatedPrimes {R M : Type*} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] :
    {q : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q} =
      {q : PrimeSpectrum R | Minimal (· ∈ PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M) q} :=
  setOfPred_minimal_eq_of_setOfPred_minimal_subset preimage_associatedPrimes_subset_support
    (fun _ hq ↦ Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M
      (minimal_mem_support_iff.mp hq))
    fun _ hq ↦ exists_minimal_mem_support_le hq

end Module

end

@[expose] public section

/-- The canonical $R$-linear comparison map
$\varphi \colon M \to \prod_{\mathfrak{p} \in \operatorname{Ass}(M)} M_{\mathfrak{p}}$, whose
$\mathfrak{p}$-th component is the localization map $m \mapsto m/1$. -/
noncomputable def assMap (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    M →ₗ[R] (∀ p : associatedPrimes R M, LocalizedModule p.val.primeCompl M) :=
  LinearMap.pi (fun p => LocalizedModule.mkLinearMap p.val.primeCompl M)

/-- Over a Noetherian ring, the canonical map from $M$ into the product of its localizations at
associated primes is injective. -/
@[stacks 0311]
theorem zero_at_ass_zero (R : Type*) [CommRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Injective (assMap R M) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have key : ∀ p : associatedPrimes R M, ∃ s : p.val.primeCompl, (s : R) • x = 0 := by
    intro p
    have hp := congrFun hx p
    simp only [assMap, LinearMap.pi_apply, LocalizedModule.mkLinearMap_apply, Pi.zero_apply] at hp
    rw [show (0 : LocalizedModule p.val.primeCompl M) = LocalizedModule.mk 0 1 from
      (LocalizedModule.zero_mk 1).symm, LocalizedModule.mk_eq] at hp
    obtain ⟨u, hu⟩ := hp
    exact ⟨u, by simpa only [Submonoid.smul_def, OneMemClass.coe_one, one_smul, smul_zero] using hu⟩
  set N : Submodule R M := Submodule.span R {x}
  have hempty : ∀ q : Ideal R, ¬ IsAssociatedPrime q N := by
    intro q hq
    obtain ⟨s, hs⟩ := key ⟨q, hq.map_of_injective N.subtype N.injective_subtype⟩
    obtain ⟨-, n, hncolon⟩ := id hq
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (n.property : (n : M) ∈ Submodule.span R {x})
    have hmem : ∀ t : R, t • n = 0 → t ∈ q := fun t ht ↦ by
      rw [hncolon]
      refine Ideal.le_radical (Submodule.mem_colon.mpr fun c hc ↦ ?_)
      rwa [Set.mem_singleton_iff.mp hc, Submodule.mem_bot]
    refine s.property (hmem _ (Subtype.ext ?_))
    show (s : R) • (n : M) = 0
    rw [← hr, smul_smul, mul_comm, ← smul_smul, hs, smul_zero]
  have : Subsingleton N := not_nontrivial_iff_subsingleton.mp fun _ ↦
    let ⟨q, hq⟩ := associatedPrimes.nonempty R N
    hempty q hq
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, Submodule.mem_span_singleton_self x⟩ : N) 0)

@[expose] public section

namespace Stacks.AssociatedPrimes.GenericPoint

section

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The support of a submodule is contained in the support of the ambient module. -/
private theorem support_subset_support_span_singleton (m : M) :
    Module.support R ↥(R ∙ m) ⊆ Module.support R M :=
  Module.support_subset_of_injective (R ∙ m).subtype Subtype.val_injective

/-- The support of a module is the union of the supports of its cyclic submodules,
`Supp(M) = ⋃_{m ∈ M} Supp(R·m)`. -/
private theorem support_eq_iUnion_support_span_singleton :
    Module.support R M = ⋃ m : M, Module.support R ↥(R ∙ m) := by
  refine Set.Subset.antisymm (fun p hp ↦ ?_) (Set.iUnion_subset
    support_subset_support_span_singleton)
  obtain ⟨m, hm⟩ := Module.mem_support_iff_exists_annihilator.mp hp
  exact Set.mem_iUnion.mpr ⟨m, Module.mem_support_iff_of_finite.mpr hm⟩

/-- For `M` finite over a Noetherian ring, a prime minimal in `Supp(M)` is associated to `M`. -/
private theorem mem_associatedPrimes_of_minimal_mem_support_of_finite [IsNoetherianRing R]
    [Module.Finite R M] {p : PrimeSpectrum R} (hp : Minimal (· ∈ Module.support R M) p) :
    p.asIdeal ∈ associatedPrimes R M :=
  have hp' : Minimal (· ∈ PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M) p :=
    Module.setOf_minimal_support_eq_setOf_minimal_associatedPrimes.subset hp
  hp'.prop

end

/-- Over a Noetherian ring, a prime minimal in the support of `M` is an associated prime of `M`. -/
public theorem solution {R : Type*} [CommRing R]
    [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M] {p : PrimeSpectrum R}
    (hp : Minimal (· ∈ Module.support R M) p) :
    p.asIdeal ∈ associatedPrimes R M := by
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (support_eq_iUnion_support_span_singleton.subset hp.prop)
  exact associatedPrimes.subset_of_injective (f := (R ∙ m).subtype) Subtype.val_injective
    (mem_associatedPrimes_of_minimal_mem_support_of_finite (hp.mono
      (support_subset_support_span_singleton m) hm))

end Stacks.AssociatedPrimes.GenericPoint

end

@[expose] public section

/-- Let `R` be a Noetherian ring and let `M` be an `R`-module. Any prime `𝔭` which is minimal among
the elements of the support of `M` is an associated prime of `M`. -/
@[stacks 05BV]
public theorem Module.mem_associatedPrimes_of_minimal_mem_support {R : Type*} [CommRing R]
    [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M] {p : PrimeSpectrum R}
    (hp : Minimal (· ∈ Module.support R M) p) :
    p.asIdeal ∈ associatedPrimes R M :=
  Stacks.AssociatedPrimes.GenericPoint.solution hp

end

end
end

/-!
### Associated primes and zerodivisors

Over a Noetherian ring, the union of the associated primes of `M` is the set of zerodivisors on
`M`: this is `biUnion_associatedPrimes_eq_zero_divisors`, and
`biUnion_associatedPrimes_eq_compl_regular` phrases it via `IsSMulRegular`.
-/

@[expose] public section

add_to_stacks 00LD biUnion_associatedPrimes_eq_zero_divisors
add_to_ega "IV 20.2.13" "S" biUnion_associatedPrimes_eq_zero_divisors
add_to_stacks 00LD "the same union, phrased via `IsSMulRegular`"
  biUnion_associatedPrimes_eq_compl_regular
add_to_ega "IV 20.2.13" "S" biUnion_associatedPrimes_eq_compl_regular

end
