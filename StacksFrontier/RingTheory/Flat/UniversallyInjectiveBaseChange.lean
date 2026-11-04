module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.LinearAlgebra.TensorProduct.InjectiveComposition
public import StacksFrontier.RingTheory.EssentialFiniteness.Composition
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.RingTheory.Flat.RegularSequenceOverBase
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Basic
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import StacksFrontier.RingTheory.Noetherian.Spec

/-!
# Universal injectivity of a flat base change over a local base

Let `R → S` be a local homomorphism of local rings which is essentially of finite presentation,
let `N` be a finitely presented `S`-module which is flat over `R`, and let `S → S'` be a flat
ring map. Writing `Σ ⊆ S` for the set of elements acting injectively on the closed fibre
`N / 𝔪_R N`:

* the localization `Σ⁻¹S` is semilocal, its maximal ideals coming from the associated primes of
  the closed fibre;
* each element of `Σ` acts on `N` by a universally injective homothety, and `N → Σ⁻¹N` is
  universally injective over `R`;
* if the image of `Spec(S') → Spec(S)` contains every associated prime of the closed fibre, then
  `N → N ⊗[S] S'` is universally injective over `R`.

## Main results

* `Stacks.UniversalInjectivity.finite_maximalSpectrum_localization_nonZeroSMulDivisors`:
  the localization at the elements regular on the closed fibre is semilocal.
* `Stacks.UniversalInjectivity.range_under_localization_nonZeroSMulDivisors`: its prime
  spectrum, described by contraction to `S`.
* `Stacks.UniversalInjectivity.exists_assStacks_closedFibre_of_isMaximal_localization`: the
  associated prime of the closed fibre attached to a maximal ideal of the localization.
* `Stacks.UniversalInjectivity.universallyInjectivePoly_lsmul_of_nonZeroSMulDivisors`: the
  homotheties by elements regular on the closed fibre are universally injective over `R`.
* `Stacks.UniversalInjectivity.universallyInjectivePoly_mkLinearMap_nonZeroSMulDivisors`:
  so is the canonical map from `N` to that localization.
* `Stacks.UniversalInjectivity.universallyInjectivePoly_tensorUnit_of_flat`: the canonical map
  `N → N ⊗[S] S'` is universally injective over `R`.

## Implementation notes

The multiplicative subset of the source is Mathlib's `nonZeroSMulDivisors`, and the closed
fibre is the quotient of `N` by `Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) • ⊤`,
so that the closed-fibre module is a module over the closed-fibre ring. Associated primes are
the strict associated primes `IsAssociatedPrimeStacks`/`assStacks` of Stacks 00LA, where the
annihilator of an element is required to equal the prime exactly rather than up to radical.
Semilocality is finiteness of `MaximalSpectrum`.

Universal injectivity is the universe-polymorphic `UniversallyInjectivePoly`: the test module
ranges over an arbitrary universe, and the source and target of the map need not share one.

The hypothesis on the image of `Spec(S') → Spec(S)` is spelled out as the existence of a prime
of `S'` with the prescribed contraction, and the canonical base-change map `n ↦ n ⊗ 1` is
`(TensorProduct.mk S N S').flip 1`.

## References

* [Stacks Project, Tag 05DE](https://stacks.math.columbia.edu/tag/05DE)
* [Stacks Project, Tag 05DF](https://stacks.math.columbia.edu/tag/05DF)
* [Stacks Project, Tag 05DG](https://stacks.math.columbia.edu/tag/05DG)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u v w x

namespace Stacks.UniversalInjectivity

/-! ### The localization at the elements regular on the closed fibre

In this section `I ⊆ A` is an ideal such that `M` is a module over `A ⧸ I`; in the applications
`I` cuts out the closed fibre. -/

section AssociatedPrimes

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- The colon ideal of `⊥` by a singleton is the torsion ideal of the element. -/
private lemma bot_colon_singleton_eq_torsionOf (m : M) :
    (⊥ : Submodule A M).colon ({m} : Set M) = Ideal.torsionOf A M m := by
  rw [Submodule.bot_colon', Ideal.annihilator_span_singleton_eq_torsionOf]

/-- The strict associated primes of Stacks 00LA are the associated primes of Stacks 05BY. -/
private lemma assStacks_eq_assPrimes : assStacks A M = Stacks.AssociatedPrimes.assPrimes A M := by
  ext p
  simp only [mem_assStacks_iff, Stacks.AssociatedPrimes.mem_assPrimes_iff]
  constructor
  · rintro ⟨hp, m, hm⟩
    have hm' : (⊥ : Submodule A M).colon ({m} : Set M) = p := by
      simpa [Submodule.colon_span] using hm
    exact ⟨hp, m, (bot_colon_singleton_eq_torsionOf m).symm.trans hm'⟩
  · rintro ⟨hp, m, hm⟩
    have hm' : (⊥ : Submodule A M).colon ({m} : Set M) = p :=
      (bot_colon_singleton_eq_torsionOf m).trans hm
    exact ⟨hp, m, by simpa [Submodule.colon_span] using hm'⟩

/-- Over a Noetherian ring the associated primes of Stacks 05BY are Mathlib's
`associatedPrimes`. -/
private lemma assPrimes_eq_associatedPrimes [IsNoetherianRing A] :
    Stacks.AssociatedPrimes.assPrimes A M = associatedPrimes A M := by
  ext p
  rw [Stacks.AssociatedPrimes.mem_assPrimes_iff, AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
  constructor
  · rintro ⟨hp, m, hm⟩
    exact ⟨hp, m, hm.symm.trans (bot_colon_singleton_eq_torsionOf m).symm⟩
  · rintro ⟨hp, m, hm⟩
    exact ⟨hp, m, (bot_colon_singleton_eq_torsionOf m).symm.trans hm.symm⟩

/-- The primes of `A` that survive the localization at the regular elements are exactly the
primes disjoint from the regular elements. -/
private lemma range_under_localization {T : Type*} [CommRing T] [Algebra A T]
    [IsLocalization (nonZeroSMulDivisors A M) T] :
    Set.range (fun q : PrimeSpectrum T => q.asIdeal.under A) =
      {p : Ideal A | p.IsPrime ∧ Disjoint (nonZeroSMulDivisors A M : Set A) (p : Set A)} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    have h := (IsLocalization.isPrime_iff_isPrime_disjoint
      (nonZeroSMulDivisors A M) T q.asIdeal).mp q.isPrime
    exact ⟨h.1, h.2⟩
  · rintro ⟨hp, hdis⟩
    refine ⟨⟨Ideal.map (algebraMap A T) p,
      IsLocalization.isPrime_of_isPrime_disjoint (nonZeroSMulDivisors A M) T p hp hdis⟩, ?_⟩
    show (Ideal.map (algebraMap A T) p).under A = p
    exact IsLocalization.under_map_of_isPrime_disjoint (nonZeroSMulDivisors A M) T hp hdis

/-- For a module over `A ⧸ I`, the associated primes over `A` are the contractions of the
associated primes over `A ⧸ I`. -/
private lemma assStacks_quotient_comap (I : Ideal A) [Module (A ⧸ I) M]
    [IsScalarTower A (A ⧸ I) M] :
    assStacks A M =
      (fun p : Ideal (A ⧸ I) => p.comap (Ideal.Quotient.mk I)) '' assStacks (A ⧸ I) M := by
  rw [assStacks_eq_assPrimes (A := A), ← Stacks.AssociatedPrimes.main_theorem_05by (I := I),
    ← assStacks_eq_assPrimes (A := A ⧸ I)]

/-- An element of `A` acts regularly on a module over `A ⧸ I` exactly when its class does. -/
private lemma isSMulRegular_quotient_iff (I : Ideal A) [Module (A ⧸ I) M]
    [IsScalarTower A (A ⧸ I) M] (y : A) :
    IsSMulRegular M y ↔ IsSMulRegular M (Ideal.Quotient.mk I y) := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul, isSMulRegular_iff_right_eq_zero_of_smul]
  constructor <;> intro h m hm <;> apply h m
  · rwa [← IsScalarTower.algebraMap_smul (A ⧸ I) y m, Ideal.Quotient.algebraMap_eq]
  · rwa [← IsScalarTower.algebraMap_smul (A ⧸ I) y m, Ideal.Quotient.algebraMap_eq] at hm

variable (I : Ideal A) [Module (A ⧸ I) M] [IsScalarTower A (A ⧸ I) M] [IsNoetherianRing (A ⧸ I)]
  [Module.Finite (A ⧸ I) M]

include I

omit [Module A M] [IsScalarTower A (A ⧸ I) M] in
/-- A finite module over a Noetherian ring has finitely many associated primes. -/
private lemma assStacks_finite_of_quotient : (assStacks (A ⧸ I) M).Finite := by
  simpa only [assStacks_eq_assPrimes, assPrimes_eq_associatedPrimes] using
    associatedPrimes.finite (A ⧸ I) M

/-- A finite module over a Noetherian quotient has finitely many associated primes over `A`. -/
private lemma assStacks_finite : (assStacks A M).Finite := by
  rw [assStacks_quotient_comap (A := A) (M := M) I]
  exact (assStacks_finite_of_quotient (A := A) (M := M) I).image _

omit [Module A M] [IsScalarTower A (A ⧸ I) M] [Module.Finite (A ⧸ I) M] in
/-- The union of the associated primes over `A ⧸ I` is the set of non-regular elements. -/
private lemma biUnion_assStacks_quotient_eq_compl_regular :
    (⋃ p ∈ assStacks (A ⧸ I) M, (p : Set (A ⧸ I))) =
      (nonZeroSMulDivisors (A ⧸ I) M : Set (A ⧸ I))ᶜ := by
  simp only [assStacks_eq_assPrimes, assPrimes_eq_associatedPrimes,
    biUnion_associatedPrimes_eq_compl_regular]
  ext y
  simp [isSMulRegular_iff_mem_nonZeroSMulDivisors]

omit [IsNoetherianRing (A ⧸ I)] [Module.Finite (A ⧸ I) M] in
/-- The union of the associated primes over `A` is the preimage of the union over `A ⧸ I`. -/
private lemma biUnion_assStacks_quotient_preimage :
    (⋃ p ∈ assStacks A M, (p : Set A)) =
      (Ideal.Quotient.mk I) ⁻¹' (⋃ p ∈ assStacks (A ⧸ I) M, (p : Set (A ⧸ I))) := by
  ext y
  rw [assStacks_quotient_comap (A := A) (M := M) I]
  simp [Set.mem_iUnion, Set.mem_preimage, Set.mem_image]

omit [Module.Finite (A ⧸ I) M] in
/-- The union of the associated primes over `A` is the set of non-regular elements. -/
private lemma biUnion_assStacks_eq_compl_regular :
    (⋃ p ∈ assStacks A M, (p : Set A)) = (nonZeroSMulDivisors A M : Set A)ᶜ := by
  rw [biUnion_assStacks_quotient_preimage (A := A) (M := M) I,
    biUnion_assStacks_quotient_eq_compl_regular (A := A) (M := M) I]
  ext y
  show ¬ (Ideal.Quotient.mk I y ∈ nonZeroSMulDivisors (A ⧸ I) M) ↔
    ¬ (y ∈ nonZeroSMulDivisors A M)
  exact not_congr <|
    (isSMulRegular_iff_mem_nonZeroSMulDivisors (M := M)).symm.trans <|
      (isSMulRegular_quotient_iff (A := A) (M := M) I y).symm.trans <|
        isSMulRegular_iff_mem_nonZeroSMulDivisors (M := M)

/-- An ideal survives the localization at the regular elements exactly when it is contained in
an associated prime. -/
lemma localization_disjoint_iff_exists_assStacks (J : Ideal A) :
    Disjoint (nonZeroSMulDivisors A M : Set A) (J : Set A) ↔ ∃ p ∈ assStacks A M, J ≤ p := by
  classical
  have hcompl := biUnion_assStacks_eq_compl_regular (A := A) (M := M) I
  have hfin := assStacks_finite (A := A) (M := M) I
  constructor
  · intro hdis
    have hsub : (J : Set A) ⊆ ⋃ p ∈ assStacks A M, (p : Set A) := by
      intro y hy
      rw [hcompl]
      intro hyreg
      exact ((Set.disjoint_left.mp hdis) hyreg) hy
    exact (Ideal.subset_union_prime_finite hfin ⊥ ⊥ (fun p hp _ _ => hp.1)).mp hsub
  · rintro ⟨q, hq, hJq⟩
    apply Set.disjoint_left.mpr
    intro y hyreg hyJ
    have hyunion : y ∈ (⋃ p : Ideal A, ⋃ (_ : p ∈ assStacks A M), (p : Set A)) :=
      Set.mem_iUnion₂.mpr ⟨q, hq, hJq hyJ⟩
    rw [hcompl] at hyunion
    exact hyunion hyreg

/-- A maximal ideal of the localization contracts to an associated prime. -/
private lemma under_mem_assStacks_of_isMaximal_localization {T : Type*} [CommRing T] [Algebra A T]
    [IsLocalization (nonZeroSMulDivisors A M) T] (q : MaximalSpectrum T) :
    q.asIdeal.under A ∈ assStacks A M := by
  have hqdis : Disjoint (nonZeroSMulDivisors A M : Set A) (q.asIdeal.under A : Set A) :=
    (IsLocalization.disjoint_under_iff (nonZeroSMulDivisors A M) T q.asIdeal).mpr
      q.isMaximal.ne_top
  obtain ⟨p, hp, hle⟩ :=
    (localization_disjoint_iff_exists_assStacks (A := A) (M := M) I (q.asIdeal.under A)).mp hqdis
  have hpdis : Disjoint (nonZeroSMulDivisors A M : Set A) (p : Set A) :=
    (localization_disjoint_iff_exists_assStacks (A := A) (M := M) I p).mpr ⟨p, hp, le_rfl⟩
  have hpprime : p.IsPrime := hp.1
  have hpTprime :=
    IsLocalization.isPrime_of_isPrime_disjoint (nonZeroSMulDivisors A M) T p hpprime hpdis
  have hqmap : q.asIdeal ≤ Ideal.map (algebraMap A T) p := by
    rw [← IsLocalization.map_under (nonZeroSMulDivisors A M) T q.asIdeal]
    exact Ideal.map_mono hle
  have heq : q.asIdeal = Ideal.map (algebraMap A T) p :=
    q.isMaximal.eq_of_le hpTprime.ne_top hqmap
  rwa [heq, IsLocalization.under_map_of_isPrime_disjoint (nonZeroSMulDivisors A M) T hpprime hpdis]

end AssociatedPrimes

section ClosedFibre

variable {R S N T : Type*} [CommRing R] [CommRing S] [CommRing T] [IsLocalRing R] [Algebra R S]
  [AddCommGroup N] [Module S N]
  [IsNoetherianRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))]
  [Module.Finite (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))
    (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N)))]
  [Algebra S T]
  [IsLocalization
    (nonZeroSMulDivisors S
      (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N)))) T]

include R S N in
/-- Localizing at the elements regular on a finite module over the Noetherian closed fibre of a
local base produces a semilocal ring. -/
@[stacks 05DE "semilocality; the multiplicative subset is `nonZeroSMulDivisors`"]
theorem finite_maximalSpectrum_localization_nonZeroSMulDivisors : Finite (MaximalSpectrum T) := by
  classical
  let I : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R)
  let H := N ⧸ (I • (⊤ : Submodule S N))
  let : Module (S ⧸ I) H := Module.instQuotientIdealSubmoduleHSMulTop N I
  have hfin := assStacks_finite (A := S) (M := H) I
  let : Finite {p : Ideal S // p ∈ assStacks S H} := hfin.to_subtype
  apply Finite.of_injective (fun q : MaximalSpectrum T =>
    (⟨q.asIdeal.under S, under_mem_assStacks_of_isMaximal_localization (A := S) (M := H) I q⟩ :
      {p : Ideal S // p ∈ assStacks S H}))
  intro q q' h
  apply MaximalSpectrum.ext
  simpa only [IsLocalization.map_under (nonZeroSMulDivisors S H) T] using
    congrArg (Ideal.map (algebraMap S T)) (congrArg Subtype.val h)

/-- The contractions of the primes of the localization are exactly the primes of `S` contained
in an associated prime of the closed-fibre module. -/
@[stacks 05DE "the prime spectrum"]
theorem range_under_localization_nonZeroSMulDivisors :
    Set.range (fun q : PrimeSpectrum T ↦ q.asIdeal.under S) =
      {q : Ideal S | q.IsPrime ∧
        ∃ p ∈ assStacks S
          (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))), q ≤ p} := by
  classical
  let I : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R)
  let H := N ⧸ (I • (⊤ : Submodule S N))
  let : Module (S ⧸ I) H := Module.instQuotientIdealSubmoduleHSMulTop N I
  rw [range_under_localization (A := S) (M := H) (T := T)]
  ext q
  exact and_congr_right fun _ => localization_disjoint_iff_exists_assStacks (A := S) (M := H) I q

/-- Every maximal ideal of the localization corresponds to an associated prime of the
closed-fibre module over the closed-fibre ring, whose contraction to `S` is the maximal ideal's.
-/
@[stacks 05DE "the maximal ideals"]
theorem exists_assStacks_closedFibre_of_isMaximal_localization (q : MaximalSpectrum T) :
    ∃ p ∈ assStacks (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))
      (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))),
      p.comap (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R))) =
        q.asIdeal.under S := by
  let I : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R)
  let H := N ⧸ (I • (⊤ : Submodule S N))
  let : Module (S ⧸ I) H := Module.instQuotientIdealSubmoduleHSMulTop N I
  simpa only [assStacks_quotient_comap (A := S) (M := H) I, Set.mem_image] using
    (under_mem_assStacks_of_isMaximal_localization (A := S) (M := H) I q)

end ClosedFibre

/-! ### Universal injectivity of the localization map -/

section Homothety

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable [Algebra R S] [IsLocalHom (algebraMap R S)]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.FinitePresentation S N] [Module.Flat R N]

/-- An injective map with flat cokernel stays injective after tensoring with any module. -/
@[ega "0 15.1.15" "special case",
  ega "0 6.1.2" "partial",
  ega "IV 2.1.8" "(i)",
  sga "1 IV 1.1" "(i)"]
private lemma rTensor_injective_of_injective_of_flat_quotient {A M M' Q : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] [AddCommGroup Q] [Module A Q]
    (f : M →ₗ[A] M') (hf : Function.Injective f)
    (hflat : Module.Flat A (M' ⧸ LinearMap.range f)) :
    Function.Injective (f.rTensor Q) := by
  let := hflat
  have hl := LinearMap.lTensor_injective_of_exact_of_flat (LinearMap.range f).mkQ
    (Submodule.mkQ_surjective _) f hf (LinearMap.exact_map_mkQ_range f) Q
  intro a b hab
  apply (TensorProduct.comm A M Q).injective
  apply hl
  rw [LinearMap.lTensor_comm, LinearMap.lTensor_comm, hab]

/-- A homothety by an element regular on the closed fibre is injective with flat cokernel. -/
private lemma injective_and_flat_quotient_lsmul
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation)
    (s : nonZeroSMulDivisors S
      (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N)))) :
    Function.Injective (LinearMap.lsmul S N s.1) ∧
      Module.Flat R (N ⧸ LinearMap.range (LinearMap.lsmul S N s.1)) := by
  have hrange : LinearMap.range (LinearMap.lsmul S N s.1) =
      Ideal.span {s.1} • (⊤ : Submodule S N) := by
    rw [Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_def,
      ← LinearMap.range_eq_map]
    rfl
  obtain ⟨hreg, hflat⟩ :=
    Module.Flat.isSMulRegular_and_flat_quotient_smul_of_isSMulRegular_maximalIdeal hS
      (isSMulRegular_iff_mem_nonZeroSMulDivisors.mpr s.2)
  exact ⟨hreg, hrange ▸ hflat⟩

/-- Every element acting injectively on the closed fibre defines a universally injective
`R`-linear homothety of `N`. -/
@[stacks 05DF "the homotheties"]
lemma universallyInjectivePoly_lsmul_of_nonZeroSMulDivisors
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation)
    (s : nonZeroSMulDivisors S
      (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N)))) :
    UniversallyInjectivePoly (((LinearMap.lsmul S N) s.1).restrictScalars R) := by
  obtain ⟨hinj, hflat⟩ := injective_and_flat_quotient_lsmul hS s
  intro Q _ _
  exact rTensor_injective_of_injective_of_flat_quotient
    ((LinearMap.lsmul S N s.1).restrictScalars R) hinj hflat

/-- The canonical map from `N` to its localization at the elements acting injectively on the
closed fibre is universally injective over `R`. -/
@[stacks 05DF "the localization map"]
lemma universallyInjectivePoly_mkLinearMap_nonZeroSMulDivisors
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) :
    UniversallyInjectivePoly
      ((LocalizedModule.mkLinearMap
        (nonZeroSMulDivisors S
          (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) •
            (⊤ : Submodule S N)))) N).restrictScalars R) := by
  intro Q _ _
  let T := nonZeroSMulDivisors S
    (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N)))
  let g : N ⊗[R] Q →ₗ[S] LocalizedModule T N ⊗[R] Q :=
    TensorProduct.AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T N)
  have hg : IsLocalizedModule T g := by
    dsimp [g]
    infer_instance
  have hg_inj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    refine le_antisymm (fun z hz => ?_) bot_le
    obtain ⟨s, hsT, hs⟩ := (IsLocalizedModule.mem_ker_iff T).1 hz
    have hi := universallyInjectivePoly_lsmul_of_nonZeroSMulDivisors hS (⟨s, hsT⟩ : T) Q
    exact hi (hs.trans (map_zero _).symm)
  exact hg_inj

end Homothety

/-! ### Universal injectivity of a flat base change -/

section BaseChange

/-- A ring map essentially of finite presentation is essentially of finite type. -/
private lemma essFiniteType_of_essentiallyOfFinitePresentation {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (h : (algebraMap R S).EssentiallyOfFinitePresentation) :
    (algebraMap R S).EssFiniteType := by
  obtain ⟨A, ringA, algRA, algAS, tower, fp, T, loc⟩ := h
  let := ringA
  let := algRA
  let := algAS
  let := tower
  let := fp
  let := loc
  have hf : (algebraMap R A).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    infer_instance
  have hg : (algebraMap A S).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization S T
  have hc := hf.comp hg
  have heq : (@algebraMap A S _ _ algAS).comp (@algebraMap R A _ _ algRA) = algebraMap R S :=
    (@IsScalarTower.algebraMap_eq R A S _ _ _ algRA algAS (algebraMap R S).toAlgebra tower).symm
  rw [← heq]
  exact hc

/-- The closed fibre of a ring map essentially of finite presentation over a local ring is
Noetherian. -/
private lemma closedFibre_isNoetherianRing {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [Algebra R S] (h : (algebraMap R S).EssentiallyOfFinitePresentation) :
    IsNoetherianRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) := by
  let : Algebra.EssFiniteType R S := by
    rw [← RingHom.essFiniteType_algebraMap]
    exact essFiniteType_of_essentiallyOfFinitePresentation h
  let : IsNoetherianRing (R ⧸ maximalIdeal R) :=
    isNoetherianRing_of_ringEquiv (ResidueField R) (RingEquiv.refl _)
  exact Algebra.EssFiniteType.isNoetherianRing (R ⧸ maximalIdeal R)
    (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))

/-- The contraction of an associated prime over the closed-fibre ring is an associated prime over
`S`. -/
private lemma isAssociatedPrimeStacks_comap_quotient {S N : Type*} [CommRing S] [AddCommGroup N]
    [Module S N] (I : Ideal S) (p : Ideal (S ⧸ I))
    (hp : IsAssociatedPrimeStacks (S ⧸ I) (N ⧸ I • (⊤ : Submodule S N)) p) :
    IsAssociatedPrimeStacks S (N ⧸ I • (⊤ : Submodule S N))
      (Ideal.comap (Ideal.Quotient.mk I) p) := by
  have hp' : p ∈ Stacks.AssociatedPrimes.assPrimes (S ⧸ I) (N ⧸ I • (⊤ : Submodule S N)) := by
    rw [← assStacks_eq_assPrimes]
    exact hp
  have h := (Stacks.AssociatedPrimes.mem_assPrimes_quotient_iff_comap_mem_assPrimes I p).mp hp'
  rwa [← assStacks_eq_assPrimes] at h

/-- A prime of the closed fibre contracts to the maximal ideal of the local base. -/
private lemma comap_closedFibre_prime_eq_maximalIdeal {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [Algebra R S] (p : Ideal (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)))
    (hp : p.IsPrime) :
    Ideal.comap (algebraMap R S) (Ideal.comap
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R))) p) = maximalIdeal R := by
  refine le_antisymm (IsLocalRing.le_maximalIdeal
    (((hp.comap (Ideal.Quotient.mk _)).comap (algebraMap R S)).ne_top)) fun r hr =>
    (Ideal.mk_ker.symm.trans_le (Ideal.ker_le_comap _)) (Ideal.mem_map_of_mem _ hr)

/-- Over a faithfully flat ring extension `L → Lp` the unit map `M → M ⊗[L] Lp` of an `L`-module
is universally injective over any base `R` below `L`. -/
private lemma universallyInjectivePoly_tensorUnit_of_faithfullyFlat {R L Lp M : Type*}
    [CommRing R] [CommRing L] [CommRing Lp] [Algebra R L] [Algebra L Lp]
    [AddCommGroup M] [Module L M] [Module R M] [IsScalarTower R L M]
    [Module.FaithfullyFlat L Lp] :
    UniversallyInjectivePoly (((TensorProduct.mk L M Lp).flip 1).restrictScalars R) := by
  intro Q _ _
  let e := TensorProduct.AlgebraTensorModule.rightComm R L L M Lp Q
  have hi : Function.Injective ((TensorProduct.mk L (M ⊗[R] Q) Lp).flip 1) := by
    intro a b hab
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := L) (B := Lp) (M ⊗[R] Q)
    simpa using congrArg (TensorProduct.comm L (M ⊗[R] Q) Lp) hab
  have he (z : M ⊗[R] Q) :
      e (((((TensorProduct.mk L M Lp).flip) 1).restrictScalars R).rTensor Q z) =
        ((TensorProduct.mk L (M ⊗[R] Q) Lp).flip 1) z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m q => simp [e, TensorProduct.AlgebraTensorModule.rightComm_tmul]
    | add a b ha hb => simp [map_add, ha, hb]
  intro a b hab
  apply hi
  rw [← he a, ← he b, hab]

/-- Let `R → S` be a local homomorphism of local rings, essentially of finite presentation, let
`N` be a finitely presented `S`-module which is flat over `R`, and let `S → S'` be flat. If the
image of `Spec(S') → Spec(S)` contains every prime of `S` lying over the maximal ideal of `R`
which is an associated prime of the closed fibre `N / 𝔪_R N`, then the canonical map
`N → N ⊗[S] S'` is universally injective over `R`. -/
@[stacks 05DG]
theorem universallyInjectivePoly_tensorUnit_of_flat {R : Type u} {S : Type v} {S' : Type w}
    {N : Type x} [CommRing R] [CommRing S] [CommRing S'] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Algebra S S']
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N] [Module.Flat R N] [Module.Flat S S']
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation)
    (hspec : ∀ q : Ideal S, Ideal.comap (algebraMap R S) q = maximalIdeal R →
      IsAssociatedPrimeStacks S
        (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))) q →
      ∃ q' : Ideal S', q'.IsPrime ∧ Ideal.comap (algebraMap S S') q' = q) :
    UniversallyInjectivePoly (((TensorProduct.mk S N S').flip 1).restrictScalars R) := by
  classical
  let : IsNoetherianRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
    closedFibre_isNoetherianRing hS
  let : Module.Finite (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))
      (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))) :=
    inferInstance
  set Sigma : Submonoid S := nonZeroSMulDivisors S
    (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))) with hSigma
  set L := Localization Sigma with hL
  set Lp := Localization (Algebra.algebraMapSubmonoid S' Sigma) with hLp
  let : Module.Flat L Lp := inferInstance
  have hpure : UniversallyInjectivePoly
      ((LocalizedModule.mkLinearMap Sigma N).restrictScalars R) :=
    universallyInjectivePoly_mkLinearMap_nonZeroSMulDivisors hS
  have hmaxLp (q : MaximalSpectrum L) : ∃ Q : PrimeSpectrum Lp, Q.asIdeal.under L = q.asIdeal := by
    obtain ⟨p, hp, hpq⟩ :=
      exists_assStacks_closedFibre_of_isMaximal_localization (R := R) (S := S) (N := N)
        (T := L) q
    obtain ⟨q', hq', hq'eq⟩ := hspec _ (comap_closedFibre_prime_eq_maximalIdeal p hp.1)
      (isAssociatedPrimeStacks_comap_quotient
        (Ideal.map (algebraMap R S) (maximalIdeal R)) p hp)
    have hq'eq := hq'eq.trans hpq
    have hdq : Disjoint (Sigma : Set S) (q.asIdeal.under S : Set S) :=
      (IsLocalization.disjoint_under_iff Sigma L q.asIdeal).mpr q.isMaximal.ne_top
    have hdq' : Disjoint (Algebra.algebraMapSubmonoid S' Sigma : Set S') (q' : Set S') := by
      rw [Set.disjoint_left]
      intro z hz hzq
      change z ∈ Submonoid.map (algebraMap S S') Sigma at hz
      obtain ⟨s, hs, rfl⟩ := hz
      exact (Set.disjoint_left.mp hdq) hs (hq'eq ▸ hzq)
    let Q' : Ideal Lp := Ideal.map (algebraMap S' Lp) q'
    have hQ' : Q'.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint
        (Algebra.algebraMapSubmonoid S' Sigma) Lp q' hq' hdq'
    refine ⟨⟨Q', hQ'⟩, ?_⟩
    apply (IsLocalization.orderEmbedding Sigma L).injective
    show (Ideal.comap (algebraMap L Lp) Q').under S = q.asIdeal.under S
    calc
      (Ideal.comap (algebraMap L Lp) Q').under S = Q'.under S := by
        show Ideal.comap (algebraMap S L) (Ideal.comap (algebraMap L Lp) Q') =
          Ideal.comap (algebraMap S Lp) Q'
        rw [Ideal.comap_comap, IsScalarTower.algebraMap_eq S L Lp]
      _ = Ideal.comap (algebraMap S S') q' := by
        show Ideal.comap (algebraMap S Lp) Q' = Ideal.comap (algebraMap S S') q'
        rw [IsScalarTower.algebraMap_eq S S' Lp, ← Ideal.comap_comap]
        dsimp [Q']
        show Ideal.comap (algebraMap S S') ((Ideal.map (algebraMap S' Lp) q').under S') =
          Ideal.comap (algebraMap S S') q'
        rw [IsLocalization.under_map_of_isPrime_disjoint
          (Algebra.algebraMapSubmonoid S' Sigma) Lp hq' hdq']
      _ = q.asIdeal.under S := hq'eq
  have hff : (algebraMap L Lp).FaithfullyFlat := by
    apply ((faithfullyFlat_tfae00HQ (algebraMap L Lp)
      (RingHom.flat_algebraMap_iff.mpr inferInstance)).out 3 1).mp
    intro z hz
    obtain ⟨Q, hQ⟩ :=
      hmaxLp ⟨z.asIdeal, (PrimeSpectrum.isClosed_singleton_iff_isMaximal z).mp hz⟩
    exact ⟨Q, PrimeSpectrum.ext hQ⟩
  let : Module.FaithfullyFlat L Lp := RingHom.faithfullyFlat_algebraMap_iff.mp hff
  let eS : (LocalizedModule Sigma N ⊗[L] Lp) ≃ₗ[S] (N ⊗[S] Lp) :=
    ((TensorProduct.comm L (LocalizedModule Sigma N) Lp).restrictScalars S).trans
      (((TensorProduct.congr (LinearEquiv.refl L Lp)
        ((LocalizedModule.isBaseChange Sigma N).equiv.symm)).restrictScalars S).trans
      (((TensorProduct.AlgebraTensorModule.cancelBaseChange S L Lp Lp N).restrictScalars S).trans
        (TensorProduct.comm S Lp N)))
  let e := eS.restrictScalars R
  have he (n : N) :
      e ((LocalizedModule.mk n (1 : Sigma)) ⊗ₜ[L] (1 : Lp)) = n ⊗ₜ[S] (1 : Lp) := by
    have hm : (LocalizedModule.isBaseChange Sigma N).equiv.symm
        (LocalizedModule.mk n (1 : Sigma)) = (1 : L) ⊗ₜ[S] n := by
      simpa only [LocalizedModule.mkLinearMap_apply] using
        (LocalizedModule.isBaseChange Sigma N).equiv_symm_apply n
    simp [e, eS, hm]
  let fLoc : N →ₗ[R] LocalizedModule Sigma N :=
    (LocalizedModule.mkLinearMap Sigma N).restrictScalars R
  let gLoc : LocalizedModule Sigma N →ₗ[R] (LocalizedModule Sigma N ⊗[L] Lp) :=
    ((TensorProduct.mk L (LocalizedModule Sigma N) Lp).flip 1).restrictScalars R
  let fLp : N →ₗ[R] (N ⊗[S] Lp) := ((TensorProduct.mk S N Lp).flip 1).restrictScalars R
  have hgLoc : UniversallyInjectivePoly gLoc :=
    universallyInjectivePoly_tensorUnit_of_faithfullyFlat (R := R) (L := L) (Lp := Lp)
      (M := LocalizedModule Sigma N)
  have hcEq : e.toLinearMap ∘ₗ (gLoc ∘ₗ fLoc) = fLp := by
    ext n
    exact he n
  intro Q _ _
  have hflp : Function.Injective (fLp.rTensor Q) := by
    rw [← hcEq, LinearMap.rTensor_comp, LinearMap.rTensor_comp]
    exact ((e.rTensor Q).injective).comp ((hgLoc Q).comp (hpure Q))
  refine Function.Injective.of_rTensor_comp
    (f := ((TensorProduct.mk S N S').flip 1).restrictScalars R)
    (g := (TensorProduct.map (LinearMap.id : N →ₗ[S] N)
      ((Algebra.linearMap S' Lp).restrictScalars S)).restrictScalars R) ?_
  have hfg : (TensorProduct.map (LinearMap.id : N →ₗ[S] N)
      ((Algebra.linearMap S' Lp).restrictScalars S)).restrictScalars R ∘ₗ
      (((TensorProduct.mk S N S').flip 1).restrictScalars R) = fLp := by
    ext n
    simp [fLp]
  rwa [hfg]

end BaseChange

end Stacks.UniversalInjectivity

end
