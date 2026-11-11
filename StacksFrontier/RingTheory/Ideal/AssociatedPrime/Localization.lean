module

public import StacksCore.Tactic.StacksAttribute
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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs

@[expose] public section

/-!
# Associated primes are unchanged by localization at nonzerodivisors

Let `R` be a commutative ring, `M` an `R`-module, and `S ⊆ R` a multiplicative subset
every element of which is a nonzerodivisor on `M`, meaning that multiplication by
`s ∈ S` is injective on `M`. Then the associated primes of `M` and of the localization
`S⁻¹M`, both taken with respect to the `R`-module structure, coincide:

`Ass_R(M) = Ass_R(S⁻¹M)`.

This is Stacks tag 05C0 (Lemma 10.63.17).

## Main definitions

* `AssLocalization.AllNonZeroDivisorsOn S M`: every `s ∈ S` acts injectively on `M`,
  that is `IsSMulRegular M s`.

The set of associated primes itself is `Stacks.AssociatedPrimes.assPrimes R M`, imported
from `StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs`: the prime ideals `p` of `R` with
`Ann_R(m) = p` for some `m : M`, where `Ann_R(m) = {r ∈ R | r • m = 0}` is
`Ideal.torsionOf R M m`. This is the *exact-annihilator* notion of an associated prime
used by the Stacks project (Definition 10.63.1, tag 00LA): the annihilator equals `p` on
the nose.

The localization `S⁻¹M` is `LocalizedModule S M` with its canonical `Module R`
structure obtained by restricting scalars along `R → S⁻¹R`; the canonical `R`-linear
map `ι : M → S⁻¹M`, `m ↦ m / 1`, is `LocalizedModule.mkLinearMap S M`.

## Main results

* `AssLocalization.smul_mk_eq_zero_iff` and `AssLocalization.annihilator_mk_eq`: under
  the nonzerodivisor hypothesis, `r` annihilates `m / s` in `S⁻¹M` exactly when it
  annihilates `m`, so `Ann_R(m / s) = Ann_R(m)`. Every element of `S⁻¹M` has this form,
  which is what forces the two sets of associated primes to agree.
* `AssLocalization.assPrimes_localizedModule_eq`: the equality `Ass_R(M) = Ass_R(S⁻¹M)`.

## Implementation notes

`assPrimes` is deliberately not Mathlib's `associatedPrimes` / `IsAssociatedPrime`.
Mathlib's `Submodule.IsAssociatedPrime N I` is the radical-based condition
`I.IsPrime ∧ ∃ x, I = (N.colon {x}).radical`, which is in general weaker than
`I = Ann_R(x)`, so the two notions are not interchangeable here.

Both sides of the equality are sets of primes of the *base ring* `R`; on the right,
`S⁻¹M` is regarded as an `R`-module. For the zero module the exact-annihilator
definition gives `assPrimes R 0 = ∅`, since `Ann_R(0) = R` is not prime.
-/


namespace AssLocalization

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Every element of the multiplicative subset `S` is a nonzerodivisor on `M`, that is,
acts injectively by scalar multiplication. -/
def AllNonZeroDivisorsOn (S : Submonoid R) (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  ∀ s ∈ S, IsSMulRegular M s

/-- Core lemma: for `m : M` and `s : S`, scalar `r` annihilates `mk m s`
in the localization iff it annihilates `m`. -/
theorem smul_mk_eq_zero_iff (S : Submonoid R) (hS : AllNonZeroDivisorsOn S M)
    (m : M) (s : S) (r : R) :
    r • LocalizedModule.mk m s = (0 : LocalizedModule S M) ↔ r • m = 0 := by
  rw [LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
  refine ⟨fun ⟨u, hu⟩ ↦ hS s s.2 (hS u u.2 ?_), fun h ↦ ⟨1, by simp [h]⟩⟩
  simpa only [Submonoid.smul_def, smul_zero] using hu

/-- The annihilator of `mk m s` equals the annihilator of `m`. -/
theorem annihilator_mk_eq (S : Submonoid R) (hS : AllNonZeroDivisorsOn S M)
    (m : M) (s : S) :
    Submodule.annihilator (Submodule.span R {LocalizedModule.mk m s})
      = Submodule.annihilator (Submodule.span R {m}) := by
  ext r
  simpa only [Submodule.mem_annihilator_span_singleton] using smul_mk_eq_zero_iff S hS m s r

/-- The same statement as `annihilator_mk_eq`, written with `Ideal.torsionOf`, which is the
spelling of the annihilator used by `Stacks.AssociatedPrimes.assPrimes`. -/
theorem torsionOf_mk_eq (S : Submonoid R) (hS : AllNonZeroDivisorsOn S M) (m : M) (s : S) :
    Ideal.torsionOf R (LocalizedModule S M) (LocalizedModule.mk m s)
      = Ideal.torsionOf R M m := by
  ext r
  exact smul_mk_eq_zero_iff S hS m s r

/-- **Stacks Tag 05C0 / Lemma 10.63.17.**
If every element of the multiplicative subset `S` is a nonzerodivisor on the
`R`-module `M`, then the (exact-annihilator) associated primes of `M` and of its
localization `S⁻¹M = LocalizedModule S M` (both as `R`-modules) coincide. -/
@[stacks 05C0]
theorem assPrimes_localizedModule_eq (S : Submonoid R) (hS : AllNonZeroDivisorsOn S M) :
    Stacks.AssociatedPrimes.assPrimes R M
      = Stacks.AssociatedPrimes.assPrimes R (LocalizedModule S M) := by
  ext p
  constructor
  · rintro ⟨hp, m, hm⟩
    exact ⟨hp, LocalizedModule.mk m 1, (torsionOf_mk_eq S hS m 1).trans hm⟩
  · rintro ⟨hp, x, hx⟩
    induction x using LocalizedModule.induction_on with
    | _ m s => exact ⟨hp, m, (torsionOf_mk_eq S hS m s).symm.trans hx⟩

end AssLocalization

-- ===== merged from StacksDraft.Ch10.Sec65.Tag05C1 =====

/-!
# Associated primes are unchanged by base change to the fraction field

Let `R → S` be a homomorphism of commutative rings, let `N` be an `S`-module, and
assume `N` is flat as an `R`-module. Let `K` be the total ring of fractions of `R`.
Stacks 05C1 (Lemma 10.65.4) says
`Ass_S(N) = Ass_S(N ⊗_R K) = Ass_{S ⊗_R K}(N ⊗_R K)` via the canonical inclusion
`Spec(S ⊗_R K) ⊆ Spec(S)`, with `Ass` the exact-annihilator notion of Stacks 00LA
(`Stacks.AssociatedPrimes.assPrimes`). This is `assPrimes_chain`, which also states that
contraction along `algebraMap S (S ⊗_R K)` is injective on ideals and carries
`Ass_{S ⊗_R K}(N ⊗_R K)` onto `Ass_S(N ⊗_R K)`.

The file also records the analogous statements for Mathlib's radical-based
`associatedPrimes`, which differ from the Stacks notion outside the Noetherian case.
Writing `Ass` for that set, two things hold:

1. `Ass_S(N) = Ass_S(N ⊗_R K)` as subsets of `Ideal S`;
2. the comap `Ideal.comap (algebraMap S (S ⊗_R K))` along the canonical inclusion
   `Spec(S ⊗_R K) ⊆ Spec(S)` satisfies
   `(Ideal.comap (algebraMap S (S ⊗_R K)))⁻¹' (Ass_S(N ⊗_R K)) = Ass_{S ⊗_R K}(N ⊗_R K)`.

Together these give `Ass_S(N) = Ass_S(N ⊗_R K) = Ass_{S ⊗_R K}(N ⊗_R K)`.

## Formalization design

Tensoring with `K = (R⁰)⁻¹ R` is exactly localization at `R⁰ = nonZeroDivisors R`. Concretely:

* `S ⊗_R K` is the localization `T⁻¹ S` of `S` at
  `T = Algebra.algebraMapSubmonoid S (nonZeroDivisors R)`, the image of `R⁰`
  under `algebraMap R S`;
* `N ⊗_R K` is the localization `(R⁰)⁻¹ N` of the `R`-module `N`, the canonical
  `R`-linear map `μ_N : N → N ⊗_R K`, `n ↦ n ⊗ₜ 1`, being a localized-module map.
  Viewed as an `S`-module, `N ⊗_R K` is the localization of `N` at `T`, via the
  `S`-linear version of the same map.

There are accordingly two layers of statements.

In the **abstract layer**, `S ⊗_R K` is modelled by a ring `SK` carrying the explicit
named hypothesis `IsLocalization T SK`, and `N ⊗_R K` by an `S`- and `SK`-module `NK`
carrying the explicit named hypotheses `IsLocalizedModule (nonZeroDivisors R) μN`, the
`R`-module localization, and `IsLocalizedModule T μNₛ`, the `S`-module localization.
These localization data are explicit hypotheses of every theorem, so the statements
genuinely range over localizations and base changes rather than over arbitrary rings
and modules; this is faithful because localizations are unique up to unique
isomorphism.

In the **concrete layer**, for the parts where the relevant instances are available,
the corollaries are additionally stated in terms of the actual tensor products
`N ⊗[R] K` and `S ⊗[R] K`: the `S`-module structure on `N ⊗[R] K` by left base change
is an instance, so `associatedPrimes S N = associatedPrimes S (N ⊗[R] K)` is stated
verbatim, and likewise the `S`-algebra structure on `S ⊗[R] K` is an instance, so
injectivity of `PrimeSpectrum.comap (algebraMap S (S ⊗[R] K))` is stated verbatim. The
`(S ⊗_R K)`-module structure on `N ⊗_R K` is deliberately not a global instance, to
avoid diamonds among the right-factor structures on `A ⊗[R] B`, so the comparison of
`Ass_S` with `Ass_{S ⊗_R K}` is given only in the abstract layer, with the localization
hypotheses named explicitly.

No Noetherian hypothesis is needed, matching the Stacks statement.
-/

@[expose] public section

open scoped TensorProduct nonZeroDivisors

namespace Stacks.AssociatedPrimes.Localization

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {K : Type*} [CommRing K] [Algebra R K] [IsFractionRing R K]
-- `N` : an `S`-module that is flat over `R`.
variable {N : Type*} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
-- `SK` : the ring `S ⊗_R K`, modelled as the localization `T⁻¹ S` of `S` at
-- `T = Algebra.algebraMapSubmonoid S (nonZeroDivisors R) = (algebraMap R S) '' (R \ {0})`.
variable {SK : Type*} [CommRing SK] [Algebra S SK]
-- `NK` : the module `N ⊗_R K`, viewed as an `S`-module and as an `SK`-module, with the two
-- actions compatible (scalar tower `S → SK → NK`).
variable {NK : Type*} [AddCommGroup NK] [Module S NK] [Module R NK] [IsScalarTower R S NK]
variable [Module SK NK] [IsScalarTower S SK NK]

/-! ## The abstract layer

In each theorem the localization data are named explicit hypotheses:
* `hSK : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) SK`
  pins `SK` down as `S ⊗_R K`;
* `hμN : IsLocalizedModule (nonZeroDivisors R) μN` pins `NK` down as the
  localization of the `R`-module `N`, that is, as `N ⊗_R K`;
* `hμNₛ : IsLocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) μNₛ`
  pins `NK` down as the localization of the `S`-module `N` along `algebraMap S SK`;
* `hμ : ∀ n, μNₛ n = μN n` says the `R`- and `S`-linear localization maps agree.
-/

/-- The canonical localization map `μN : N → N ⊗_R K` of an `R`-flat module `N` is
injective. -/
theorem baseChange_map_injective [Module.Flat R N] (μN : N →ₗ[R] NK)
    (hμN : IsLocalizedModule (nonZeroDivisors R) μN) : Function.Injective μN := by
  refine (IsLocalizedModule.injective_iff_isRegular (S := nonZeroDivisors R) (f := μN)).mpr ?_
  intro c
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors c.property

omit [IsScalarTower R S N] [IsScalarTower R S NK] in
/-- Part 1 of the Mathlib-`associatedPrimes` analogue of Stacks 05C1 (abstract).  If `N` is
flat over `R`, then `associatedPrimes S N = associatedPrimes S (N ⊗_R K)` as subsets of
`Ideal S`; for the Stacks notion see `assPrimes_eq_of_baseChange`. -/
theorem associatedPrimes_eq_of_baseChange [Module.Flat R N] (μN : N →ₗ[R] NK) (μNₛ : N →ₗ[S] NK)
    (hμN : IsLocalizedModule (nonZeroDivisors R) μN)
    (hμNₛ : IsLocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) μNₛ)
    (hμ : ∀ n, μNₛ n = μN n) :
    associatedPrimes S N = associatedPrimes S NK := by
  -- `μNₛ` is injective: it equals `μN` pointwise, and `μN` is injective by flatness.
  have hμN_inj : Function.Injective μN := baseChange_map_injective μN hμN
  have hμNₛ_inj : Function.Injective μNₛ := fun a b hab => hμN_inj (by rwa [← hμ, ← hμ])
  -- Forward inclusion `Ass_S(N) ⊆ Ass_S(NK)` from injectivity of `μNₛ` (Stacks 02M3).
  refine (associatedPrimes.subset_of_injective hμNₛ_inj).antisymm ?_
  -- Reverse inclusion `Ass_S(NK) ⊆ Ass_S(N)`: `T` acts invertibly on `NK`.
  rintro I ⟨hIprime, x, hIx⟩
  -- write x = μNₛ n / t
  obtain ⟨⟨n, t⟩, ht⟩ := IsLocalizedModule.surj (Algebra.algebraMapSubmonoid S (nonZeroDivisors
      R)) μNₛ x
  simp only [Submonoid.smul_def] at ht
  -- ht : (t : S) • x = μNₛ n
  refine ⟨hIprime, n, ?_⟩
  -- `t` acts invertibly on `NK`, so `t • y = 0 ↔ y = 0`.
  have htinj : ∀ y : NK, (t : S) • y = 0 ↔ y = 0 := fun y => by
    simpa [Module.algebraMap_end_apply] using
      ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units μNₛ t)).injective.eq_iff
        (a := y) (b := 0)
  have hcolon : (⊥ : Submodule S NK).colon {x} = (⊥ : Submodule S N).colon {n} := by
    ext r
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
    rw [← htinj (r • x), smul_comm (t : S) r x, ht, ← map_smul, ← map_zero μNₛ]
    exact hμNₛ_inj.eq_iff
  rw [hIx, hcolon]

omit [Module R N] [IsScalarTower R S N] [Module R NK] [IsScalarTower R S NK] in
/-- Part 2 of the Mathlib-`associatedPrimes` analogue of Stacks 05C1 (abstract).  Transport
along the canonical inclusion
`Spec(S ⊗_R K) ⊆ Spec(S)` identifies the associated primes of `N ⊗_R K` over `S` with those
over `S ⊗_R K`: the preimage under `Ideal.comap (algebraMap S SK)` of `Ass_S(N ⊗_R K)` equals
`Ass_{S ⊗_R K}(N ⊗_R K)`. -/
theorem preimage_comap_associatedPrimes_eq
    (hSK : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) SK) :
    (Ideal.comap (algebraMap S SK)) ⁻¹' (associatedPrimes S NK)
      = associatedPrimes SK NK := by
  -- `NK` is its own localization at `T := algebraMapSubmonoid S (nonZeroDivisors R)`, via the
  -- identity map (the `SK`-module structure makes `T` act invertibly on `NK`).
  have hid : IsLocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))
      (LinearMap.id : NK →ₗ[S] NK) :=
    isLocalizedModule_id (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) NK SK
  ext p
  refine ⟨fun hp =>
    Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) LinearMap.id p hp, fun hp => ?_⟩
  -- `p` associated over `SK` ⇒ its comap is associated over `S` (identity case, no FG).
  rw [Set.mem_preimage]
  rw [AssociatedPrimes.mem_iff, IsAssociatedPrime, Submodule.isAssociatedPrime_def] at hp ⊢
  obtain ⟨hpprime, x, hx⟩ := hp
  refine ⟨Ideal.IsPrime.comap (algebraMap S SK) (hK := hpprime), x, ?_⟩
  ext r
  simp only [Ideal.mem_comap, hx, Ideal.mem_radical_iff, Submodule.mem_colon_singleton,
    Submodule.mem_bot]
  exact exists_congr fun n => by rw [← map_pow, algebraMap_smul]

/-- The canonical map `PrimeSpectrum.comap (algebraMap S SK) : Spec(S ⊗_R K) → Spec(S)` is
injective. -/
theorem comap_injective
    (hSK : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) SK) :
    Function.Injective (PrimeSpectrum.comap (algebraMap S SK)) :=
  (PrimeSpectrum.localization_comap_isEmbedding SK
    (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))).injective

omit [IsScalarTower R S N] [IsScalarTower R S NK] in
/-- An analogue of Stacks 05C1 for Mathlib's radical-based `associatedPrimes` (not the
Stacks notion of associated prime, which is `assPrimes_chain` below).  Under flatness, via the
canonical map `Spec(S ⊗_R K) → Spec(S)`, we have
`Ass_S(N) = Ass_S(N ⊗_R K)` and the preimage identity along
`Ideal.comap (algebraMap S (S ⊗_R K))` relating `Ass_S(N ⊗_R K)` and
`Ass_{S ⊗_R K}(N ⊗_R K)`.  All localization data are explicit hypotheses. -/
theorem associatedPrimes_chain [Module.Flat R N] (μN : N →ₗ[R] NK) (μNₛ : N →ₗ[S] NK)
    (hSK : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) SK)
    (hμN : IsLocalizedModule (nonZeroDivisors R) μN)
    (hμNₛ : IsLocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) μNₛ)
    (hμ : ∀ n, μNₛ n = μN n) :
    associatedPrimes S N = associatedPrimes S NK ∧
      (Ideal.comap (algebraMap S SK)) ⁻¹' (associatedPrimes S NK)
        = associatedPrimes SK NK :=
  ⟨associatedPrimes_eq_of_baseChange μN μNₛ hμN hμNₛ hμ, preimage_comap_associatedPrimes_eq hSK⟩

/-! ## The Stacks notion of associated prime

The statements above use Mathlib's radical-based `associatedPrimes`. Stacks 05C1 is about the
exact-annihilator notion `Stacks.AssociatedPrimes.assPrimes` (Stacks 00LA): `p = Ann(m)` on the
nose. Without a Noetherian hypothesis the two notions differ, so we redo the argument for
`assPrimes`. The identification of `Ass_S(N ⊗_R K)` with `Ass_{S ⊗_R K}(N ⊗_R K)` "via the
canonical inclusion `Spec(S ⊗_R K) ⊆ Spec(S)`" is stated as: contraction along
`algebraMap S (S ⊗_R K)` is injective on ideals, and carries `Ass_{S ⊗_R K}(N ⊗_R K)` onto
`Ass_S(N ⊗_R K)`.
-/

omit [Module R NK] [IsScalarTower R S NK] in
/-- If `SK` is the localization of `S` at `T`, every `t ∈ T` acts injectively on the
`SK`-module `NK`. -/
theorem smul_eq_zero_iff_of_isLocalization
    (hSK : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) SK)
    (t : Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) (y : NK) :
    (t : S) • y = 0 ↔ y = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, smul_zero]⟩
  obtain ⟨u, hu⟩ := IsLocalization.map_units SK t
  rw [← algebraMap_smul SK (t : S) y, ← hu] at h
  simpa using congrArg (fun z => (↑u⁻¹ : SK) • z) h

omit [IsScalarTower R S N] [IsScalarTower R S NK] in
/-- **Stacks 05C1, first equality.**  If `N` is flat over `R`, then
`Ass_S(N) = Ass_S(N ⊗_R K)`, with `Ass` the exact-annihilator notion of Stacks 00LA. -/
theorem assPrimes_eq_of_baseChange [Module.Flat R N] (μN : N →ₗ[R] NK) (μNₛ : N →ₗ[S] NK)
    (hSK : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) SK)
    (hμN : IsLocalizedModule (nonZeroDivisors R) μN)
    (hμNₛ : IsLocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) μNₛ)
    (hμ : ∀ n, μNₛ n = μN n) :
    assPrimes S N = assPrimes S NK := by
  have hμNₛ_inj : Function.Injective μNₛ := fun a b hab =>
    baseChange_map_injective μN hμN (by rwa [← hμ, ← hμ])
  -- `Ann_S(t • μNₛ n / t) = Ann_S(n)`: every element of `NK` has the form `μNₛ n / t`.
  have key : ∀ (x : NK) (n : N) (t : Algebra.algebraMapSubmonoid S (nonZeroDivisors R)),
      (t : S) • x = μNₛ n → Ideal.torsionOf S NK x = Ideal.torsionOf S N n := by
    intro x n t ht
    ext r
    rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff,
      ← smul_eq_zero_iff_of_isLocalization hSK t (r • x), smul_comm (t : S) r x, ht,
      ← map_smul, ← map_zero μNₛ]
    exact hμNₛ_inj.eq_iff
  ext p
  refine ⟨fun ⟨hp, n, hn⟩ => ⟨hp, μNₛ n, (key _ n 1 (one_smul S _)).trans hn⟩, ?_⟩
  rintro ⟨hp, x, hx⟩
  obtain ⟨⟨n, t⟩, ht⟩ := IsLocalizedModule.surj
    (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) μNₛ x
  exact ⟨hp, n, (key x n t ht).symm.trans hx⟩

/-- Contraction of ideals along `algebraMap S SK` is injective when `SK` is a localization
of `S`. -/
theorem ideal_comap_injective
    (hSK : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) SK) :
    Function.Injective (Ideal.comap (algebraMap S SK)) := fun I J h => by
  have e : ∀ L : Ideal SK, Ideal.map (algebraMap S SK) (Ideal.comap (algebraMap S SK) L) = L :=
    IsLocalization.map_under (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) SK
  rw [← e I, h, e J]

omit [Module R NK] [IsScalarTower R S NK] in
/-- **Stacks 05C1, second equality.**  Contraction along `algebraMap S SK`, that is the
canonical inclusion `Spec(S ⊗_R K) ⊆ Spec(S)`, carries `Ass_{S ⊗_R K}(N ⊗_R K)` onto
`Ass_S(N ⊗_R K)`, with `Ass` the exact-annihilator notion of Stacks 00LA. -/
theorem image_comap_assPrimes_eq
    (hSK : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) SK) :
    Ideal.comap (algebraMap S SK) '' assPrimes SK NK = assPrimes S NK := by
  set T := Algebra.algebraMapSubmonoid S (nonZeroDivisors R)
  -- `Ann_S(x)` is the contraction of `Ann_{SK}(x)`.
  have hcomap : ∀ x : NK,
      (Ideal.torsionOf SK NK x).comap (algebraMap S SK) = Ideal.torsionOf S NK x := by
    intro x
    ext r
    rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff, algebraMap_smul]
  ext q
  constructor
  · rintro ⟨p, ⟨hp, x, rfl⟩, rfl⟩
    exact ⟨Ideal.IsPrime.comap (algebraMap S SK) (hK := hp), x, (hcomap x).symm⟩
  · rintro ⟨hq, x, rfl⟩
    -- `Ann_S(x)` misses `T`, since `T` acts injectively and `x ≠ 0`.
    have hdisj : Disjoint (T : Set S) (Ideal.torsionOf S NK x : Set S) := by
      rw [Set.disjoint_left]
      intro t ht htx
      have hx0 : x = 0 :=
        (smul_eq_zero_iff_of_isLocalization hSK ⟨t, ht⟩ x).mp ((Ideal.mem_torsionOf_iff x t).mp htx)
      exact hq.ne_top (by rw [hx0, Ideal.torsionOf_zero])
    have hprime : (Ideal.torsionOf SK NK x).IsPrime := by
      have e : Ideal.map (algebraMap S SK) ((Ideal.torsionOf SK NK x).comap (algebraMap S SK))
          = Ideal.torsionOf SK NK x := IsLocalization.map_under T SK _
      rw [← e, hcomap]
      exact IsLocalization.isPrime_of_isPrime_disjoint T SK _ hq hdisj
    exact ⟨_, ⟨hprime, x, rfl⟩, hcomap x⟩

omit [IsScalarTower R S N] [IsScalarTower R S NK] in
/-- **Stacks 05C1 / Lemma 10.65.4.**  Let `R → S` be a ring map, `N` an `S`-module that is flat
over `R`, and `K` the fraction field of `R` (more generally, its total ring of fractions).
Then `Ass_S(N) = Ass_S(N ⊗_R K) = Ass_{S ⊗_R K}(N ⊗_R K)` via the canonical inclusion
`Spec(S ⊗_R K) ⊆ Spec(S)`: the first equality holds as sets of ideals of `S`, and contraction
along `algebraMap S (S ⊗_R K)` is injective on ideals and maps `Ass_{S ⊗_R K}(N ⊗_R K)` onto
`Ass_S(N ⊗_R K)`.  Here `Ass` is the exact-annihilator notion `assPrimes` of Stacks 00LA,
`S ⊗_R K` is modelled as the localization `SK` of `S` at the image of `R⁰`, and `N ⊗_R K` as
the localization `NK` of `N` at `R⁰` (over `R`) and at the image of `R⁰` (over `S`), the two
localization maps agreeing. -/
@[stacks 05C1 "Exact-annihilator Ass (00LA); S ⊗_R K and N ⊗_R K modelled by their \
localization universal properties; R generalized from a domain to any ring with K its total \
ring of fractions."]
theorem assPrimes_chain [Module.Flat R N] (μN : N →ₗ[R] NK) (μNₛ : N →ₗ[S] NK)
    (hSK : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) SK)
    (hμN : IsLocalizedModule (nonZeroDivisors R) μN)
    (hμNₛ : IsLocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) μNₛ)
    (hμ : ∀ n, μNₛ n = μN n) :
    assPrimes S N = assPrimes S NK ∧
      Function.Injective (Ideal.comap (algebraMap S SK)) ∧
      Ideal.comap (algebraMap S SK) '' assPrimes SK NK = assPrimes S NK :=
  ⟨assPrimes_eq_of_baseChange μN μNₛ hSK hμN hμNₛ hμ, ideal_comap_injective hSK,
    image_comap_assPrimes_eq hSK⟩

/-! ## The concrete tensor-product corollaries

These restate the results above directly for the actual tensor products `N ⊗[R] K`
and `S ⊗[R] K`, using the instances that are available globally: `N ⊗[R] K` carries
its canonical `S`-module structure by left base change, and `S ⊗[R] K` its canonical
`S`-algebra structure, together with
`IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) (S ⊗[R] K)`.
-/

/-- Part 1 of the Mathlib-`associatedPrimes` analogue of Stacks 05C1 (concrete).  The equality
of associated-prime sets, in Mathlib's radical-based sense, stated for the actual tensor product
`N ⊗[R] K` with its canonical `S`-module structure. -/
theorem associatedPrimes_eq_baseChange_tensor [Module.Flat R N] :
    associatedPrimes S N = associatedPrimes S (N ⊗[R] K) := by
  -- The S-linear localization map `μNₛ : N → N ⊗[R] K`, `n ↦ n ⊗ₜ 1`.
  let μNₛ : N →ₗ[S] N ⊗[R] K :=
    { toFun := fun n => n ⊗ₜ[R] (1 : K)
      map_add' := fun a b => by rw [TensorProduct.add_tmul]
      map_smul' := fun s n => by
        simp only [RingHom.id_apply]; rw [TensorProduct.smul_tmul'] }
  -- The `R`-side localization: `μNₛ.restrictScalars R = (n ↦ n ⊗ₜ 1)` is a localized module.
  -- The Mathlib instance `IsLocalization.tensorProduct_isLocalizedModule` is for the map
  -- `TensorProduct.mk R K N 1 : N → K ⊗[R] N` (`n ↦ 1 ⊗ₜ n`); transport it across
  -- `TensorProduct.comm` to our right-handed map.
  have hμN : IsLocalizedModule (nonZeroDivisors R) (μNₛ.restrictScalars R) := by
    have h : IsLocalizedModule (nonZeroDivisors R)
        (↑(TensorProduct.comm R K N) ∘ₗ (TensorProduct.mk R K N 1) : N →ₗ[R] N ⊗[R] K) :=
      IsLocalizedModule.of_linearEquiv (nonZeroDivisors R) (TensorProduct.mk R K N 1)
        (TensorProduct.comm R K N)
    have he : (↑(TensorProduct.comm R K N) ∘ₗ (TensorProduct.mk R K N 1) : N →ₗ[R] N ⊗[R] K)
        = μNₛ.restrictScalars R := by
      ext n; simp [μNₛ]
    rwa [he] at h
  -- The `S`-side localization, at `T = algebraMapSubmonoid S (nonZeroDivisors R)`, follows from
  -- the `R`-side one via `IsLocalizedModule.of_restrictScalars`.
  have hμNₛ : IsLocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) μNₛ :=
    IsLocalizedModule.of_restrictScalars (nonZeroDivisors R) μNₛ
  -- Instantiate the abstract part 1; the two maps agree pointwise (`rfl`).
  exact associatedPrimes_eq_of_baseChange (μNₛ.restrictScalars R) μNₛ hμN hμNₛ (fun _ => rfl)

/-- The canonical map `Spec(S ⊗[R] K) → Spec(S)` is injective, stated for the actual ring
`S ⊗[R] K`. -/
theorem comap_injective_tensor :
    Function.Injective (PrimeSpectrum.comap (algebraMap S (S ⊗[R] K))) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) (S ⊗[R] K) :=
    IsLocalization.tensor K (nonZeroDivisors R)
  exact comap_injective (SK := S ⊗[R] K) ‹_›

end Stacks.AssociatedPrimes.Localization
