module

public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.PID
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationDimensionBounds
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.EssentiallyFiniteType
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.FieldExtensionBaseChange
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessCriterion
import all StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationDepthCollapse

/-!
# Stacks 0EFI is false for a negative `d`

Stacks 0EFI says: for ideals `I, J` of a Noetherian ring `A`, a finite module `M` and integers
`s` and `d`, hypotheses (1)–(4) of the source give an ideal `J₀ ⊆ J` with
`V(J₀) ∩ V(I) = V(J) ∩ V(I)` such that every further `J' ⊆ J₀` with the same intersection has
`RΓ_{J'}(M) → RΓ_{J₀}(M)` an isomorphism in degrees `≤ s`, and such that a power of `J₀ I`
annihilates those modules. The source places no condition on `d`, and the assertion is false as
it stands: its proof of the annihilation clause reads hypothesis (4), a lower bound on
`depth + dim` by `d + s`, as the lower bound by `s` that Faltings' annihilator theorem needs, and
that step requires `0 ≤ d`.

This file exhibits the counterexample, so that `0 ≤ d` is part of the corrected statement rather
than a restriction this development chose.

## The example

`A` is the localization of `ℚ[x]` at the complement of `(x) ∪ (x - 1)`, a semilocal Dedekind
domain whose spectrum is the three primes `0 ⊂ 𝔪₁ = (x)` and `0 ⊂ 𝔪₂ = (x - 1)`; the part of
that used below is `Stacks.Algebraization.eq_bot_of_notMem_of_notMem`, that a prime containing
neither `x` nor `x - 1` is zero. Take `M = A`, `I = (x(x-1))`, `J = 𝔪₁`,
`s = 1` and `d = -1`. Then `V(I) = {𝔪₁, 𝔪₂}` and `V(J) ∩ V(I) = {𝔪₁}`, so
`T = {𝔭 : V(𝔭) ∩ V(I) ⊆ V(J) ∩ V(I)}` is `{𝔪₁}`, contained in `V(I)`.

* (1) holds: `A` is essentially of finite type over `ℚ`, so Stacks 0A7K gives it a dualizing
  complex.
* (2) is vacuous.
* (3) holds because no prime outside `V(I)` lies in `T`: such a prime is the generic point, and
  `𝔪₂` lies in `V(I)` above it but not in `V(J)`.
* (4) holds because a prime outside `V(I)` is strictly smaller than every prime of `V(I)`, so
  the relative dimension along any specialization in `V(J) ∩ V(I)` is at least `1`, while
  `d + s = 0`.

The conclusion fails. By Faltings' annihilator theorem — an equivalence — the conclusion forces
`depth(M_𝔭) + dim((A/𝔭)_𝔮) > s` for every `𝔭 ∉ T ∪ V(I)` and every `𝔮 ∈ V(J)` above it
(`Stacks.Algebraization.depth_add_dim_gt_of_isStabilizingData`), and at `𝔭 = 0`, `𝔮 = 𝔪₁` that
inequality reads `0 + 1 > 1`. Concretely every admissible `J₀` is a power of `𝔪₁`, so
`H¹_{J₀}(A) = A[1/x]/A`, whose annihilator is zero while `J₀ I ≠ 0`.

A local ring cannot do this: there `T ⊆ V(I)` forces `I` to be nilpotent and the conclusion
degenerates, which is why the companion maximal-ideal statements of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdealExistence` need no
`0 ≤ d`.

## Main results

* `Stacks.Algebraization.exists_stabilizationHypotheses_semilocalLine` — hypotheses (1)–(4) of
  Stacks 0EFI hold for this data, with `s = 1` and `d = -1`.
* `Stacks.Algebraization.not_exists_isStabilizingData_semilocalLine` — the conclusion of Stacks
  0EFI fails for it.
* `Stacks.Algebraization.not_forall_exists_isStabilizingData_of_neg` — hence the `d < 0` case of
  Stacks 0EFI is false, and the hypothesis `0 ≤ d` of
  `Stacks.Algebraization.exists_isStabilizingData` cannot be dropped.
* `Stacks.Algebraization.not_forall_exists_isStabilizingData` — hence Stacks 0EFI is false as
  literally stated, its source placing no condition on `d`.
* `Stacks.Algebraization.forall_exists_isStabilizingData_of_nonneg` — the same statement with
  `0 ≤ d` restored, which holds: the two differ in that hypothesis and in nothing else.

No declaration here carries `@[stacks 0EFI]`: none of them states that tag.

## Implementation notes

The refutation goes through the equivalence of Faltings' annihilator theorem rather than through
a computation of `H¹_{J₀}(A)`: the library already derives the depth-dimension inequality from
the conclusion of Stacks 0EFI, for every `d`, and refuting an inequality between a depth and a
Krull dimension needs no local cohomology. The two obstructions are the same one.

The relative dimension is only bounded above by `1`, which is all that refuting `> 1` asks for.

`import all` reaches two private arithmetic lemmas of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationDepthCollapse`: the extended-integer
form of the depth-dimension bound and the positivity of a relative dimension at a strict
specialization. This is the pattern that
`StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence` itself uses.

## References

* [Stacks Project, Tag 0EFI](https://stacks.math.columbia.edu/tag/0EFI)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
* [Stacks Project, Tag 0A7K](https://stacks.math.columbia.edu/tag/0A7K)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Polynomial

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Algebraization

/-! ### The semilocal line -/

/-- The prime ideal `(x)` of `ℚ[x]`. -/
def lineAtZero : Ideal ℚ[X] := Ideal.span {X}

/-- The prime ideal `(x - 1)` of `ℚ[x]`. -/
def lineAtOne : Ideal ℚ[X] := Ideal.span {X - 1}

/-- `x - 1` is a prime element of `ℚ[x]`. -/
theorem prime_X_sub_one : Prime (X - 1 : ℚ[X]) := by
  simpa using Polynomial.prime_X_sub_C (1 : ℚ)

/-- The ideal `(x)` of `ℚ[x]` is prime. -/
instance : lineAtZero.IsPrime :=
  (Ideal.span_singleton_prime Polynomial.prime_X.ne_zero).2 Polynomial.prime_X

/-- The ideal `(x - 1)` of `ℚ[x]` is prime. -/
instance : lineAtOne.IsPrime :=
  (Ideal.span_singleton_prime prime_X_sub_one.ne_zero).2 prime_X_sub_one

/-- The ideal `(x)` of `ℚ[x]` is maximal. -/
instance : lineAtZero.IsMaximal := Polynomial.prime_X.isMaximal_span_singleton

/-- The ideal `(x - 1)` of `ℚ[x]` is maximal. -/
instance : lineAtOne.IsMaximal := prime_X_sub_one.isMaximal_span_singleton

/-- The multiplicative set of polynomials lying in neither `(x)` nor `(x - 1)`, i.e. vanishing
at neither `0` nor `1`. -/
def lineMonoid : Submonoid ℚ[X] := lineAtZero.primeCompl ⊓ lineAtOne.primeCompl

/-- A polynomial lies in `lineMonoid` exactly when it lies in neither `(x)` nor `(x - 1)`. -/
theorem mem_lineMonoid_iff {f : ℚ[X]} :
    f ∈ lineMonoid ↔ f ∉ lineAtZero ∧ f ∉ lineAtOne := Iff.rfl

/-- `lineMonoid` consists of nonzerodivisors. -/
theorem lineMonoid_le_nonZeroDivisors : lineMonoid ≤ nonZeroDivisors ℚ[X] :=
  le_trans inf_le_left lineAtZero.primeCompl_le_nonZeroDivisors

/-- The semilocal Dedekind domain `A` of the counterexample: the localization of `ℚ[x]` at the
complement of `(x) ∪ (x - 1)`. -/
abbrev SemilocalLine : Type := Localization lineMonoid

/-- The semilocal line `A` is an integral domain. -/
instance : IsDomain SemilocalLine :=
  IsLocalization.isDomain_localization lineMonoid_le_nonZeroDivisors

/-- The semilocal line `A` is a Noetherian ring. -/
instance : IsNoetherianRing SemilocalLine :=
  IsLocalization.isNoetherianRing lineMonoid _ inferInstance

/-- `A` is a localization of the finite type `ℚ`-algebra `ℚ[x]`, hence essentially of finite
type over `ℚ`. -/
theorem isEssentiallyOfFiniteType_semilocalLine :
    IsEssentiallyOfFiniteType ℚ SemilocalLine (algebraMap ℚ SemilocalLine) :=
  ⟨ℚ[X], inferInstance, inferInstance, inferInstance, lineMonoid, inferInstance,
    @IsScalarTower.of_algebraMap_eq ℚ ℚ[X] SemilocalLine _ _ _ _ _
      ((algebraMap ℚ SemilocalLine).toAlgebra) (fun _ => rfl),
    inferInstance⟩

/-- **Hypothesis (1) of Stacks 0EFI for `A`:** the semilocal line has a dualizing complex.

It is essentially of finite type over `ℚ`, and a field is its own dualizing complex, so Stacks
0A7K applies. -/
theorem exists_isDualizingComplex_semilocalLine :
    ∃ omega : DerivedCategory (ModuleCat.{0} SemilocalLine),
      Dualizing.IsDualizingComplex omega := by
  obtain ⟨_, omega, homega⟩ := Dualizing.exists_isDualizingComplex_of_isEssentiallyOfFiniteType
    isEssentiallyOfFiniteType_semilocalLine _ (Dualizing.isDualizingComplex_single_self_field ℚ)
  exact ⟨omega, homega⟩

/-! ### The spectrum of the semilocal line -/

/-- The maximal ideal `𝔪₁ = (x)` of `A`. -/
def semilocalOrigin : Ideal SemilocalLine := lineAtZero.map (algebraMap ℚ[X] SemilocalLine)

/-- `𝔪₁` is the image of `(x)` under the localization map. -/
theorem semilocalOrigin_eq :
    semilocalOrigin = lineAtZero.map (algebraMap ℚ[X] SemilocalLine) := rfl

/-- The maximal ideal `𝔪₂ = (x - 1)` of `A`. -/
def semilocalOne : Ideal SemilocalLine := lineAtOne.map (algebraMap ℚ[X] SemilocalLine)

/-- The ideal `I = (x(x-1))` of `A`. -/
def semilocalDouble : Ideal SemilocalLine :=
  Ideal.span {algebraMap ℚ[X] SemilocalLine (X * (X - 1))}

/-- The multiplicative set misses `(x)`. -/
theorem disjoint_lineMonoid_lineAtZero :
    Disjoint (lineMonoid : Set ℚ[X]) (lineAtZero : Set ℚ[X]) :=
  Set.disjoint_left.mpr fun _ ha hb => (mem_lineMonoid_iff.mp ha).1 hb

/-- The multiplicative set misses `(x - 1)`. -/
theorem disjoint_lineMonoid_lineAtOne :
    Disjoint (lineMonoid : Set ℚ[X]) (lineAtOne : Set ℚ[X]) :=
  Set.disjoint_left.mpr fun _ ha hb => (mem_lineMonoid_iff.mp ha).2 hb

/-- The ideal `𝔪₁ = (x)` of `A` is prime. -/
instance : semilocalOrigin.IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint lineMonoid _ _ inferInstance
    disjoint_lineMonoid_lineAtZero

/-- The ideal `𝔪₂ = (x - 1)` of `A` is prime. -/
instance : semilocalOne.IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint lineMonoid _ _ inferInstance
    disjoint_lineMonoid_lineAtOne

/-- `x` lies in `𝔪₁`. -/
theorem algebraMap_X_mem_semilocalOrigin :
    algebraMap ℚ[X] SemilocalLine X ∈ semilocalOrigin :=
  Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self X)

/-- `x - 1` lies in `𝔪₂`. -/
theorem algebraMap_X_sub_one_mem_semilocalOne :
    algebraMap ℚ[X] SemilocalLine (X - 1) ∈ semilocalOne :=
  Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)

/-- `x` does not lie in `(x - 1)`. -/
theorem X_notMem_lineAtOne : (X : ℚ[X]) ∉ lineAtOne := by
  intro h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h
  simpa using congrArg (Polynomial.eval 1) hc

/-- `x` does not lie in `𝔪₂`: the second maximal ideal is not in the zero locus of `J = (x)`. -/
theorem algebraMap_X_notMem_semilocalOne :
    algebraMap ℚ[X] SemilocalLine X ∉ semilocalOne := by
  intro h
  refine X_notMem_lineAtOne ?_
  rwa [← IsLocalization.under_map_of_isPrime_disjoint lineMonoid SemilocalLine
    (inferInstanceAs lineAtOne.IsPrime) disjoint_lineMonoid_lineAtOne]

/-- `I = (x(x-1))` is contained in `𝔪₂`. -/
theorem semilocalDouble_le_semilocalOne : semilocalDouble ≤ semilocalOne := by
  rw [semilocalDouble, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, map_mul]
  exact Ideal.mul_mem_left _ _ algebraMap_X_sub_one_mem_semilocalOne

/-- `I = (x(x-1))` is not the zero ideal: `A` is a domain and `x(x-1) ≠ 0`. -/
theorem semilocalDouble_ne_bot : semilocalDouble ≠ ⊥ := by
  rw [semilocalDouble, Ne, Ideal.span_singleton_eq_bot,
    map_eq_zero_iff _ (IsLocalization.injective SemilocalLine lineMonoid_le_nonZeroDivisors)]
  exact mul_ne_zero Polynomial.prime_X.ne_zero prime_X_sub_one.ne_zero

/-- **The generic point is the only prime of `A` off `V(I)`:** a prime of `A` containing neither
`x` nor `x - 1` is the zero ideal.

Its contraction `q` to `ℚ[x]` is a prime disjoint from the multiplicative set, hence contained in
`(x) ∪ (x - 1)`, hence — the two being ideals — contained in one of them; a nonzero prime of the
principal ideal domain `ℚ[x]` is maximal, so `q` would have to be that one, which it is not. -/
theorem eq_bot_of_notMem_of_notMem (p : Ideal SemilocalLine) (hp : p.IsPrime)
    (h0 : algebraMap ℚ[X] SemilocalLine X ∉ p)
    (h1 : algebraMap ℚ[X] SemilocalLine (X - 1) ∉ p) : p = ⊥ := by
  obtain ⟨hq, hdisj⟩ :=
    (IsLocalization.isPrime_iff_isPrime_disjoint lineMonoid SemilocalLine p).mp hp
  have hsub : ((p.under ℚ[X] : Ideal ℚ[X]) : Set ℚ[X]) ⊆
      (lineAtZero : Set ℚ[X]) ∪ (lineAtOne : Set ℚ[X]) := by
    intro f hf
    by_contra hnot
    exact Set.disjoint_right.mp hdisj hf
      (mem_lineMonoid_iff.mpr ⟨fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩)
  have hbot : p.under ℚ[X] = ⊥ := by
    rcases Ideal.subset_union.mp hsub with hle | hle
    · by_contra hne
      have heq : p.under ℚ[X] = lineAtZero :=
        (hq.isMaximal_of_ne_bot hne).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
      exact h0 (heq ▸ Ideal.mem_span_singleton_self X : X ∈ p.under ℚ[X])
    · by_contra hne
      have heq : p.under ℚ[X] = lineAtOne :=
        (hq.isMaximal_of_ne_bot hne).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
      exact h1 (heq ▸ Ideal.mem_span_singleton_self (X - 1 : ℚ[X]) :
        (X - 1 : ℚ[X]) ∈ p.under ℚ[X])
  rw [← IsLocalization.map_under lineMonoid SemilocalLine p, hbot, Ideal.map_bot]

/-- `V(I)` is the set of primes containing `x` or containing `x - 1`, i.e. `{𝔪₁, 𝔪₂}`. -/
theorem mem_zeroLocus_semilocalDouble_iff (p : PrimeSpectrum SemilocalLine) :
    p ∈ PrimeSpectrum.zeroLocus (semilocalDouble : Set SemilocalLine) ↔
      algebraMap ℚ[X] SemilocalLine X ∈ p.asIdeal ∨
        algebraMap ℚ[X] SemilocalLine (X - 1) ∈ p.asIdeal := by
  rw [PrimeSpectrum.mem_zeroLocus]
  constructor
  · intro h
    have hc : algebraMap ℚ[X] SemilocalLine (X * (X - 1)) ∈ p.asIdeal :=
      h (Ideal.mem_span_singleton_self _)
    rw [map_mul] at hc
    exact p.isPrime.mem_or_mem hc
  · intro h
    rw [SetLike.coe_subset_coe, semilocalDouble, Ideal.span_singleton_le_iff_mem, map_mul]
    rcases h with h | h
    · exact Ideal.mul_mem_right _ _ h
    · exact Ideal.mul_mem_left _ _ h

/-! ### The generic point lies outside `T ∪ V(I)` -/

/-- **Hypothesis (3) of Stacks 0EFI at `d = -1`, for `A`:** no prime outside `V(I)` lies in `T`.

A prime outside `V(I)` contains neither `x` nor `x - 1`, hence is the generic point; and `𝔪₂`
lies in `V(I)` above the generic point but not in `V(J)`, so the generic point is not in `T`. -/
theorem notMem_associatedSubset_of_notMem_zeroLocus (p : PrimeSpectrum SemilocalLine)
    (hp : p ∉ PrimeSpectrum.zeroLocus (semilocalDouble : Set SemilocalLine)) :
    p ∉ associatedSubset semilocalDouble semilocalOrigin := by
  intro hT
  rw [mem_zeroLocus_semilocalDouble_iff, not_or] at hp
  have hbot : p.asIdeal = ⊥ := eq_bot_of_notMem_of_notMem p.asIdeal p.isPrime hp.1 hp.2
  have honeV : (⟨semilocalOne, inferInstance⟩ : PrimeSpectrum SemilocalLine) ∈
      PrimeSpectrum.zeroLocus (p.asIdeal : Set SemilocalLine) ∩
        PrimeSpectrum.zeroLocus (semilocalDouble : Set SemilocalLine) := by
    refine ⟨?_, (mem_zeroLocus_semilocalDouble_iff _).mpr
      (Or.inr algebraMap_X_sub_one_mem_semilocalOne)⟩
    rw [PrimeSpectrum.mem_zeroLocus, hbot]
    exact fun _ hx => (Ideal.mem_bot.mp hx) ▸ Submodule.zero_mem _
  exact algebraMap_X_notMem_semilocalOne
    ((hT honeV).1 algebraMap_X_mem_semilocalOrigin)

/-- The generic point of `A` lies neither in `T` nor in `V(I)`. -/
theorem genericPoint_notMem_associatedSubset_union :
    (⟨⊥, inferInstance⟩ : PrimeSpectrum SemilocalLine) ∉
      associatedSubset semilocalDouble semilocalOrigin ∪
        PrimeSpectrum.zeroLocus (semilocalDouble : Set SemilocalLine) := by
  have hp : (⟨⊥, inferInstance⟩ : PrimeSpectrum SemilocalLine) ∉
      PrimeSpectrum.zeroLocus (semilocalDouble : Set SemilocalLine) := by
    rw [PrimeSpectrum.mem_zeroLocus]
    intro h
    exact semilocalDouble_ne_bot (le_bot_iff.mp (SetLike.coe_subset_coe.mp h))
  rintro (h | h)
  · exact notMem_associatedSubset_of_notMem_zeroLocus _ hp h
  · exact hp h

/-! ### Depth and relative dimension at the pair `(0, 𝔪₁)` -/

/-- Over a domain the local ring at the generic point is a field: its maximal ideal is zero. -/
theorem maximalIdeal_localizationAtBot (R : Type*) [CommRing R] [IsDomain R] :
    maximalIdeal (Localization.AtPrime (⊥ : Ideal R)) = ⊥ := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (⊥ : Ideal R)
    (Localization.AtPrime (⊥ : Ideal R)), Ideal.map_bot]

/-- **`depth(A_0) = 0`:** at the generic point of a domain the ring has depth zero, the maximal
ideal of the local ring there being zero while the local ring itself is not. -/
theorem depth_localizationAtBot_eq_zero (R : Type*) [CommRing R] [IsDomain R] :
    Module.depth (Localization.AtPrime (⊥ : Ideal R))
        (maximalIdeal (Localization.AtPrime (⊥ : Ideal R)))
        (LocalizedModule (⊥ : Ideal R).primeCompl R) = 0 := by
  have hnt : Nontrivial (LocalizedModule (⊥ : Ideal R).primeCompl R) := by
    refine ⟨⟨LocalizedModule.mk 1 1, 0, fun heq => ?_⟩⟩
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (⊥ : Ideal R).primeCompl
      (LocalizedModule.mkLinearMap (⊥ : Ideal R).primeCompl R)).mp heq
    exact one_ne_zero ((smul_eq_zero.mp ht).resolve_left fun ht0 => t.2 (Ideal.mem_bot.mpr ht0))
  rw [maximalIdeal_localizationAtBot]
  exact Module.depth_bot_eq_zero _

/-- **`dim((A/0)_{𝔪₁}) ≤ 1`:** `A_{𝔪₁}` is the localization of the principal ideal domain `ℚ[x]`
at the height-one maximal ideal `(x)`, and the relative dimension at the generic point is the
dimension of that local ring. -/
theorem ringKrullDim_localizationAtOrigin_quotient_bot_le_one :
    ringKrullDim ((Localization.AtPrime semilocalOrigin) ⧸
        (⊥ : Ideal SemilocalLine).map
          (algebraMap SemilocalLine (Localization.AtPrime semilocalOrigin))) ≤ 1 := by
  rw [Ideal.map_bot]
  refine le_trans (ringKrullDim_quotient_le ⊥) ?_
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height semilocalOrigin
    (Localization.AtPrime semilocalOrigin), semilocalOrigin_eq,
    IsLocalization.height_map_of_disjoint lineMonoid lineAtZero disjoint_lineMonoid_lineAtZero,
    IsPrincipalIdealRing.height_eq_one_of_isMaximal lineAtZero (Polynomial.not_isField ℚ)]
  simp

/-! ### The counterexample -/

/-- The image of `1 : WithBot ℕ∞` in the extended integers. -/
theorem krullDimToEInt_one : krullDimToEInt (1 : WithBot ℕ∞) = ((1 : ℤ) : EInt) := by
  simpa using krullDimToEInt_natCast 1

/-- **The depth–dimension inequality of Faltings' annihilator theorem fails for `A`** at the
prime `𝔭 = 0` outside `T ∪ V(I)` and the prime `𝔮 = 𝔪₁` of `V(J)` above it: there it reads
`depth(A_0) + dim((A/0)_{𝔪₁}) = 0 + 1 > 1 = s`, which is false. -/
theorem not_depth_add_dim_gt_semilocalLine :
    ¬ enatToEInt (Module.depth (Localization.AtPrime (⊥ : Ideal SemilocalLine))
          (maximalIdeal (Localization.AtPrime (⊥ : Ideal SemilocalLine)))
          (LocalizedModule (⊥ : Ideal SemilocalLine).primeCompl SemilocalLine)) +
        krullDimToEInt (ringKrullDim ((Localization.AtPrime semilocalOrigin) ⧸
          (⊥ : Ideal SemilocalLine).map
            (algebraMap SemilocalLine (Localization.AtPrime semilocalOrigin)))) >
      ((1 : ℤ) : EInt) := by
  rw [depth_localizationAtBot_eq_zero SemilocalLine,
    show enatToEInt (0 : ℕ∞) = ((0 : ℤ) : EInt) from rfl]
  refine not_lt.mpr ?_
  rw [show ((0 : ℤ) : EInt) = 0 from rfl, zero_add]
  exact le_trans (krullDimToEInt_mono ringKrullDim_localizationAtOrigin_quotient_bot_le_one)
    (le_of_eq krullDimToEInt_one)

/-- **The conclusion of Stacks 0EFI fails for `A`.** No pair `(J₀, n)` has the stabilization
property of Stacks 0EFI for the module `M = A`, the ideals `I = (x(x-1))` and `J = 𝔪₁`, and
`s = 1`.

Were there one, Faltings' annihilator theorem — an equivalence — would return the inequality
`depth(A_𝔭) + dim((A/𝔭)_𝔮) > s` at every `𝔭 ∉ T ∪ V(I)` and every `𝔮 ∈ V(J)` above it, and at
`𝔭 = 0`, `𝔮 = 𝔪₁` that inequality is false. -/
theorem not_exists_isStabilizingData_semilocalLine :
    ¬ ∃ p : Ideal SemilocalLine × ℕ,
      IsStabilizingData (M := SemilocalLine) semilocalDouble semilocalOrigin 1 p := by
  intro h
  obtain ⟨omega, homega⟩ := exists_isDualizingComplex_semilocalLine
  exact not_depth_add_dim_gt_semilocalLine <|
    depth_add_dim_gt_of_isStabilizingData semilocalDouble semilocalOrigin 1 zero_le_one
      omega homega h ⟨⊥, inferInstance⟩ ⟨semilocalOrigin, inferInstance⟩
      genericPoint_notMem_associatedSubset_union
      ((PrimeSpectrum.mem_zeroLocus _ _).mpr subset_rfl) bot_le

/-- **Hypotheses (1)–(4) of Stacks 0EFI hold for `A`** with `M = A`, `I = (x(x-1))`, `J = 𝔪₁`,
`s = 1` and `d = -1`.

(1) is `Stacks.Algebraization.exists_isDualizingComplex_semilocalLine`. (2) is vacuous. (3) holds
because no prime outside `V(I)` lies in `T`. (4) holds because a prime `𝔭 ∉ V(I)` is strictly
smaller than every prime of `V(I)`, so the relative dimension there is at least one, while
`d + s = 0`. -/
theorem exists_stabilizationHypotheses_semilocalLine :
    ∃ omega : DerivedCategory (ModuleCat.{0} SemilocalLine),
      StabilizationHypotheses (M := SemilocalLine) semilocalDouble semilocalOrigin 1 (-1)
        omega := by
  obtain ⟨omega, homega⟩ := exists_isDualizingComplex_semilocalLine
  refine ⟨omega, homega, fun p hp hT =>
    absurd hT (notMem_associatedSubset_of_notMem_zeroLocus p hp), fun p hp _ => Or.inr ?_⟩
  intro q hq
  have hlt : p.asIdeal < q.asIdeal := by
    refine lt_of_le_of_ne ((PrimeSpectrum.mem_zeroLocus _ _).mp hq.1.1) fun heq => ?_
    exact hp (PrimeSpectrum.ext heq ▸ hq.2)
  refine lt_enatToEInt_add_krullDimToEInt (Or.inr ⟨?_, ?_⟩)
  · rw [show ((-1 + 1 : ℤ) : EInt) = ((0 : ℤ) : EInt) by norm_num,
      ← show enatToEInt (0 : ℕ∞) = ((0 : ℤ) : EInt) from rfl]
    exact enatToEInt_mono (by simp)
  · exact one_le_ringKrullDim_localization_quotient p q hlt

/-- **The `d < 0` case of Stacks 0EFI is false as literally stated.**

There are a Noetherian ring `A`, a finite module `M`, ideals `I` and `J` and integers `s` and
`d < 0` satisfying hypotheses (1)–(4) of Stacks 0EFI for which no pair `(J₀, n)` has the
stabilization property. The witness is `A` the localization of `ℚ[x]` at the complement of
`(x) ∪ (x - 1)`, `M = A`, `I = (x(x-1))`, `J = (x)`, `s = 1` and `d = -1`; see
`Stacks.Algebraization.exists_stabilizationHypotheses_semilocalLine` for the hypotheses and
`Stacks.Algebraization.not_exists_isStabilizingData_semilocalLine` for the failure.

This is why the hypothesis `0 ≤ d` of `Stacks.Algebraization.exists_isStabilizingData` cannot be
dropped: with it removed, that statement is this one. -/
theorem not_forall_exists_isStabilizingData_of_neg :
    ¬ ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (M : Type) [AddCommGroup M] [Module A M]
        [Module.Finite A M] (I J : Ideal A) (s d : ℤ), d < 0 →
        ∀ omega : DerivedCategory (ModuleCat.{0} A),
          StabilizationHypotheses (M := M) I J s d omega →
            ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I J s p := by
  intro h
  obtain ⟨omega, homega⟩ := exists_stabilizationHypotheses_semilocalLine
  exact not_exists_isStabilizingData_semilocalLine (h SemilocalLine SemilocalLine
    semilocalDouble semilocalOrigin 1 (-1) (by norm_num) omega homega)

/-- Restoring `0 ≤ d` makes the statement that
`Stacks.Algebraization.not_forall_exists_isStabilizingData_of_neg` refutes true: it becomes the
universe-`0` instance of `Stacks.Algebraization.exists_isStabilizingData`.

This is recorded so that the contrast is exact — the two displayed statements differ in the
hypothesis on `d` and in nothing else. It carries no `@[stacks 0EFI]` attribute because
`Stacks.Algebraization.exists_isStabilizingData`, of which it is an instance, already does. -/
theorem forall_exists_isStabilizingData_of_nonneg :
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (M : Type) [AddCommGroup M] [Module A M]
        [Module.Finite A M] (I J : Ideal A) (s d : ℤ), 0 ≤ d →
        ∀ omega : DerivedCategory (ModuleCat.{0} A),
          StabilizationHypotheses (M := M) I J s d omega →
            ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I J s p :=
  fun _ _ _ _ _ _ _ I J s d hd omega H => exists_isStabilizingData I J s d hd omega H

/-- **Stacks 0EFI is false as literally stated**, its source placing no condition on the integer
`d`: hypotheses (1)–(4) do not imply the existence of a stabilizing pair.

The failure is confined to `d < 0`, where hypothesis (3) is an exclusion rather than a bound; see
`Stacks.Algebraization.not_forall_exists_isStabilizingData_of_neg` for the located form, and
`Stacks.Algebraization.exists_isStabilizingData` for the corrected statement. -/
theorem not_forall_exists_isStabilizingData :
    ¬ ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (M : Type) [AddCommGroup M] [Module A M]
        [Module.Finite A M] (I J : Ideal A) (s d : ℤ)
        (omega : DerivedCategory (ModuleCat.{0} A)),
          StabilizationHypotheses (M := M) I J s d omega →
            ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I J s p := by
  intro h
  refine not_forall_exists_isStabilizingData_of_neg ?_
  intro A _ _ M _ _ _ I J s d _ omega H
  exact h A M I J s d omega H

end Stacks.Algebraization

end
