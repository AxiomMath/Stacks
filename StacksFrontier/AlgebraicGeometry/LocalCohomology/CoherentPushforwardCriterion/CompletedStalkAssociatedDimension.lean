module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.CompletedLocalBaseChange

/-!
# Non-coherence of `j_* 𝒪_U` from an associated prime of dimension at most one

Let `X` be an integral locally Noetherian scheme, let `U` be a nonempty open subscheme and let
`z` be a point outside `U`. If the completion `𝒪^∧_{X, z}` has an associated prime `𝔭` with
`dim(𝒪^∧_{X, z} ⧸ 𝔭) ≤ 1`, then `j_* 𝒪_U` is not coherent; this is the second paragraph of
[Stacks, Tag 0AWC], where `dim(𝒪^∧_{X, z} ⧸ 𝔭) = 1` is assumed. The case
`dim(𝒪^∧_{X, z} ⧸ 𝔭) = 0`, in which `𝔭` is the maximal ideal of `𝒪^∧_{X, z}`, does not occur:
the maximal ideal of `𝒪^∧_{X, z}` contains a nonzerodivisor.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.CoherentPushforwardCriterion`.

* `not_isAssociatedPrimeStacks_of_flat_of_mem`: over a flat extension of a domain, no ideal
  containing the image of a nonzero element is associated to the extension.
* `one_le_ringKrullDim_quotient_of_ne_maximalIdeal`: in a local ring, a prime other than the
  maximal ideal has a quotient of dimension at least one.
* `maximalIdeal_stalk_ne_bot_of_notMem`: the local ring of an integral scheme at a point outside
  a nonempty open has nonzero maximal ideal.
* `not_isAssociatedPrimeStacks_maximalIdeal_completedStalk`: the maximal ideal of
  `𝒪^∧_{X, z}` is not associated to `𝒪^∧_{X, z}`.
* `not_isCoherent_pushforward_structureSheaf_of_isAssociatedPrime_completedStalk_le_one`: the
  second paragraph of [Stacks, Tag 0AWC] with the dimension hypothesis weakened to `≤ 1`.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 0BK3](https://stacks.math.columbia.edu/tag/0BK3)
* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA)
-/


@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry IsLocalRing
open Stacks.LocalCohomology (puncturedSpectrum)

universe u

namespace Stacks.AlgebraicGeometry.CoherentPushforwardCriterion

open CodimensionOneObstruction

/-! ### A nonzerodivisor rules out an associated prime -/

/-- **A flat extension of a domain has no associated prime containing the image of a nonzero
element.** If `f : R → Λ` is flat, `R` is a domain and `a ≠ 0` in `R`, then no ideal of `Λ`
containing `f a` is the annihilator of an element of `Λ`. -/
theorem not_isAssociatedPrimeStacks_of_flat_of_mem {R Λ : Type*} [CommRing R] [CommRing Λ]
    [IsDomain R] {f : R →+* Λ} (hf : f.Flat) {a : R} (ha : a ≠ 0) {p : Ideal Λ} (hap : f a ∈ p) :
    ¬ IsAssociatedPrimeStacks Λ Λ p := by
  rintro ⟨hp, m, hm⟩
  algebraize [f]
  have hreg : IsSMulRegular Λ (f a) := by
    have h := IsSMulRegular.of_flat (S := Λ) (IsSMulRegular.of_ne_zero ha)
    rwa [f.algebraMap_toAlgebra] at h
  have hm0 : f a • m = 0 := by
    rw [← hm] at hap
    simpa [Submodule.mem_colon_span_singleton] using hap
  have hz : m = 0 := hreg (by simpa using hm0)
  rw [hz] at hm
  refine hp.ne_top ?_
  rw [← hm, eq_top_iff]
  intro r _
  simp

/-! ### A prime other than the maximal ideal has positive-dimensional quotient -/

/-- **In a local ring a prime other than the maximal ideal has a quotient of dimension at least
one.** -/
theorem one_le_ringKrullDim_quotient_of_ne_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    (p : Ideal R) [hp : p.IsPrime] (h : p ≠ maximalIdeal R) : 1 ≤ ringKrullDim (R ⧸ p) := by
  rw [ringKrullDim_quotient, Order.one_le_krullDim_iff]
  refine ⟨⟨⟨p, hp⟩, by simp⟩,
    ⟨⟨maximalIdeal R, inferInstance⟩, by simpa using le_maximalIdeal hp.ne_top⟩,
    lt_of_le_of_ne (le_maximalIdeal hp.ne_top) ?_⟩
  simp only [ne_eq, Subtype.mk.injEq, PrimeSpectrum.mk.injEq]
  exact h

/-! ### The local ring at a point outside a nonempty open -/

/-- **The local ring of an integral scheme at a point outside a nonempty open has nonzero maximal
ideal.** -/
theorem maximalIdeal_stalk_ne_bot_of_notMem {X : Scheme.{u}} [IsIntegral X] {U : X.Opens}
    [Nonempty U.toScheme] {z : X} (hzU : z ∉ U) :
    maximalIdeal (X.presheaf.stalk z) ≠ ⊥ := by
  intro hbot
  have hne : (U : Set X).Nonempty := by simpa using ‹Nonempty U.toScheme›
  have hxU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
  obtain ⟨s⟩ := nonempty_preimage_fromSpecStalk_of_specializes (genericPoint_specializes z) hxU
  have hs : s.1 ∈ puncturedSpectrum (X.presheaf.stalk z) :=
    preimage_le_puncturedSpectrum hzU s.2
  refine (Stacks.LocalCohomology.mem_puncturedSpectrumOpens_iff (A := ToType _) _).mp hs
    (PrimeSpectrum.ext (le_antisymm ?_ ?_))
  · exact le_maximalIdeal s.1.isPrime.ne_top
  · exact (le_of_eq hbot).trans bot_le

/-! ### The maximal ideal of the completed local ring -/

/-- **The maximal ideal of `𝒪^∧_{X, z}` is not an associated prime of `𝒪^∧_{X, z}`**, for `z` a
point of an integral locally Noetherian scheme lying outside a nonempty open `U`. -/
theorem not_isAssociatedPrimeStacks_maximalIdeal_completedStalk {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {U : X.Opens} [Nonempty U.toScheme] {z : X} (hzU : z ∉ U) :
    ¬ IsAssociatedPrimeStacks (X.completedLocalRingCat z) (X.completedLocalRingCat z)
      (maximalIdeal (X.completedLocalRingCat z)) := by
  obtain ⟨a, haM, ha0⟩ := Submodule.ne_bot_iff _ |>.mp (maximalIdeal_stalk_ne_bot_of_notMem hzU)
  refine not_isAssociatedPrimeStacks_of_flat_of_mem (f := (X.toCompletedLocalRing z).hom)
    (AdicCompletion.flat_of_isNoetherian _) ha0 ?_
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.mem_map_of_mem _ haM

/-! ### The second paragraph of Tag 0AWC, with the dimension hypothesis weakened -/

/-- **`j_* 𝒪_U` is not coherent when a completed local ring outside `U` has an associated prime
of dimension at most one.** Let `j : U → X` be the inclusion of a nonempty open subscheme of an
integral locally Noetherian scheme and let `z` be a point of `X` outside `U`. If the completion
`𝒪^∧_{X, z}` has an associated prime `𝔭` — a prime which is the annihilator of one of its
elements — with `dim(𝒪^∧_{X, z} ⧸ 𝔭) ≤ 1`, then `j_* 𝒪_U` is not coherent. -/
@[stacks 0AWC "second paragraph, for an associated quotient of the completion of dimension at \
most one", ega "IV 7.2.4" "(e) ⇒ (f)"]
theorem not_isCoherent_pushforward_structureSheaf_of_isAssociatedPrime_completedStalk_le_one
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {U : X.Opens}
    [Nonempty U.toScheme] {z : X} (hzU : z ∉ U)
    {p : PrimeSpectrum (X.completedLocalRingCat z)}
    (hp : IsAssociatedPrimeStacks (X.completedLocalRingCat z) (X.completedLocalRingCat z)
      p.asIdeal)
    (hdim : ringKrullDim (X.completedLocalRingCat z ⧸ p.asIdeal) ≤ 1) :
    ¬ ((Scheme.Modules.pushforward U.ι).obj (SheafOfModules.unit _)).IsCoherent := by
  have := p.isPrime
  rcases eq_or_ne p.asIdeal (maximalIdeal (X.completedLocalRingCat z)) with hmax | hmax
  · exact absurd (hmax ▸ hp) (not_isAssociatedPrimeStacks_maximalIdeal_completedStalk hzU)
  · exact not_isCoherent_pushforward_structureSheaf_of_isAssociatedPrime_completedStalk hzU hp
      (le_antisymm hdim (one_le_ringKrullDim_quotient_of_ne_maximalIdeal p.asIdeal hmax))

end Stacks.AlgebraicGeometry.CoherentPushforwardCriterion

end
