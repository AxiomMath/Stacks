module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The punctured spectrum of a local ring, and its sections

This file introduces the *punctured spectrum* of a local ring — the open complement of the closed
point of its spectrum — and computes the sections of the structure sheaf over it when the ring is
a one-dimensional local domain: they are a fraction field.

This is the second of the three inputs that the sketch of [Stacks, Tag 0AWC] needs and the
library lacks. In that sketch the ring is the quotient `B ⧸ 𝔭` of the completed local ring `B` by
an associated prime with `dim(B ⧸ 𝔭) = 1`, and the computation below is the step "`X'` consists
only of the two points `x` and `z`": `Spec (B ⧸ 𝔭)` has exactly the two primes `0` and the
maximal ideal, so its punctured spectrum is the single generic point and the sections there are
`Frac(B ⧸ 𝔭)`.

## Main results

* `Stacks.LocalCohomology.puncturedSpectrumOpens` and
  `Stacks.LocalCohomology.puncturedSpectrum`: the punctured spectrum of a local ring, as an open
  of `PrimeSpectrum` and as an open of the scheme `Spec`.
* `Stacks.LocalCohomology.puncturedSpectrumOpens_eq_basicOpen` and
  `Stacks.LocalCohomology.puncturedSpectrum_eq_basicOpen`: for a one-dimensional local domain the
  punctured spectrum is the basic open of any nonzero element of the maximal ideal.
* `Stacks.LocalCohomology.basicOpen_eq_singleton_bot`: hence it consists of the single generic
  point.
* `Stacks.LocalCohomology.isFractionRing_sections_puncturedSpectrum`: for a local domain `R` with
  `ringKrullDim R = 1`, the sections `Γ(Spec R, puncturedSpectrum R)` are a fraction field of `R`.
* `Stacks.LocalCohomology.preimage_puncturedSpectrum`: the punctured spectrum pulls back to the
  punctured spectrum along the spectrum of a surjective local homomorphism. Together with
  `AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj` this identifies the sections of
  `𝒪_{V(𝔭)}` over the punctured spectrum of `B` with the sections over the punctured spectrum of
  `B ⧸ 𝔭`, which the previous item computes.

## Implementation notes

The scheme-level `puncturedSpectrum` is phrased for `R : CommRingCat`, not for a bare `Type u`
carrying a `CommRing` instance. This is forced: Mathlib's `Algebra R Γ(Spec R, U)` and
`IsLocalization.Away f Γ(Spec R, PrimeSpectrum.basicOpen f)` instances are keyed on the carrier of
a `CommRingCat` and are not found for a bare type. For the same reason the scheme-level open is an
`(Spec R).Opens` rather than an `Opens (PrimeSpectrum R)`: the two are definitionally equal, but
only the former shape lets instance search reach the `Γ(Spec R, -)` instances. Statements that
need no such instance are proved at the `Opens (PrimeSpectrum R)` level and transported across the
definitional equality.

### What [Stacks, Tag 0AWC] still needs

No `@[stacks 0AWC]` attribute is attached to anything here. That tag asserts outright that
`j_*𝒪_U` is *not* coherent, and this file proves none of that: it supplies one of the three
sheaf-theoretic inputs of the source's sketch. The other two are left exactness of `Γ(V, -)` and
the sheaf-level identification of the sections over the punctured spectrum, both in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSections`, and the degree-zero flat base
change of [Stacks, Tag 02KH] part (1) together with [Stacks, Tag 05AZ], which is
`Stacks.AlgebraicGeometry.FlatBaseChange.isIso_pushforwardBaseChange_of_isAffine` and
`Stacks.AlgebraicGeometry.FlatBaseChange.isFiniteType_of_pullback_fpqcCover`. What the tag still
needs on top of all three is recorded in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.CompletedLocalObstruction`.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.LocalCohomology

/-- The **punctured spectrum** of a local ring `A`, as an open of `PrimeSpectrum A`: the
complement of the closed point. -/
def puncturedSpectrumOpens (A : Type u) [CommRing A] [IsLocalRing A] :
    Opens (PrimeSpectrum A) :=
  ⟨{IsLocalRing.closedPoint A}ᶜ,
    (IsLocalRing.isClosed_singleton_closedPoint A).isOpen_compl⟩

/-- The **punctured spectrum** of a local ring `R`, as an open of the scheme `Spec R`.

This is the open that [Stacks, Tag 0AWC] and [Stacks, Tag 0E9I] work over. The library had no
name for it; it was previously spelled out inline wherever it was needed. -/
def puncturedSpectrum (R : CommRingCat.{u}) [IsLocalRing R] : (Spec R).Opens :=
  puncturedSpectrumOpens (ToType R)

/-- A point lies in the punctured spectrum exactly when it is not the closed point. -/
@[simp]
theorem mem_puncturedSpectrumOpens_iff {A : Type u} [CommRing A] [IsLocalRing A]
    (x : PrimeSpectrum A) :
    x ∈ puncturedSpectrumOpens A ↔ x ≠ IsLocalRing.closedPoint A := Iff.rfl

/-- The closed point is not in the punctured spectrum. -/
theorem closedPoint_notMem_puncturedSpectrumOpens (A : Type u) [CommRing A] [IsLocalRing A] :
    IsLocalRing.closedPoint A ∉ puncturedSpectrumOpens A := by simp

/-- Sections over an open which happens to be a basic open are the corresponding localization.

This is Mathlib's instance `IsLocalization.Away f Γ(Spec R, PrimeSpectrum.basicOpen f)` made
available for an open that is only *equal* to a basic open; instance search cannot see through the
equality on its own. -/
theorem isLocalization_away_sections_of_eq_basicOpen {R : CommRingCat.{u}} (f : R)
    {U : (Spec R).Opens} (hU : U = PrimeSpectrum.basicOpen f) :
    IsLocalization.Away f Γ(Spec R, U) := by
  subst hU; infer_instance

/-- A nonzero element of a domain is not in the zero prime. -/
private theorem notMem_bot_asIdeal {A : Type u} [CommRing A] [IsDomain A] {f : A}
    (hf0 : f ≠ 0) : f ∉ (⊥ : PrimeSpectrum A).asIdeal := by
  simpa using hf0

section OneDimensional

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [Ring.KrullDimLE 1 A]

/-- In a one-dimensional local domain the only primes are `0` and the maximal ideal, so the basic
open of a nonzero element of the maximal ideal is the single generic point.

This is the sketch of [Stacks, Tag 0AWC] observing that `X'` has only the two points `x` and
`z`. -/
@[ega "I 3.7.2" "partial", ega "II 7.1.5" "{b} is open"]
theorem basicOpen_eq_singleton_bot {f : A} (hf : f ∈ IsLocalRing.maximalIdeal A) (hf0 : f ≠ 0) :
    (PrimeSpectrum.basicOpen f).1 = {(⊥ : PrimeSpectrum A)} := by
  refine Set.ext fun x => ?_
  show f ∉ x.asIdeal ↔ x = ⊥
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · exact (IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top x).resolve_right fun h => hx (h ▸ hf)
  · exact hx ▸ notMem_bot_asIdeal hf0

/-- In a one-dimensional local domain the punctured spectrum is the basic open of any nonzero
element of the maximal ideal. -/
theorem puncturedSpectrumOpens_eq_basicOpen {f : A} (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hf0 : f ≠ 0) :
    puncturedSpectrumOpens A = PrimeSpectrum.basicOpen f := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  show x ≠ IsLocalRing.closedPoint A ↔ f ∉ x.asIdeal
  refine ⟨fun hx => ?_, fun hx h => hx (h ▸ hf)⟩
  rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top x with h | h
  · exact h ▸ notMem_bot_asIdeal hf0
  · exact absurd h hx

end OneDimensional

/-- The scheme-level form of `puncturedSpectrumOpens_eq_basicOpen`. -/
theorem puncturedSpectrum_eq_basicOpen (R : CommRingCat.{u}) [IsLocalRing R] [IsDomain R]
    [Ring.KrullDimLE 1 R] {f : R} (hf : f ∈ IsLocalRing.maximalIdeal (ToType R)) (hf0 : f ≠ 0) :
    puncturedSpectrum R = PrimeSpectrum.basicOpen f :=
  puncturedSpectrumOpens_eq_basicOpen (ToType R) hf hf0

/-- **The sections over the punctured spectrum of a one-dimensional local domain are a fraction
field.**

For `R` a local domain with `ringKrullDim R = 1`, the punctured spectrum is the basic open of any
nonzero element `f` of the maximal ideal, and it consists of the single prime `0`; hence the
sections there are the localization of `R` away from `f`, which is the localization of `R` at the
prime `0`, which is `Frac R`.

This is the identification of `Γ(V, 𝒪_{V(𝔭)}|_V)` with `Frac(B ⧸ 𝔭)` that the sketch of
[Stacks, Tag 0AWC] uses, applied with `R = B ⧸ 𝔭` for `𝔭` an associated prime of the completed
local ring `B` with `dim(B ⧸ 𝔭) = 1`. -/
theorem isFractionRing_sections_puncturedSpectrum (R : CommRingCat.{u}) [IsLocalRing R]
    [IsDomain R] (hR : ringKrullDim (ToType R) = 1) :
    IsFractionRing R Γ(Spec R, puncturedSpectrum R) := by
  have hle : Ring.KrullDimLE 1 (ToType R) := Ring.krullDimLE_iff.mpr (le_of_eq hR)
  have hfield : ¬ IsField (ToType R) := by
    intro h
    rw [ringKrullDim_eq_zero_of_isField h] at hR
    exact absurd hR (by simp)
  have hm : IsLocalRing.maximalIdeal (ToType R) ≠ ⊥ := fun h =>
    hfield (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have haway : IsLocalization.Away f Γ(Spec R, puncturedSpectrum R) :=
    isLocalization_away_sections_of_eq_basicOpen f (puncturedSpectrum_eq_basicOpen R hf hf0)
  have hat := (PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton
    (S := Γ(Spec R, puncturedSpectrum R))
    (basicOpen_eq_singleton_bot (ToType R) hf hf0)).mp haway
  rw [IsLocalization.AtPrime] at hat
  have heq : ((⊥ : PrimeSpectrum (ToType R)).asIdeal).primeCompl = nonZeroDivisors (ToType R) :=
    Ideal.primeCompl_bot
  rwa [heq] at hat

/-- **The punctured spectrum pulls back to the punctured spectrum** along the spectrum of a
surjective homomorphism of local rings.

For `φ : B ⟶ B ⧸ 𝔭` this says that the closed subscheme `V(𝔭) = Spec (B ⧸ 𝔭)` meets the punctured
spectrum of `B` exactly in the punctured spectrum of `B ⧸ 𝔭`. Since the sections of a direct image
over an open are by definition the sections over its preimage
(`AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj`), this identifies
`Γ(V, 𝒪_{V(𝔭)}|_V)` with `Γ(Spec (B ⧸ 𝔭), puncturedSpectrum (B ⧸ 𝔭))`, which
`isFractionRing_sections_puncturedSpectrum` computes to be `Frac(B ⧸ 𝔭)`. -/
theorem preimage_puncturedSpectrum {R S : CommRingCat.{u}} [IsLocalRing R] [IsLocalRing S]
    (φ : R ⟶ S) (hφ : Function.Surjective φ.hom) :
    Spec.map φ ⁻¹ᵁ puncturedSpectrum R = puncturedSpectrum S := by
  have : IsLocalHom φ.hom := IsLocalHom.of_surjective φ.hom hφ
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  show PrimeSpectrum.comap φ.hom x ≠ IsLocalRing.closedPoint (ToType R) ↔
    x ≠ IsLocalRing.closedPoint (ToType S)
  rw [not_iff_not]
  refine ⟨fun h => PrimeSpectrum.comap_injective_of_surjective _ hφ ?_,
    fun h => h ▸ IsLocalRing.comap_closedPoint φ.hom⟩
  rw [h, IsLocalRing.comap_closedPoint φ.hom]

/-- **The sections of `𝒪_{V(𝔭)}` over the punctured spectrum of `B` are a fraction field of
`B ⧸ 𝔭`.**

This is `isFractionRing_sections_puncturedSpectrum` transported along
`preimage_puncturedSpectrum`: the sections of the direct image `π_*𝒪_{Spec S}` over the punctured
spectrum of `R` are by definition (`AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj`) the
sections of `𝒪_{Spec S}` over `Spec φ ⁻¹ᵁ puncturedSpectrum R`, and that open is the punctured
spectrum of `S`. -/
theorem isFractionRing_sections_preimage_puncturedSpectrum {R S : CommRingCat.{u}} [IsLocalRing R]
    [IsLocalRing S] [IsDomain S] (φ : R ⟶ S) (hφ : Function.Surjective φ.hom)
    (hS : ringKrullDim (ToType S) = 1) :
    IsFractionRing S Γ(Spec S, Spec.map φ ⁻¹ᵁ puncturedSpectrum R) := by
  rw [preimage_puncturedSpectrum φ hφ]
  exact isFractionRing_sections_puncturedSpectrum S hS

end Stacks.LocalCohomology

end
