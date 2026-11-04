module

public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullback
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.NagataCatenaryCoherence
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterionMain
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrumReductionInduction
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.FirstLocalCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenaryExamples
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.RingTheory.AssociatedPrime.Spellings
public import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coherence of the pushforward from a punctured spectrum

Let `X` be an integral locally Noetherian scheme, `j : U ⟶ X` the inclusion of a nonempty open
subscheme with complement `Z`, and assume that for every `z ∈ Z` and every associated prime `𝔭`
of the completed local ring `𝒪^∧_{X,z}` one has `dim(𝒪^∧_{X,z} ⧸ 𝔭) ≥ 2`. [Stacks, Tag 0BK1]
asserts that `j_*𝒪_U` is coherent. This file proves it.

The argument has two halves. The first five steps of the source reduce the tag to the punctured
spectra of the local rings `𝒪_{X,z}` along the complement; that reduction is
`Stacks.LocalCohomology.puncturedSpectrumReduction`, in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrumReductionInduction`. The last
three steps prove the tag for the punctured spectrum of a Noetherian local ring `A`, and they are
the content of this file:

* the completion `Â` of a Noetherian local ring is Nagata ([Stacks, Tag 032W]) and universally
  catenary ([Stacks, Tag 032C]), so assumptions (1) and (2) of [Stacks, Tag 0AWA] hold on
  `Spec Â`;
* assumption (3) of that tag on the punctured spectrum of `Spec Â` is exactly the hypothesis of
  [Stacks, Tag 0BK1] at the closed point, once the associated points of the structure sheaf of
  the punctured spectrum are identified with the associated primes of `Â` other than the maximal
  ideal and the reduced closure of such a point is identified with `Spec (Â ⧸ 𝔭)`;
* the punctured spectrum of `Spec Â` is the preimage of the punctured spectrum of `Spec A` under
  the completion map, which is flat and surjective, so coherence descends
  ([Stacks, Tag 02KH] and [Stacks, Tag 05AZ], assembled in
  `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_adicCompletion`).

## Main results

* `Stacks.LocalCohomology.isAssociatedPrimeStacks_of_isAssociatedPoint_unit_opens`: an associated
  point of the structure sheaf of an open of `Spec B`, for `B` Noetherian, sits at an associated
  prime of `B`.
* `Stacks.LocalCohomology.two_le_ringKrullDim_stalk_pointClosure_of_notMem_puncturedSpectrum`:
  assumption (3) of [Stacks, Tag 0AWA] on a punctured spectrum, read off `dim(B ⧸ 𝔭) ≥ 2`.
* `LocalCohomology.isCoherent_pushforward_structureSheaf_puncturedSpectrum_of_isPrecomplete`:
  coherence for the punctured spectrum of a *complete* Noetherian local ring.
* `Stacks.LocalCohomology.puncturedSpectrum_adicCompletion_eq_preimage`: the punctured spectrum of
  `Spec Â` is the preimage of the punctured spectrum of `Spec A`.
* `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_puncturedSpectrum`: coherence for
  the punctured spectrum of a Noetherian local ring `A`, under the dimension bound on the
  associated primes of `Â`.
* `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_completion_associatedPrime_dim`:
  **[Stacks, Tag 0BK1]**.

## Implementation notes

Associated primes are taken in the Stacks Project's sense (`IsAssociatedPrimeStacks`, the
annihilator of a single element), which over a Noetherian ring agrees with Mathlib's
`associatedPrimes`.

This file is not part of
`StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterionMain`, where the other
steps of the tag live, only because that module is imported by
`StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.SectionsFiniteness` and hence
by `...PushforwardCoherence.FirstLocalCohomologyFiniteness`, whose `pointClosureIso` is needed
here; putting these results there would make the import graph cyclic.

## References

* [Stacks Project, Tag 0BK1](https://stacks.math.columbia.edu/tag/0BK1)
* [Stacks Project, Tag 0AWA](https://stacks.math.columbia.edu/tag/0AWA)
* [Stacks Project, Tag 032C](https://stacks.math.columbia.edu/tag/032C)
* [Stacks Project, Tag 032W](https://stacks.math.columbia.edu/tag/032W)
* [Stacks Project, Tag 0310](https://stacks.math.columbia.edu/tag/0310)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace Stacks.LocalCohomology

/-! ### Associated points of the structure sheaf of an open of an affine scheme -/

/-- The maximal ideal of a local ring being an associated prime of the ring itself transports
along a ring isomorphism. -/
private theorem isAssociatedPrimeStacks_maximalIdeal_of_ringEquiv {A B : Type*} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B)
    (h : IsAssociatedPrimeStacks A A (maximalIdeal A)) :
    IsAssociatedPrimeStacks B B (maximalIdeal B) := by
  obtain ⟨_, m, hm⟩ := h
  refine ⟨(maximalIdeal.isMaximal B).isPrime, e m, ?_⟩
  ext b
  obtain ⟨a, rfl⟩ := e.surjective b
  rw [Submodule.mem_colon_span_singleton, Submodule.mem_bot]
  show e a * e m = 0 ↔ _
  rw [← map_mul, map_eq_zero_iff e e.injective]
  have hmul : a * m = 0 ↔ a ∈ maximalIdeal A := by
    rw [← hm, Submodule.mem_colon_span_singleton, Submodule.mem_bot]
    rfl
  rw [hmul, mem_maximalIdeal, mem_maximalIdeal]
  exact not_congr ⟨fun hu ↦ hu.map e.toMonoidHom,
    fun hu ↦ by simpa using hu.map e.symm.toMonoidHom⟩

open Module.associatedPrimes in
/-- **An associated point of the structure sheaf of an open of an affine scheme sits at an
associated prime of the ring.** Let `B` be a Noetherian ring, `V` an open subscheme of `Spec B`
and `x` a point of `V` which is an associated point of `𝒪_V`. Then the prime of `B` at which `x`
sits is an associated prime of `B` in the Stacks Project's sense.

The local ring of `V` at `x` is the local ring of `Spec B` at the image of `x`
(`AlgebraicGeometry.Scheme.Opens.stalkIso`), which is the localization `B_𝔭`
(`AlgebraicGeometry.Spec.stalkIso`); being an associated point says that the maximal ideal of
that localization is an associated prime of it, and over a Noetherian ring an associated prime of
a localization contracts to an associated prime ([Stacks, Tag 0310] part (2)). -/
theorem isAssociatedPrimeStacks_of_isAssociatedPoint_unit_opens (B : Type u) [CommRing B]
    [IsNoetherianRing B] (V : (Spec (CommRingCat.of B)).Opens) (x : V.toScheme)
    (hx : x ∈ Stacks.Divisors.associatedPoints
      (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf)) :
    IsAssociatedPrimeStacks B B (V.ι.base x).asIdeal := by
  have h1 : IsAssociatedPrimeStacks (V.toScheme.presheaf.stalk x) (V.toScheme.presheaf.stalk x)
      (maximalIdeal (V.toScheme.presheaf.stalk x)) :=
    (Stacks.Divisors.isAssociatedPrimeStacks_congr
      (AlgebraicGeometry.structureSheafStalkLinearEquiv V.toScheme x) _).mp hx
  have h2 : IsAssociatedPrimeStacks ((Spec (CommRingCat.of B)).presheaf.stalk (V.ι.base x))
      ((Spec (CommRingCat.of B)).presheaf.stalk (V.ι.base x))
      (maximalIdeal ((Spec (CommRingCat.of B)).presheaf.stalk (V.ι.base x))) :=
    isAssociatedPrimeStacks_maximalIdeal_of_ringEquiv
      (AlgebraicGeometry.Scheme.Opens.stalkIso V x).commRingCatIsoToRingEquiv h1
  have hp : ((V.ι.base x).asIdeal).IsPrime := (V.ι.base x).isPrime
  have h3 : IsAssociatedPrimeStacks (Localization.AtPrime (V.ι.base x).asIdeal)
      (Localization.AtPrime (V.ι.base x).asIdeal)
      (maximalIdeal (Localization.AtPrime (V.ι.base x).asIdeal)) :=
    isAssociatedPrimeStacks_maximalIdeal_of_ringEquiv (AlgebraicGeometry.Spec.stalkIso
      (CommRingCat.of B) (V.ι.base x)).commRingCatIsoToRingEquiv h2
  have h4 : maximalIdeal (Localization.AtPrime (V.ι.base x).asIdeal) ∈
      associatedPrimes (Localization.AtPrime (V.ι.base x).asIdeal)
        (Localization.AtPrime (V.ι.base x).asIdeal) :=
    Stacks.RingTheory.AssociatedPrimeStacks.assStacks_subset_associatedPrimes _ _ h3
  have hfg : (Ideal.under B
      (maximalIdeal (Localization.AtPrime (V.ι.base x).asIdeal))).FG := by
    rw [Localization.AtPrime.under_maximalIdeal]
    exact Ideal.fg_of_isNoetherianRing _
  have h5 := comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
    ((V.ι.base x).asIdeal).primeCompl
    (Algebra.linearMap B (Localization.AtPrime (V.ι.base x).asIdeal))
    (maximalIdeal (Localization.AtPrime (V.ι.base x).asIdeal)) h4 hfg
  rw [show Ideal.comap (algebraMap B (Localization.AtPrime (V.ι.base x).asIdeal))
      (maximalIdeal (Localization.AtPrime (V.ι.base x).asIdeal)) = (V.ι.base x).asIdeal from
    Localization.AtPrime.under_maximalIdeal] at h5
  exact isAssociatedPrimeStacks_of_mem_associatedPrimes h5

/-! ### The dimension bound on the point closures inside a punctured spectrum -/

/-- A prime of `B ⧸ 𝔭` whose contraction to `B` is the maximal ideal is the maximal ideal: the
contraction of a prime along a surjection determines it, and the image of a maximal ideal along a
surjection is maximal unless it is the unit ideal. -/
private theorem eq_maximalIdeal_quotient_of_comap {B : Type u} [CommRing B] [IsLocalRing B]
    (p : Ideal B) [IsLocalRing (B ⧸ p)] (z : Ideal (B ⧸ p)) (hzp : z.IsPrime)
    (hz : z.comap (Ideal.Quotient.mk p) = maximalIdeal B) : z = maximalIdeal (B ⧸ p) := by
  refine eq_maximalIdeal ?_
  have hsurj : Function.Surjective (Ideal.Quotient.mk p) := Ideal.Quotient.mk_surjective
  have hmc := Ideal.map_comap_of_surjective (Ideal.Quotient.mk p) hsurj z
  rw [hz] at hmc
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk p) hsurj
      (maximalIdeal.isMaximal B) with hh | hh
  · exact absurd (hmc ▸ hh) hzp.ne_top
  · exact hmc ▸ hh

/-- The localization of a local ring at its maximal ideal has the same Krull dimension as the
ring, being isomorphic to it: the complement of the maximal ideal consists of units. -/
private theorem ringKrullDim_localization_atPrime_maximalIdeal_eq (R : Type u) [CommRing R]
    [IsLocalRing R] (q : Ideal R) [q.IsPrime] (hq : q = maximalIdeal R) :
    ringKrullDim (Localization.AtPrime q) = ringKrullDim R := by
  subst hq
  exact (ringKrullDim_eq_of_ringEquiv (IsLocalization.atUnits R (maximalIdeal R).primeCompl
    (fun _ ha => IsLocalRing.notMem_maximalIdeal.mp ha)).toRingEquiv).symm

/-- **Assumption (3) of [Stacks, Tag 0AWA] on a punctured spectrum.** Let `B` be a local ring,
`V` the punctured spectrum of `Spec B` and `𝔭` a prime of `B` with `dim(B ⧸ 𝔭) ≥ 2`. Then every
point of the reduced closure of `𝔭` lying outside `V` — that is, the one point over the closed
point of `Spec B` — has local ring of Krull dimension at least two.

The reduced closure of `𝔭` is `Spec (B ⧸ 𝔭)` (`Stacks.LocalCohomology.pointClosureIso`), the one
point of it over the closed point is the maximal ideal of the local ring `B ⧸ 𝔭`
(`Stacks.LocalCohomology.subschemeι_pointClosureIso_hom`), and the localization of a local ring
at its maximal ideal is the ring itself. -/
theorem two_le_ringKrullDim_stalk_pointClosure_of_notMem_puncturedSpectrum (B : Type u)
    [CommRing B] [IsLocalRing B] (pt : PrimeSpectrum B) (V : (Spec (CommRingCat.of B)).Opens)
    (hV : (V : Set (Spec (CommRingCat.of B))) =
      ({IsLocalRing.closedPoint B} : Set (PrimeSpectrum B))ᶜ)
    (h : (2 : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ pt.asIdeal))
    (w : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({pt} : Set (Spec (CommRingCat.of B))))).subscheme)
    (hw : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({pt} : Set (Spec (CommRingCat.of B))))).subschemeι.base w ∉
        (V : Set (Spec (CommRingCat.of B)))) :
    (2 : WithBot ℕ∞) ≤ ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({pt} : Set (Spec (CommRingCat.of B))))).subscheme.presheaf.stalk w) := by
  obtain ⟨z, rfl⟩ : ∃ z, (pointClosureIso B pt).hom.base z = w :=
    ⟨_, (Scheme.homeoOfIso (pointClosureIso B pt)).apply_symm_apply w⟩
  have hiso : IsIso ((pointClosureIso B pt).hom.stalkMap z) :=
    IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
  have hpz : z.asIdeal.IsPrime := z.isPrime
  rw [ringKrullDim_eq_of_ringEquiv (CategoryTheory.Iso.commRingCatIsoToRingEquiv
      (asIso ((pointClosureIso B pt).hom.stalkMap z))),
    ringKrullDim_eq_of_ringEquiv (CategoryTheory.Iso.commRingCatIsoToRingEquiv
      (AlgebraicGeometry.Spec.stalkIso (CommRingCat.of (B ⧸ pt.asIdeal)) z))]
  have hclosed : PrimeSpectrum.comap (Ideal.Quotient.mk pt.asIdeal) z =
      IsLocalRing.closedPoint B := by
    rw [← subschemeι_pointClosureIso_hom B pt z]
    rw [hV] at hw
    by_contra hne
    exact hw hne
  have hz' : Ideal.comap (Ideal.Quotient.mk pt.asIdeal) z.asIdeal = maximalIdeal B :=
    congrArg PrimeSpectrum.asIdeal hclosed
  have : Nontrivial (B ⧸ pt.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr pt.isPrime.ne_top
  have : IsLocalRing (B ⧸ pt.asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk pt.asIdeal) Ideal.Quotient.mk_surjective
  rw [ringKrullDim_localization_atPrime_maximalIdeal_eq _ z.asIdeal
    (eq_maximalIdeal_quotient_of_comap pt.asIdeal z.asIdeal hpz hz')]
  exact h

/-! ### The punctured spectrum of a complete Noetherian local ring -/

/-- **[Stacks, Tag 0BK1] for the punctured spectrum of a complete Noetherian local ring.** Let
`B` be a Noetherian local ring which is complete for its maximal ideal, and assume every
associated prime `𝔭` of `B` satisfies `dim(B ⧸ 𝔭) ≥ 2`. Then the direct image of the structure
sheaf of the punctured spectrum of `Spec B` along its inclusion is coherent.

This is the sixth and seventh step of the argument of [Stacks, Tag 0BK1]. A complete Noetherian
local ring is Nagata ([Stacks, Tag 032W]) and universally catenary ([Stacks, Tag 032C]), so
assumptions (1) and (2) of [Stacks, Tag 0AWA] hold on `Spec B`; assumption (3) is the hypothesis
here, read at the associated points of the structure sheaf of the punctured spectrum through
`isAssociatedPrimeStacks_of_isAssociatedPoint_unit_opens` and
`two_le_ringKrullDim_stalk_pointClosure_of_notMem_puncturedSpectrum`. -/
@[ega "IV 7.2.2" "(b) ⇒ (a)", ega "IV 7.8.3" "(ix)"]
theorem isCoherent_pushforward_structureSheaf_puncturedSpectrum_of_isPrecomplete (B : Type u)
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [IsPrecomplete (maximalIdeal B) B]
    (hdim : ∀ p : Ideal B, IsAssociatedPrimeStacks B B p →
      (2 : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ p)) :
    ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum B).ι).obj
      (SheafOfModules.unit.{u}
        (Stacks.Divisors.puncturedSpectrum B).toScheme.ringCatSheaf)).IsCoherent :=
  isCoherent_pushforward_of_isNagataScheme _ _
    (AlgebraicGeometry.isNagataScheme_spec_of_isNagataRing B
      IsNagataRing.of_isPrecomplete_maximalIdeal)
    (AlgebraicGeometry.Scheme.isUniversallyCatenary_spec B
      (isUniversallyCatenary_of_isPrecomplete_maximalIdeal B))
    fun x hx w hw =>
      two_le_ringKrullDim_stalk_pointClosure_of_notMem_puncturedSpectrum B _ _ rfl
        (hdim _ (isAssociatedPrimeStacks_of_isAssociatedPoint_unit_opens B _ x hx)) w hw

/-! ### Descent along the completion map -/

/-- A prime of the completion of a Noetherian local ring contracts to the closed point exactly
when it is the closed point: the maximal ideal of the completion is the extension of the maximal
ideal, so a prime contracting into the maximal ideal contains the maximal ideal of the completion
and therefore equals it. -/
theorem comap_eq_closedPoint_iff_adicCompletion (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (q : PrimeSpectrum (AdicCompletion (maximalIdeal A) A)) :
    PrimeSpectrum.comap (algebraMap A (AdicCompletion (maximalIdeal A) A)) q =
      closedPoint A ↔ q = closedPoint (AdicCompletion (maximalIdeal A) A) := by
  refine ⟨fun hq ↦ ?_, ?_⟩
  · have hcomap : Ideal.comap (algebraMap A (AdicCompletion (maximalIdeal A) A)) q.asIdeal =
        maximalIdeal A := congrArg PrimeSpectrum.asIdeal hq
    have hle : maximalIdeal (AdicCompletion (maximalIdeal A) A) ≤ q.asIdeal := by
      rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_le_iff_le_comap, hcomap]
    exact PrimeSpectrum.ext
      ((maximalIdeal.isMaximal (AdicCompletion (maximalIdeal A) A)).eq_of_le
        q.isPrime.ne_top hle).symm
  · rintro rfl
    exact PrimeSpectrum.ext (IsLocalRing.maximalIdeal_comap _)

/-- The punctured spectrum of the completion of a Noetherian local ring is the preimage of the
punctured spectrum under the morphism of spectra induced by the completion map. -/
theorem puncturedSpectrum_adicCompletion_eq_preimage (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] :
    Stacks.Divisors.puncturedSpectrum (AdicCompletion (maximalIdeal A) A) =
      Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (maximalIdeal A) A))) ⁻¹ᵁ
        Stacks.Divisors.puncturedSpectrum A :=
  TopologicalSpace.Opens.ext
    (Set.ext fun q => (not_congr (comap_eq_closedPoint_iff_adicCompletion A q)).symm)

/-- **The punctured spectrum of a Noetherian local ring.** Let `A` be a
Noetherian local ring with completion `Â`, and assume every associated prime `𝔭` of `Â`
satisfies `dim(Â ⧸ 𝔭) ≥ 2`. Then the direct image of the structure sheaf of the punctured
spectrum of `Spec A` along its inclusion is coherent.

This is the case `X = Spec A`, `U` the punctured spectrum, of [Stacks, Tag 0BK1]: the complement
`Z` is the closed point, whose local ring is `A` itself, so the dimension bound above is the
tag's at that point. It is the last three steps of the tag's argument — the statement is
proved on the completion by
`isCoherent_pushforward_structureSheaf_puncturedSpectrum_of_isPrecomplete`, whose punctured
spectrum is the preimage of this one by `puncturedSpectrum_adicCompletion_eq_preimage`, and
descended along the faithfully flat completion map by
`isCoherent_pushforward_structureSheaf_of_adicCompletion`. -/
@[ega "IV 7.2.2" "(b) ⇒ (a)"]
theorem isCoherent_pushforward_structureSheaf_puncturedSpectrum (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ∀ p : Ideal (AdicCompletion (maximalIdeal A) A),
      IsAssociatedPrimeStacks (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal A) A) p →
      (2 : WithBot ℕ∞) ≤ ringKrullDim (AdicCompletion (maximalIdeal A) A ⧸ p)) :
    ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj
      (SheafOfModules.unit.{u}
        (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf)).IsCoherent :=
  isCoherent_pushforward_structureSheaf_of_adicCompletion A
    (Stacks.Divisors.puncturedSpectrum A)
    (puncturedSpectrum_adicCompletion_eq_preimage A)
    (isCoherent_pushforward_structureSheaf_puncturedSpectrum_of_isPrecomplete
      (AdicCompletion (maximalIdeal A) A) hdim)

/-! ### [Stacks, Tag 0BK1] -/

/-- **[Stacks, Tag 0BK1].** Let `X` be an integral locally Noetherian scheme and let `j : U ⟶ X`
be the inclusion of a nonempty open subscheme with complement `Z`. Assume that for every `z ∈ Z`
and every associated prime `𝔭` of the completed local ring `𝒪^∧_{X,z}` one has
`dim(𝒪^∧_{X,z} ⧸ 𝔭) ≥ 2`. Then `j_*𝒪_U` is coherent.

The proof is the source's. The reduction to the punctured spectra of the local rings along the
complement is `Stacks.LocalCohomology.puncturedSpectrumReduction`, and at a point `z` of the
complement the punctured spectrum of `𝒪_{X,z}` has coherent direct image by
`isCoherent_pushforward_structureSheaf_puncturedSpectrum`, whose hypothesis is `hdim` at `z`. -/
@[stacks 0BK1, ega "I 1.5.2" "special case", ega "IV 7.2.2" "(b) ⇒ (a)"]
theorem isCoherent_pushforward_structureSheaf_of_completion_associatedPrime_dim
    {U X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    [Nonempty U]
    (hdim : ∀ z : X, z ∉ Set.range j.base →
      ∀ p : Ideal (AdicCompletion (maximalIdeal (X.presheaf.stalk z)) (X.presheaf.stalk z)),
        IsAssociatedPrimeStacks
          (AdicCompletion (maximalIdeal (X.presheaf.stalk z)) (X.presheaf.stalk z))
          (AdicCompletion (maximalIdeal (X.presheaf.stalk z)) (X.presheaf.stalk z)) p →
        (2 : WithBot ℕ∞) ≤ ringKrullDim (AdicCompletion
          (maximalIdeal (X.presheaf.stalk z)) (X.presheaf.stalk z) ⧸ p)) :
    ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit.{u} U.ringCatSheaf)).IsCoherent :=
  puncturedSpectrumReduction j fun z hz =>
    isCoherent_pushforward_structureSheaf_puncturedSpectrum (X.presheaf.stalk z) (hdim z hz)

end Stacks.LocalCohomology

end
