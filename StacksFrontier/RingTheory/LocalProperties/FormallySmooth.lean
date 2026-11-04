module

public import Mathlib.RingTheory.RingHom.Smooth
public import StacksFrontier.RingTheory.LocalProperties.Projective

/-!
# Formal smoothness is a local property of ring maps

Let `R → S` be a map of commutative rings and let `g₁, …, gₙ ∈ S` generate the unit ideal. If
every `S_{gᵢ}` is formally smooth over `R`, then so is `S`. Consequently
`RingHom.FormallySmooth` satisfies `RingHom.PropertyIsLocal`.

Mathlib has `RingHom.Smooth.propertyIsLocal`, but its proof of the descent step goes through
`Algebra.smoothLocus`, whose characterisations require `Algebra.FinitePresentation`, so it does
not apply to formal smoothness alone. The proof here instead localises the two conditions that
*define* `Algebra.FormallySmooth` in Mathlib (Stacks 031J (6)): projectivity of `Ω[S⁄R]` and
vanishing of `H¹(L_{S/R})`.

## Main results

* `Module.subsingleton_of_isLocalized_span_range`: a module whose localisations at a family
  generating the unit ideal vanish, vanishes.
* `Algebra.FormallySmooth.of_isLocalized_span_range`: formal smoothness is Zariski-local on the
  target.
* `RingHom.FormallySmooth.ofLocalizationSpanTarget`,
  `RingHom.FormallySmooth.ofLocalizationFiniteSpanTarget`,
  `RingHom.FormallySmooth.propertyIsLocal`: the `RingHom` meta-properties.

## Implementation notes

`Algebra.FormallySmooth R S` is Mathlib's class with fields `Module.Projective S Ω[S⁄R]` and
`Subsingleton (Algebra.H1Cotangent R S)`, so the two halves descend independently:

* `Ω[S⁄R]` localises, `KaehlerDifferential.isLocalizedModule`, and projectivity is Zariski-local
  by `Module.projective_of_isLocalized_span_range` — which is where the work is, projectivity
  being local only by faithfully flat descent (Stacks 05A9);
* `H¹(L_{S/R})` localises, `Algebra.H1Cotangent.isLocalizedModule`, and a module that vanishes
  locally vanishes.

Both localisation statements hold with no finiteness hypothesis on `S` over `R`.

The only input `RingHom.PropertyIsLocal` was missing for `RingHom.FormallySmooth` is
`OfLocalizationSpanTarget`; `localizationAwayPreserves`,
`StableUnderCompositionWithLocalizationAwayTarget` and, through
`RingHom.OfLocalizationSpanTarget.ofLocalizationSpan`, `OfLocalizationSpan` all follow from
Mathlib's `RingHom.FormallySmooth.isStableUnderBaseChange`,
`RingHom.FormallySmooth.stableUnderComposition` and
`RingHom.FormallySmooth.holdsForLocalizationAway`.

## References

* [Stacks Project, Tag 031J](https://stacks.math.columbia.edu/tag/031J)
* [Stacks Project, Tag 05A9](https://stacks.math.columbia.edu/tag/05A9)
* [Stacks Project, Tag 0D0F](https://stacks.math.columbia.edu/tag/0D0F)
-/

@[expose] public section

universe u

namespace Module

/-- **A module that vanishes locally vanishes.** If `f : ι → R` generates the unit ideal and the
localisation of `M` away from each `f i`, presented by `g i : M →ₗ[R] N i`, is zero, then `M` is
zero. The index type need not be finite. -/
theorem subsingleton_of_isLocalized_span_range {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {ι : Type*} (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤)
    (N : ι → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (g : ∀ i, M →ₗ[R] N i) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (g i)]
    (H : ∀ i, Subsingleton (N i)) : Subsingleton M := by
  refine subsingleton_of_forall_eq 0 fun m ↦ ?_
  suffices h : Module.eqIdeal R m 0 = ⊤ by
    simpa [Module.eqIdeal] using (Ideal.eq_top_iff_one _).mp h
  by_contra hne
  obtain ⟨r, hrs, hdisj⟩ := Ideal.exists_disjoint_powers_of_span_eq_top (Set.range f) hf _ hne
  obtain ⟨i, rfl⟩ := hrs
  obtain ⟨⟨_, n, rfl⟩, heq⟩ := (IsLocalizedModule.eq_iff_exists (.powers (f i)) (g i)).mp
    (@Subsingleton.elim _ (H i) _ _)
  exact Set.disjoint_left.mp hdisj heq ⟨n, rfl⟩

end Module

namespace Algebra

/-- **Formal smoothness is Zariski-local on the target.** Let `f : ι → S` be a finite family
generating the unit ideal of `S` and let `A i` be a localisation of `S` away from `f i`. If every
`A i` is formally smooth over `R`, then `S` is formally smooth over `R`.

This is the affine case of the equivalence of conditions (3) and (4) of Stacks 0D0F. No
finiteness hypothesis is placed on `S` over `R`. -/
theorem FormallySmooth.of_isLocalized_span_range {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {ι : Type*} [Finite ι] (f : ι → S) (hf : Ideal.span (Set.range f) = ⊤)
    (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra S (A i)] [∀ i, Algebra R (A i)]
    [∀ i, IsScalarTower R S (A i)] [∀ i, IsLocalization.Away (f i) (A i)]
    (H : ∀ i, Algebra.FormallySmooth R (A i)) :
    Algebra.FormallySmooth R S where
  projective_kaehlerDifferential :=
    Module.projective_of_isLocalized_span_range f hf A (fun i ↦ Ω[A i⁄R])
      (fun i ↦ KaehlerDifferential.map R R S (A i))
      fun i ↦ (H i).projective_kaehlerDifferential
  subsingleton_h1Cotangent :=
    Module.subsingleton_of_isLocalized_span_range f hf (fun i ↦ Algebra.H1Cotangent R (A i))
      (fun i ↦ Algebra.H1Cotangent.map R R S (A i))
      fun i ↦ (H i).subsingleton_h1Cotangent

/-- **Formal smoothness is Zariski-local on the target**, for the canonical localisations: if
`f : ι → S` is a finite family generating the unit ideal and every `Localization.Away (f i)` is
formally smooth over `R`, then so is `S`. -/
theorem FormallySmooth.of_localized_span_range {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {ι : Type*} [Finite ι] (f : ι → S) (hf : Ideal.span (Set.range f) = ⊤)
    (H : ∀ i, Algebra.FormallySmooth R (Localization.Away (f i))) :
    Algebra.FormallySmooth R S :=
  FormallySmooth.of_isLocalized_span_range f hf (fun i ↦ Localization.Away (f i)) H

end Algebra

namespace RingHom.FormallySmooth

/-- **Formal smoothness of a ring map can be checked on a finite standard cover of the target.**
This is `RingHom.OfLocalizationFiniteSpanTarget` for `RingHom.FormallySmooth`. -/
theorem ofLocalizationFiniteSpanTarget :
    RingHom.OfLocalizationFiniteSpanTarget @RingHom.FormallySmooth := by
  introv R hs hf
  algebraize [f]
  have key : ∀ r : {x // x ∈ s}, Algebra.FormallySmooth R (Localization.Away (r : S)) := by
    intro r
    have h := hf r
    rw [show (algebraMap S (Localization.Away (r : S))).comp f
          = algebraMap R (Localization.Away (r : S)) from
        (IsScalarTower.algebraMap_eq R S (Localization.Away (r : S))).symm] at h
    exact RingHom.formallySmooth_algebraMap.mp h
  exact Algebra.FormallySmooth.of_localized_span_range (Subtype.val : {x // x ∈ s} → S)
    (by rwa [Subtype.range_coe_subtype, Finset.setOfPred_mem]) key

/-- **Formal smoothness of a ring map can be checked on a standard cover of the target.** This is
`RingHom.OfLocalizationSpanTarget` for `RingHom.FormallySmooth`. -/
theorem ofLocalizationSpanTarget :
    RingHom.OfLocalizationSpanTarget @RingHom.FormallySmooth :=
  (_root_.RingHom.ofLocalizationSpanTarget_iff_finite
    (P := @RingHom.FormallySmooth)).mpr ofLocalizationFiniteSpanTarget

/-- Formal smoothness is stable under composition with localisation away, on source and target. -/
private theorem stableUnderCompositionWithLocalizationAway :
    RingHom.StableUnderCompositionWithLocalizationAway @RingHom.FormallySmooth :=
  RingHom.FormallySmooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway
    RingHom.FormallySmooth.holdsForLocalizationAway

/-- **Formal smoothness of a ring map can be checked on a standard cover of the source.** This is
`RingHom.OfLocalizationSpan` for `RingHom.FormallySmooth`. -/
theorem ofLocalizationSpan : RingHom.OfLocalizationSpan @RingHom.FormallySmooth :=
  ofLocalizationSpanTarget.ofLocalizationSpan stableUnderCompositionWithLocalizationAway.left

/-- **Formal smoothness is a local property of ring homomorphisms.** -/
theorem propertyIsLocal : RingHom.PropertyIsLocal @RingHom.FormallySmooth where
  localizationAwayPreserves :=
    RingHom.FormallySmooth.isStableUnderBaseChange.localizationPreserves.away
  ofLocalizationSpanTarget := ofLocalizationSpanTarget
  ofLocalizationSpan := ofLocalizationSpan
  StableUnderCompositionWithLocalizationAwayTarget :=
    stableUnderCompositionWithLocalizationAway.right

end RingHom.FormallySmooth

end
