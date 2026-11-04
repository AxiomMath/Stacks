module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteLocalFinal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalencePort
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ResolutionByNormalizedBlowUps
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lipman's theorem on the resolution of two-dimensional schemes

For a two-dimensional integral Noetherian scheme `Y` the following four conditions are
equivalent:

1. there is an alteration `X ⟶ Y` with `X` regular;
2. there is a resolution of singularities of `Y`;
3. `Y` has a resolution of singularities by normalized blowups;
4. the normalization `Y^ν ⟶ Y` is finite, `Y^ν` has finitely many singular points, and the
   local ring of `Y^ν` at each of them has normal completion.

The implications `(3) ⇒ (2) ⇒ (1) ⇒ (4)` are in `Resolution/LipmanEquivalence.lean`. This file
supplies the way back from `(4)`, and the reduction it rests on.

## Main results

* `AlgebraicGeometry.ringKrullDim_adicCompletion_stalk_eq_two_of_mem_singularLocus`: the
  completion of the local ring at a singular point of a normal surface has dimension two.
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_adicCompletion_stalks`: a
  two-dimensional integral Noetherian scheme with finite normalization, whose normalization has
  finitely many singular points with normal completed local rings, has a resolution by normalized
  blowups as soon as the spectra of those completions do.
* `AlgebraicGeometry.tfae_exists_isAlteration_isRegular_of_gorensteinChain`: the equivalence of
  the four conditions, over the Gorenstein sequence of blowups of [Stacks, Tag 0BBV] alone (the
  only input of [Stacks, Tags 0BGM and 0BGN] not yet supplied by this library).

## Implementation notes

The reduction follows the source. One replaces `Y` by its normalization `N`, whose singular
points are closed, and globalizes resolutions by normalized blowups of the spectra of the local
rings of `N` at them (`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_local`). Each of
those is descended from the spectrum of the completion of the local ring
(`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_adicCompletion`, which is
[Stacks, Tag 0BGA] together with [Stacks, Tag 0BG6]); the completion is Nagata, being a complete
Noetherian local ring ([Stacks, Tag 032W]). Over the completion, which is a complete Noetherian
local normal domain of dimension two, the source applies [Stacks, Tags 0BGN and 0BGM].

## References

* [Lipman, *Rational singularities*, Theorem on page 151]
* [Stacks Project, Tag 0BGP](https://stacks.math.columbia.edu/tag/0BGP)
* [Stacks Project, Tag 0BGA](https://stacks.math.columbia.edu/tag/0BGA)
* [Stacks Project, Tag 0BGM](https://stacks.math.columbia.edu/tag/0BGM)
* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-- The completion of the local ring at a singular point of a normal locally Noetherian scheme of
dimension at most two has Krull dimension two: the local ring itself has dimension two, and
completion preserves the dimension of a Noetherian local ring. -/
theorem ringKrullDim_adicCompletion_stalk_eq_two_of_mem_singularLocus (N : Scheme.{u})
    [IsLocallyNoetherian N] [IsNormal N] (hdim : topologicalKrullDim N ≤ 2) (y : N)
    (hy : y ∈ singularLocus N) :
    ringKrullDim (AdicCompletion (maximalIdeal (N.presheaf.stalk y)) (N.presheaf.stalk y)) =
      2 := by
  rw [IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal]
  exact ringKrullDim_stalk_eq_two_of_mem_singularLocus N hdim y hy

/-- **Reduction of `(4) ⇒ (3)` to the completed local rings.** A two-dimensional integral
Noetherian scheme `Y` whose normalization is finite, with finitely many singular points at each
of which the completed local ring is normal, has a resolution of singularities by normalized
blowups as soon as the spectrum of each of those completions has one.

A resolution by normalized blowups of the spectrum of the completion of a Noetherian local
normal domain descends to the spectrum of the local ring itself, the completion being normal by
hypothesis and Nagata as a complete Noetherian local ring; and resolutions by normalized blowups
of the spectra of the local rings of the normalization at its singular points globalize. -/
@[ega "IV 7.9.6" "special case"]
theorem hasResolutionByNormalizedBlowUps_of_adicCompletion_stalks (Y : Scheme.{u})
    [IsIntegral Y] [IsNoetherian Y]
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)
    (hdim : topologicalKrullDim Y = 2)
    (hfin : IsFinite (Scheme.normalization Y hY))
    (hsing : (singularLocus (Y.normalizationScheme hY)).Finite)
    (hnormal : ∀ y : Y.normalizationScheme hY, y ∈ singularLocus (Y.normalizationScheme hY) →
      IsNormalRing (AdicCompletion
        (maximalIdeal ((Y.normalizationScheme hY).presheaf.stalk y))
        ((Y.normalizationScheme hY).presheaf.stalk y)))
    (hres : ∀ y : Y.normalizationScheme hY, y ∈ singularLocus (Y.normalizationScheme hY) →
      HasResolutionByNormalizedBlowUps (Spec (.of (AdicCompletion
        (maximalIdeal ((Y.normalizationScheme hY).presheaf.stalk y))
        ((Y.normalizationScheme hY).presheaf.stalk y))))) :
    HasResolutionByNormalizedBlowUps Y := by
  let N := Y.normalizationScheme hY
  have : IsNormal N := Scheme.isNormal_normalizationScheme Y hY
  have : IsLocallyNoetherian N :=
    LocallyOfFiniteType.isLocallyNoetherian (Scheme.normalization Y hY)
  refine hasResolutionByNormalizedBlowUps_of_local Y hY hdim hfin hsing fun y hy => ?_
  have : IsNormalDomain (N.presheaf.stalk y) :=
    ⟨IsNormal.stalk_isDomain y, IsNormal.stalk_normal y⟩
  exact hasResolutionByNormalizedBlowUps_of_adicCompletion _ (hnormal y hy)
    IsNagataRing.of_isPrecomplete_maximalIdeal (hres y hy)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **Lipman's theorem ([Stacks, Tag 0BGP]) over Tag 0BBV.** Let `Y` be a two-dimensional integral
Noetherian scheme. The following are equivalent:

1. there exists an alteration `X ⟶ Y` with `X` regular;
2. there exists a resolution of singularities of `Y`;
3. `Y` has a resolution of singularities by normalized blowups;
4. the normalization `Y^ν ⟶ Y` is finite, `Y^ν` has finitely many singular points, and the
   completion of the local ring of `Y^ν` at each of them is normal.

This is stated granted [Stacks, Tag 0BBV] in the form `h0BBV` of
`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_exists_isResolution_of_gorensteinChain`,
through which [Stacks, Tags 0BGM and 0BGN] enter the step `(4) ⇒ (3)`. -/
theorem tfae_exists_isAlteration_isRegular_of_gorensteinChain
    (h0BBV : ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A],
      IsNagataRing A → ringKrullDim A = 2 → DefinesRationalSingularity A →
      (∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        SingularPointBlowupChain IsNormal (Spec (.of A)) Y f ∧ IsGorenstein Y)
    (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y] (hdim : topologicalKrullDim Y = 2) :
    List.TFAE
      [∃ (X : Scheme.{u}) (f : X ⟶ Y), IsAlteration f ∧ IsRegular X,
       ∃ (X : Scheme.{u}) (f : X ⟶ Y), IsResolution f,
       HasResolutionByNormalizedBlowUps Y,
       ∃ hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite,
        IsFinite (Scheme.normalization Y hY) ∧
        (singularLocus (Y.normalizationScheme hY)).Finite ∧
        ∀ y : Y.normalizationScheme hY, y ∈ singularLocus (Y.normalizationScheme hY) →
          IsNormalRing (AdicCompletion
            (maximalIdeal ((Y.normalizationScheme hY).presheaf.stalk y))
            ((Y.normalizationScheme hY).presheaf.stalk y))] := by
  have hY := finite_irreducibleComponents_of_isCompact Y
  tfae_have 3 → 2 := exists_resolution_of_hasResolutionByNormalizedBlowUps Y hdim
  tfae_have 2 → 1 := exists_regular_alteration_of_exists_resolution Y
  tfae_have 1 → 4 := fun h =>
    ⟨hY, finite_normalization_and_normal_completions_of_exists_regular_alteration Y hY hdim h⟩
  tfae_have 4 → 3 := by
    rintro ⟨hY, hfin, hsing, hnormal⟩
    refine hasResolutionByNormalizedBlowUps_of_adicCompletion_stalks Y hY hdim hfin hsing
      hnormal fun y hy => ?_
    let N := Y.normalizationScheme hY
    have : IsNormal N := Scheme.isNormal_normalizationScheme Y hY
    have : IsLocallyNoetherian N :=
      LocallyOfFiniteType.isLocallyNoetherian (Scheme.normalization Y hY)
    let B := AdicCompletion (maximalIdeal (N.presheaf.stalk y)) (N.presheaf.stalk y)
    obtain ⟨hdom, hic⟩ := (hnormal y hy).of_isLocalRing
    have : IsNormalDomain B := ⟨hdom, hic⟩
    have hdimB : ringKrullDim B = 2 :=
      ringKrullDim_adicCompletion_stalk_eq_two_of_mem_singularLocus N
        ((topologicalKrullDim_le_of_isIntegralHom (Scheme.normalization Y hY)).trans_eq hdim) y hy
    exact hasResolutionByNormalizedBlowUps_of_exists_isResolution_of_gorensteinChain h0BBV B
      hdimB (exists_isResolution_of_isAdicComplete_of_gorensteinChain h0BBV B hdimB)
  tfae_finish

end AlgebraicGeometry

end
