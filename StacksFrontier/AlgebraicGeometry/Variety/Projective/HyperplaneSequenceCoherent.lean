module

public import StacksFrontier.AlgebraicGeometry.ProjSaturation.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRestrictionConstruction

/-!
# [Stacks, Tag 08A0] for a coherent sheaf on `ℙⁿ_k`

Let `k` be an infinite field and let `ℱ` be a coherent sheaf on
`ℙⁿ_k = AlgebraicGeometry.projectiveSpaceOverRing n k`. Tag 08A0 asserts the existence of a
nonzero global section `s` of `𝒪(1)` such that, writing `i : H ⟶ ℙⁿ_k` for the hyperplane `H`
cut out by `s`, the sequence

`0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_* i^* ℱ ⟶ 0`

is short exact, the first arrow being multiplication by `s`. That is
`AlgebraicGeometry.exists_section_shortExact_hyperplaneUnit` below, on no hypothesis beyond
`k` infinite and `ℱ` coherent.

## Main results

* `AlgebraicGeometry.degreeSection_one_ne_zero`: a nonzero linear form on `k[T₀, …, Tₙ]` gives a
  nonzero global section of `𝒪(1)` on `Proj k[T₀, …, Tₙ]`.
* `AlgebraicGeometry.exists_section_shortExact_hyperplaneUnit`: **[Stacks, Tag 08A0].**

## The mathematics

The two halves of the tag are proved separately, and this file is their junction.

The section is `AlgebraicGeometry.exists_form_section_nonvanishing`, applied to `ℱ(-1)` — which
is coherent, `ℱ` being coherent — on the base-change model `ℙⁿ_k`: over an infinite field it
produces a global section of `𝒪(1)` vanishing at no associated point of `ℱ(-1)`, and coming from
a nonzero degree-one form `f` on `Proj k[T₀, …, Tₙ]`.

The sequence is `…ProjectiveSpaceHyperplaneSection.shortExact_hyperplaneUnit_of_nonvanishing`,
which holds on `ℙⁿ_S` for a module whose twist `ℱ(-1)` and whose `ℱ(-1) ⊗ 𝒪(1)` are
quasi-coherent, given a section not vanishing near any associated point of `ℱ(-1)`. All three
inputs are discharged here. The nonvanishing hypothesis is the chosen section's, read from the
nonvanishing *locus* to the nonvanishing *open* that surrounds each of its points
(`Stacks.NonvanishingOpen.nonvanishingOpen`), the two spellings of the locus being compared by
`Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq`. Quasi-coherence of `ℱ(-1)` is
quasi-coherence of a coherent module; quasi-coherence of `ℱ(-1) ⊗ 𝒪(1)` is [Stacks, Tag 0GQM]
(`Stacks.SheafOfModules.TensorProduct.isQuasicoherent_tensorSheaf'`), transported from the
sheafification spelling of the tensor product to
`Stacks.RelativeVeryAmple.tensorModules` along
`Stacks.AmplePullbackPart1.tensorIsoTensorModules`.

Nonvanishing of `s` itself — `s ≠ 0`, which is part of the assertion — is where
`AlgebraicGeometry.degreeSection_one_ne_zero` is used: the comparison of the two models carries
`s` to the section `f / 1` of `𝒪(1)` on `Proj k[T₀, …, Tₙ]`, and that section is nonzero because
`f` is. By the saturation criterion `…ProjectiveSpectrum.Proj.degreeSection_eq_zero_iff` a
homogeneous element of a Noetherian ring generated in degree one has vanishing twisted section
exactly when some whole homogeneous component kills it; `T₀ᴺ` is a nonzero element of the `N`-th
component of a polynomial ring over a field, which is a domain, so nothing but `0` is killed.

## References

* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
* [Stacks Project, Tag 0GQM](https://stacks.math.columbia.edu/tag/0GQM)
* [Stacks Project, Tag 0BXD](https://stacks.math.columbia.edu/tag/0BXD)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistTensorPow Stacks.RelativeVeryAmple
open Stacks.ProjectiveCohomology (polyGrading)

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **A nonzero linear form has a nonzero section of `𝒪(1)`.** For `f` a nonzero degree-one
element of `k[T₀, …, Tₙ]`, the canonical global section `f / 1` of `𝒪(1)` on
`Proj k[T₀, …, Tₙ]` is nonzero.

By `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection_eq_zero_iff` the section vanishes
only if some whole homogeneous component annihilates `f`; the `N`-th component contains `T₀ᴺ`,
which is nonzero, and a polynomial ring over a field is a domain. -/
theorem degreeSection_one_ne_zero (k : Type u) [Field k] (n : ℕ)
    {f : MvPolynomial (Fin (n + 1)) k} (hf : f ∈ polyGrading k n 1) (hf0 : f ≠ 0) :
    degreeSection (polyGrading k n) 1 ⟨f, hf⟩ ≠ 0 := by
  intro hzero
  obtain ⟨N, hN⟩ := (degreeSection_eq_zero_iff (polyGrading k n)
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n + 1)) k) ⟨f, hf⟩).mp hzero
  have hX : (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) k) ^ N ∈
      polyGrading k n N := by
    simpa using
      SetLike.pow_mem_graded N (Stacks.AlgebraicGeometry.ProjPolyChart.X_mem_one k n 0)
  rcases mul_eq_zero.mp (hN _ hX) with h | h
  · exact pow_ne_zero N (MvPolynomial.X_ne_zero (0 : Fin (n + 1))) h
  · exact hf0 h

section Sequence

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

open CategoryTheory.MonoidalCategory
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication
open Stacks.AlgebraicGeometry.ProjectiveSpaceHyperplaneSection
  (shortExact_hyperplaneUnit_of_nonvanishing)

/-- **[Stacks, Tag 08A0].** Let `k` be an infinite field and let `ℱ` be a coherent sheaf on
`ℙⁿ_k`. Then there is a nonzero global section `s` of `𝒪(1)` such that, with `i : H ⟶ ℙⁿ_k` the
hyperplane cut out by `s`, the sequence

`0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_* i^* ℱ ⟶ 0`

is short exact — the first arrow being multiplication by `s`
(`…ProjectiveSpaceSectionMultiplication.twistSectionMulNegOne`) and the second the restriction
to `H` (`…ProjectiveSpaceSectionMultiplication.hyperplaneUnit`).

The section is produced by `AlgebraicGeometry.exists_form_section_nonvanishing` applied to the
coherent module `ℱ(-1)`, which is the only step at which `k` has to be infinite, and the
sequence is `…ProjectiveSpaceHyperplaneSection.shortExact_hyperplaneUnit_of_nonvanishing`; the
quasi-coherence that the latter asks of `ℱ(-1)` and of `ℱ(-1) ⊗ 𝒪(1)` holds for every coherent
`ℱ`, by [Stacks, Tag 0GQM]. -/
@[stacks 08A0]
theorem exists_section_shortExact_hyperplaneUnit (k : Type u) [Field k] [Infinite k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) [F.IsCoherent] :
    ∃ s : (twistOver n (Spec (CommRingCat.of k)) 1).sections,
      PresheafOfModules.sections.eval s (op ⊤) ≠ 0 ∧
      ∃ w : twistSectionMulNegOne n (Spec (CommRingCat.of k)) F s ≫
          hyperplaneUnit n (Spec (CommRingCat.of k)) F s = 0,
        (ShortComplex.mk (twistSectionMulNegOne n (Spec (CommRingCat.of k)) F s)
          (hyperplaneUnit n (Spec (CommRingCat.of k)) F s) w).ShortExact := by
  have : IsLocallyNoetherian (projectiveSpaceOverRing n (CommRingCat.of k)) :=
    projectiveSpaceOver_isLocallyNoetherian n (Spec (CommRingCat.of k))
  have : (projectiveTwist n F (-1)).IsCoherent := isCoherent_projectiveTwist n F (-1)
  obtain ⟨f, hf, v, hf0, hv, hsub⟩ :=
    exists_form_section_nonvanishing k n (projectiveTwist n F (-1))
  set s := (Stacks.NonvanishingSpelling.sectionsEquiv
    (projectiveSpaceOverRing n (CommRingCat.of k))
    (twistOver n (Spec (CommRingCat.of k)) 1)).symm v with hs
  have hsv : PresheafOfModules.sections.eval s (op ⊤) = v := by
    rw [hs, ← Stacks.NonvanishingSpelling.sectionsEquiv_apply, Equiv.apply_symm_apply]
  rw [← hsv] at hv hsub
  have hnv : Stacks.SheafOfModules.nonvanishingLocus
        (twistOver n (Spec (CommRingCat.of k)) 1) s
      = Stacks.Ample.nonvanishingLocus (twistOver n (Spec (CommRingCat.of k)) 1)
        (PresheafOfModules.sections.eval s (op ⊤)) :=
    Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq
      (projectiveSpaceOverRing n (CommRingCat.of k))
      (twistOver n (Spec (CommRingCat.of k)) 1) s
  have hW : ∀ x ∈ Stacks.Divisors.associatedPoints
      (Stacks.RelativeVeryAmple.tensorModules
        (projectiveSpaceOverRing n (CommRingCat.of k)) F
        (twistOver n (Spec (CommRingCat.of k)) (-1))),
      ∃ W : (projectiveSpaceOverRing n (CommRingCat.of k)).Opens, x ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (twistOver n (Spec (CommRingCat.of k)) 1) s := by
    intro x hx
    refine ⟨Stacks.NonvanishingOpen.nonvanishingOpen
      (projectiveSpaceOverRing n (CommRingCat.of k))
      (twistOver n (Spec (CommRingCat.of k)) 1)
      (PresheafOfModules.sections.eval s (op ⊤)), hsub hx, fun y hy => ?_⟩
    rw [hnv]
    exact hy
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : (Stacks.RelativeVeryAmple.tensorModules
          (projectiveSpaceOverRing n (CommRingCat.of k)) F
          (twistOver n (Spec (CommRingCat.of k)) (-1))
      ⊗ twistOver n (Spec (CommRingCat.of k)) 1).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent
        (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf).prop_of_iso
      (Stacks.AmplePullbackPart1.tensorIsoTensorModules
        (projectiveSpaceOverRing n (CommRingCat.of k))
        (Stacks.RelativeVeryAmple.tensorModules
          (projectiveSpaceOverRing n (CommRingCat.of k)) F
          (twistOver n (Spec (CommRingCat.of k)) (-1)))
        (twistOver n (Spec (CommRingCat.of k)) 1)).symm
      inferInstance
  obtain ⟨w, hSE⟩ :=
    shortExact_hyperplaneUnit_of_nonvanishing n (Spec (CommRingCat.of k)) F s hW
  refine ⟨s, ?_, w, hSE⟩
  intro h0
  refine degreeSection_one_ne_zero k n hf hf0 ?_
  rw [← hv, h0]
  exact map_zero _

end Sequence

end AlgebraicGeometry

end
