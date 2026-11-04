module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Twist
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneSequenceCoherent

/-!
# [Stacks, Tag 08A0] at every twist, for one hyperplane

Let `k` be an infinite field and `ℱ` a coherent sheaf on `ℙⁿ_k`. Tag 08A0 produces a nonzero
global section `s` of `𝒪(1)` for which

`0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_* i^* ℱ ⟶ 0`

is short exact, `i : H ⟶ ℙⁿ_k` being the hyperplane cut out by `s`. What [Stacks, Tag 08A7]
needs is the same sequence for *every* twist `ℱ(d)`, with *one* hyperplane — the sequences at
different `d` have to be cut out by the same `s`, since the restriction maps they contain are
compared with each other.

That is `AlgebraicGeometry.exists_section_forall_twist_shortExact_hyperplaneUnit` below, and
twist-invariance of the associated points is what makes it available. The single condition the
section has to satisfy for the sequence at `ℱ(d)` is that it not vanish near any associated point
of `ℱ(d-1)`; by `Stacks.Divisors.associatedPoints_tensorModules_eq_of_isInvertibleModule` that
set is `Ass(ℱ)`, the same for every `d`, so a single application of the choice of Tag 08A0 — made
at `ℱ` itself rather than at one twist of it — serves all of them at once.

## Main results

* `AlgebraicGeometry.associatedPoints_projectiveTwist`: `Ass(ℱ(d)) = Ass(ℱ)` for every `d : ℤ`.
* `AlgebraicGeometry.exists_section_forall_twist_shortExact_hyperplaneUnit`: one nonzero section
  of `𝒪(1)` whose hyperplane gives the short exact sequence of [Stacks, Tag 08A0] at every twist
  `ℱ(d)`.

## Implementation notes

The twist `AlgebraicGeometry.projectiveTwist n F d` is `ℱ ⊗ 𝒪(d)` at the
`Stacks.RelativeVeryAmple.tensorModules` spelling of the tensor product, and `𝒪(d)` is invertible
by `Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver`, so
`associatedPoints_projectiveTwist` is an instance of the general twist-invariance of
`StacksFrontier/AlgebraicGeometry/Divisors/AssociatedPoints/Twist.lean` with no projective-space
input beyond that instance. It holds in every integer degree, negative ones included, which is
what the sequence at `ℱ(d)` needs: that sequence involves `ℱ(d-1)`.

The quasi-coherence that
`…ProjectiveSpaceHyperplaneSection.shortExact_hyperplaneUnit_of_nonvanishing` asks of `ℱ(d)(-1)`
and of `ℱ(d)(-1) ⊗ 𝒪(1)` is discharged exactly as in
`AlgebraicGeometry.exists_section_shortExact_hyperplaneUnit`: the first is coherence of a twist
of a coherent module, the second is [Stacks, Tag 0GQM] transported along
`Stacks.AmplePullbackPart1.tensorIsoTensorModules`.

## References

* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.ProjectiveCohomology (polyGrading)

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The associated points of a twist are the associated points.** `Ass(ℱ(d)) = Ass(ℱ)` on
`ℙⁿ_R`, in every integer degree `d`: the twist is `ℱ ⊗ 𝒪(d)` and `𝒪(d)` is invertible, so this
is `Stacks.Divisors.associatedPoints_tensorModules_eq_of_isInvertibleModule`. -/
theorem associatedPoints_projectiveTwist {R : Type u} [CommRing R] (n : ℕ)
    (F : (projectiveSpaceOverRing n (CommRingCat.of R)).Modules) (d : ℤ) :
    Stacks.Divisors.associatedPoints (projectiveTwist n F d) =
      Stacks.Divisors.associatedPoints F :=
  Stacks.Divisors.associatedPoints_tensorModules_eq_of_isInvertibleModule F
    (twistOver n (Spec (CommRingCat.of R)) d)

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

/-- **[Stacks, Tag 08A0] at every twist, for one hyperplane.** Let `k` be an infinite field and
`ℱ` a coherent sheaf on `ℙⁿ_k`. Then there is a nonzero global section `s` of `𝒪(1)` such that,
with `i : H ⟶ ℙⁿ_k` the hyperplane cut out by `s`, the sequence

`0 ⟶ ℱ(d)(-1) ⟶ ℱ(d) ⟶ i_* i^* ℱ(d) ⟶ 0`

is short exact **for every** `d : ℤ` — the first arrow being multiplication by `s` and the second
the restriction to `H`.

One `s` works for all `d` because the condition on it does not depend on `d`: the sequence at
`ℱ(d)` needs `s` not to vanish near any associated point of `ℱ(d)(-1)`, and
`AlgebraicGeometry.associatedPoints_projectiveTwist` identifies that set with `Ass(ℱ)`. So the
choice of [Stacks, Tag 08A0] is made once, at `ℱ` itself. -/
theorem exists_section_forall_twist_shortExact_hyperplaneUnit (k : Type u) [Field k] [Infinite k]
    (n : ℕ) (F : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) [F.IsCoherent] :
    ∃ s : (twistOver n (Spec (CommRingCat.of k)) 1).sections,
      PresheafOfModules.sections.eval s (op ⊤) ≠ 0 ∧
      ∀ d : ℤ, ∃ w : twistSectionMulNegOne n (Spec (CommRingCat.of k))
            (projectiveTwist n F d) s ≫
          hyperplaneUnit n (Spec (CommRingCat.of k)) (projectiveTwist n F d) s = 0,
        (ShortComplex.mk
          (twistSectionMulNegOne n (Spec (CommRingCat.of k)) (projectiveTwist n F d) s)
          (hyperplaneUnit n (Spec (CommRingCat.of k)) (projectiveTwist n F d) s) w).ShortExact := by
  have : IsLocallyNoetherian (projectiveSpaceOverRing n (CommRingCat.of k)) :=
    projectiveSpaceOver_isLocallyNoetherian n (Spec (CommRingCat.of k))
  obtain ⟨f, hf, v, hf0, hv, hsub⟩ := exists_form_section_nonvanishing k n F
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
  refine ⟨s, ?_, fun d => ?_⟩
  · intro h0
    refine degreeSection_one_ne_zero k n hf hf0 ?_
    rw [← hv, h0]
    exact map_zero _
  · have hFd : (projectiveTwist n F d).IsCoherent := isCoherent_projectiveTwist n F d
    have : (projectiveTwist n F d).IsQuasicoherent := isQuasicoherent_of_isCoherent _
    have : (projectiveTwist n (projectiveTwist n F d) (-1)).IsCoherent :=
      isCoherent_projectiveTwist n (projectiveTwist n F d) (-1)
    have hA : Stacks.Divisors.associatedPoints
        (Stacks.RelativeVeryAmple.tensorModules
          (projectiveSpaceOverRing n (CommRingCat.of k)) (projectiveTwist n F d)
          (twistOver n (Spec (CommRingCat.of k)) (-1)))
        = Stacks.Divisors.associatedPoints F :=
      (associatedPoints_projectiveTwist n (projectiveTwist n F d) (-1)).trans
        (associatedPoints_projectiveTwist n F d)
    have hW : ∀ x ∈ Stacks.Divisors.associatedPoints
        (Stacks.RelativeVeryAmple.tensorModules
          (projectiveSpaceOverRing n (CommRingCat.of k)) (projectiveTwist n F d)
          (twistOver n (Spec (CommRingCat.of k)) (-1))),
        ∃ W : (projectiveSpaceOverRing n (CommRingCat.of k)).Opens, x ∈ W ∧ ∀ y ∈ W,
          y ∈ Stacks.SheafOfModules.nonvanishingLocus
            (twistOver n (Spec (CommRingCat.of k)) 1) s := by
      intro x hx
      refine ⟨Stacks.NonvanishingOpen.nonvanishingOpen
        (projectiveSpaceOverRing n (CommRingCat.of k))
        (twistOver n (Spec (CommRingCat.of k)) 1)
        (PresheafOfModules.sections.eval s (op ⊤)), hsub (hA.subset hx), fun y hy => ?_⟩
      rw [hnv]
      exact hy
    have : (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (CommRingCat.of k))
            (projectiveTwist n F d) (twistOver n (Spec (CommRingCat.of k)) (-1))
        ⊗ twistOver n (Spec (CommRingCat.of k)) 1).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent
          (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf).prop_of_iso
        (Stacks.AmplePullbackPart1.tensorIsoTensorModules
          (projectiveSpaceOverRing n (CommRingCat.of k))
          (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (CommRingCat.of k))
            (projectiveTwist n F d) (twistOver n (Spec (CommRingCat.of k)) (-1)))
          (twistOver n (Spec (CommRingCat.of k)) 1)).symm
        inferInstance
    exact shortExact_hyperplaneUnit_of_nonvanishing n (Spec (CommRingCat.of k))
      (projectiveTwist n F d) s hW

end Sequence

end AlgebraicGeometry

end
