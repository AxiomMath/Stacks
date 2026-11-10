module

public import StacksFrontier.AlgebraicGeometry.SectionExtensionNoAmple.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.Basic

/-!
# The hypothesis of Stacks Tag 01PW holds for the pullback of an ample module

`Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing` is what replaces ampleness in
`StacksFrontier/AlgebraicGeometry/SectionExtensionNoAmple/Basic.lean`. This file discharges it in
the one case part (1) of [Stacks, Tag 0892] needs, **with no ampleness of the module it is asserted
of**:

> if `M` is an ample invertible module on `S` then `f^* M` satisfies
> `Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing` on `X`, for every `f : X ⟶ S`.

That is the whole point of the hypothesis. Part (1) of Tag 0892 applies Tag 01PW on `X` with
`N = f^* M`, and the ampleness of `f^* M` is part (2), which the source deduces *from* part (1); so
`Stacks.ModuleSectionExtension.exists_tensorSection_of_isAmple` and
`Stacks.SectionExtension.isSectionRatio_of_isAmple`, both of which assume the module ample, are
circular there. The hypothesis proved here is available before part (1) is known, and it needs
nothing of `f` at all: only that the preimages of the affine nonvanishing opens of `S` are the
nonvanishing opens of the pulled-back sections, which is [Stacks, Tag 0H78].

The opens `f⁻¹(S_t)` are in general **not affine**, which is exactly why
`Stacks.SectionExtension.exists_common_degree_affine_cover` — whose cover members are affine
nonvanishing loci — cannot be used and
`Stacks.SectionExtensionNoAmple.exists_common_degree_affine_subcover` is.

## Main results

* `Stacks.SectionExtensionNoAmple.hasPointwiseNonvanishing_of_forall_mem_powNonvanishingOpen`: the
  vocabulary bridge, from honest global sections of the tensor powers of Stacks Tag 01CU to the
  homogeneous elements of the section ring, through
  `Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq`.
* `Stacks.SectionExtensionNoAmple.hasPointwiseNonvanishing_pullbackModule_of_isAmple`: **the
  deliverable.** The pullback of an ample invertible module satisfies the hypothesis.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample Stacks.AmpleTheory Stacks.NonvanishingOpen
open Stacks.AmpleFiniteAvoidance

universe u

namespace Stacks.SectionExtensionNoAmple

section Bridge

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- **The vocabulary bridge for the hypothesis.** It is enough to produce, through every point, an
honest global section of a positive tensor power of `L` in the vocabulary of Stacks Tag 01CU
(`Stacks.Ample.tensorPowModule`, `Stacks.AmpleTheory.powNonvanishingOpen`) rather than a
homogeneous element of the section ring; the passage is
`Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq`, which preserves the nonvanishing
locus. -/
theorem hasPointwiseNonvanishing_of_forall_mem_powNonvanishingOpen
    (h : ∀ x : X, ∃ m : ℕ, 1 ≤ m ∧ ∃ t : Γ(tensorPowModule X L (m : ℤ), ⊤),
      x ∈ powNonvanishingOpen X L m t) :
    HasPointwiseNonvanishing L := by
  intro x
  obtain ⟨m, hm, t, hxt⟩ := h x
  obtain ⟨b, hb⟩ := exists_powSections_nvLocus_eq L m t
  refine ⟨m, b, hm, ?_⟩
  have : (x : X) ∈ nvLocus L b := by
    rw [hb]; exact hxt
  rwa [← coe_nvOpen] at this

end Bridge

section Pullback

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X S : Scheme.{u}} (f : X ⟶ S) (M : S.Modules) [IsInvertibleModule S M]

/-- **The pullback of an ample invertible module has enough sections.** For `M` ample on `S` and
`f : X ⟶ S` arbitrary, every point of `X` lies in the nonvanishing open of a global section of a
positive tensor power of `f^* M`, namely of the pullback of the section through whose nonvanishing
open its image passes.

This is the hypothesis of
`Stacks.SectionExtensionNoAmple.exists_tensorSection_of_hasPointwiseNonvanishing`,
and it holds **without any ampleness of `f^* M`**, which is the circularity that blocks the
library's two ample forms of Stacks Tag 01PW at part (1) of [Stacks, Tag 0892]. The two inputs are
`Stacks.Ample.IsAmple.exists_affine_nonvanishingOpen` for `M` and [Stacks, Tag 0H78] in the form
`Stacks.AmplePullback.powNonvanishingOpen_pullbackPowSection`; the affineness of `S_t` is not used.
-/
theorem hasPointwiseNonvanishing_pullbackModule_of_isAmple (hM : IsAmple S M) :
    HasPointwiseNonvanishing (Stacks.AmpleLocallyClosed.pullbackModule f M) := by
  refine hasPointwiseNonvanishing_of_forall_mem_powNonvanishingOpen _ fun x => ?_
  obtain ⟨m, hm, t, -, hfx⟩ := IsAmple.exists_affine_nonvanishingOpen S M hM (f.base x)
  refine ⟨m, hm, Stacks.NonvanishingPullback.pullbackPowSection f M m t, ?_⟩
  rw [Stacks.AmplePullback.powNonvanishingOpen_pullbackPowSection f M m t]
  exact hfx

end Pullback

end Stacks.SectionExtensionNoAmple

end
