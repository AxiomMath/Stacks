module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.ToSpecZero
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Nonvanishing opens of relatively ample sections are affine over the base: Stacks Tag 0EKE

Let `f : X ⟶ S` be a universally closed morphism of schemes, `L` an invertible `𝒪_X`-module that
is ample relative to `f`, and `s` a global section of `L`. Then the nonvanishing open `X_s` of
Stacks Tag 01CY is affine over `S`.

## The route

Affineness of a morphism may be checked over an affine open `V ⊆ S`, and over such a `V` the
hypothesis of relative ampleness says exactly that the restriction of `L` to `f⁻¹V` is ample
(Stacks Tag 01VH is stated in that shape, so Stacks Tag 01VK is not needed). The nonvanishing
open of the restricted section is the preimage of `X_s` (Stacks Tag 0H78), so everything reduces
to the affine base case:

**`S` affine, `f` universally closed, `L` ample, `s ∈ Γ(X, L)` ⟹ `X_s` is an affine open.**

For that case, `Γ_*(X, L)` is the graded section ring of Stacks Tag 01CV and
`r : X ⟶ Proj Γ_*(X, L)` the canonical morphism of Stacks Tag 01PZ. Universal closedness of `f`
over an affine base makes `X ⟶ Spec Γ(X, 𝒪_X)` universally closed, hence `r` an isomorphism
(`Stacks.SectionRingProjMorphism.ToSpecZero.isIso_projHomOfIsAmple`, which is the affine-base
case of Stacks Tag 0C6J). The section `s` is a homogeneous element of degree one, `X_s` is its
preimage under `r` of the chart `D₊(s)` by Stacks Tag 01PZ, and `D₊(s)` is affine by the
construction of `Proj`.

## Main results

* `Stacks.AmpleNonvanishingUniversallyClosed.isAffineOpen_nonvanishingOpen_of_isAmple`: the
  affine base case, `X_s` is an affine open.
* `Stacks.AmpleNonvanishingUniversallyClosed.isAffineHom_nonvanishingOpen`: **Stacks Tag 0EKE.**

## Implementation notes

A global section of `L` is turned into a homogeneous element of degree one of `Γ_*(X, L)` through
the identification `L ^⊗ 1 ≅ L`, which is the left unitor; the nonvanishing locus is unchanged
because an isomorphism of modules carries nonvanishing loci to nonvanishing loci.

## References

* [Stacks Project, Tag 0EKE](https://stacks.math.columbia.edu/tag/0EKE)
* [Stacks Project, Tag 0C6J](https://stacks.math.columbia.edu/tag/0C6J)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open RingedSpaceModuleAdjunction
open Stacks.GradedSections (powSections)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionProduct (globalSection)
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u

namespace Stacks.AmpleNonvanishingUniversallyClosed

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **`L ^⊗ 1 ≅ L`**, the left unitor: the first tensor power is `𝟙_ ⊗ L`. -/
noncomputable def oneIso : natTensorPow L 1 ≅ L := λ_ L

/-- **The affine base case of Stacks Tag 0EKE.** Let `L` be an ample invertible `𝒪_X`-module and
`s` a global section of `L`. If `X ⟶ Spec Γ(X, 𝒪_X)` is universally closed — which is what a
universally closed morphism to an affine scheme provides — then the nonvanishing open `X_s` is
affine.

The canonical morphism `r : X ⟶ Proj Γ_*(X, L)` of Stacks Tag 01PZ is an isomorphism under that
hypothesis, `X_s` is the preimage under `r` of the chart `D₊(s)` of the degree-one homogeneous
element attached to `s`, and that chart is affine. -/
theorem isAffineOpen_nonvanishingOpen_of_isAmple (hL : Stacks.Ample.IsAmple X L)
    (h : UniversallyClosed X.toSpecΓ) (s : Γ(L, ⊤)) :
    IsAffineOpen (nonvanishingOpen X L s) := by
  have hiso := Stacks.SectionRingProjMorphism.ToSpecZero.isIso_projHomOfIsAmple L hL h
  set a : powSections L 1 :=
    (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (natTensorPow L 1)).symm
      ((oneIso L).inv.app ⊤ s) with ha
  have hgs : globalSection X (natTensorPow L 1) a = (oneIso L).inv.app ⊤ s :=
    (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
      (natTensorPow L 1)).apply_symm_apply _
  have hnv : nvOpen L a = nonvanishingOpen X L s := by
    refine TopologicalSpace.Opens.ext ?_
    show Stacks.Ample.nonvanishingLocus (natTensorPow L 1) (globalSection X _ a) = _
    rw [hgs]
    exact Stacks.Ample.nonvanishingLocus_congr (oneIso L).symm s
  rw [← hnv, ← Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL a
    Nat.one_pos]
  exact (Proj.isAffineOpen_basicOpen (grading L) _
    (Stacks.ExternalGrading.of_mem_summand 1 a) Nat.one_pos).preimage_of_isIso _

/-- **Stacks Tag 0EKE.** Let `f : X ⟶ S` be a universally closed morphism, `L` an invertible
`𝒪_X`-module ample relative to `f`, and `s` a global section of `L`. Then the nonvanishing open
`X_s` of Stacks Tag 01CY is affine over `S`.

Affineness of a morphism is checked over an affine open `V` of `S`. There the restriction of `L`
to `f⁻¹V` is ample, by the very definition of relative ampleness, the restriction of `f` is still
universally closed, and the nonvanishing open of the restricted section is the preimage of `X_s`
by Stacks Tag 0H78; so the affine base case applies and gives `X_s ∩ f⁻¹V` affine. -/
@[stacks 0EKE]
theorem isAffineHom_nonvanishingOpen {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) (s : Γ(L, ⊤)) :
    IsAffineHom ((nonvanishingOpen X L s).ι ≫ f) := by
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun y => ?_
  have hy : y ∈ ⨆ V : S.affineOpens, (V : S.Opens) := by
    rw [iSup_affineOpens_eq_top]; trivial
  obtain ⟨V, hyV⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  refine ⟨V.1, hyV, V.2, ?_⟩
  set U : X.Opens := nonvanishingOpen X L s with hU
  set Y : X.Opens := f ⁻¹ᵁ V.1 with hYdef
  have hVaff : IsAffine V.1.toScheme := V.2
  have huc : UniversallyClosed (Y.toScheme).toSpecΓ :=
    Stacks.SectionRingProjMorphism.ToSpecZero.universallyClosed_toSpecΓ (f ∣_ V.1)
  have hcore := isAffineOpen_nonvanishingOpen_of_isAmple
    ((modulePullback Y.ι.toLRSHom.toShHom).obj L) (hL.2 V.1 V.2) huc
    (Stacks.NonvanishingPullback.pullbackGlobalSection Y.ι L s)
  have hYU : nonvanishingOpen Y.toScheme ((modulePullback Y.ι.toLRSHom.toShHom).obj L)
      (Stacks.NonvanishingPullback.pullbackGlobalSection Y.ι L s) = Y.ι ⁻¹ᵁ U := by
    refine TopologicalSpace.Opens.ext ?_
    show Stacks.Ample.nonvanishingLocus _ _ = _
    rw [← Stacks.NonvanishingPullback.preimage_nonvanishingLocus Y.ι L s]
    rfl
  rw [hYU] at hcore
  have h2 : IsAffineOpen (Y.ι ''ᵁ (Y.ι ⁻¹ᵁ U)) :=
    (Y.ι.isAffineOpen_iff_of_isOpenImmersion).mpr hcore
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at h2
  rw [Scheme.Hom.comp_preimage, ← U.ι.isAffineOpen_iff_of_isOpenImmersion,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
  exact h2

end Monoidal

end Stacks.AmpleNonvanishingUniversallyClosed

end
