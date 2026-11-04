module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjIso.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.ToSpecZero

import Mathlib.AlgebraicGeometry.Morphisms.Integral
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A proper scheme with an ample invertible module is its own `Proj`

Let `R` be a ring, `P` a proper scheme over `R` and `𝓛` an ample invertible `𝒪_P`-module, and set
`A = Γ_*(P, 𝓛) = ⨁_{m ≥ 0} Γ(P, 𝓛^{⊗ m})`. This file shows that the canonical morphism
`r : P ⟶ Proj A` of [Stacks, Tag 01PZ] is an isomorphism, which is the identification
`P = Proj A` of [Stacks, Tag 0EKI].

## Main results

* `Stacks.SectionRingProjIso.universallyClosed_toSpecΓ`: a scheme universally closed over an
  affine scheme is universally closed over the spectrum of its own global sections.
* `Stacks.SectionRingProjIso.universallyClosed_of_isIntegral_appTop`: a morphism into an affine
  scheme out of such a scheme is universally closed once its global-sections map is integral.
* `Stacks.SectionRingProjIso.isIntegral_appTop_projHomOfIsAmple_toSpecZero`: the degree-zero
  global-sections map `A₀ ⟶ Γ(P, 𝒪_P)` of `r ≫ Proj.toSpecZero` is integral.
* `Stacks.SectionRingProjIso.isIso_projHomOfIsAmple_of_isProper`: `r : P ⟶ Proj A` is an
  isomorphism for `P` proper over `R`.
* `Stacks.SectionRingProjIso.projIsoOfIsProper`: the isomorphism `P ≅ Proj A`.

## References

* [Stacks Project, Tag 0EKI](https://stacks.math.columbia.edu/tag/0EKI)
* [Stacks Project, Tag 0C6J](https://stacks.math.columbia.edu/tag/0C6J)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Ample (IsAmple)
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)

universe u

namespace Stacks.SectionRingProjIso

/-! ### Universal closedness over the spectrum of the global sections -/

/-- For a morphism `f` into an affine scheme, `f` is universally closed iff
`X.toSpecΓ ≫ Spec.map f.appTop` is. -/
private theorem universallyClosed_toSpecΓ_comp_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] :
    UniversallyClosed (X.toSpecΓ ≫ Spec.map f.appTop) ↔ UniversallyClosed f := by
  have := universallyClosed_respectsIso
  rw [← Scheme.toSpecΓ_naturality,
    MorphismProperty.cancel_right_of_respectsIso (P := @UniversallyClosed)]

/-- A scheme universally closed over an affine scheme is universally closed over the spectrum of
its own global sections. -/
theorem universallyClosed_toSpecΓ {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversallyClosed f]
    [IsAffine Y] : UniversallyClosed X.toSpecΓ :=
  have := (universallyClosed_toSpecΓ_comp_iff f).mpr ‹_›
  UniversallyClosed.of_comp_of_isSeparated _ (Spec.map f.appTop)

/-- A morphism into an affine scheme with integral global-sections map is universally closed,
provided the source is universally closed over the spectrum of its global sections. -/
@[ega "II 6.1.10" "affine case", sga "3 V 4.1.1" "partial"]
theorem universallyClosed_of_isIntegral_appTop {X : Scheme.{u}} {T : CommRingCat.{u}}
    (g : X ⟶ Spec T) (hX : UniversallyClosed X.toSpecΓ) (hg : g.appTop.hom.IsIntegral) :
    UniversallyClosed g :=
  have : UniversallyClosed (Spec.map g.appTop) :=
    (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp (IsIntegralHom.SpecMap_iff.mpr hg)).1
  (universallyClosed_toSpecΓ_comp_iff g).mp inferInstance

/-! ### The identification `P = Proj A` -/

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

/-- The global-sections map `A₀ ⟶ Γ(P, 𝒪_P)` of the composite `r ≫ Proj.toSpecZero` of the
canonical morphism `r : P ⟶ Proj A` of [Stacks, Tag 01PZ] with the structure morphism of
`Proj A` is integral. -/
theorem isIntegral_appTop_projHomOfIsAmple_toSpecZero (hL : IsAmple X L) :
    (projHomOfIsAmple L hL ≫
      AlgebraicGeometry.Proj.toSpecZero (grading L)).appTop.hom.IsIntegral := by
  have : IsIso (CommRingCat.ofHom
      (Stacks.SectionRingProjMorphism.ToSpecZero.degZeroRingHom L)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (Stacks.SectionRingProjMorphism.ToSpecZero.bijective_degZeroRingHom L)
  have key : IsIso (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (Stacks.SectionRingProjMorphism.ToSpecZero.degZeroRingHom L))).appTop := by
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]
    infer_instance
  rw [Stacks.SectionRingProjMorphism.ToSpecZero.projHomOfIsAmple_toSpecZero L hL]
  exact RingHom.isIntegral_of_surjective _ ((ConcreteCategory.isIso_iff_bijective _).mp key).2

/-- Let `P` be a proper scheme over a ring `R` and `𝓛` an ample invertible `𝒪_P`-module with
graded section ring `A = Γ_*(P, 𝓛)`. Then the canonical morphism `r : P ⟶ Proj A` of
[Stacks, Tag 01PZ] is an isomorphism. -/
@[stacks 0EKI "the identification P = Proj(A), for P proper over R"]
theorem isIso_projHomOfIsAmple_of_isProper (hL : IsAmple X L) {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) [IsProper f] :
    IsIso (projHomOfIsAmple L hL) :=
  have : UniversallyClosed
      (projHomOfIsAmple L hL ≫ AlgebraicGeometry.Proj.toSpecZero (grading L)) :=
    universallyClosed_of_isIntegral_appTop _ (universallyClosed_toSpecΓ f)
      (isIntegral_appTop_projHomOfIsAmple_toSpecZero L hL)
  isIso_projHomOfIsAmple L hL this

/-- The isomorphism `P ≅ Proj Γ_*(P, 𝓛)` whose underlying morphism is the canonical one of
[Stacks, Tag 01PZ], for `P` proper over `R` and `𝓛` ample. -/
@[stacks 0EKI "the identification P = Proj(A) as an isomorphism P ≅ Proj Γ_*(P, 𝓛), for P proper \
over R"]
noncomputable def projIsoOfIsProper (hL : IsAmple X L) {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) [IsProper f] :
    X ≅ AlgebraicGeometry.Proj (grading L) :=
  haveI := isIso_projHomOfIsAmple_of_isProper L hL f
  asIso (projHomOfIsAmple L hL)

end Monoidal

end Stacks.SectionRingProjIso

end
