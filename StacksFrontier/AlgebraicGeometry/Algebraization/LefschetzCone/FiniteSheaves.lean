module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.ChartSections
public import StacksFrontier.AlgebraicGeometry.ProjCoherentModule.Basic
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.SerreFiniteness
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeCoherentDerivedHom

/-!
# Noetherian section rings and coherent sheaves from finite graded modules

Let `X` be proper over a Noetherian ring `R` with an ample invertible `𝒪_X`-module `L`. By
clause (1) of Stacks 0B5T the section ring `A = Γ_*(X, L)` is a finitely generated `R`-algebra,
hence Noetherian. When the canonical morphism `X ⟶ Proj A` is an open immersion, the sheaf
`M̃|_X` attached to a finite graded `A`-module is then coherent.

## Main results

* `Stacks.LefschetzCone.isNoetherianRing_sectionRing`: `Γ_*(X, L)` is Noetherian.
* `Stacks.LefschetzCone.isCoherent_restrictedTilde`: `M̃|_X` is coherent for `M` finite.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.GradedSections (powSections sectionRing)
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality

universe u

namespace Stacks.LefschetzCone

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

/-- **The section ring of an ample invertible module on a proper scheme over a Noetherian ring is
Noetherian**: it is a finitely generated algebra over the base (Stacks 0B5T (1)). -/
public theorem isNoetherianRing_sectionRing {X : Scheme.{u}} {R : Type u} [CommRing R]
    [IsNoetherianRing R] (fX : X ⟶ Spec (CommRingCat.of R)) [IsProper fX] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) :
    IsNoetherianRing (sectionRing L) := by
  have h := Stacks.AlgebraicGeometry.ProperAmpleCohomology.ringHomFiniteType_sectionRing fX L hL
  let : Algebra R (sectionRing L) :=
    ((Stacks.SectionRingZero.sectionRingZeroHom X L).comp
      (Stacks.AlgebraicGeometry.GradedProperCohomology.specAlgebraRingHom R fX)).toAlgebra
  have : Algebra.FiniteType R (sectionRing L) := h
  exact Algebra.FiniteType.isNoetherianRing R _

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L) [IsOpenImmersion (projHomOfIsAmple L hL)]

/-- **`M̃|_X` is coherent for a finite graded module `M`** over a Noetherian section ring. -/
public theorem isCoherent_restrictedTilde [IsNoetherianRing (sectionRing L)]
    [IsLocallyNoetherian X] (M : GradedModuleCat.{u, u, u} (grading L))
    [Module.Finite (sectionRing L) M.carrier] :
    (restrictedTilde L hL M).IsCoherent :=
  AlgebraicGeometry.isCoherent_restrict_of_isOpenImmersion (projHomOfIsAmple L hL) _
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.isCoherent_associatedModuleSheafFunctor_obj
      (grading L) M)

end Monoidal

end Stacks.LefschetzCone

end
