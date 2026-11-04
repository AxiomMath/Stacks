module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bundle
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeFlat
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projective bundle of a locally free module is smooth

Let `ℰ` be a finite locally free `𝒪_X`-module of constant rank `n + 1`. The projection
`π : 𝐏(ℰ) ⟶ X` of its projective bundle is smooth. Smoothness is local on the target, and over an
open on which `ℰ` is free the projection is that of `𝐏(𝒪^{n+1}) = ℙⁿ`, which is smooth by
Tag 0B2P.

## Main results

* `Stacks.ProjectiveBundle.smooth_toBase`: the projection of the projective bundle of a finite
  locally free module of constant rank is smooth.
* `Stacks.Chow.smooth_bundleProj`: the same for `Stacks.Chow.bundleProj`.

## References

* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
* [Stacks Project, Tag 0B2P](https://stacks.math.columbia.edu/tag/0B2P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.SymGraded

universe u

/-- Smoothness of morphisms of schemes is local on the target. -/
theorem isZariskiLocalAtTarget_smooth :
    IsZariskiLocalAtTarget (@Smooth : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth) (Q := RingHom.Smooth)

namespace Stacks.SymGraded

variable {X : Scheme.{u}} (n : ℕ)

/-- The projection of the projective bundle `𝐏(𝒪_X^{n+1})` is smooth: the bundle is `ℙⁿ_X` over
`X` by Stacks 01OE, and `ℙⁿ_X` is smooth over `X` by Tag 0B2P. -/
instance smooth_freeProjectiveBundleToBase :
    Smooth (freeProjectiveBundle (X := X) n).toBase := by
  rw [← projectiveBundleIsoProjectiveSpace_hom_comp_fst (X := X) n]
  exact inferInstanceAs (Smooth
    ((projectiveBundleIsoProjectiveSpace (X := X) n).hom ≫ (projectiveSpaceOver n X ↘ X)))

end Stacks.SymGraded

namespace Stacks.ProjectiveBundle

variable {X : Scheme.{u}} (E : X.Modules) (hqc : IsQuasicoherentPieces E)

/-- **The projection of the projective bundle of a module finite locally free of constant rank
is smooth.** Smoothness is local on the base, and over an open trivialising the module the
projection is that of `𝐏(𝒪^{n+1}) = ℙⁿ`, which is smooth. -/
@[ega "IV 17.3.9" "special case"]
theorem smooth_toBase (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] :
    Smooth (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase := by
  have := isZariskiLocalAtTarget_smooth.{u}
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun x ↦ ?_
  obtain ⟨U, hxU, Φ, hΦ⟩ := exists_iso_morphismRestrict_free E hqc n x
  refine ⟨U, hxU, ?_⟩
  rw [(Iso.eq_inv_comp Φ).mpr hΦ]
  exact inferInstanceAs (Smooth (Φ.inv ≫ (freeProjectiveBundle (X := U.toScheme) n).toBase))

end Stacks.ProjectiveBundle

namespace Stacks.Chow

variable {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]

/-- **The projection of the projective bundle of a module finite locally free of constant rank
`n + 1` is smooth.** -/
@[ega "IV 17.3.9" "special case"]
theorem smooth_bundleProj :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    Smooth (bundleProj E) :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  Stacks.ProjectiveBundle.smooth_toBase E (bundlePieces E) n

end Stacks.Chow
