module

public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.ProjComparison
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleProjOpenImmersion
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic

/-!
# Transport of the Serre twist along `Proj B ≅ Proj_{Spec R}(B̃)`

The inverse image of `𝒪_{Proj B}(n)` along the inverse of `projComparison` is the `n`-th Serre
twist of `Proj_{Spec R}(B̃)`; invertibility and ampleness of `𝒪(1)` travel along it.

## Main definitions

* `Stacks.PolarizedAlgebraization.twistComparisonInv`.

## Main results

* `Stacks.PolarizedAlgebraization.isInvertibleModule_relativeTwist_one`.
* `Stacks.PolarizedAlgebraization.isAmple_relativeTwist_one`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.Tag07ZGTwist
open Stacks.Ample (IsAmple IsInvertibleModule)
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.PolarizedAlgebraization

variable {R : CommRingCat.{u}} {B : Type u} [CommRing B] [Algebra R B]
  (𝒢 : ℕ → Submodule R B) [_root_.GradedAlgebra 𝒢]

/-- **The `n`-th twist of `Proj_{Spec R}(B̃)` is the inverse image of `𝒪_{Proj B}(n)`.** -/
def twistComparisonInv (n : ℤ) :
    (Scheme.Modules.pullback (inv (projComparison 𝒢))).obj (twistingSheaf 𝒢 n) ≅
      (twistAlgebra (specSheafGradedAlgebra 𝒢)).piece n :=
  (Scheme.Modules.pullback (inv (projComparison 𝒢))).mapIso (twistComparison 𝒢 n).symm ≪≫
    (Scheme.Modules.pullbackComp (inv (projComparison 𝒢)) (projComparison 𝒢)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id (projComparison 𝒢))).app _ ≪≫
    (Scheme.Modules.pullbackId _).app _

/-- The inverse image of `𝒪_{Proj B}(1)` along `inv projComparison` is invertible. -/
private theorem isInvertibleModule_pullback_inv_projComparison_twist_one
    [IsInvertibleModule (AlgebraicGeometry.Proj 𝒢) (twistingSheaf 𝒢 1)] :
    IsInvertibleModule (relativeProj (specSheafGradedAlgebra 𝒢)).scheme
      ((Scheme.Modules.pullback (inv (projComparison 𝒢))).obj (twistingSheaf 𝒢 1)) :=
  Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _

/-- **`𝒪(1)` of `Proj_{Spec R}(B̃)` is invertible** when `𝒪(1)` of `Proj B` is. -/
theorem isInvertibleModule_relativeTwist_one
    [IsInvertibleModule (AlgebraicGeometry.Proj 𝒢) (twistingSheaf 𝒢 1)] :
    IsInvertibleModule (relativeProj (specSheafGradedAlgebra 𝒢)).scheme
      ((twistAlgebra (specSheafGradedAlgebra 𝒢)).piece 1) := by
  have := isInvertibleModule_pullback_inv_projComparison_twist_one 𝒢
  exact Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
    (twistComparisonInv 𝒢 1)

/-- **`𝒪(1)` of `Proj_{Spec R}(B̃)` is ample** when `𝒪(1)` of `Proj B` is. -/
theorem isAmple_relativeTwist_one
    [IsInvertibleModule (AlgebraicGeometry.Proj 𝒢) (twistingSheaf 𝒢 1)]
    (h : IsAmple (AlgebraicGeometry.Proj 𝒢) (twistingSheaf 𝒢 1)) :
    haveI := isInvertibleModule_relativeTwist_one 𝒢
    IsAmple (relativeProj (specSheafGradedAlgebra 𝒢)).scheme
      ((twistAlgebra (specSheafGradedAlgebra 𝒢)).piece 1) := by
  have := isInvertibleModule_relativeTwist_one 𝒢
  have := isInvertibleModule_pullback_inv_projComparison_twist_one 𝒢
  have h₁ := Stacks.AmplePullback.isAmple_modulePullback_of_isClosedImmersion
    (inv (projComparison 𝒢)) (twistingSheaf 𝒢 1) h
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ (twistComparisonInv 𝒢 1)).mp h₁

end Stacks.PolarizedAlgebraization

end
