module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationConeBase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The strict henselization of a strictly henselian local scheme

Let `R` be a strictly henselian local ring and `σ` a geometric point of `Spec R` lying over the
closed point. Then the structure morphism `Spec 𝒪^{sh}_{Spec R, σ} ⟶ Spec R` of the strict
henselization is an isomorphism.

## Main results

* `AlgebraicGeometry.isIso_strictHenselizationToBase_of_strictlyHenselian` — the structure
  morphism of the strict henselization of a strictly henselian local scheme at a geometric point
  over the closed point is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- For a strictly henselian local ring `R` and a geometric point `σ` of `Spec R` lying over the
closed point, the structure morphism of the strict henselization of `Spec R` at `σ` is an
isomorphism. -/
@[ega "IV 18.8.8"]
theorem isIso_strictHenselizationToBase_of_strictlyHenselian (B : BigEtaleSite.{u})
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R] (hS : B.Contains (Spec (.of R)))
    (σ : GeometricPoint (Spec (.of R))) (hσ : σ.LiesOver (closedPoint R)) :
    IsIso (strictHenselizationToBase B (Spec (.of R)) hS σ) := by
  obtain ⟨hI⟩ := Stacks.StrictlyHenselian.nonempty_isInitial_finalNeighborhood B R hS σ hσ
  have hleg := (strictHenselizationConeIsLimit B (Spec (.of R)) hS σ).isIso_π_app_of_isInitial
    _ hI
  rw [← strictHenselizationCone_π_comp_hom_eq B (Spec (.of R)) hS σ
    (Stacks.StrictlyHenselian.finalNeighborhood B R hS σ)]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hleg (inferInstanceAs (IsIso (𝟙 (Spec (.of R)))))

end AlgebraicGeometry
