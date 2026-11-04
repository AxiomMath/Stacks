module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseTwo
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedTransport

/-!
# The parts of clause (2) of Stacks Tag 01O9 over the affine opens of the base

For an open `W` of `X` on which `ψ` is surjective in degree `k`, and an affine open `V` of the
base, the part `W ∩ f^{-1}(V)` of `W` maps into `f^{-1}(V)`, and the [Stacks, Tag 01NK] datum
that `ψ` induces over `V` pulls back to it.

## Main definitions

* `…RelativeProjInvertibleMorphism.partInclusion`: the inclusion `W ∩ f^{-1}(V) ⟶ f^{-1}(V)`.
* `…RelativeProjInvertibleMorphism.partDatum`: the pullback to `W ∩ f^{-1}(V)` of the datum
  `…GradedPowerMap.affineDatum V` of the graded map attached to `ψ`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : T ⟶ S}
  {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : Twisting f (situationAlgebra A) 1 L) {W : T.Opens}

/-- **The inclusion of the part of `W` over `V` into `f^{-1}(V)`.** -/
def partInclusion (V : S.Opens) :
    ((W.ι ≫ f) ⁻¹ᵁ V).toScheme ⟶ (f ⁻¹ᵁ V).toScheme :=
  W.ι.resLE (f ⁻¹ᵁ V) ((W.ι ≫ f) ⁻¹ᵁ V) le_rfl

/-- Composing `partInclusion V` with the inclusion of `f^{-1}(V)` into `T` gives the inclusion
of `W ∩ f^{-1}(V)` into `W` followed by the inclusion of `W` into `T`. -/
theorem partInclusion_ι (V : S.Opens) :
    partInclusion (W := W) (f := f) V ≫ (f ⁻¹ᵁ V).ι = ((W.ι ≫ f) ⁻¹ᵁ V).ι ≫ W.ι :=
  Scheme.Hom.resLE_comp_ι _ _

/-- **The [Stacks, Tag 01NK] datum induced by `ψ` over `V`, pulled back to the part of `W` over
`V`.** -/
def partDatum (V : S.Opens) :
    GradedSections (A.grading V) ((Scheme.Modules.pullback (partInclusion (W := W) V)).obj
      ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj L)) :=
  GradedSections.pullback (partInclusion (W := W) V) ((toGradedPowerMap ψ).affineDatum V)

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
