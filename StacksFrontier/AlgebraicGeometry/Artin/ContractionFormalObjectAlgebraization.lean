module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFormalObject
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicAlgebraization.FormalObjectAdic

/-!
# Formal objects of a locally Noetherian formal algebraic space algebraize along the reduction

This is the first step of the proof of Stacks 0GI8: for a locally Noetherian formal algebraic
space `W` over `S`, a formal object `(R, w_n)` of `W` gives the ideal `I ⊆ R` of
`Spf R ×_W W_red`, the closed subset `Z = V(I)` of `Spec R` containing the closed point, and an
adic morphism `x̂ : (Spec R)_{/Z} ⟶ W` restricting to `w_n` on every thickening
`Spec(R/𝔪ⁿ⁺¹)`. The ingredients are Stacks 0GHM (the infinitesimal neighbourhoods `W_k` of
`W_red`, `AlgebraicGeometry.FormalSpace.reductionNeighbourhood`) and Stacks 0AQH for the algebraic
spaces `W_k`.

## Main results

* `AlgebraicGeometry.FormalSpace.hasAdicAlgebraizationOfFormalObjects_of_isLocallyNoetherian`.

## References

* [Stacks Project, Tag 0GI8](https://stacks.math.columbia.edu/tag/0GI8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

open Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- **Formal objects of a locally Noetherian formal algebraic space algebraize along the
reduction** (the first step of the proof of Stacks 0GI8). -/
theorem hasAdicAlgebraizationOfFormalObjects_of_isLocallyNoetherian {W : FppfSheaf B S hS}
    (hW : IsLocallyNoetherian B S hS W) : HasAdicAlgebraizationOfFormalObjects W := by
  intro A hA w hw
  obtain ⟨Wred, i, hred⟩ := exists_isReduction_of_isFormalAlgebraicSpace B S hS W hW.1
  exact ⟨formalObjectZeroLocus hred A hA w, isClosed_formalObjectZeroLocus hred A hA w,
    hasImageIn_formalObjectZeroLocus hred A hA w, formalObjectCompletion hW hred A hA w hw,
    isRepresentableByAlgebraicSpacesULift_formalObjectCompletion hW hred A hA w hw,
    fun n => formalObjectCompletion_thickeningSection hW hred A hA w hw n⟩

end AlgebraicGeometry.FormalSpace

namespace AlgebraicGeometry.Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (c : ContractionSituation B S hS)

/-- **Stacks 0GI8 reduced to its second step.** In the situation of Stacks 0GH8, compatibility
over complete local bases
(`AlgebraicGeometry.Artin.ContractionSituation.HasCompatibilityOverCompleteLocalBase`) makes every
formal object of Artin's functor `F` effective; the first step, algebraization of formal objects
of `W` along its reduction, holds for every locally Noetherian `W`. -/
theorem hasEffectiveFormalObjects_of_hasCompatibility
    (h₂ : c.HasCompatibilityOverCompleteLocalBase) :
    LocallyNoetherianOver.HasEffectiveFormalObjects B S hS (contractionFunctor c) :=
  c.hasEffectiveFormalObjects_of
    (FormalSpace.hasAdicAlgebraizationOfFormalObjects_of_isLocallyNoetherian
      c.isLocallyNoetherian_W) h₂

end AlgebraicGeometry.Artin.ContractionSituation

end
