module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpace
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaSection

/-!
# The map `θ` of Stacks 0D2Z on a scheme point of `U(ψ)`

Let `f : X ⟶ Y` be a morphism towards the algebraic space `Y` of Situation 0849, with `ℒ` and
`ψ : f^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}` given by their restrictions to the scheme points of `X`
(`AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction`).  A scheme point
`w : W ⟶ X` lies in the open subspace `U(ψ)` exactly when the open `U(w^*ψ)` of [Stacks, Tag 01O8]
is all of `W`; then the value of `r_{ℒ,ψ}` at `w` is defined through the morphism
`W ⟶ U(w^*ψ) ⟶ Proj_W((f ∘ w)^*𝒜)` of [Stacks, Tag 01O9], whose first arrow is the inverse of the
inclusion `U(w^*ψ) ⊆ W`.

This file reads `θ_w` of [Stacks, Tag 01O9] on `W` itself, along that inverse
(`…GradedPowerMap.thetaOnSection`): **the restriction of `θ` to the scheme point `w`** of
`U(ψ)`, a map `r_w^*𝒪(d) ⟶ (w^*ℒ)^{⊗ d}` of `𝒪_W`-modules for the morphism
`r_w : W ⟶ Proj_W((f ∘ w)^*𝒜)` attached to `r_{ℒ,ψ} ∘ w`.

## Main definitions

* `…InvertibleTwistingRestriction.chartLift`: `W ⟶ U(w^*ψ)`, the inverse of the inclusion.
* `…InvertibleTwistingRestriction.chartMorphism`: `r_w = (W ⟶ U(w^*ψ) ⟶ Proj_W((f ∘ w)^*𝒜))`.
* `…InvertibleTwistingRestriction.chartTheta`: **`θ` at the scheme point `w`**, in degree `d`.

## Main results

* `…InvertibleTwistingRestriction.chartLift_ι`: `W ⟶ U(w^*ψ) ⊆ W` is the identity.
* `…InvertibleTwistingRestriction.pointEquivProjOver_point`: the value of `r_{ℒ,ψ}` at `w` is the
  `W`-point of `Proj_Y(𝒜)` attached to `r_w`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

universe u m

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable {s : RelativeProjSituation.{u, m}}
  {X : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} {f : X ⟶ s.space.1}
  (R : s.InvertibleTwistingRestriction f)
  {W : BigFppfOver s.site s.base s.containsBase} (w : yoneda.obj W ⟶ X) (hw : R.locusOpen W w = ⊤)

/-- **`W ⟶ U(w^*ψ)`, the inverse of the inclusion `U(w^*ψ) ⊆ W`**, for a scheme point `w` of
`U(ψ)`: the morphism through which the value of `r_{ℒ,ψ}` at `w` is defined. -/
abbrev chartLift :
    (BigFppfOver.toScheme s.site s.base s.containsBase).obj W ⟶
      (toGradedPowerMap (R.twisting W w)).coveringOpen.toScheme :=
  s.relativeProjPoints.locusLift (R.twisting W w) (𝟙 W)
    (R.mem_subspaceOfOpens_of_locusOpen (𝟙 W) w ((R.locusOpen_id_comp w).trans hw))

/-- `W ⟶ U(w^*ψ) ⊆ W` is the identity. -/
theorem chartLift_ι :
    R.chartLift w hw ≫ (toGradedPowerMap (R.twisting W w)).coveringOpen.ι = 𝟙 _ :=
  (s.relativeProjPoints.locusLift_ι _ _ _).trans
    (CategoryTheory.Functor.map_id (BigFppfOver.toScheme s.site s.base s.containsBase) W)

/-- **`r_w : W ⟶ Proj_W((f ∘ w)^*𝒜)`**: the morphism `r_{w^*ψ}` of [Stacks, Tag 01O9] for the
restriction `w^*ψ`, read on `W` through `W ⟶ U(w^*ψ)`. -/
abbrev chartMorphism :
    (BigFppfOver.toScheme s.site s.base s.containsBase).obj W ⟶
      (relativeProj (s.relativeProjPoints.algebra W (w ≫ f))).scheme :=
  R.chartLift w hw ≫
    (toGradedPowerMap (R.twisting W w)).globalMorphism
      (relativeProj (s.relativeProjPoints.algebra W (w ≫ f)))

/-- **The value of `r_{ℒ,ψ}` at a scheme point `w` of `U(ψ)` is the `W`-point of `Proj_Y(𝒜)`
attached to `r_w`** through `W ×_Y Proj_Y(𝒜) = Proj_W((f ∘ w)^*𝒜)` (Stacks 084B). -/
theorem pointEquivProjOver_point :
    (s.relativeProjPoints.pointEquivProjOver W (w ≫ f) (𝟙 W) (R.point w hw)).1 =
      R.chartMorphism w hw :=
  s.relativeProjPoints.pointEquivProjOver_invertiblePoint _ _ _

/-- **`θ` at a scheme point `w : W ⟶ X` of `U(ψ)`** (Stacks 0D2Z), in degree `d`: the map
`r_w^*𝒪(d) ⟶ (w^*ℒ)^{⊗ d}` of `𝒪_W`-modules, which is `θ_{w^*ψ}` of [Stacks, Tag 01O9] on
`U(w^*ψ) = W`, read along `W ⟶ U(w^*ψ)`
(`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap.thetaOnSection`). -/
def chartTheta (d : ℤ) :
    (Scheme.Modules.pullback (R.chartMorphism w hw)).obj
        ((GradedPowerMap.twD (s.relativeProjPoints.algebra W (w ≫ f))).algebra.piece d) ⟶
      tensorPowerModule _ (R.line W w) d :=
  (toGradedPowerMap (R.twisting W w)).thetaOnSection (R.chartLift w hw) (R.chartLift_ι w hw) d

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
