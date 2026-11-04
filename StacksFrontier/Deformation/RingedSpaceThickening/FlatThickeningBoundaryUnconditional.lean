module

public import StacksFrontier.Deformation.RingedSpaceThickening.FlatThickeningBoundaryLifts
import StacksCore.Tactic.StacksAttribute

/-!
# The boundary of the difference of two flat lifts

In Situation **Stacks 08VS** the modules `π^* ℱ` and `h^* ℱ'₂` are `𝒪'₁`-modules flat over `S'₁`
restricting to `ℱ` on `X`; their difference (**Stacks 08VR**) is an element `θ` of
`Ext¹_{𝒪_X}(ℱ, f^* 𝒥₁ ⊗_{𝒪_X} ℱ)` whose boundary in `Ext²_{𝒪_X}(ℱ, f^* 𝒥₃ ⊗_{𝒪_X} ℱ)` is the
obstruction (**Stacks 08VR**) to lifting `ℱ` to an `𝒪'₃`-module flat over `S'₃`.

## Main results

* `boundary_difference_trivialLift_pulledLift_eq_flatDeformationObstruction`: under the
  hypotheses of Situation 08VS alone, the boundary of the difference of `π^* ℱ` and `h^* ℱ'₂` is
  the obstruction to lifting `ℱ` to an `𝒪'₃`-module flat over `S'₃`.

## References

* [Stacks Project, Tag 08VT](https://stacks.math.columbia.edu/tag/08VT)
* [Stacks Project, Tag 08VS](https://stacks.math.columbia.edu/tag/08VS)
* [Stacks Project, Tag 08VR](https://stacks.math.columbia.edu/tag/08VR)
* [Stacks Project, Tag 08LF](https://stacks.math.columbia.edu/tag/08LF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace
open AlgebraicGeometry.RingedSpaceThickening.FlatModuleDeformation

universe u w w'

namespace AlgebraicGeometry.RingedSpaceThickening

namespace FlatShortExactThickeningDiagram

variable (D : FlatShortExactThickeningDiagram.{u})

/-- The comparison map `f^* 𝒥₁ ⟶ ℐ₁` of the first column is an isomorphism. -/
theorem isIso_baseToSourceIdeal₁ : IsIso D.morphism₁.baseToSourceIdeal :=
  isIso_baseToSourceIdeal_of_isFlat D.morphism₁ D.isStrict₁ D.flat₁

/-- The comparison map `f^* 𝒥₂ ⟶ ℐ₂` of the second column is an isomorphism. -/
theorem isIso_baseToSourceIdeal₂ : IsIso D.morphism₂.baseToSourceIdeal :=
  isIso_baseToSourceIdeal_of_isFlat D.morphism₂ D.isStrict₂ D.flat₂

/-- The comparison map `f^* 𝒥₃ ⟶ ℐ₃` of the third column is an isomorphism. -/
theorem isIso_baseToSourceIdeal₃ : IsIso D.morphism₃.baseToSourceIdeal :=
  isIso_baseToSourceIdeal_of_isFlat D.morphism₃ D.isStrict₃ D.flat₃

attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
/-- The identifications `ℐ₃ ⊗ ℱ ≅ f^* 𝒥₃ ⊗ ℱ` and `ℐ₂ ⊗ ℱ ≅ f^* 𝒥₂ ⊗ ℱ` intertwine the map
induced by `ℐ₃ ⟶ ℐ₂` with the map induced by `f^* 𝒥₃ ⟶ f^* 𝒥₂`. -/
theorem baseIdealTensorIso_transition₃₂ :
    (baseIdealTensorIso D.morphism₃ D.isIso_baseToSourceIdeal₃ D.restriction).inv ≫
        D.baseTransition₃₂ =
      D.idealTensorTransition₃₂ ≫
        (baseIdealTensorIso D.morphism₂ D.isIso_baseToSourceIdeal₂ D.restriction).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  change D.baseTransition₃₂ ≫ baseIdealTensorComparison D.morphism₂ D.restriction =
    baseIdealTensorComparison D.morphism₃ D.restriction ≫ D.idealTensorTransition₃₂
  unfold baseIdealTensorComparison idealTensorTransition₃₂
  rw [show D.baseTransition₃₂ = _ from D.pullbackTensorFunctor_map_eq _]
  erw [← D.tensor_map_comp_id, ← D.tensor_map_comp_id, D.baseToSourceIdeal_transition₃₂]

attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
/-- The identifications `ℐ₂ ⊗ ℱ ≅ f^* 𝒥₂ ⊗ ℱ` and `ℐ₁ ⊗ ℱ ≅ f^* 𝒥₁ ⊗ ℱ` intertwine the map
induced by `ℐ₂ ⟶ ℐ₁` with the map induced by `f^* 𝒥₂ ⟶ f^* 𝒥₁`. -/
theorem baseIdealTensorIso_transition₂₁ :
    (baseIdealTensorIso D.morphism₂ D.isIso_baseToSourceIdeal₂ D.restriction).inv ≫
        D.baseTransition₂₁ =
      D.idealTensorTransition₂₁ ≫
        (baseIdealTensorIso D.morphism₁ D.isIso_baseToSourceIdeal₁ D.restriction).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  change D.baseTransition₂₁ ≫ baseIdealTensorComparison D.morphism₁ D.restriction =
    baseIdealTensorComparison D.morphism₂ D.restriction ≫ D.idealTensorTransition₂₁
  unfold baseIdealTensorComparison idealTensorTransition₂₁
  rw [show D.baseTransition₂₁ = _ from D.pullbackTensorFunctor_map_eq _]
  erw [← D.tensor_map_comp_id, ← D.tensor_map_comp_id, D.baseToSourceIdeal_transition₂₁]

/-- In Situation **Stacks 08VS** — a commutative diagram of short exact sequences of first order
thickenings `X'₁ ⟶ X'₂ ⟶ X'₃` of `X` over `S'₁ ⟶ S'₂ ⟶ S'₃` of `S`, with every
`(f, f'ᵢ)` strict and every `f'ᵢ` flat, and an `𝒪'₂`-module `ℱ'₂` flat over `S'₂` with
`ℱ = ℱ'₂|_X` — let `π : X'₁ ⟶ X` be the canonical splitting of **Stacks 08LE**.
Then `π^* ℱ` and `h^* ℱ'₂` are `𝒪'₁`-modules flat over `S'₁` (the first two conjuncts); they
restrict to `ℱ` on `X` through `i₁^* π^* ℱ ≅ (i₁ ≫ π)^* ℱ = ℱ` and
`i₁^* h^* ℱ'₂ ≅ (i₁ ≫ h)^* ℱ'₂ = ℱ`, which makes them the flat lifts `trivialLift` and
`pulledLift`. Their difference `θ ∈ Ext¹_{𝒪_X}(ℱ, f^* 𝒥₁ ⊗_{𝒪_X} ℱ)`, the difference of
**Stacks 08VR** (2) of the two isomorphism classes, has for boundary along
`0 ⟶ f^* 𝒥₃ ⊗ ℱ ⟶ f^* 𝒥₂ ⊗ ℱ ⟶ f^* 𝒥₁ ⊗ ℱ ⟶ 0` — the sequence induced by the lower row, short
exact by `baseTransition_shortExact` — the obstruction of **Stacks 08VR** (1) to lifting `ℱ` to an
`𝒪'₃`-module flat over `S'₃`.

The difference is taken in the order `(h^* ℱ'₂, π^* ℱ)`. -/
@[stacks 08VT]
theorem boundary_difference_trivialLift_pulledLift_eq_flatDeformationObstruction
    [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.upper.X))]
    [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.upper.X₁))]
    [HasDerivedCategory.{w'} (SheafOfModules.{u} (structureSheafRing D.upper.X))] :
    AlgebraicGeometry.IsFlatOver D.f₁
        ((modulePullback D.trivialization.retraction).obj D.restriction) ∧
      AlgebraicGeometry.IsFlatOver D.f₁ ((modulePullback D.upper.f₁₂).obj D.module₂) ∧
      (flatLiftClassDifferenceBase D.morphism₁ D.upper.firstOrder₁ D.isStrict₁
          D.isIso_baseToSourceIdeal₁ D.restriction
          (Quotient.mk (flatLiftSetoid D.morphism₁ D.restriction) D.pulledLift)
          (Quotient.mk (flatLiftSetoid D.morphism₁ D.restriction) D.trivialLift)).comp
          D.baseTransition_shortExact.extClass (by decide) =
        flatDeformationObstruction D.morphism₃ D.upper.firstOrder₃ D.isIso_baseToSourceIdeal₃
          D.restriction := by
  refine ⟨D.isFlatOver_trivialModule, D.isFlatOver_pulledModule, ?_⟩
  have hb : IsIso D.upper.f₁₂.hom.base := isIso_base_of_thickeningMap D.upper.i₁ D.upper.i₂
    D.upper.f₁₂ D.upper.comm₁₂ D.upper.firstOrder₁.1.1 D.upper.firstOrder₂.1.1
  have hrestrict := firstOrderExtensionAction_restrictedExtension D.upper.i₂ D.upper.i₃
    D.upper.f₂₃ D.upper.comm₂₃ D.upper.firstOrder₂ D.upper.firstOrder₃ D.restriction
    (idealTensor D.morphism₂ D.restriction)
    (D.liftOfModule₂.kernelExtension D.upper.firstOrder₂ D.isStrict₂)
    (isIso_base_of_thickeningMap D.upper.i₂ D.upper.i₃ D.upper.f₂₃ D.upper.comm₂₃
      D.upper.firstOrder₂.1.1 D.upper.firstOrder₃.1.1)
  rw [FlatLift.kernelExtension_action D.upper.firstOrder₂ D.isStrict₂ D.liftOfModule₂] at hrestrict
  exact boundary_flatLiftClassDifferenceBase_eq_flatDeformationObstruction D
    D.isIso_baseToSourceIdeal₁ D.isIso_baseToSourceIdeal₂ D.isIso_baseToSourceIdeal₃
    D.baseTransition₃₂ D.baseTransition₂₁ D.baseTransition_comp D.baseTransition_shortExact
    D.baseIdealTensorIso_transition₃₂ D.baseIdealTensorIso_transition₂₁
    D.trivialLift D.pulledLift D.underlyingExtensionClass_trivialLift D.pushedExtension
    (PushedExtension.isPushout D.upper.i₁ D.upper.i₂ D.upper.f₁₂ D.upper.comm₁₂ hb
      D.restriction _ _ _ D.pushedExtension) (hrestrict.trans (Category.comp_id _))

end FlatShortExactThickeningDiagram

end AlgebraicGeometry.RingedSpaceThickening
