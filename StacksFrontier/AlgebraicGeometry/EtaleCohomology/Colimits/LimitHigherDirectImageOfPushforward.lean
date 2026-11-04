module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImage

/-!
# Higher direct images along a limit, for the direct images of a sheaf on the limit

Let `(X_i, f_{i'i})` and `(S_i, h_{i'i})` be inverse systems of schemes and let `g_i : X_i ⟶ S_i`
be a morphism of the first system into the second. Let `f_i : X ⟶ X_i` be the projections of a
cone over the first system, let `h_i : S ⟶ S_i` be those of a limit cone over the second, and let
`g : X ⟶ S` be the limit morphism. Let `𝓕` be an abelian sheaf on the small étale site of `X`.

Stacks 0DV2 asserts `R^p g_* 𝓕 = colim_{i ∈ I} h_i^{-1} R^p g_{i, *}(f_{i, *}𝓕)`. This file
constructs the objects, the transition maps and the cocone maps of that diagram, the maps of
Stacks 0EYM at the system of direct images `f_{i, *}𝓕`, and proves that the counits
`f_i^{-1}f_{i, *}𝓕 ⟶ 𝓕` form a cocone on that system.

## Main definitions

* `Stacks.EtaleCohomology.coneDirectImageCompAb` — `Stacks.EtaleCohomology.coneDirectImageComp`
  for abelian coefficients, in the vocabulary of `Stacks.EtaleCohomology.smallEtalePushforwardAb`.
* `Stacks.EtaleCohomology.conePullbackComp` — the comparison `f_{i'}^{-1} ∘ f_{i'i}^{-1} ≅
  f_i^{-1}` of inverse images along a factorisation of a projection, adjoint to
  `Stacks.EtaleCohomology.coneDirectImageCompAb`.
* `Stacks.EtaleCohomology.coneDirectImageCounit` — the map `ι_i : f_i^{-1}f_{i, *}𝓕 ⟶ 𝓕`, the
  counit of the inverse-image/direct-image adjunction along the projection `f_i`.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.pushforwardStage`,
  `Stacks.EtaleCohomology.LimitHigherDirectImage.pushforwardStageTransition` and
  `Stacks.EtaleCohomology.LimitHigherDirectImage.pushforwardStageLeg` — the objects
  `h_i^{-1}R^p g_{i, *}(f_{i, *}𝓕)`, the transition maps `ψ_{i'i}` and the cocone maps `ψ_i` of
  the diagram of Stacks 0DV2: the maps of Stacks 0EYM at the system of direct images.

## Main results

* `Stacks.EtaleCohomology.coneDirectImageCounit_cocone` — the counits form a cocone on the
  system of direct images: for `i' ≥ i` the triangle `ι_{i'} ∘ f_{i'}^{-1}φ_{i'i} = ι_i`
  commutes, through the comparison `conePullbackComp`.

## References

* [Stacks Project, Tag 0DV2](https://stacks.math.columbia.edu/tag/0DV2)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 0EXJ](https://stacks.math.columbia.edu/tag/0EXJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

variable {I : Type v} [Preorder I] {DX : Iᵒᵖ ⥤ Scheme.{u}} (cX : Cone DX)
  (𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})

/-- The identification `f_{i, *}𝓕 ≅ f_{i'i, *}f_{i', *}𝓕` of
`Stacks.EtaleCohomology.coneDirectImageComp` for abelian coefficients, with the direct images
written as `Stacks.EtaleCohomology.smallEtalePushforwardAb`. -/
def coneDirectImageCompAb {i j : Iᵒᵖ} (a : i ⟶ j) :
    smallEtalePushforwardAb (cX.π.app i) ⋙ systemPushforward DX Ab.{u + 1} a ≅
      smallEtalePushforwardAb (cX.π.app j) :=
  coneDirectImageComp DX Ab.{u + 1} cX a

/-- The comparison `f_{i'}^{-1} ∘ f_{i'i}^{-1} ≅ f_i^{-1}` of inverse images of abelian sheaves
along the factorisation `f_i = f_{i'} ≫ f_{i'i}` of a projection of a cone: the left adjoint of
`Stacks.EtaleCohomology.coneDirectImageCompAb`. -/
def conePullbackComp {i j : Iᵒᵖ} (a : i ⟶ j) :
    systemPullback DX Ab.{u + 1} a ⋙ smallEtalePullbackAb (cX.π.app i) ≅
      smallEtalePullbackAb (cX.π.app j) :=
  Adjunction.leftAdjointCompIso (systemAdjunction DX Ab.{u + 1} a)
    (smallEtaleAdjunctionAb (cX.π.app i)) (smallEtaleAdjunctionAb (cX.π.app j))
    (coneDirectImageCompAb cX a)

/-- The map `ι_i : f_i^{-1}f_{i, *}𝓕 ⟶ 𝓕` presenting `𝓕` over the system of its direct images:
the counit of the inverse-image/direct-image adjunction along the projection `f_i : X ⟶ X_i`. -/
def coneDirectImageCounit (i : Iᵒᵖ) :
    (smallEtalePullbackAb (cX.π.app i)).obj
        ((directImageSystem DX Ab.{u + 1} cX 𝓕).obj i) ⟶ 𝓕 :=
  (smallEtaleAdjunctionAb (cX.π.app i)).counit.app 𝓕

/-- The counits form a cocone on the system of direct images: for `i' ≥ i` the triangle
`ι_{i'} ∘ f_{i'}^{-1}φ_{i'i} = ι_i` commutes, where `φ_{i'i}` is the transition map of
`Stacks.EtaleCohomology.directImageSystem` and the two inverse images are compared by
`Stacks.EtaleCohomology.conePullbackComp`. -/
theorem coneDirectImageCounit_cocone {i j : Iᵒᵖ} (a : i ⟶ j) :
    (conePullbackComp cX a).inv.app ((directImageSystem DX Ab.{u + 1} cX 𝓕).obj j) ≫
        (smallEtalePullbackAb (cX.π.app i)).map
            ((directImageSystem DX Ab.{u + 1} cX 𝓕).map a) ≫
          coneDirectImageCounit cX 𝓕 i =
      coneDirectImageCounit cX 𝓕 j := by
  have h := leftAdjointCompIso_inv_homEquiv_symm (systemAdjunction DX Ab.{u + 1} a)
    (smallEtaleAdjunctionAb (cX.π.app i)) (smallEtaleAdjunctionAb (cX.π.app j))
    (coneDirectImageCompAb cX a) ((coneDirectImageCompAb cX a).inv.app 𝓕) (𝟙 _)
  simp only [Adjunction.homEquiv_symm_id] at h
  refine h.trans (.trans ?_ ((smallEtaleAdjunctionAb (cX.π.app j)).homEquiv_symm_id 𝓕))
  simp

namespace LimitHigherDirectImage

variable {DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS) (cS : Cone DS) (hcS : IsLimit cS) (p : ℕ)

/-- The object `h_i^{-1} R^p g_{i, *}(f_{i, *}𝓕)` of the diagram of Stacks 0DV2:
`Stacks.EtaleCohomology.LimitBaseChange.sourceTerm` at the system of direct images of `𝓕` along
the projections. -/
abbrev pushforwardStage (i : Iᵒᵖ) : Sheaf (smallEtaleTopology cS.pt) Ab.{u + 1} :=
  LimitBaseChange.sourceTerm (g := γ) (cS := cS)
    (F := directImageSystem DX Ab.{u + 1} cX 𝓕) (q := p) i

/-- The transition map `ψ_{i'i} : h_{i'i}^{-1} R^p g_{i, *}(f_{i, *}𝓕) ⟶
R^p g_{i', *}(f_{i', *}𝓕)` of Stacks 0DV2: the map of Stacks 0EYM at the system of direct images
of `𝓕` along the projections. -/
def pushforwardStageTransition {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtalePullbackAb (DS.map a)).obj
        (((smallEtalePushforwardAb (γ.app j)).rightDerived p).obj
          ((directImageSystem DX Ab.{u + 1} cX 𝓕).obj j)) ⟶
      ((smallEtalePushforwardAb (γ.app i)).rightDerived p).obj
        ((directImageSystem DX Ab.{u + 1} cX 𝓕).obj i) :=
  transitionMap γ p (directImageSystem DX Ab.{u + 1} cX 𝓕) a

/-- The cocone map `ψ_i : h_i^{-1} R^p g_{i, *}(f_{i, *}𝓕) ⟶ R^p g_* 𝓕` of Stacks 0DV2: the map
of Stacks 0EYM at the system of direct images of `𝓕` along the projections, with the counits
`Stacks.EtaleCohomology.coneDirectImageCounit` as the maps presenting `𝓕`. -/
def pushforwardStageLeg (i : Iᵒᵖ) :
    pushforwardStage cX 𝓕 γ cS p i ⟶
      ((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived p).obj 𝓕 :=
  projectionMap γ cX cS hcS p 𝓕 (directImageSystem DX Ab.{u + 1} cX 𝓕)
    (coneDirectImageCounit cX 𝓕) i

end LimitHigherDirectImage

end Stacks.EtaleCohomology

end
