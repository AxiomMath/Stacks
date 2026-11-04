module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemColimitPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageColimit
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageColimitTheorem

/-!
# Higher direct images along a limit as a colimit of the system of direct images

Let `I` be a directed set, let `(X_i, f_{i'i})` and `(S_i, h_{i'i})` be inverse systems of schemes
with affine transition morphisms, let `g_i : X_i ⟶ S_i` be a morphism of the first system into the
second with every `g_i` quasi-compact and quasi-separated, let `f_i : X ⟶ X_i` and
`h_i : S ⟶ S_i` be the projections of limit cones over the two systems, let `g : X ⟶ S` be the
limit morphism, and let `𝓕` be an abelian sheaf on the small étale site of `X`.
[Stacks, Tag 0DV2] asserts

`R^p g_* 𝓕 = colim_{i ∈ I} h_i^{-1} R^p g_{i, *}(f_{i, *}𝓕)`.

The proof is the source's: it is the combination of [Stacks, Tag 0EYM],
`Stacks.EtaleCohomology.LimitHigherDirectImage.isHigherDirectImageColimit`, with
[Stacks, Tag 0EYN], whose cocone half is `Stacks.EtaleCohomology.coneDirectImageCounit_cocone`
and whose colimit half is `Stacks.EtaleCohomology.isPullbackColimitPresentation_directImageSystem`.

The colimit assertions are stated with the universal-property predicates
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation` and
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsHigherDirectImageColimit`.

## Main results

* `Stacks.EtaleCohomology.LimitHigherDirectImage.isColimit_pushforwardStage_of_isLimit` —
  [Stacks, Tag 0DV2].

## References

* [Stacks Project, Tag 0DV2](https://stacks.math.columbia.edu/tag/0DV2)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

variable {I : Type u} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS) (p : ℕ)
  (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS)
  (𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})

/-- **Stacks 0DV2.** Let `I` be a directed set, let `(X_i, f_{i'i})` and `(S_i, h_{i'i})` be
inverse systems of schemes with affine transition morphisms, let `g_i : X_i ⟶ S_i` be a morphism
of the first system into the second with every `g_i` quasi-compact and quasi-separated, let
`f_i : X ⟶ X_i` and `h_i : S ⟶ S_i` be the projections of limit cones over the two systems, let
`g : X ⟶ S` be the limit morphism, and let `𝓕` be an abelian sheaf on the small étale site of
`X`. Then

`R^p g_* 𝓕 = colim_{i ∈ I} h_i^{-1} R^p g_{i, *}(f_{i, *}𝓕)`:

the objects `h_i^{-1} R^p g_{i, *}(f_{i, *}𝓕)` with the maps induced by the transition maps
`ψ_{i'i}` of [Stacks, Tag 0EYM] satisfy the cocycle condition, the maps `ψ_i` of the same source
form a cocone on them, and that cocone is a colimit.

The counits present `𝓕 = colim_i f_i^{-1}f_{i, *}𝓕` by the colimit half of [Stacks, Tag 0EYN],
`Stacks.EtaleCohomology.isPullbackColimitPresentation_directImageSystem`; they are compatible with
the transition maps of `Stacks.EtaleCohomology.directImageSystem` by
`Stacks.EtaleCohomology.coneDirectImageCounit_cocone`, and [Stacks, Tag 0EYM],
`Stacks.EtaleCohomology.LimitHigherDirectImage.isHigherDirectImageColimit`, applies. -/
@[stacks 0DV2 "the colimit assertion for the canonical diagram and the canonical cocone, with \
the cocycle condition of the diagram and the cocone identity of its legs"]
theorem isColimit_pushforwardStage_of_isLimit [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
    [∀ i : Iᵒᵖ, QuasiCompact (γ.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (γ.app i)]
    (hcX : IsLimit cX) :
    (∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k),
        (systemPullbackComp DS Ab.{u + 1} a b).inv.app
              (((smallEtalePushforwardAb (γ.app k)).rightDerived p).obj
                ((directImageSystem DX Ab.{u + 1} cX 𝓕).obj k)) ≫
            (systemPullback DS Ab.{u + 1} a).map (pushforwardStageTransition cX 𝓕 γ p b) ≫
              pushforwardStageTransition cX 𝓕 γ p a =
          pushforwardStageTransition cX 𝓕 γ p (a ≫ b)) ∧
      (∀ {i j : Iᵒᵖ} (a : i ⟶ j),
          (conePullbackComp cS a).inv.app
                (((smallEtalePushforwardAb (γ.app j)).rightDerived p).obj
                  ((directImageSystem DX Ab.{u + 1} cX 𝓕).obj j)) ≫
              (smallEtalePullbackAb (cS.π.app i)).map (pushforwardStageTransition cX 𝓕 γ p a) ≫
                pushforwardStageLeg cX 𝓕 γ cS hcS p i =
            pushforwardStageLeg cX 𝓕 γ cS hcS p j) ∧
        IsHigherDirectImageColimit γ p cX cS hcS 𝓕 (directImageSystem DX Ab.{u + 1} cX 𝓕)
          (coneDirectImageCounit cX 𝓕) :=
  ⟨fun a b => pushforwardStageTransition_comp γ p cX 𝓕 a b,
    fun a => pushforwardStageLeg_cocone γ p cX cS hcS 𝓕 a,
    isHigherDirectImageColimit γ hcX hcS p (directImageSystem DX Ab.{u + 1} cX 𝓕) 𝓕
      (coneDirectImageCounit cX 𝓕) (fun a => coneDirectImageCounit_cocone cX 𝓕 a)
      (isPullbackColimitPresentation_directImageSystem 𝓕 hcX)⟩

end Stacks.EtaleCohomology.LimitHigherDirectImage

end
