module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageCocycle

/-!
# Higher direct images along a limit of morphisms of schemes as a colimit

Let `I` be a directed set, let `(X_i, f_{i'i})` and `(S_i, h_{i'i})` be inverse systems of schemes
with affine transition morphisms, let `g_i : X_i ⟶ S_i` be a morphism of the first system into the
second with every `g_i` quasi-compact and quasi-separated, let `f_i : X ⟶ X_i` be the projections
of a cone over the first system, let `h_i : S ⟶ S_i` be those of a limit cone over the second, let
`g : X ⟶ S` be the limit morphism, and let `𝓕` be an abelian sheaf on the small étale site of `X`.
[Stacks, Tag 0DV2] asserts

`R^p g_* 𝓕 = colim_{i ∈ I} h_i^{-1} R^p g_{i, *}(f_{i, *}𝓕)`.

This file defines the universal-property predicates in which that assertion and its inputs are
stated; the assertion itself is
`Stacks.EtaleCohomology.LimitHigherDirectImage.isColimit_pushforwardStage_of_isLimit`, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PushforwardStageColimit`. Its diagram is
the one of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageOfPushforward`: the
objects are `h_i^{-1} R^p g_{i, *}(f_{i, *}𝓕)`, the maps are the inverse images along the
projections of the transition maps `ψ_{i'i}` of [Stacks, Tag 0EYM], read through the comparison
`Stacks.EtaleCohomology.conePullbackComp` of inverse images along `h_i = h_{i'} ≫ h_{i'i}`, and
the legs of the cocone at `R^p g_* 𝓕` are the maps `ψ_i` of the same source.

Colimits of abelian sheaves on the small étale site of `S` are not known in this development to be
computed by a functor on `I`: the diagram's objects and maps satisfy the cocycle condition, but
the identity law — which is what would turn them into a functor and hence the legs into a
`CategoryTheory.Limits.Cocone` — is carried only at the level of the underlying sheaves, by
`Stacks.EtaleCohomology.directImageSystem_map_id`, and not at the level of their higher direct
images. The colimit is therefore expressed by its universal property, as in
`CategoryTheory.Sites.InverseSystem.InverseSystemOfSites.isColimit_pullback_pushforward_of_colimit`:
every family of maps out of the objects of the diagram that is compatible with its maps factors
uniquely through the legs. Nothing is weakened by this: the factorisation is required to be
through the canonical legs, and it is required to be unique.

## Main definitions

* `Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation` — the assertion
  `𝓖 = colim_i f_i^{-1}F_i` for a system of sheaves `F` on `(X_i, f_{i'i})` and a family
  `ι_i : f_i^{-1}F_i ⟶ 𝓖`, in universal-property form.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.IsHigherDirectImageColimit` — the assertion
  `R^p g_* 𝓖 = colim_i h_i^{-1} R^p g_{i, *}F_i` of [Stacks, Tag 0EYM], in universal-property
  form.

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

attribute [local instance] HasDerivedCategory.standard

variable {I : Type v} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS) (p : ℕ)
  (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS)
  (𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})

/-! ### The two colimit assertions, in universal-property form -/

/-- **The colimit presentation `𝓕 = colim_i f_i^{-1}F_i` of a sheaf on the limit**, for a system
of sheaves `F` on `(X_i, f_{i'i})` and a family `ι_i : f_i^{-1}F_i ⟶ 𝓕`: every family of maps out
of the inverse images `f_i^{-1}F_i` that is compatible with the transition maps of `F` factors
uniquely through the `ι_i`. This is the hypothesis `𝓕 = colim f_i^{-1}ℱ_i` of
[Stacks, Tag 0EYM] and the colimit half of the conclusion of [Stacks, Tag 0EYN]. -/
def IsPullbackColimitPresentation (F : EtaleSheafSystem DX Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕) : Prop :=
  ∀ (𝒢 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
      (τ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝒢),
    (∀ {i j : Iᵒᵖ} (a : i ⟶ j),
        (conePullbackComp cX a).inv.app (F.obj j) ≫
          (smallEtalePullbackAb (cX.π.app i)).map (F.map a) ≫ τ i = τ j) →
      ∃! χ : 𝓕 ⟶ 𝒢, ∀ i : Iᵒᵖ, ι i ≫ χ = τ i

/-- **The colimit assertion `R^p g_* 𝓕 = colim_i h_i^{-1} R^p g_{i, *}F_i` of
[Stacks, Tag 0EYM].** The diagram is the one of the maps `ψ_{i'i}` of
`Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap`, pulled back along the projections
through the comparison `Stacks.EtaleCohomology.conePullbackComp` of inverse images along
`h_i = h_{i'} ≫ h_{i'i}`, and its cocone at `R^p g_* 𝓕` is the one of the maps `ψ_i` of
`Stacks.EtaleCohomology.LimitHigherDirectImage.projectionMap`: every family of maps out of the
objects of the diagram that is compatible with its maps factors uniquely through the `ψ_i`. -/
def IsHigherDirectImageColimit (F : EtaleSheafSystem DX Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕) : Prop :=
  ∀ (𝒢 : Sheaf (smallEtaleTopology cS.pt) Ab.{u + 1})
      (τ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cS.π.app i)).obj
        (((smallEtalePushforwardAb (γ.app i)).rightDerived p).obj (F.obj i)) ⟶ 𝒢),
    (∀ {i j : Iᵒᵖ} (a : i ⟶ j),
        (conePullbackComp cS a).inv.app
            (((smallEtalePushforwardAb (γ.app j)).rightDerived p).obj (F.obj j)) ≫
          (smallEtalePullbackAb (cS.π.app i)).map (transitionMap γ p F a) ≫ τ i = τ j) →
      ∃! χ : ((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived p).obj 𝓕 ⟶ 𝒢,
        ∀ i : Iᵒᵖ, projectionMap γ cX cS hcS p 𝓕 F ι i ≫ χ = τ i

end Stacks.EtaleCohomology.LimitHigherDirectImage

end
