module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableStacksSite

/-!
# The augmentation `j_0` of `C/K` for an arbitrary site (Stacks 0D8B)

Let `(C, J)` be a site in the sense of the Stacks project, given by its topology under
`CategoryTheory.GrothendieckTopology.IsStacksSite J`, and `K` a simplicial object of `SR(C)`.
The module `SimplicialSemiRepresentableStacksSite` builds the simplicial site `n ↦ C/K_n` from
the stable covering families of `J`, the augmentation
`CategoryTheory.SimplicialSemiRepresentable.stableAugmentation` defined by `j_0`, and the
identifications of the morphisms of topoi `a_n` and `a` of Stacks 0D70 with those of `j_n` and
`j_total`. This module adds the two remaining clauses of Stacks 0D8B for that site:

* `CategoryTheory.SimplicialSemiRepresentable.stableAugmentation_functor`: the functor of the
  augmentation is `j_0`;
* `CategoryTheory.SimplicialSemiRepresentable.stableTotalPushforward_eq`: the direct image of
  `a` *equals* that of the morphism of topoi of `j_total`.

## References

* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

namespace SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.IsStacksSite]

/-- **Stacks 0D8B.** For an arbitrary site, the functor underlying the augmentation
`CategoryTheory.SimplicialSemiRepresentable.stableAugmentation` is the degree-zero localization
functor `j_0`. -/
@[stacks 0D8B "the functor underlying that augmentation is j_0"]
theorem stableAugmentation_functor :
    (stableAugmentation J K).functor = sliceForget K (op (SimplexCategory.mk 0)) := rfl

/-- **Stacks 0D8B.** For an arbitrary site, the morphism of topoi `a : Sh((C/K)_total) ⟶ Sh(C)`
which Stacks 0D70 attaches to the augmentation `j_0` is the morphism of topoi of the
localization functor `j_total`: their direct images are *equal*, because the cocontinuous
functor which Stacks 0D70 attaches to the augmentation is `j_total` on the nose. -/
@[stacks 0D8B "a is the morphism of topoi of j_total: the direct images are equal"]
theorem stableTotalPushforward_eq :
    (CocontinuousSimplicialSite.Augmentation.totalMorphismOfTopoi
        (stableAugmentation J K)).pushforward =
      (stableTotalLocalizationMorphism J K).pushforward := by
  have key : ∀ {X : Type u} [SmallCategory X] (Jx : GrothendieckTopology X) {F G : X ⥤ C}
      [iF : F.IsCocontinuous Jx J] [iG : G.IsCocontinuous Jx J], F = G →
      F.sheafPushforwardCocontinuous (Type u) Jx J =
        G.sheafPushforwardCocontinuous (Type u) Jx J := by
    intro X _ Jx F G _ _ h
    subst h
    rfl
  exact key _
    (iF := CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor_isCocontinuous
      (stableAugmentation J K)) (iG := stable_totalForget_isCocontinuous J K)
    (stableTotalAugmentationFunctor_eq J K)

end SimplicialSemiRepresentable

end CategoryTheory

end
