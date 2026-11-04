module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationModulePullback
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModule
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSheafify
import StacksCore.Tactic.StacksAttribute

/-!
# The pullback of modules along a ringed augmentation is cartesian

Let `S` be a simplicial-site situation, `a` an augmentation of `S` towards a site `(D, K)` and
`A` a ringed augmentation of Stacks 0D9D, with total morphism of ringed topoi
`a : (Sh(C_total), O) ⟶ (Sh(D), O_D)`. Stacks 0D7H (3) says that the pullback `a^*F` of a sheaf
of `O_D`-modules is a cartesian sheaf of `O`-modules on the total site, i.e. that every transition
`f_φ^*(a^*F)_m ⟶ (a^*F)_n` is invertible.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.isIso_whiskerRight`
  `_componentPushforwardTransition`: the 2-morphism `g_n ⟶ g_m ∘ f_φ` becomes invertible after
  the direct image of the total augmentation is appended.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.isCartesianModule_pullbackModules`:
  **Stacks 0D7H (3)**.

## The argument

The reason is the source's: `a_m ∘ f_φ = a_n`. In this development that identification is not
used through a 2-isomorphism of *ringed* topoi — which the tree does not have — but through
Stacks 0D7H (1), which is already proved here for sheaves of sets.

The transition of sheaves of modules is the mate, under the adjunctions of Stacks 03D7, of the
2-morphism `g_n ⟶ g_m ∘ f_φ` of ringed topoi. Mathlib's
`CategoryTheory.conjugateEquiv_whiskerLeft` says that precomposing a mate with a left adjoint is
appending its right adjoint to the transformation it is the mate of. So the transition of the
pullbacks along the ringed augmentation is invertible exactly when the 2-morphism becomes
invertible after `a_*` is appended, and — one more application of the same lemma, on sheaves of
sets — that happens exactly when the inverse-image transition `g_m⁻¹ ⋙ f_φ⁻¹ ⟶ g_n⁻¹` becomes
invertible after `a⁻¹` is *prepended*. Prepending `a⁻¹` is evaluating at `a⁻¹𝒢`, where the
transition is the transition of Stacks 09WF conjugated by two comparisons of Stacks 09WG, and
that transition is invertible by Stacks 0D7H (1).

So no coherence of the augmentation with the simplicial transitions is assumed beyond part (1),
nothing is restricted to the cocontinuous case, and the whole passage from sheaves of sets to
sheaves of modules is the two steps where a mate meets a whiskering.

The reduction from sheaves of modules to sheaves of sets is the other half: a morphism of sheaves
of modules is invertible as soon as its underlying morphism of sheaves of sets is, and the
underlying morphism of the induced transformation of direct images of modules is the 2-morphism
itself — the direct image of a sheaf of modules has the direct image of its underlying sheaf of
sets underneath, on the nose.

## References

* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Section 85.10 (Tag 0D9D)](https://stacks.math.columbia.edu/tag/0D9D)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CategoryTheory.SimplicialSiteSituation

namespace Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- **Stacks 0D7H (1), read through the component morphisms of topoi.** The inverse-image
transition `g_m⁻¹ ⋙ f_φ⁻¹ ⟶ g_n⁻¹` of
`CategoryTheory.SimplicialSiteSituation.componentInverseImageTransition`, evaluated at the
inverse image of a sheaf on the augmentation site, is invertible.

It is the transition of Stacks 09WF at that sheaf, which part (1) says is invertible, conjugated
by the two comparisons of Stacks 09WG. -/
theorem isIso_componentInverseImageTransition_inverseImage {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf K (Type u)) :
    IsIso ((S.componentInverseImageTransition φ).app
      ((totalMorphismOfTopoi S D K a).inverseImage.obj G)) := by
  have hcart : IsIso ((S.fiberTransition φ).app
      ((totalMorphismOfTopoi S D K a).inverseImage.obj G)) :=
    isCartesianSheaf_totalMorphismOfTopoi_inverseImage S D K a G φ
  have h : (S.componentInverseImageTransition φ).app
        ((totalMorphismOfTopoi S D K a).inverseImage.obj G) =
      ((S.transitionMorphism φ).inverseImage.mapIso
            ((S.componentRingedTopos_setRestrictionIso m).app
              ((totalMorphismOfTopoi S D K a).inverseImage.obj G)) ≪≫
          @asIso _ _ _ _ ((S.fiberTransition φ).app
              ((totalMorphismOfTopoi S D K a).inverseImage.obj G)) hcart ≪≫
            ((S.componentRingedTopos_setRestrictionIso n).app
              ((totalMorphismOfTopoi S D K a).inverseImage.obj G)).symm).hom := rfl
  rw [h]
  exact Iso.isIso_hom _

/-- **Stacks 0D7H (1), as a statement about the transition and not about one sheaf.** The
inverse-image transition becomes invertible once the inverse image of the total augmentation is
prepended: evaluating at `a⁻¹𝒢` is exactly what part (1) makes invertible. -/
theorem isIso_whiskerLeft_componentInverseImageTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (Functor.whiskerLeft (totalMorphismOfTopoi S D K a).inverseImage
      (S.componentInverseImageTransition φ)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro G
  exact isIso_componentInverseImageTransition_inverseImage S D K a φ G

/-- **The 2-morphism `g_n ⟶ g_m ∘ f_φ` becomes invertible after the direct image of the total
augmentation.** This is the form in which the source's `a_m ∘ f_φ = a_n` is used here.

The 2-morphism is the mate of the inverse-image transition, and appending a right adjoint to a
mate is prepending its left adjoint to the transformation it is the mate of
(`CategoryTheory.conjugateEquiv_whiskerLeft`); the prepended transformation is invertible by
Stacks 0D7H (1). -/
theorem isIso_whiskerRight_componentPushforwardTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (Functor.whiskerRight (S.componentPushforwardTransition φ)
      (totalMorphismOfTopoi S D K a).pushforward) := by
  have hwl := isIso_whiskerLeft_componentInverseImageTransition S D K a φ
  have hdef : S.componentPushforwardTransition φ =
      conjugateEquiv (componentMorphism S n).adj
        ((componentMorphism S m).comp (S.transitionMorphism φ)).adj
        (S.componentInverseImageTransition φ) := rfl
  rw [hdef, ← conjugateEquiv_whiskerLeft (componentMorphism S n).adj
    ((componentMorphism S m).comp (S.transitionMorphism φ)).adj
    (totalMorphismOfTopoi S D K a).adj (S.componentInverseImageTransition φ)]
  exact Iso.isIso_hom ((conjugateIsoEquiv
    ((totalMorphismOfTopoi S D K a).adj.comp (componentMorphism S n).adj)
    ((totalMorphismOfTopoi S D K a).adj.comp
      ((componentMorphism S m).comp (S.transitionMorphism φ)).adj))
    (@asIso _ _ _ _ (Functor.whiskerLeft (totalMorphismOfTopoi S D K a).inverseImage
      (S.componentInverseImageTransition φ)) hwl))

end Augmentation

namespace RingedAugmentation

variable {S : SimplicialSiteSituation.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  {a : Augmentation S D K} (A : RingedAugmentation S D K a)

/-- Abelian sheaves on the total site are sheafifiable at the site universe, the total category
being small there. -/
local instance hasWeakSheafifyTotalAugmentationCartesian :
    HasWeakSheafify S.totalTopology AddCommGrpCat.{u} :=
  (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} S.totalTopology).1

/-- On the total site at the site universe, the maps inverted by sheafification of abelian
sheaves are exactly the locally bijective ones. -/
local instance wEqualsLocallyBijectiveTotalAugmentationCartesian :
    S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  letI : HasSheafify ((equivSmallModel.{u} (S.totalCategory : Type u)).inverse.inducedTopology
      S.totalTopology) AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u, u + 1, u}
    S.totalTopology

attribute [local instance] hasWeakSheafifyComponent

/-- **The transformation of direct images of modules induced by the 2-morphism `g_n ⟶ g_m ∘ f_φ`
becomes invertible after the direct image of modules along the ringed augmentation.** -/
theorem isIso_whiskerRight_pushforwardModulesMap {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (Functor.whiskerRight (S.componentRingedTwoMorphism A.O φ).pushforwardModulesMap
      A.totalRingedHom.pushforwardModules) :=
  (S.componentRingedTwoMorphism A.O φ).isIso_whiskerRight_pushforwardModulesMap
    A.totalRingedHom
    (Augmentation.isIso_whiskerRight_componentPushforwardTransition S D K a φ)

/-- **The transformation of pullbacks of modules induced by the 2-morphism `g_n ⟶ g_m ∘ f_φ`
becomes invertible after the pullback of modules along the ringed augmentation.** -/
theorem isIso_whiskerLeft_pullbackModulesMap {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (Functor.whiskerLeft (A.totalRingedHom.toModulesHom.pullbackModules)
      (S.componentRingedTwoMorphism A.O φ).pullbackModulesMap) :=
  (S.componentRingedTwoMorphism A.O φ).isIso_whiskerLeft_pullbackModulesMap
    A.totalRingedHom (A.isIso_whiskerRight_pushforwardModulesMap φ)

/-- **Stacks 0D7H (3).** The pullback `a^*F` of a sheaf of `O_D`-modules along the ringed
augmentation of Stacks 0D9D is a cartesian sheaf of `O`-modules on the total site: every
transition `f_φ^*(a^*F)_m ⟶ (a^*F)_n` of sheaves of modules is invertible.

The transition is the compositor of Stacks 03D8 followed by the transformation of pullbacks
induced by the 2-morphism `g_n ⟶ g_m ∘ f_φ`, and that transformation is invertible after the
pullback along the ringed augmentation by
`CategoryTheory.SimplicialSiteSituation.RingedAugmentation.isIso_whiskerLeft_pullbackModulesMap`,
which rests on Stacks 0D7H (1). -/
@[stacks 0D7H "part (3)"]
theorem isCartesianModule_pullbackModules
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf A.augmentationRingedTopos.O)) :
    S.IsModuleFiberTransitionIso A.O ((A.totalRingedHom.toModulesHom.pullbackModules).obj F) := by
  intro m n φ
  have hpb := A.isIso_whiskerLeft_pullbackModulesMap φ
  have h2 : IsIso ((S.componentRingedTwoMorphism A.O φ).pullbackModulesMap.app
      ((A.totalRingedHom.toModulesHom.pullbackModules).obj F)) :=
    Iso.isIso_hom ((@asIso _ _ _ _ (Functor.whiskerLeft
      (A.totalRingedHom.toModulesHom.pullbackModules)
      (S.componentRingedTwoMorphism A.O φ).pullbackModulesMap) hpb).app F)
  have h1 : IsIso ((AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso
        (S.transitionRingedToposHom A.O φ) (componentRingedToposHom S A.O m)).inv.app
      ((A.totalRingedHom.toModulesHom.pullbackModules).obj F)) :=
    Iso.isIso_hom ((AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso
      (S.transitionRingedToposHom A.O φ) (componentRingedToposHom S A.O m)).app
      ((A.totalRingedHom.toModulesHom.pullbackModules).obj F)).symm
  have hfun : S.moduleFiberTransition A.O φ =
      (AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso
          (S.transitionRingedToposHom A.O φ) (componentRingedToposHom S A.O m)).inv ≫
        (S.componentRingedTwoMorphism A.O φ).pullbackModulesMap := rfl
  rw [hfun, NatTrans.comp_app]
  exact ((@asIso _ _ _ _ _ h1) ≪≫ (@asIso _ _ _ _ _ h2)).isIso_hom

end RingedAugmentation

end CategoryTheory.SimplicialSiteSituation

end
