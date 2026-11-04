module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousComp
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Augmentation
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Morphism

/-!
# Morphisms of augmented simplicial sites

A morphism between the topoi of two augmentation sites is compatible with a morphism of
simplicial sites if it is induced by a site-level morphism making the degree-zero square
commute. Such a morphism makes the square of degree-zero topoi and augmentation topoi
commute, as witnessed by a natural isomorphism of direct-image functors.

## Main definitions

* `CategoryTheory.cocontinuousMorphismOfTopoi`: the morphism of topoi induced by a
  cocontinuous functor of sites.
* `CategoryTheory.SimplicialSiteMorphism.CompatibleWithAugmentations`: compatibility of a
  morphism of topoi between augmentation sites with a morphism of simplicial sites and the two
  augmentations.

## Main results

* `CategoryTheory.SimplicialSiteMorphism.augmentationPushforwardIso`: the comparison between
  the two composites around the degree-zero square.

## Implementation notes

The site-level witness is continuous in case (A) and cocontinuous in case (B). Composition of
functors is written in diagrammatic order. The equality of morphisms of topoi in the source is
expressed as a natural isomorphism of their direct-image functors; this form applies to both
cases without identifying choices of adjunction data inside the morphisms of topoi.

## References

* [Stacks Project, Tag 0D98](https://stacks.math.columbia.edu/tag/0D98)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

/-- The morphism of topoi induced by a cocontinuous functor of sites. -/
@[implicit_reducible]
noncomputable def cocontinuousMorphismOfTopoi
    {D D' : Cat.{u, u}} {K : GrothendieckTopology D}
    {K' : GrothendieckTopology D'} (v : D ⥤ D')
    (hv : v.IsCocontinuous K K') :
    MorphismOfTopoi (Sheaf K (Type u)) (Sheaf K' (Type u)) := by
  letI : v.IsCocontinuous K K' := hv
  exact
    { pushforward := gStar _ _ _ _ v
      inverseImage := gInv _ _ _ _ v
      adj := Classical.choice (main_adjunction00XO _ _ _ _ v)
      preservesFiniteLimits := main_left_exact _ _ _ _ v }

namespace SimplicialSiteMorphism

/-- Compatibility of a morphism of topoi between augmentation sites with a morphism of simplicial
sites and the two augmentations. -/
@[stacks 0D98 "compatibility_with_augmentations"]
def CompatibleWithAugmentations
    {S S' : SimplicialSiteSituation.{u}}
    {D D' : Cat.{u, u}} {K : GrothendieckTopology D}
    {K' : GrothendieckTopology D'}
    (h : SimplicialSiteMorphism S S')
    (a : SimplicialSiteSituation.Augmentation S D K)
    (a' : SimplicialSiteSituation.Augmentation S' D' K')
    (g : MorphismOfTopoi (Sheaf K (Type u)) (Sheaf K' (Type u))) : Prop := by
  cases h with
  | ofMorphismOfSites h =>
    change SimplicialSite.ContinuousAugmentation _ D K at a
    change SimplicialSite.ContinuousAugmentation _ D' K' at a'
    exact ∃ (v : D' ⥤ D) (hv : v.IsMorphismOfSites K' K),
      (g = hv.morphismOfTopoi) ∧
      (v ⋙ a.functor = a'.functor ⋙ (h.hom.app (SimplexCategory.mk 0)).toFunctor)
  | ofCocontinuous h =>
    change CocontinuousSimplicialSite.Augmentation _ D K at a
    change CocontinuousSimplicialSite.Augmentation _ D' K' at a'
    exact ∃ (v : D ⥤ D') (hv : v.IsCocontinuous K K'),
      (g = cocontinuousMorphismOfTopoi v hv) ∧
      (a.functor ⋙ v =
        (h.hom.app (Opposite.op (SimplexCategory.mk 0))).toFunctor ⋙ a'.functor)

/-- The degree-zero square of a morphism of augmented simplicial sites commutes, as witnessed by a
natural isomorphism of direct-image functors. -/
@[stacks 0D98]
noncomputable def augmentationPushforwardIso
    {S S' : SimplicialSiteSituation.{u}}
    {D D' : Cat.{u, u}} {K : GrothendieckTopology D}
    {K' : GrothendieckTopology D'}
    (h : SimplicialSiteMorphism S S')
    (a : SimplicialSiteSituation.Augmentation S D K)
    (a' : SimplicialSiteSituation.Augmentation S' D' K')
    (g : MorphismOfTopoi (Sheaf K (Type u)) (Sheaf K' (Type u)))
    (hg : CompatibleWithAugmentations h a a' g) :
    (h.componentMorphism (SimplexCategory.mk 0)).pushforward ⋙
        (SimplicialSiteSituation.Augmentation.morphismOfTopoi S' D' K' a').pushforward ≅
      (SimplicialSiteSituation.Augmentation.morphismOfTopoi S D K a).pushforward ⋙
        g.pushforward := by
  cases h with
  | @ofMorphismOfSites C C' hm =>
      change ∃ (v : D' ⥤ D) (hv : v.IsMorphismOfSites K' K),
        (g = hv.morphismOfTopoi) ∧
          (v ⋙ a.functor = a'.functor ⋙
            (hm.hom.app (SimplexCategory.mk 0)).toFunctor) at hg
      let v := Classical.choose hg
      let hv := Classical.choose (Classical.choose_spec hg)
      have ⟨hg_eq, hcomp⟩ := Classical.choose_spec (Classical.choose_spec hg)
      rw [hg_eq]
      change
        ((hm.isMorphismOfSites (SimplexCategory.mk 0)).morphismOfTopoi).pushforward ⋙
            a'.isMorphismOfSites.morphismOfTopoi.pushforward ≅
          a.isMorphismOfSites.morphismOfTopoi.pushforward ⋙
            hv.morphismOfTopoi.pushforward
      let F := (hm.hom.app (SimplexCategory.mk 0)).toFunctor
      let J₀ := C.coverage (SimplexCategory.mk 0) |>.toGrothendieck
      let J₁ := C'.coverage (SimplexCategory.mk 0) |>.toGrothendieck
      letI : F.IsContinuous J₁ J₀ :=
        (hm.isMorphismOfSites (SimplexCategory.mk 0)).isContinuous
      letI : a'.functor.IsContinuous K' J₁ := a'.isMorphismOfSites.isContinuous
      letI : a.functor.IsContinuous K J₀ := a.isMorphismOfSites.isContinuous
      letI : v.IsContinuous K' K := hv.isContinuous
      letI : (a'.functor ⋙ F).IsContinuous K' J₀ :=
        Functor.isContinuous_comp a'.functor F K' J₁ J₀
      letI : (v ⋙ a.functor).IsContinuous K' J₀ :=
        Functor.isContinuous_comp v a.functor K' K J₀
      have e₁ := Functor.sheafPushforwardContinuousComp'
        (F := a'.functor) (G := F) (FG := a'.functor ⋙ F)
        (eFG := Iso.refl _) (A := Type u) K' J₁ J₀
      have e₂ := Functor.sheafPushforwardContinuousComp'
        (F := v) (G := a.functor) (FG := v ⋙ a.functor)
        (eFG := Iso.refl _) (A := Type u) K' K J₀
      have e₃ := Functor.sheafPushforwardContinuousIso
        (e := eqToIso hcomp.symm) (A := Type u) K' J₀
      exact e₁.trans (e₃.trans e₂.symm)
  | @ofCocontinuous C C' hm =>
      change ∃ (v : D ⥤ D') (hv : v.IsCocontinuous K K'),
        (g = cocontinuousMorphismOfTopoi v hv) ∧
          (a.functor ⋙ v =
            (hm.hom.app (Opposite.op (SimplexCategory.mk 0))).toFunctor ⋙
              a'.functor) at hg
      let v := Classical.choose hg
      let hv := Classical.choose (Classical.choose_spec hg)
      have ⟨hg_eq, hcomp⟩ := Classical.choose_spec (Classical.choose_spec hg)
      rw [hg_eq]
      let U₁ := (hm.hom.app (Opposite.op (SimplexCategory.mk 0))).toFunctor
      let V₁ := a'.functor
      let U₂ := a.functor
      let V₂ := v
      let J₀ := topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))
      let J₁ := topologyOfCoverings (C'.coverage (Opposite.op (SimplexCategory.mk 0)))
      let K₀ := K
      let K₁ := K'
      let Fcomp := U₁ ⋙ V₁
      let Gcomp := U₂ ⋙ V₂
      letI : U₁.IsCocontinuous J₀ J₁ := hm.isCocontinuous _
      letI : V₁.IsCocontinuous J₁ K₁ := a'.isCocontinuous
      letI : U₂.IsCocontinuous J₀ K₀ := a.isCocontinuous
      letI : V₂.IsCocontinuous K₀ K₁ := hv
      letI : Fcomp.IsCocontinuous J₀ K₁ :=
        CategoryTheory.isCocontinuous_comp U₁ V₁ J₀ J₁ (L := K₁)
      letI : Gcomp.IsCocontinuous J₀ K₁ :=
        CategoryTheory.isCocontinuous_comp U₂ V₂ J₀ K₀ (L := K₁)
      change
        gStar _ _ J₀ J₁ U₁ ⋙ gStar _ _ J₁ K₁ V₁ ≅
          gStar _ _ J₀ K₀ U₂ ⋙ gStar _ _ K₀ K₁ V₂
      have hcomp' : Fcomp = Gcomp := hcomp.symm
      have e₁ := _root_.sheafPushforwardCocontinuousCompIso J₀ J₁ K₁ U₁ V₁
      have e₂ := _root_.sheafPushforwardCocontinuousCompIso J₀ K₀ K₁ U₂ V₂
      let P := {F : _ ⥤ _ // F.IsCocontinuous J₀ K₁}
      let push : P → (Sheaf J₀ (Type u) ⥤ Sheaf K₁ (Type u)) :=
        fun F => by
          letI : F.val.IsCocontinuous J₀ K₁ := F.property
          exact gStar _ _ J₀ K₁ F.val
      have e₃ : gStar _ _ J₀ K₁ Fcomp ≅ gStar _ _ J₀ K₁ Gcomp := by
        change push ⟨Fcomp, inferInstance⟩ ≅ push ⟨Gcomp, inferInstance⟩
        exact eqToIso (congrArg push (Subtype.ext hcomp'))
      simpa [gStar, Fcomp, Gcomp] using e₁.symm.trans (e₃.trans e₂)

end SimplicialSiteMorphism

end CategoryTheory

end
