module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationForkLimit
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationMorphism
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationPushforwardComparison

/-!
# The two constructions of the total augmentation agree in case (B)

Let `C` be a simplicial family of sites with cocontinuous transitions and `a` an augmentation of
`C` towards a site `(D, K)`. Stacks 0D70 attaches to `a` a morphism of topoi
`Sh(C_total) ⟶ Sh(D)`, which has two constructions: the one of the cocontinuous functor
`C_total ⥤ D` (`CocontinuousSimplicialSite.Augmentation.totalMorphismOfTopoi`), and the one
uniform in the two cases of the situation, whose direct image is the limit over the simplex
category of the direct images of the components
(`SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi`). This file identifies them.

## Main definitions

All names are in the namespace `CategoryTheory.CocontinuousSimplicialSite.Augmentation`.

* `pushforwardComparisonTotalAugmentationComparison`: the comparison of the two direct images,
  whose leg in degree `k` is the canonical map to the direct image of the component
  augmentation.
* `pushforwardComparisonIsoTotalAugmentationComparison`: it is an isomorphism.
* `inverseImageComparisonIsoTotalAugmentationComparison`: the resulting identification of the
  two inverse images.

## Implementation notes

Both direct images are the equalizer of the two transitions `0 ⇉ 1` of the cosimplicial system
of component direct images: the limit construction by
`CategoryTheory.CosimplicialObject.isLimitForkOfIsLimit`, and the cocontinuous one by Stacks 0D70
(3) in the restriction form `restrictFork_existsUnique`. The transitions of the two systems are
the same maps, so the comparison is an isomorphism by uniqueness of factorisations.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.CocontinuousSimplicialSite.Augmentation

open CategoryTheory.SimplicialSiteSituation

variable {C : CocontinuousSimplicialSite.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  (a : C.Augmentation D K)

/-- The legs of the fork of Stacks 0D70 (3) in restriction form are natural in the sheaf. -/
theorem restrictForkLeg_naturality_totalAugmentationComparison
    {F F' : Sheaf (situation C).totalTopology (Type u)} (α : F ⟶ F') (k : SimplexCategory) :
    (totalMorphism a).pushforward.map α ≫ restrictForkLeg a F' k =
      restrictForkLeg a F k ≫
        (componentAug a k).pushforward.map (((situation C).restrict k).map α) := by
  have h1 := (componentRestrictAdj (C := C) k).unit.naturality α
  have h2 := (componentCompIso a k).hom.naturality (((situation C).restrict k).map α)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at h1 h2
  simp only [restrictForkLeg, ← CategoryTheory.Functor.map_comp_assoc, h1]
  rw [CategoryTheory.Functor.map_comp, Category.assoc, h2, Category.assoc]

/-- The transition of the fork of Stacks 0D70 (3) in restriction form is the transition of the
cosimplicial system of component direct images of the limit construction. -/
theorem restrictForkMap_eq_totalAugmentationComparison
    (F : Sheaf (situation C).totalTopology (Type u)) {m n : SimplexCategory} (φ : m ⟶ n) :
    restrictForkMap a F φ =
      (SimplicialSiteSituation.Augmentation.componentPushforwardTransition (situation C) D K a
        φ).app F := rfl

/-- The cone over the cosimplicial system of component direct images with vertex the direct
image of the cocontinuous total augmentation. -/
def restrictForkConeTotalAugmentationComparison (F : Sheaf (situation C).totalTopology (Type u)) :
    Cone (SimplicialSiteSituation.Augmentation.pushforwardDiagram (situation C) D K a F) where
  pt := (totalMorphism a).pushforward.obj F
  π :=
    { app := fun k => restrictForkLeg a F k
      naturality := fun _ _ φ =>
        (Category.id_comp _).trans (restrictForkLeg_comp_restrictForkMap a F φ).symm }

/-- The lift of the cone of legs, followed by the leg of the limit in degree `k`, is the leg of
the fork. -/
theorem lift_restrictForkCone_comp_projection_totalAugmentationComparison
    (F : Sheaf (situation C).totalTopology (Type u)) (k : SimplexCategory) :
    limit.lift _ (restrictForkConeTotalAugmentationComparison a F) ≫
        SimplicialSiteSituation.Augmentation.pushforwardProjection (situation C) D K a F k =
      restrictForkLeg a F k :=
  limit.lift_π (restrictForkConeTotalAugmentationComparison a F) k

/-- **Stacks 0D70, comparison of the two constructions, direct images.** The comparison from the
direct image of the cocontinuous total augmentation to the limit of the cosimplicial system of
component direct images. -/
def pushforwardComparisonTotalAugmentationComparison :
    (totalMorphism a).pushforward ⟶
      SimplicialSiteSituation.Augmentation.pushforward (situation C) D K a where
  app F := limit.lift _ (restrictForkConeTotalAugmentationComparison a F)
  naturality F F' α := limit.hom_ext fun k => by
    have e1 := lift_restrictForkCone_comp_projection_totalAugmentationComparison a F' k
    have e2 := lift_restrictForkCone_comp_projection_totalAugmentationComparison a F k
    have e3 := SimplicialSiteSituation.Augmentation.pushforward_map_comp_projection (situation C)
      D K a α k
    have e4 := restrictForkLeg_naturality_totalAugmentationComparison a α k
    refine (Category.assoc _ _ _).trans (((congrArg (fun t => _ ≫ t) e1).trans e4).trans ?_)
    refine (congrArg (fun t => t ≫ _) e2.symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun t => _ ≫ t) e3.symm).trans ?_
    exact (Category.assoc _ _ _).symm

/-- The comparison followed by the leg of the limit in degree `k` is the leg of the fork. -/
theorem pushforwardComparison_app_comp_projection_totalAugmentationComparison
    (F : Sheaf (situation C).totalTopology (Type u)) (k : SimplexCategory) :
    (pushforwardComparisonTotalAugmentationComparison a).app F ≫
        SimplicialSiteSituation.Augmentation.pushforwardProjection (situation C) D K a F k =
      restrictForkLeg a F k :=
  limit.lift_π (restrictForkConeTotalAugmentationComparison a F) k

/-- The degree-zero leg of the limit construction equalises the two vertex transitions. -/
theorem pushforwardProjection_zero_condition_totalAugmentationComparison
    (F : Sheaf (situation C).totalTopology (Type u)) :
    SimplicialSiteSituation.Augmentation.pushforwardProjection (situation C) D K a F
          (SimplexCategory.mk 0) ≫
        restrictForkMap a F
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0) =
      SimplicialSiteSituation.Augmentation.pushforwardProjection (situation C) D K a F
          (SimplexCategory.mk 0) ≫
        restrictForkMap a F
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1) :=
  (SimplicialSiteSituation.Augmentation.pushforwardProjection_comp (situation C) D K a F _).trans
    (SimplicialSiteSituation.Augmentation.pushforwardProjection_comp (situation C) D K a F _).symm

/-- The degree-zero leg of the fork in restriction form equalises the two vertex transitions. -/
theorem restrictForkLeg_zero_condition_totalAugmentationComparison
    (F : Sheaf (situation C).totalTopology (Type u)) :
    restrictForkLeg a F (SimplexCategory.mk 0) ≫
        restrictForkMap a F
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0) =
      restrictForkLeg a F (SimplexCategory.mk 0) ≫
        restrictForkMap a F
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1) :=
  (restrictForkLeg_comp_restrictForkMap a F _).trans
    (restrictForkLeg_comp_restrictForkMap a F _).symm

/-- **Stacks 0D70, the two constructions agree.** The comparison of the direct image of the
cocontinuous total augmentation with the limit construction is invertible: both are the
equalizer of the two vertex transitions of the component direct images. -/
instance isIso_pushforwardComparison_app_totalAugmentationComparison
    (F : Sheaf (situation C).totalTopology (Type u)) :
    IsIso ((pushforwardComparisonTotalAugmentationComparison a).app F) := by
  obtain ⟨l, hl, -⟩ := restrictFork_existsUnique a F _
    (SimplicialSiteSituation.Augmentation.pushforwardProjection (situation C) D K a F
      (SimplexCategory.mk 0))
    (pushforwardProjection_zero_condition_totalAugmentationComparison a F)
  obtain ⟨w, -, huniq⟩ := restrictFork_existsUnique a F _
    (restrictForkLeg a F (SimplexCategory.mk 0))
    (restrictForkLeg_zero_condition_totalAugmentationComparison a F)
  have h1 : ((pushforwardComparisonTotalAugmentationComparison a).app F ≫ l) ≫
      restrictForkLeg a F (SimplexCategory.mk 0) = restrictForkLeg a F (SimplexCategory.mk 0) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t => (pushforwardComparisonTotalAugmentationComparison a).app F ≫ t)
        hl).trans (pushforwardComparison_app_comp_projection_totalAugmentationComparison a F _))
  have hlim := CosimplicialObject.isLimitForkOfIsLimit
    (SimplicialSiteSituation.Augmentation.pushforwardDiagram (situation C) D K a F) _
    (limit.isLimit _)
  refine ⟨l, (huniq _ h1).trans (huniq _ (Category.id_comp _)).symm,
    Fork.IsLimit.hom_ext hlim ?_⟩
  exact (Category.assoc _ _ _).trans ((congrArg (fun t => l ≫ t)
    (pushforwardComparison_app_comp_projection_totalAugmentationComparison a F _)).trans
      (hl.trans (Category.id_comp _).symm))

/-- **Stacks 0D70, the two constructions agree, direct images.** The direct image of the
cocontinuous total augmentation is the limit construction. -/
def pushforwardComparisonIsoTotalAugmentationComparison :
    (totalMorphism a).pushforward ≅
      (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi (situation C) D K a).pushforward :=
  NatIso.ofComponents
    (fun F => @asIso _ _ _ _ ((pushforwardComparisonTotalAugmentationComparison a).app F)
      (isIso_pushforwardComparison_app_totalAugmentationComparison a F))
    (fun α => (pushforwardComparisonTotalAugmentationComparison a).naturality α)

/-- **Stacks 0D70, the two constructions agree, inverse images.** The inverse image of the limit
construction of the total augmentation is the inverse image of the cocontinuous one, by
uniqueness of left adjoints. -/
def inverseImageComparisonIsoTotalAugmentationComparison :
    (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi (situation C) D K a).inverseImage ≅
      (totalMorphism a).inverseImage :=
  Adjunction.leftAdjointUniq
    (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi (situation C) D K a).adj
    ((totalMorphism a).adj.ofNatIsoRight (pushforwardComparisonIsoTotalAugmentationComparison a))

end CategoryTheory.CocontinuousSimplicialSite.Augmentation

namespace CategoryTheory.SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-- **Stacks 0D8B, for the limit construction.** The inverse image of the total augmentation of
Stacks 0D70, built as the limit construction uniform in the two cases, is restriction along the
localization functor `j_total` of the total site. -/
noncomputable def situationTotalInverseImageIsoTotalAugmentationComparison :
    (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi (situation J K) (Cat.of C) J
        (situationAugmentation J K)).inverseImage ≅
      (totalLocalizationMorphism J K).inverseImage :=
  CocontinuousSimplicialSite.Augmentation.inverseImageComparisonIsoTotalAugmentationComparison
      (augmentation J K) ≪≫
    totalInverseImageIso J K

end CategoryTheory.SimplicialSemiRepresentable

end
