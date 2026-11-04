module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectTotalSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectPushforwardAcyclic
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationDescentAb
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianInverseImageULift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImageRestriction
public import StacksFrontier.Homology.AdjunctionSquareDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of abelian sheaves along a hypercovering, on the site `(C/U)_total`

Let `C` be a site with fibre products given by a pretopology `P`, and let `a : U → X` be a
hypercovering of an object `X` of `C` by a simplicial object `U` of `C` (Section 09X8). The total
site `(C/U)_total` of Stacks 09WL has the objects `V/U_n` and the augmentation
`a : Sh((C/U)_total) → Sh(C/X)` of the cocontinuous functor `V/U_n ↦ V/X`. Stacks 0DA8 (2) and
Stacks 0D8N say that on abelian sheaves the unit `𝒢 → a_* a⁻¹ 𝒢` is an isomorphism and that
`a⁻¹ 𝒢` is acyclic for `a_*`. This file records both statements for the abelian direct image of
the augmentation morphism of topoi of `(C/U)_total`, which is the morphism `a_ph` of the diagram
of Stacks 0DHJ.

## Main definitions

* `CategoryTheory.SimplicialOver.associatedTotalAbEquivalence`: abelian sheaves on `(C/U)_total`
  are abelian sheaves on the total site `(C/K)_total` of Remark 0D8C attached to the simplicial
  semi-representable object `K_n = {U_n → X}`.
* `CategoryTheory.SimplicialOver.augmentationAbelianInverseImageIso`: the abelian inverse image
  of the augmentation is restriction along `V/U_n ↦ V/X`.

## Main results

* `CategoryTheory.SimplicialOver.isIso_augmentationAbelianUnit_app`: the unit
  `𝒢 → a_* a⁻¹ 𝒢` is an isomorphism (Stacks 0DA8 (2)).
* `CategoryTheory.SimplicialOver.isZero_rightDerived_augmentationAbelianPushforward`:
  `Rᵠ a_* (a⁻¹ 𝒢) = 0` for `q > 0` (Stacks 0D8N).

## References

* [Stacks Project, Tag 0DA8](https://stacks.math.columbia.edu/tag/0DA8)
* [Stacks Project, Tag 0D8N](https://stacks.math.columbia.edu/tag/0D8N)
* [Stacks Project, Tag 09WL](https://stacks.math.columbia.edu/tag/09WL)
* [Stacks Project, Section 09X8](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CategoryTheory.Hypercovering
open Stacks.Topos.AbelianPushforward

universe u

namespace CategoryTheory.SimplicialOver

variable {C : Type u} [SmallCategory C] [HasPullbacks C] {X : C} (U : SimplicialObject C)
  (a : U ⟶ (SimplicialObject.const C).obj X) (J : GrothendieckTopology C)

/-- The comparison functor `(C/K)_total ⥤ (C/U)_total` is continuous. -/
instance fromAssociatedTotal_isContinuous :
    (fromAssociatedTotal U a).IsContinuous (associatedTotalTopology U a J)
      (SimplicialOver.totalTopology J U) :=
  haveI := associatedTotalEquivalence_isDenseSubsite U a J
  inferInstanceAs ((associatedTotalEquivalence U a).functor.IsContinuous _ _)

/-- The comparison functor `(C/U)_total ⥤ (C/K)_total` is continuous. -/
instance toAssociatedTotal_isContinuous :
    (toAssociatedTotal U a).IsContinuous (SimplicialOver.totalTopology J U)
      (associatedTotalTopology U a J) :=
  Functor.isContinuous_of_iso (associatedTotalEquivalenceInverseIso U a) _ _

/-- The functor `V/U_n ↦ V/X` is continuous. -/
instance augmentationFunctor_isContinuous :
    (augmentationFunctor U a).IsContinuous (SimplicialOver.totalTopology J U) (J.over X) := by
  rw [← toAssociatedTotal_comp_totalForget]
  have := SimplicialSemiRepresentable.totalForget_isContinuous (J.over X)
    (associatedSimplicialObject.{u} U a)
  exact Functor.isContinuous_comp _ _ _ (associatedTotalTopology U a J) _

/-- Restriction of abelian sheaves along `(C/K)_total ⥤ (C/U)_total`. -/
abbrev fromAssociatedTotalAb :
    Sheaf (SimplicialOver.totalTopology J U) AddCommGrpCat.{u} ⥤
      Sheaf (associatedTotalTopology U a J) AddCommGrpCat.{u} :=
  (fromAssociatedTotal U a).sheafPushforwardContinuous AddCommGrpCat.{u}
    (associatedTotalTopology U a J) (SimplicialOver.totalTopology J U)

/-- Restriction of abelian sheaves along `(C/U)_total ⥤ (C/K)_total`. -/
abbrev toAssociatedTotalAb :
    Sheaf (associatedTotalTopology U a J) AddCommGrpCat.{u} ⥤
      Sheaf (SimplicialOver.totalTopology J U) AddCommGrpCat.{u} :=
  (toAssociatedTotal U a).sheafPushforwardContinuous AddCommGrpCat.{u}
    (SimplicialOver.totalTopology J U) (associatedTotalTopology U a J)

/-- The equivalence of abelian sheaves on `(C/U)_total` and `(C/K)_total`. -/
def associatedTotalAbEquivalence :
    Sheaf (SimplicialOver.totalTopology J U) AddCommGrpCat.{u} ≌
      SimplicialSemiRepresentable.TotalAbelianSheavesOver J X
        (associatedSimplicialObject.{u} U a) :=
  Equivalence.mk (fromAssociatedTotalAb U a J) (toAssociatedTotalAb U a J)
    (Functor.sheafPushforwardContinuousComp'
        (eqToIso (toAssociatedTotal_comp_fromAssociatedTotal U a))
        AddCommGrpCat.{u} (SimplicialOver.totalTopology J U) (associatedTotalTopology U a J)
        (SimplicialOver.totalTopology J U) ≪≫
      Functor.sheafPushforwardContinuousId _ _).symm
    (Functor.sheafPushforwardContinuousComp'
        (Functor.isoWhiskerLeft _ (associatedTotalEquivalenceInverseIso U a).symm ≪≫
          (associatedTotalEquivalence U a).unitIso.symm)
        AddCommGrpCat.{u} (associatedTotalTopology U a J) (SimplicialOver.totalTopology J U)
        (associatedTotalTopology U a J) ≪≫
      Functor.sheafPushforwardContinuousId _ _)

/-- The set-valued inverse image of the augmentation `a : Sh((C/U)_total) → Sh(C/X)` is restriction
along the functor `V/U_n ↦ V/X`, which is continuous. -/
def augmentationInverseImageIso :
    (augmentationMorphismOfTopoi J U a).inverseImage ≅
      (augmentationFunctor U a).sheafPushforwardContinuous (Type u)
        (SimplicialOver.totalTopology J U) (J.over X) :=
  Adjunction.leftAdjointUniq (augmentationMorphismOfTopoi J U a).adj
    (((augmentationFunctor U a).sheafAdjunctionCocontinuous (Type u)
      (SimplicialOver.totalTopology J U) (J.over X)).ofNatIsoRight
        (eqToIso (augmentationMorphismOfTopoi_pushforward J U a).symm))

/-- The abelian inverse image of the augmentation is restriction of abelian sheaves along
`V/U_n ↦ V/X`. -/
def augmentationAbelianInverseImageIso :
    Sites.abelianInverseImage (augmentationMorphismOfTopoi J U a) ≅
      (augmentationFunctor U a).sheafPushforwardContinuous AddCommGrpCat.{u}
        (SimplicialOver.totalTopology J U) (J.over X) :=
  haveI : ((augmentationFunctor U a).sheafPushforwardContinuous (Type u)
      (SimplicialOver.totalTopology J U) (J.over X)).IsRightAdjoint :=
    ⟨_, ⟨(augmentationFunctor U a).sheafAdjunctionContinuous (Type u)
      (SimplicialOver.totalTopology J U) (J.over X)⟩⟩
  Sites.abelianInverseImageIsoSheafPushforwardContinuous (augmentationFunctor U a) _ _
    (augmentationMorphismOfTopoi J U a) (augmentationInverseImageIso U a J)

/-- `V/U_n ↦ V/X`, precomposed with `(C/K)_total ⥤ (C/U)_total`, is the localization functor
`j_total` of `(C/K)_total`. -/
def fromAssociatedTotalCompAugmentationFunctorIso :
    fromAssociatedTotal U a ⋙ augmentationFunctor U a ≅
      SimplicialSemiRepresentable.totalForget (associatedSimplicialObject.{u} U a) :=
  Functor.isoWhiskerLeft _ (eqToIso (toAssociatedTotal_comp_totalForget U a).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft _ (associatedTotalEquivalenceInverseIso U a).symm ≪≫
        (associatedTotalEquivalence U a).unitIso.symm) _ ≪≫
    Functor.leftUnitor _

/-- The abelian inverse image of the augmentation of `(C/U)_total`, transported to `(C/K)_total`,
is the inverse image of the augmentation of `(C/K)_total`. -/
def augmentationAbelianInverseImageCompIso :
    Sites.abelianInverseImage (augmentationMorphismOfTopoi J U a) ⋙
        (associatedTotalAbEquivalence U a J).functor ≅
      𝟭 _ ⋙ SimplicialSemiRepresentable.abelianTotalInverseImageOver J X
        (associatedSimplicialObject.{u} U a) :=
  haveI := SimplicialSemiRepresentable.totalForget_isContinuous (J.over X)
    (associatedSimplicialObject.{u} U a)
  Functor.isoWhiskerRight (augmentationAbelianInverseImageIso U a J) _ ≪≫
    Functor.sheafPushforwardContinuousComp' (fromAssociatedTotalCompAugmentationFunctorIso U a)
      AddCommGrpCat.{u} (associatedTotalTopology U a J) (SimplicialOver.totalTopology J U)
      (J.over X) ≪≫
    (Functor.leftUnitor _).symm

/-! ### Restriction to a simplicial degree -/

section Component

variable (b : SimplexCategoryᵒᵖ)

/-- The inclusion `C/U_b ⥤ (C/U)_total` of a simplicial degree is continuous (Stacks 09WG). -/
instance ι_isContinuous :
    (Grothendieck.ι (slices U) b).IsContinuous (J.over (U.obj b))
      (SimplicialOver.totalTopology J U) := by
  have h := SimplicialSiteSituation.componentFunctor_isContinuous (situation J U) b.unop
  rw [componentTopology_eq] at h
  exact h

/-- The inclusion `C/U_b ⥤ (C/U)_total` of a simplicial degree is cocontinuous (Stacks 09WG). -/
instance ι_isCocontinuous :
    (Grothendieck.ι (slices U) b).IsCocontinuous (J.over (U.obj b))
      (SimplicialOver.totalTopology J U) := by
  have h := SimplicialSiteSituation.componentFunctor_isCocontinuous (situation J U) b.unop
  rw [componentTopology_eq] at h
  exact h

/-- Restriction of abelian sheaves on `(C/U)_total` to the simplicial degree `b`. -/
abbrev componentRestrictionAb :
    Sheaf (SimplicialOver.totalTopology J U) AddCommGrpCat.{u} ⥤
      Sheaf (J.over (U.obj b)) AddCommGrpCat.{u} :=
  (Grothendieck.ι (slices U) b).sheafPushforwardContinuous AddCommGrpCat.{u}
    (J.over (U.obj b)) (SimplicialOver.totalTopology J U)

/-- Restriction of abelian sheaves to a simplicial degree preserves finite limits. -/
instance componentRestrictionAb_preservesFiniteLimits :
    PreservesFiniteLimits (componentRestrictionAb U J b) :=
  Functor.preservesFiniteLimits_sheafPushforwardContinuous _ _ _ AddCommGrpCat.{u}

/-- Restriction of abelian sheaves to a simplicial degree is additive. -/
instance componentRestrictionAb_additive : (componentRestrictionAb U J b).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **Stacks 09WH on `(C/U)_total`**: restriction of abelian sheaves to a simplicial degree
preserves injective objects. -/
@[sga "4 VI 7.4.15" "special case"]
instance componentRestrictionAb_preservesInjectiveObjects :
    (componentRestrictionAb U J b).PreservesInjectiveObjects := by
  have key : ∀ (K' : GrothendieckTopology (Over (U.obj b)))
      (_ : (situation J U).componentTopology b.unop = K')
      [(Grothendieck.ι (slices U) b).IsContinuous K' (SimplicialOver.totalTopology J U)],
      ((Grothendieck.ι (slices U) b).sheafPushforwardContinuous AddCommGrpCat.{u} K'
        (SimplicialOver.totalTopology J U)).PreservesInjectiveObjects := by
    intro K' hK _
    subst hK
    exact SimplicialSiteSituation.preservesInjectiveObjects_componentRestrictionAb
      (situation J U) b.unop
  exact key _ (componentTopology_eq J U b.unop)

/-- Restriction of abelian sheaves to a simplicial degree preserves finite colimits. -/
instance componentRestrictionAb_preservesFiniteColimits :
    PreservesFiniteColimits (componentRestrictionAb U J b) :=
  haveI : PreservesColimitsOfSize.{0, 0} (componentRestrictionAb U J b) :=
    ((Grothendieck.ι (slices U) b).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
      (J.over (U.obj b)) (SimplicialOver.totalTopology J U)).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- **The components of `a⁻¹ 𝒢`.** Restricted to the simplicial degree `b`, the abelian inverse
image of `𝒢` along the augmentation `a : Sh((C/U)_total) → Sh(C/X)` is the restriction of `𝒢`
along the localization functor `C/U_b ⥤ C/X` of `a_b : U_b → X`. -/
def augmentationAbelianInverseImageCompRestrictionIso :
    Sites.abelianInverseImage (augmentationMorphismOfTopoi J U a) ⋙ componentRestrictionAb U J b ≅
      (Over.map (augmentationApp U a b)).sheafPushforwardContinuous AddCommGrpCat.{u}
        (J.over (U.obj b)) (J.over X) :=
  haveI : (augmentationFibre U a b).IsContinuous (J.over (U.obj b)) (J.over X) :=
    inferInstanceAs ((Over.map (augmentationApp U a b)).IsContinuous _ _)
  Functor.isoWhiskerRight (augmentationAbelianInverseImageIso U a J) _ ≪≫
    Functor.sheafPushforwardContinuousComp' (eqToIso (ι_comp_augmentationFunctor U a b))
      AddCommGrpCat.{u} (J.over (U.obj b)) (SimplicialOver.totalTopology J U) (J.over X)

end Component

section Descent

variable (P : Pretopology C)

/-- The square relating the augmentation of `(C/U)_total` to that of `(C/K)_total`, on direct
images of abelian sheaves. -/
def augmentationAbelianPushforwardSquareIso :
    SimplicialSemiRepresentable.abelianTotalPushforwardOver P.toGrothendieck X
        (associatedSimplicialObject.{u} U a) ⋙ 𝟭 _ ≅
      (associatedTotalAbEquivalence U a P.toGrothendieck).inverse ⋙
        abelianPushforward (SimplicialOver.totalTopology P.toGrothendieck U)
          (augmentationMorphismOfTopoi P.toGrothendieck U a) :=
  conjugateIsoEquiv (Adjunction.id.comp (SimplicialSemiRepresentable.abelianTotalAdjunctionOver
      P.toGrothendieck X (associatedSimplicialObject.{u} U a)))
    ((abelianInverseImageAdjPushforward (SimplicialOver.totalTopology P.toGrothendieck U)
      (augmentationMorphismOfTopoi P.toGrothendieck U a)).comp
        (associatedTotalAbEquivalence U a P.toGrothendieck).toAdjunction)
    (augmentationAbelianInverseImageCompIso U a P.toGrothendieck)

variable {U a}

/-- For a hypercovering, the unit of the abelian total adjunction of `(C/K)_total` is an
isomorphism. -/
private theorem isIso_abelianTotalAdjunctionOver_unit_app (h : IsHypercoveringAugmentation P U a)
    (N : Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u}) :
    IsIso ((SimplicialSemiRepresentable.abelianTotalAdjunctionOver P.toGrothendieck X
      (associatedSimplicialObject.{u} U a)).unit.app ((𝟭 _).obj N)) :=
  @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _
    (SimplicialSemiRepresentable.isIso_abelianUnit_augmented' P U a h) _

/-- **Stacks 0DA8 (2) on `(C/U)_total`.** For a hypercovering `a : U → X` of `X` in `C`, the unit
`𝒢 → a_* a⁻¹ 𝒢` of the abelian augmentation `a : Sh((C/U)_total) → Sh(C/X)` is an isomorphism. -/
theorem isIso_augmentationAbelianUnit_app (h : IsHypercoveringAugmentation P U a)
    (N : Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u}) :
    IsIso ((abelianInverseImageAdjPushforward (SimplicialOver.totalTopology P.toGrothendieck U)
      (augmentationMorphismOfTopoi P.toGrothendieck U a)).unit.app N) := by
  have := isIso_abelianTotalAdjunctionOver_unit_app P h N
  have : IsIso
      ((Adjunction.id (C := Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u})).unit.app N) := by
    simp only [Adjunction.id_unit]; infer_instance
  exact Adjunction.isIso_unit_app_of_comp_iso
    (abelianInverseImageAdjPushforward (SimplicialOver.totalTopology P.toGrothendieck U)
      (augmentationMorphismOfTopoi P.toGrothendieck U a))
    (associatedTotalAbEquivalence U a P.toGrothendieck).toAdjunction
    (SimplicialSemiRepresentable.abelianTotalAdjunctionOver P.toGrothendieck X
      (associatedSimplicialObject.{u} U a)) Adjunction.id
    (augmentationAbelianPushforwardSquareIso U a P) N

/-- **Stacks 0D8N on `(C/U)_total`.** For a hypercovering `a : U → X` of `X` in `C` and an abelian
sheaf `𝒢` on `C/X`, `Rᵠ a_* (a⁻¹ 𝒢) = 0` for `q > 0`, where `a : Sh((C/U)_total) → Sh(C/X)` is the
augmentation. -/
theorem isZero_rightDerived_augmentationAbelianPushforward (h : IsHypercoveringAugmentation P U a)
    (N : Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u}) (q : ℕ) (hq : 0 < q) :
    IsZero (((abelianPushforward (SimplicialOver.totalTopology P.toGrothendieck U)
      (augmentationMorphismOfTopoi P.toGrothendieck U a)).rightDerived q).obj
        ((Sites.abelianInverseImage
          (augmentationMorphismOfTopoi P.toGrothendieck U a)).obj N)) := by
  let adj_b := SimplicialSemiRepresentable.abelianTotalAdjunctionOver P.toGrothendieck X
      (associatedSimplicialObject.{u} U a)
  let E := associatedTotalAbEquivalence U a P.toGrothendieck
  have : (abelianPushforward (SimplicialOver.totalTopology P.toGrothendieck U)
      (augmentationMorphismOfTopoi P.toGrothendieck U a)).Additive :=
    abelianPushforward_additive _ _
  have := SimplicialSemiRepresentable.additive_abelianTotalPushforwardOver P.toGrothendieck X
      (associatedSimplicialObject.{u} U a)
  have : PreservesFiniteLimits
      (SimplicialSemiRepresentable.abelianTotalPushforwardOver P.toGrothendieck X
      (associatedSimplicialObject.{u} U a)) :=
    have : PreservesLimitsOfSize.{0, 0} _ := adj_b.rightAdjoint_preservesLimits
    PreservesLimitsOfSize.preservesFiniteLimits _
  have : (SimplicialSemiRepresentable.abelianTotalPushforwardOver P.toGrothendieck X
      (associatedSimplicialObject.{u} U a)).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj_b
  have : E.inverse.Additive :=
    inferInstanceAs (toAssociatedTotalAb U a P.toGrothendieck).Additive
  have : E.inverse.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms E.toAdjunction
  have : E.inverse.PreservesHomology := Functor.preservesHomologyOfExact _
  have : IsIso (adj_b.unit.app ((𝟭 _).obj N)) := isIso_abelianTotalAdjunctionOver_unit_app P h N
  exact Adjunction.isZero_rightDerived_of_comp_iso
    (abelianInverseImageAdjPushforward (SimplicialOver.totalTopology P.toGrothendieck U)
      (augmentationMorphismOfTopoi P.toGrothendieck U a))
    E.toAdjunction adj_b Adjunction.id (augmentationAbelianPushforwardSquareIso U a P) N
    (fun q hq ↦ Stacks.Cohomology.isZero_rightDerived_obj_of_preservesHomology _ _ q hq)
    (fun q hq ↦
      SimplicialSemiRepresentable.isZero_rightDerived_abelianTotalPushforwardOver_of_isHypercovering
        P U a h N q hq)
    (fun q hq ↦ Stacks.Cohomology.isZero_rightDerived_obj_of_preservesHomology _ _ q hq) q hq

/-- `isIso_augmentationAbelianUnit_app` for a topology `J` given as the one generated by the
pretopology `P` the hypercovering conditions are stated with. -/
theorem isIso_augmentationAbelianUnit_app_of_eq {J : GrothendieckTopology C}
    (hJ : P.toGrothendieck = J) (h : IsHypercoveringAugmentation P U a)
    (N : Sheaf (J.over X) AddCommGrpCat.{u}) :
    IsIso ((abelianInverseImageAdjPushforward (SimplicialOver.totalTopology J U)
      (augmentationMorphismOfTopoi J U a)).unit.app N) := by
  subst hJ
  exact isIso_augmentationAbelianUnit_app P h N

/-- `isZero_rightDerived_augmentationAbelianPushforward` for a topology `J` given as the one
generated by the pretopology `P` the hypercovering conditions are stated with. -/
theorem isZero_rightDerived_augmentationAbelianPushforward_of_eq {J : GrothendieckTopology C}
    (hJ : P.toGrothendieck = J) (h : IsHypercoveringAugmentation P U a)
    (N : Sheaf (J.over X) AddCommGrpCat.{u}) (q : ℕ) (hq : 0 < q) :
    IsZero (((abelianPushforward (SimplicialOver.totalTopology J U)
      (augmentationMorphismOfTopoi J U a)).rightDerived q).obj
        ((Sites.abelianInverseImage (augmentationMorphismOfTopoi J U a)).obj N)) := by
  subst hJ
  exact isZero_rightDerived_augmentationAbelianPushforward P h N q hq

end Descent

end CategoryTheory.SimplicialOver

end
