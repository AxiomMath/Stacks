module

public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.StructureSheafAugmentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleCongr
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars

/-!
# The pullback along the augmentation is restriction along `j_total`

For the ringed augmentation `a : (Sh((C/K)_total), O) ⟶ (Sh(C/X), O_X)` with `O = j_total⁻¹O_X`
(`CategoryTheory.SimplicialSemiRepresentable.structureSheafAugmentation`), the pullback of
sheaves of modules `a^*` is restriction along the localization functor `j_total`, and so is
`La^*` on derived categories: the source's identity `La^* = a^* = a⁻¹` of Remark 0D9W.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.totalRestrictionModules`: restriction of sheaves
  of `O_X`-modules along `j_total`.
* `CategoryTheory.SimplicialSemiRepresentable.pullbackModulesIsoTotalRestriction`: `a^*` is that
  restriction.
* `CategoryTheory.SimplicialSemiRepresentable.derivedPullbackIsoTotalRestriction`: `La^*` is
  that restriction applied to complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.CategoryTheory.Hypercovering Stacks.Sheaves.ToposPullback
  Stacks.Sheaves.ToposPushforward

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SimplicialSiteSituation

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))
  (OC : Sheaf P.toGrothendieck CommRingCat.{u})

/-- **Restriction of sheaves of `O_X`-modules along the localization functor `j_total`**, with
the identity structure map: the structure sheaf of the total site is the restriction of `O_X`. -/
abbrev totalRestrictionModules :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := (structureSheafAugmentation P K OC).augmentationRingedTopos.J)
        (structureSheafAugmentation P K OC).augmentationRingedTopos.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := ((situation (P.toGrothendieck.over X) K).totalRingedTopos
          (structureSheafAugmentation P K OC).O).J)
        ((situation (P.toGrothendieck.over X) K).totalRingedTopos
          (structureSheafAugmentation P K OC).O).O) :=
  @SheafOfModules.pushforward _ _ _ _ _ _ (totalForget K) _ _
    (by exact totalForget_isContinuous _ K) (𝟙 _)

/-- A functor isomorphic to a left exact functor preserves finite products. -/
theorem preservesFiniteProducts_of_natIso_of_preservesFiniteLimits {A B : Type*} [Category A]
    [Category B] {F G : A ⥤ B} (e : F ≅ G) (hF : PreservesFiniteLimits F) :
    PreservesFiniteProducts G :=
  ⟨fun _ => have := hF.preservesFiniteLimits; preservesLimitsOfShape_of_natIso e⟩

/-- The restriction along `j_total` preserves finite products, in the form in which it is the
target of `situationTotalInverseImageRestrictionIso`. -/
theorem preservesFiniteProducts_situationTotalRestriction :
    PreservesFiniteProducts ((totalForget K).sheafPushforwardContinuous (Type u)
      (situation (P.toGrothendieck.over X) K).totalTopology (P.toGrothendieck.over X)) :=
  preservesFiniteProducts_of_natIso_of_preservesFiniteLimits
    (situationTotalInverseImageRestrictionIso P K)
    (Augmentation.totalMorphismOfTopoi (situation (P.toGrothendieck.over X) K)
      (Cat.of (Over X)) (P.toGrothendieck.over X)
      (situationAugmentation (P.toGrothendieck.over X) K)).preservesFiniteLimits

/-- The ring map identifying the structure sheaf of the total site with the restriction of
`O_X`, read through the pullback of modules: it is the identity. -/
theorem pullbackRingSheafCongr_restriction_comp :
    ((asIso
        (structureSheafAugmentation P K OC).totalRingedHom.toModulesHom.fSharpInverseImage).inv ≫
      (pullbackRingSheafCongr (situation (P.toGrothendieck.over X) K).totalTopology
        (hΨ := preservesFiniteProducts_situationTotalRestriction P K)
        (situationTotalInverseImageRestrictionIso P K)
        (Stacks.SheafOfModules.Tensor.ringSheaf (OC.over X))).hom) ≫
      (restrictionRingIso (situation (P.toGrothendieck.over X) K).totalTopology
        (P.toGrothendieck.over X) (totalForget K)
        (Stacks.SheafOfModules.Tensor.ringSheaf (OC.over X))).hom = 𝟙 _ := by
  refine (Category.assoc _ _ _).trans
    ((Iso.inv_comp_eq _).2 (Eq.trans ?_ (Category.comp_id _).symm))
  refine Eq.symm (((structureSheafAugmentation P K
    OC).totalRingedHom.forgetCommRingSheaf_map_fSharpInverseImage).symm.trans ?_)
  refine (congrArg (Stacks.forgetCommRingSheaf ((situation (P.toGrothendieck.over X)
    K).totalRingedTopos (structureSheafAugmentation P K OC).O).J).map
    (structureSheafAugmentation_fSharpInverseImage P K OC)).trans ?_
  apply Sheaf.hom_ext
  ext Y x
  rfl

/-- **The pullback of sheaves of modules along the augmentation is restriction along
`j_total`.** -/
def pullbackModulesIsoTotalRestriction :
    (structureSheafAugmentation P K OC).totalRingedHom.toModulesHom.pullbackModules ≅
      totalRestrictionModules P K OC := by
  refine Functor.isoWhiskerLeft _
    (Stacks.Sheaves.RingedToposModules.RingedToposHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso
      (structureSheafAugmentation P K OC).totalRingedHom.toModulesHom) ≪≫ ?_
  refine Functor.isoWhiskerRight (pullbackModuleFunctorCongr
      (situation (P.toGrothendieck.over X) K).totalTopology
      (hΨ := preservesFiniteProducts_situationTotalRestriction P K)
      (situationTotalInverseImageRestrictionIso P K)
      (Stacks.SheafOfModules.Tensor.ringSheaf (OC.over X))) _ ≪≫ ?_
  refine Functor.isoWhiskerRight (Functor.isoWhiskerRight (restrictionModuleIso
      (situation (P.toGrothendieck.over X) K).totalTopology (P.toGrothendieck.over X)
      (totalForget K) (Stacks.SheafOfModules.Tensor.ringSheaf (OC.over X))) _) _ ≪≫ ?_
  refine Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (eqToIso (Stacks.Sheaves.RingedToposModules.restrictScalars_comp _ _)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (eqToIso (Stacks.Sheaves.RingedToposModules.restrictScalars_comp _ _)) ≪≫
    eqToIso (restrictionModules_comp_restrictScalars
      (situation (P.toGrothendieck.over X) K).totalTopology (P.toGrothendieck.over X)
      (totalForget K) (Stacks.SheafOfModules.Tensor.ringSheaf (OC.over X)) _) ≪≫ ?_
  exact SheafOfModules.pushforwardCongr (pullbackRingSheafCongr_restriction_comp P K OC)

/-- Restriction of sheaves of modules along `j_total` is an additive functor. -/
instance totalRestrictionModules_additive : (totalRestrictionModules P K OC).Additive :=
  ⟨by intros; ext; rfl⟩

/-- Restriction of sheaves of modules along `j_total` preserves finite limits. -/
instance totalRestrictionModules_preservesFiniteLimits :
    PreservesFiniteLimits (totalRestrictionModules P K OC) :=
  haveI := AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteLimits_of_isIso_fSharp
    (structureSheafAugmentation P K OC).totalRingedHom
  preservesFiniteLimits_of_natIso (pullbackModulesIsoTotalRestriction P K OC)

/-- Restriction of sheaves of modules along `j_total` preserves finite colimits. -/
instance totalRestrictionModules_preservesFiniteColimits :
    PreservesFiniteColimits (totalRestrictionModules P K OC) :=
  haveI := AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits_of_adjunction
    (structureSheafAugmentation P K OC).totalRingedHom
  preservesFiniteColimits_of_natIso (pullbackModulesIsoTotalRestriction P K OC)

end CategoryTheory.SimplicialSemiRepresentable

namespace AlgebraicGeometry.RingedToposHom

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposHom X Y) [IsIso f.fSharpInverseImage]

attribute [local instance] pullbackModules_preservesFiniteLimits_of_isIso_fSharp
  pullbackModules_preservesFiniteColimits_of_adjunction

/-- **`La^*` is the functor induced on derived categories by the exact functor `a^*`**, for a
morphism of ringed topoi with invertible structure map, naturally. -/
def derivedPullbackIsoMapDerivedCategory :
    (leftDerivedPullbackOfIsIsoFSharp f).functor ≅
      f.toModulesHom.pullbackModules.mapDerivedCategory :=
  haveI := isIso_derivedPullbackComparison f
  letI : Localization.Lifting DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      (Stacks.Cohomology.DerivedPushforward.pullbackOnHomotopy f)
      (leftDerivedPullbackOfIsIsoFSharp f).functor :=
    ⟨asIso (leftDerivedPullbackOfIsIsoFSharp f).comparison⟩
  Localization.liftNatIso DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (Stacks.Cohomology.DerivedPushforward.pullbackOnHomotopy f)
    (f.toModulesHom.pullbackModules.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh) _ _ (Iso.refl _)

end AlgebraicGeometry.RingedToposHom

namespace CategoryTheory.SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))
  (OC : Sheaf P.toGrothendieck CommRingCat.{u})

/-- **`La^*` is restriction along `j_total`, applied to complexes.** -/
def derivedPullbackIsoTotalRestriction :
    (AlgebraicGeometry.RingedToposHom.leftDerivedPullbackOfIsIsoFSharp
        (structureSheafAugmentation P K OC).totalRingedHom).functor ≅
      (totalRestrictionModules P K OC).mapDerivedCategory :=
  haveI := AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteLimits_of_isIso_fSharp
    (structureSheafAugmentation P K OC).totalRingedHom
  haveI := AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits_of_adjunction
    (structureSheafAugmentation P K OC).totalRingedHom
  AlgebraicGeometry.RingedToposHom.derivedPullbackIsoMapDerivedCategory
      (structureSheafAugmentation P K OC).totalRingedHom ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (pullbackModulesIsoTotalRestriction P K OC)

end CategoryTheory.SimplicialSemiRepresentable

end
