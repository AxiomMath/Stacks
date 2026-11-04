module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringSimplicialObjectModuleCohomologicalDescentUnconditional
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleBoundedBelowEquivalence
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.StructureSheafAugmentation
public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableSummandRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomOfRestriction
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization

/-!
# The augmentation of a hypercovering of an object, with the restricted structure sheaf

Let `C` be a site with fibre products, given by a pretopology, `O_C` a sheaf of commutative rings
on it, `X` an object of `C` and `K` a simplicial semi-representable object of `C/X`. The total
site `(C/K)_total` carries the sheaf of rings `O`, the restriction of `O_X = O_C|_{C/X}` along
the localization functor `j_total`, and the augmentation of Stacks 0D70 is a morphism of ringed
topoi `a : (Sh((C/K)_total), O) ⟶ (Sh(C/X), O_X)` whose structure map identifies `a⁻¹O_X` with
`O` (Remark 0D9X). This file records that ringed augmentation and, for a hypercovering `K` of
`X`, the descent statements Stacks 0DA4 and Stacks 0DA5 for it, together with the consequence of
Stacks 0D7S that the derived counit `La^*Ra_*E ⟶ E` is invertible on bounded below objects with
cartesian cohomology modules.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.structureSheafAugmentation`: the ringed
  augmentation with structure sheaf `O = j_total⁻¹O_X`.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.isIso_derivedUnit_structureSheafAugmentation`:
  for a hypercovering `K`, the derived unit `E ⟶ Ra_*La^*E` is invertible on `D(O_X)`.
* `CategoryTheory.SimplicialSemiRepresentable.isIso_derivedCounit_structureSheafAugmentation`:
  for a hypercovering `K`, the derived counit `La^*Ra_*M ⟶ M` is invertible at every bounded
  below `M` whose cohomology modules are cartesian.

## Implementation notes

The ringed augmentation of Stacks 0D9X recorded as
`CategoryTheory.SimplicialSemiRepresentable.hypercoveringObjectRingedAugmentation` takes the
inverse image `a⁻¹O_X` itself as structure sheaf. The one here takes the restriction along
`j_total`, which is the structure sheaf of the total ringed site on which Stacks 0DCA produces
its objects (`CategoryTheory.SimplicialSemiRepresentable.structureSheaf`). The descent proofs of
the former use of its structure sheaf only that the structure map is invertible, and are
repeated here for the latter.

## References

* [Stacks Project, Tag 0D9X](https://stacks.math.columbia.edu/tag/0D9X)
* [Stacks Project, Tag 0DA4](https://stacks.math.columbia.edu/tag/0DA4)
* [Stacks Project, Tag 0DA5](https://stacks.math.columbia.edu/tag/0DA5)
* [Stacks Project, Tag 0D7S](https://stacks.math.columbia.edu/tag/0D7S)
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

section TotalTopology

variable {D : Type u} [SmallCategory D] (J : GrothendieckTopology D) [J.toCoverage.HasPullbacks]
  (K : SimplicialObject (FormalCoproduct.{u} D))

/-- `CategoryTheory.SimplicialSemiRepresentable.totalForget_isContinuous`, stated with the category
structure of the total site of the simplicial-site situation, in which the restriction functors of
the situation are written. -/
instance totalForget_isContinuous_totalTopology :
    @Functor.IsContinuous (situation J K).totalCategory (situation J K).totalCategory.str D _
      (totalForget K) (situation J K).totalTopology J :=
  totalForget_isContinuous J K

/-- Restriction of sheaves of sets along `j_total` preserves finite products, being a right
adjoint. -/
instance preservesFiniteProducts_totalForget_sheafPushforwardContinuous :
    PreservesFiniteProducts (@Functor.sheafPushforwardContinuous (situation J K).totalCategory
      (situation J K).totalCategory.str D _ (totalForget K) (Type u) _
      (situation J K).totalTopology J (totalForget_isContinuous_totalTopology J K)) :=
  ⟨fun _ => ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (totalForget K)
      (Type u) (situation J K).totalTopology J).rightAdjoint_preservesLimits.{0, 0}
      ).preservesLimitsOfShape⟩

/-- Restriction of sheaves of sets along `j_total` preserves finite products, being a right
adjoint; stated with the category structure of the localization functor. -/
instance preservesFiniteProducts_totalForget_sheafPushforwardContinuous' :
    PreservesFiniteProducts ((totalForget K).sheafPushforwardContinuous (Type u)
      (situation J K).totalTopology J) :=
  ⟨fun _ => ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (totalForget K)
      (Type u) (situation J K).totalTopology J).rightAdjoint_preservesLimits.{0, 0}
      ).preservesLimitsOfShape⟩

/-- `CategoryTheory.SimplicialSemiRepresentable.totalForget_isContinuous`, stated with the topology
of a ringed topos of the total site. -/
instance totalForget_isContinuous_totalRingedTopos (O : Sheaf (situation J K).totalTopology
    CommRingCat.{u}) :
    (totalForget K).IsContinuous ((situation J K).totalRingedTopos O).J J :=
  totalForget_isContinuous J K

end TotalTopology

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))
  (OC : Sheaf P.toGrothendieck CommRingCat.{u})

/-- The localized topology of `(C, O_C)` at `X` has pullbacks. Not an instance: as one it would
be tried, and leave the sheaf of rings undetermined, at every site of the form `J.over X`. -/
theorem pretopologyRingedSite_over_hasPullbacks :
    ((pretopologyRingedSite P OC).over X).J.toCoverage.HasPullbacks :=
  inferInstanceAs ((P.toGrothendieck.over X).toCoverage.HasPullbacks)

/-- The sheaf of rings `O = j_total⁻¹O_X` on the total site. -/
abbrev totalStructureSheaf : Sheaf (situation (P.toGrothendieck.over X) K).totalTopology
    CommRingCat.{u} :=
  @structureSheaf ((pretopologyRingedSite P OC).over X)
    (pretopologyRingedSite_over_hasPullbacks P OC) K

/-- **Stacks 0D8B on inverse images.** The inverse image of the morphism of topoi of Stacks 0D70
attached to the augmentation of the simplicial-site situation of `K` is restriction along
`j_total`. -/
def situationTotalInverseImageRestrictionIso :
    (Augmentation.totalMorphismOfTopoi (situation (P.toGrothendieck.over X) K) (Cat.of (Over X))
        (P.toGrothendieck.over X)
        (situationAugmentation (P.toGrothendieck.over X) K)).inverseImage ≅
      (totalForget K).sheafPushforwardContinuous (Type u)
        (situation (P.toGrothendieck.over X) K).totalTopology (P.toGrothendieck.over X) :=
  CocontinuousSimplicialSite.Augmentation.totalInverseImageIso
      (augmentation (P.toGrothendieck.over X) K) ≪≫
    totalInverseImageIso (P.toGrothendieck.over X) K

/-- **The ringed augmentation of Remark 0D9X with the restricted structure sheaf**: the total
site carries `O = j_total⁻¹O_X`, and the structure map is the adjunct of the identification
`a⁻¹O_X ≅ O`. -/
def structureSheafAugmentation :
    RingedAugmentation (situation (P.toGrothendieck.over X) K) (Cat.of (Over X))
      (P.toGrothendieck.over X) (situationAugmentation (P.toGrothendieck.over X) K) where
  O := totalStructureSheaf P K OC
  OD := OC.over X
  aSharp := (commRingImageAdjunction (Augmentation.totalMorphismOfTopoi
    (situation (P.toGrothendieck.over X) K) (Cat.of (Over X)) (P.toGrothendieck.over X)
    (situationAugmentation (P.toGrothendieck.over X) K))).homEquiv _ _
      (@structureSheafInverseImageIso ((pretopologyRingedSite P OC).over X)
      (pretopologyRingedSite_over_hasPullbacks P OC) K).hom

/-- The structure map of the ringed augmentation, in inverse-image form, is the identification
`a⁻¹O_X ≅ O`. -/
theorem structureSheafAugmentation_fSharpInverseImage :
    (structureSheafAugmentation P K OC).totalRingedHom.fSharpInverseImage =
      (@structureSheafInverseImageIso ((pretopologyRingedSite P OC).over X)
      (pretopologyRingedSite_over_hasPullbacks P OC) K).hom :=
  Equiv.symm_apply_apply _ _

/-- The structure map `a⁻¹O_X ⟶ O` of the ringed augmentation, in inverse-image form, is an
isomorphism. -/
instance isIso_structureSheafAugmentation_fSharpInverseImage :
    IsIso (structureSheafAugmentation P K OC).totalRingedHom.fSharpInverseImage := by
  rw [structureSheafAugmentation_fSharpInverseImage]
  exact (@structureSheafInverseImageIso ((pretopologyRingedSite P OC).over X)
      (pretopologyRingedSite_over_hasPullbacks P OC) K).isIso_hom

/-! ### Descent along the augmentation of a hypercovering of `X` -/

variable {P K OC}

/-- **Stacks 0DA4**: for a hypercovering `K` of `X`, the pullback of sheaves of modules along the
augmentation is fully faithful. -/
def fullyFaithfulPullbackModulesStructureSheaf (hK : IsHypercovering P K) :
    (structureSheafAugmentation P K OC).totalRingedHom.toModulesHom.pullbackModules.FullyFaithful :=
  haveI := RingedAugmentation.full_pullbackModules_of_full_inverseImage
    (structureSheafAugmentation P K OC) (full_situationTotalInverseImage_over P K hK)
    (faithful_situationTotalInverseImage_over P K hK)
  haveI := RingedAugmentation.faithful_pullbackModules_of_faithful_inverseImage
    (structureSheafAugmentation P K OC) (faithful_situationTotalInverseImage_over P K hK)
  Functor.FullyFaithful.ofFullyFaithful _

/-- **Stacks 0DA4**: for a hypercovering `K` of `X`, every cartesian sheaf of modules on the
total site is a pullback. -/
theorem essImage_pullbackModules_structureSheaf (hK : IsHypercovering P K)
    {F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (situation (P.toGrothendieck.over X) K).totalTopology)
      (structureSheafAugmentation P K OC).O)}
    (hF : (situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
      (structureSheafAugmentation P K OC).O F) :
    (structureSheafAugmentation P K OC).totalRingedHom.toModulesHom.pullbackModules.essImage F :=
  RingedAugmentation.essImage_pullbackModules_of_isCartesianModule
    (structureSheafAugmentation P K OC)
    (full_situationTotalInverseImage_over P K hK)
    (faithful_situationTotalInverseImage_over P K hK)
    (fun G hG => essImage_situationTotalInverseImage_of_isCartesianSheaf_over P K hK G hG) hF

/-- The unit `M ⟶ a_*a^*M` of the adjunction of Stacks 03D7 is an isomorphism, for a
hypercovering. -/
theorem isIso_pullbackAdjPushforwardModules_unit_structureSheaf (hK : IsHypercovering P K) :
    IsIso (RingedToposHom.pullbackAdjPushforwardModules
      (structureSheafAugmentation P K OC).totalRingedHom).unit :=
  have := (fullyFaithfulPullbackModulesStructureSheaf (OC := OC) hK).full
  have := (fullyFaithfulPullbackModulesStructureSheaf (OC := OC) hK).faithful
  Adjunction.unit_isIso_of_L_fully_faithful _

section Over

attribute [local instance] additive_abelianTotalPushforwardOver
  additive_abelianTotalInverseImageOver preservesFiniteColimits_abelianTotalInverseImageOver
  hasPointwiseRightDerivedFunctor_homotopyAbelianTotalPushforwardOver
  hasRightDerivedFunctor_homotopyAbelianTotalPushforwardOver

variable (P K OC)

/-- The underlying abelian sheaf of the direct image of a sheaf of modules along the augmentation
is the direct image along `j_total` of its underlying abelian sheaf. -/
def structureSheafPushforwardModulesToSheafIso :
    (structureSheafAugmentation P K OC).totalRingedHom.pushforwardModules ⋙
        SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf _ ⋙ abelianTotalPushforwardOver P.toGrothendieck X K := by
  haveI : HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((situation (P.toGrothendieck.over X) K).totalRingedTopos
        (structureSheafAugmentation P K OC).O).O)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  haveI := Augmentation.additive_abelianTotalPushforward (situation (P.toGrothendieck.over X) K)
    (Cat.of (Over X)) (P.toGrothendieck.over X) (situationAugmentation (P.toGrothendieck.over X) K)
  refine Iso.trans ?_
    (Functor.isoWhiskerLeft _ (abelianTotalPushforwardOverIso P.toGrothendieck X K))
  exact @Stacks.Cohomology.abelianSheafNatIsoOfUnderlying _ _ _ _ _ _ _ _ _ inferInstance
    ⟨fun {_ _ f g} => ((Augmentation.abelianTotalPushforward _ _ _ _).congr_map
      ((SheafOfModules.toSheaf _).map_add (f := f) (g := g))).trans
        ((Augmentation.abelianTotalPushforward _ _ _ _).map_add)⟩ (Iso.refl _)

/-- The underlying abelian sheaf of the pullback of a sheaf of modules along the augmentation is
the restriction along `j_total` of its underlying abelian sheaf. -/
def structureSheafPullbackModulesToSheafIso :
    (structureSheafAugmentation P K OC).totalRingedHom.toModulesHom.pullbackModules ⋙
        SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf _ ⋙ abelianTotalInverseImageOver P.toGrothendieck X K := by
  haveI : HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (structureSheafAugmentation P K OC).augmentationRingedTopos.O)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  refine Iso.trans ?_ (Functor.isoWhiskerLeft _
    (situationTotalInverseImageAbIso (P.toGrothendieck.over X) K))
  exact @Stacks.Cohomology.abelianSheafNatIsoOfUnderlying _ _ _ _ _ _ _ _ _
    (inferInstanceAs ((structureSheafAugmentation P K
      OC).totalRingedHom.toModulesHom.pullbackModules ⋙ SheafOfModules.toSheaf _).Additive)
    ⟨fun {_ _ f g} => ((Augmentation.totalInverseImageAb _ _ _ _).congr_map
      ((SheafOfModules.toSheaf _).map_add (f := f) (g := g))).trans
        ((Augmentation.totalInverseImageAb _ _ _ _).map_add)⟩
    (RingedToposHom.pullbackUnderlyingIsoOfIsIso
      (structureSheafAugmentation P K OC).totalRingedHom)

variable {P K OC}

/-- **For a hypercovering of `X`, `a^*` of a K-injective complex of `O_X`-modules computes
`Ra_*`.** -/
theorem pullbackComputesDerivedPushforward_structureSheaf (hK : IsHypercovering P K) :
    RingedToposHom.PullbackComputesDerivedPushforward.{u}
      (structureSheafAugmentation P K OC).totalRingedHom := by
  intro I hI
  have hU := fun (I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((situation (P.toGrothendieck.over X) K).totalRingedTopos
        (structureSheafAugmentation P K OC).O).O)) ℤ)
      (hI' : I'.IsKInjective) =>
    @Stacks.Cohomology.CocontinuousForgetModule.abelianPushforwardUnit_isIso_at_underlying_kInjective
      _ _ _ _ (situation (P.toGrothendieck.over X) K).totalTopology (P.toGrothendieck.over X)
      (totalForget K) (totalForget_isCocontinuous (P.toGrothendieck.over X) K) _ _ _
      (Stacks.SheafOfModules.Tensor.ringSheaf
      ((situation (P.toGrothendieck.over X) K).totalRingedTopos
        (structureSheafAugmentation P K OC).O).O) I' hI'
  let eP := structureSheafPullbackModulesToSheafIso P K OC
  let ι : ((SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((situation (P.toGrothendieck.over X) K).totalRingedTopos
        (structureSheafAugmentation P K OC).O).O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((structureSheafAugmentation P K
          OC).totalRingedHom.toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≅
      ((abelianTotalInverseImageOver P.toGrothendieck X K).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (structureSheafAugmentation P K OC).augmentationRingedTopos.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) :=
    HomologicalComplex.Hom.isoOfComponents (fun i => eP.app (I.X i))
      (fun i j _ => (eP.hom.naturality (I.d i j)).symm)
  have hK' := (NatTrans.isIso_app_iff_of_iso
    (derivedAbelianTotalPushforwardOverUnit P.toGrothendieck X K)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso ι)).mpr
      (isIso_derivedAbelianTotalPushforwardOverUnit_app_inverseImage_of_isHypercovering P K hK
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((SheafOfModules.toSheaf _).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
  exact @Stacks.Cohomology.UnboundedComplexes.isIso_rightDerivedUnit_of_forget
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (structureSheafAugmentation P K OC).totalRingedHom.pushforwardModules
    (abelianTotalPushforwardOver P.toGrothendieck X K)
    (SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((situation (P.toGrothendieck.over X) K).totalRingedTopos
        (structureSheafAugmentation P K OC).O).O))
    (SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (structureSheafAugmentation P K OC).augmentationRingedTopos.O))
    _ _ ⟨fun {_ _ f g} => (SheafOfModules.toSheaf _).map_add (f := f) (g := g)⟩
    ⟨fun {_ _ f g} => (SheafOfModules.toSheaf _).map_add (f := f) (g := g)⟩
    (inferInstance : PreservesFiniteLimits (SheafOfModules.toSheaf.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
      ((situation (P.toGrothendieck.over X) K).totalRingedTopos
        (structureSheafAugmentation P K OC).O).O)))
    (Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf _)
    (inferInstance : PreservesFiniteLimits (SheafOfModules.toSheaf.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
      (structureSheafAugmentation P K OC).augmentationRingedTopos.O)))
    (Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf _)
    (inferInstance : (SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (structureSheafAugmentation P K OC).augmentationRingedTopos.O)).ReflectsIsomorphisms)
    (structureSheafPushforwardModulesToSheafIso P K OC)
    _ (derivedAbelianTotalPushforwardOver P.toGrothendieck X K) _
    (derivedAbelianTotalPushforwardOverUnit P.toGrothendieck X K) _ hU _ hK'

end Over

/-- **Stacks 0DA5** for the augmentation with the restricted structure sheaf: for a
hypercovering `K` of `X`, the derived unit `E ⟶ Ra_*La^*E` is an isomorphism for every object
`E` of `D(O_X)`. -/
theorem isIso_derivedUnit_structureSheafAugmentation (hK : IsHypercovering P K)
    (E : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (structureSheafAugmentation P K OC).augmentationRingedTopos.J))
      (structureSheafAugmentation P K OC).augmentationRingedTopos.O))) :
    IsIso ((AlgebraicGeometry.RingedToposHom.derivedAdjunctionOfIsIsoFSharp
      (structureSheafAugmentation P K OC).totalRingedHom).unit.app E) :=
  have := AlgebraicGeometry.RingedToposHom.isIso_derivedPullbackPushforwardUnit
    (structureSheafAugmentation P K OC).totalRingedHom
    (isIso_pullbackAdjPushforwardModules_unit_structureSheaf hK)
    (pullbackComputesDerivedPushforward_structureSheaf hK)
  NatIso.isIso_app_of_isIso _ E

/-- **Stacks 0D7S for the augmentation with the restricted structure sheaf**: for a
hypercovering `K` of `X`, the derived counit `La^*Ra_*M ⟶ M` is an isomorphism at every bounded
below object `M` of `D(O)` whose cohomology modules are cartesian. -/
theorem isIso_derivedCounit_structureSheafAugmentation (hK : IsHypercovering P K)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((situation (P.toGrothendieck.over X) K).totalRingedTopos
        (structureSheafAugmentation P K OC).O).O)))
    (hM : AlgebraicGeometry.RingedToposHom.derivedPlusProperty
      (X := (situation (P.toGrothendieck.over X) K).totalRingedTopos
        (structureSheafAugmentation P K OC).O)
      ((situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
        (structureSheafAugmentation P K OC).O) M) :
    IsIso ((AlgebraicGeometry.RingedToposHom.derivedAdjunctionOfIsIsoFSharp
      (structureSheafAugmentation P K OC).totalRingedHom).counit.app M) :=
  AlgebraicGeometry.RingedToposHom.isIso_derivedCounit_app_of_property
    (structureSheafAugmentation P K OC).totalRingedHom
    ((situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
      (structureSheafAugmentation P K OC).O)
    (fun E => isIso_derivedUnit_structureSheafAugmentation hK E)
    (fun _ hF => essImage_pullbackModules_structureSheaf hK hF) M hM

end CategoryTheory.SimplicialSemiRepresentable

end
