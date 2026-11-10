module

public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableSummandRestriction
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleCohomologicalDescentUnconditional
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleBoundedBelowEquivalence
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback

/-!
# The ringed augmentation of the total site with the restricted structure sheaf

Let `(C, O_C)` be a ringed site and `K` a simplicial semi-representable object of `C`. Remark 0D9W
puts on the total site `(C/K)_total` the sheaf of rings `O = a⁻¹O_C`. This development has two
spellings of that sheaf of rings: `CategoryTheory.SimplicialSemiRepresentable.structureSheaf`,
the restriction of `O_C` along the localization functor `j_total`, on which the simplicial
systems of Stacks 0DCA are built; and the inverse image of `O_C` along the morphism of topoi of
Stacks 0D70, on which `CategoryTheory.SimplicialSiteSituation.inverseImageRingedAugmentation` and
this library's Stacks 0DA0 are built. This file identifies the two and records the ringed
augmentation `a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` with `O` the restricted structure sheaf,
whose structure map is invertible.

It then proves, for an arbitrary ringed augmentation with invertible structure map, the two
facts about it from which this library's Stacks 0DA0 is assembled — the underlying abelian
sheaves of `a^*M` and of `a_*F` are the abelian inverse and direct images — and deduces, for a
hypercovering, that `E ⟶ Ra_*La^*E` is an isomorphism for the ringed augmentation with the
restricted structure sheaf, and that `La^*` is fully faithful.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.structureSheafInverseImageIso`: `a⁻¹O_C` is the
  restricted structure sheaf.
* `CategoryTheory.SimplicialSemiRepresentable.structureAugmentation`: the ringed augmentation
  with the restricted structure sheaf.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.structureAugmentation_fSharpInverseImage`: its
  structure map in inverse-image form is `structureSheafInverseImageIso`.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation`
  `.pullbackComputesDerivedPushforward_of_isIso`: the reduction of Stacks 0DA0 to abelian sheaves,
  for any ringed augmentation with invertible structure map.
* `CategoryTheory.SimplicialSemiRepresentable.isIso_structureAugmentation_derivedUnit`:
  Stacks 0DA0 for the ringed augmentation with the restricted structure sheaf.

## References

* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
* [Stacks Project, Tag 0DA0](https://stacks.math.columbia.edu/tag/0DA0)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.CategoryTheory.Hypercovering Stacks.Sheaves.ToposPullback
  Stacks.Sheaves.ToposPushforward

attribute [local instance] HasDerivedCategory.standard

universe u

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

namespace CategoryTheory.SimplicialSiteSituation.RingedAugmentation

variable {S : SimplicialSiteSituation.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  {a : Augmentation S D K} (A : RingedAugmentation S D K a)

/-- The underlying abelian sheaf of the direct image of a sheaf of modules along a ringed
augmentation is the direct image of its underlying abelian sheaf: on underlying sheaves of sets
the direct image of modules is the direct image of the morphism of topoi of Stacks 0D70. -/
def pushforwardToSheafIso :
    A.totalRingedHom.pushforwardModules ⋙ SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf _ ⋙ Augmentation.abelianTotalPushforward S D K a := by
  have : HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (S.totalRingedTopos A.O).O)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have := Augmentation.additive_abelianTotalPushforward S D K a
  exact @Stacks.Cohomology.abelianSheafNatIsoOfUnderlying _ _ _ _ _ _ _ _ _ inferInstance
    ⟨fun {_ _ f g} => ((Augmentation.abelianTotalPushforward S D K a).congr_map
      ((SheafOfModules.toSheaf _).map_add (f := f) (g := g))).trans
        ((Augmentation.abelianTotalPushforward S D K a).map_add)⟩ (Iso.refl _)

/-- The underlying abelian sheaf of the pullback of a sheaf of modules along a ringed
augmentation with invertible structure map is the inverse image of its underlying abelian
sheaf. -/
def pullbackToSheafIso [IsIso A.totalRingedHom.fSharpInverseImage] :
    A.totalRingedHom.toModulesHom.pullbackModules ⋙ SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf _ ⋙ Augmentation.totalInverseImageAb S D K a := by
  have : HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      A.augmentationRingedTopos.O)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  exact @Stacks.Cohomology.abelianSheafNatIsoOfUnderlying _ _ _ _ _ _ _ _ _
    (inferInstanceAs (A.totalRingedHom.toModulesHom.pullbackModules ⋙
      SheafOfModules.toSheaf _).Additive)
    ⟨fun {_ _ f g} => ((Augmentation.totalInverseImageAb S D K a).congr_map
      ((SheafOfModules.toSheaf _).map_add (f := f) (g := g))).trans
        ((Augmentation.totalInverseImageAb S D K a).map_add)⟩
    (RingedToposHom.pullbackUnderlyingIsoOfIsIso A.totalRingedHom)

/-- **`a^*` of a K-injective complex computes `Ra_*`, for any ringed augmentation with invertible
structure map**, granted the two abelian facts: the underlying abelian complex of a K-injective
complex of modules on the total site computes the abelian `Ra_*`, and `a⁻¹` of every complex of
abelian sheaves computes `Ra_*`. -/
theorem pullbackComputesDerivedPushforward_of_isIso [IsIso A.totalRingedHom.fSharpInverseImage]
    (hU : ∀ (O : Sheaf S.totalTopology RingCat.{u}) (I : CochainComplex (SheafOfModules.{u} O) ℤ),
      I.IsKInjective → IsIso ((Augmentation.derivedTotalPushforwardUnit S D K a).app
        ((HomotopyCategory.quotient (Sheaf S.totalTopology AddCommGrpCat.{u})
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))))
    (hinv : ∀ M : HomotopyCategory (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ),
      IsIso ((Augmentation.derivedTotalPushforwardUnit S D K a).app
        (((Augmentation.totalInverseImageAb S D K a).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj M))) :
    RingedToposHom.PullbackComputesDerivedPushforward.{u} A.totalRingedHom := by
  intro I hI
  let UT := SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (S.totalRingedTopos A.O).O)
  let UC := SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    A.augmentationRingedTopos.O)
  have hU' := fun (I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (S.totalRingedTopos A.O).O)) ℤ) (hI' : I'.IsKInjective) =>
    (NatTrans.isIso_app_iff_of_iso _
      ((Functor.mapHomotopyCategoryFactors UT (ComplexShape.up ℤ)).app I')).mpr
      (hU _ I' hI')
  let eP := A.pullbackToSheafIso
  let ι : (UT.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((A.totalRingedHom.toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≅
      ((Augmentation.totalInverseImageAb S D K a).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((UC.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    HomologicalComplex.Hom.isoOfComponents (fun i => eP.app (I.X i))
      (fun i j _ => (eP.hom.naturality (I.d i j)).symm)
  have hK' := (NatTrans.isIso_app_iff_of_iso
    (Augmentation.derivedTotalPushforwardUnit S D K a)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso ι)).mpr
      (hinv ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((UC.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
  have := Augmentation.additive_abelianTotalPushforward S D K a
  exact @Stacks.Cohomology.UnboundedComplexes.isIso_rightDerivedUnit_of_forget
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    A.totalRingedHom.pushforwardModules (Augmentation.abelianTotalPushforward S D K a)
    UT UC _ _ ⟨fun {_ _ f g} => UT.map_add (f := f) (g := g)⟩
    ⟨fun {_ _ f g} => UC.map_add (f := f) (g := g)⟩
    (inferInstance : PreservesFiniteLimits UT)
    (Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf _)
    (inferInstance : PreservesFiniteLimits UC)
    (Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf _)
    (inferInstance : UC.ReflectsIsomorphisms)
    A.pushforwardToSheafIso
    _ (Augmentation.derivedTotalPushforward S D K a) _
    (Augmentation.derivedTotalPushforwardUnit S D K a) _ hU' _ hK'

section Hypercovering

open CategoryTheory.SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] {P : Pretopology C}
  (H : HypercoveringOfTerminal.{u, u} P)
  (B : RingedAugmentation (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C)
    P.toGrothendieck (situationAugmentation P.toGrothendieck H.toSimplicialObject))
  [IsIso B.totalRingedHom.fSharpInverseImage]

/-- **Stacks 0DA0 for any ringed augmentation of a hypercovering with invertible structure
map**: `E ⟶ Ra_*La^*E` is an isomorphism for every `E` in `D(O_C)`. -/
theorem isIso_derivedPullbackPushforwardUnit_of_hypercovering :
    IsIso (RingedToposHom.derivedPullbackPushforwardUnit B.totalRingedHom) :=
  RingedToposHom.isIso_derivedPullbackPushforwardUnit B.totalRingedHom
    (isIso_pullbackAdjPushforwardModules_unit H B)
    (pullbackComputesDerivedPushforward_of_isIso B
      (isIso_derivedTotalPushforwardUnit_app_underlying_of_isKInjective P.toGrothendieck
        H.toSimplicialObject)
      (isIso_derivedTotalPushforwardUnit_app_inverseImage_of_hypercoveringOfTerminal P H))

/-- **`La^*` is fully faithful** on `D(O_C)`, for a ringed augmentation of a hypercovering with
invertible structure map: its unit is invertible (Stacks 0DA0). -/
def derivedPullbackFullyFaithfulOfHypercovering :
    (RingedToposHom.leftDerivedPullbackOfIsIsoFSharp B.totalRingedHom).functor.FullyFaithful :=
  have := isIso_derivedPullbackPushforwardUnit_of_hypercovering H B
  (RingedToposHom.derivedAdjunctionOfIsIsoFSharp B.totalRingedHom).fullyFaithfulLOfIsIsoUnit

/-- **The counit `La^*Ra_*E ⟶ E` is invertible on `D⁺_𝒜(O)`**, `𝒜` the cartesian `O`-modules,
for a ringed augmentation of a hypercovering with invertible structure map: the
essential-surjectivity half of Stacks 0DA2. -/
theorem isIso_derivedCounit_app_of_hypercovering
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((situation P.toGrothendieck H.toSimplicialObject).totalRingedTopos B.O).O)))
    (hE : RingedToposHom.derivedPlusProperty
      (X := (situation P.toGrothendieck H.toSimplicialObject).totalRingedTopos B.O)
      ((situation P.toGrothendieck H.toSimplicialObject).IsModuleFiberTransitionIso B.O) E) :
    IsIso ((RingedToposHom.derivedAdjunctionOfIsIsoFSharp B.totalRingedHom).counit.app E) :=
  have _hunit := isIso_derivedPullbackPushforwardUnit_of_hypercovering H B
  RingedToposHom.isIso_derivedCounit_app_of_property B.totalRingedHom _
    (fun M => inferInstanceAs (IsIso ((RingedToposHom.derivedPullbackPushforwardUnit
      B.totalRingedHom).app M)))
    (fun _ hM => essImage_pullbackModules H B hM) E hE

end Hypercovering

end CategoryTheory.SimplicialSiteSituation.RingedAugmentation

namespace CategoryTheory.SimplicialSemiRepresentable

open CategoryTheory.SimplicialSiteSituation

variable (X : RingedSite.{u, u, u}) [X.J.toCoverage.HasPullbacks]
  (K : SimplicialObject (FormalCoproduct.{u} X.C))

/-- The comparison of Stacks 0D8B: the inverse image of the morphism of topoi of the
augmentation is restriction along `j_total`. -/
abbrev structureInverseImageIso :
    (Augmentation.totalMorphismOfTopoi (situation X.J K) (Cat.of X.C) X.J
        (situationAugmentation X.J K)).inverseImage ≅
      (totalLocalizationMorphism X.J K).inverseImage :=
  CocontinuousSimplicialSite.Augmentation.totalInverseImageIso (augmentation X.J K) ≪≫
    totalInverseImageIso X.J K

/-- **`a⁻¹O_C` is the restricted structure sheaf.** The inverse image of `O_C` along the morphism
of topoi of Stacks 0D70 is its restriction along the localization functor `j_total`: the inverse
image of that morphism of topoi is restriction along `j_total` (Stacks 0D8B), and the inverse
image of a sheaf of commutative rings along a restriction functor is the restriction. -/
def structureSheafInverseImageIso :
    (inverseImageCommRingFunctor.{u, u, u, u, u, u}
      (J := (situation X.J K).totalTopology) (K := X.J)
      (Augmentation.totalMorphismOfTopoi (situation X.J K)
      (Cat.of X.C) X.J (situationAugmentation X.J K))).obj X.O ≅ structureSheaf X K :=
  pullbackCommRingSheafIsoOfNatIso (situation X.J K).totalTopology
      (structureInverseImageIso X K) X.O ≪≫
    @restrictionCommRingIso _ _ _ _ (situation X.J K).totalTopology X.J _ (totalForget K)
      (totalForget_isContinuous X.J K) X.O

/-- On underlying sheaves of sets, `structureSheafInverseImageIso` is the comparison of
Stacks 0D8B of the inverse image of the augmentation with restriction along `j_total`. -/
theorem structureSheafInverseImageIso_hom_forget :
    (sheafCompose (situation X.J K).totalTopology (forget CommRingCat.{u})).map
        (structureSheafInverseImageIso X K).hom =
      (structureInverseImageIso X K).hom.app
        ((sheafCompose X.J (forget CommRingCat.{u})).obj X.O) :=
  ((sheafCompose (situation X.J K).totalTopology (forget CommRingCat.{u})).map_comp _ _).trans
    ((congrArg₂ (· ≫ ·)
      (pullbackCommRingSheafIsoOfNatIso_hom_forget (situation X.J K).totalTopology
        (structureInverseImageIso X K) X.O)
      (@restrictionCommRingIso_hom_forget _ _ _ _ (situation X.J K).totalTopology X.J _
        (totalForget K) (totalForget_isContinuous X.J K) X.O _ _)).trans (Category.comp_id _))

/-- **The ringed augmentation of Remark 0D9W with the restricted structure sheaf.** The total
site carries `O = structureSheaf X K`, the restriction of `O_C` along `j_total`, and the
structure map is the adjunct of the identification `a⁻¹O_C ≅ O` of
`structureSheafInverseImageIso`. -/
def structureAugmentation :
    RingedAugmentation (situation X.J K) (Cat.of X.C) X.J (situationAugmentation X.J K) where
  O := structureSheaf X K
  OD := X.O
  aSharp := (commRingImageAdjunction.{u, u, u, u, u, u}
      (J := (situation X.J K).totalTopology) (K := X.J)
      (Augmentation.totalMorphismOfTopoi (situation X.J K)
      (Cat.of X.C) X.J (situationAugmentation X.J K))).unit.app X.O ≫
    (pushforwardCommRingFunctor.{u, u, u, u, u, u} (J := (situation X.J K).totalTopology) (K := X.J)
      (Augmentation.totalMorphismOfTopoi (situation X.J K)
      (Cat.of X.C) X.J (situationAugmentation X.J K))).map (structureSheafInverseImageIso X K).hom

/-- The sheaf of rings on the total site of `structureAugmentation` is `structureSheaf X K`. -/
theorem structureAugmentation_O : (structureAugmentation X K).O = structureSheaf X K := rfl

/-- The sheaf of rings on the base of `structureAugmentation` is `O_C`. -/
theorem structureAugmentation_OD : (structureAugmentation X K).OD = X.O := rfl

/-- The structure map of `structureAugmentation`, in inverse-image form, is the identification
`a⁻¹O_C ≅ O` of `structureSheafInverseImageIso`. -/
theorem structureAugmentation_fSharpInverseImage :
    (structureAugmentation X K).totalRingedHom.fSharpInverseImage =
      (structureSheafInverseImageIso X K).hom := by
  unfold RingedToposHom.fSharpInverseImage
  exact (Equiv.symm_apply_eq _).2 (Adjunction.homEquiv_unit _ _ _ _).symm

/-- The structure map of `structureAugmentation`, in inverse-image form, is an isomorphism. -/
instance isIso_structureAugmentation_fSharpInverseImage :
    IsIso (structureAugmentation X K).totalRingedHom.fSharpInverseImage := by
  rw [structureAugmentation_fSharpInverseImage]
  exact Iso.isIso_hom (structureSheafInverseImageIso X K)

/-- The ringed site `(C, O_C)` with the topology generated by a pretopology. -/
abbrev pretopologyRingedSite {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C)
    (OC : Sheaf P.toGrothendieck CommRingCat.{u}) : RingedSite.{u, u, u} where
  C := C
  J := P.toGrothendieck
  O := OC

/-- The structure map of the augmentation with the restricted structure sheaf is invertible
for the ringed site `pretopologyRingedSite P OC` of a pretopology. -/
instance isIso_structureAugmentation_fSharpInverseImage_pretopology {C : Type u}
    [SmallCategory C] [HasPullbacks C] (P : Pretopology C)
    (OC : Sheaf P.toGrothendieck CommRingCat.{u}) (K : SimplicialObject (FormalCoproduct.{u} C)) :
    IsIso
      (structureAugmentation (pretopologyRingedSite P OC) K).totalRingedHom.fSharpInverseImage :=
  isIso_structureAugmentation_fSharpInverseImage _ _

end CategoryTheory.SimplicialSemiRepresentable

end
