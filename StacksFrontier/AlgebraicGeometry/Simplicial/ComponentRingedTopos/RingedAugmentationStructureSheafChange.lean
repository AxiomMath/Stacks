module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.HypercoveringUnboundedEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLowerShriek

/-!
# Changing the structure sheaf of a ringed augmentation with invertible structure map

Let `a : (Sh(C_total), O) ⟶ (Sh(D), O_D)` be a ringed augmentation whose structure map
`a♯ : a⁻¹O_D ⟶ O` is invertible. Then `O` is identified with `a⁻¹O_D`, the structure sheaf of the
ringed augmentation `a'` with the pulled-back structure sheaf, and restriction of scalars along
that identification carries `a^*` to `a'^*`, both on modules and on derived categories.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.inverseImageStructureRingIso`: the
  identification `a⁻¹O_D ≅ O`.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.pullbackModulesInverseImageIso`:
  `a^*` followed by restriction of scalars along it is `a'^*`.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.derivedPullbackInverseImageIso`: the
  same for `La^*` and `La'^*`.

## Main results

* `Stacks.CategoryTheory.Hypercovering.exists_derivedPullback_iso_of_localSerreFamily`: the
  essential surjectivity half of Stacks 0DC7 for any ringed augmentation of a hypercovering with
  invertible structure map: an object of `D(O)` all of whose cohomology modules are of the form
  `a^*N` with `N` in `A` is `La^*F` for some `F` in `D_A(O_C)`.

## References

* [Stacks Project, Tag 0DC7](https://stacks.math.columbia.edu/tag/0DC7)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward Stacks.Cohomology.CohomologicalDescent

universe u

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules

variable {C : Type*} [Category C] {J : GrothendieckTopology C}

/-- Restriction of scalars along `x` and then along `y` is restriction of scalars along any `z`
equal to `y ≫ x`. -/
def restrictScalarsCompIsoOfEq {R₁ R₂ R₃ : Sheaf J RingCat.{u}} (x : R₂ ⟶ R₃) (y : R₁ ⟶ R₂)
    (z : R₁ ⟶ R₃) (h : y ≫ x = z) :
    SheafOfModules.restrictScalars.{u} x ⋙ SheafOfModules.restrictScalars.{u} y ≅
      SheafOfModules.restrictScalars.{u} z :=
  SheafOfModules.pushforwardComp (F := 𝟭 C) (G := 𝟭 C) y x ≪≫ SheafOfModules.pushforwardCongr h

end SheafOfModules

namespace CategoryTheory.SimplicialSiteSituation.RingedAugmentation

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal

attribute [local instance] RingedToposHom.pullbackModules_preservesFiniteLimits_of_isIso_fSharp
  RingedToposHom.pullbackModules_preservesFiniteColimits_of_adjunction

variable {S : SimplicialSiteSituation.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  {a : Augmentation S D K} (A : RingedAugmentation S D K a)
  [IsIso A.totalRingedHom.fSharpInverseImage]

/-- The ringed augmentation of the same augmentation with the pulled-back structure sheaf
`a⁻¹O_D`. -/
abbrev inverseImageAugmentation : RingedAugmentation S D K a :=
  inverseImageRingedAugmentation S D K a A.OD

/-- The structure map `a⁻¹O_D ⟶ O` of a ringed augmentation, on sheaves of rings, in the form
along which the pullback of modules extends scalars. -/
abbrev structureMapRing :
    Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf
        (Augmentation.totalMorphismOfTopoi S D K a)
        (Stacks.SheafOfModules.Tensor.ringSheaf A.OD) ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf A.O :=
  A.totalRingedHom.toModulesHom.fSharpInverseImage

/-- The structure map `a⁻¹O_D ⟶ O`, on sheaves of rings, is invertible. -/
instance isIso_structureMapRing : IsIso A.structureMapRing :=
  RingedToposHom.isIso_toModulesHom_fSharpInverseImage A.totalRingedHom

/-- The (identity) structure map `a⁻¹O_D ⟶ a⁻¹O_D` of the ringed augmentation with the
pulled-back structure sheaf, with its source written through `O_D` itself. -/
abbrev inverseImageStructureMapRing :
    Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf
        (Augmentation.totalMorphismOfTopoi S D K a)
        (Stacks.SheafOfModules.Tensor.ringSheaf A.OD) ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf A.inverseImageAugmentation.O :=
  A.inverseImageAugmentation.totalRingedHom.toModulesHom.fSharpInverseImage

/-- The structure map of the ringed augmentation with the pulled-back structure sheaf is
invertible. -/
instance isIso_inverseImageStructureMapRing : IsIso A.inverseImageStructureMapRing :=
  RingedToposHom.isIso_toModulesHom_fSharpInverseImage A.inverseImageAugmentation.totalRingedHom

/-- **The structure sheaf of a ringed augmentation with invertible structure map is `a⁻¹O_D`**:
the inverse of the (identity) structure map of the augmentation with `O = a⁻¹O_D`, followed by
the structure map of the given one. -/
def inverseImageStructureRingIso :
    Stacks.SheafOfModules.Tensor.ringSheaf A.inverseImageAugmentation.O ≅
      Stacks.SheafOfModules.Tensor.ringSheaf A.O :=
  (asIso A.inverseImageStructureMapRing).symm ≪≫ asIso A.structureMapRing

/-- The identification `a⁻¹O_D ≅ O` followed by the inverse of the structure map `a⁻¹O_D ⟶ O` is
the inverse of the structure map of the ringed augmentation with `O = a⁻¹O_D`. -/
theorem inverseImageStructureRingIso_hom_comp_inv :
    A.inverseImageStructureRingIso.hom ≫ inv A.structureMapRing =
      inv A.inverseImageStructureMapRing := by
  rw [inverseImageStructureRingIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, asIso_hom,
    IsIso.hom_inv_id, Category.comp_id, asIso_inv]

/-- Restriction of scalars along `inverseImageStructureRingIso`, an equivalence
`Mod(O) ≌ Mod(a⁻¹O_D)`. -/
def inverseImageModulesEquivalence :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.O) ≌
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.inverseImageAugmentation.O) :=
  Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso A.inverseImageStructureRingIso.symm

/-- Restriction of scalars `Mod(O) ⥤ Mod(a⁻¹O_D)` is additive. -/
instance additive_inverseImageModulesEquivalence_functor :
    A.inverseImageModulesEquivalence.functor.Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars _).Additive

/-- Restriction of scalars `Mod(a⁻¹O_D) ⥤ Mod(O)` is additive. -/
instance additive_inverseImageModulesEquivalence_inverse :
    A.inverseImageModulesEquivalence.inverse.Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars _).Additive

/-- Restriction of scalars `Mod(O) ⥤ Mod(a⁻¹O_D)` preserves finite limits. -/
instance preservesFiniteLimits_inverseImageModulesEquivalence_functor :
    PreservesFiniteLimits A.inverseImageModulesEquivalence.functor :=
  inferInstance

/-- Restriction of scalars `Mod(O) ⥤ Mod(a⁻¹O_D)` preserves finite colimits. -/
instance preservesFiniteColimits_inverseImageModulesEquivalence_functor :
    PreservesFiniteColimits A.inverseImageModulesEquivalence.functor :=
  inferInstance

/-- **`a^*` followed by restriction of scalars along `a⁻¹O_D ≅ O` is `a'^*`**, for `a'` the ringed
augmentation with `O = a⁻¹O_D`. -/
def pullbackModulesInverseImageIso :
    A.totalRingedHom.toModulesHom.pullbackModules ⋙ A.inverseImageModulesEquivalence.functor ≅
      A.inverseImageAugmentation.totalRingedHom.toModulesHom.pullbackModules :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft _
      A.totalRingedHom.toModulesHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (SheafOfModules.restrictScalarsCompIsoOfEq _ _
      (inv A.inverseImageStructureMapRing)
      A.inverseImageStructureRingIso_hom_comp_inv) ≪≫
    (Functor.isoWhiskerLeft _
      (A.inverseImageAugmentation.totalRingedHom.toModulesHom
        |>.extendScalarsFSharpIsoRestrictScalarsOfIsIso)).symm

/-- **`La^*` followed by restriction of scalars along `a⁻¹O_D ≅ O` is `La'^*`**, for `a'` the
ringed augmentation with `O = a⁻¹O_D`. -/
def derivedPullbackInverseImageIso :
    (RingedToposHom.leftDerivedPullbackOfIsIsoFSharp A.totalRingedHom).functor ⋙
        A.inverseImageModulesEquivalence.functor.mapDerivedCategory ≅
      (RingedToposHom.leftDerivedPullbackOfIsIsoFSharp
        A.inverseImageAugmentation.totalRingedHom).functor :=
  let Φ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos A.O).O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (S.totalRingedTopos A.inverseImageAugmentation.O).O) :=
    A.inverseImageModulesEquivalence.functor
  haveI : Φ.Additive := A.additive_inverseImageModulesEquivalence_functor
  haveI : PreservesFiniteLimits Φ := A.preservesFiniteLimits_inverseImageModulesEquivalence_functor
  haveI : PreservesFiniteColimits Φ :=
    A.preservesFiniteColimits_inverseImageModulesEquivalence_functor
  haveI := RingedToposHom.pullbackModules_additive A.totalRingedHom
  haveI : (A.totalRingedHom.toModulesHom.pullbackModules ⋙ Φ).Additive := inferInstance
  Functor.isoWhiskerRight (RingedToposHom.derivedPullbackNatIsoOfIsIsoFSharp A.totalRingedHom) _ ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ Φ).symm ≪≫
    @Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ _ _ _ _ _ _
      (A.totalRingedHom.toModulesHom.pullbackModules ⋙ Φ)
      A.inverseImageAugmentation.totalRingedHom.toModulesHom.pullbackModules
      inferInstance inferInstance inferInstance
      (RingedToposHom.pullbackModules_additive A.inverseImageAugmentation.totalRingedHom)
      (RingedToposHom.pullbackModules_preservesFiniteLimits_of_isIso_fSharp
        A.inverseImageAugmentation.totalRingedHom)
      (RingedToposHom.pullbackModules_preservesFiniteColimits_of_adjunction
        A.inverseImageAugmentation.totalRingedHom)
      A.pullbackModulesInverseImageIso ≪≫
    (RingedToposHom.derivedPullbackNatIsoOfIsIsoFSharp
      A.inverseImageAugmentation.totalRingedHom).symm

end CategoryTheory.SimplicialSiteSituation.RingedAugmentation

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory.SimplicialSiteSituation
  CategoryTheory.SimplicialSiteSituation.RingedAugmentation

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} J)
  (A : RingedAugmentation (hypercoveringSituation J H) (Cat.of C) J.toGrothendieck
    (hypercoveringAugmentation J H)) [IsIso A.totalRingedHom.fSharpInverseImage]
  (T : LocalSerreFamily.{u}
    (CategoryTheory.SimplicialSemiRepresentable.pretopologyRingedSite J A.OD))

/-- **The essential surjectivity half of Stacks 0DC7, for any ringed augmentation of a
hypercovering with invertible structure map.** Let `A ⊂ Mod(O_C)` be the modules whose
restriction to every `C/U` lies in `A_U`, for a family `A_U` satisfying 0DC2, 0DC3 and 0DC4. An
object `E` of `D(O)` each of whose cohomology modules is `a^*N` for some `N` in `A` is `La^*F` for
an object `F` of `D_A(O_C)`. -/
theorem exists_derivedPullback_iso_of_localSerreFamily
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((hypercoveringSituation J H).totalRingedTopos A.O).O)))
    (hE : ∀ q : ℤ, ∃ N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.OD),
      baseLocalSerre J A.OD T N ∧
        Nonempty ((DerivedCategory.homologyFunctor _ q).obj E ≅
          A.totalRingedHom.toModulesHom.pullbackModules.obj N)) :
    ∃ F : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.OD)),
      DerivedCategoryB.derivedCategoryB (baseLocalSerre J A.OD T) F ∧
        Nonempty ((RingedToposHom.leftDerivedPullbackOfIsIsoFSharp A.totalRingedHom).functor.obj F
          ≅ E) := by
  have := isWeakSerreClass_totalLocalSerre J H A.OD T
  let Φ := A.inverseImageModulesEquivalence
  have hE' : ∀ q : ℤ, totalLocalSerre J H A.OD T
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        ((hypercoveringSituation J H).totalRingSheaf
          (hypercoveringRingedAugmentation J H A.OD).O)) q).obj
          (Φ.functor.mapDerivedCategory.obj E)) := fun q ↦ by
    obtain ⟨N, hN, ⟨e⟩⟩ := hE q
    exact ObjectProperty.prop_of_iso _
      (((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso Φ.functor q).app E ≪≫
        Φ.functor.mapIso e ≪≫ A.pullbackModulesInverseImageIso.app N).symm)
      (totalLocalSerre_pullbackModules J H A.OD T N hN)
  obtain ⟨-, e, he₁, -⟩ := exists_derivedPullbackEquivalence_localSerreFamily J H A.OD T
  let X : (DerivedCategoryB.derivedCategoryB (A := SheafOfModules.{u}
      ((hypercoveringSituation J H).totalRingSheaf (hypercoveringRingedAugmentation J H A.OD).O))
      (totalLocalSerre J H A.OD T)).FullSubcategory := ⟨_, hE'⟩
  refine ⟨(e.inverse.obj X).obj, (e.inverse.obj X).property, ⟨?_⟩⟩
  have e₁ : (RingedToposHom.leftDerivedPullbackOfIsIsoFSharp
      A.inverseImageAugmentation.totalRingedHom).functor.obj (e.inverse.obj X).obj ≅
        Φ.functor.mapDerivedCategory.obj E :=
    eqToIso (Functor.congr_obj he₁ (e.inverse.obj X)).symm ≪≫
      (DerivedCategoryB.derivedCategoryB (totalLocalSerre J H A.OD T)).ι.mapIso (e.counitIso.app X)
  exact (Functor.FullyFaithful.ofFullyFaithful Φ.functor.mapDerivedCategory).preimageIso
    ((A.derivedPullbackInverseImageIso.app _) ≪≫ e₁)

end Stacks.CategoryTheory.Hypercovering

end
