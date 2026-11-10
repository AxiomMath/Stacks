module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationModuleDescent
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModuleIffCartesianSheaf
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringDescentOfLocal
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Descent of sheaves of modules along the ringed augmentation of a hypercovering

Let `A` be a ringed augmentation of Stacks 0D9D, with morphism of ringed topoi
`a : (Sh(C_total), O) ⟶ (Sh(D), O_D)` whose structure map is the identification `O = a⁻¹O_D`.
Then `a^*` is `a⁻¹` on underlying sheaves of sets, so descent for sheaves of sets (Stacks 0D8E)
gives descent for sheaves of modules: for a hypercovering, `a^*` is fully faithful with essential
image the cartesian `O`-modules and `a_*` is a quasi-inverse (Stacks 0D9Z).

## Main results

All names below are in the namespace `CategoryTheory.SimplicialSiteSituation`, and all but the
first in its sub-namespace `RingedAugmentation`.

* `descent_modules_of_ringedToposHom_augmentationModuleDescentHypercovering`: for any morphism
  of ringed topoi `f` out of the total site with `O = f⁻¹O_Y`, descent for sheaves of sets along
  `f` gives descent for modules.
* `descent_modules_of_descent_sheaves_augmentationModuleDescentHypercovering`: the same for a
  ringed augmentation.
* `descent_modules_of_localization_descent_augmentationModuleDescentHypercovering`: its form for
  a simplicial semi-representable object, phrased through restriction along `j_total`.
* `descent_modules_of_isHypercovering_augmentationModuleDescentHypercovering`: **Stacks 0D9Z**:
  `a^*` is fully faithful with essential image the cartesian `O`-modules, and `a_*` is a
  quasi-inverse.

## References

* [Stacks Project, Tag 0D9Z](https://stacks.math.columbia.edu/tag/0D9Z)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] hasWeakSheafifyTotalModuleDescent

attribute [local instance] wEqualsLocallyBijectiveTotalModuleDescent

attribute [local instance] hasWeakSheafifyComponent

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

section RingedToposHom

variable {S O} {Y : RingedTopos.{u, u, u}} (f : RingedToposHom (S.totalRingedTopos O) Y)
  [hf : IsIso f.fSharpInverseImage]

/-- `f⁻¹` of the underlying sheaf of sets of `O_Y` is that of `O`, since the
structure map of `f` is invertible. -/
private def forgetStructureSheafIsoInverseImage :
    f.toToposHom.inverseImage.obj ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O) ≅
      (sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O :=
  ((inverseImageCommRingForgetIso S.totalTopology f.toToposHom).app Y.O).symm ≪≫
    (sheafCompose S.totalTopology (forget CommRingCat.{u})).mapIso
      (@asIso _ _ _ _ f.fSharpInverseImage hf)

/-- **Descent of modules from descent of sheaves of sets, along any morphism of ringed topoi
out of the total site.** If the structure map of `f` is the identification `O = f⁻¹O_Y` and
`f⁻¹` is fully faithful on sheaves of sets with essential image the cartesian sheaves, then
`f^*` is fully faithful on sheaves of modules with essential image the cartesian `O`-modules,
the unit of `f^* ⊣ f_*` is invertible, and its counit is invertible at every cartesian module. -/
theorem descent_modules_of_ringedToposHom_augmentationModuleDescentHypercovering
    (hff : Nonempty f.toToposHom.inverseImage.FullyFaithful)
    (hess : ∀ F : Sheaf S.totalTopology (Type u),
      f.toToposHom.inverseImage.essImage F ↔ S.IsCartesianSheaf F) :
    Nonempty f.toModulesHom.pullbackModules.FullyFaithful ∧
      (∀ F : SheafOfModules.{u} (S.totalRingSheaf O),
        f.toModulesHom.pullbackModules.essImage F ↔ S.IsCartesianModule O F) ∧
      IsIso f.pullbackAdjPushforwardModules.unit ∧
      ∀ F : SheafOfModules.{u} (S.totalRingSheaf O),
        S.IsCartesianModule O F → IsIso (f.pullbackAdjPushforwardModules.counit.app F) := by
  have hL := hff.some
  have hunit : IsIso f.toToposHom.adj.unit :=
    @Adjunction.unit_isIso_of_L_fully_faithful _ _ _ _ _ _ f.toToposHom.adj hL.full hL.faithful
  have hO : S.IsCartesianSheaf ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O) :=
    (hess _).mp ⟨_, ⟨forgetStructureSheafIsoInverseImage f⟩⟩
  have hmod := @RingedToposHom.fullyFaithfulPullbackModules _ _ _ _ _ _ _ _ _ _ f hf
    hL.full hL.faithful
  have hessM : ∀ F : SheafOfModules.{u} (S.totalRingSheaf O),
      f.toModulesHom.pullbackModules.essImage F ↔ S.IsCartesianModule O F := fun F =>
    ((@RingedToposHom.pullbackModules_essImage_iff_ringedToposMorphismAdjunction
        _ _ _ _ _ _ _ _ _ _ f hf hunit F).trans (hess _)).trans
      (S.isCartesianModule_iff_isCartesianSheaf_cartesianModuleIffCartesianSheaf O hO F).symm
  have := hmod.full
  have := hmod.faithful
  have hu : IsIso f.pullbackAdjPushforwardModules.unit :=
    @RingedToposHom.isIso_pullbackAdjPushforwardModules_unit_of_isIso_ringedToposMorphismAdjunction
      _ _ _ _ _ _ _ _ _ _ f hf hunit
  refine ⟨⟨hmod⟩, hessM, hu, fun F hF => ?_⟩
  exact (f.pullbackAdjPushforwardModules.isIso_counit_app_iff_mem_essImage).mpr ((hessM F).mpr hF)

end RingedToposHom

namespace RingedAugmentation

section General

variable {S : SimplicialSiteSituation.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  {a : Augmentation S D K} (A : RingedAugmentation S D K a)

variable [hA : IsIso A.totalRingedHom.fSharpInverseImage]

/-- The structure sheaf `O = a⁻¹O_D` of the total site has a cartesian underlying sheaf of sets,
by Stacks 0D7H (1). -/
theorem isCartesianSheaf_structureSheaf_augmentationModuleDescentHypercovering :
    S.IsCartesianSheaf ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj A.O) := by
  have h := isCartesianSheaf_of_iso _ (forgetStructureSheafIsoInverseImage A.totalRingedHom)
    (Augmentation.isCartesianSheaf_totalMorphismOfTopoi_inverseImage _ _ _ _ _)
  exact h

/-- **Descent of modules from descent of sheaves of sets.** For a ringed augmentation whose
structure map is the identification `O = a⁻¹O_D`, if `a⁻¹` is fully faithful on sheaves of sets
with essential image the cartesian sheaves, then `a^* : Mod(O_D) ⥤ Mod(O)` is fully faithful with
essential image the cartesian `O`-modules, the unit of `a^* ⊣ a_*` is invertible, and its counit
is invertible at every cartesian module. -/
theorem descent_modules_of_descent_sheaves_augmentationModuleDescentHypercovering
    (hff : Nonempty A.totalRingedHom.toToposHom.inverseImage.FullyFaithful)
    (hess : ∀ F : Sheaf S.totalTopology (Type u),
      A.totalRingedHom.toToposHom.inverseImage.essImage F ↔ S.IsCartesianSheaf F) :
    Nonempty A.totalRingedHom.toModulesHom.pullbackModules.FullyFaithful ∧
      (∀ F : SheafOfModules.{u} (S.totalRingSheaf A.O),
        A.totalRingedHom.toModulesHom.pullbackModules.essImage F ↔ S.IsCartesianModule A.O F) ∧
      IsIso A.totalRingedHom.pullbackAdjPushforwardModules.unit ∧
      ∀ F : SheafOfModules.{u} (S.totalRingSheaf A.O),
        S.IsCartesianModule A.O F →
          IsIso (A.totalRingedHom.pullbackAdjPushforwardModules.counit.app F) :=
  descent_modules_of_ringedToposHom_augmentationModuleDescentHypercovering A.totalRingedHom hff hess

end General

section SemiRepresentable

open SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} [J.toCoverage.HasPullbacks]
  {K : SimplicialObject (FormalCoproduct.{u} C)}
  (A : RingedAugmentation (situation J K) (Cat.of C) J (situationAugmentation J K))

/-- The inverse image `a⁻¹` of the total augmentation of a simplicial semi-representable object,
in the limit construction of Stacks 0D70, is fully faithful as soon as restriction along
`j_total` is: the two functors are isomorphic. -/
def fullyFaithfulSituationTotalInverseImageAugmentationModuleDescentHypercovering
    (hff : (totalLocalizationMorphism J K).inverseImage.FullyFaithful) :
    (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi (situation J K) (Cat.of C) J
      (situationAugmentation J K)).inverseImage.FullyFaithful :=
  Functor.FullyFaithful.ofIso hff
    (situationTotalInverseImageIsoTotalAugmentationComparison J K).symm

/-- The essential image of `a⁻¹` in the limit construction of Stacks 0D70 is that of restriction
along `j_total`. -/
theorem situationTotalInverseImage_essImage_augmentationModuleDescentHypercovering :
    (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi (situation J K) (Cat.of C) J
      (situationAugmentation J K)).inverseImage.essImage =
      (totalLocalizationMorphism J K).inverseImage.essImage :=
  Functor.essImage_eq_of_natIso (situationTotalInverseImageIsoTotalAugmentationComparison J K)

variable [IsIso A.totalRingedHom.fSharpInverseImage]

/-- **Descent of modules along a simplicial semi-representable object.** If restriction along
`j_total` is fully faithful on sheaves of sets with essential image the cartesian sheaves, the
conclusions of `descent_modules_of_descent_sheaves_augmentationModuleDescentHypercovering` hold
for every ringed augmentation of the total site with structure map `O = a⁻¹O_C`. -/
theorem descent_modules_of_localization_descent_augmentationModuleDescentHypercovering
    (hff : Nonempty (totalLocalizationMorphism J K).inverseImage.FullyFaithful)
    (hess : ∀ F : Sheaf (situation J K).totalTopology (Type u),
      (totalLocalizationMorphism J K).inverseImage.essImage F ↔
        (situation J K).IsCartesianSheaf F) :
    Nonempty A.totalRingedHom.toModulesHom.pullbackModules.FullyFaithful ∧
      (∀ F : SheafOfModules.{u} ((situation J K).totalRingSheaf A.O),
        A.totalRingedHom.toModulesHom.pullbackModules.essImage F ↔
          (situation J K).IsCartesianModule A.O F) ∧
      IsIso A.totalRingedHom.pullbackAdjPushforwardModules.unit ∧
      ∀ F : SheafOfModules.{u} ((situation J K).totalRingSheaf A.O),
        (situation J K).IsCartesianModule A.O F →
          IsIso (A.totalRingedHom.pullbackAdjPushforwardModules.counit.app F) :=
  descent_modules_of_descent_sheaves_augmentationModuleDescentHypercovering A
    ⟨fullyFaithfulSituationTotalInverseImageAugmentationModuleDescentHypercovering hff.some⟩
    fun F => by
      change (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi (situation J K)
        (Cat.of C) J (situationAugmentation J K)).inverseImage.essImage F ↔ _
      rw [situationTotalInverseImage_essImage_augmentationModuleDescentHypercovering]
      exact hess F

end SemiRepresentable

section Hypercovering

open Stacks.CategoryTheory.Hypercovering SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] {P : Pretopology C}
  (H : HypercoveringOfTerminal.{u, u, u} P)
  (A : RingedAugmentation (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C)
    P.toGrothendieck (situationAugmentation P.toGrothendieck H.toSimplicialObject))

/-- **Stacks 0D9Z.** Let `C` be a site with equalizers and fibre products, `O_C` a sheaf of rings,
`K` a hypercovering, and `a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` the ringed augmentation with
`O = a⁻¹O_C`. Then `a^* : Mod(O_C) ⥤ Mod(O)` is fully faithful with essential image the cartesian
`O`-modules, and `a_*` is a quasi-inverse: the unit `F ⟶ a_*a^*F` is invertible, and the counit
`a^*a_*G ⟶ G` is invertible for every cartesian `G`. -/
theorem descent_modules_of_isHypercovering_augmentationModuleDescentHypercovering
    [IsIso A.totalRingedHom.fSharpInverseImage] :
    Nonempty A.totalRingedHom.toModulesHom.pullbackModules.FullyFaithful ∧
      (∀ F : SheafOfModules.{u} ((situation P.toGrothendieck H.toSimplicialObject).totalRingSheaf
          A.O),
        A.totalRingedHom.toModulesHom.pullbackModules.essImage F ↔
          (situation P.toGrothendieck H.toSimplicialObject).IsCartesianModule A.O F) ∧
      IsIso A.totalRingedHom.pullbackAdjPushforwardModules.unit ∧
      ∀ F : SheafOfModules.{u} ((situation P.toGrothendieck H.toSimplicialObject).totalRingSheaf
          A.O),
        (situation P.toGrothendieck H.toSimplicialObject).IsCartesianModule A.O F →
          IsIso (A.totalRingedHom.pullbackAdjPushforwardModules.counit.app F) :=
  descent_modules_of_localization_descent_augmentationModuleDescentHypercovering A
    (descent_sheaves_of_isHypercovering_hypercoveringDescentOfLocal P H).1
    (descent_sheaves_of_isHypercovering_hypercoveringDescentOfLocal P H).2.1

end Hypercovering

end RingedAugmentation

end CategoryTheory.SimplicialSiteSituation

end
