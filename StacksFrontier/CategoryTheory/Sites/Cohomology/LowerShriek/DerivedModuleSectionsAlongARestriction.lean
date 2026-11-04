module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgettingTheModuleStructureUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedGlobalSectionsFromConstantSheafCounit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekCocontinuousSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactCocontinuous
public import StacksFrontier.Homology.Tor.DerivedBaseChangeSquareLocalization

/-!
# Derived sections of modules along a restriction of sites

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, `g : Sh(C) ⟶ Sh(D)` the
corresponding morphism of topoi, `𝒪_D` a sheaf of rings on `D` and `𝒪_C = g⁻¹𝒪_D`, so that
`g^* = g⁻¹` on sheaves of modules (`Stacks.SheafOfModules.inverseImage`). Let `T_C`, `T_D` be
functors of sections of abelian sheaves on the two sites — sections over an object, or global
sections — corepresented by sectionwise torsion-free abelian sheaves, and suppose the comparison
`g⁻¹ ⋙ RT_C ≅ RT_D` is known on abelian sheaves. Then the same comparison holds on sheaves of
modules:

`g^* ⋙ R(T_C ∘ forget) ≅ R(T_D ∘ forget)`.

This is the remark closing the statement of **Stacks 0H10**: "the same holds for modules, since
we have `g⁻¹ = g^*` and there is no difference in computing cohomology", the latter by
**Stacks 0D6J** (`Stacks.Cohomology.ForgetModuleUnivLE.derivedForgetIso`). The proof is that
chain: `R(T ∘ forget) ≅ forget ⋙ RT` on both sites (Stacks 0D6J), and forgetting the module
structure commutes with `g^* = g⁻¹` on the nose
(`Stacks.SheafOfModules.inverseImage_comp_toSheaf`).

The sites have objects in `Type (u + 1)`, morphisms in `Type u` and structure rings in
`RingCat.{u}`; abelian sheaves and sheaves of modules have sections in `Type (u + 1)`. These are
the universes of the geometric sites of an algebraic stack.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedModuleSectionsRestrictionIsoOfAbelian`:
  the general comparison.
* `Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedModuleSectionsRestrictionIso`: for
  sections over an object, from Stacks 0DD8 (1).
* `Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedModuleGlobalSectionsRestrictionIso`: for
  global sections, from the counit form of Stacks 0H0Z.

## References

* [Stacks Project, Tag 0H10](https://stacks.math.columbia.edu/tag/0H10)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
* [Stacks Project, Tag 0DD8](https://stacks.math.columbia.edu/tag/0DD8)
* [Stacks Project, Tag 0H0Z](https://stacks.math.columbia.edu/tag/0H0Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.DerivedLowerShriek.BigSite

attribute [local instance] HasDerivedCategory.standard

section Modules

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u + 1}] [HasSheafify K AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [IsGrothendieckAbelian.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
  [IsGrothendieckAbelian.{u + 1} (Sheaf K AddCommGrpCat.{u + 1})]
  [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}, f.op.HasPointwiseRightKanExtension F]

/-- The sheaf of rings `𝒪_C = g⁻¹𝒪_D` on the source site. -/
abbrev restrictedRing : Sheaf J RingCat.{u} :=
  Stacks.SheafOfModules.inverseImageRing J K f O

/-- `g^* = g⁻¹ : Mod(𝒪_D) ⥤ Mod(𝒪_C)` on sheaves of modules with sections in `Type (u + 1)`. -/
abbrev moduleInverseImage :
    SheafOfModules.{u + 1} O ⥤ SheafOfModules.{u + 1} (restrictedRing J K f O) :=
  Stacks.SheafOfModules.inverseImage.{u + 1} J K f O

/-- The functor `g^* = g⁻¹` on sheaves of modules is additive. -/
instance moduleInverseImage_additive : (moduleInverseImage J K f O).Additive :=
  exactFunctor_le_additiveFunctor _ _ _
    (SheafOfModules.exactFunctor_pushforward_of_isCocontinuous f
      (Stacks.SheafOfModules.structureMap J K f O))

/-- The functor `g^* = g⁻¹` on sheaves of modules preserves finite limits. -/
instance moduleInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (moduleInverseImage J K f O) :=
  ((exactFunctor_iff _).mp (SheafOfModules.exactFunctor_pushforward_of_isCocontinuous f
    (Stacks.SheafOfModules.structureMap J K f O))).1

/-- The functor `g^* = g⁻¹` on sheaves of modules preserves finite colimits. -/
instance moduleInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (moduleInverseImage J K f O) :=
  ((exactFunctor_iff _).mp (SheafOfModules.exactFunctor_pushforward_of_isCocontinuous f
    (Stacks.SheafOfModules.structureMap J K f O))).2

/-- **Forgetting the module structure commutes with `g^* = g⁻¹` on derived categories.** Both
composites are induced by the one exact functor `Mod(𝒪_D) ⥤ Ab(C)`, restriction of the
underlying abelian sheaf, by `Stacks.SheafOfModules.inverseImage_comp_toSheaf`. -/
def moduleInverseImageForgetIso :
    (moduleInverseImage J K f O).mapDerivedCategory ⋙
        (SheafOfModules.toSheaf (restrictedRing J K f O)).mapDerivedCategory ≅
      (SheafOfModules.toSheaf O).mapDerivedCategory ⋙
        derivedAbelianRestriction.{u + 1} J K f :=
  RingTheory.TorIndependence.mapDerivedCategoryCompNatIso _ _
      (SheafOfModules.toSheaf O ⋙ abelianRestriction.{u + 1} J K f)
      (eqToIso (Stacks.SheafOfModules.inverseImage_comp_toSheaf f O)) ≪≫
    (RingTheory.TorIndependence.mapDerivedCategoryCompNatIso _ _ _ (Iso.refl _)).symm

variable (T_C : Sheaf J AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}) [T_C.Additive]
  (T_D : Sheaf K AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}) [T_D.Additive]

/-- The unbounded right derived functor of `T` on abelian sheaves. -/
abbrev derivedAbelianOf {E : Type (u + 1)} [Category.{u} E] {L : GrothendieckTopology E}
    [HasSheafify L AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian.{u + 1} (Sheaf L AddCommGrpCat.{u + 1})]
    (T : Sheaf L AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}) [T.Additive] :
    DerivedCategory (Sheaf L AddCommGrpCat.{u + 1}) ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    (T.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  (T.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf L AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))

/-- The unbounded right derived functor of `T ∘ forget` on sheaves of modules. -/
abbrev derivedModuleOf {E : Type (u + 1)} [Category.{u} E] {L : GrothendieckTopology E}
    [HasSheafify L AddCommGrpCat.{u + 1}] [L.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R : Sheaf L RingCat.{u})
    (T : Sheaf L AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}) [T.Additive] :
    DerivedCategory (SheafOfModules.{u + 1} R) ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  letI := Stacks.SheafOfModules.sheafModulesGrothendieck.{u + 1, u, u, 0} L R
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    ((SheafOfModules.toSheaf R ⋙ T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  ((SheafOfModules.toSheaf R ⋙ T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u + 1} R) (ComplexShape.up ℤ))

/-- **Stacks 0D6J, in the form used here**: for `T` corepresented by a sectionwise torsion-free
abelian sheaf, `R(T ∘ forget) ≅ forget ⋙ RT`. -/
def derivedModuleOfIso {E : Type (u + 1)} [Category.{u} E] {L : GrothendieckTopology E}
    [HasSheafify L AddCommGrpCat.{u + 1}] [L.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian.{u + 1} (Sheaf L AddCommGrpCat.{u + 1})]
    (R : Sheaf L RingCat.{u})
    (T : Sheaf L AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}) [T.Additive]
    (A₀ : Sheaf L AddCommGrpCat.{u + 1}) (e : preadditiveCoyoneda.obj (op A₀) ≅ T)
    (hA₀ : ∀ V, Module.IsTorsionFree ℤ (A₀.obj.obj V)) :
    derivedModuleOf R T ≅ (SheafOfModules.toSheaf R).mapDerivedCategory ⋙ derivedAbelianOf T :=
  letI := Stacks.SheafOfModules.sheafModulesGrothendieck.{u + 1, u, u, 0} L R
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    (T.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    ((SheafOfModules.toSheaf R ⋙ T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  Stacks.Cohomology.ForgetModuleUnivLE.derivedForgetIso.{0, u, u, u + 1} L R T _
    ((T.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf L AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ)))
    A₀ e hA₀

/-- **The comparison of derived sections passes from abelian sheaves to sheaves of modules.** If
`T_C` and `T_D` are corepresented by sectionwise torsion-free abelian sheaves and
`g⁻¹ ⋙ RT_C ≅ RT_D` on abelian sheaves, then `g^* ⋙ R(T_C ∘ forget) ≅ R(T_D ∘ forget)` on
sheaves of modules: both sides are computed on the underlying abelian complexes (Stacks 0D6J),
and forgetting the module structure commutes with `g^* = g⁻¹`. -/
def derivedModuleSectionsRestrictionIsoOfAbelian
    (A_C : Sheaf J AddCommGrpCat.{u + 1}) (e_C : preadditiveCoyoneda.obj (op A_C) ≅ T_C)
    (hA_C : ∀ V, Module.IsTorsionFree ℤ (A_C.obj.obj V))
    (A_D : Sheaf K AddCommGrpCat.{u + 1}) (e_D : preadditiveCoyoneda.obj (op A_D) ≅ T_D)
    (hA_D : ∀ V, Module.IsTorsionFree ℤ (A_D.obj.obj V))
    (Φ : derivedAbelianRestriction.{u + 1} J K f ⋙ derivedAbelianOf T_C ≅
      derivedAbelianOf T_D) :
    (moduleInverseImage J K f O).mapDerivedCategory ⋙
        derivedModuleOf (restrictedRing J K f O) T_C ≅
      derivedModuleOf O T_D :=
  Functor.isoWhiskerLeft _ (derivedModuleOfIso (restrictedRing J K f O) T_C A_C e_C hA_C) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleInverseImageForgetIso J K f O) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ Φ ≪≫
    (derivedModuleOfIso O T_D A_D e_D hA_D).symm

end Modules

section TorsionFree

variable {E : Type (u + 1)} [Category.{u} E] (L : GrothendieckTopology E)
  [HasSheafify L AddCommGrpCat.{u + 1}]

/-- The free abelian sheaf `j_{U!} ℤ_U` on an object of a site is sectionwise torsion free: it is
the sheafification of a sectionwise free abelian presheaf. -/
lemma isTorsionFree_extensionByZeroUnitAb (U : E) (V : Eᵒᵖ) :
    Module.IsTorsionFree ℤ ((extensionByZeroUnitAb.{u + 1} L U).obj.obj V) :=
  ModuleSheafCohomology.isTorsionFree_sheafify L
    (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free) (fun W => by
      show Module.IsTorsionFree ℤ (FreeAbelianGroup (ULift.{u + 1} (W.unop ⟶ U)))
      exact Module.Flat.isTorsionFree) V

/-- The constant sheaf `ℤ` is sectionwise torsion free: it is the sheafification of the constant
presheaf `ℤ`. -/
lemma isTorsionFree_constantIntegerSheaf (V : Eᵒᵖ) :
    Module.IsTorsionFree ℤ ((constantIntegerSheaf.{u + 1} L).obj.obj V) :=
  ModuleSheafCohomology.isTorsionFree_sheafify L
    ((Functor.const Eᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) (fun W => by
      show Module.IsTorsionFree ℤ (ULift.{u + 1} ℤ)
      exact Module.Flat.isTorsionFree) V

end TorsionFree

end Stacks.Cohomology.DerivedLowerShriek.BigSite

end
