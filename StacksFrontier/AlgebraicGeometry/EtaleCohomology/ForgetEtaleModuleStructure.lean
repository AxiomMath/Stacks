module
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRingUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImageUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.UnderlyingAbelianDerivedDirectImage
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative

/-!
# Forgetting the module structure of complexes of étale sheaves of `Λ`-modules

Let `Λ` be a ring and `X` a scheme. Forgetting the module structure is an exact functor from
sheaves of `Λ`-modules on the small étale site of `X` to abelian sheaves, so it induces a functor
`D(X_étale, Λ) ⥤ D(X_étale)` on unbounded derived categories. This file records that functor,
that it is conservative, and that it commutes with the unbounded derived direct image `Rf_*`
along any morphism of schemes `f : X ⟶ Y` — the case of [Stacks, Tag 0D6J] part (3) for the
model `Stacks.EtaleCohomology.EtaleModules` of sheaves of `Λ`-modules on which cohomology with
compact support is built.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleForgetDerived`: the functor `D(X_étale, Λ) ⥤ D(X_étale)`.
* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageForgetIsoUnconditional`: the natural
  isomorphism `(Rf_* K)_ab ≅ Rf_*(K_ab)`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleForgetDerived_reflectsIsomorphisms`: the forgetful functor
  on derived categories reflects isomorphisms.
* `Stacks.EtaleCohomology.isKInjective_etaleModuleSheafEquivalence_mapHomologicalComplex`: the
  equivalence `EtaleModules Λ X ≌ SheafOfModules Λ̲` preserves K-injective complexes.
* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedDirectImageUnit_app_forget_of_isKInjective`:
  the underlying abelian complex of a K-injective complex of sheaves of `Λ`-modules computes the
  derived direct image of abelian sheaves.
* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageForget_isRightDerivedFunctor` and
  `Stacks.EtaleCohomology.forgetEtaleAbelianDerivedDirectImage_isRightDerivedFunctor`: both
  composites `Rf_* ⋙ forget` and `forget ⋙ Rf_*` are right derived functors of the degreewise
  direct image followed by forgetting.

## Implementation notes

Nothing about forgetting the module structure is reproved here. The one input, that the
underlying abelian complex `I_ab` of a K-injective complex `I` computes `Rf_*`, is
`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedDirectImageUnit_app_toSheaf_of_isKInjective`,
stated for complexes of sheaves of modules over a sheaf of rings. It is transported along the
equivalence `Stacks.EtaleCohomology.etaleModuleSheafEquivalence` with the sheaves of modules over
the constant sheaf of rings `Λ̲`: an equivalence preserves K-injective complexes, and the
equivalence followed by `SheafOfModules.toSheaf` is the forgetful functor
(`Stacks.EtaleCohomology.etaleModuleSheafEquivalenceFunctorCompToSheafGeneral`).

The two derived functors are defined differently — `Rf_*` on sheaves of `Λ`-modules along the
localization of cochain complexes, `Rf_*` on abelian sheaves along the localization of the
homotopy category — so the comparison is made along cochain complexes: both composites are
right derived functors of the same functor there, by the K-injective criterion
`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective`,
and the isomorphism is the uniqueness of right derived functors.

## References

* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Injectives.KInjectiveResolution (invertsQuasiIso_mapHomologicalComplex_comp_Q
  isRightDerivedFunctor_iff_isIso_app_of_isKInjective)

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-! ### The forgetful functor on derived categories -/

/-- Forgetting the module structure, on unbounded derived categories:
`D(X_étale, Λ) ⥤ D(X_étale)`. It is induced by the exact functor
`_root_.Stacks.EtaleCohomology.etaleModuleForgetAb`. -/
abbrev etaleModuleForgetDerived (X : Scheme.{u}) :
    DerivedCategory (EtaleModules.{u, r} Λ X) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) :=
  (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapDerivedCategory

/-- **Forgetting the module structure on derived categories reflects isomorphisms**: a morphism
of `D(X_étale, Λ)` is invertible as soon as it is invertible in `D(X_étale)`, cohomology sheaves
being computed by the exact and conservative forgetful functor. -/
instance etaleModuleForgetDerived_reflectsIsomorphisms (X : Scheme.{u}) :
    (etaleModuleForgetDerived.{u, r} Λ X).ReflectsIsomorphisms :=
  Functor.reflectsIsomorphisms_mapDerivedCategory _

/-! ### The derived inverse image -/

/-- The inverse image `f⁻¹ : D(Y_étale, Λ) ⥤ D(X_étale, Λ)` on unbounded derived categories of
sheaves of `Λ`-modules: `f⁻¹` is exact, so it is applied degreewise. -/
abbrev etaleModuleDerivedInverseImageGeneral {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (EtaleModules.{u, r} Λ Y) ⥤ DerivedCategory (EtaleModules.{u, r} Λ X) :=
  (etaleModuleInverseImage.{u, r} Λ f).mapDerivedCategory

/-! ### K-injective complexes and the abelian derived direct image -/

/-- The functor `EtaleModules Λ X ⥤ SheafOfModules Λ̲` of the equivalence is additive. -/
instance etaleModuleSheafEquivalence_functor_additive (X : Scheme.{u}) :
    (etaleModuleSheafEquivalence.{u, r} Λ X).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The functor `SheafOfModules Λ̲ ⥤ EtaleModules Λ X` of the equivalence is additive. -/
instance etaleModuleSheafEquivalence_inverse_additive (X : Scheme.{u}) :
    (etaleModuleSheafEquivalence.{u, r} Λ X).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The equivalence `EtaleModules Λ X ≌ SheafOfModules Λ̲` carries K-injective complexes to
K-injective complexes: its functor is right adjoint to its inverse, which is exact. -/
theorem isKInjective_etaleModuleSheafEquivalence_mapHomologicalComplex (X : Scheme.{u})
    (I : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((etaleModuleSheafEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    (etaleModuleSheafEquivalence.{u, r} Λ X).functor
    (etaleModuleSheafEquivalence.{u, r} Λ X).inverse
    (etaleModuleSheafEquivalence.{u, r} Λ X).symm.toAdjunction I

/-- **The underlying abelian complex of a K-injective complex of sheaves of `Λ`-modules computes
the unbounded derived direct image of abelian sheaves**: the unit `f_* I_ab ⟶ Rf_* I_ab` is an
isomorphism. This is
`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedDirectImageUnit_app_toSheaf_of_isKInjective`
transported along `Stacks.EtaleCohomology.etaleModuleSheafEquivalence`. -/
theorem isIso_etaleAbelianDerivedDirectImageUnit_app_forget_of_isKInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) (I : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    [I.IsKInjective] :
    IsIso ((etaleAbelianDerivedDirectImageUnit.{u, r} f).app
      ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r})
          (ComplexShape.up ℤ)).obj
        (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I))) := by
  have := isKInjective_etaleModuleSheafEquivalence_mapHomologicalComplex.{u, r} Λ X I
  have h := isIso_etaleAbelianDerivedDirectImageUnit_app_toSheaf_of_isKInjective.{u, r} f
    (etaleConstantRingSheaf.{u, r} Λ X)
    (((etaleModuleSheafEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I)
  refine (NatTrans.isIso_app_iff_of_iso _ ((HomotopyCategory.quotient _ _).mapIso ?_)).mp h
  exact (Functor.mapHomologicalComplexCompIso
    (etaleModuleSheafEquivalenceFunctorCompToSheafGeneral.{u, r} Λ X) (ComplexShape.up ℤ)).app I

/-! ### Forgetting the module structure commutes with `Rf_*` -/

section DirectImage

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Direct image followed by forgetting the module structure is forgetting followed by the
direct image of abelian sheaves, on the nose: both restrict sections along base change. -/
def etaleModuleDirectImageCompForgetIso :
    _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X ⋙
        etaleAbelianDirectImage.{u, r} f ≅
      etaleModuleDirectImage.{u, r} Λ f ⋙
        _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y :=
  Iso.refl _

/-- Degreewise direct image followed by forgetting the module structure, then localization:
the functor of which both `Rf_* ⋙ forget` and `forget ⋙ Rf_*` are right derived functors. -/
abbrev etaleModuleDirectImageForgetToDerivedCategory :
    CochainComplex (EtaleModules.{u, r} Λ X) ℤ ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) :=
  (etaleModuleDirectImage.{u, r} Λ f ⋙
      _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/-- The derivation unit exhibiting `Rf_* ⋙ forget` as a right derived functor of
`Stacks.EtaleCohomology.etaleModuleDirectImageForgetToDerivedCategory`: the unit of `Rf_*` on
sheaves of `Λ`-modules, followed by the forgetful functor. -/
def etaleModuleDerivedDirectImageForgetUnit :
    etaleModuleDirectImageForgetToDerivedCategory.{u, r} Λ f ⟶
      DerivedCategory.Q ⋙
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙ etaleModuleForgetDerived.{u, r} Λ Y) :=
  Functor.whiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModuleDirectImage.{u, r} Λ f ⋙
          _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y))
        (ComplexShape.up ℤ)).inv DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex
        (ComplexShape.up ℤ))
      (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y).mapDerivedCategoryFactors.inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f)
      (etaleModuleForgetDerived.{u, r} Λ Y) ≫
    (Functor.associator _ _ _).hom

/-- Degreewise direct image followed by forgetting, then localization, is forgetting followed by
the degreewise direct image of abelian sheaves on the homotopy category, then localization. -/
def etaleModuleDirectImageForgetToDerivedCategoryIso :
    etaleModuleDirectImageForgetToDerivedCategory.{u, r} Λ f ≅
      ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙
          HomotopyCategory.quotient
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) (ComplexShape.up ℤ)) ⋙
        etaleAbelianPushforwardToDerivedCategory.{u, r} f :=
  Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (etaleModuleDirectImageCompForgetIso.{u, r} Λ f).symm
        (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X ⋙
          etaleAbelianDirectImage.{u, r} f))
        (ComplexShape.up ℤ)).symm DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _
          (DerivedCategory.quotientCompQhIso
            (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r})).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ((etaleAbelianDirectImage.{u, r} f).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

/-- Forgetting, passing to the homotopy category and localizing is localizing and then forgetting
on derived categories. -/
def forgetQuotientQhIso :
    ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙
          HomotopyCategory.quotient
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) (ComplexShape.up ℤ)) ⋙
        (DerivedCategory.Qh ⋙ etaleAbelianDerivedDirectImage.{u, r} f) ≅
      DerivedCategory.Q ⋙
        (etaleModuleForgetDerived.{u, r} Λ X ⋙ etaleAbelianDerivedDirectImage.{u, r} f) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (DerivedCategory.quotientCompQhIso
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}))
          (etaleAbelianDerivedDirectImage.{u, r} f)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapDerivedCategoryFactors.symm
      (etaleAbelianDerivedDirectImage.{u, r} f) ≪≫
    Functor.associator _ _ _

/-- The derivation unit exhibiting `forget ⋙ Rf_*` as a right derived functor of
`Stacks.EtaleCohomology.etaleModuleDirectImageForgetToDerivedCategory`: forget, then the unit of
`Rf_*` on abelian sheaves. -/
def forgetEtaleAbelianDerivedDirectImageUnit :
    etaleModuleDirectImageForgetToDerivedCategory.{u, r} Λ f ⟶
      DerivedCategory.Q ⋙
        (etaleModuleForgetDerived.{u, r} Λ X ⋙ etaleAbelianDerivedDirectImage.{u, r} f) :=
  (etaleModuleDirectImageForgetToDerivedCategoryIso.{u, r} Λ f).hom ≫
    Functor.whiskerLeft
      ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        HomotopyCategory.quotient
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) (ComplexShape.up ℤ))
      (etaleAbelianDerivedDirectImageUnit.{u, r} f) ≫
    (forgetQuotientQhIso.{u, r} Λ f).hom

/-- `Rf_*` on sheaves of `Λ`-modules followed by forgetting the module structure is a right
derived functor of degreewise direct image followed by forgetting: its unit is invertible on
K-injective complexes, where the unit of `Rf_*` is. -/
instance etaleModuleDerivedDirectImageForget_isRightDerivedFunctor :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
        etaleModuleForgetDerived.{u, r} Λ Y).IsRightDerivedFunctor
      (etaleModuleDerivedDirectImageForgetUnit.{u, r} Λ f)
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) := by
  rw [isRightDerivedFunctor_iff_isIso_app_of_isKInjective DerivedCategory.Q _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q
      (etaleModuleDirectImage.{u, r} Λ f ⋙
        _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y))]
  intro K hK
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ f K hK
  dsimp only [etaleModuleDerivedDirectImageForgetUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- Forgetting the module structure followed by `Rf_*` on abelian sheaves is a right derived
functor of degreewise direct image followed by forgetting: on a K-injective complex `I` its unit
is the unit of the abelian `Rf_*` at `I_ab`, which is invertible by
`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedDirectImageUnit_app_forget_of_isKInjective`. -/
instance forgetEtaleAbelianDerivedDirectImage_isRightDerivedFunctor :
    (etaleModuleForgetDerived.{u, r} Λ X ⋙
        etaleAbelianDerivedDirectImage.{u, r} f).IsRightDerivedFunctor
      (forgetEtaleAbelianDerivedDirectImageUnit.{u, r} Λ f)
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) := by
  rw [isRightDerivedFunctor_iff_isIso_app_of_isKInjective DerivedCategory.Q _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q
      (etaleModuleDirectImage.{u, r} Λ f ⋙
        _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y))]
  intro K hK
  have := hK
  have := isIso_etaleAbelianDerivedDirectImageUnit_app_forget_of_isKInjective.{u, r} Λ f K
  dsimp only [forgetEtaleAbelianDerivedDirectImageUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.comp_obj]
  infer_instance

/-- **Forgetting the module structure commutes with the unbounded derived direct image.** For a
morphism of schemes `f : X ⟶ Y` and `K` in `D(X_étale, Λ)`, the image of `Rf_* K` in `D(Y_étale)`
is the derived direct image of abelian sheaves of the image of `K`, naturally in `K`. -/
def etaleModuleDerivedDirectImageForgetIsoUnconditional :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙ etaleModuleForgetDerived.{u, r} Λ Y ≅
      etaleModuleForgetDerived.{u, r} Λ X ⋙ etaleAbelianDerivedDirectImage.{u, r} f :=
  Functor.rightDerivedUnique _ _ (etaleModuleDerivedDirectImageForgetUnit.{u, r} Λ f)
    (forgetEtaleAbelianDerivedDirectImageUnit.{u, r} Λ f)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))

/-- The isomorphism `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageForgetIsoUnconditional`
is the one compatible with the two derivation units. -/
@[reassoc]
theorem etaleModuleDerivedDirectImageForgetIso_hom_fac :
    etaleModuleDerivedDirectImageForgetUnit.{u, r} Λ f ≫
        Functor.whiskerLeft DerivedCategory.Q
          (etaleModuleDerivedDirectImageForgetIsoUnconditional.{u, r} Λ f).hom =
      forgetEtaleAbelianDerivedDirectImageUnit.{u, r} Λ f := by
  simp [etaleModuleDerivedDirectImageForgetIsoUnconditional]

end DirectImage

end Stacks.EtaleCohomology

end
