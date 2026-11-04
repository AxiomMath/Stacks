module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedTrace
public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHomBifunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf

/-!
# The derived identity of Stacks 0E2I at the source `𝒪_Z[0]`, from its cochain-level form

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces, so that `i_*` is left adjoint to
sheaf Hom with exact support `ℰom(𝒪_Z, -)` ([Stacks, Tag 0A75]). At the class of a K-injective
cochain complex `I` of `𝒪_X`-modules, restriction along a unit `u : 𝒪_X[0] ⟶ Ri_* 𝒪_Z[0]` followed
by the trivialisation of `R ℰom_X(𝒪_X[0], -)` is the component formula
`derivedSheafHomPushforwardModelIso` of [Stacks, Tag 0E2I], followed by the trivialisation of
`R ℰom_Z(𝒪_Z[0], -)` pushed forward and by the trace of [Stacks, Tag 0A76], as soon as the
corresponding identity holds for a morphism of complexes `cu` whose class is `u`.

## Main results

All names are in the namespace `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`.

* `derivedStructureSheafHomIso_exactSupport_kInjective`: the trivialisation of
  `R ℰom_Z(𝒪_Z[0], -)` at `R ℰom(𝒪_Z, Q I)`, for a K-injective `I`, read through the
  identification of `R ℰom(𝒪_Z, Q I)` with the class of the degreewise `ℰom^•(𝒪_Z, I)`, is the
  class of evaluation at the unit section.
* `derivedStructureSheafHomNatIso_hom_app_Q`: the trivialisation of `R ℰom_X(𝒪_X[0], -)` at the
  class of a K-injective complex, in the ringed-space spelling of the internal Hom complex.
* `derivedCore_of_cochainCore`: the derived identity at `Q I` from the cochain-level identity
  for `cu` at a K-injective `I`.

## References

* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules (derivedSheafHom ringedSite)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

/-- K-injectivity of a complex of `𝒪_W`-modules, read in the spelling `structureSheaf W.sheaf` of
the sheaf of rings that the internal Hom complex of a ringed space uses. The two spellings are
`structureSheafRing W` unfolded. -/
instance isKInjective_structureSheafSpelling (W : AlgebraicGeometry.RingedSpace.{u, u})
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing W)) ℤ) [hI : I.IsKInjective] :
    CochainComplex.IsKInjective (C := SheafOfModules.{u} (_root_.structureSheaf W.sheaf))
      (show CochainComplex (SheafOfModules.{u} (_root_.structureSheaf W.sheaf)) ℤ from I) :=
  hI

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- **The trivialisation of `R ℰom_Z(𝒪_Z[0], -)` at `R ℰom(𝒪_Z, Q I)` for a K-injective `I`.**

Conjugated by the identification `…derivedSheafHomExactSupportKInjectiveIso` of
`R ℰom(𝒪_Z, Q I)` with the class of the degreewise `ℰom^•(𝒪_Z, I)`, and preceded by the
K-injective model comparison for `R ℰom_Z(𝒪_Z[0], -)`, it is the class of evaluation at the unit
section `AlgebraicGeometry.RingedSite.structureSheafHomEvaluation`. -/
theorem derivedStructureSheafHomIso_exactSupport_kInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    (Stacks.SheafOfModules.derivedSheafHomComparison S.Z.sheaf
          (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))
          ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).inv ≫
        ((derivedSheafHom S.Z.sheaf).obj
              (op (RingedSite.derivedStructureSheaf (ringedSite S.Z.sheaf)))).map
            (S.derivedSheafHomExactSupportKInjectiveIso I).inv ≫
          (RingedSite.derivedStructureSheafHomNatIso (ringedSite S.Z.sheaf)).hom.app
              (S.derivedSheafHomExactSupport.obj (DerivedCategory.Q.obj I)) ≫
            (S.derivedSheafHomExactSupportKInjectiveIso I).hom =
      DerivedCategory.Q.map (RingedSite.structureSheafHomEvaluation (ringedSite S.Z.sheaf)
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) := by
  have h1 := RingedSite.derivedStructureSheafHomIso_naturality (ringedSite S.Z.sheaf)
    (S.derivedSheafHomExactSupportKInjectiveIso I).inv
  have hmodel := @RingedSite.derivedStructureSheafHomIso_model (ringedSite S.Z.sheaf) _
    ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    (S.isKInjective_sheafHomExactSupport I)
  have key : ((derivedSheafHom S.Z.sheaf).obj
            (op (RingedSite.derivedStructureSheaf (ringedSite S.Z.sheaf)))).map
          (S.derivedSheafHomExactSupportKInjectiveIso I).inv ≫
        (RingedSite.derivedStructureSheafHomNatIso (ringedSite S.Z.sheaf)).hom.app
            (S.derivedSheafHomExactSupport.obj (DerivedCategory.Q.obj I)) ≫
          (S.derivedSheafHomExactSupportKInjectiveIso I).hom =
      (RingedSite.derivedStructureSheafHomIso (ringedSite S.Z.sheaf)
        (DerivedCategory.Q.obj
          ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))).hom :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t ↦ t ≫ (S.derivedSheafHomExactSupportKInjectiveIso I).hom) h1).trans
        ((Category.assoc _ _ _).trans
          ((congrArg
              (fun t ↦ (RingedSite.derivedStructureSheafHomIso (ringedSite S.Z.sheaf)
                (DerivedCategory.Q.obj
                  ((S.sheafHomExactSupport.mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj I))).hom ≫ t)
              (S.derivedSheafHomExactSupportKInjectiveIso I).inv_hom_id).trans
            (Category.comp_id _))))
  refine (congrArg
    (fun t ↦ (Stacks.SheafOfModules.derivedSheafHomComparison S.Z.sheaf
        (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).inv ≫ t)
    (key.trans hmodel)).trans ?_
  exact (Stacks.SheafOfModules.derivedSheafHomComparison S.Z.sheaf
    (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))
    ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).inv_hom_id_assoc
      (DerivedCategory.Q.map (RingedSite.structureSheafHomEvaluation (ringedSite S.Z.sheaf)
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))

/-- **The trivialisation of `R ℰom_X(𝒪_X[0], -)` at the class of a K-injective complex** is the
K-injective model comparison `Stacks.SheafOfModules.derivedSheafHomComparison` followed by the
class of evaluation at the unit section. -/
theorem derivedStructureSheafHomNatIso_hom_app_Q (W : AlgebraicGeometry.RingedSpace.{u, u})
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing W)) ℤ) [I.IsKInjective] :
    (RingedSite.derivedStructureSheafHomNatIso (ringedSite W.sheaf)).hom.app
        (DerivedCategory.Q.obj I) =
      (Stacks.SheafOfModules.derivedSheafHomComparison W.sheaf
          (RingedSite.structureSheafComplex (ringedSite W.sheaf)) I).hom ≫
        DerivedCategory.Q.map
          (RingedSite.structureSheafHomEvaluation (ringedSite W.sheaf) I) :=
  @RingedSite.derivedStructureSheafHomIso_model (ringedSite W.sheaf) _ I ‹_›

/-- **The `X`-side of the derived identity of [Stacks, Tag 0E2I] at the source `𝒪_Z[0]`.**

Restriction along a morphism `u : 𝒪_X[0] ⟶ Ri_* 𝒪_Z[0]` of `D(𝒪_X)` whose composite with
`CategoryTheory.Functor.mapDerivedCategoryFactors` is the class of a morphism of complexes
`cu : 𝒪_X[0] ⟶ i_*(𝒪_Z[0])`, followed by the trivialisation of `R ℰom_X(𝒪_X[0], -)` at the class
of a K-injective complex, is: the first factor of `…derivedSheafHomPushforwardModelIso`, then its
second factor, then the class of restriction along `cu` followed by evaluation at the unit
section. -/
theorem derivedStructureSheafHomNatIso_restrict_eq
    (cu : RingedSite.structureSheafComplex (ringedSite S.X.sheaf) ⟶
      ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf)))
    (u : RingedSite.derivedStructureSheaf (ringedSite S.X.sheaf) ⟶
      (modulePushforward S.i).mapDerivedCategory.obj
        (RingedSite.derivedStructureSheaf (ringedSite S.Z.sheaf)))
    (hu : u ≫ (modulePushforward S.i).mapDerivedCategoryFactors.hom.app
          (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf)) =
        DerivedCategory.Q.map cu)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    ((derivedSheafHom S.X.sheaf).map u.op).app (DerivedCategory.Q.obj I) ≫
        (RingedSite.derivedStructureSheafHomNatIso (ringedSite S.X.sheaf)).hom.app
          (DerivedCategory.Q.obj I) =
      ((derivedSheafHom S.X.sheaf).map
            (Quiver.Hom.op ((modulePushforward S.i).mapDerivedCategoryFactors.inv.app
              (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))))).app
          (DerivedCategory.Q.obj I) ≫
        (Stacks.SheafOfModules.derivedSheafHomComparison S.X.sheaf
            (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))) I).hom ≫
          DerivedCategory.Q.map
            (sheafHomComplexHomMap S.X cu (𝟙 I) ≫
              RingedSite.structureSheafHomEvaluation (ringedSite S.X.sheaf) I) := by
  have hu' : u = DerivedCategory.Q.map cu ≫
      (modulePushforward S.i).mapDerivedCategoryFactors.inv.app
        (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf)) :=
    ((Category.comp_id u).symm.trans
      (congrArg (fun t ↦ u ≫ t)
        ((modulePushforward S.i).mapDerivedCategoryFactors.hom_inv_id_app
          (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))).symm)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun t ↦ t ≫
          (modulePushforward S.i).mapDerivedCategoryFactors.inv.app
            (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))) hu))
  refine Eq.trans (congrArg (fun t ↦ t ≫ (RingedSite.derivedStructureSheafHomNatIso
    (ringedSite S.X.sheaf)).hom.app (DerivedCategory.Q.obj I))
    ((congrArg (fun t ↦ ((derivedSheafHom S.X.sheaf).map
          (Quiver.Hom.op t)).app (DerivedCategory.Q.obj I)) hu').trans
      (NatTrans.congr_app
        ((derivedSheafHom S.X.sheaf).map_comp
          (Quiver.Hom.op ((modulePushforward S.i).mapDerivedCategoryFactors.inv.app
            (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))))
          (Quiver.Hom.op (DerivedCategory.Q.map cu))) (DerivedCategory.Q.obj I)))) ?_
  refine Eq.trans (congrArg (fun t ↦ _ ≫ t)
    (derivedStructureSheafHomNatIso_hom_app_Q S.X I)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun t ↦ _ ≫ t) ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun t ↦ t ≫ DerivedCategory.Q.map
        (RingedSite.structureSheafHomEvaluation (ringedSite S.X.sheaf) I))
      (derivedSheafHomComparison_naturality_source S.X cu I)).trans
      (Category.assoc _ _ _)))) ?_
  exact congrArg (fun t ↦ _ ≫ _ ≫ t) (DerivedCategory.Q.map_comp _ _).symm

/-- The forward map of the image under `derivedSheafHom` of the inverse of
`mapDerivedCategoryFactors` at `𝒪_Z[0]`, evaluated at `Q I`, is the image of its inverse
component. -/
theorem derivedSheafHom_map_mapDerivedCategoryFactors_symm_op
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    (((derivedSheafHom S.X.sheaf).mapIso
        ((modulePushforward S.i).mapDerivedCategoryFactors.app
          (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))).symm.op).app
        (DerivedCategory.Q.obj I)).hom =
      ((derivedSheafHom S.X.sheaf).map
        (Quiver.Hom.op ((modulePushforward S.i).mapDerivedCategoryFactors.inv.app
          (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))))).app
        (DerivedCategory.Q.obj I) :=
  rfl

/-- The `Z`-side trivialisation at `derivedSheafHomExactSupport` of the class of a K-injective
complex, pushed forward between the two identifications of `Ri_*` and followed by the degreewise
trace, is the class of the pushforward of evaluation at the unit section followed by the trace. -/
theorem pushforward_derivedStructureSheafHomIso_exactSupport_kInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    (modulePushforward S.i).mapDerivedCategoryFactors.inv.app
          (Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf
            (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))
            ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).obj ≫
        (modulePushforward S.i).mapDerivedCategory.map
          ((Stacks.SheafOfModules.derivedSheafHomComparison S.Z.sheaf
            (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))
            ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).inv ≫
          ((derivedSheafHom S.Z.sheaf).obj
                (op (RingedSite.derivedStructureSheaf (ringedSite S.Z.sheaf)))).map
              (S.derivedSheafHomExactSupportKInjectiveIso I).inv ≫
            (RingedSite.derivedStructureSheafHomNatIso (ringedSite S.Z.sheaf)).hom.app
                (S.derivedSheafHomExactSupport.obj (DerivedCategory.Q.obj I)) ≫
              (S.derivedSheafHomExactSupportKInjectiveIso I).hom) ≫
          (modulePushforward S.i).mapDerivedCategoryFactors.hom.app
              ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
            DerivedCategory.Q.map
              ((Adjunction.mapHomologicalComplexAdjunction
                S.modulePushforwardSheafHomExactSupportAdjunction
                  (ComplexShape.up ℤ)).counit.app I) =
      DerivedCategory.Q.map
        (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (RingedSite.structureSheafHomEvaluation (ringedSite S.Z.sheaf)
              ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
          (Adjunction.mapHomologicalComplexAdjunction
            S.modulePushforwardSheafHomExactSupportAdjunction
              (ComplexShape.up ℤ)).counit.app I) := by
  have hnat := (modulePushforward S.i).mapDerivedCategoryFactors_hom_naturality
    (RingedSite.structureSheafHomEvaluation (ringedSite S.Z.sheaf)
      ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
  have hkey := S.derivedStructureSheafHomIso_exactSupport_kInjective I
  have hstep :
      (modulePushforward S.i).mapDerivedCategoryFactors.inv.app
            (Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf
              (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))
              ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).obj ≫
          (modulePushforward S.i).mapDerivedCategory.map
              (DerivedCategory.Q.map
                (RingedSite.structureSheafHomEvaluation (ringedSite S.Z.sheaf)
                  ((S.sheafHomExactSupport.mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj I))) ≫
            (modulePushforward S.i).mapDerivedCategoryFactors.hom.app
                ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
              DerivedCategory.Q.map
                ((Adjunction.mapHomologicalComplexAdjunction
                  S.modulePushforwardSheafHomExactSupportAdjunction
                    (ComplexShape.up ℤ)).counit.app I) =
        DerivedCategory.Q.map
          (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (RingedSite.structureSheafHomEvaluation (ringedSite S.Z.sheaf)
                ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
            (Adjunction.mapHomologicalComplexAdjunction
              S.modulePushforwardSheafHomExactSupportAdjunction
                (ComplexShape.up ℤ)).counit.app I) := by
    refine Eq.trans (congrArg
      (fun t ↦ (modulePushforward S.i).mapDerivedCategoryFactors.inv.app
        (Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf
          (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))
          ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).obj ≫ t)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t ↦ t ≫ DerivedCategory.Q.map
            ((Adjunction.mapHomologicalComplexAdjunction
              S.modulePushforwardSheafHomExactSupportAdjunction
                (ComplexShape.up ℤ)).counit.app I)) hnat).trans
          (Category.assoc _ _ _)))) ?_
    refine Eq.trans ((Category.assoc _ _ _).symm.trans (congrArg
      (fun t ↦ t ≫ DerivedCategory.Q.map
          (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (RingedSite.structureSheafHomEvaluation (ringedSite S.Z.sheaf)
              ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplexAdjunction
            S.modulePushforwardSheafHomExactSupportAdjunction
              (ComplexShape.up ℤ)).counit.app I))
      ((modulePushforward S.i).mapDerivedCategoryFactors.inv_hom_id_app
        (Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf
          (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))
          ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).obj))) ?_
    exact (Category.id_comp _).trans (DerivedCategory.Q.map_comp _ _).symm
  exact (congrArg
        (fun t ↦ (modulePushforward S.i).mapDerivedCategoryFactors.inv.app
            (Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf
              (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))
              ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).obj ≫
          (modulePushforward S.i).mapDerivedCategory.map t ≫
            (modulePushforward S.i).mapDerivedCategoryFactors.hom.app
                ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
              DerivedCategory.Q.map
                ((Adjunction.mapHomologicalComplexAdjunction
                  S.modulePushforwardSheafHomExactSupportAdjunction
                    (ComplexShape.up ℤ)).counit.app I))
    hkey).trans hstep

attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf
  CategoryTheory.sheafCompose in
/-- **The `Z`-side of the derived identity of [Stacks, Tag 0E2I] at the source `𝒪_Z[0]`.**

The component formula of [Stacks, Tag 0E2I] at the class of a K-injective complex
(`…derivedSheafHomPushforwardModelIso`), followed by the trivialisation of `R ℰom_Z(𝒪_Z[0], -)`
pushed forward and by the trace of [Stacks, Tag 0A76], is: the formula's first two factors,
followed by the class of the complex-level identification read backwards, the pushforward of
evaluation at the unit section on `Z`, and the degreewise trace of [Stacks, Tag 0A75]. -/
theorem derivedSheafHomPushforwardModelIso_structureSheaf_comp
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    (S.derivedSheafHomPushforwardModelIso
          (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf)) I).hom ≫
        (modulePushforward S.i).mapDerivedCategory.map
            ((RingedSite.derivedStructureSheafHomNatIso (ringedSite S.Z.sheaf)).hom.app
              (S.derivedSheafHomExactSupport.obj (DerivedCategory.Q.obj I))) ≫
          S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
            (DerivedCategory.Q.obj I) =
      ((derivedSheafHom S.X.sheaf).map
            (Quiver.Hom.op ((modulePushforward S.i).mapDerivedCategoryFactors.inv.app
              (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))))).app
          (DerivedCategory.Q.obj I) ≫
        (Stacks.SheafOfModules.derivedSheafHomComparison S.X.sheaf
            (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))) I).hom ≫
          DerivedCategory.Q.map
            ((S.pushforwardSheafHomComplex.iso
                  (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf)) I).inv ≫
              ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map
                  (RingedSite.structureSheafHomEvaluation (ringedSite S.Z.sheaf)
                    ((S.sheafHomExactSupport.mapHomologicalComplex
                      (ComplexShape.up ℤ)).obj I)) ≫
                (Adjunction.mapHomologicalComplexAdjunction
                  S.modulePushforwardSheafHomExactSupportAdjunction
                    (ComplexShape.up ℤ)).counit.app I) := by
  have composeMappedChain {sourceCategory targetCategory : Type (u + 1)}
      [Category.{u + 1} sourceCategory] [Category.{u + 1} targetCategory]
      (mapFunctor : sourceCategory ⥤ targetCategory)
      {source0 source1 source2 source3 source4 : sourceCategory}
      {outer0 outer1 outer2 input output finish : targetCategory}
      (firstPrefix : outer0 ⟶ outer1) (secondPrefix : outer1 ⟶ outer2)
      (thirdPrefix : outer2 ⟶ input) (enter : input ⟶ mapFunctor.obj source0)
      (firstArrow : source0 ⟶ source1) (secondArrow : source1 ⟶ source2)
      (thirdArrow : source2 ⟶ source3) (fourthArrow : source3 ⟶ source4)
      (leave : mapFunctor.obj source4 ⟶ output) (lastArrow : output ⟶ finish)
      (result : input ⟶ finish)
      (equation : enter ≫ mapFunctor.map (firstArrow ≫ secondArrow ≫ thirdArrow ≫ fourthArrow) ≫
        leave ≫ lastArrow = result) :
      firstPrefix ≫ secondPrefix ≫ thirdPrefix ≫ enter ≫ mapFunctor.map firstArrow ≫
          mapFunctor.map secondArrow ≫ mapFunctor.map thirdArrow ≫ mapFunctor.map fourthArrow ≫
          leave ≫ lastArrow = firstPrefix ≫ secondPrefix ≫ thirdPrefix ≫ result := by
    simp only [Functor.map_comp, Category.assoc] at equation ⊢
    exact congrArg (fun morphism ↦ firstPrefix ≫ secondPrefix ≫ thirdPrefix ≫ morphism) equation
  refine Eq.trans ?_
    (congrArg (· ≫ _) (S.derivedSheafHom_map_mapDerivedCategoryFactors_symm_op I))
  dsimp only [derivedSheafHomPushforwardModelIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Functor.mapIso_inv, Iso.op_hom, Iso.app_inv]
  rw [S.derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app_Q_of_isKInjective I]
  simp only [Category.assoc]
  refine Eq.trans (composeMappedChain (modulePushforward S.i).mapDerivedCategory
    _ _ _ _ _ _ _ _ _ _ _
    (S.pushforward_derivedStructureSheafHomIso_exactSupport_kInjective I)) ?_
  exact congrArg (fun morphism ↦ _ ≫ _ ≫ morphism) (DerivedCategory.Q.map_comp _ _).symm

/-- **The derived identity of [Stacks, Tag 0E2I] at the source `𝒪_Z[0]`, from the cochain-level
one.**

Let `cu : 𝒪_X[0] ⟶ i_*(𝒪_Z[0])` be a morphism of complexes and `u : 𝒪_X[0] ⟶ Ri_* 𝒪_Z[0]` a
morphism of `D(𝒪_X)` whose composite with
`CategoryTheory.Functor.mapDerivedCategoryFactors` is the class of `cu`.  At a K-injective
cochain complex `I`, if the identification
`i_* SheafHom^•_Z(𝒪_Z[0], ℰom^•(𝒪_Z, I)) ≅ SheafHom^•_X(i_* 𝒪_Z[0], I)` of [Stacks, Tag 0E2I],
read backwards and followed by the pushforward of evaluation at the unit section on `Z` and by
the degreewise trace of [Stacks, Tag 0A75], is restriction along `cu` followed by evaluation at
the unit section on `X`, then restriction along `u` followed by the trivialisation of
`R ℰom_X(𝒪_X[0], -)` is the component formula of [Stacks, Tag 0E2I] at the class of `I`, followed
by the trivialisation of `R ℰom_Z(𝒪_Z[0], -)` pushed forward and by the trace of
[Stacks, Tag 0A76]. -/
theorem derivedCore_of_cochainCore
    (cu : RingedSite.structureSheafComplex (ringedSite S.X.sheaf) ⟶
      ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf)))
    (u : RingedSite.derivedStructureSheaf (ringedSite S.X.sheaf) ⟶
      (modulePushforward S.i).mapDerivedCategory.obj
        (RingedSite.derivedStructureSheaf (ringedSite S.Z.sheaf)))
    (hu : u ≫ (modulePushforward S.i).mapDerivedCategoryFactors.hom.app
          (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf)) =
        DerivedCategory.Q.map cu)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective]
    (hc : (S.pushforwardSheafHomComplex.iso
            (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf)) I).inv ≫
          ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (RingedSite.structureSheafHomEvaluation (ringedSite S.Z.sheaf)
                ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
            (Adjunction.mapHomologicalComplexAdjunction
              S.modulePushforwardSheafHomExactSupportAdjunction
                (ComplexShape.up ℤ)).counit.app I =
        sheafHomComplexHomMap S.X cu (𝟙 I) ≫
          RingedSite.structureSheafHomEvaluation (ringedSite S.X.sheaf) I) :
    ((derivedSheafHom S.X.sheaf).map u.op).app (DerivedCategory.Q.obj I) ≫
        (RingedSite.derivedStructureSheafHomNatIso (ringedSite S.X.sheaf)).hom.app
          (DerivedCategory.Q.obj I) =
      (S.derivedSheafHomPushforwardModelIso
            (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf)) I).hom ≫
        (modulePushforward S.i).mapDerivedCategory.map
            ((RingedSite.derivedStructureSheafHomNatIso (ringedSite S.Z.sheaf)).hom.app
              (S.derivedSheafHomExactSupport.obj (DerivedCategory.Q.obj I))) ≫
          S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
            (DerivedCategory.Q.obj I) :=
  (S.derivedStructureSheafHomNatIso_restrict_eq cu u hu I).trans
    ((congrArg
        (fun t ↦ ((derivedSheafHom S.X.sheaf).map
              (Quiver.Hom.op ((modulePushforward S.i).mapDerivedCategoryFactors.inv.app
                (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))))).app
            (DerivedCategory.Q.obj I) ≫
          (Stacks.SheafOfModules.derivedSheafHomComparison S.X.sheaf
              (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (RingedSite.structureSheafComplex (ringedSite S.Z.sheaf))) I).hom ≫
            DerivedCategory.Q.map t) hc).symm.trans
      (S.derivedSheafHomPushforwardModelIso_structureSheaf_comp I).symm)

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
