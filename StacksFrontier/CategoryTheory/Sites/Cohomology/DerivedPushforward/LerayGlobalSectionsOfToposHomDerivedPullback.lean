module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PostcompIntoPushforwardOfKInjectiveGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedGlobalSectionsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSectionsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsCorepresentable

/-!
# The Leray comparison for global sections along a morphism of ringed topoi

For a morphism `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` of ringed topoi in the sense of Stacks 01D3,
with objects in any universe, the derived global sections of `Rf_*K` are the derived global
sections of `K`: `RΓ(D, Rf_*K) ≅ RΓ(C, K)` for unbounded `K`, as for a morphism of ringed sites
in `LerayForUnboundedGlobalSectionsGeneral.lean`.

## References

* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.Cohomology.SiteModules
open CochainComplex.HomComplex

universe u c

/-! ### The chain for a morphism of ringed topoi -/

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat hasResolutions_isKFlat)

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X Y : RingedTopos.{u, c, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  [IsGrothendieckAbelian.{u}
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))]
  (f : RingedToposHom X Y)

/-- The comparison `f_* ⟶ Rf_*` of the unbounded derived direct image along a morphism of
ringed topoi. -/
noncomputable abbrev derivedPushforwardUnit :
    pushforwardOnHomotopy (X := X) (Y := Y) f ⟶
      DerivedCategory.Qh ⋙ derivedPushforward (X := X) (Y := Y) f :=
  (pushforwardOnHomotopy (X := X) (Y := Y) f).totalRightDerivedUnit DerivedCategory.Qh
    (sourceQuasiIso X)

/-- **The derived transposition is the degreewise one**, for a morphism of ringed topoi. For
`g : P ⟶ f_* K` in the unbounded homotopy category, transposing `Q(g)` followed by
`f_* K ⟶ Rf_* K` along `Lf^* ⊣ Rf_*` gives `Lf^* P ⟶ f^* P` followed by the localization of the
degreewise transpose of `g`. This is Stacks 0FPI at `K` and the naturality of `Lf^* ⟶ f^*`. -/
theorem derivedAdjunction_homEquiv_symm_qh_map
    (P : HomotopyCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))
      (ComplexShape.up ℤ))
    (K : HomotopyCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))
      (ComplexShape.up ℤ))
    (g : P ⟶ (pushforwardMapHomotopy f).obj K) :
    ((derivedAdjunction f).homEquiv (DerivedCategory.Qh.obj P)
        (DerivedCategory.Qh.obj K)).symm
        (DerivedCategory.Qh.map g ≫ (derivedPushforwardUnit f).app K) =
      (derivedPullbackComparison f).app P ≫ DerivedCategory.Qh.map
        (((pullbackAdjPushforwardMapHomotopy f).homEquiv P K).symm g) := by
  rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    derivedAdjunction_counit_fac f K, Adjunction.homEquiv_counit, Functor.map_comp,
    ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ DerivedCategory.Qh.map
    ((pullbackAdjPushforwardMapHomotopy f).counit.app K))
    ((derivedPullbackComparison f).naturality g)

/-- **Localization is bijective on morphisms into the direct image of a K-injective complex**,
along a morphism of ringed topoi, out of any `P` at which `Lf^* ⟶ f^*` is invertible: both sides
are `Hom(f^* P, I)`, by the degreewise and by the derived adjunction, and the two
identifications agree by `derivedAdjunction_homEquiv_symm_qh_map`. -/
theorem bijective_qh_map_pushforward_of_isKInjective
    (P : HomotopyCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))
      (ComplexShape.up ℤ))
    [IsIso ((derivedPullbackComparison f).app P)]
    (I : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) ℤ)
    (hI : I.IsKInjective) :
    Function.Bijective (DerivedCategory.Qh.map :
      (P ⟶ (pushforwardMapHomotopy f).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) → _) := by
  have := hI
  set Iq := (HomotopyCategory.quotient
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))
    (ComplexShape.up ℤ)).obj I with hIq
  have : IsIso ((derivedPushforwardUnit f).app Iq) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ DerivedCategory.Qh _
      (derivedPushforwardUnit f) I hI
  have hu : Function.Bijective
      (fun q => ((derivedAdjunction f).homEquiv (DerivedCategory.Qh.obj P)
        (DerivedCategory.Qh.obj Iq)).symm (q ≫ (derivedPushforwardUnit f).app Iq)) :=
    (((derivedAdjunction f).homEquiv (DerivedCategory.Qh.obj P)
      (DerivedCategory.Qh.obj Iq)).symm.bijective).comp
        (asIso ((derivedPushforwardUnit f).app Iq)).homToEquiv.bijective
  have hpre : Function.Bijective (fun h : DerivedCategory.Qh.obj
      ((pullbackMapHomotopy f).obj P) ⟶ DerivedCategory.Qh.obj Iq =>
        (derivedPullbackComparison f).app P ≫ h) :=
    (asIso ((derivedPullbackComparison f).app P)).homFromEquiv.symm.bijective
  refine (Function.Bijective.of_comp_iff' hu _).1 ?_
  have hfun : (fun q => ((derivedAdjunction f).homEquiv (DerivedCategory.Qh.obj P)
        (DerivedCategory.Qh.obj Iq)).symm (q ≫ (derivedPushforwardUnit f).app Iq)) ∘
      (DerivedCategory.Qh.map : (P ⟶ (pushforwardMapHomotopy f).obj Iq) → _) =
      (fun h : DerivedCategory.Qh.obj ((pullbackMapHomotopy f).obj P) ⟶
          DerivedCategory.Qh.obj Iq => (derivedPullbackComparison f).app P ≫ h) ∘
        (DerivedCategory.Qh.map : ((pullbackMapHomotopy f).obj P ⟶ Iq) → _) ∘
        ((pullbackAdjPushforwardMapHomotopy f).homEquiv P Iq).symm :=
    funext fun g => derivedAdjunction_homEquiv_symm_qh_map f P Iq g
  exact hfun ▸ hpre.comp
    ((CochainComplex.IsKInjective.Qh_map_bijective ((pullbackMapHomotopy f).obj P) I).comp
      ((pullbackAdjPushforwardMapHomotopy f).homEquiv P Iq).symm.bijective)

/-- **Postcomposition with a K-injective resolution of `f_* I`, shifted, is bijective**, along a
morphism of ringed topoi and out of any `P` at which `Lf^* ⟶ f^*` is invertible. Localization is
bijective on morphisms into `(f_* I)⟦n⟧ = f_*(I⟦n⟧)` and into `J⟦n⟧`, and `Q(s⟦n⟧)` is
invertible. -/
theorem bijective_postcomp_quotient_shift_of_isKInjective
    (P : HomotopyCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))
      (ComplexShape.up ℤ))
    [IsIso ((derivedPullbackComparison f).app P)]
    (I : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) ℤ)
    (hI : I.IsKInjective)
    {J : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) ℤ}
    (s : ((RingedToposHom.pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶
      J)
    (hJ : J.IsKInjective) (hs : QuasiIso s) (n : ℤ) :
    Function.Bijective
      (fun a : P ⟶ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((((RingedToposHom.pushforwardModules f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I)⟦n⟧) =>
        a ≫ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (s⟦n⟧')) := by
  have := hJ
  have := hs
  have := hI
  have hleft : Function.Bijective (DerivedCategory.Qh.map :
      (P ⟶ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((((RingedToposHom.pushforwardModules f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)⟦n⟧)) → _) :=
    Stacks.Cohomology.DerivedPullbackOnRingedTopoi.bijective_qh_map_of_iso_general
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
        ((((RingedToposHom.pushforwardModules f).mapHomologicalComplex
          (ComplexShape.up ℤ)).commShiftIso n).app I)).symm
      (bijective_qh_map_pushforward_of_isKInjective f P (I⟦n⟧) inferInstance)
  have hright := CochainComplex.IsKInjective.Qh_map_bijective P (J⟦n⟧)
  have hcomp : (DerivedCategory.Qh.map : (P ⟶ _) → _) ∘
        (fun a : P ⟶ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((((RingedToposHom.pushforwardModules f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)⟦n⟧) =>
          a ≫ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (s⟦n⟧')) =
      (fun b => b ≫ DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (s⟦n⟧'))) ∘
        (DerivedCategory.Qh.map : (P ⟶ _) → _) :=
    funext fun a => DerivedCategory.Qh.map_comp a _
  have hpost : Function.Bijective (fun b : DerivedCategory.Qh.obj P ⟶ _ =>
      b ≫ DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (s⟦n⟧'))) :=
    (asIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (s⟦n⟧')))).homToEquiv.bijective
  exact (Function.Bijective.of_comp_iff' hright _).1 (hcomp ▸ hpost.comp hleft)

omit [IsGrothendieckAbelian.{u}
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))] in
/-- **The comparison `Lf^* ⟶ f^*` is invertible at `O_D[0]`** along a morphism of ringed topoi:
`O_D[0]` is K-flat with flat terms (Stacks 06YY). -/
theorem isIso_derivedPullbackComparison_app_single_unit :
    IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))
        (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) 0).obj
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))))) :=
  isIso_derivedPullbackComparison_app f (IsKFlat (Y := Y)) (hasResolutions_isKFlat (Y := Y))
    (pullbackInvertsQuasiIso_isKFlat f) _
    ⟨Stacks.SheafOfModules.isKFlat_single_unit Y.O, isFlat_single_unit_X⟩

end Stacks.Cohomology.DerivedPullbackOfToposHom

namespace Stacks.Cohomology.LerayUnbounded

/-! ### Global sections along a morphism of ringed topoi -/

section ToposHom

open Stacks.Cohomology.DerivedPushforward Stacks.Cohomology.DerivedPullbackOfToposHom

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {X Y : RingedTopos.{u, c, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  [IsGrothendieckAbelian.{u}
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))]
  [IsGrothendieckAbelian.{u}
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))]
  (f : RingedToposHom X Y)

omit [IsGrothendieckAbelian.{u}
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))] in
/-- **A K-injective resolution of `f_* I` induces a quasi-isomorphism on global sections**,
along a morphism of ringed topoi. Global sections are corepresented by the structure sheaf
(`Stacks.Cohomology.SiteModules.coyonedaUnitGlobalSectionsIso`), so on degree-`n` cohomology,
read in abelian groups, the induced map is postcomposition with `s⟦n⟧` on morphisms out of
`O_D[0]` in the homotopy category, which `bijective_postcomp_quotient_shift_of_isKInjective`
makes bijective; `forget₂` preserves and reflects homology. -/
theorem quasiIso_globalSections_map_of_toposHom
    (I : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) ℤ)
    (hI : I.IsKInjective)
    {J : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) ℤ}
    (s : ((RingedToposHom.pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶
      J)
    (hJ : J.IsKInjective) (hs : QuasiIso s) :
    QuasiIso (((globalSectionsFunctor.{c, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map s) := by
  have :=
    Stacks.Cohomology.DerivedPullbackOfToposHom.isIso_derivedPullbackComparison_app_single_unit f
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat.{max c u}
      (RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)).obj))
      AddCommGrpCat.{max c u}),
    quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : IsIso (HomologicalComplex.homologyMap (homComplexPostcomp
      ((CochainComplex.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) 0).obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))) s) n) :=
    Stacks.Injectives.isIso_homologyMap_homComplexPostcomp _ s n
      (bijective_postcomp_quotient_shift_of_isKInjective f _ I hI s hJ hs n)
  refine (NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex
      (coyonedaUnitGlobalSectionsIso (J := Y.J)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))
      (ComplexShape.up ℤ))
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{max c u} (ComplexShape.up ℤ) n)) s).1 ?_
  exact isIso_homologyMap_coyonedaComplexMap _ s n

variable [HasDerivedCategory.{max c (u + 1)}
  (ModuleCat.{max c u}
    (RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)).obj))]

/-- **The hypothesis of Stacks 0D6H's global-sections clause, for a morphism of ringed topoi.**
`f_* I` computes `RΓ(D, -)` for every K-injective complex `I` of `O_C`-modules, for every model
of `D(Γ(O_D))`: on a K-injective resolution `s : f_* I ⟶ J` global sections give a
quasi-isomorphism (`quasiIso_globalSections_map_of_toposHom`), and the comparison of `RΓ(D, -)`
is invertible at the K-injective `J`. -/
theorem computesSecond_pushforwardModules_globalSections :
    ComputesSecond (RingedToposHom.pushforwardModules f)
      (globalSectionsFunctor.{c, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) := by
  intro I hI
  obtain ⟨J, s, hJ, hs⟩ := Stacks.Cohomology.Localization.enoughKInjectives
    (((RingedToposHom.pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  have hq := quasiIso_globalSections_map_of_toposHom f I hI s hJ hs
  refine isIso_of_comp_sq ((totalDerivedUnit
    (globalSectionsFunctor.{c, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)) ?_ ?_ ?_
  · exact @isIso_Qh_map_quotient_map_of_quasiIso _ _ _ _ _ _ _ hq
  · have := hJ
    exact Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ J
  · have := isIso_Qh_map_quotient_map_of_quasiIso s
    exact ((Stacks.DerivedFunctor.totalRightDerived
      (globalSectionsFunctor.{c, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).mapIso
      (asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _
        (ComplexShape.up ℤ)).map s)))).isIso_hom

/-- **Stacks 0D6H, the global-sections clause, for a morphism of ringed topoi.** Let
`f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. Then
`RΓ(D, -) ∘ Rf_* = RΓ(C, -)` as functors `D(O_C) ⟶ D(Γ(O_D))`, the right hand side being derived
global sections on `C` with scalars restricted along `Γ(O_D) ⟶ Γ(O_C)`, for every model of
`D(Γ(O_D))`. -/
noncomputable def derivedGlobalSectionsPushforwardIsoOfToposHom :
    derivedPushforward (X := X) (Y := Y) f ⋙
        DerivedFunctor.totalRightDerived
          (globalSectionsFunctor.{c, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) ≅
      DerivedFunctor.totalRightDerived
        (globalSectionsFunctor.{c, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) ⋙
          ModuleCat.restrictScalars (globalSectionsRingHom f.toRingedToposModulesHom)) :=
  derivedCompIsoOfComputes (RingedToposHom.pushforwardModules f)
    (globalSectionsFunctor.{c, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))
    (globalSectionsFunctor.{c, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) ⋙
      ModuleCat.restrictScalars (globalSectionsRingHom f.toRingedToposModulesHom))
    (Functor.isoWhiskerRight (RingedToposHom.pushforwardModulesIso f).symm
        (globalSectionsFunctor.{c, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) ≪≫
      globalSectionsPushforwardIso f.toRingedToposModulesHom)
    (computesSecond_pushforwardModules_globalSections f)

end ToposHom

end Stacks.Cohomology.LerayUnbounded

end
