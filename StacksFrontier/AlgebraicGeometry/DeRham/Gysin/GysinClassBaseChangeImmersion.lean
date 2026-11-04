module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.ChartDataExcision
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinClassBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDerivedSupportImmersion

/-!
# The degree-`p` reading of the square of Tag 0G7U, along an arbitrary open immersion

`Stacks.Gysin.map_extendHomologyToSupport_comp_supportCohomologyRestrictIso` of
`GysinClassBaseChange.lean` reads the derived square of [Stacks, Tag 0G7U] in degree `p` for the
leg `W.ι` of an open subscheme.  This file does the same for an **arbitrary** open immersion
`g : X' ⟶ X` of schemes.

That generality is what the two-chart comparison of [Stacks, Tag 0G86] needs: the chart-to-chart
leg is `AlgebraicGeometry.Scheme.homOfLE`, an open immersion which is not the canonical inclusion
of an open subscheme, and an open immersion factors as an isomorphism onto its range followed by
such an inclusion — so the `W.ι` statements cannot produce the general one.

## Main definitions

* `Stacks.Gysin.cechExtendHomologyImmersionIso`: **the restriction along `g` of the degree-`p`
  cohomology of the extended alternating Čech complex is the degree-`p` cohomology of the
  extended alternating Čech complex of the restricted equations.**
* `Stacks.Gysin.cechHomologyImmersionIso`: the same on the `ℕ`-graded Čech complex of
  [Stacks, Tag 0G7I].

## Main results

* `Stacks.Gysin.map_extendHomologyToSupport_comp_supportCohomologyOpenImmersionIso`: **the
  degree-`p` reading of the square of [Stacks, Tag 0G7U] along an arbitrary open immersion.**
* `Stacks.Gysin.map_cechHomologyToSupport_comp_supportCohomologyOpenImmersionIso`: the same on
  the cohomology of the `ℕ`-graded Čech complex, which is the shape
  `Stacks.Perfect.SupportedFraction.supportedFractionSource_eq` consumes.

## Implementation notes

**Nothing new is proved here.**  Every input is already general: the derived square is
`map_cechToDerivedSupport_comp_supportPushPullbackIso_hom` of
`Stacks.Perfect.CechDerivedSupportImmersion`, the excision is
`Stacks.Gysin.supportCohomologyOpenImmersionIso`, and the four passages between
the derived and the abelian category — `singleMapHomologicalComplex_natIso`,
`mapHomologicalComplexHomologyIso_natIso`, `mapDerivedCategoryHomologyIso_inv_app_Q` and
`homologyFunctorFactors_inv_naturality` — are stated at a variable functor in
`GysinClassBaseChange.lean` and are reused verbatim.

**One vocabulary only.**  `Stacks.Perfect.CechDerivedSupportBaseChange` and
`Stacks.Perfect.CechDerivedSupportImmersion` export the same names for the `W.ι` and the general
form of each comparison; this file opens only the second, so that no identifier can resolve to
the specialised one.

**The two spellings of the category of modules on `X'`.**  As in `GysinClassBaseChange.lean`,
every chase is a helper stated at a **variable** category and applied with `exact`, so that the
unifier rather than `rw` crosses between `SheafOfModules (structureSheafRing X')` and
`X'.Modules`, and instances are transported across isomorphisms rather than searched for again.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedOpenImmersion
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.SupportedFraction
open Stacks.Perfect.CechDerivedSupport
open Stacks.Perfect.CechDerivedSupportBaseChange (preservesZeroMorphisms_of_natIso)
open Stacks.Perfect.CechDerivedSupportImmersion
open Stacks.Perfect.ExtendedAlternatingCech (cplx)
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)
open StacksDraft.DerivedCategoryHomology

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

section Degree

attribute [local instance] preservesFiniteLimits_modulePullback_of_isOpenImmersion

variable {X X' : Scheme.{u}} (g : X' ⟶ X) [IsOpenImmersion g] {m : ℕ} (e : Fin m → Γ(X, ⊤))
  (F : X.Modules) [F.IsQuasicoherent] {T : Set X} (hT : IsClosed T)
  (hTe : equationsClosedSet e ⊆ T) (hT' : IsClosed (restrictClosedSubset g T))
  (hTe' : equationsClosedSet (fun j => g.appTop (e j)) ⊆ restrictClosedSubset g T)

/-- `Stacks.Perfect.CechDerivedSupportImmersion.restrictQIso`, factor by factor. -/
theorem immersionRestrictQIso_hom_eq (C : CochainComplex X.Modules ℤ) :
    letI := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso g)
    (restrictQIso g C).hom =
      (derivedPullbackOpenImmersionIso (legIncl g)).hom.app (DerivedCategory.Q.obj C) ≫
        (modulePullback (legIncl g)).mapDerivedCategoryFactors.hom.app C ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (modulePullbackRestrictIso g)
              (ComplexShape.up ℤ)).hom.app C) := rfl

omit [F.IsQuasicoherent] in
/-- **`Stacks.Perfect.CechDerivedSupportImmersion.singleRestrictIso` is the
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` comparison.** -/
theorem immersionSingleRestrictIso_hom_eq :
    (singleRestrictIso g F).hom =
      (derivedPullbackOpenImmersionIso (legIncl g)).hom.app
          ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
        ((modulePullback (legIncl g)).mapDerivedCategorySingleFunctor 0).hom.app F ≫
          (DerivedCategory.singleFunctor X'.Modules 0).map
            ((modulePullbackRestrictIso g).hom.app F) := by
  let := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso g)
  refine Eq.trans (congrArg (fun z => z ≫ DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.restrictFunctor g)
        (ComplexShape.up ℤ) 0).hom.app F))
    (immersionRestrictQIso_hom_eq g
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F)))
    ?_
  refine chase5 _ _ ((modulePullback (legIncl g)).mapDerivedCategoryFactors.inv.app
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F)) _ _
    (DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (modulePullback (legIncl g))
        (ComplexShape.up ℤ) 0).hom.app F)) _ _
    ((modulePullback (legIncl g)).mapDerivedCategoryFactors.hom_inv_id_app _)
    (Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app
      (modulePullback (legIncl g)) F)
    ?_
  refine Eq.trans (DerivedCategory.Q.map_comp _ _).symm ?_
  refine Eq.trans (congrArg DerivedCategory.Q.map
    (singleMapHomologicalComplex_natIso (modulePullbackRestrictIso g)
      (ComplexShape.up ℤ) 0 F)) ?_
  exact DerivedCategory.Q.map_comp _ _

omit [F.IsQuasicoherent] in
/-- `Stacks.Gysin.supportCohomologyOpenImmersionIso` is
`Stacks.Gysin.supportCohomologyPullbackIso` conjugated by the identification of the pullback
along the ringed-space leg with the restriction along `g`; the two are the same expression. -/
theorem supportCohomologyOpenImmersionIso_hom_eq (n : ℤ) :
    (supportCohomologyOpenImmersionIso g hT hT' n F).hom =
      (modulePullbackRestrictIso g).inv.app ((supportCohomologySheafFunctor hT n).obj F) ≫
        (supportCohomologyPullbackIso (legIncl g) T hT n F).hom ≫
          (supportCohomologySheafFunctor hT' n).map ((modulePullbackRestrictIso g).hom.app F) :=
  rfl

omit [F.IsQuasicoherent] in
/-- `Stacks.Gysin.supportCohomologyPullbackIso` at the ringed-space leg of `g`, factor by
factor. -/
theorem immersionSupportCohomologyPullbackIso_hom_eq (n : ℤ) :
    (supportCohomologyPullbackIso (legIncl g) T hT n F).hom =
      ((mapDerivedCategoryHomologyIso (modulePullback (legIncl g)) n).app
          ((supportPush hT).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F))).inv ≫
        (DerivedCategory.homologyFunctor X'.Modules n).map
          ((derivedPullbackOpenImmersionIso (legIncl g)).inv.app
              ((supportPush hT).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≫
            (Stacks.Perfect.SupportPushExcision.supportPushPullbackIso
                (legIncl g) hT).hom.app
                ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
              (supportPush hT').map
                ((derivedPullbackOpenImmersionIso (legIncl g)).hom.app
                    ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
                  ((modulePullback (legIncl g)).mapDerivedCategorySingleFunctor 0).hom.app F)) :=
  rfl

/-- **The restriction along `g` of the cohomology of the extended alternating Čech complex is
the cohomology of the extended alternating Čech complex of the restricted equations.** -/
def cechExtendHomologyImmersionIso (p : ℤ) :
    (Scheme.Modules.restrictFunctor g).obj
        (((cplx e F).extend ComplexShape.embeddingUpNat).homology p) ≅
      ((cplx (fun j => g.appTop (e j)) ((Scheme.Modules.restrictFunctor g).obj F)).extend
        ComplexShape.embeddingUpNat).homology p :=
  ((mapHomologicalComplexHomologyIso (Scheme.Modules.restrictFunctor g)
      (ComplexShape.up ℤ) p).app ((cplx e F).extend ComplexShape.embeddingUpNat)).symm ≪≫
    (HomologicalComplex.homologyFunctor X'.Modules (ComplexShape.up ℤ) p).mapIso
      (restrictExtendIso g e F)

omit [F.IsQuasicoherent] in
/-- `mapHomologicalComplexHomologyIso_natIso` at the identification of the pullback of modules
along the ringed-space leg of `g` with the restriction along `g`. -/
theorem mapHomologicalComplexHomologyIso_natIso_immersion (p : ℤ) :
    letI := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso g)
    HomologicalComplex.homologyMap
          ((NatIso.mapHomologicalComplex (modulePullbackRestrictIso g)
            (ComplexShape.up ℤ)).hom.app
              ((cplx e F).extend ComplexShape.embeddingUpNat)) p ≫
        (mapHomologicalComplexHomologyIso (Scheme.Modules.restrictFunctor g)
            (ComplexShape.up ℤ) p).hom.app
          ((cplx e F).extend ComplexShape.embeddingUpNat) =
      (mapHomologicalComplexHomologyIso (modulePullback (legIncl g))
            (ComplexShape.up ℤ) p).hom.app
          ((cplx e F).extend ComplexShape.embeddingUpNat) ≫
        (modulePullbackRestrictIso g).hom.app
          (((cplx e F).extend ComplexShape.embeddingUpNat).homology p) :=
  mapHomologicalComplexHomologyIso_natIso (modulePullbackRestrictIso g) (ComplexShape.up ℤ) p _

omit [F.IsQuasicoherent] in
/-- `cechExtendHomologyImmersionIso`, factor by factor. -/
theorem cechExtendHomologyImmersionIso_hom (p : ℤ) :
    (cechExtendHomologyImmersionIso g e F p).hom =
      (mapHomologicalComplexHomologyIso (Scheme.Modules.restrictFunctor g)
            (ComplexShape.up ℤ) p).inv.app
          ((cplx e F).extend ComplexShape.embeddingUpNat) ≫
        HomologicalComplex.homologyMap (restrictExtendIso g e F).hom p := rfl

omit [F.IsQuasicoherent] in
/-- The degree-`p` cohomology of the degreewise comparison of the two Čech complexes, solved for:
it is the comparison of the pullback with cohomology, the identification of the pullback with the
restriction, and the inverse of the comparison of the restriction with cohomology. -/
theorem homologyMap_mapHomologicalComplex_immersion_eq (p : ℤ) :
    letI := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso g)
    HomologicalComplex.homologyMap
        ((NatIso.mapHomologicalComplex (modulePullbackRestrictIso g)
          (ComplexShape.up ℤ)).hom.app
            ((cplx e F).extend ComplexShape.embeddingUpNat)) p =
      (mapHomologicalComplexHomologyIso (modulePullback (legIncl g))
            (ComplexShape.up ℤ) p).hom.app
          ((cplx e F).extend ComplexShape.embeddingUpNat) ≫
        (modulePullbackRestrictIso g).hom.app
            (((cplx e F).extend ComplexShape.embeddingUpNat).homology p) ≫
          (mapHomologicalComplexHomologyIso (Scheme.Modules.restrictFunctor g)
              (ComplexShape.up ℤ) p).inv.app
            ((cplx e F).extend ComplexShape.embeddingUpNat) := by
  let := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso g)
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine (Iso.eq_comp_inv ((mapHomologicalComplexHomologyIso
    (Scheme.Modules.restrictFunctor g) (ComplexShape.up ℤ) p).app
      ((cplx e F).extend ComplexShape.embeddingUpNat))).mpr ?_
  exact mapHomologicalComplexHomologyIso_natIso_immersion g e F p

omit [F.IsQuasicoherent] in
/-- **The restricted cohomology comparison, factored through the pullback spelling.** -/
theorem cechExtendHomologyImmersionIso_hom_eq (p : ℤ) :
    letI := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso g)
    (modulePullbackRestrictIso g).inv.app
          (((cplx e F).extend ComplexShape.embeddingUpNat).homology p) ≫
        (mapHomologicalComplexHomologyIso (modulePullback (legIncl g))
              (ComplexShape.up ℤ) p).inv.app
            ((cplx e F).extend ComplexShape.embeddingUpNat) ≫
          HomologicalComplex.homologyMap
              ((NatIso.mapHomologicalComplex (modulePullbackRestrictIso g)
                (ComplexShape.up ℤ)).hom.app
                  ((cplx e F).extend ComplexShape.embeddingUpNat)) p ≫
            HomologicalComplex.homologyMap (restrictExtendIso g e F).hom p =
      (cechExtendHomologyImmersionIso g e F p).hom := by
  let := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso g)
  refine Eq.trans (chaseCancel _ ((modulePullbackRestrictIso g).hom.app _) _
    ((mapHomologicalComplexHomologyIso (modulePullback (legIncl g))
      (ComplexShape.up ℤ) p).hom.app _) _ _ _
    ((modulePullbackRestrictIso g).inv_hom_id_app _)
    ((mapHomologicalComplexHomologyIso (modulePullback (legIncl g))
      (ComplexShape.up ℤ) p).inv_hom_id_app _)
    (homologyMap_mapHomologicalComplex_immersion_eq g e F p))
    (cechExtendHomologyImmersionIso_hom g e F p).symm

/-! ### The derived-category core -/

omit [F.IsQuasicoherent] in
/-- The derived pullback of the comparison of [Stacks, Tag 0G7L], read at the degreewise
pullback: the square of `Stacks.Perfect.CechDerivedSupportImmersion`, with the comparison of the
derived pullback with the degreewise one inserted on both sides. -/
theorem mapDerivedCategory_cechToDerivedSupport_comp_immersion :
    (modulePullback (legIncl g)).mapDerivedCategory.map (cechToDerivedSupport e F hT hTe) ≫
        ((derivedPullbackOpenImmersionIso (legIncl g)).inv.app
              ((supportPush hT).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≫
            (Stacks.Perfect.SupportPushExcision.supportPushPullbackIso (legIncl g) hT).hom.app
                ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
              (supportPush hT').map
                ((derivedPullbackOpenImmersionIso (legIncl g)).hom.app
                    ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
                  ((modulePullback (legIncl g)).mapDerivedCategorySingleFunctor 0).hom.app F)) ≫
          (supportPush hT').map
            ((DerivedCategory.singleFunctor X'.Modules 0).map
              ((modulePullbackRestrictIso g).hom.app F)) =
      (derivedPullbackOpenImmersionIso (legIncl g)).inv.app
          (DerivedCategory.Q.obj ((cplx e F).extend ComplexShape.embeddingUpNat)) ≫
        (cechRestrictIso g e F).hom ≫
          cechToDerivedSupport (fun j => g.appTop (e j))
            ((Scheme.Modules.restrictFunctor g).obj F) hT' hTe' :=
  assembleSq (supportPush hT') _ _ _ _ _ _ _ (singleRestrictIso g F).hom _ _
    ((derivedPullbackOpenImmersionIso (legIncl g)).inv.naturality
      (cechToDerivedSupport e F hT hTe))
    ((immersionSingleRestrictIso_hom_eq g F).trans (Category.assoc _ _ _).symm)
    (map_cechToDerivedSupport_comp_supportPushPullbackIso_hom g e F hT hTe hT' hTe')

omit [F.IsQuasicoherent] in
/-- The two comparisons of the derived pullback with the degreewise pullback cancel: what is
left of `cechRestrictIso` is the degreewise comparison of the two Čech complexes. -/
theorem factors_inv_comp_cechRestrictIso_immersion :
    letI := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso g)
    (modulePullback (legIncl g)).mapDerivedCategoryFactors.inv.app
          ((cplx e F).extend ComplexShape.embeddingUpNat) ≫
        (derivedPullbackOpenImmersionIso (legIncl g)).inv.app
            (DerivedCategory.Q.obj ((cplx e F).extend ComplexShape.embeddingUpNat)) ≫
          (cechRestrictIso g e F).hom =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (modulePullbackRestrictIso g)
            (ComplexShape.up ℤ)).hom.app
          ((cplx e F).extend ComplexShape.embeddingUpNat)) ≫
        DerivedCategory.Q.map (restrictExtendIso g e F).hom := by
  let := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso g)
  refine Eq.trans (congrArg (fun z =>
      (modulePullback (legIncl g)).mapDerivedCategoryFactors.inv.app _ ≫
        (derivedPullbackOpenImmersionIso (legIncl g)).inv.app _ ≫ z)
    (cechRestrictIso_hom g e F)) ?_
  exact chaseCancel _
    ((modulePullback (legIncl g)).mapDerivedCategoryFactors.hom.app _) _
    ((derivedPullbackOpenImmersionIso (legIncl g)).hom.app _) _ _ _
    ((modulePullback (legIncl g)).mapDerivedCategoryFactors.inv_hom_id_app _)
    ((derivedPullbackOpenImmersionIso (legIncl g)).inv_hom_id_app _)
    (immersionRestrictQIso_hom_eq g _)

omit [F.IsQuasicoherent] in
/-- **The derived-category identity behind the degree-`p` reading.** -/
theorem factors_inv_comp_mapDerivedCategory_cechToDerivedSupport_immersion :
    letI := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso g)
    (modulePullback (legIncl g)).mapDerivedCategoryFactors.inv.app
          ((cplx e F).extend ComplexShape.embeddingUpNat) ≫
        (modulePullback (legIncl g)).mapDerivedCategory.map
            (cechToDerivedSupport e F hT hTe) ≫
          ((derivedPullbackOpenImmersionIso (legIncl g)).inv.app
                ((supportPush hT).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≫
              (Stacks.Perfect.SupportPushExcision.supportPushPullbackIso
                  (legIncl g) hT).hom.app
                  ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
                (supportPush hT').map
                  ((derivedPullbackOpenImmersionIso (legIncl g)).hom.app
                      ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
                    ((modulePullback (legIncl g)).mapDerivedCategorySingleFunctor 0).hom.app
                      F)) ≫
            (supportPush hT').map
              ((DerivedCategory.singleFunctor X'.Modules 0).map
                ((modulePullbackRestrictIso g).hom.app F)) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (modulePullbackRestrictIso g)
            (ComplexShape.up ℤ)).hom.app
          ((cplx e F).extend ComplexShape.embeddingUpNat)) ≫
        DerivedCategory.Q.map (restrictExtendIso g e F).hom ≫
          cechToDerivedSupport (fun j => g.appTop (e j))
            ((Scheme.Modules.restrictFunctor g).obj F) hT' hTe' := by
  let := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso g)
  refine Eq.trans (congrArg (fun z =>
      (modulePullback (legIncl g)).mapDerivedCategoryFactors.inv.app _ ≫ z)
    (mapDerivedCategory_cechToDerivedSupport_comp_immersion g e F hT hTe hT' hTe')) ?_
  exact postcomp _ _ _ _ _ _ (factors_inv_comp_cechRestrictIso_immersion g e F)

/-! ### The degree-`p` reading -/

omit [F.IsQuasicoherent] in
/-- **The degree-`p` reading of the square of [Stacks, Tag 0G7U] along an arbitrary open
immersion.**  The restriction along `g` of the degree-`p` cohomology of the comparison of
[Stacks, Tag 0G7L], followed by the excision
`Stacks.Gysin.supportCohomologyOpenImmersionIso` of [Stacks, Tag 0G78] on degree-`p` cohomology
sheaves, is the same comparison for the restricted equations and `g^*ℱ`, read across
`cechExtendHomologyImmersionIso`. -/
theorem map_extendHomologyToSupport_comp_supportCohomologyOpenImmersionIso (p : ℕ) :
    (Scheme.Modules.restrictFunctor g).map (extendHomologyToSupport e F hT hTe p) ≫
        (supportCohomologyOpenImmersionIso g hT hT' (p : ℤ) F).hom =
      (cechExtendHomologyImmersionIso g e F (p : ℤ)).hom ≫
        extendHomologyToSupport (fun j => g.appTop (e j))
          ((Scheme.Modules.restrictFunctor g).obj F) hT' hTe' p := by
  let := preservesZeroMorphisms_of_natIso (modulePullbackRestrictIso g)
  exact assembleDeg (Scheme.Modules.restrictFunctor g) (modulePullback (legIncl g))
    (DerivedCategory.homologyFunctor X'.Modules (p : ℤ)) _ _ _ _ _
    ((modulePullbackRestrictIso g).inv.app _) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((cechExtendHomologyImmersionIso g e F (p : ℤ)).hom)
    ((modulePullbackRestrictIso g).inv.naturality _)
    ((modulePullbackRestrictIso g).inv.naturality _)
    ((mapDerivedCategoryHomologyIso (modulePullback (legIncl g)) (p : ℤ)).inv.naturality
      (cechToDerivedSupport e F hT hTe))
    (mapDerivedCategoryHomologyIso_inv_app_Q (modulePullback (legIncl g))
      ((cplx e F).extend ComplexShape.embeddingUpNat)
      (p : ℤ))
    (factors_inv_comp_mapDerivedCategory_cechToDerivedSupport_immersion
      g e F hT hTe hT' hTe')
    (homologyFunctorFactors_inv_naturality
      ((NatIso.mapHomologicalComplex (modulePullbackRestrictIso g)
        (ComplexShape.up ℤ)).hom.app
          ((cplx e F).extend ComplexShape.embeddingUpNat)) (p : ℤ))
    (homologyFunctorFactors_inv_naturality (restrictExtendIso g e F).hom (p : ℤ))
    (cechExtendHomologyImmersionIso_hom_eq g e F (p : ℤ))

/-! ### The same, on the cohomology of the `ℕ`-graded Čech complex -/

/-- **The restriction along `g` of the degree-`p` cohomology of the extended alternating Čech
complex of [Stacks, Tag 0G7I] is the degree-`p` cohomology of that complex for the restricted
equations**, read on the `ℕ`-graded complexes.  This is `cechExtendHomologyImmersionIso`
conjugated by the two identifications of the cohomology of a complex with the cohomology of its
extension to the grading `ℤ`. -/
def cechHomologyImmersionIso (p : ℕ) :
    (Scheme.Modules.restrictFunctor g).obj ((cplx e F).homology p) ≅
      (cplx (fun j => g.appTop (e j))
        ((Scheme.Modules.restrictFunctor g).obj F)).homology p :=
  (Scheme.Modules.restrictFunctor g).mapIso
      (HomologicalComplex.extendHomologyIso (cplx e F) ComplexShape.embeddingUpNat
        (embeddingUpNat_f p)).symm ≪≫
    cechExtendHomologyImmersionIso g e F (p : ℤ) ≪≫
      HomologicalComplex.extendHomologyIso
        (cplx (fun j => g.appTop (e j)) ((Scheme.Modules.restrictFunctor g).obj F))
        ComplexShape.embeddingUpNat (embeddingUpNat_f p)

omit [F.IsQuasicoherent] in
/-- **The degree-`p` reading of the square of [Stacks, Tag 0G7U] along an arbitrary open
immersion, on the cohomology of the `ℕ`-graded Čech complex.**  The restriction along `g` of
`Stacks.Perfect.SupportedFraction.cechHomologyToSupport`, followed by the excision of
[Stacks, Tag 0G78] on degree-`p` cohomology sheaves, is that map for the restricted equations and
`g^*ℱ`, read across `cechHomologyImmersionIso`.

This is the shape `Stacks.Perfect.SupportedFraction.supportedFractionSource_eq` consumes: the
class map of [Stacks, Tag 0G7Q] read on the coefficient module is the degree-`c` cohomology class
of the fraction `s / (f₁ ⋯ f_c)` followed by this map. -/
theorem map_cechHomologyToSupport_comp_supportCohomologyOpenImmersionIso (p : ℕ) :
    (Scheme.Modules.restrictFunctor g).map (cechHomologyToSupport e F hT hTe p) ≫
        (supportCohomologyOpenImmersionIso g hT hT' (p : ℤ) F).hom =
      (cechHomologyImmersionIso g e F p).hom ≫
        cechHomologyToSupport (fun j => g.appTop (e j))
          ((Scheme.Modules.restrictFunctor g).obj F) hT' hTe' p := by
  refine Eq.trans (congrArg
    (fun z => z ≫ (supportCohomologyOpenImmersionIso g hT hT' (p : ℤ) F).hom)
    ((Scheme.Modules.restrictFunctor g).map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z =>
      (Scheme.Modules.restrictFunctor g).map
        (HomologicalComplex.extendHomologyIso (cplx e F) ComplexShape.embeddingUpNat
          (embeddingUpNat_f p)).inv ≫ z)
    (map_extendHomologyToSupport_comp_supportCohomologyOpenImmersionIso
      g e F hT hTe hT' hTe' p)) ?_
  exact (chaseInsert _ _ _ _ _
    ((HomologicalComplex.extendHomologyIso
        (cplx (fun j => g.appTop (e j)) ((Scheme.Modules.restrictFunctor g).obj F))
        ComplexShape.embeddingUpNat (embeddingUpNat_f p)).hom_inv_id)).symm

end Degree

end Stacks.Gysin

end
