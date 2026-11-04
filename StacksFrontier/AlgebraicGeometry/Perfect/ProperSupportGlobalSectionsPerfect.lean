module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSections
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLeray
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.Counterexample
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusRestriction

/-!
# Perfectness of `RΓ(X, G)` over the base ring for a properly supported flat module

Let `A` be a ring, let `f : X ⟶ Spec A` be of finite presentation and let `G` be an
`𝒪_X`-module of finite presentation, flat over `A`, whose support is proper over `A`. Then the
derived global sections `RΓ(X, G)`, read as an object of `D(A)`, are a perfect object of `D(A)`.

## Main definitions

* `derivedGlobalSectionsOverBaseIso`: the object `derivedGlobalSectionsOverBase f F` (bounded
  below derived global sections over `Γ(X, 𝒪_X)`, with scalars restricted to `A`) is `RΓ(X, F[0])`
  for the unbounded `A`-linear derived global sections
  `AlgebraicGeometry.derivedGlobalSectionsOver f`.

## Main results

* `isPerfect_derivedGlobalSectionsOverBase_of_isPerfect`: for `f` quasi-compact and
  quasi-separated and `F` quasi-coherent, if `Rf_*(F[0])` is a perfect object of
  `D(𝒪_{Spec A})`, then `RΓ(X, F)` is a perfect object of `D(A)`.
* `isPerfect_derivedGlobalSectionsOverBase_of_properSupport`: `RΓ(X, G)` is perfect in `D(A)` for
  `f` of finite presentation and `G` of finite presentation, flat over `A`, with support proper
  over `A`.

## References

* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportGlobalSectionsPerfect

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.AlgebraicGeometry.ProperFlatGlobalSections.preservesFiniteLimits_baseRestriction
  Stacks.AlgebraicGeometry.ProperFlatGlobalSections.preservesFiniteColimits_baseRestriction
  Stacks.AlgebraicGeometry.ProperFlatGlobalSections.preservesHomology_baseRestriction

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- Unbounded derived sections over the top open, with scalars restricted to the base ring, are
the `A`-linear unbounded derived global sections: both are right derived functors of the same
functor, sections over `⊤` read over `A`. -/
def derivedSectionsTopRestrictIso :
    derivedSectionsOverOpen X.toRingedSpace ⊤ ⋙
        (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapDerivedCategory ≅
      (homotopyBaseSections f).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ)) := by
  haveI := Stacks.Cohomology.SiteCohomologyPresheaf.isRightDerivedFunctor_totalRightDerived_comp
    (homotopySectionsOverOpen X.toRingedSpace ⊤)
    (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapDerivedCategory
  exact Functor.rightDerivedNatIso _ _
    (Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedCompUnit
      (homotopySectionsOverOpen X.toRingedSpace ⊤)
      (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapDerivedCategory)
    ((homotopyBaseSections f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ))
    (homotopyCompBaseIso (sectionsOverOpen X.toRingedSpace ⊤)
      (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom)
      (baseSections f) (Iso.refl _))

/-- `derivedGlobalSectionsOverBase f F` is the unbounded `A`-linear `RΓ(X, -)` at `F[0]`. -/
def derivedGlobalSectionsOverBaseIso (F : X.Modules) :
    derivedGlobalSectionsOverBase f F ≅
      (derivedGlobalSectionsOver f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F) :=
  (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapDerivedCategory.mapIso
      ((Functor.boundedDerivedIso (sectionsOverOpen X.toRingedSpace ⊤)
          (derivedSectionsOverOpen X.toRingedSpace ⊤)
          (derivedSectionsOverOpenUnit X.toRingedSpace ⊤)
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective _)).app
        ((DerivedCategory.Plus.singleFunctor
          (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F) ≪≫
      (derivedSectionsOverOpen X.toRingedSpace ⊤).mapIso
        ((DerivedCategory.Plus.singleFunctorιIso
          (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).app F)) ≪≫
    (derivedSectionsTopRestrictIso f).app _

/-- For a quasi-compact quasi-separated `f : X ⟶ Spec A` and `W ∈ D(𝒪_X)` with quasi-coherent
cohomology, if `Rf_* W` is a perfect object of `D(𝒪_{Spec A})` then `RΓ(X, W)` is a perfect object
of `D(A)`. -/
theorem isPerfect_derivedGlobalSectionsOver_of_isPerfect_derivedPushforward
    [QuasiCompact f] [QuasiSeparated f] (W : DerivedCategory X.Modules)
    (hW : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj W).IsQuasicoherent)
    (hP : RingedSpace.IsPerfect (X := (Spec (CommRingCat.of A)).toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj W)) :
    StacksDraft.Perfect.IsPerfect ((derivedGlobalSectionsOver f).obj W) := by
  let T := (derivedPushforward f.toLRSHom.toShHom).obj W
  have hT : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules n).obj
      T).IsQuasicoherent :=
    isQuasicoherent_derivedPushforward f ⟨W, hW⟩
  obtain ⟨M0, ⟨e0⟩⟩ := StandardModel.exists_iso_mapDerivedCategory (CommRingCat.of A) T hT
  have hu := StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_unit (CommRingCat.of A)
  have eM : M0 ≅ (derivedGlobalSectionsOver f).obj W :=
    asIso ((derivedTildeGlobalSectionsAdjunction (CommRingCat.of A)).val.unit.app M0) ≪≫
      (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).mapIso
        ((derivedTildeCompι (CommRingCat.of A)).app M0 ≪≫ e0) ≪≫
      ((derivedGlobalSectionsOverPushforwardIso f).app W).symm
  have hpt : Stacks.Cohomology.PerfectComplexes.IsPerfect
      ((tilde.functor (CommRingCat.of A)).mapDerivedCategory.obj M0) :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (X := (Spec (CommRingCat.of A)).toRingedSpace) e0.symm hP
  exact StacksDraft.Perfect.isPerfect_of_iso eM.symm ((isPerfect_tilde_iff M0).1 hpt)

/-- `RΓ(X, F)` is perfect in `D(A)` as soon as `Rf_*(F[0])` is perfect in `D(𝒪_{Spec A})`, for
`f` quasi-compact and quasi-separated and `F` quasi-coherent. -/
theorem isPerfect_derivedGlobalSectionsOverBase_of_isPerfect
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent]
    (hP : RingedSpace.IsPerfect (X := (Spec (CommRingCat.of A)).toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F))) :
    StacksDraft.Perfect.IsPerfect (derivedGlobalSectionsOverBase f F) :=
  StacksDraft.Perfect.isPerfect_of_iso (derivedGlobalSectionsOverBaseIso f F)
    (isPerfect_derivedGlobalSectionsOver_of_isPerfect_derivedPushforward f _
      (fun n => Stacks.Thickenings.isQuasicoherent_homology_singleFunctor_obj _ F
        inferInstance n) hP)

/-- For `f : X ⟶ S` of finite presentation and `G` an `𝒪_X`-module of finite presentation, flat
over `S`, whose support lies in a closed subset proper over `S`, the derived direct image
`Rf_*(G[0])` is a perfect object of `D(𝒪_S)`. -/
theorem isPerfect_derivedPushforward_singleFunctor {S : Scheme.{u}} (g : X ⟶ S)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (G : X.Modules) [G.IsFinitePresentation] (hflat : IsFlatOver g.toLRSHom.toShHom G)
    (hsupp : ∃ Z : Closeds X, IsProperOver g Z ∧ SheafOfModules.supp G ⊆ (Z : Set X)) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforward g.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj G)) := by
  have hG : FlatProperSupportFinitelyPresented g (ProperFlatBaseChange.singleDegreeComplex G) :=
    { bounded := ⟨0, 0, inferInstance, inferInstance⟩
      isFinitePresentation :=
        ProperFlatBaseChange.isFinitePresentation_singleDegreeComplex G inferInstance
      isFlatOver := ProperFlatBaseChange.isFlatOver_singleDegreeComplex g G hflat
      properSupport := by
        obtain ⟨Z, hZ, hGZ⟩ := hsupp
        refine ⟨Z, hZ, fun i => ?_⟩
        by_cases hi : i = 0
        · subst hi
          rw [SheafOfModules.supp_eq_of_iso
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) G)]
          exact hGZ
        · rw [SheafOfModules.supp_eq_empty_of_isZero
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G i hi)]
          exact Set.empty_subset _ }
  have h := isPerfect_derivedPushforward_tensor g ⟨‹_›, ‹_›, ‹_›⟩
    (DescentSituation.unitObj X) (DescentSituation.isPerfect_unitObj X) _ hG
  exact isPerfect_of_iso_scheme
    ((derivedPushforward g.toLRSHom.toShHom).mapIso
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).leftUnitIso
          (Stacks.SheafOfModules.ringedSite X.sheaf) _ ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app G).symm)) h

/-- Let `f : X ⟶ Spec A` be of finite presentation and let `G` be an `𝒪_X`-module of finite
presentation, flat over `A`, whose support lies in a closed subset proper over `A`. Then
`RΓ(X, G)`, as an object of `D(A)`, is perfect. -/
theorem isPerfect_derivedGlobalSectionsOverBase_of_properSupport
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (G : X.Modules) [G.IsFinitePresentation] (hflat : IsFlatOver f.toLRSHom.toShHom G)
    (hsupp : ∃ Z : Closeds X, IsProperOver f Z ∧ SheafOfModules.supp G ⊆ (Z : Set X)) :
    StacksDraft.Perfect.IsPerfect (derivedGlobalSectionsOverBase f G) :=
  have : G.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation G
  isPerfect_derivedGlobalSectionsOverBase_of_isPerfect f G
    (isPerfect_derivedPushforward_singleFunctor f G hflat hsupp)

end Stacks.AlgebraicGeometry.ProperSupportGlobalSectionsPerfect

end
