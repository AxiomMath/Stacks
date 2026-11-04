module

public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphism
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Hypercohomology of a complex with no negative cohomology

Let `M` be an object of the unbounded derived category of `O_X`-modules on a ringed space whose
cohomology sheaves vanish in negative degrees. Then its hypercohomology over every open
vanishes in negative degrees, and its degree-zero hypercohomology over an open is the module of
sections there of its degree-zero cohomology sheaf.

## Main results

* `Stacks.Cohomology.Connective.isZero_homology_rightDerived_and_nonempty_zerothIso`,
  `Stacks.Cohomology.Connective.isZero_homology_rightDerived_of_isGE` and
  `Stacks.Cohomology.Connective.nonempty_zerothHomologyRightDerivedIso`: the statement for an
  arbitrary left-exact additive functor out of a Grothendieck abelian category and an arbitrary
  right derived functor of it.
* `Stacks.Cohomology.Connective.isZero_homology_derivedSections_of_isZero_negative` and
  `Stacks.Cohomology.Connective.nonempty_zerothDerivedSectionsIsoSections`: the two
  consequences for derived sections over an open of a ringed space.

## References

* [Stacks Project, Tag 0BKM](https://stacks.math.columbia.edu/tag/0BKM)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.Connective

universe w v₁ u₁ v₂ u₂ dC dD u g

section Abstract

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{dC} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{dD} D]

/-- Let `F` be a left-exact additive functor out of a Grothendieck abelian category with right
derived functor `RF`, and let `M` be an object of the derived category with no cohomology in
negative degrees. Then `RF M` has no cohomology in negative degrees, and its degree-zero
cohomology is isomorphic to `F` applied to the degree-zero cohomology of `M`. -/
theorem isZero_homology_rightDerived_and_nonempty_zerothIso (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] (RF : DerivedCategory C ⥤ DerivedCategory D)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (M : DerivedCategory C)
    (hM : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor C i).obj M)) :
    (∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor D i).obj (RF.obj M))) ∧
      Nonempty ((DerivedCategory.homologyFunctor D 0).obj (RF.obj M) ≅
        F.obj ((DerivedCategory.homologyFunctor C 0).obj M)) := by
  have hGE : M.IsGE 0 := (DerivedCategory.isGE_iff M 0).2 hM
  let Mplus : DerivedCategory.Plus C := ⟨M, ⟨0, hGE⟩⟩
  have _ : Mplus.IsGE 0 := ⟨hGE.ge⟩
  obtain ⟨L, hL, ⟨ePlus⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso Mplus 0
  have _ : L.obj.IsStrictlyGE 0 := hL
  let I : CochainComplex C ℤ := ((InjectiveObject.ι C).mapCochainComplexPlus.obj L).obj
  have hIge : I.IsStrictlyGE 0 :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff
      (K := L.obj) (InjectiveObject.ι C) 0).2 hL
  have hZero : ∀ n : ℤ, n < 0 → IsZero (I.X n) :=
    fun n hn => I.isZero_of_isStrictlyGE 0 n hn
  have hIinj : ∀ n : ℤ, Injective (I.X n) := fun n => (L.obj.X n).property
  have ePlusFull : DerivedCategory.Q.obj I ≅ M := DerivedCategory.Plus.ι.mapIso ePlus
  have hIK : I.IsKInjective :=
    let : ∀ n : ℤ, Injective (I.X n) := hIinj
    CochainComplex.isKInjective_of_injective I 0
  have hα : IsIso (α.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (fun K => ⟨(Stacks.Injectives.kInjectiveResolutionFunctor C).obj K,
        (Stacks.Injectives.kInjectiveResolutionInclusion C).app K, inferInstance,
        inferInstance⟩)).2 DerivedCategory.Qh RF α I hIK
  have eDerived : RF.obj M ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    let := hα
    RF.mapIso ePlusFull |>.symm ≪≫
      RF.mapIso ((DerivedCategory.quotientCompQhIso C).app I).symm ≪≫
      (asIso (α.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I))).symm ≪≫
      DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I) ≪≫
      (DerivedCategory.quotientCompQhIso D).app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  refine ⟨fun i hi => ?_, ⟨?_⟩⟩
  · have hIC : CochainComplex.IsStrictlyGE
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) 0 :=
      (CochainComplex.isStrictlyGE_iff _ 0).2 fun n hn => F.map_isZero (hZero n hn)
    have _ : (DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).IsGE 0 :=
      (DerivedCategory.isGE_Q_obj_iff _ 0).2 inferInstance
    exact (DerivedCategory.isZero_of_isGE _ 0 i (by omega)).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso eDerived)
  · refine ((DerivedCategory.homologyFunctor D 0).mapIso eDerived).trans ?_
    have hX₁ : IsZero (I.sc 0).X₁ := by
      dsimp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor]
      exact hZero _ (by simp)
    have hpres : (I.sc 0).leftHomologyData.IsPreservedBy F :=
      { g := inferInstance
        f' := by rw [hX₁.eq_of_src (I.sc 0).leftHomologyData.f' 0]; infer_instance }
    have _ : F.PreservesLeftHomologyOf (I.sc 0) :=
      let := hpres
      Functor.PreservesLeftHomologyOf.mk' (F := F) (S := I.sc 0) (I.sc 0).leftHomologyData
    refine ((DerivedCategory.homologyFunctorFactors D 0).app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).trans ?_
    exact ((I.sc 0).mapHomologyIso F).trans
      (F.mapIso ((DerivedCategory.homologyFunctorFactors C 0).app I).symm ≪≫
        F.mapIso ((DerivedCategory.homologyFunctor C 0).mapIso ePlusFull))

/-- The negative-degree half of `isZero_homology_rightDerived_and_nonempty_zerothIso`. -/
theorem isZero_homology_rightDerived_of_isGE (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (RF : DerivedCategory C ⥤ DerivedCategory D)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (M : DerivedCategory C)
    (hM : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor C i).obj M))
    (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor D i).obj (RF.obj M)) :=
  (isZero_homology_rightDerived_and_nonempty_zerothIso F RF α M hM).1 i hi

/-- The degree-zero half of `isZero_homology_rightDerived_and_nonempty_zerothIso`. -/
theorem nonempty_zerothHomologyRightDerivedIso (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] (RF : DerivedCategory C ⥤ DerivedCategory D)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (M : DerivedCategory C)
    (hM : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor C i).obj M)) :
    Nonempty ((DerivedCategory.homologyFunctor D 0).obj (RF.obj M) ≅
      F.obj ((DerivedCategory.homologyFunctor C 0).obj M)) :=
  (isZero_homology_rightDerived_and_nonempty_zerothIso F RF α M hM).2

end Abstract

section RingedSpace

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.HypercohomologyEdge

attribute [local instance] Stacks.Cohomology.HypercohomologyEdge.evaluation_additive

variable (X : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{u} (structureSheafRing X))]

/-- **Negative hypercohomology of a complex with no negative cohomology vanishes.** For every
open `U` of a ringed space and every object `M` of `D(O_X)` whose cohomology sheaves vanish in
negative degrees, `H^i(U, M) = 0` for `i < 0`. -/
theorem isZero_homology_derivedSections_of_isZero_negative
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hM : ∀ i : ℤ, i < 0 → IsZero
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) i).obj M))
    (U : Opens X.carrier) (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))) i).obj
        ((derivedSections (structureSheafRing X) U).obj M)) :=
  isZero_homology_rightDerived_of_isGE (SheafOfModules.evaluation (structureSheafRing X) (op U))
    (derivedSections (structureSheafRing X) U)
    ((homotopySections (structureSheafRing X) U).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)))
    M hM i hi

/-- **Degree-zero hypercohomology of a complex with no negative cohomology is the module of
sections of its degree-zero cohomology sheaf.** For every open `U` of a ringed space,
`H^0(U, M) ≅ Γ(U, H^0(M))`. -/
theorem nonempty_zerothDerivedSectionsIsoSections
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hM : ∀ i : ℤ, i < 0 → IsZero
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) i).obj M))
    (U : Opens X.carrier) :
    Nonempty ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))) 0).obj
          ((derivedSections (structureSheafRing X) U).obj M) ≅
      (SheafOfModules.evaluation (structureSheafRing X) (op U)).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj M)) :=
  nonempty_zerothHomologyRightDerivedIso (SheafOfModules.evaluation (structureSheafRing X) (op U))
    (derivedSections (structureSheafRing X) U)
    ((homotopySections (structureSheafRing X) U).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)))
    M hM

end RingedSpace

end Stacks.Cohomology.Connective

end
