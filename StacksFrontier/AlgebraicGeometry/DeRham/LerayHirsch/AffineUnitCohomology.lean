module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineBase
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedGlobalCupProduct.UnitEvaluation
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.AffineProjectionFormulaDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The cohomology of the shifted structure sheaf of an affine scheme

For a ringed space `X` at which global sections compute derived global sections of `𝒪_X[-m]`,
`H^m(X, 𝒪_X[-m])` is free of rank one over `Γ(X, 𝒪_X)` on the class of `1` and
`H^q(X, 𝒪_X[-m]) = 0` for `q ≠ m`. For an affine scheme the hypothesis holds
([Stacks, Tag 0G9P]).

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.bijective_smul_unitCycleClass`:
  `H^m(X, 𝒪_X[-m])` is free of rank one over `Γ(X, 𝒪_X)` on the class of `1`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.isZero_cohomologyModule_unitComplex`:
  `H^q(X, 𝒪_X[-m]) = 0` for `q ≠ m`.
* `AlgebraicGeometry.AffineUnitCohomology.isIso_sectionsUnitQ_unitComplex`: on an affine scheme,
  global sections compute derived global sections of `𝒪_X[-m]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- The complex of global sections of `𝒪_X[-m]` has zero differentials. -/
theorem sectionsComplex_unitComplex_d (m i j : ℤ) :
    (sectionsComplex X (unitComplex X m)).d i j = 0 := by
  simp [sectionsComplex, unitComplex]

/-- Multiples of the section `1` in degree `m` of `Γ(X, 𝒪_X[-m])` are all its sections. -/
theorem bijective_smul_unitSection (m : ℤ) :
    Function.Bijective (fun a : baseRing X => a • unitSection X m) := by
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m
    (_root_.SheafOfModules.unit (structureSheafRing X))
  let E := ((_root_.SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).mapIso e).symm
  have h : (fun a : baseRing X => a • unitSection X m) =
      fun a : baseRing X => (e.inv.val.app (op ⊤)).hom a := by
    funext a
    let a' : (structureSheafRing X).obj.obj (op ⊤) := a
    change a' • (e.inv.val.app (op ⊤)).hom (1 : (structureSheafRing X).obj.obj (op ⊤)) =
      (e.inv.val.app (op ⊤)).hom a'
    exact ((e.inv.val.app (op ⊤)).hom.map_smul a'
      (1 : (structureSheafRing X).obj.obj (op ⊤))).symm.trans
        (congrArg (e.inv.val.app (op ⊤)).hom (mul_one a'))
  rw [h]
  exact ConcreteCategory.bijective_of_isIso E.hom

/-- Multiples of the cocycle `1` are all the cocycles of `Γ(X, 𝒪_X[-m])` in degree `m`. -/
theorem bijective_smul_unitCycle (m : ℤ) :
    Function.Bijective (fun a : baseRing X => a • unitCycle X m) := by
  let K := sectionsComplex X (unitComplex X m)
  have := K.isIso_iCycles m (m + 1) (CochainComplex.next ℤ m)
    (sectionsComplex_unitComplex_d X m m (m + 1))
  have hi : Function.Bijective (K.iCycles m).hom := ConcreteCategory.bijective_of_isIso _
  refine (Function.Bijective.of_comp_iff' hi _).1 ?_
  convert bijective_smul_unitSection X m using 1
  funext a
  change (K.iCycles m).hom (a • unitCycle X m) = a • unitSection X m
  rw [map_smul, iCycles_unitCycle]

/-- The map from the cohomology of global sections to that of derived global sections is
invertible when the unit `Γ ⟶ RΓ` is. -/
theorem isIso_globalClass_comp (N : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (n : ℤ) (h : IsIso (sectionsUnitQ X ⊤ N)) :
    IsIso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (baseRing X)) n).inv.app
      (sectionsComplex X N) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) n).map (sectionsUnitQ X ⊤ N)) :=
  @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (Functor.map_isIso _ _)

/-- **`H^m(X, 𝒪_X[-m]) = Γ(X, 𝒪_X)`**, when global sections compute derived global sections at
`𝒪_X[-m]`: every class is a unique multiple of the class of `1`. -/
theorem bijective_smul_unitCycleClass (m : ℤ) (h : IsIso (sectionsUnitQ X ⊤ (unitComplex X m))) :
    Function.Bijective (fun a : baseRing X => a • unitCycleClass X m) := by
  let K := sectionsComplex X (unitComplex X m)
  have := K.isIso_homologyπ (m - 1) m (CochainComplex.prev ℤ m)
    (sectionsComplex_unitComplex_d X m (m - 1) m)
  have h' := isIso_globalClass_comp X (unitComplex X m) m h
  let ψ := K.homologyπ m ≫ (DerivedCategory.homologyFunctorFactors
    (ModuleCat.{u} (baseRing X)) m).inv.app K ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) m).map
        (sectionsUnitQ X ⊤ (unitComplex X m))
  have : IsIso ψ := by exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance h'
  convert (ConcreteCategory.bijective_of_isIso ψ).comp (bijective_smul_unitCycle X m) using 1
  funext a
  exact (ψ.hom.map_smul a (unitCycle X m)).symm

/-- **`H^q(X, 𝒪_X[-m]) = 0` for `q ≠ m`**, when global sections compute derived global sections
at `𝒪_X[-m]`. -/
theorem isZero_cohomologyModule_unitComplex (m q : ℤ) (hq : q ≠ m)
    (h : IsIso (sectionsUnitQ X ⊤ (unitComplex X m))) :
    IsZero (cohomologyModule (DerivedCategory.Q.obj (unitComplex X m)) q) := by
  have := isIso_globalClass_comp X (unitComplex X m) q h
  refine IsZero.of_iso ?_ (asIso ((DerivedCategory.homologyFunctorFactors
    (ModuleCat.{u} (baseRing X)) q).inv.app (sectionsComplex X (unitComplex X m)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) q).map
        (sectionsUnitQ X ⊤ (unitComplex X m)))).symm
  exact ShortComplex.isZero_homology_of_isZero_X₂ _ ((globalSections X).map_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) m _ q hq))

end Stacks.Cohomology.DerivedGlobalCupProduct

namespace AlgebraicGeometry.AffineUnitCohomology

variable (Y : Scheme.{u})

/-- The terms of `𝒪_Y[-m]` are quasi-coherent. -/
theorem isQuasicoherent_unitComplex_X (m n : ℤ) :
    ((unitComplex Y.toRingedSpace m).X n).IsQuasicoherent := by
  by_cases h : n = m
  · subst h
    exact (_root_.SheafOfModules.isQuasicoherent (structureSheafRing Y.toRingedSpace)).prop_of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n
        (_root_.SheafOfModules.unit (structureSheafRing Y.toRingedSpace))).symm
      Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit
  · exact Stacks.Cohomology.AffineProjectionFormulaComplexes.isQuasicoherent_of_isZero
      Y.toRingedSpace
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) m _ n h)

/-- **Global sections compute derived global sections of `𝒪_Y[-m]` on an affine scheme**
([Stacks, Tag 0G9P]). -/
theorem isIso_derivedSectionsOverOpenUnit_unitComplex [IsAffine Y] (m : ℤ) :
    IsIso ((derivedSectionsOverOpenUnit Y.toRingedSpace ⊤).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (unitComplex Y.toRingedSpace m))) :=
  @isIso_to_derivedGlobalSections_of_termwise_acyclic Y _ _ (unitComplex Y.toRingedSpace m)
    (isQuasicoherent_unitComplex_X Y m)
    (fun n => @Stacks.Cohomology.AffineBase.rightAcyclic_sectionsFunctor_of_isQuasicoherent Y _ _
      (isQuasicoherent_unitComplex_X Y m n))
    (derivedSectionsOverOpen Y.toRingedSpace ⊤) (derivedSectionsOverOpenUnit Y.toRingedSpace ⊤)
    (inferInstanceAs ((derivedSectionsOverOpen Y.toRingedSpace ⊤).IsRightDerivedFunctor
      (derivedSectionsOverOpenUnit Y.toRingedSpace ⊤)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
        (ComplexShape.up ℤ))))

/-- The unit `Γ(Y, 𝒪_Y[-m]) ⟶ RΓ(Y, 𝒪_Y[-m])` is an isomorphism on an affine scheme. -/
theorem isIso_sectionsUnitQ_unitComplex [IsAffine Y] (m : ℤ) :
    IsIso (sectionsUnitQ Y.toRingedSpace ⊤ (unitComplex Y.toRingedSpace m)) := by
  have h2 : IsIso ((derivedSectionsOverOpen Y.toRingedSpace ⊤).map
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))).hom.app
          (unitComplex Y.toRingedSpace m))) := Functor.map_isIso _ _
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (@IsIso.comp_isIso _ _ _ _ _ _ _
    (isIso_derivedSectionsOverOpenUnit_unitComplex Y m) h2)

end AlgebraicGeometry.AffineUnitCohomology

end
