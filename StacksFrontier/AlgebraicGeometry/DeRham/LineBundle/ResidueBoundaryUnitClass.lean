module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ResidueBoundaryUnitValue
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.RealizationUnboundedGlobalClass

/-!
# The abelian class of the unit and the unit of de Rham cohomology

Let `D` be a line-bundle situation and `t` a global section of the image of the degree-zero
cycles of the abelian residue sequence whose image in `Ω⁰` is the global section `1`. The class
of `t` in the hypercohomology of the abelian de Rham complex is carried by the realization
comparison of [Stacks, Tag 01F1] to the unit `1 ∈ H⁰_{dR}`.

## Main results

* `Stacks.LineBundle.Situation.realizationIsoAt_imageCycleClass`: the comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.DerivedIndexing

/-- The algebra of `singleCyclesHom_cyclesMap_iCycles`, with every object and morphism a
variable. -/
private theorem cycles_paste {C : Type*} [Category* C] {p z w y q : C} (a : p ⟶ z) (c : z ⟶ w)
    (i : w ⟶ y) (i' : z ⟶ q) (φ : q ⟶ y) (g : p ⟶ q) (r : p ⟶ y) (hc : c ≫ i = i' ≫ φ)
    (ha : a ≫ i' = g) (hr : g ≫ φ = r) : a ≫ c ≫ i = r := by
  rw [hc, reassoc_of% ha, hr]

open Stacks.Cohomology.RightDerivedBoundary in
/-- **The class map on the image of the cycles, before taking classes**: a section of the image
`I` of `Z⁰K₂ ⟶ Z⁰K₃` is carried, as a cocycle of `F(K₃)`, to its image under `I ⟶ Z⁰K₃ ⟶ K₃⁰`. -/
theorem singleCyclesHom_cyclesMap_iCycles {A : Type*} [Category* A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory A] {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (S : ShortComplex (CochainComplex.Plus A)) :
    singleCyclesHom F (HomologicalComplex.shortExactCycles (toSC S) 0).X₃ ≫
        HomologicalComplex.cyclesMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (cyclesImageSingleHom S).hom) 0 ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj S.X₃.obj).iCycles 0 =
      F.map (HomologicalComplex.cyclesImageι (toSC S) 0 ≫ S.X₃.obj.iCycles 0) := by
  have hr : F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (HomologicalComplex.shortExactCycles (toSC S) 0).X₃).inv ≫
      F.map ((cyclesImageSingleHom S).hom.f 0) =
      F.map (HomologicalComplex.cyclesImageι (toSC S) 0 ≫ S.X₃.obj.iCycles 0) := by
    refine (F.map_comp _ _).symm.trans (congrArg F.map ?_)
    exact (congrArg (_ ≫ ·) (cyclesImageSingleHom_f S)).trans (Iso.inv_hom_id_assoc _ _)
  exact cycles_paste _ _ _ _ _ _ _ (HomologicalComplex.cyclesMap_i _ 0)
    (singleCyclesHom_iCycles F _) hr

end Stacks.DerivedIndexing

namespace Stacks.LineBundle

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus

variable (D : Situation.{u})

open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.Cohomology.RealizationShift (realizationIsoAt)

/-- **The class of a lift of `1` is the unit of de Rham cohomology**: a global section `t` of the
image of `Z⁰(ℱ₂) ⟶ Z⁰(Ω^•)` in the abelian residue sequence whose image in `Ω⁰` is the global
section `1` has class `1 ∈ H⁰_{dR}(X/S)`, across the realization comparison of
[Stacks, Tag 01F1]. -/
theorem Situation.realizationIsoAt_imageCycleClass
    (t : (HomologicalComplex.shortExactCycles
      (Stacks.Cohomology.RightDerivedBoundary.toSC D.residueAbelianSequence) 0).X₃.obj.obj (op ⊤))
    (hone : (D.residueAbelianSequence.X₃.obj.iCycles 0).hom.app (op ⊤)
        ((HomologicalComplex.cyclesImageι
          (Stacks.Cohomology.RightDerivedBoundary.toSC D.residueAbelianSequence) 0).hom.app
            (op ⊤) t) =
      (AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra
        (Scheme.Hom.deRhamAlgebras D.f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras D.f))).one.eval (op ⊤)) :
    (realizationIsoAt D.baseSpace D.deRhamPlus 0).hom
        (Stacks.DerivedIndexing.imageCycleClass (sectionsFunctor D.baseSpace.carrier ⊤)
          D.residueAbelianSequence t) =
      AlgebraicGeometry.SheafOfModules.deRhamOneClass (Scheme.Hom.deRhamAlgebras D.f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) := by
  have h1 :=
    Stacks.Cohomology.RealizationAgreement.realizationIso_hom_comp_derivedSectionsFunctorIso
      D.baseSpace D.deRhamPlus 0
  have hi := ConcreteCategory.congr_hom
    (Stacks.DerivedIndexing.singleCyclesHom_cyclesMap_iCycles
      (sectionsFunctor D.baseSpace.carrier ⊤) D.residueAbelianSequence) t
  refine (ConcreteCategory.congr_hom h1.symm _).trans ?_
  refine (Stacks.Cech.Hypercohomology.realizationUnbounded_abelianGlobalClass D.deRhamPlus 0 _
    (AlgebraicGeometry.SheafOfModules.deRhamOneCycle (Scheme.Hom.deRhamAlgebras D.f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)))
    ?_).trans
    (AlgebraicGeometry.SheafOfModules.deRhamOneClass_eq_globalClass_one _ _).symm
  refine (hi.trans ?_).trans
    (AlgebraicGeometry.SheafOfModules.iCycles_deRhamOneCycle _ _).symm
  exact hone

end Stacks.LineBundle


end
