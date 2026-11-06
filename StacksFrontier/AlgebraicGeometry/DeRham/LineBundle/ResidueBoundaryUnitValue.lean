module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ResidueBoundaryChern

/-!
# The value at the unit of the boundary map of the residue sequence, from Čech data

Let `D` be a line-bundle situation. This file combines the reduction of `δ(1)` to the abelian-sheaf
realization (`Stacks.LineBundle.Situation.deRhamEvalOne_residueBoundary_eq_of`) with the
computation of the abelian boundary on Čech data
(`Stacks.LineBundle.Situation.abelianBoundary_eq_chernClass`): given a global section `t` of the
image of the cycles of the residue sequence lifting locally to cocycles, whose differences are
`d log` of a transition cocycle of `L`, and whose abelian class is carried to the unit
`1 ∈ H⁰_{dR}` by the realization comparison, the boundary map of the residue sequence takes the
value `c₁^{dR}(L)` at the unit ([Stacks, Tag 0FUG]).

## Main results

* `Stacks.LineBundle.Situation.deRhamEvalOne_residueBoundary_eq_of_cech`: the value at the unit.

## References

* [Stacks Project, Tag 0FUG](https://stacks.math.columbia.edu/tag/0FUG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.LineBundle

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

variable (D : Situation.{u})

open Stacks.Cohomology.Leray (sectionsFunctor)
open Stacks.Cohomology.RightDerivedBoundary (toSC)
open Stacks.Cohomology.RealizationShift (realizationIsoAt)

/-- **`δ(1) = c₁^{dR}(p)` from Čech data**: if the Čech data of the residue sequence represent the
Picard class `p`, and the abelian class of the global section `t` is carried to the unit by the
realization comparison, then the boundary map of the residue sequence takes the value
`c₁^{dR}(p)` at the unit. -/
theorem Situation.deRhamEvalOne_residueBoundary_eq_of_cech
    (p : Stacks.SheafOfModules.Picard.PicardGroup D.X.toRingedSpace.sheaf.obj
      (_root_.structureSheaf D.X.toRingedSpace.sheaf).property)
    (t : (HomologicalComplex.shortExactCycles (toSC D.residueAbelianSequence) 0).X₃.obj.obj (op ⊤))
    {I : Type u} (Ui : I → Opens D.baseSpace.carrier)
    (hUi : (⊤ : Opens D.baseSpace.carrier) = ⨆ i, Ui i)
    (e : CechCochains.Cochain Ui
      (HomologicalComplex.shortExactCycles (toSC D.residueAbelianSequence) 0).X₂.obj 0)
    (he : ∀ i : Fin 1 → I, (HomologicalComplex.shortExactCycles (toSC D.residueAbelianSequence)
        0).g.hom.app (op (CechCochains.inter Ui i)) (e i) =
      (HomologicalComplex.shortExactCycles (toSC D.residueAbelianSequence) 0).X₃.obj.map
        (homOfLE le_top).op t)
    (z : CechCochains.cocycles1 Ui D.unitsSheafBase.obj)
    (ω : CechCochains.cocycles1 Ui
      (HomologicalComplex.shortExactCycles (toSC D.residueAbelianSequence) 0).X₁.obj)
    (hωz : ∀ i : Fin 2 → I, ω.val i =
      D.logarithmicDifferentialClosed.hom.app (op (CechCochains.inter Ui i)) (z.val i))
    (hω : ∀ i : Fin 2 → I, (HomologicalComplex.shortExactCycles (toSC D.residueAbelianSequence)
        0).f.hom.app (op (CechCochains.inter Ui i)) (ω.val i) =
      CechCochains.cechD Ui
        (HomologicalComplex.shortExactCycles (toSC D.residueAbelianSequence) 0).X₂.obj 0 e i)
    (hz : Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections D.baseSpace.carrier ⊤ Ui hUi
        D.unitsSheafBase (CechCochains.cls Ui _ z) =
      (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup D.X.toRingedSpace).symm p)
    (hU1 : (realizationIsoAt D.baseSpace D.deRhamPlus 0).hom
        (Stacks.DerivedIndexing.imageCycleClass (sectionsFunctor D.baseSpace.carrier ⊤)
          D.residueAbelianSequence t) =
      AlgebraicGeometry.SheafOfModules.deRhamOneClass (Scheme.Hom.deRhamAlgebras D.f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))) :
    AlgebraicGeometry.SheafOfModules.deRhamEvalOne (Scheme.Hom.deRhamAlgebras D.f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) 2
        D.residueShiftedSequence.boundary =
      (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
        (Scheme.Hom.deRhamAlgebras D.f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))
          2).hom.hom
        (AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian
          (Scheme.Hom.deRhamAlgebras D.f)
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras D.f)) p) :=
  D.deRhamEvalOne_residueBoundary_eq_of _ hU1 _
    (D.abelianBoundary_eq_chernClass p t Ui hUi e he z ω hωz hω hz)

end Stacks.LineBundle

end
