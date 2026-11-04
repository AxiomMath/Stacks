module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductSquare
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyShiftedSingleCochains

/-!
# Classes of Čech cocycles in the unbounded model of cohomology

Let `(S, 𝒪_S)` be a ringed space and `𝒰` an open covering of `S`. The comparison
`Tot(Č^•(𝒰, 𝒦^•)) ⟶ RΓ(S, 𝒦^•)` of [Stacks, Tag 08BN] is stated by
`Stacks.Cech.CupProductSquare.cechToBaseSections` with values in the unbounded derived global
sections `Stacks.Cohomology.GlobalKunneth.baseSections`, the model on which the global cup product
of Cohomology, Section 0FKU, and the pullback maps of Hodge cohomology are stated. This file
records, in that model, the class of a cohomology class of the total Čech complex, and the class
of an explicit Čech cocycle of a sheaf of modules placed in degree `0`, and compares them with the
classes of `Stacks.Cech.Hypercohomology`, which are taken in the bounded below model.

## Main definitions

* `Stacks.HodgeWeil.cechBaseClass`: the class in `H^n(S, 𝒦^•)` of a class of
  `H^n(Tot(Č^•(𝒰, 𝒦^•)))`.
* `Stacks.HodgeWeil.cechSheafClass`: the class in `H^p(S, ℱ)` of a Čech `p`-cocycle of a sheaf of
  modules `ℱ`.

## Main results

* `Stacks.HodgeWeil.cechBaseClass_eq`: the class is the class of `Stacks.Cech.Hypercohomology`
  followed by the identification of the two models of derived global sections.

## References

* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing abSections)
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard

variable (S : RingedSpace.{u, u}) {I : Type u} (U : I → Opens S.carrier)
  (hU : (⊤ : Opens S.carrier) = ⨆ i, U i)

/-- **The class in `Hⁿ(S, 𝒦^•)` of a cohomology class of the total Čech complex** of an open
covering, through the comparison `Tot(Č^•(𝒰, 𝒦^•)) ⟶ RΓ(S, 𝒦^•)` of [Stacks, Tag 08BN] in the
unbounded model `baseSections` of derived global sections. -/
def cechBaseClass
    (K : CochainComplex.Plus
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)))
    (n : ℤ) :
    ((Stacks.Cech.Linear.totalCechComplexFunctor S.carrier
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf) ⊤ U hU).obj K.obj).homology n ⟶
      cohomologyModule (S := S) (DerivedCategory.Q.obj K.obj) n :=
  (DerivedCategory.homologyFunctorFactors _ n).inv.app _ ≫
    (DerivedCategory.homologyFunctor _ n).map
      ((Stacks.Cech.CupProductSquare.cechToBaseSections S U hU).app K)

/-- **The class is the class of `Stacks.Cech.Hypercohomology`**, taken in the bounded below
model, followed by the identification of the two models of derived global sections. -/
theorem cechBaseClass_eq
    (K : CochainComplex.Plus
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)))
    (n : ℤ) :
    cechBaseClass S U hU K n =
      Stacks.Cech.Hypercohomology.cechClass S.sheaf U hU K n ≫
        (DerivedCategory.homologyFunctor _ n).map
          ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIsoBaseSections S).hom.app
            K) := by
  rw [cechBaseClass, Stacks.Cech.CupProductSquare.cechToBaseSections_app]
  exact (congrArg (fun t => (DerivedCategory.homologyFunctorFactors _ n).inv.app _ ≫ t)
    ((DerivedCategory.homologyFunctor _ n).map_comp _ _)).trans (Category.assoc _ _ _).symm

/-- **The class in `H^p(S, ℱ)` of a Čech `p`-cocycle** `c` of a sheaf of modules `ℱ` on an open
covering: the class of the cochain of the total Čech complex of `ℱ[0]` attached to `c`. -/
def cechSheafClass
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)) {p : ℕ}
    (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0) :
    cohomologyModule (S := S)
      (DerivedCategory.Q.obj (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj)
      ((p : ℤ) + 0) :=
  (cechBaseClass S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0) ((p : ℤ) + 0)).hom
    ((Stacks.Cech.Hypercohomology.cocycleClass ((p : ℤ) + 0)
      (Stacks.Cech.Hypercohomology.cochainOfAt U hU F 0 c)
      (Stacks.Cech.Hypercohomology.cochainOfAt_d_eq_zero U hU F 0 c hc)).hom
      (1 : SectionRing (ringSheaf S.sheaf) ⊤))

/-- `cechSheafClass` is the class `Stacks.Cech.Hypercohomology.cechCocycleClassAt` of the
bounded below model, followed by the identification of the two models. -/
theorem cechSheafClass_eq
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)) {p : ℕ}
    (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0) :
    cechSheafClass S U hU F c hc =
      ((DerivedCategory.homologyFunctor _ ((p : ℤ) + 0)).map
          ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIsoBaseSections S).hom.app
            (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0))).hom
        (Stacks.Cech.Hypercohomology.cechCocycleClassAt U hU F 0 c hc) := by
  rw [cechSheafClass, cechBaseClass_eq]
  rfl

end Stacks.HodgeWeil

end
