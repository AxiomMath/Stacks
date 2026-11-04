module

public import StacksFrontier.Homology.DerivedIndexing.UnitClass
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.DerivedBoundaryCocycle

/-!
# The boundary map of a short exact sequence of complexes of sheaves on a global cocycle

Let `0 → K₁ → K₂ → K₃ → 0` be a short exact sequence of bounded below complexes of abelian
sheaves on a topological space `X`, and let `t` be a global section of the image `I` of the
degree-zero cycles `Z⁰K₂ ⟶ Z⁰K₃`; it is a global cocycle of `K₃`. Suppose `t` lifts on an open
covering `𝒰` to local cocycles `eᵢ` of `K₂`, and that the Čech coboundary `e_{i₁} - e_{i₀}` is the
image of a Čech `1`-cocycle `ω` of `Z⁰K₁`. Then the boundary map `H⁰(X, K₃) ⟶ H¹(X, K₁)` of the
sequence carries the class of `t` to the image under `Z⁰K₁[0] ⟶ K₁` of the class of `ω`
([Stacks, Tags 01EQ, 02AP]).

## Main results

* `Stacks.Cohomology.CechOne.shortExactBoundary_unitClassHom_cyclesImage`: the formula.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.HigherDirectImagePresheaf Stacks.Cohomology.RightDerivedBoundary
open Stacks.DerivedIndexing (unitClassHom singleCyclesHom)

universe u

namespace Stacks.Cohomology.CechOne

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)

variable {X : TopCat.{u}} {S : ShortComplex (CochainComplex.Plus (AbelianSheaf X))}
  (hS : (toSC S).ShortExact)

/-- **The boundary map of a short exact sequence of complexes of sheaves on a global cocycle that
lifts locally to cocycles of the middle term.** The class of a global section `t` of the image of
the cycles is carried to the image under the inclusion of the cycles `Z⁰K₁[0] ⟶ K₁` of the class
of the Čech `1`-cocycle `ω` of the differences of the lifts. -/
theorem shortExactBoundary_imageCycleClass
    (t : (HomologicalComplex.shortExactCycles (toSC S) 0).X₃.val.obj (op ⊤))
    {I : Type u} (Ui : I → Opens X) (hUi : (⊤ : Opens X) = ⨆ i, Ui i)
    (e : CechCochains.Cochain Ui (HomologicalComplex.shortExactCycles (toSC S) 0).X₂.val 0)
    (he : ∀ i : Fin 1 → I, (HomologicalComplex.shortExactCycles (toSC S) 0).g.hom.app
        (op (CechCochains.inter Ui i)) (e i) =
      (HomologicalComplex.shortExactCycles (toSC S) 0).X₃.val.map (homOfLE le_top).op t)
    (ω : CechCochains.cocycles1 Ui (HomologicalComplex.shortExactCycles (toSC S) 0).X₁.val)
    (hω : ∀ i : Fin 2 → I, (HomologicalComplex.shortExactCycles (toSC S) 0).f.hom.app
        (op (CechCochains.inter Ui i)) (ω.val i) =
      CechCochains.cechD Ui (HomologicalComplex.shortExactCycles (toSC S) 0).X₂.val 0 e i) :
    shortExactBoundary (sectionsFunctor X ⊤) S hS 0 1 rfl
        (Stacks.DerivedIndexing.imageCycleClass (sectionsFunctor X ⊤) S t) =
      Stacks.DerivedIndexing.cyclesRightDerivedOneMap (sectionsFunctor X ⊤) S
        (cechH1ToRightDerivedSections X ⊤ Ui hUi _ (CechCochains.cls Ui _ ω)) := by
  have hZ := HomologicalComplex.shortExactCycles_shortExact 0 hS
  have hc := rightDerivedPlusδ_toRightDerivedZero _ hZ t Ui hUi e he ω hω
  have hmor := ConcreteCategory.congr_hom
    (Stacks.DerivedIndexing.imageCycleClass_comp_shortExactBoundary_eq (sectionsFunctor X ⊤) S hS) t
  refine hmor.trans ?_
  rw [← hc]
  simp only [ConcreteCategory.comp_apply]

end Stacks.Cohomology.CechOne

end
