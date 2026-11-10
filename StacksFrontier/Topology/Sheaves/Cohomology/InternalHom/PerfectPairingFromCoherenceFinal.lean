module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedDualEvaluationAsApplication
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectPairingFromCoherence

/-! # The left-dual clause of Example 0FPC, from the derived passage and the coherence

Let `(X, O_X)` be a ringed space and let `K` be a perfect object of `D(O_X)`.  This file holds
the single declaration that assembles the left-dual assertion of **Example 0FPC** from the two
equations that
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectPairingFromCoherence` reduces it to:

* **the derived passage** `hcmp`, the statement that the composition morphism of Stacks 0A8V is
  the `Φ`-transpose of `RSheafHom(ε, O_X)` run through a currying comparison `cur⁻¹`;
* **the coherence** `hcoh`, `Stacks.SheafOfModules.derivedCurryCounitSourceCoherence`, the single
  instance of the associativity coherence of Stacks 08DI.

## Implementation notes

`Stacks.SheafOfModules.exactPairingDerivedDualOfCompositionLaw` takes the composition law with
the inner application written `Stacks.SheafOfModules.derivedDualEvaluation` (the evaluation of
Tag 0FPU), while the composition law obtained from the coherence has it written
`derivedSheafHomCounit Rc K O_X` (the application morphism of Stacks 08J8 at target the structure
sheaf). The two are identified by
`Stacks.SheafOfModules.derivedSheafHomCounit_structureSheaf_eq_derivedDualEvaluation`, which
requires the three slice-site instance binders carried here.

## Main results

* `Stacks.SheafOfModules.exactPairingDerivedDualOfCoherence`: **the left-dual assertion of
  Example 0FPC from `hcmp` and `hcoh`.**

The left dual of a perfect object with no hypothesis beyond perfectness is
`Stacks.SheafOfModules.exactPairingDerivedDual`, from the composition law
`Stacks.SheafOfModules.compositionApplicationLaw`.

## References

* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]
  [∀ V : Opens X, HasSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X, ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [∀ V : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]

open Stacks.SheafOfModules renaming
derivedSheafHomComposition_structureSheafMiddle_whiskerRight_comp_derivedSheafHomCounit_of_coherence
  → compositionLawOfCoherence in
/-- **The left dual of a perfect object, from the derived passage and the coherence.**  For a
perfect object `K` of `D(O_X)` the pair `(η, ε) = (derivedDualCoevaluation,
derivedDualEvaluation)` is an exact pairing — `K^∨ = RSheafHom(K, O_X)` is a left dual of `K` in
the sense of Categories, Definition 0FFP — as soon as the derived passage `hcmp` and the
coherence `hcoh` hold at `K`: together they give the composition law (C), and the right unit
law (UR) and the unit law (UL) are
`Stacks.SheafOfModules.derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit`
and `Stacks.SheafOfModules.derivedSheafHomCounit_unit_law_monoidal'`. -/
@[instance_reducible]
def exactPairingDerivedDualOfCoherence
    (K : DerivedCategory (StructureSheafModules Rc)) (hK : (ringedSite Rc).IsPerfect K)
    (cur : ((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj
            (RingedSite.derivedStructureSheaf (ringedSite Rc))))).obj
          (((derivedSheafHom Rc).obj (op K)).obj K) ≅
        ((derivedSheafHom Rc).obj
          (op (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj
            (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj K))).obj K)
    (hcmp : derivedSheafHomTensorEquiv Rc
          (((derivedSheafHom Rc).obj
            (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj K)
          (((derivedSheafHom Rc).obj (op K)).obj
            (RingedSite.derivedStructureSheaf (ringedSite Rc)))
          (((derivedSheafHom Rc).obj (op K)).obj K)
          (((derivedSheafHom Rc).map
              (derivedSheafHomCounit Rc K
                (RingedSite.derivedStructureSheaf (ringedSite Rc))).op).app K ≫ cur.inv) =
        derivedSheafHomComposition Rc K
          (RingedSite.derivedStructureSheaf (ringedSite Rc)) K)
    (hcoh : derivedCurryCounitSourceCoherence Rc
      (((derivedSheafHom Rc).obj (op K)).obj
        (RingedSite.derivedStructureSheaf (ringedSite Rc))) K K cur.hom) :
    letI := derivedMonoidalStructure Rc
    ExactPairing K (derivedDual Rc K) := by
  letI := derivedMonoidalStructure Rc
  have hC :=
    compositionLawOfCoherence Rc K K cur hcmp hcoh
  rw [derivedSheafHomCounit_structureSheaf_eq_derivedDualEvaluation] at hC
  exact exactPairingDerivedDualOfCompositionLaw Rc K hK hC

end Stacks.SheafOfModules

end
