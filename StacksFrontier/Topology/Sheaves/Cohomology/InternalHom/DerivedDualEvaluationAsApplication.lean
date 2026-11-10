module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CupProductAndDualityPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionDoubleContraction
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationRightUnitLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedDualPairing

/-! # The application morphism at target the structure sheaf is the evaluation of the dual

Let `(X, O_X)` be a ringed space and let `L` be an object of `D(O_X)`. Two morphisms

`L^∨ ⊗^L_{O_X} L ⟶ O_X`

are available. One is `Stacks.SheafOfModules.derivedSheafHomCounit Rc L O_X`, the application
morphism of Stacks 08J8 — the bijection of Stacks 08DI applied to the identity of
`RSheafHom(L, O_X)` — read at target the structure sheaf. The other is
`AlgebraicGeometry.RingedSite.derivedDualEvaluation (ringedSite Rc) L`, the evaluation `ε` of
Tag 0FPU, the bijection of Stacks 08J8 applied to the identity of `L^∨`. They are equal, since
`Stacks.SheafOfModules.derivedDual Rc L` is `RSheafHom(L, O_X)` and both constructions are the
same bijection at the identity of that object.

## Main results

Both results are in the namespace `Stacks.SheafOfModules`.

* `derivedSheafHomCounit_structureSheaf_eq_derivedDualEvaluation`: the application morphism of
  Stacks 08J8 at target the structure sheaf is the evaluation of Tag 0FPU.
* `derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_doubleContraction`:
  if the composition morphism of Stacks 0A8V at intermediate object the structure sheaf is the
  transpose of the double contraction, then the canonical map of Stacks 08I1 followed by the
  application morphism is the contraction against `ε`.

## References

* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0FPU](https://stacks.math.columbia.edu/tag/0FPU)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] derivedMonoidalStructure

-- The statement below crosses the two spellings of the sheaf of rings of the space:
-- `derivedSheafHomCounit Rc` is stated over `StructureSheafModules Rc`, i.e. over
-- `(sheafCompose _ (forget₂ CommRingCat RingCat)).obj Rc`, while
-- `RingedSite.derivedDualEvaluation (ringedSite Rc)` is stated over
-- `Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O`. The two are the same sheaf of
-- rings, but seeing it needs `TopCat.Sheaf`, `CategoryTheory.sheafCompose` and
-- `Tensor.ringSheaf` unfolded; without that the `Abelian` instances on the two sides are
-- different terms at the transparency the keyed matching of `rw` works at, and the first step
-- of the proof below does not fire. Same attribute, for the same reason, as in the neighbour
-- that defines `ringedSite`, `StacksDraft.Topology.Sheaves.Cohomology`
-- `.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso`.
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose Tensor.ringSheaf

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **The application morphism of Stacks 08J8 at target the structure sheaf is the evaluation of
Tag 0FPU.** Both are the bijection of Stacks 08DI applied to the identity of
`RSheafHom(L, O_X) = L^∨`, the first written through `Stacks.SheafOfModules.derivedSheafHom` and
the second through `AlgebraicGeometry.RingedSite.derivedDual`. -/
theorem derivedSheafHomCounit_structureSheaf_eq_derivedDualEvaluation
    (L : DerivedCategory (StructureSheafModules Rc)) :
    derivedSheafHomCounit Rc L (RingedSite.derivedStructureSheaf (ringedSite Rc)) =
      RingedSite.derivedDualEvaluation (ringedSite Rc) L := by
  rw [derivedSheafHomCounit_eq, derivedSheafHomTensorEquiv_eq,
    RingedSite.derivedDualEvaluation_eq]

/-- **The canonical map of Stacks 08I1 against application, from the double contraction.** If
the composition morphism of Stacks 0A8V at intermediate object the structure sheaf is the
transpose, under the bijection of Stacks 08DI, of the double contraction written with
`Stacks.SheafOfModules.derivedCounitCurry` (`htr`), then

`derivedTensorDualToSheafHom Rc L M ▷ L ≫ derivedSheafHomCounit Rc L M =
  derivedDualContraction Rc M L`. -/
theorem derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_doubleContraction
    (L M : DerivedCategory (StructureSheafModules Rc))
    (htr : (derivedSheafHomTensorEquiv Rc
            (((derivedSheafHom Rc).obj
              (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj M)
            (((derivedSheafHom Rc).obj (op L)).obj
              (RingedSite.derivedStructureSheaf (ringedSite Rc)))
            (((derivedSheafHom Rc).obj (op L)).obj M)).symm
          (derivedSheafHomComposition Rc L
            (RingedSite.derivedStructureSheaf (ringedSite Rc)) M) ≫
          derivedCounitCurry Rc L (RingedSite.derivedStructureSheaf (ringedSite Rc)) M =
        ((derivedSheafHom Rc).map
          (derivedSheafHomCounit Rc L
            (RingedSite.derivedStructureSheaf (ringedSite Rc))).op).app M) :
    derivedTensorDualToSheafHom Rc L M ▷ L ≫ derivedSheafHomCounit Rc L M =
      derivedDualContraction Rc M L := by
  have h :=
    derivedSheafHomComposition_structSheafMiddle_whiskerRight_comp_counit_of_doubleContraction
      Rc L M htr
  rw [derivedSheafHomCounit_structureSheaf_eq_derivedDualEvaluation] at h
  exact derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws
    Rc L M (RingedSite.derivedDualEvaluation (ringedSite Rc) L) h
    (derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit_monoidal Rc M)

end Stacks.SheafOfModules

end
