module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationRightUnitLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCurryingAssociativityGeneralSource

/-! # Example 0FPC's left-dual clause from two equations

Let `(X, O_X)` be a ringed space and let `K` be a perfect object of `D(O_X)`. The left-dual
assertion of **Example 0FPC** is that `(K^∨, η, ε)` is a left dual of `K` in the symmetric
monoidal category `D(O_X)` of Stacks 0FPT. It follows from the equation **(C)**, the
compatibility of the composition morphism of Stacks 0A8V with the application morphism of
Stacks 08J8, and (C) follows in turn from two equations:

* **the derived passage** `hcmp`: `cmp_{K,L,M} = Φ_{H,G,E'}(ψ ≫ cur⁻¹)`, where
  `ψ = RSheafHom(ε_{K,L}, M)` and `cur` is a currying comparison
  `RSheafHom(G, RSheafHom(K,M)) ≅ RSheafHom(G ⊗^L K, M)`. Its chain-level counterpart is
  `AlgebraicGeometry.RingedSite.curryHomEquiv_doubleContraction`.
* **the coherence** `hcoh`: `Stacks.SheafOfModules.derivedCurryCounitSourceCoherence`, an
  instance of the associativity coherence of Stacks 08DI.

This file proves (C′) from `hcmp` and `hcoh`, via
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv_derivedSheafHomComposition_of_laws`, and
deduces (C) at intermediate object the structure sheaf. The left-dual clause then follows by
`Stacks.SheafOfModules.exactPairingDerivedDualOfCompositionLaw`.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomTensorEquiv_derivedSheafHomComposition_of_coherence`:
  (C′) from `hcmp` and `hcoh`.
* the `structureSheafMiddle` specialisation of the first result (the second theorem of this
  file): (C) at intermediate object the structure sheaf from `hcmp` and `hcoh`, with the right
  tensor factor written `derivedDual Rc L`.

The composition law (C) itself holds for all objects, by
`Stacks.SheafOfModules.compositionApplicationLaw`.

## Implementation notes

The additivity and total-complex instances are carried as binders. The left-dual clause itself,
`Stacks.SheafOfModules.exactPairingDerivedDualOfCoherence`, is stated in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectPairingFromCoherenceFinal`, where
these instances are fixed to file-local constants.

## References

* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
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
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

section Monoidal

attribute [local instance] derivedMonoidalStructure

/-- **(C′)**: given a currying comparison `cur`, the derived passage `hcmp` and the coherence
`hcoh` (`Stacks.SheafOfModules.derivedCurryCounitSourceCoherence` at `A := RSheafHom(K, L)`,
`B := K`), the `Φ`-transpose of the composition morphism of Stacks 0A8V is the associator
followed by the `Φ`-transpose of `RSheafHom(ε_{K,L}, M)`. -/
theorem derivedSheafHomTensorEquiv_derivedSheafHomComposition_of_coherence
    (K L M : DerivedCategory (StructureSheafModules Rc))
    (cur : ((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
          (((derivedSheafHom Rc).obj (op K)).obj M) ≅
        ((derivedSheafHom Rc).obj
          (op (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K))).obj M)
    (hcmp : derivedSheafHomTensorEquiv Rc (((derivedSheafHom Rc).obj (op L)).obj M)
          (((derivedSheafHom Rc).obj (op K)).obj L)
          (((derivedSheafHom Rc).obj (op K)).obj M)
          (((derivedSheafHom Rc).map (derivedSheafHomCounit Rc K L).op).app M ≫ cur.inv) =
        derivedSheafHomComposition Rc K L M)
    (hcoh : derivedCurryCounitSourceCoherence Rc (((derivedSheafHom Rc).obj (op K)).obj L) K M
      cur.hom) :
    derivedSheafHomTensorEquiv Rc
        (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op L)).obj M)).obj
          (((derivedSheafHom Rc).obj (op K)).obj L)) K M
        (derivedSheafHomComposition Rc K L M) =
      (α_ (((derivedSheafHom Rc).obj (op L)).obj M)
          (((derivedSheafHom Rc).obj (op K)).obj L) K).hom ≫
        derivedSheafHomTensorEquiv Rc (((derivedSheafHom Rc).obj (op L)).obj M)
          (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K) M
          (((derivedSheafHom Rc).map (derivedSheafHomCounit Rc K L).op).app M) := by
  refine derivedSheafHomTensorEquiv_derivedSheafHomComposition_of_laws Rc K L M cur.hom _
    (by rw [Category.assoc, cur.inv_hom_id, Category.comp_id]) hcmp ?_
  rw [← derivedSheafHomCounit_whiskerRight_eq' Rc _
    (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K) M cur.hom]
  exact hcoh.symm

/-- **(C) at intermediate object the structure sheaf**: given a currying comparison `cur`,
the derived passage `hcmp` and the coherence `hcoh`, the composition morphism
`RSheafHom(O_X, M) ⊗^L RSheafHom(L, O_X) → RSheafHom(L, M)` whiskered by `L` and followed by
the application morphism agrees with the associator followed by the two application morphisms,
the right tensor factor being written `Stacks.SheafOfModules.derivedDual Rc L`. -/
theorem
derivedSheafHomComposition_structureSheafMiddle_whiskerRight_comp_derivedSheafHomCounit_of_coherence
    (L M : DerivedCategory (StructureSheafModules Rc))
    (cur : ((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op L)).obj
            (RingedSite.derivedStructureSheaf (ringedSite Rc))))).obj
          (((derivedSheafHom Rc).obj (op L)).obj M) ≅
        ((derivedSheafHom Rc).obj
          (op (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op L)).obj
            (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj L))).obj M)
    (hcmp : derivedSheafHomTensorEquiv Rc
          (((derivedSheafHom Rc).obj
            (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj M)
          (((derivedSheafHom Rc).obj (op L)).obj
            (RingedSite.derivedStructureSheaf (ringedSite Rc)))
          (((derivedSheafHom Rc).obj (op L)).obj M)
          (((derivedSheafHom Rc).map
              (derivedSheafHomCounit Rc L
                (RingedSite.derivedStructureSheaf (ringedSite Rc))).op).app M ≫ cur.inv) =
        derivedSheafHomComposition Rc L
          (RingedSite.derivedStructureSheaf (ringedSite Rc)) M)
    (hcoh : derivedCurryCounitSourceCoherence Rc
      (((derivedSheafHom Rc).obj (op L)).obj
        (RingedSite.derivedStructureSheaf (ringedSite Rc))) L M cur.hom) :
    derivedSheafHomComposition Rc L
          (RingedSite.derivedStructureSheaf (ringedSite Rc)) M ▷ L ≫
        derivedSheafHomCounit Rc L M =
      (α_ (((derivedSheafHom Rc).obj
            (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj M)
          (derivedDual Rc L) L).hom ≫
        (((derivedSheafHom Rc).obj
            (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj M ◁
          derivedSheafHomCounit Rc L (RingedSite.derivedStructureSheaf (ringedSite Rc))) ≫
          derivedSheafHomCounit Rc
            (RingedSite.derivedStructureSheaf (ringedSite Rc)) M :=
  derivedSheafHomComposition_structureSheafMiddle_whiskerRight_comp_counit_of_transpose
    Rc L M
    (derivedSheafHomTensorEquiv_derivedSheafHomComposition_of_coherence Rc L
      (RingedSite.derivedStructureSheaf (ringedSite Rc)) M cur hcmp hcoh)

end Monoidal

end Stacks.SheafOfModules

end
