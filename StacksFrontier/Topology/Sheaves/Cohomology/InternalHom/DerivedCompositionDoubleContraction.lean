module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionTransposeReduction

/-! # A canonical currying morphism and the composition–application equation (C)

Let `(X, O_X)` be a ringed space, let `K`, `L`, `M` be objects of `D(O_X)`, and write
`H = RSheafHom(L, M)`, `G = RSheafHom(K, L)`, `E' = RSheafHom(K, M)` and
`E = RSheafHom(G, E')`. Write **(C)** for the equation

`cmp_{K,L,M} ▷ K ≫ ε_{K,M} = (α_ H G K).hom ≫ (H ◁ ε_{K,L}) ≫ ε_{L,M}`

relating the composition morphism `cmp` of [Stacks, Tag 0A8V] and the application morphisms `ε`
of [Stacks, Tag 08J8]. This file defines the morphism

`derivedCounitCurry Rc K L M := Φ_{E, G ⊗^L K, M}⁻¹((α_ E G K).inv ≫ ε_{G,E'} ▷ K ≫ ε_{K,M})`,

`Φ` being the bijection of [Stacks, Tag 08DI], which has the type of the currying comparison of
[Stacks, Tag 08J9] at `(G, K, M)`. It satisfies the associativity coherence

`ε_{G,E'} ▷ K ≫ ε_{K,M} = (α_ E G K).hom ≫ Φ_{E, G ⊗^L K, M}(derivedCounitCurry Rc K L M)`,

and (C) follows from the single equation

`Φ_{H,G,E'}⁻¹(cmp_{K,L,M}) ≫ derivedCounitCurry Rc K L M = RSheafHom(ε_{K,L}, M)`.

## Main definitions

* `Stacks.SheafOfModules.derivedCounitCurry`: the transpose under `Φ` of the double contraction
  against the application morphisms.

## Main results

* `Stacks.SheafOfModules.derivedCounitCurry_spec`: the associativity coherence above.
* `derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_doubleContraction`:
  (C) from the single equation above, and its `structureSheafMiddle` variant: the same with
  middle object the structure sheaf `O_X`.

## References

* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
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

/-- **The transpose of the double contraction against the application morphisms of
[Stacks, Tag 08J8].** For objects `K`, `L`, `M` of `D(O_X)`, with `G = RSheafHom(K, L)`,
`E' = RSheafHom(K, M)` and `E = RSheafHom(G, E')`, the morphism

`E ⟶ RSheafHom(G ⊗^L_{O_X} K, M)`

which the bijection `Φ` of [Stacks, Tag 08DI] matches with the double contraction
`(α_ E G K).inv ≫ ε_{G,E'} ▷ K ≫ ε_{K,M} : E ⊗^L (G ⊗^L K) ⟶ M`. -/
def derivedCounitCurry (K L M : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
        (((derivedSheafHom Rc).obj (op K)).obj M) ⟶
      ((derivedSheafHom Rc).obj
        (op (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K))).obj M :=
  (derivedSheafHomTensorEquiv Rc
      (((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
        (((derivedSheafHom Rc).obj (op K)).obj M))
      (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K) M).symm
    ((α_ (((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
            (((derivedSheafHom Rc).obj (op K)).obj M))
          (((derivedSheafHom Rc).obj (op K)).obj L) K).inv ≫
      derivedSheafHomCounit Rc (((derivedSheafHom Rc).obj (op K)).obj L)
          (((derivedSheafHom Rc).obj (op K)).obj M) ▷ K ≫
        derivedSheafHomCounit Rc K M)

/-- **`derivedCounitCurry` satisfies the associativity coherence**

`ε_{G,E'} ▷ K ≫ ε_{K,M} = (α_ E G K).hom ≫ Φ_{E, G ⊗^L K, M}(derivedCounitCurry Rc K L M)`. -/
theorem derivedCounitCurry_spec (K L M : DerivedCategory (StructureSheafModules Rc)) :
    derivedSheafHomCounit Rc (((derivedSheafHom Rc).obj (op K)).obj L)
          (((derivedSheafHom Rc).obj (op K)).obj M) ▷ K ≫
        derivedSheafHomCounit Rc K M =
      (α_ (((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
            (((derivedSheafHom Rc).obj (op K)).obj M))
          (((derivedSheafHom Rc).obj (op K)).obj L) K).hom ≫
        derivedSheafHomTensorEquiv Rc
          (((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
            (((derivedSheafHom Rc).obj (op K)).obj M))
          (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K) M
          (derivedCounitCurry Rc K L M) := by
  rw [derivedCounitCurry, AddEquiv.apply_symm_apply, Iso.hom_inv_id_assoc]

/-- **(C) from the single equation that the composition morphism of [Stacks, Tag 0A8V] is the
transpose of the double contraction.** Given the hypothesis `htr`

`Φ_{H,G,E'}⁻¹(cmp_{K,L,M}) ≫ derivedCounitCurry Rc K L M = RSheafHom(ε_{K,L}, M)`,

(C) holds: `cmp_{K,L,M} ▷ K ≫ ε_{K,M} = (α_ H G K).hom ≫ (H ◁ ε_{K,L}) ≫ ε_{L,M}`. -/
theorem derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_doubleContraction
    (K L M : DerivedCategory (StructureSheafModules Rc))
    (htr : (derivedSheafHomTensorEquiv Rc (((derivedSheafHom Rc).obj (op L)).obj M)
            (((derivedSheafHom Rc).obj (op K)).obj L)
            (((derivedSheafHom Rc).obj (op K)).obj M)).symm
          (derivedSheafHomComposition Rc K L M) ≫ derivedCounitCurry Rc K L M =
        ((derivedSheafHom Rc).map (derivedSheafHomCounit Rc K L).op).app M) :
    derivedSheafHomComposition Rc K L M ▷ K ≫ derivedSheafHomCounit Rc K M =
      (α_ (((derivedSheafHom Rc).obj (op L)).obj M)
          (((derivedSheafHom Rc).obj (op K)).obj L) K).hom ≫
        (((derivedSheafHom Rc).obj (op L)).obj M ◁ derivedSheafHomCounit Rc K L) ≫
          derivedSheafHomCounit Rc L M :=
  derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_laws Rc K L M
    (derivedCounitCurry Rc K L M) _ htr (AddEquiv.apply_symm_apply _ _)
    (derivedCounitCurry_spec Rc K L M)

/-- **(C) with middle object the structure sheaf, from the same single equation `htr`**: the
previous theorem at `K := L`, `L := O_X` and `M := M`, with the right tensor factor
`RSheafHom(L, O_X)` written as `derivedDual Rc L`. -/
theorem derivedSheafHomComposition_structSheafMiddle_whiskerRight_comp_counit_of_doubleContraction
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
  derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_doubleContraction Rc L
    (RingedSite.derivedStructureSheaf (ringedSite Rc)) M htr

end Monoidal

end Stacks.SheafOfModules

end
