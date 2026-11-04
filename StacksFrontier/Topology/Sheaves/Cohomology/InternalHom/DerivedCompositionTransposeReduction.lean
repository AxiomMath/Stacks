module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationCompositionReduction

/-!
# The composition law of derived internal Hom from two hypotheses

Let `(X, O_X)` be a ringed space, let `K`, `L`, `M` be objects of `D(O_X)`, and write
`H = RSheafHom(L, M)`, `G = RSheafHom(K, L)`, `E' = RSheafHom(K, M)` and
`E = RSheafHom(G, E')`. Write `ε` for the application morphisms, `cmp_{K,L,M} : H ⊗ G ⟶ E'` for
the composition morphism of [Stacks, Tag 0A8V] and `Φ` for the bijection
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv` of [Stacks, Tag 08DI]. This file proves

`cmp_{K,L,M} ▷ K ≫ ε_{K,M} = (α_ H G K).hom ≫ (H ◁ ε_{K,L}) ≫ ε_{L,M}`,

and its transpose under `Φ`, from two hypotheses taken as arguments, for a morphism
`cur : E ⟶ RSheafHom(G ⊗^L K, M)`:

* `hcmp`: `cmp_{K,L,M} = Φ_{H,G,E'}(D)` for a morphism `D : H ⟶ E` with
  `D ≫ cur = RSheafHom(ε_{K,L}, M)`;
* `hA9`: `ε_{G,E'} ▷ K ≫ ε_{K,M} = (α_ E G K).hom ≫ Φ_{E, G ⊗^L K, M}(cur)`, the associativity
  coherence of [Stacks, Tag 08J9].

## Main results

All in the namespace `Stacks.SheafOfModules`:

* `derivedSheafHomTensorEquiv_comp_left`: source naturality of `Φ`,
  `Φ_{A',B,Z}(a ≫ y) = a ▷ B ≫ Φ_{A,B,Z}(y)`.
* `derivedSheafHomTensorEquiv_derivedSheafHomComposition_of_laws`: the transpose of the
  composition morphism under `Φ`, from `hcmp` and `hA9`.
* `derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_laws`: the displayed
  equation, from `hcmp` and `hA9`.
* `derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_curryIso`: the displayed
  equation, from `hcmp` and `hA9`, when `cur` is an isomorphism and
  `D = RSheafHom(ε_{K,L}, M) ≫ cur⁻¹`.

## References

* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
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

/-- Source naturality of the bijection `Stacks.SheafOfModules.derivedSheafHomTensorEquiv`:
`Φ_{A',B,Z}(a ≫ y) = a ▷ B ≫ Φ_{A,B,Z}(y)`. -/
theorem derivedSheafHomTensorEquiv_comp_left
    {A A' : DerivedCategory (StructureSheafModules Rc)}
    (B Z : DerivedCategory (StructureSheafModules Rc)) (a : A' ⟶ A)
    (y : A ⟶ ((derivedSheafHom Rc).obj (op B)).obj Z) :
    derivedSheafHomTensorEquiv Rc A' B Z (a ≫ y) =
      a ▷ B ≫ derivedSheafHomTensorEquiv Rc A B Z y := by
  rw [← derivedSheafHomCounit_whiskerRight_eq' Rc A' B Z (a ≫ y),
    ← derivedSheafHomCounit_whiskerRight_eq' Rc A B Z y, comp_whiskerRight, Category.assoc]

/-- With `H = RSheafHom(L, M)`, `G = RSheafHom(K, L)`, `E' = RSheafHom(K, M)`,
`E = RSheafHom(G, E')`, `ε` the application morphisms and
`Φ = Stacks.SheafOfModules.derivedSheafHomTensorEquiv`: let `cur : E ⟶ RSheafHom(G ⊗ K, M)` and
`D : H ⟶ E` satisfy `D ≫ cur = RSheafHom(ε_{K,L}, M)` (`hD`). If the composition morphism is
`Φ_{H,G,E'}(D)` (`hcmp`) and the coherence
`ε_{G,E'} ▷ K ≫ ε_{K,M} = (α_ E G K).hom ≫ Φ_{E, G ⊗ K, M}(cur)` holds (`hA9`), then
`Φ_{H ⊗ G, K, M}(cmp_{K,L,M}) = (α_ H G K).hom ≫ Φ_{H, G ⊗ K, M}(RSheafHom(ε_{K,L}, M))`. -/
theorem derivedSheafHomTensorEquiv_derivedSheafHomComposition_of_laws
    (K L M : DerivedCategory (StructureSheafModules Rc))
    (cur : ((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
          (((derivedSheafHom Rc).obj (op K)).obj M) ⟶
        ((derivedSheafHom Rc).obj
          (op (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K))).obj M)
    (D : ((derivedSheafHom Rc).obj (op L)).obj M ⟶
        ((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
          (((derivedSheafHom Rc).obj (op K)).obj M))
    (hD : D ≫ cur = ((derivedSheafHom Rc).map (derivedSheafHomCounit Rc K L).op).app M)
    (hcmp : derivedSheafHomTensorEquiv Rc (((derivedSheafHom Rc).obj (op L)).obj M)
          (((derivedSheafHom Rc).obj (op K)).obj L)
          (((derivedSheafHom Rc).obj (op K)).obj M) D =
        derivedSheafHomComposition Rc K L M)
    (hA9 : derivedSheafHomCounit Rc (((derivedSheafHom Rc).obj (op K)).obj L)
            (((derivedSheafHom Rc).obj (op K)).obj M) ▷ K ≫
          derivedSheafHomCounit Rc K M =
        (α_ (((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
              (((derivedSheafHom Rc).obj (op K)).obj M))
            (((derivedSheafHom Rc).obj (op K)).obj L) K).hom ≫
          derivedSheafHomTensorEquiv Rc
            (((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
              (((derivedSheafHom Rc).obj (op K)).obj M))
            (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K) M cur) :
    derivedSheafHomTensorEquiv Rc
        (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op L)).obj M)).obj
          (((derivedSheafHom Rc).obj (op K)).obj L)) K M
        (derivedSheafHomComposition Rc K L M) =
      (α_ (((derivedSheafHom Rc).obj (op L)).obj M)
          (((derivedSheafHom Rc).obj (op K)).obj L) K).hom ≫
        derivedSheafHomTensorEquiv Rc (((derivedSheafHom Rc).obj (op L)).obj M)
          (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K) M
          (((derivedSheafHom Rc).map (derivedSheafHomCounit Rc K L).op).app M) := by
  rw [← hcmp, ← derivedSheafHomCounit_whiskerRight_eq' Rc _ K M,
    ← derivedSheafHomCounit_whiskerRight_eq' Rc _ _ _ D, comp_whiskerRight, Category.assoc,
    hA9, ← Category.assoc, associator_naturality_left, Category.assoc, ← hD,
    derivedSheafHomTensorEquiv_comp_left]
  rfl

/-- Under the hypotheses `hD`, `hcmp` and `hA9` of
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv_derivedSheafHomComposition_of_laws`, the
composition morphism satisfies
`cmp_{K,L,M} ▷ K ≫ ε_{K,M} = (α_ H G K).hom ≫ (H ◁ ε_{K,L}) ≫ ε_{L,M}`. -/
theorem derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_laws
    (K L M : DerivedCategory (StructureSheafModules Rc))
    (cur : ((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
          (((derivedSheafHom Rc).obj (op K)).obj M) ⟶
        ((derivedSheafHom Rc).obj
          (op (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K))).obj M)
    (D : ((derivedSheafHom Rc).obj (op L)).obj M ⟶
        ((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
          (((derivedSheafHom Rc).obj (op K)).obj M))
    (hD : D ≫ cur = ((derivedSheafHom Rc).map (derivedSheafHomCounit Rc K L).op).app M)
    (hcmp : derivedSheafHomTensorEquiv Rc (((derivedSheafHom Rc).obj (op L)).obj M)
          (((derivedSheafHom Rc).obj (op K)).obj L)
          (((derivedSheafHom Rc).obj (op K)).obj M) D =
        derivedSheafHomComposition Rc K L M)
    (hA9 : derivedSheafHomCounit Rc (((derivedSheafHom Rc).obj (op K)).obj L)
            (((derivedSheafHom Rc).obj (op K)).obj M) ▷ K ≫
          derivedSheafHomCounit Rc K M =
        (α_ (((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
              (((derivedSheafHom Rc).obj (op K)).obj M))
            (((derivedSheafHom Rc).obj (op K)).obj L) K).hom ≫
          derivedSheafHomTensorEquiv Rc
            (((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
              (((derivedSheafHom Rc).obj (op K)).obj M))
            (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K) M cur) :
    derivedSheafHomComposition Rc K L M ▷ K ≫ derivedSheafHomCounit Rc K M =
      (α_ (((derivedSheafHom Rc).obj (op L)).obj M)
          (((derivedSheafHom Rc).obj (op K)).obj L) K).hom ≫
        (((derivedSheafHom Rc).obj (op L)).obj M ◁ derivedSheafHomCounit Rc K L) ≫
          derivedSheafHomCounit Rc L M :=
  derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_transpose Rc K L M
    (derivedSheafHomTensorEquiv_derivedSheafHomComposition_of_laws Rc K L M cur D hD hcmp hA9)

/-- For an isomorphism `cur : E ≅ RSheafHom(G ⊗ K, M)`, if the composition morphism is
`Φ_{H,G,E'}(RSheafHom(ε_{K,L}, M) ≫ cur⁻¹)` (`hcmp`) and the coherence `hA9` holds for
`cur.hom`, then `cmp_{K,L,M} ▷ K ≫ ε_{K,M} = (α_ H G K).hom ≫ (H ◁ ε_{K,L}) ≫ ε_{L,M}`. -/
theorem derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_curryIso
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
    (hA9 : derivedSheafHomCounit Rc (((derivedSheafHom Rc).obj (op K)).obj L)
            (((derivedSheafHom Rc).obj (op K)).obj M) ▷ K ≫
          derivedSheafHomCounit Rc K M =
        (α_ (((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
              (((derivedSheafHom Rc).obj (op K)).obj M))
            (((derivedSheafHom Rc).obj (op K)).obj L) K).hom ≫
          derivedSheafHomTensorEquiv Rc
            (((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
              (((derivedSheafHom Rc).obj (op K)).obj M))
            (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K) M
            cur.hom) :
    derivedSheafHomComposition Rc K L M ▷ K ≫ derivedSheafHomCounit Rc K M =
      (α_ (((derivedSheafHom Rc).obj (op L)).obj M)
          (((derivedSheafHom Rc).obj (op K)).obj L) K).hom ≫
        (((derivedSheafHom Rc).obj (op L)).obj M ◁ derivedSheafHomCounit Rc K L) ≫
          derivedSheafHomCounit Rc L M :=
  derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_laws Rc K L M cur.hom _
    (by rw [Category.assoc, cur.inv_hom_id, Category.comp_id]) hcmp hA9

end Monoidal

end Stacks.SheafOfModules

end
