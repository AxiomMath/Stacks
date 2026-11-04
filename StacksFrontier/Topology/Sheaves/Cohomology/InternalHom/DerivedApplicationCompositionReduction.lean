module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingInternalHomNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationCompositionLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationUnitLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedComposition
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCurryingOnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorInternalHom

/-!
# The application morphism against a whiskering, and the composition law (C) without application

Let `(X, O_X)` be a ringed space.  The application morphism of **Stacks 08J8**,
`ε_{K,M} : RSheafHom(K, M) ⊗^L_{O_X} K ⟶ M`
(`Stacks.SheafOfModules.derivedSheafHomCounit`), is the value of the bijection of Stacks 08DI at
the identity, so every composite of it with a whiskering is again a value of that bijection.
This file proves the two such identities — one for each whiskering — and uses them to remove the
application morphism from the equation the derived-duality cluster calls **(C)**:

`cmp_{K,L,M} ▷ K ≫ ε_{K,M} = (α_ H G K).hom ≫ (H ◁ ε_{K,L}) ≫ ε_{L,M}`,

where `cmp_{K,L,M}` is the composition morphism of **Stacks 0A8V**,
`H = RSheafHom(L, M)` and `G = RSheafHom(K, L)`.  (C) is the `hcomp` hypothesis of
`Stacks.SheafOfModules.derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws`
and of `Stacks.SheafOfModules.exactPairingDerivedDualOfCompositionUnitLaws` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationCompositionLaw`, which
reduce the left-dual clause of Example 0FPC to it and to the right unit law (UR).

## Main results

* `Stacks.SheafOfModules.derivedTensor_map_app_comp_derivedSheafHomCounit`: for
  `y : A ⟶ RSheafHom(K, M)`, `y ▷ K ≫ ε_{K,M}` is the value of the bijection of Stacks 08DI at
  `y`.  This is `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_eq_tensor_evaluation` at a
  ringed space, for an *arbitrary* source `A`;
  `Stacks.SheafOfModules.derivedTensor_map_app_comp_derivedSheafHomCounit` of
  `…InternalHom.DerivedApplicationUnitLaw` is its case `A = O_X`.
* `Stacks.SheafOfModules.derivedSheafHomTensorEquiv_dinaturality`: Stacks 08J8's dinaturality
  clause at a ringed space.
* `Stacks.SheafOfModules.derivedSheafHomCounit_whiskerLeft_eq`: for `v : B' ⟶ B`,
  `RSheafHom(B, M) ◁ v ≫ ε_{B,M}` is the value of the bijection at the map
  `RSheafHom(B, M) ⟶ RSheafHom(B', M)` induced by `v`.  This is the dinaturality clause at an
  identity.
* `derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_transpose`:
  **(C) follows from the single equation (C′)**, in which the application morphism does not
  occur:

  `Φ_{H ⊗ G, K, M}(cmp_{K,L,M}) = (α_ H G K).hom ≫ Φ_{H, G ⊗ K, M}(RSheafHom(ε_{K,L}, M))`,

  `Φ` being the bijection of Stacks 08DI.  So (C) asks exactly that the composition morphism of
  Stacks 0A8V be the transpose of the double contraction, and nothing about evaluation.
* Its `structureSheafMiddle` specialisation: the same at intermediate object the structure
  sheaf, written in the exact shape of the `hcomp` hypothesis of the two consumers above, so that
  (C′) there feeds them directly.

## Nothing here is tagged

Stacks 08J8's two naturality clauses are already carried, at the ringed site, by
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source` and
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_dinaturality`; the declarations below are
those clauses read at a ringed space and specialised at an identity, together with a
reformulation of (C).  (C) itself is a compatibility of Stacks 0A8V with Stacks 08J8 that
neither tag asserts — the reason `…InternalHom.DerivedApplicationCompositionLaw` and
`…InternalHom.DerivedCompositionUnit` give for carrying no attribute either.  So no declaration
below carries a `@[stacks]` attribute.

## What (C′) still owes, and why it is not plumbing

(C′) is the statement that the composition morphism of Stacks 0A8V — which this development
builds, as the source does, from the composition morphism of internal Hom *complexes* of
Stacks 0A91 — is the morphism the tensor–internal-Hom bijection of Stacks 08DI attaches to the
double contraction.  That is a comparison of two constructions, and
`…InternalHom.DerivedTensorInternalHom` states it from the other side ("that the two agree is a
statement about two constructions and is not proved here").  Four separate searches establish
that no part of it is in the library, and record what each part would need.

1. **The chain-level content of (C) is available.**
   `AlgebraicGeometry.RingedSite.compositionSection_apply` of `…InternalHom.CompositionMorphism`
   says that evaluating a composite hom-section is evaluating the two factors in turn, with no
   extra sign, and `AlgebraicGeometry.RingedSite.compositionSection_assoc` of
   `…InternalHom.CompositionAssociativity` is its triple case.  Both are unconditional.

2. **The application morphism has no chain-level model.**  What would carry (C) down to 1 is the
   identification of `ε` with the chain-level evaluation morphism
   `AlgebraicGeometry.RingedSite.cochainEvaluation` of `…InternalHom.CurryingHomEquiv`,
   conjugated by the K-flat comparison of Stacks 06YU and the K-injective model comparison of
   Stacks 0A97.  That identification is **the evaluation square of Tag 0GM7**, and
   `…InternalHom.StrictlyPerfectHomComparisonEvaluation` *reduces* it to a K-flat source
   (`AlgebraicGeometry.RingedSite.evaluationSquare_of_curryingSquare_kFlatResolution`, with the
   comparison `σ` a variable) without proving it.  Nothing else in the tree mentions
   `DerivedCategory.Q.map (cochainEvaluation …)` at all, and there is no formula for
   `cochainEvaluation` on homogeneous local sections — its only characterisations are
   `AlgebraicGeometry.RingedSite.curryHomEquiv_symm_cochainEvaluation` and
   `AlgebraicGeometry.RingedSite.curryHomEquiv_eq_tensor_evaluation`, both inside the bijection.
   So (C) is **shared with Tag 0GM7**: the square that releases one releases the other.

3. **The derived evaluation morphism of Stacks 0A97 does have a chain-level model**
   (`AlgebraicGeometry.RingedSite.derivedEvaluation_model`, at a K-flat source and K-injective
   middle and target), but it is the map
   `RSheafHom(L, M) ⊗^L_{O_X} K ⟶ RSheafHom(RSheafHom(K, L), M)` of Stacks 0A92, not `ε`, and
   nothing in the tree identifies the two.  Reading `ε` off it would need the identity section
   of `RSheafHom(L, L)`, which `…InternalHom.DerivedCompositionUnit` records as absent.

4. **There is no associativity coherence for the bijection**, at either level: nothing relates
   `derivedCurryHomEquiv X (A ⊗ B) C Z` to `derivedCurryHomEquiv X A (B ⊗ C) Z` through the
   associator and the currying isomorphism of Stacks 08J9, and there is no chain-level analogue
   for `AlgebraicGeometry.RingedSite.curryHomEquiv`.  The available coherences of Stacks 08J9 are
   its naturality in each of the three objects and its *left* unit law.  So (C′) cannot be
   transposed into a statement about `cmp` alone, and the `α_` in it cannot be moved across the
   bijection.  `…InternalHom.CompositionMapAssociativity` records the reason an associator-level
   statement is absent at chain level: the total tensor complex of this development has no
   associator, the good-trifunctor instances not being available.

## References

* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard

-- The ring sheaf of `StructureSheafModules Rc` is `structureSheaf Rc`, i.e.
-- `CategoryTheory.sheafCompose` applied to `Rc`, while the site-level clauses rewritten with
-- below are stated at `Stacks.SheafOfModules.Tensor.ringSheaf Rc`, which writes that composite
-- presheaf out.  The two are the same sheaf of rings and elaboration unfolds the gap, but `rw`
-- matches at the `instances` transparency, where neither plain `def` unfolds; both are therefore
-- made `implicit_reducible` for this file, as the files upstream of it already do for
-- `sheafCompose`.
attribute [local implicit_reducible] CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

-- The additivity of `⊗_{O_X}` in each variable and the existence of the total tensor complexes
-- are carried as instance BINDERS and not pinned to file-local constants.  They occur in the
-- types of every result below, and a consumer that has pinned its own copies — as
-- `…InternalHom.DerivedApplicationCompositionLaw` does, under the `CompositionLaw` names —
-- would then have to unify its constants with this file's, which exhausts the recursion limit
-- of a single elaboration.  That is the discipline
-- `…InternalHom.DerivedApplicationUnitLaw` records, and it applies here: with the
-- instances pinned, the specialisation of
-- `Stacks.SheafOfModules.derivedTensor_map_app_comp_derivedSheafHomCounit` to the
-- structure-sheaf case fails with `maximum recursion depth`, and with binders it is immediate.
variable [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-! ### The application morphism against each whiskering -/

/-- **Stacks 08J8, dinaturality in the internal-Hom variable, at a ringed space.**
Postcomposing `y : A ⟶ RSheafHom(B, M)` with the map induced by `v : B' ⟶ B` corresponds, under
the bijection of Stacks 08DI, to precomposing the morphism matched with `y` with `1_A ⊗ v`.

This is `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_dinaturality` read along
`Stacks.SheafOfModules.ringedSite`.  The step is a `rw` with the site-level clause rather than
an `exact` against it, for the reason given above. -/
theorem derivedSheafHomTensorEquiv_dinaturality
    {B B' : DerivedCategory (StructureSheafModules Rc)}
    (A M : DerivedCategory (StructureSheafModules Rc)) (v : B' ⟶ B)
    (y : A ⟶ ((derivedSheafHom Rc).obj (op B)).obj M) :
    ((derivedTensor Rc).obj A).map v ≫ derivedSheafHomTensorEquiv Rc A B M y =
      derivedSheafHomTensorEquiv Rc A B' M (y ≫ ((derivedSheafHom Rc).map v.op).app M) := by
  rw [derivedSheafHomTensorEquiv_eq Rc A B M, derivedSheafHomTensorEquiv_eq Rc A B' M,
    RingedSite.derivedCurryHomEquiv_dinaturality (ringedSite Rc) A M v y]

/-- **Contracting the right-hand tensor factor against the application morphism is a transpose
too.**  For `v : B' ⟶ B`,

`1_{RSheafHom(B,M)} ⊗ v ≫ ε_{B,M} = Φ_{RSheafHom(B,M), B', M}(RSheafHom(v, M))`,

where `RSheafHom(v, M) : RSheafHom(B, M) ⟶ RSheafHom(B', M)` is the map induced by `v`.  This is
`derivedSheafHomTensorEquiv_dinaturality` at `y = 𝟙`, the identity being absorbed by `congrArg`
rather than by a rewrite: `rw [Category.id_comp]` is available here but the congruence is one
step and does not re-check the goal at a transparency these composites do not survive. -/
theorem derivedSheafHomCounit_whiskerLeft_eq
    {B B' : DerivedCategory (StructureSheafModules Rc)}
    (M : DerivedCategory (StructureSheafModules Rc)) (v : B' ⟶ B) :
    ((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op B)).obj M)).map v ≫
        derivedSheafHomCounit Rc B M =
      derivedSheafHomTensorEquiv Rc (((derivedSheafHom Rc).obj (op B)).obj M) B' M
        (((derivedSheafHom Rc).map v.op).app M) :=
  (derivedSheafHomTensorEquiv_dinaturality Rc (((derivedSheafHom Rc).obj (op B)).obj M) M v
      (𝟙 (((derivedSheafHom Rc).obj (op B)).obj M))).trans
    (congrArg
      (fun t => derivedSheafHomTensorEquiv Rc (((derivedSheafHom Rc).obj (op B)).obj M) B' M t)
      (Category.id_comp (((derivedSheafHom Rc).map v.op).app M)))

/-! ### (C) without the application morphism -/

section Monoidal

attribute [local instance] derivedMonoidalStructure

/-- `Stacks.SheafOfModules.derivedTensor_map_app_comp_derivedSheafHomCounit` in the monoidal
spelling of Stacks 0FPT.  The whiskering `y ▷ K` *is* `((derivedTensor Rc).map y).app K`: the
`whiskerRight` field of `CategoryTheory.MonoidalCategory.reseatStruct` is literally that, so the
restatement is `rfl` and the `exact` below crosses nothing. -/
theorem derivedSheafHomCounit_whiskerRight_eq'
    (A K M : DerivedCategory (StructureSheafModules Rc))
    (y : A ⟶ ((derivedSheafHom Rc).obj (op K)).obj M) :
    y ▷ K ≫ derivedSheafHomCounit Rc K M = derivedSheafHomTensorEquiv Rc A K M y :=
  Stacks.SheafOfModules.derivedTensor_map_app_comp_derivedSheafHomCounit Rc A K M y

/-- `derivedSheafHomCounit_whiskerLeft_eq` in the monoidal spelling of Stacks 0FPT.

The monoidal structure is in force as a section-local instance and not as a `letI` in the
statement, and that is load-bearing rather than cosmetic: with a `letI` the identification of
`A ◁ v` with `((derivedTensor Rc).obj A).map v` — the `whiskerLeft` field of
`CategoryTheory.MonoidalCategory.reseatStruct`, hence `rfl` — **exhausts the recursion limit**,
while under the section-local instance it is free.  The right whiskering is free either way. -/
theorem derivedSheafHomCounit_whiskerLeft_eq'
    {B B' : DerivedCategory (StructureSheafModules Rc)}
    (M : DerivedCategory (StructureSheafModules Rc)) (v : B' ⟶ B) :
    ((derivedSheafHom Rc).obj (op B)).obj M ◁ v ≫ derivedSheafHomCounit Rc B M =
      derivedSheafHomTensorEquiv Rc (((derivedSheafHom Rc).obj (op B)).obj M) B' M
        (((derivedSheafHom Rc).map v.op).app M) :=
  derivedSheafHomCounit_whiskerLeft_eq Rc M v

/-- **(C) from (C′): the composition law for application holds as soon as the composition
morphism of Stacks 0A8V is the transpose of the double contraction.**

Write `H = RSheafHom(L, M)`, `G = RSheafHom(K, L)` and `Φ` for the bijection of Stacks 08DI.
The hypothesis `htr` is

`Φ_{H ⊗ G, K, M}(cmp_{K,L,M}) = (α_ H G K).hom ≫ Φ_{H, G ⊗ K, M}(RSheafHom(ε_{K,L}, M))`,

and the conclusion is (C),

`cmp_{K,L,M} ▷ K ≫ ε_{K,M} = (α_ H G K).hom ≫ (H ◁ ε_{K,L}) ≫ ε_{L,M}`,

the `hcomp` hypothesis of
`Stacks.SheafOfModules.derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws`
at `K := L`, `L := O_X`, `M := M`.  The two sides are turned into values of `Φ` by
`derivedSheafHomCounit_whiskerRight_eq'` on the left and `derivedSheafHomCounit_whiskerLeft_eq'`
on the right, so the application morphism is gone from `htr`: what (C) asks is only that `cmp`
be the transpose of the double contraction, which is the comparison of the two constructions of
derived composition that the module docstring describes. -/
theorem derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_transpose
    (K L M : DerivedCategory (StructureSheafModules Rc))
    (htr : derivedSheafHomTensorEquiv Rc
          (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op L)).obj M)).obj
            (((derivedSheafHom Rc).obj (op K)).obj L)) K M
          (derivedSheafHomComposition Rc K L M) =
        (α_ (((derivedSheafHom Rc).obj (op L)).obj M)
            (((derivedSheafHom Rc).obj (op K)).obj L) K).hom ≫
          derivedSheafHomTensorEquiv Rc (((derivedSheafHom Rc).obj (op L)).obj M)
            (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K) M
            (((derivedSheafHom Rc).map (derivedSheafHomCounit Rc K L).op).app M)) :
    derivedSheafHomComposition Rc K L M ▷ K ≫ derivedSheafHomCounit Rc K M =
      (α_ (((derivedSheafHom Rc).obj (op L)).obj M)
          (((derivedSheafHom Rc).obj (op K)).obj L) K).hom ≫
        (((derivedSheafHom Rc).obj (op L)).obj M ◁ derivedSheafHomCounit Rc K L) ≫
          derivedSheafHomCounit Rc L M :=
  (derivedSheafHomCounit_whiskerRight_eq' Rc
        (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op L)).obj M)).obj
          (((derivedSheafHom Rc).obj (op K)).obj L)) K M
        (derivedSheafHomComposition Rc K L M)).trans
    (htr.trans
      (congrArg
        (fun t => (α_ (((derivedSheafHom Rc).obj (op L)).obj M)
            (((derivedSheafHom Rc).obj (op K)).obj L) K).hom ≫ t)
        (derivedSheafHomCounit_whiskerLeft_eq' Rc M (derivedSheafHomCounit Rc K L)).symm))

/-- **(C) at intermediate object the structure sheaf, from (C′) there**, written in exactly the
shape of the `hcomp` hypothesis of
`Stacks.SheafOfModules.derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws`
and of `Stacks.SheafOfModules.exactPairingDerivedDualOfCompositionUnitLaws` of
`…InternalHom.DerivedApplicationCompositionLaw`, with the inner application instantiated at
`ε_{L,O_X}`.  So a consumer holding (C′) at the structure sheaf gets (E1), and with (UR) the
left-dual clause of Example 0FPC, by feeding this to those two.

It is the previous theorem at `K := L`, `L := O_X`, `M := M` and nothing else; it is stated
because that is the only instantiation the pairing cluster uses, and because stating it here
checks — against the consumers' own spelling, `derivedDual Rc L` for the right tensor factor —
that the fit is exact.

(E1) itself is deliberately *not* restated here.  Assembling it in one declaration
exceeds the recursion limit: the sibling file pins the additivity and total-complex instances
to file-local constants while this file carries them as binders, and a single declaration that
both crosses that boundary and respells `derivedTensorDualToSheafHom Rc L M ▷ L`,
`(α_ M (derivedDual Rc L) L).hom`, `𝟙_` and `(ρ_ M).hom` spends far more than the two
definitional crossings a declaration affords.  Applied at this shape instead, the fit costs
nothing. -/
theorem derivedSheafHomComposition_structureSheafMiddle_whiskerRight_comp_derivedSheafHomCounit_of_transpose
    (L M : DerivedCategory (StructureSheafModules Rc))
    (htr : derivedSheafHomTensorEquiv Rc
          (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj
              (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj M)).obj
            (((derivedSheafHom Rc).obj (op L)).obj
              (RingedSite.derivedStructureSheaf (ringedSite Rc)))) L M
          (derivedSheafHomComposition Rc L
            (RingedSite.derivedStructureSheaf (ringedSite Rc)) M) =
        (α_ (((derivedSheafHom Rc).obj
              (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj M)
            (((derivedSheafHom Rc).obj (op L)).obj
              (RingedSite.derivedStructureSheaf (ringedSite Rc))) L).hom ≫
          derivedSheafHomTensorEquiv Rc
            (((derivedSheafHom Rc).obj
              (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj M)
            (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op L)).obj
              (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj L) M
            (((derivedSheafHom Rc).map
              (derivedSheafHomCounit Rc L
                (RingedSite.derivedStructureSheaf (ringedSite Rc))).op).app M)) :
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
  derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_transpose Rc L
    (RingedSite.derivedStructureSheaf (ringedSite Rc)) M htr

end Monoidal

end Stacks.SheafOfModules

end
