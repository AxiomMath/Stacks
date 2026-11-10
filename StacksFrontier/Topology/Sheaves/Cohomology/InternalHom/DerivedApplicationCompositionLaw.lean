module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedComposition
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectCoevaluation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DualityDescentDiagrams

/-!
# The composition law and the right unit law for application, and (E1)

Let `(X, O_X)` be a ringed space.  Write `app = derivedSheafHomCounit` for the application
morphism of Stacks 08J8 and `ε` for the evaluation of the derived dual.  This file derives the
equation

`derivedTensorDualToSheafHom Rc L M ▷ L ≫ app = (α_ M L^∨ L).hom ≫ (M ◁ ε) ≫ (ρ_ M).hom`, (E1)

for arbitrary objects, from two equations about the composition morphism of Stacks 0A8V and the
application morphism:

* **(C)**, the compatibility of composition with application, at intermediate object the
  structure sheaf: `hcomp` below; it holds for all objects, by
  `Stacks.SheafOfModules.compositionApplicationLaw`;
* **(UR)**, the right unit law for application at a structure-sheaf source: `hunit` below; it is
  `Stacks.SheafOfModules.derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit`.

The derivation is formal: `derivedTensorDualToSheafHom` **is** the composition morphism of
Stacks 0A8V at intermediate object the structure sheaf, whiskered with the identification
`M ≅ RSheafHom(O_X, M)`, by `rfl`, and the rest is `comp_whiskerRight`, the naturality of the
associator in its left variable and the interchange law.

## Main results

* `Stacks.SheafOfModules.derivedTensorDualToSheafHom_eq_whiskerRight_composition`: the canonical
  map of Stacks 08I1 is `(M ≅ RSheafHom(O_X, M))⁻¹ ▷ K^∨` followed by the composition morphism of
  Stacks 0A8V at intermediate object the structure sheaf.  `rfl`.
* `derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws`:
  (E1), for arbitrary `L` and `M`, from (C) and (UR).  The inner application is carried as a
  variable `ev`, so the statement serves both spellings of it.
* `Stacks.SheafOfModules.exactPairingDerivedDualOfCompositionUnitLaws`: for a perfect `K`,
  `(η, ε)` is an exact pairing as soon as (C) at intermediate object the structure sheaf and (UR)
  hold.

## Implementation notes

The inner leg of (C) at intermediate object the structure sheaf is the application morphism at
target the structure sheaf, `derivedSheafHomCounit Rc L O_X`, which is the evaluation
`Stacks.SheafOfModules.derivedDualEvaluation Rc L` of the derived dual
(`Stacks.SheafOfModules.derivedSheafHomCounit_structureSheaf_eq_derivedDualEvaluation`).  `rfl`
for that identification reaches the maximum recursion depth, so the inner application is a
variable `ev` of the statements below.

## References

* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose Tensor.ringSheaf

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-! ### The paste, over an arbitrary monoidal category -/

/-- **A composition law and a right unit law paste into a contraction law.** Over an arbitrary
monoidal category: if a morphism `cmp : H ⊗ D ⟶ P` satisfies the composition law `hC` against
`appP`, `ev` and `appU`, and `v : M ⟶ H` satisfies the right unit law `hUR` against `appU`, then
`v ▷ D ≫ cmp` contracts against `ev`.

Stated with every object and morphism a variable, and applied by `exact` below: the derived-level
goal it is applied to mentions the source of the derived internal Hom at two definitionally equal
spellings, across which no rewriting tactic fires, and one `exact` pays that crossing once.  The
three moves are `CategoryTheory.MonoidalCategory.comp_whiskerRight`, the naturality of the
associator in its left variable, and the interchange law; no braiding and no coherence diagram
is used. -/
private alias paste_composition_unit := Stacks.Cohomology.DualityDescent.paste_composition_unit

/-! ### The canonical map of Stacks 08I1 as a whiskered composition -/

/-- **The canonical map of Stacks 08I1 is a whiskered composition morphism**, in the monoidal
spelling: `Φ_{L,M} : M ⊗^L_{O_X} L^∨ ⟶ RSheafHom(L, M)` is the identification
`M ≅ RSheafHom(O_X, M)` run backwards and whiskered with `L^∨`, followed by the composition
morphism of Stacks 0A8V at intermediate object the structure sheaf.

This is `Stacks.SheafOfModules.derivedTensorDualToSheafHom_eq_composition` with the induced map
on the derived tensor product written as a right whiskering, which it is on the nose: the
`whiskerRight` field of `CategoryTheory.MonoidalCategory.reseatStruct` is literally
`(T.map f).app Y`.  That theorem's statement is therefore this one, and is given as the proof; a
bare `rfl` takes a path through `AlgebraicGeometry.RingedSite.sheafHomComplex`, which is
`no_expose` and so cannot be unfolded here.

The right whiskering is written as `MonoidalCategoryStruct.whiskerRight` with its category
named, rather than with the `▷` notation.  The morphism whiskered is the inverse of
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso`, stated over
`SheafOfModules (Tensor.ringSheaf (ringedSite Rc).O)`; `▷` reads its category off that morphism,
whereas the monoidal structure of Stacks 0FPT is seated on the `StructureSheafModules Rc`
spelling of the same category, so instance search went looking for a `MonoidalCategoryStruct` on
a spelling that carries none.  Naming the category makes the whiskering elaborate where the
monoidal structure is. -/
theorem derivedTensorDualToSheafHom_eq_whiskerRight_composition
    (L M : DerivedCategory (StructureSheafModules Rc)) :
    (letI := derivedMonoidalStructure Rc
    derivedTensorDualToSheafHom Rc L M =
      MonoidalCategoryStruct.whiskerRight (C := DerivedCategory (StructureSheafModules Rc))
            (RingedSite.derivedStructureSheafHomIso (ringedSite Rc) M).inv
            (derivedDual Rc L) ≫
        derivedSheafHomComposition Rc L
          (RingedSite.derivedStructureSheaf (ringedSite Rc)) M) :=
  derivedTensorDualToSheafHom_eq_composition Rc L M

/-! ### (E1) -/

/-- **(E1), for arbitrary `L` and `M`, from the composition law (C) and the right unit law
(UR).** The canonical map of Stacks 08I1 followed by the application morphism of Stacks 08J8 is
the contraction against `ev`:

`Φ_{L,M} ▷ L ≫ app = (α_ M L^∨ L).hom ≫ (M ◁ ev) ≫ (ρ_ M).hom`.

The hypotheses are exactly the two equations recorded as owed in
`…InternalHom.PerfectCoevaluation`:

* `hcomp` is **(C)** — the compatibility of the composition morphism of Stacks 0A8V with the
  application morphism of Stacks 08J8 — at intermediate object the structure sheaf, with the
  inner application written as `ev`;
* `hunit` is **(UR)** — the right unit law for application at a structure-sheaf source.

The inner application is carried as the variable `ev` rather than written out, for the reason
the module docstring gives: its two spellings, `derivedSheafHomCounit Rc L O_X` and the
evaluation `derivedDualEvaluation Rc L` of Tag 0FPU, are the same term and the elaborator
cannot cross between them.  At `ev := derivedDualEvaluation Rc L` the conclusion is the `happ`
hypothesis of `Stacks.SheafOfModules.exactPairingDerivedDualOfApplicationLaw`, which is
Example 0FPC's residual; at `ev := derivedSheafHomCounit Rc L O_X` it is (E1) in the spelling
that file displays.

The source of `ev` is written as `MonoidalCategoryStruct.tensorObj` with its category named,
rather than with the `⊗` notation, for the reason
`derivedTensorDualToSheafHom_eq_whiskerRight_composition` gives about `▷`:
`Stacks.SheafOfModules.derivedDual` is stated over
`SheafOfModules (Tensor.ringSheaf Rc)`, so `⊗` reads its category off that spelling, whereas the
monoidal structure of Stacks 0FPT is seated on `StructureSheafModules Rc`.

Nothing is tagged: (C) and (UR) are compatibilities of published identifications that no tag
asserts, and they are not proved here. -/
theorem derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws
    (L M : DerivedCategory (StructureSheafModules Rc))
    (ev : letI := derivedMonoidalStructure Rc
      MonoidalCategoryStruct.tensorObj (C := DerivedCategory (StructureSheafModules Rc))
            (derivedDual Rc L) L ⟶
        𝟙_ (DerivedCategory (StructureSheafModules Rc)))
    (hcomp : letI := derivedMonoidalStructure Rc
      derivedSheafHomComposition Rc L
            (RingedSite.derivedStructureSheaf (ringedSite Rc)) M ▷ L ≫
          derivedSheafHomCounit Rc L M =
        (α_ (((derivedSheafHom Rc).obj
              (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj M)
            (derivedDual Rc L) L).hom ≫
          (((derivedSheafHom Rc).obj
              (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj M ◁ ev) ≫
            derivedSheafHomCounit Rc
              (RingedSite.derivedStructureSheaf (ringedSite Rc)) M)
    (hunit : letI := derivedMonoidalStructure Rc
      MonoidalCategoryStruct.whiskerRight (C := DerivedCategory (StructureSheafModules Rc))
              (RingedSite.derivedStructureSheafHomIso (ringedSite Rc) M).inv
              (𝟙_ (DerivedCategory (StructureSheafModules Rc))) ≫
          derivedSheafHomCounit Rc
            (RingedSite.derivedStructureSheaf (ringedSite Rc)) M = (ρ_ M).hom) :
    letI := derivedMonoidalStructure Rc
    derivedTensorDualToSheafHom Rc L M ▷ L ≫ derivedSheafHomCounit Rc L M =
      (α_ M (derivedDual Rc L) L).hom ≫ (M ◁ ev) ≫ (ρ_ M).hom := by
  let := derivedMonoidalStructure Rc
  rw [derivedTensorDualToSheafHom_eq_whiskerRight_composition Rc L M]
  exact paste_composition_unit _ _ _ _ _ hcomp hunit

/-! ### The left-dual clause of Example 0FPC -/

/-- **The left dual of a perfect object, from (C) and (UR).** For a perfect object `K` of
`D(O_X)` the pair `(η, ε) = (derivedDualCoevaluation, derivedDualEvaluation)` is an exact
pairing — `K^∨ = RSheafHom(K, O_X)` is a left dual of `K` in the sense of Categories,
Definition 0FFP — as soon as the composition law (C) at intermediate object the structure sheaf
and the right unit law (UR) hold.  This is
`Stacks.SheafOfModules.exactPairingDerivedDualOfApplicationLaw` with its hypothesis (E1) supplied
by `derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws` at `L = M = K`
and `ev = ε`. -/
@[instance_reducible]
def exactPairingDerivedDualOfCompositionUnitLaws
    (K : DerivedCategory (StructureSheafModules Rc)) (hK : (ringedSite Rc).IsPerfect K)
    (hcomp : letI := derivedMonoidalStructure Rc
      derivedSheafHomComposition Rc K
            (RingedSite.derivedStructureSheaf (ringedSite Rc)) K ▷ K ≫
          derivedSheafHomCounit Rc K K =
        (α_ (((derivedSheafHom Rc).obj
              (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj K)
            (derivedDual Rc K) K).hom ≫
          (((derivedSheafHom Rc).obj
              (op (RingedSite.derivedStructureSheaf (ringedSite Rc)))).obj K ◁
            derivedDualEvaluation Rc K) ≫
            derivedSheafHomCounit Rc
              (RingedSite.derivedStructureSheaf (ringedSite Rc)) K)
    (hunit : letI := derivedMonoidalStructure Rc
      MonoidalCategoryStruct.whiskerRight (C := DerivedCategory (StructureSheafModules Rc))
              (RingedSite.derivedStructureSheafHomIso (ringedSite Rc) K).inv
              (𝟙_ (DerivedCategory (StructureSheafModules Rc))) ≫
          derivedSheafHomCounit Rc
            (RingedSite.derivedStructureSheaf (ringedSite Rc)) K = (ρ_ K).hom) :
    letI := derivedMonoidalStructure Rc
    ExactPairing K (derivedDual Rc K) :=
  exactPairingDerivedDualOfApplicationLaw Rc K hK
    (derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws Rc K K
      (derivedDualEvaluation Rc K) hcomp hunit)

end Stacks.SheafOfModules

end
