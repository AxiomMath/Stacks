module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseCorrespondence
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange

/-!
# Change of base scheme (Stacks, Section 04X4)

Let `g : S ⟶ S'` be a morphism of a big fppf site. Section 04X4 of the Stacks project has two
pieces of running text around its labelled results 04X5, 04X6 and 04X7.

* Its introduction states the upshot: an algebraic stack over `S` can be viewed as an algebraic
  stack over `S'`. That is Construction A on objects of the 2-category of algebraic stacks,
  `AlgebraicGeometry.Stack.changeBaseAlgebraicStack`, which this file registers under the section
  tag.
* Between Definitions 04X6 and 04X7 it goes the other way. Starting from an algebraic stack `𝒳'`
  over `S'` it forms the 2-fibre product
  `𝒳'_S = (Sch/S)_fppf ×_{(Sch/S')_fppf} 𝒳'`, which is an algebraic stack over `S'` by
  Lemma 04T2, notes that it comes with a natural 1-morphism `p : 𝒳'_S ⟶ (Sch/S)_fppf`, and
  concludes that by Lemma 04X5 it corresponds canonically to an algebraic stack over `S`. This
  file builds each of those objects as the source describes them.

In the source's reading, `(Sch/S')_fppf` over `S'` is the big fppf site of `S'` with the identity
as structure functor, which is `AlgebraicGeometry.Stack.AlgebraicStacks.terminalStack`, and
`(Sch/S)_fppf` over `S'` is the big fppf site of `S` through the localization functor at the
object `S/S'` (the remark that opens the proof of Lemma 04X5), which is the stack represented by
`S/S'`, `AlgebraicGeometry.Stack.schemeStack B S' hS' (Over.mk g)`. Both 1-morphisms of the
cospan are the structure 1-morphisms to the final object, which is how the source forms the
2-fibre product over `(Sch/S')_fppf`.

## Main definitions

* `AlgebraicGeometry.Stack.changeOfBaseFibreProduct`: the 2-fibre product `𝒳'_S` as an algebraic
  stack over `S'`.
* `AlgebraicGeometry.Stack.changeOfBaseFibreProductProjection`: the natural 1-morphism
  `p : 𝒳'_S ⟶ (Sch/S)_fppf`, the projection of the 2-fibre product to its first factor.
* `AlgebraicGeometry.Stack.changeOfBaseFibreProductPair`: the pair `(𝒳'_S, p)`, an object of the
  right-hand 2-category of Lemma 04X5.
* `AlgebraicGeometry.Stack.changeOfBaseFibreProductOverBase`: the algebraic stack over `S` that the
  pair corresponds to under Lemma 04X5.

## Main results

* `AlgebraicGeometry.Stack.algebraicStackConstructionObjEquiv_changeOfBaseFibreProductOverBase`:
  the correspondence of Lemma 04X5 carries that algebraic stack over `S` back to `(𝒳'_S, p)`, so
  it is the one the pair corresponds to.
* `AlgebraicGeometry.Stack.changeOfBaseFibreProductOverBase_p`: its structure functor over `S` is
  `p`, read through the identification of `(Sch/S)_fppf` with the localization of `(Sch/S')_fppf`
  at `S/S'`.

## Implementation notes

The correspondence of Lemma 04X5 is used through its bijection on objects,
`AlgebraicGeometry.Stack.algebraicStackConstructionObjEquiv`, whose inverse is Construction B.
Nothing is assumed: the algebraicity of `𝒳'_S` is the 04TF/04T2 instance carried by
`AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare`, and the algebraicity of the
stack over `S` is the one Construction B proves from the algebraicity criterion of Lemma 04X5.

## References

* [Stacks Project, Tag 04X4](https://stacks.math.columbia.edu/tag/04X4)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

add_to_stacks 04X4 "the introduction's upshot: given a morphism S → S' of base schemes, any
  algebraic stack over S can be viewed as an algebraic stack over S' (Construction A on objects of
  the 2-category of algebraic stacks)"
  AlgebraicGeometry.Stack.changeBaseAlgebraicStack

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **The 2-fibre product `𝒳'_S = (Sch/S)_fppf ×_{(Sch/S')_fppf} 𝒳'` of Section 04X4.** For an
algebraic stack `𝒳'` over `S'`, the apex of the canonical 2-fibre product square of the cospan
formed by the structure 1-morphisms of the stack represented by `S/S'` (that is, `(Sch/S)_fppf`
over `S'`) and of `𝒳'` to the final object `(Sch/S')_fppf`. It is an object of the 2-category of
algebraic stacks over `S'`, which is the source's appeal to Lemma 04T2. -/
@[stacks 04X4 "the 2-fibre product X'_S = (Sch/S)_fppf ×_{(Sch/S')_fppf} X', which is an
  algebraic stack over S' according to Lemma 04T2"]
def changeOfBaseFibreProduct (𝒳' : AlgebraicStacks.{u, w} B S' hS') :
    AlgebraicStacks.{u, w} B S' hS' :=
  (AlgebraicStacks.twoFibreProductSquare B S' hS'
    (AlgebraicStacks.toTerminalStack B S' hS' (schemeStack.{u, w} B S' hS' (Over.mk g)))
    (AlgebraicStacks.toTerminalStack B S' hS' 𝒳')).pt

/-- **The natural 1-morphism `p : 𝒳'_S ⟶ (Sch/S)_fppf` of Section 04X4**: the projection of the
2-fibre product `AlgebraicGeometry.Stack.changeOfBaseFibreProduct` to its first factor, the
stack represented by `S/S'`. -/
@[stacks 04X4 "the natural 1-morphism p : X'_S → (Sch/S)_fppf"]
def changeOfBaseFibreProductProjection (𝒳' : AlgebraicStacks.{u, w} B S' hS') :
    changeOfBaseFibreProduct B S S' hS hS' g 𝒳' ⟶ schemeStack.{u, w} B S' hS' (Over.mk g) :=
  (AlgebraicStacks.twoFibreProductSquare B S' hS'
    (AlgebraicStacks.toTerminalStack B S' hS' (schemeStack.{u, w} B S' hS' (Over.mk g)))
    (AlgebraicStacks.toTerminalStack B S' hS' 𝒳')).fst

/-- **The pair `(𝒳'_S, p)` of Section 04X4**, as an object of the right-hand 2-category of
Lemma 04X5: an algebraic stack over `S'` with a 1-morphism to the stack represented by
`S/S'`. -/
@[stacks 04X4 "the pair (X'_S, p), an algebraic stack over S' with a 1-morphism to
  (Sch/S)_fppf, i.e. an object of the right-hand side of Lemma 04X5"]
def changeOfBaseFibreProductPair (𝒳' : AlgebraicStacks.{u, w} B S' hS') :
    AlgebraicStackPair.{u, w} B S S' hS hS' g :=
  ⟨changeOfBaseFibreProduct B S S' hS hS' g 𝒳',
    (changeOfBaseFibreProductProjection B S S' hS hS' g 𝒳').hom⟩

/-- **The algebraic stack over `S` that `(𝒳'_S, p)` corresponds to (Section 04X4).** The image of
the pair `AlgebraicGeometry.Stack.changeOfBaseFibreProductPair` under the inverse of the
bijection on objects of Lemma 04X5, that is, under Construction B. -/
@[stacks 04X4 "by Lemma 04X5 the pair (X'_S, p) corresponds in a canonical way to an algebraic
  stack over S"]
def changeOfBaseFibreProductOverBase (𝒳' : AlgebraicStacks.{u, w} B S' hS') :
    AlgebraicStacks.{u, w} B S hS :=
  (algebraicStackConstructionObjEquiv.{u, w} B S S' hS hS' g).symm
    (changeOfBaseFibreProductPair B S S' hS hS' g 𝒳')

/-- **The correspondence of Lemma 04X5 carries the algebraic stack over `S` of Section 04X4 back
to `(𝒳'_S, p)`.** Construction A applied to
`AlgebraicGeometry.Stack.changeOfBaseFibreProductOverBase` returns the 2-fibre product `𝒳'_S`
over `S'` together with its natural 1-morphism `p`. -/
@[stacks 04X4 "the algebraic stack over S corresponds to (X'_S, p) under Lemma 04X5: Construction
  A returns X'_S over S' together with p"]
theorem algebraicStackConstructionObjEquiv_changeOfBaseFibreProductOverBase
    (𝒳' : AlgebraicStacks.{u, w} B S' hS') :
    algebraicStackConstructionObjEquiv.{u, w} B S S' hS hS' g
        (changeOfBaseFibreProductOverBase B S S' hS hS' g 𝒳') =
      changeOfBaseFibreProductPair B S S' hS hS' g 𝒳' :=
  Equiv.apply_symm_apply _ _

/-- The structure functor over `S` of the algebraic stack of Section 04X4 is the natural
1-morphism `p : 𝒳'_S ⟶ (Sch/S)_fppf`, read through the identification of the big fppf site of `S`
with the localization of the big fppf site of `S'` at `S/S'`. -/
@[simp, stacks 04X4 "the structure functor of that algebraic stack over S is p"]
lemma changeOfBaseFibreProductOverBase_p (𝒳' : AlgebraicStacks.{u, w} B S' hS') :
    (changeOfBaseFibreProductOverBase B S S' hS hS' g 𝒳').val.val.p =
      (changeOfBaseFibreProductProjection B S S' hS hS' g 𝒳').hom.hom.toFunctor ⋙
        (Over.iteratedSliceEquiv (Over.mk g)).functor :=
  rfl

end AlgebraicGeometry.Stack

end
