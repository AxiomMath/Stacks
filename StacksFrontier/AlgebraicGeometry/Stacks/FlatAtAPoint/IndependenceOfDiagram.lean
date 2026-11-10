module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.AtAPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FlatLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.CompatibleEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
import all StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAtAPoint.PointedFlatDiagram
import all StacksFrontier.AlgebraicGeometry.Stacks.FlatAtAPoint.PointedFlatDiagram

/-!
# Independence of the diagram in flatness at a point (Stacks 0CIC)

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlatAt_of_forall_isFlatAt`: one implication of
  **Stacks 0CIC** — the universal condition implies the existential one.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_isFlatAt_iff_forall_isFlatAt`: **Stacks 0CIC**,
  the equivalence of the existential and the universal condition.

## Implementation notes

The hard implication is an iterated-2-fibre-product chase over the canonical squares of
**Stacks 04T2**, cut into named private pieces that are elaborated one at a time, and turned into
a statement about morphisms of algebraic spaces through **Stacks 04SW** and **Stacks 04XH**.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {B S hS}

/-! ### The 2-fibre products of the chase -/

section Chase

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {x : points B S hS 𝒳}

/-- The algebraic space in the top left corner of a diagram, as an algebraic stack over `S`. -/
private abbrev PointedFlatDiagram.sourceStack (d : PointedFlatDiagram B S hS f x) :
    Stack.AlgebraicStacks.{u, w} B S hS :=
  Stack.algebraicSpaceStack.{u, w} B S hS d.U d.algebraicU

/-- The algebraic space in the top right corner of a diagram, as an algebraic stack over `S`. -/
private abbrev PointedFlatDiagram.targetStack (d : PointedFlatDiagram B S hS f x) :
    Stack.AlgebraicStacks.{u, w} B S hS :=
  Stack.algebraicSpaceStack.{u, w} B S hS d.V d.algebraicV

/-- The left vertical 1-morphism of a diagram, in the 2-category of algebraic stacks. -/
private abbrev PointedFlatDiagram.aStack (d : PointedFlatDiagram B S hS f x) :
    d.sourceStack ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom d.a

/-- The right vertical 1-morphism of a diagram, in the 2-category of algebraic stacks. -/
private abbrev PointedFlatDiagram.bStack (d : PointedFlatDiagram B S hS f x) :
    d.targetStack ⟶ 𝒴 :=
  Bicategory.InducedBicategory.mkHom d.b

/-- The top horizontal 1-morphism of a diagram, in the 2-category of algebraic stacks. -/
private abbrev PointedFlatDiagram.hStack (d : PointedFlatDiagram B S hS f x) :
    d.sourceStack ⟶ d.targetStack :=
  Bicategory.InducedBicategory.mkHom (Stack.associatedMap B S hS d.h).1

/-- The filler of a diagram, in the 2-category of algebraic stacks. -/
private def PointedFlatDiagram.isoStack (d : PointedFlatDiagram B S hS f x) :
    d.hStack ≫ d.bStack ≅ d.aStack ≫ f :=
  Bicategory.InducedBicategory.isoMk d.iso

/-- The right vertical 1-morphism of a diagram is flat. -/
private theorem PointedFlatDiagram.isFlat_bStack (d : PointedFlatDiagram B S hS f x) :
    IsFlat B S hS d.bStack :=
  (isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS d.bStack).2 d.flatB

/-- The left vertical 1-morphism of a diagram is flat. -/
private theorem PointedFlatDiagram.isFlat_aStack (d : PointedFlatDiagram B S hS f x) :
    IsFlat B S hS d.aStack :=
  (isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS d.aStack).2 d.source_flat

/-- The left vertical 1-morphism of a diagram sends the marked point to the point `x`. -/
private theorem PointedFlatDiagram.pointsMap_aStack (d : PointedFlatDiagram B S hS f x) :
    pointsMap B S hS d.aStack (Stack.spacePointMap B S hS d.U (Stack.fibredCategory B S hS d.U)
      (BasedFunctor.id (Stack.fibredCategory B S hS d.U).val) d.u) = x :=
  (congrFun (Stack.spacePointMap_eq_pointsMap_comp B S hS d.U 𝒳.val d.a.hom) d.u).symm.trans
    d.liesOver

/-- The top horizontal 1-morphism of a diagram is representable by algebraic spaces. -/
private theorem PointedFlatDiagram.isRepresentableByAlgebraicSpaces_hStack
    (d : PointedFlatDiagram B S hS f x) :
    Stack.IsRepresentableByAlgebraicSpaces B S hS d.hStack.hom.hom :=
  Stack.isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
    d.hStack.hom
    (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS d.U d.algebraicU)
    (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS d.V d.algebraicV)

/-- The canonical 2-fibre product `V ×_𝒴 𝒳` of the right vertical 1-morphism of a diagram
against `f`. -/
private def PointedFlatDiagram.cospanSquare (d : PointedFlatDiagram B S hS f x) :
    Bicategory.TwoCommSq d.bStack f :=
  Stack.twoFibreProductSquareAlgebraicStacks B S hS d.bStack f

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.PointedFlatDiagram.cospanSquare` is a 2-fibre
product. -/
private noncomputable def PointedFlatDiagram.isTwoFibreProduct_cospanSquare
    (d : PointedFlatDiagram B S hS f x) :
    Bicategory.IsTwoFibreProduct d.cospanSquare :=
  Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS d.bStack f

/-- The square underlying `AlgebraicGeometry.Stack.AlgebraicStacks.PointedFlatDiagram.cospanSquare`
is a 2-fibre product of categories fibred in groupoids. -/
private noncomputable def PointedFlatDiagram.isTwoFibreProduct_cospanSquare_underlying
    (d : PointedFlatDiagram B S hS f x) :
    Bicategory.IsTwoFibreProduct d.cospanSquare.underlying :=
  Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS d.cospanSquare
    d.isTwoFibreProduct_cospanSquare

/-- The comparison 1-morphism from a diagram to the 2-fibre product
`AlgebraicGeometry.Stack.AlgebraicStacks.PointedFlatDiagram.cospanSquare`. -/
private noncomputable def PointedFlatDiagram.comparison (d : PointedFlatDiagram B S hS f x) :
    Bicategory.TwoCommSq.PreHom (Stack.diagramCone B S hS f.hom d.a d.b d.h d.iso)
      d.cospanSquare.underlying :=
  Bicategory.twoFibreProductPreHom d.isTwoFibreProduct_cospanSquare_underlying _

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.PointedFlatDiagram.comparison`, in the 2-category of
algebraic stacks. -/
private noncomputable abbrev PointedFlatDiagram.comparisonStack
    (d : PointedFlatDiagram B S hS f x) :
    d.sourceStack ⟶ d.cospanSquare.pt :=
  Bicategory.InducedBicategory.mkHom d.comparison.hom

/-- The comparison 1-morphism of a diagram is flat, by hypothesis. -/
private theorem PointedFlatDiagram.isFlat_comparisonStack
    (d : PointedFlatDiagram B S hS f x) :
    IsFlat B S hS d.comparisonStack :=
  d.flatComparison d.cospanSquare.underlying d.isTwoFibreProduct_cospanSquare_underlying
    d.comparison

variable (d e : PointedFlatDiagram B S hS f x)

/-- The canonical 2-fibre product `𝒩 = U ×_𝒳 (V' ×_𝒴 𝒳)` of the left vertical 1-morphism of `d`
against the projection of the 2-fibre product attached to `e`. -/
private def midSquare : Bicategory.TwoCommSq d.aStack e.cospanSquare.snd :=
  Stack.twoFibreProductSquareAlgebraicStacks B S hS d.aStack e.cospanSquare.snd

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.midSquare` is a 2-fibre product. -/
private noncomputable def isTwoFibreProduct_midSquare :
    Bicategory.IsTwoFibreProduct (midSquare d e) :=
  Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS d.aStack e.cospanSquare.snd

/-- The canonical 2-fibre product `𝒭 = U' ×_{V' ×_𝒴 𝒳} 𝒩` of the comparison 1-morphism of `e`
against the projection of `AlgebraicGeometry.Stack.AlgebraicStacks.midSquare`. -/
private noncomputable def refineSquare :
    Bicategory.TwoCommSq e.comparisonStack (midSquare d e).snd :=
  Stack.twoFibreProductSquareAlgebraicStacks B S hS e.comparisonStack (midSquare d e).snd

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.refineSquare` is a 2-fibre product. -/
private noncomputable def isTwoFibreProduct_refineSquare :
    Bicategory.IsTwoFibreProduct (refineSquare d e) :=
  Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS e.comparisonStack
    (midSquare d e).snd

/-- The canonical 2-fibre product `𝒯 = V' ×_𝒴 V` of the two right vertical 1-morphisms. -/
private def targetSquare : Bicategory.TwoCommSq e.bStack d.bStack :=
  Stack.twoFibreProductSquareAlgebraicStacks B S hS e.bStack d.bStack

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.targetSquare` is a 2-fibre product. -/
private noncomputable def isTwoFibreProduct_targetSquare :
    Bicategory.IsTwoFibreProduct (targetSquare d e) :=
  Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS e.bStack d.bStack

/-- The canonical 2-fibre product `𝒵 = (V' ×_𝒴 V) ×_V U` of the projection of
`AlgebraicGeometry.Stack.AlgebraicStacks.targetSquare` against the top horizontal 1-morphism
of `d`. -/
private def sliceSquare : Bicategory.TwoCommSq (targetSquare d e).snd d.hStack :=
  Stack.twoFibreProductSquareAlgebraicStacks B S hS (targetSquare d e).snd d.hStack

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.sliceSquare` is a 2-fibre product. -/
private noncomputable def isTwoFibreProduct_sliceSquare :
    Bicategory.IsTwoFibreProduct (sliceSquare d e) :=
  Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (targetSquare d e).snd
    d.hStack

/-- `𝒩`, read as a 2-fibre product of the cospan `(b', a ≫ f)` by pasting. -/
private def pastedMid : Bicategory.TwoCommSq e.bStack (d.aStack ≫ f) :=
  e.cospanSquare.pasteSnd (midSquare d e).swap

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.pastedMid` is a 2-fibre product. -/
private noncomputable def isTwoFibreProduct_pastedMid :
    Bicategory.IsTwoFibreProduct (pastedMid d e) :=
  Bicategory.isTwoFibreProduct_pasteSnd e.cospanSquare e.isTwoFibreProduct_cospanSquare
    (midSquare d e).swap (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_midSquare d e))

/-- `𝒵`, read as a 2-fibre product of the cospan `(b', a ≫ f)` by pasting and reindexing along
the filler of `d`. -/
private def pastedSlice : Bicategory.TwoCommSq e.bStack (d.aStack ≫ f) :=
  ((targetSquare d e).pasteSnd (sliceSquare d e)).reindexSnd d.isoStack

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.pastedSlice` is a 2-fibre product. -/
private noncomputable def isTwoFibreProduct_pastedSlice :
    Bicategory.IsTwoFibreProduct (pastedSlice d e) :=
  Bicategory.isTwoFibreProduct_reindexSnd d.isoStack
    (Bicategory.isTwoFibreProduct_pasteSnd (targetSquare d e) (isTwoFibreProduct_targetSquare d e)
      (sliceSquare d e) (isTwoFibreProduct_sliceSquare d e))

/-- The comparison 1-morphism `𝒩 ⟶ 𝒵` between the two readings of the cospan
`(b', a ≫ f)`. -/
private noncomputable def chaseComparison :
    Bicategory.TwoCommSq.PreHom (pastedMid d e) (pastedSlice d e) :=
  Bicategory.twoFibreProductPreHom (isTwoFibreProduct_pastedSlice d e) (pastedMid d e)

/-! ### Flatness of the projections of the chase -/

/-- The projection `𝒩 ⟶ V' ×_𝒴 𝒳` is flat, as a base change of the left vertical 1-morphism
of `d` (**Stacks 06PY**). -/
private theorem isFlat_midSquare_snd : IsFlat B S hS (midSquare d e).snd :=
  isFlat_baseChange B S hS d.aStack e.cospanSquare.snd (midSquare d e).swap
    (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_midSquare d e)) d.isFlat_aStack

/-- The projection `𝒭 ⟶ U'` is flat, as a base change of `𝒩 ⟶ V' ×_𝒴 𝒳`
(**Stacks 06PY**). -/
private theorem isFlat_refineSquare_fst : IsFlat B S hS (refineSquare d e).fst :=
  isFlat_baseChange B S hS (midSquare d e).snd e.comparisonStack (refineSquare d e)
    (isTwoFibreProduct_refineSquare d e) (isFlat_midSquare_snd d e)

/-- The projection `𝒭 ⟶ 𝒩` is flat, as a base change of the comparison 1-morphism of `e`
(**Stacks 06PY**). -/
private theorem isFlat_refineSquare_snd : IsFlat B S hS (refineSquare d e).snd :=
  isFlat_baseChange B S hS e.comparisonStack (midSquare d e).snd (refineSquare d e).swap
    (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_refineSquare d e))
    e.isFlat_comparisonStack

/-- The projection `V' ×_𝒴 V ⟶ V'` is flat, as a base change of the right vertical 1-morphism
of `d` (**Stacks 06PY**). -/
private theorem isFlat_targetSquare_fst : IsFlat B S hS (targetSquare d e).fst :=
  isFlat_baseChange B S hS d.bStack e.bStack (targetSquare d e)
    (isTwoFibreProduct_targetSquare d e) d.isFlat_bStack

/-- **The comparison `𝒩 ⟶ 𝒵` is flat.** It is the comparison of two 2-fibre products of one
cospan, so it is an equivalence; the identity 1-morphism of `𝒩` is flat, and
`AlgebraicGeometry.Stack.AlgebraicStacks.hasPropertyOnSomeSmoothDiagram_preHom_of_preHom`
transports that along the identity comparison. -/
private theorem isFlat_chaseComparison : IsFlat B S hS (chaseComparison d e).hom := by
  refine (isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS (chaseComparison d e).hom).2 ?_
  refine hasPropertyOnSomeSmoothDiagram_preHom_of_preHom _
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS (pastedMid d e)
      (isTwoFibreProduct_pastedMid d e))
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS (pastedSlice d e)
      (isTwoFibreProduct_pastedSlice d e))
    (Bicategory.TwoCommSq.PreHom.id (pastedMid d e).underlying)
    (chaseComparison d e).underlying ?_
  exact (isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS (𝟙 (pastedMid d e).pt)).1
    (isFlat_id B S hS (pastedMid d e).pt)

/-! ### Representability of the two apexes read at space level -/

/-- **`V' ×_𝒴 V` is representable by an algebraic space** (**Stacks 0300**): the right vertical
1-morphism of `d` is representable by algebraic spaces because its source is an algebraic space
and `𝒴` has representable diagonal (**Stacks 04ZP**), and `V'` is an algebraic space. -/
private theorem isRepresentableByAlgebraicSpace_targetSquare :
    Stack.IsRepresentableByAlgebraicSpace B S hS (targetSquare d e).pt.val :=
  Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
    d.targetStack.val 𝒴.val e.targetStack.val d.bStack.hom e.bStack.hom
    (targetSquare d e).underlying
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS (targetSquare d e)
      (isTwoFibreProduct_targetSquare d e))
    (Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒴.property
      (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS d.V d.algebraicV)
      d.bStack.hom)
    (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS e.V e.algebraicV)

/-- **`(V' ×_𝒴 V) ×_V U` is representable by an algebraic space** (**Stacks 0300**): the top
horizontal 1-morphism of `d` has both source and target representable by algebraic spaces
(**Stacks 02ZZ**), and `V' ×_𝒴 V` is representable by an algebraic space. -/
private theorem isRepresentableByAlgebraicSpace_sliceSquare :
    Stack.IsRepresentableByAlgebraicSpace B S hS (sliceSquare d e).pt.val :=
  Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
    d.sourceStack.val d.targetStack.val (targetSquare d e).pt.val d.hStack.hom
    (targetSquare d e).snd.hom (sliceSquare d e).underlying
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS (sliceSquare d e)
      (isTwoFibreProduct_sliceSquare d e))
    d.isRepresentableByAlgebraicSpaces_hStack
    (isRepresentableByAlgebraicSpace_targetSquare d e)

/-- **The canonical apex of the cospan `((V' ×_𝒴 V) ⟶ V, U ⟶ V)` is representable by an
algebraic space.** This is the same statement as
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpace_sliceSquare` at the
canonical 2-fibre product of Stacks 003Q, which is what the comparison of **Stacks 04SD**
is stated against. -/
private theorem isRepresentableByAlgebraicSpace_sliceCanonical :
    Stack.IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (targetSquare d e).snd.hom d.hStack.hom).pt :=
  Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
    d.sourceStack.val d.targetStack.val (targetSquare d e).pt.val d.hStack.hom
    (targetSquare d e).snd.hom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (targetSquare d e).snd.hom d.hStack.hom)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (targetSquare d e).snd.hom d.hStack.hom)
    d.isRepresentableByAlgebraicSpaces_hStack
    (isRepresentableByAlgebraicSpace_targetSquare d e)

/-! ### The route from `𝒭` to `V'` -/

/-- **The two routes from `𝒭` to `V'` agree.** Going `𝒭 ⟶ 𝒩 ⟶ 𝒵 ⟶ V' ×_𝒴 V ⟶ V'` is
2-isomorphic to going `𝒭 ⟶ U' ⟶ V'`: the comparison `𝒩 ⟶ 𝒵` identifies the first projection
of `𝒩` with the composite through `𝒵`, the filler of `𝒭` identifies `𝒭 ⟶ 𝒩 ⟶ V' ×_𝒴 𝒳` with
`𝒭 ⟶ U' ⟶ V' ×_𝒴 𝒳`, and the comparison 1-morphism of `e` identifies `U' ⟶ V' ×_𝒴 𝒳 ⟶ V'`
with the top horizontal 1-morphism of `e`.

Every reassociation is written out: the hom-categories here are those of an induced bicategory,
where `simp` does not see the associativity of composition of 1-morphisms. -/
private noncomputable def chaseRoute {𝒲 : Stack.AlgebraicStacks.{u, w} B S hS}
    (k : 𝒲 ⟶ (refineSquare d e).pt) :
    (k ≫ (refineSquare d e).snd ≫ (chaseComparison d e).hom) ≫
        ((sliceSquare d e).fst ≫ (targetSquare d e).fst) ≅
      (k ≫ (refineSquare d e).fst) ≫ e.hStack :=
  letI κ : (midSquare d e).snd ≫ e.cospanSquare.fst ≅
      (chaseComparison d e).hom ≫ ((sliceSquare d e).fst ≫ (targetSquare d e).fst) :=
    (chaseComparison d e).isoFst
  letI σ : e.hStack ≅ e.comparisonStack ≫ e.cospanSquare.fst :=
    Bicategory.InducedBicategory.isoMk e.comparison.isoFst
  Bicategory.associator k ((refineSquare d e).snd ≫ (chaseComparison d e).hom)
      ((sliceSquare d e).fst ≫ (targetSquare d e).fst) ≪≫
    Bicategory.whiskerLeftIso k
      (Bicategory.associator (refineSquare d e).snd (chaseComparison d e).hom
          ((sliceSquare d e).fst ≫ (targetSquare d e).fst) ≪≫
        Bicategory.whiskerLeftIso (refineSquare d e).snd κ.symm ≪≫
        (Bicategory.associator (refineSquare d e).snd (midSquare d e).snd
          e.cospanSquare.fst).symm ≪≫
        Bicategory.whiskerRightIso (refineSquare d e).iso.symm e.cospanSquare.fst ≪≫
        Bicategory.associator (refineSquare d e).fst e.comparisonStack e.cospanSquare.fst ≪≫
        Bicategory.whiskerLeftIso (refineSquare d e).fst σ.symm) ≪≫
    (Bicategory.associator k (refineSquare d e).fst e.hStack).symm

/-! ### The five morphisms of algebraic spaces the chase is run on -/

/-- The morphism of algebraic spaces induced by the composite `𝒲 ⟶ 𝒭 ⟶ 𝒩 ⟶ 𝒵` out of a chart
`𝒲` of `𝒭`, through **Stacks 04SW**. -/
private noncomputable def chartToSlice {𝒲 : Stack.AlgebraicStacks.{u, w} B S hS}
    (k : 𝒲 ⟶ (refineSquare d e).pt) (W Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eW : StacksRepresentableCFG.EquivalenceOver 𝒲.val.val.p
      (presheafOfCategories (W ⋙ typeToCat)).p)
    (eZ : StacksRepresentableCFG.EquivalenceOver (sliceSquare d e).pt.val.val.p
      (presheafOfCategories (Z ⋙ typeToCat)).p) :
    W ⟶ Z :=
  Stack.representingMap B S hS 𝒲.val (sliceSquare d e).pt.val W Z eW eZ
    (k ≫ (refineSquare d e).snd ≫ (chaseComparison d e).hom).hom

/-- The morphism of algebraic spaces induced by the projection `𝒵 ⟶ V' ×_𝒴 V`, through
**Stacks 04SW**. -/
private noncomputable def sliceToTarget (Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eZ : StacksRepresentableCFG.EquivalenceOver (sliceSquare d e).pt.val.val.p
      (presheafOfCategories (Z ⋙ typeToCat)).p)
    (eT : StacksRepresentableCFG.EquivalenceOver (targetSquare d e).pt.val.val.p
      (presheafOfCategories (T ⋙ typeToCat)).p) :
    Z ⟶ T :=
  Stack.representingMap B S hS (sliceSquare d e).pt.val (targetSquare d e).pt.val Z T eZ eT
    (sliceSquare d e).fst.hom

/-- The morphism of algebraic spaces induced by the projection `𝒵 ⟶ U`, through
**Stacks 04SW**. -/
private noncomputable def sliceToSource (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eZ : StacksRepresentableCFG.EquivalenceOver (sliceSquare d e).pt.val.val.p
      (presheafOfCategories (Z ⋙ typeToCat)).p) :
    Z ⟶ d.U :=
  Stack.representingMap B S hS (sliceSquare d e).pt.val d.sourceStack.val Z d.U eZ
    (StacksRepresentableCFG.EquivalenceOver.refl _) (sliceSquare d e).snd.hom

/-- The morphism of algebraic spaces induced by the projection `V' ×_𝒴 V ⟶ V'`, through
**Stacks 04SW**. -/
private noncomputable def targetToTopRight (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eT : StacksRepresentableCFG.EquivalenceOver (targetSquare d e).pt.val.val.p
      (presheafOfCategories (T ⋙ typeToCat)).p) :
    T ⟶ e.V :=
  Stack.representingMap B S hS (targetSquare d e).pt.val e.targetStack.val T e.V eT
    (StacksRepresentableCFG.EquivalenceOver.refl _) (targetSquare d e).fst.hom

/-- The morphism of algebraic spaces induced by the composite `𝒲 ⟶ 𝒭 ⟶ U'` out of a chart `𝒲`
of `𝒭`, through **Stacks 04SW**. -/
private noncomputable def chartToTopLeft {𝒲 : Stack.AlgebraicStacks.{u, w} B S hS}
    (k : 𝒲 ⟶ (refineSquare d e).pt) (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eW : StacksRepresentableCFG.EquivalenceOver 𝒲.val.val.p
      (presheafOfCategories (W ⋙ typeToCat)).p) :
    W ⟶ e.U :=
  Stack.representingMap B S hS 𝒲.val e.sourceStack.val W e.U eW
    (StacksRepresentableCFG.EquivalenceOver.refl _) (k ≫ (refineSquare d e).fst).hom

/-- **The route of `AlgebraicGeometry.Stack.AlgebraicStacks.chaseRoute`, read on representing
presheaves.** The morphism of algebraic spaces induced by the composite
`𝒲 ⟶ 𝒵 ⟶ V' ×_𝒴 V ⟶ V'` is the one induced by `𝒲 ⟶ U'` followed by the top horizontal
morphism of `e`; this is Stacks 04SW applied to the 2-isomorphism of
`AlgebraicGeometry.Stack.AlgebraicStacks.chaseRoute`, together with its functoriality. -/
private theorem chartToSlice_comp
    {𝒲 : Stack.AlgebraicStacks.{u, w} B S hS} (k : 𝒲 ⟶ (refineSquare d e).pt)
    (W Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eW : StacksRepresentableCFG.EquivalenceOver 𝒲.val.val.p
      (presheafOfCategories (W ⋙ typeToCat)).p)
    (eZ : StacksRepresentableCFG.EquivalenceOver (sliceSquare d e).pt.val.val.p
      (presheafOfCategories (Z ⋙ typeToCat)).p)
    (eT : StacksRepresentableCFG.EquivalenceOver (targetSquare d e).pt.val.val.p
      (presheafOfCategories (T ⋙ typeToCat)).p) :
    chartToSlice d e k W Z eW eZ ≫
        (sliceToTarget d e Z T eZ eT ≫ targetToTopRight d e T eT) =
      chartToTopLeft d e k W eW ≫ e.h := by
  have h1 := Stack.representingMap_comp (𝒜 := 𝒲.val) (ℬ := (sliceSquare d e).pt.val)
    (𝒞 := e.targetStack.val) B S hS W Z e.V eW eZ
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (k ≫ (refineSquare d e).snd ≫ (chaseComparison d e).hom).hom
    ((sliceSquare d e).fst ≫ (targetSquare d e).fst).hom
  have h2 := Stack.representingMap_comp (𝒜 := (sliceSquare d e).pt.val)
    (ℬ := (targetSquare d e).pt.val) (𝒞 := e.targetStack.val) B S hS Z T e.V eZ eT
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (sliceSquare d e).fst.hom (targetSquare d e).fst.hom
  have h3 := Stack.representingMap_comp (𝒜 := 𝒲.val) (ℬ := e.sourceStack.val)
    (𝒞 := e.targetStack.val) B S hS W e.U e.V eW
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (k ≫ (refineSquare d e).fst).hom (Stack.associatedMap B S hS e.h).1
  have h4 := Stack.representingMap_associatedMap B S hS e.U e.V e.h
  have h5 := Stack.representingMap_congr_twoIso (𝒜 := 𝒲.val) (𝒞 := e.targetStack.val) B S hS
    W e.V eW (StacksRepresentableCFG.EquivalenceOver.refl _)
    (Bicategory.InducedBicategory.isoHom (chaseRoute d e k))
  refine Eq.trans ?_ (h3.trans (congrArg (fun t => chartToTopLeft d e k W eW ≫ t) h4))
  refine Eq.trans ?_ h5
  exact (congrArg (fun t => chartToSlice d e k W Z eW eZ ≫ t) h2).symm.trans h1.symm

/-! ### Flatness along the route -/

/-- The composite `𝒲 ⟶ 𝒭 ⟶ 𝒩 ⟶ 𝒵` is flat, so it induces a flat morphism of algebraic
spaces. -/
private theorem isFlat_chartToSlice {𝒲 : Stack.AlgebraicStacks.{u, w} B S hS}
    (k : 𝒲 ⟶ (refineSquare d e).pt) (hk : IsFlat B S hS k)
    (W Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hW : IsAlgebraicSpace B S hS W) (hZ : IsAlgebraicSpace B S hS Z)
    (eW : StacksRepresentableCFG.EquivalenceOver 𝒲.val.val.p
      (presheafOfCategories (W ⋙ typeToCat)).p)
    (eZ : StacksRepresentableCFG.EquivalenceOver (sliceSquare d e).pt.val.val.p
      (presheafOfCategories (Z ⋙ typeToCat)).p) :
    Space.IsFlat B S hS (chartToSlice d e k W Z eW eZ) :=
  Stack.isFlat_representingMap_of_isFlat (𝒳 := 𝒲) (𝒴 := (sliceSquare d e).pt) B S hS W Z hW hZ
    eW eZ (k ≫ (refineSquare d e).snd ≫ (chaseComparison d e).hom)
    (isFlat_comp B S hS k ((refineSquare d e).snd ≫ (chaseComparison d e).hom) hk
      (isFlat_comp B S hS (refineSquare d e).snd (chaseComparison d e).hom
        (isFlat_refineSquare_snd d e) (isFlat_chaseComparison d e)))

/-- The projection `V' ×_𝒴 V ⟶ V'` is flat, so it induces a flat morphism of algebraic
spaces. -/
private theorem isFlat_targetToTopRight (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hT : IsAlgebraicSpace B S hS T)
    (eT : StacksRepresentableCFG.EquivalenceOver (targetSquare d e).pt.val.val.p
      (presheafOfCategories (T ⋙ typeToCat)).p) :
    Space.IsFlat B S hS (targetToTopRight d e T eT) :=
  Stack.isFlat_representingMap_of_isFlat (𝒳 := (targetSquare d e).pt) (𝒴 := e.targetStack)
    B S hS T e.V hT e.algebraicV eT (StacksRepresentableCFG.EquivalenceOver.refl _)
    (targetSquare d e).fst (isFlat_targetSquare_fst d e)

/-- The composite `𝒲 ⟶ 𝒭 ⟶ U'` is flat, so it induces a flat morphism of algebraic spaces. -/
private theorem isFlat_chartToTopLeft {𝒲 : Stack.AlgebraicStacks.{u, w} B S hS}
    (k : 𝒲 ⟶ (refineSquare d e).pt) (hk : IsFlat B S hS k)
    (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W)
    (eW : StacksRepresentableCFG.EquivalenceOver 𝒲.val.val.p
      (presheafOfCategories (W ⋙ typeToCat)).p) :
    Space.IsFlat B S hS (chartToTopLeft d e k W eW) :=
  Stack.isFlat_representingMap_of_isFlat (𝒳 := 𝒲) (𝒴 := e.sourceStack) B S hS W e.U hW
    e.algebraicU eW (StacksRepresentableCFG.EquivalenceOver.refl _)
    (k ≫ (refineSquare d e).fst)
    (isFlat_comp B S hS k (refineSquare d e).fst hk (isFlat_refineSquare_fst d e))

/-- **The projection `𝒵 ⟶ V' ×_𝒴 V` is flat above the marked point of `d`.** Read on
representing presheaves, `𝒵 = (V' ×_𝒴 V) ×_V U` is a cartesian square of algebraic spaces
(**Stacks 04SD**) whose other projection is the base change of the top horizontal morphism of
`d`, so this is base change of flatness at a point — the structure sheaf case of
**Stacks 05VW** — at the hypothesis of `d`. -/
private theorem isFlatAt_sliceToTarget (hd : Space.IsFlatAt B S hS d.h d.u)
    (Z T C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hZ : IsAlgebraicSpace B S hS Z) (hT : IsAlgebraicSpace B S hS T)
    (eZ : StacksRepresentableCFG.EquivalenceOver (sliceSquare d e).pt.val.val.p
      (presheafOfCategories (Z ⋙ typeToCat)).p)
    (eT : StacksRepresentableCFG.EquivalenceOver (targetSquare d e).pt.val.val.p
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (eC : StacksRepresentableCFG.EquivalenceOver
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (targetSquare d e).snd.hom d.hStack.hom).pt.val.p
      (presheafOfCategories (C ⋙ typeToCat)).p)
    (z : Space.points B S hS Z)
    (hz : Space.pointsMap B S hS Z (sliceToSource d e Z eZ) z = d.u) :
    Space.IsFlatAt B S hS (sliceToTarget d e Z T eZ eT) z := by
  have hpb := Stack.isPullback_representingMap_of_isTwoFibreProduct B S hS
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS (sliceSquare d e)
      (isTwoFibreProduct_sliceSquare d e))
    T d.U d.V Z C eT (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) eZ eC
  have hm : Stack.representingMap B S hS d.sourceStack.val d.targetStack.val d.U d.V
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) d.hStack.hom = d.h :=
    Stack.representingMap_associatedMap B S hS d.U d.V d.h
  refine isFlatAt_of_isPullback_presheaf B S hS hZ d.algebraicU hT d.algebraicV
    (hm ▸ hpb.flip) z ?_
  change Space.IsFlatAt B S hS d.h (Space.pointsMap B S hS Z (sliceToSource d e Z eZ) z)
  rw [hz]
  exact hd

/-! ### The implication -/

/-- **A point of a chart is read off the 1-morphism the chart is composed with.** Let `𝒲` be an
algebraic stack over `S` represented by an algebraic space `W` and let `g : 𝒲 ⟶ A` be a
1-morphism to an algebraic space over `S`. A point of `W` is sent by the morphism of representing
presheaves of **Stacks 04SW** to the point of `A` that `g` sends its image in `|𝒲|` to; this is
naturality of the canonical map of **Stacks 04XL** in the chart, together with bijectivity of
that map for the tautological chart. -/
private theorem pointsMap_representingMap_eq {𝒲 : Stack.AlgebraicStacks.{u, w} B S hS}
    {A W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hA : IsAlgebraicSpace B S hS A)
    (eW : StacksRepresentableCFG.EquivalenceOver 𝒲.val.val.p
      (presheafOfCategories (W ⋙ typeToCat)).p)
    (g : 𝒲 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS A hA)
    (p : Space.points B S hS W) (a : Space.points B S hS A)
    (h : pointsMap B S hS g
          (Stack.spacePointMap B S hS W 𝒲.val
            (Stack.representingEquivalence B S hS W 𝒲.val eW).functor p) =
        Stack.spacePointMap B S hS A (Stack.fibredCategory B S hS A)
          (BasedFunctor.id (Stack.fibredCategory B S hS A).val) a) :
    Space.pointsMap B S hS W
        (Stack.representingMap B S hS 𝒲.val (Stack.fibredCategory B S hS A) W A eW
          (StacksRepresentableCFG.EquivalenceOver.refl _) g.hom) p = a :=
  (Stack.spacePointMap_id_bijective B S hS A).injective
    ((Stack.spacePointMap_representing_naturality B S hS W A 𝒲.val
      (Stack.fibredCategory B S hS A) eW
      (StacksRepresentableCFG.EquivalenceOver.refl _) g.hom p).trans h)

/-- **The chosen point of a chart of `𝒭` lies over the marked point of `d`.** Going
`𝒲 ⟶ 𝒭 ⟶ 𝒩 ⟶ 𝒵 ⟶ U` is 2-isomorphic to `𝒲 ⟶ 𝒭 ⟶ 𝒩 ⟶ U`, by the second compatibility of the
comparison `𝒩 ⟶ 𝒵`, and the chosen point of `𝒩` lies over the marked point of `d`. -/
private theorem pointsMap_chartToSlice_comp
    {𝒲 : Stack.AlgebraicStacks.{u, w} B S hS} (k : 𝒲 ⟶ (refineSquare d e).pt)
    (W Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eW : StacksRepresentableCFG.EquivalenceOver 𝒲.val.val.p
      (presheafOfCategories (W ⋙ typeToCat)).p)
    (eZ : StacksRepresentableCFG.EquivalenceOver (sliceSquare d e).pt.val.val.p
      (presheafOfCategories (Z ⋙ typeToCat)).p)
    (p : Space.points B S hS W) (n : points B S hS (midSquare d e).pt)
    (r : points B S hS (refineSquare d e).pt)
    (hpk : pointsMap B S hS k
      (Stack.spacePointMap B S hS W 𝒲.val
        (Stack.representingEquivalence B S hS W 𝒲.val eW).functor p) = r)
    (hr : pointsMap B S hS (refineSquare d e).snd r = n)
    (hn : pointsMap B S hS (midSquare d e).fst n =
      Stack.spacePointMap B S hS d.U (Stack.fibredCategory B S hS d.U)
        (BasedFunctor.id (Stack.fibredCategory B S hS d.U).val) d.u) :
    Space.pointsMap B S hS Z (sliceToSource d e Z eZ)
      (Space.pointsMap B S hS W (chartToSlice d e k W Z eW eZ) p) = d.u := by
  have hroute : pointsMap B S hS (k ≫ (refineSquare d e).snd ≫ (chaseComparison d e).hom)
      (Stack.spacePointMap B S hS W 𝒲.val
        (Stack.representingEquivalence B S hS W 𝒲.val eW).functor p) =
      pointsMap B S hS (chaseComparison d e).hom n :=
    (congrFun (pointsMap_comp B S hS k
      ((refineSquare d e).snd ≫ (chaseComparison d e).hom)) _).trans
      ((congrArg (pointsMap B S hS ((refineSquare d e).snd ≫ (chaseComparison d e).hom))
          hpk).trans
        ((congrFun (pointsMap_comp B S hS (refineSquare d e).snd
            (chaseComparison d e).hom) r).trans
          (congrArg (pointsMap B S hS (chaseComparison d e).hom) hr)))
  have hpoint : pointsMap B S hS
      ((k ≫ (refineSquare d e).snd ≫ (chaseComparison d e).hom) ≫ (sliceSquare d e).snd)
      (Stack.spacePointMap B S hS W 𝒲.val
        (Stack.representingEquivalence B S hS W 𝒲.val eW).functor p) =
      Stack.spacePointMap B S hS d.U (Stack.fibredCategory B S hS d.U)
        (BasedFunctor.id (Stack.fibredCategory B S hS d.U).val) d.u :=
    (congrFun (pointsMap_comp B S hS
        (k ≫ (refineSquare d e).snd ≫ (chaseComparison d e).hom)
        (sliceSquare d e).snd) _).trans
      ((congrArg (pointsMap B S hS (sliceSquare d e).snd) hroute).trans
        ((congrFun (pointsMap_comp B S hS (chaseComparison d e).hom
            (sliceSquare d e).snd) n).symm.trans
          ((congrFun (pointsMap_eq_of_hom₂ B S hS (chaseComparison d e).isoSnd.hom) n).symm.trans
            hn)))
  have hsplit := Stack.representingMap_comp (𝒜 := 𝒲.val) (ℬ := (sliceSquare d e).pt.val)
    (𝒞 := d.sourceStack.val) B S hS W Z d.U eW eZ
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (k ≫ (refineSquare d e).snd ≫ (chaseComparison d e).hom).hom (sliceSquare d e).snd.hom
  refine Eq.trans ?_ (pointsMap_representingMap_eq d.algebraicU eW
    ((k ≫ (refineSquare d e).snd ≫ (chaseComparison d e).hom) ≫ (sliceSquare d e).snd)
    p d.u hpoint)
  exact ((congrArg (fun m => Space.pointsMap B S hS W m p) hsplit).trans
    (congrFun (Space.pointsMap_comp B S hS W (chartToSlice d e k W Z eW eZ)
      (sliceToSource d e Z eZ)) p)).symm

/-- **The chosen point of a chart of `𝒭` lies over the marked point of `e`.** The projection
`𝒭 ⟶ U'` sends the chosen point of `𝒭` to the marked point of `e`. -/
private theorem pointsMap_chartToTopLeft
    {𝒲 : Stack.AlgebraicStacks.{u, w} B S hS} (k : 𝒲 ⟶ (refineSquare d e).pt)
    (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eW : StacksRepresentableCFG.EquivalenceOver 𝒲.val.val.p
      (presheafOfCategories (W ⋙ typeToCat)).p)
    (p : Space.points B S hS W) (r : points B S hS (refineSquare d e).pt)
    (hpk : pointsMap B S hS k
      (Stack.spacePointMap B S hS W 𝒲.val
        (Stack.representingEquivalence B S hS W 𝒲.val eW).functor p) = r)
    (hr : pointsMap B S hS (refineSquare d e).fst r =
      Stack.spacePointMap B S hS e.U (Stack.fibredCategory B S hS e.U)
        (BasedFunctor.id (Stack.fibredCategory B S hS e.U).val) e.u) :
    Space.pointsMap B S hS W (chartToTopLeft d e k W eW) p = e.u :=
  pointsMap_representingMap_eq e.algebraicU eW (k ≫ (refineSquare d e).fst) p e.u
    ((congrFun (pointsMap_comp B S hS k (refineSquare d e).fst) _).trans
      ((congrArg (pointsMap B S hS (refineSquare d e).fst) hpk).trans hr))

/-- **The chase, run on a chart of `𝒭` through the point above both marked points.** Flatness of
`W ⟶ Z`, flatness of `Z ⟶ T` above the marked point of `d` and flatness of `T ⟶ V'` compose to
flatness of `W ⟶ V'` at the chosen point; that composite is `W ⟶ U'` followed by the top
horizontal morphism of `e`, and `W ⟶ U'` is flat, so flat permanence at a point
(`AlgebraicGeometry.Stack.AlgebraicStacks.isFlatAt_of_comp`) gives the conclusion. -/
private theorem isFlatAt_of_chart (hd : Space.IsFlatAt B S hS d.h d.u)
    {𝒲 : Stack.AlgebraicStacks.{u, w} B S hS} (k : 𝒲 ⟶ (refineSquare d e).pt)
    (hk : IsFlat B S hS k) (W Z T C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hW : IsAlgebraicSpace B S hS W) (hZ : IsAlgebraicSpace B S hS Z)
    (hT : IsAlgebraicSpace B S hS T)
    (eW : StacksRepresentableCFG.EquivalenceOver 𝒲.val.val.p
      (presheafOfCategories (W ⋙ typeToCat)).p)
    (eZ : StacksRepresentableCFG.EquivalenceOver (sliceSquare d e).pt.val.val.p
      (presheafOfCategories (Z ⋙ typeToCat)).p)
    (eT : StacksRepresentableCFG.EquivalenceOver (targetSquare d e).pt.val.val.p
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (eC : StacksRepresentableCFG.EquivalenceOver
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (targetSquare d e).snd.hom d.hStack.hom).pt.val.p
      (presheafOfCategories (C ⋙ typeToCat)).p)
    (p : Space.points B S hS W)
    (hzU : Space.pointsMap B S hS Z (sliceToSource d e Z eZ)
      (Space.pointsMap B S hS W (chartToSlice d e k W Z eW eZ) p) = d.u)
    (hU : Space.pointsMap B S hS W (chartToTopLeft d e k W eW) p = e.u) :
    Space.IsFlatAt B S hS e.h e.u := by
  have h1 : Space.IsFlatAt B S hS
      (chartToSlice d e k W Z eW eZ ≫ sliceToTarget d e Z T eZ eT) p :=
    isFlatAt_comp B S hS hW hZ hT (chartToSlice d e k W Z eW eZ) (sliceToTarget d e Z T eZ eT) p
      (isFlatAt_of_isFlat B S hS (chartToSlice d e k W Z eW eZ) p
        (isFlat_chartToSlice d e k hk W Z hW hZ eW eZ))
      (isFlatAt_sliceToTarget d e hd Z T C hZ hT eZ eT eC _ hzU)
  have h2 : Space.IsFlatAt B S hS
      ((chartToSlice d e k W Z eW eZ ≫ sliceToTarget d e Z T eZ eT) ≫
        targetToTopRight d e T eT) p :=
    isFlatAt_comp B S hS hW hT e.algebraicV
      (chartToSlice d e k W Z eW eZ ≫ sliceToTarget d e Z T eZ eT) (targetToTopRight d e T eT) p
      h1 (isFlatAt_of_isFlat B S hS (targetToTopRight d e T eT) _
        (isFlat_targetToTopRight d e T hT eT))
  have h3 : Space.IsFlatAt B S hS (chartToTopLeft d e k W eW ≫ e.h) p :=
    (congrArg (fun m => Space.IsFlatAt B S hS m p)
      ((Category.assoc (chartToSlice d e k W Z eW eZ) (sliceToTarget d e Z T eZ eT)
        (targetToTopRight d e T eT)).trans
        (chartToSlice_comp d e k W Z T eW eZ eT))).mp h2
  exact (congrArg (Space.IsFlatAt B S hS e.h) hU).mp
    (isFlatAt_of_comp B S hS hW e.algebraicU e.algebraicV (chartToTopLeft d e k W eW) e.h p
      (isFlatAt_of_isFlat B S hS (chartToTopLeft d e k W eW) p
        (isFlat_chartToTopLeft d e k hk W hW eW)) h3)


/-- **The point of `𝒭` above both marked points.** The comparison 1-morphism of `e` sends the
marked point of `e` to a point of `𝒬 = V' ×_𝒴 𝒳` above `x`, and so does the left vertical
1-morphism of `d` with the marked point of `d`; **Stacks 04XH** applied to `𝒩 = U ×_𝒳 𝒬` and
then to `𝒭 = U' ×_𝒬 𝒩` lifts them to a point of `𝒭`. -/
private theorem exists_point_refineSquare :
    ∃ (n : points B S hS (midSquare d e).pt) (r : points B S hS (refineSquare d e).pt),
      pointsMap B S hS (midSquare d e).fst n =
          Stack.spacePointMap B S hS d.U (Stack.fibredCategory B S hS d.U)
            (BasedFunctor.id (Stack.fibredCategory B S hS d.U).val) d.u ∧
        pointsMap B S hS (refineSquare d e).snd r = n ∧
        pointsMap B S hS (refineSquare d e).fst r =
          Stack.spacePointMap B S hS e.U (Stack.fibredCategory B S hS e.U)
            (BasedFunctor.id (Stack.fibredCategory B S hS e.U).val) e.u := by
  have hcompiso : e.aStack ≅ e.comparisonStack ≫ e.cospanSquare.snd :=
    Bicategory.InducedBicategory.isoMk e.comparison.isoSnd
  have hqx : pointsMap B S hS e.cospanSquare.snd
      (pointsMap B S hS e.comparisonStack
        (Stack.spacePointMap B S hS e.U (Stack.fibredCategory B S hS e.U)
          (BasedFunctor.id (Stack.fibredCategory B S hS e.U).val) e.u)) = x :=
    (congrFun (pointsMap_comp B S hS e.comparisonStack e.cospanSquare.snd) _).symm.trans
      ((congrFun (pointsMap_eq_of_hom₂ B S hS hcompiso.hom) _).symm.trans
        e.pointsMap_aStack)
  obtain ⟨n, hn₁, hn₂⟩ := Stack.exists_point_of_isTwoFibreProduct_algebraicStacks B S hS
    (midSquare d e) (isTwoFibreProduct_midSquare d e)
    (Stack.spacePointMap B S hS d.U (Stack.fibredCategory B S hS d.U)
      (BasedFunctor.id (Stack.fibredCategory B S hS d.U).val) d.u)
    (pointsMap B S hS e.comparisonStack
      (Stack.spacePointMap B S hS e.U (Stack.fibredCategory B S hS e.U)
        (BasedFunctor.id (Stack.fibredCategory B S hS e.U).val) e.u))
    (d.pointsMap_aStack.trans hqx.symm)
  obtain ⟨r, hr₁, hr₂⟩ := Stack.exists_point_of_isTwoFibreProduct_algebraicStacks B S hS
    (refineSquare d e) (isTwoFibreProduct_refineSquare d e)
    (Stack.spacePointMap B S hS e.U (Stack.fibredCategory B S hS e.U)
      (BasedFunctor.id (Stack.fibredCategory B S hS e.U).val) e.u) n hn₂.symm
  exact ⟨n, r, hn₁, hr₂, hr₁⟩

/-- **The canonical map on points of a chart of `𝒭`, read through its representing
equivalence.** The chart is its own composition with the identity, and the representing
equivalence of the tautological chart is that identity. -/
private theorem pointsMap_chart_refineSquare (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hW : IsAlgebraicSpace B S hS W)
    (i : Stack.fibredCategory B S hS W ⟶ (refineSquare d e).pt.val)
    (p : Space.points B S hS W) (r : points B S hS (refineSquare d e).pt)
    (hp : Stack.spacePointMap B S hS W (refineSquare d e).pt.val i.hom p = r) :
    pointsMap B S hS
      (Bicategory.InducedBicategory.mkHom i :
        Stack.algebraicSpaceStack.{u, w} B S hS W hW ⟶ (refineSquare d e).pt)
      (Stack.spacePointMap B S hS W (Stack.algebraicSpaceStack.{u, w} B S hS W hW).val
        (Stack.representingEquivalence B S hS W
          (Stack.algebraicSpaceStack.{u, w} B S hS W hW).val
          (StacksRepresentableCFG.EquivalenceOver.refl _)).functor p) = r :=
  (congrFun (Stack.spacePointMap_eq_pointsMap_comp B S hS W (refineSquare d e).pt.val i.hom)
    p).symm.trans hp

/-- **The hard implication of Stacks 0CIC.** If the top horizontal morphism of one diagram of
`AlgebraicGeometry.Stack.AlgebraicStacks.PointedFlatDiagram` is flat at its marked point, then so
is the top horizontal morphism of every other such diagram.

Write `U, V, a, b, h, u` for the data of the first diagram and `U', V', a', b', h', u'` for that
of the second. The chase runs over the five 2-fibre products `𝒬 = V' ×_𝒴 𝒳`, `𝒩 = U ×_𝒳 𝒬`,
`𝒭 = U' ×_𝒬 𝒩`, `𝒯 = V' ×_𝒴 V` and `𝒵 = 𝒯 ×_V U`. The point of `𝒭` above both marked points
exists by **Stacks 04XH** applied twice, and `W` is a flat chart of `𝒭` through it. Pasting
exhibits `𝒩` and `𝒵` as 2-fibre products of the one cospan `(b', a ≫ f)`, so the comparison
`𝒩 ⟶ 𝒵` is an equivalence and the composite `W ⟶ 𝒭 ⟶ 𝒩 ⟶ 𝒵` is flat; the remaining two steps
`𝒵 ⟶ 𝒯` and `𝒯 ⟶ V'` are flat above the marked point of the first diagram and flat
respectively. -/
private theorem PointedFlatDiagram.isFlatAt_of_isFlatAt (hd : Space.IsFlatAt B S hS d.h d.u) :
    Space.IsFlatAt B S hS e.h e.u := by
  classical
  obtain ⟨T, hT, ⟨eT⟩⟩ := isRepresentableByAlgebraicSpace_targetSquare d e
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := isRepresentableByAlgebraicSpace_sliceSquare d e
  obtain ⟨C, -, ⟨eC⟩⟩ := isRepresentableByAlgebraicSpace_sliceCanonical d e
  obtain ⟨n, r, hn, hrsnd, hrfst⟩ := exists_point_refineSquare d e
  obtain ⟨W, hW, i, hi, hisurj⟩ := exists_flat_surjective_space_chart (refineSquare d e).pt
  obtain ⟨p, hp⟩ := hisurj r
  have hchart := pointsMap_chart_refineSquare d e W hW i p r hp
  have hk := (isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS
    (Bicategory.InducedBicategory.mkHom i :
      Stack.algebraicSpaceStack.{u, w} B S hS W hW ⟶ (refineSquare d e).pt)).2 hi
  have hone := pointsMap_chartToSlice_comp d e
    (𝒲 := Stack.algebraicSpaceStack.{u, w} B S hS W hW)
    (Bicategory.InducedBicategory.mkHom i) W Z
    (StacksRepresentableCFG.EquivalenceOver.refl _) eZ p n r hchart hrsnd hn
  have htwo := pointsMap_chartToTopLeft d e
    (𝒲 := Stack.algebraicSpaceStack.{u, w} B S hS W hW)
    (Bicategory.InducedBicategory.mkHom i) W
    (StacksRepresentableCFG.EquivalenceOver.refl _) p r hchart hrfst
  exact isFlatAt_of_chart d e hd (𝒲 := Stack.algebraicSpaceStack.{u, w} B S hS W hW)
    (Bicategory.InducedBicategory.mkHom i) hk
    W Z T C hW hZ hT (StacksRepresentableCFG.EquivalenceOver.refl _) eZ eT eC p hone htwo

end Chase

/-- **One implication of Stacks 0CIC.** If the top horizontal morphism of *every* diagram of
`AlgebraicGeometry.Stack.AlgebraicStacks.PointedFlatDiagram` is flat at its marked point, then
`f` is flat at `x` in the sense of **Stacks 0CID**.

The content is that there is at least one such diagram, which is
`AlgebraicGeometry.Stack.AlgebraicStacks.nonempty_pointedFlatDiagram`. This carries no
`@[stacks]` attribute because Stacks 0CIC asserts an equivalence, so one implication of it is
not the tag's covering set; the converse implication is the substance of that tag. -/
theorem isFlatAt_of_forall_isFlatAt {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (x : points B S hS 𝒳)
    (h : ∀ d : PointedFlatDiagram B S hS f x, Space.IsFlatAt B S hS d.h d.u) :
    IsFlatAt B S hS f x :=
  (nonempty_pointedFlatDiagram f x).elim fun d => ⟨d, h d⟩

/-- **Stacks 0CIC.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let `x` be
a point of `|𝒳|`. The top horizontal morphism of *some* diagram of
`AlgebraicGeometry.Stack.AlgebraicStacks.PointedFlatDiagram` is flat at its marked point if and
only if the top horizontal morphism of *every* such diagram is.

The forward implication is the iterated-2-fibre-product chase of the source; the backward one
holds because such a diagram exists through every point of `|𝒳|`. -/
@[stacks 0CIC]
theorem exists_isFlatAt_iff_forall_isFlatAt {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (x : points B S hS 𝒳) :
    (∃ d : PointedFlatDiagram B S hS f x, Space.IsFlatAt B S hS d.h d.u) ↔
      ∀ d : PointedFlatDiagram B S hS f x, Space.IsFlatAt B S hS d.h d.u :=
  ⟨fun hex e => hex.elim fun d hd => PointedFlatDiagram.isFlatAt_of_isFlatAt d e hd,
    isFlatAt_of_forall_isFlatAt f x⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
