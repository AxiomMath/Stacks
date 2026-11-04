module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiDMRelativePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteSource
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationRepresented

/-!
# The fibre of a quasi-DM 1-morphism over a field-valued point is quasi-DM

Let `f : 𝒯 ⟶ 𝒳` be a quasi-DM 1-morphism of algebraic stacks over `S` and let `p` be a
field-valued point of `𝒳` with field spectrum `Spec k`. Then the fibre `𝒯 ×_𝒳 Spec k` is a
quasi-DM algebraic stack in the absolute sense of **Stacks 050D**, part (6).

## Main results

* `AlgebraicGeometry.Stack.isQuasiDM_fieldFibreStackSquare_fst`: the projection
  `𝒯 ×_𝒳 Spec k ⟶ Spec k` is quasi-DM, being a base change of `f`.
* `AlgebraicGeometry.Stack.isQuasiDMAbs_schemeStack`: the algebraic stack of a scheme of the
  site is quasi-DM.
* `AlgebraicGeometry.Stack.isQuasiDMAbs_fieldFibreStackSquare`: the fibre `𝒯 ×_𝒳 Spec k` is
  quasi-DM.

## Implementation notes

The fibre is `AlgebraicGeometry.Stack.fieldFibreStackSquare`, the 2-fibre product square of the
1-morphism `Spec k ⟶ 𝒳` of `p` with `f`, so the base change of `f` is its *first* projection.
**Stacks 050F** for the quasi-DM condition is available at an arbitrary 2-fibre-product square
only for the second projection, as
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_baseChange_of_isTwoFibreProduct`; exchanging
the two legs with `CategoryTheory.Bicategory.TwoCommSq.swap` turns the first projection into the
second one of the square over the reversed cospan, which is a 2-fibre product by
`CategoryTheory.Bicategory.isTwoFibreProduct_swap`.

That the base `Spec k` is quasi-DM is **Stacks 050E**, part (3), at the structure 1-morphism,
together with **Stacks 050N**, part (2): a scheme of the site represents its own algebraic stack,
which is therefore quasi-DM over `S`, hence quasi-DM. The passage from the fibre's projection to
the fibre itself is then **Stacks 050L**, part (6).

This is what Remark **Stacks 0DS5** appeals to when it says that the fibres of a quasi-DM
1-morphism over the points of its target are quasi-DM algebraic stacks. The remark continues
that such stacks have non-negative dimension, which is
`AlgebraicGeometry.Stack.zero_le_dimensionAtPoint_fieldFibreStackSquare` in
`StacksFrontier/AlgebraicGeometry/Stacks/DimensionQuasiDM.lean`; the results below are the quasi-DM
input it consumes at a fibre, both the fibre's own quasi-DM-ness and the quasi-DM-ness of its
projection to the field spectrum, the latter being what bounds the relative dimension of a chart
by the chart's own dimension.

## References

* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DS5](https://stacks.math.columbia.edu/tag/0DS5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 050F, the quasi-DM case, at the fibre over a field-valued point.** The projection
`𝒯 ×_𝒳 Spec k ⟶ Spec k` of the fibre of a quasi-DM 1-morphism `f` over a field-valued point `p`
of `𝒳` is quasi-DM, being a base change of `f`.

The fibre square is taken over the cospan `(Spec k ⟶ 𝒳, f)`, so this projection is its first
leg; exchanging the two legs presents it as the second leg of a 2-fibre product over the
reversed cospan, where Stacks 050F is available. -/
theorem isQuasiDM_fieldFibreStackSquare_fst (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsQuasiDM B S hS f)
    (p : FieldValuedPoint B S hS 𝒳.val.val) :
    AlgebraicStacks.IsQuasiDM B S hS (fieldFibreStackSquare B S hS f p).fst :=
  AlgebraicStacks.isQuasiDM_baseChange_of_isTwoFibreProduct B S hS f
    (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p)
    (fieldFibreStackSquare B S hS f p).swap
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p) f))
    hf

/-- **Stacks 050E, part (3), and Stacks 050N, part (2), at a scheme of the site.** The algebraic
stack of a scheme `W` of the site is quasi-DM: it is representable by an algebraic space, hence
quasi-DM over `S`, hence quasi-DM in the absolute sense of Stacks 050D, part (6). -/
theorem isQuasiDMAbs_schemeStack (W : BigFppfOver B S hS) :
    IsQuasiDMAbs.{u, w, w} B S hS (schemeStack.{u, w} B S hS W) :=
  isQuasiDMAbs_of_isQuasiDMOver B S hS _
    (AlgebraicStacks.isQuasiDMOver_of_isRepresentableByAlgebraicSpace B S hS
      (schemeStack.{u, w} B S hS W)
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W))

/-- **Stacks 050L, part (6), at the fibre over a field-valued point.** The fibre
`𝒯 ×_𝒳 Spec k` of a quasi-DM 1-morphism `f` over a field-valued point `p` of `𝒳` is a quasi-DM
algebraic stack: its projection to `Spec k` is quasi-DM by Stacks 050F, and `Spec k` is quasi-DM.

This is the assertion Remark Stacks 0DS5 makes about the fibres of a quasi-DM 1-morphism. -/
theorem isQuasiDMAbs_fieldFibreStackSquare (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsQuasiDM B S hS f)
    (p : FieldValuedPoint B S hS 𝒳.val.val) :
    IsQuasiDMAbs.{u, w, w} B S hS (fieldFibreStackSquare B S hS f p).pt :=
  isQuasiDMAbs_of_isQuasiDM B S hS (fieldFibreStackSquare B S hS f p).fst
    (isQuasiDMAbs_schemeStack B S hS p.base)
    (isQuasiDM_fieldFibreStackSquare_fst B S hS f hf p)

end AlgebraicGeometry.Stack

end
