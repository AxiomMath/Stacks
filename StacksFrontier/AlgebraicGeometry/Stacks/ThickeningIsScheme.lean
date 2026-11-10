module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineThickening
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSchemeStack

/-!
# Stacks 0BPW, clause (2): a thickening of algebraic stacks and being a scheme

**Stacks 0BPW, clause (2).** If `𝒳 ⊂ 𝒳'` is a thickening of algebraic stacks over `S`, then
`𝒳` is a scheme if and only if `𝒳'` is a scheme.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableCFG_iff_of_isThickening`: clause (2), with no
  hypothesis beyond the thickening.

## Implementation notes

`AlgebraicGeometry.Stack.isRepresentableCFG_iff_isThickening`
(`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSchemeStack`) proves the equivalence given the
affine case of Stacks 05ZR, `hAffineCase`: an algebraic space receiving a surjective closed
immersion from an affine algebraic space is affine. That statement is
`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace`
(`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineThickening`), which discharges
the hypothesis.

Being a scheme is read, as in `StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSchemeStack`, as
`Stacks.RepresentableMorphism.IsRepresentableCFG` of the structure functor: the category fibred
in groupoids is equivalent over the base to the category of elements of the presheaf of points
of a scheme over `S` (Stacks 02Y3, 04SV).
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-- If `𝒳 ⊂ 𝒳'` is a thickening of algebraic stacks over `S`, then `𝒳` is a scheme if and only if
`𝒳'` is a scheme. -/
@[stacks 0BPW "clause (2): scheme"]
theorem isRepresentableCFG_iff_of_isThickening (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i) :
    Stacks.RepresentableMorphism.IsRepresentableCFG 𝒳.val.val.p ↔
      Stacks.RepresentableMorphism.IsRepresentableCFG 𝒳'.val.val.p :=
  isRepresentableCFG_iff_isThickening B S hS i hi
    (Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace B S hS)

end AlgebraicGeometry.Stack
