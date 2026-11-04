module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeQuasiDMMonoInput

/-!
# Residual gerbes exist on quasi-DM algebraic stacks (Stacks 06UI)

**Stacks 06UI**: let `𝒳` be a quasi-DM algebraic stack; then the residual gerbe of `𝒳` at `x`
exists for every `x ∈ |𝒳|`. Existence of the residual gerbe at `x` is, by **Stacks 06MU**,
that some strictly full subcategory of `𝒳` meets the specification
`AlgebraicGeometry.Stack.IsResidualGerbeAt` of **Stacks 06MT**: it is closed under isomorphism,
its full subcategory is a reduced locally Noetherian algebraic stack, and that subcategory has
exactly one point, lying over `x`.

The source's argument is run in
`StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeQuasiDM`, which derives the residual gerbe
from two universally quantified inputs: the implication (1) ⟹ (2) of **Stacks 06MF** and
**Stacks 06S1**. `StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeQuasiDMMonoInput` proves the
second of those, leaving
`AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_isAbsolutelyQuasiDM_of_hasQuasiDMPresentation`
with the Stacks 06MF input alone. This file discharges that input too, from
`AlgebraicGeometry.Stack.hasQuasiDMPresentation_of_isAbsolutelyQuasiDM` — the substantial
direction of Stacks 06MF, proved in
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationUnconditional` — and so proves
Stacks 06UI outright.

## Main results

* `AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_isAbsolutelyQuasiDM`: **Stacks 06UI**.

## References

* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06MU](https://stacks.math.columbia.edu/tag/06MU)
* [Stacks Project, Tag 06S1](https://stacks.math.columbia.edu/tag/06S1)
* [Stacks Project, Tag 06UI](https://stacks.math.columbia.edu/tag/06UI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06UI.** Let `𝒳` be a quasi-DM algebraic stack over `S`. Then the residual gerbe of
`𝒳` at `x` exists for every `x ∈ |𝒳|`: some strictly full subcategory `P` of `𝒳` meets the
specification `AlgebraicGeometry.Stack.IsResidualGerbeAt` of **Stacks 06MT**, which by
**Stacks 06MU** is what it means for the residual gerbe at `x` to exist.

This is
`AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_isAbsolutelyQuasiDM_of_hasQuasiDMPresentation`
— the source's proof, with **Stacks 06S1** already supplied — applied to the substantial
direction of **Stacks 06MF**,
`AlgebraicGeometry.Stack.hasQuasiDMPresentation_of_isAbsolutelyQuasiDM`. -/
@[stacks 06UI "the residual gerbe of a quasi-DM algebraic stack exists at every point of its \
space, in the sense of 06MU: some strictly full subcategory meets the 06MT specification \
IsResidualGerbeAt, i.e. is a reduced locally Noetherian algebraic substack with one point lying \
over x. Nothing is left open: the source's chart comes from 06MF proved outright \
(hasQuasiDMPresentation_of_isAbsolutelyQuasiDM) and its 06S1 step from \
isLocallyQuasiFinite_comp_of_mono_to_field"]
theorem exists_isResidualGerbeAt_of_isAbsolutelyQuasiDM
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳)
    (x : AlgebraicStacks.points B S hS 𝒳) :
    ∃ P : ObjectProperty 𝒳.val.val.obj, IsResidualGerbeAt B S hS 𝒳 x P :=
  exists_isResidualGerbeAt_of_isAbsolutelyQuasiDM_of_hasQuasiDMPresentation.{u, w} B S hS hZ
    (hasQuasiDMPresentation_of_isAbsolutelyQuasiDM.{u, w} B S hS hZ) 𝒳 h𝒳 x

end AlgebraicGeometry.Stack

end
