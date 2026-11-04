module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# The presentation theorems for DM and quasi-DM algebraic stacks (Stacks 06N3 and 06MF)

**Stacks 06N3.** An algebraic stack is DM if and only if it is Deligne–Mumford, if and only if
there is a scheme with a surjective étale 1-morphism to it.

**Stacks 06MF.** An algebraic stack is quasi-DM if and only if there is a scheme with a
surjective, flat, locally finitely presented, locally quasi-finite 1-morphism to it.

The source's conditions (2) and (3) of **Stacks 06N3** are the same condition in this library:
`AlgebraicGeometry.Stack.IsDeligneMumfordStack` (**Stacks 03YO**) is *defined* as the existence
of a 1-morphism from a scheme of the site which is representable by algebraic spaces, surjective
and étale. So **Stacks 06N3** is the single equivalence
`AlgebraicGeometry.Stack.AlgebraicStacks.IsAbsolutelyDM ↔
AlgebraicGeometry.Stack.IsDeligneMumfordStack`.

## What is proved and what is carried

Both theorems are stated here in full, and **both implications of each are carried as explicit
named hypotheses**. These are genuine structure theorems — the hard direction builds étale,
resp. flat locally quasi-finite, charts near every finite type point and takes their disjoint
union, through a chain of two dozen cited lemmas of which **Stacks 06MD, 06ME, 06G2, 06G3,
06N0, 06N2** are carried nowhere in this library.

The easy direction is **Stacks 06MB**, which *is* carried, as
`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_of_isUnramified_flatCover` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyQuasiDM_of_isLocallyQuasiFinite_flatCover`.
It is nevertheless not applied here, and the reason is a shape mismatch rather than missing
mathematics: those two take flatness and local finite presentation as the *stack-level*
properties `AlgebraicGeometry.Stack.AlgebraicStacks.IsFlat` (**Stacks 06PW**) and
`...IsLocallyOfFinitePresentation` (**Stacks 06Q2**, part (1)), which are tests over smooth
diagrams, whereas **Stacks 03YO** records surjectivity and étaleness of its chart in the
longhand relative form of Properties of Stacks, Section 04XB. The bridge between the two
formulations — that an étale chart is flat and locally of finite presentation in the
smooth-diagram sense — is not in the library. Condition (2) of **Stacks 06MF** is therefore
spelled here with the stack-level properties, which is the form **Stacks 06MB**, part (2),
consumes, and the hypothesis `hBackward` of each theorem is exactly that missing bridge composed
with **Stacks 06MB**.

## Main definitions

* `AlgebraicGeometry.Stack.HasQuasiDMPresentation`: condition (2) of **Stacks 06MF**.
* `AlgebraicGeometry.Stack.ExistsEtalePresentationOfIsAbsolutelyDM`,
  `AlgebraicGeometry.Stack.IsAbsolutelyDMOfExistsEtalePresentation`,
  `AlgebraicGeometry.Stack.ExistsQuasiDMPresentationOfIsAbsolutelyQuasiDM`,
  `AlgebraicGeometry.Stack.IsAbsolutelyQuasiDMOfHasQuasiDMPresentation`: the four carried
  implications.

## Main results

* `AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack`: **Stacks 06N3**.
* `AlgebraicGeometry.Stack.isAbsolutelyQuasiDM_iff_hasQuasiDMPresentation`: **Stacks 06MF**.

## Implementation notes

The DM and quasi-DM properties are the *absolute* ones of **Stacks 050D**, parts (5) and (6), as
for every user of those parts; the ambient big fppf site must therefore contain the terminal
scheme, which is the hypothesis `hZ`.

A scheme of the site is read as an algebraic stack by `AlgebraicGeometry.Stack.schemeStack`.
Local quasi-finiteness of the chart is `AlgebraicGeometry.Stack.IsLocallyQuasiFinite`, the
Section 04XB notion, not the stack-level `...AlgebraicStacks.IsLocallyQuasiFinite` of
**Stacks 06PU**, because the source's condition is a condition on the chart as a representable
1-morphism.

## References

* [Stacks Project, Tag 03YO](https://stacks.math.columbia.edu/tag/03YO)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 06MB](https://stacks.math.columbia.edu/tag/06MB)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Condition (2) of Stacks 06MF.** An algebraic stack `𝒳` *has a quasi-DM presentation* when
there is a scheme `W` of the site and a 1-morphism `schemeStack W ⟶ 𝒳` which is surjective,
flat, locally of finite presentation and locally quasi-finite.

Surjectivity, flatness and local finite presentation are the stack-level properties of
**Stacks 04ZS**, **06PW** and **06Q2**, part (1) — the form **Stacks 06MB**, part (2), consumes
— while local quasi-finiteness is the Section 04XB notion
`AlgebraicGeometry.Stack.IsLocallyQuasiFinite`, which is the source's condition on the chart. -/
abbrev HasQuasiDMPresentation (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  ∃ (W : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS W ⟶ 𝒳),
    IsSurjective B S hS f ∧
    AlgebraicStacks.IsFlat B S hS f ∧
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f ∧
    IsLocallyQuasiFinite B S hS f.hom

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The substantial direction of Stacks 06N3, carried.** That a DM algebraic stack is
Deligne–Mumford, i.e. admits a surjective étale presentation by a scheme.

The source's proof builds an étale chart near each finite type point and takes the disjoint
union, through **Stacks 06MD**, **06N0**, **06N2**, **06G2** and **06G3**, none of which is in
this library. -/
abbrev ExistsEtalePresentationOfIsAbsolutelyDM : Prop :=
  ∀ 𝒳 : AlgebraicStacks.{u, w} B S hS, AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳 →
    IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val

/-- **The easy direction of Stacks 06N3, carried.** That a Deligne–Mumford algebraic stack is
DM.

The mathematics is **Stacks 06MB**, part (1), which the library has as
`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_of_isUnramified_flatCover`. What is
missing, and what this hypothesis therefore stands for, is the bridge between the two ways the
library records a chart: **Stacks 03YO** gives surjectivity and étaleness in the longhand
relative form of Section 04XB, while **Stacks 06MB** asks for flatness and local finite
presentation as the smooth-diagram properties of **Stacks 06PW** and **06Q2**, part (1). -/
abbrev IsAbsolutelyDMOfExistsEtalePresentation : Prop :=
  ∀ 𝒳 : AlgebraicStacks.{u, w} B S hS, IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val →
    AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳

/-- **The substantial direction of Stacks 06MF, carried.** That a quasi-DM algebraic stack
admits a surjective, flat, locally finitely presented, locally quasi-finite presentation by a
scheme.

The source cuts out such a chart by a regular sequence in a smooth affine chart, using
**Stacks 06MD**, **06ME**, **06FX**, **06G2** and **06G3**; the first two and the last two are
not in this library. -/
abbrev ExistsQuasiDMPresentationOfIsAbsolutelyQuasiDM : Prop :=
  ∀ 𝒳 : AlgebraicStacks.{u, w} B S hS, AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳 →
    HasQuasiDMPresentation.{u, w} B S hS 𝒳

/-- **The easy direction of Stacks 06MF, carried.** That an algebraic stack with a surjective,
flat, locally finitely presented, locally quasi-finite presentation by a scheme is quasi-DM.

This is **Stacks 06MB**, part (2), which the library has as
`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyQuasiDM_of_isLocallyQuasiFinite_flatCover`;
what this hypothesis stands for is the one step still missing, repackaging the Section 04XB
local quasi-finiteness of the chart as the `AlgebraicGeometry.Stack.HasRelativeProperty` form
that lemma takes. -/
abbrev IsAbsolutelyQuasiDMOfHasQuasiDMPresentation : Prop :=
  ∀ 𝒳 : AlgebraicStacks.{u, w} B S hS, HasQuasiDMPresentation.{u, w} B S hS 𝒳 →
    AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳

/-- **Stacks 06N3.** An algebraic stack is DM exactly when it is Deligne–Mumford — equivalently,
by **Stacks 03YO**, exactly when there is a scheme of the site with a representable, surjective,
étale 1-morphism to it.

Both implications are carried; see
`AlgebraicGeometry.Stack.ExistsEtalePresentationOfIsAbsolutelyDM` and
`AlgebraicGeometry.Stack.IsAbsolutelyDMOfExistsEtalePresentation` for what each one stands for
and why. -/
@[stacks 06N3 "the equivalence of (1) DM with (2) Deligne-Mumford and (3) the existence of a
  surjective etale presentation by a scheme; (2) and (3) are the same condition here, since
  Stacks 03YO defines Deligne-Mumford that way. Both implications are carried, as the
  hypotheses `hForward` (the structure theorem: Stacks 06MD, 06N0, 06N2, 06G2, 06G3 are absent)
  and `hBackward` (Stacks 06MB part (1) is present but the bridge from the Section 04XB form of
  an etale chart to the smooth-diagram flatness of Stacks 06PW is absent)"]
theorem isAbsolutelyDM_iff_isDeligneMumfordStack
    (hForward : ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS hZ)
    (hBackward : IsAbsolutelyDMOfExistsEtalePresentation.{u, w} B S hS hZ)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳 ↔
      IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val :=
  ⟨hForward 𝒳, hBackward 𝒳⟩

/-- **Stacks 06MF.** An algebraic stack is quasi-DM exactly when there is a scheme of the site
with a surjective, flat, locally finitely presented, locally quasi-finite 1-morphism to it.

Both implications are carried; see
`AlgebraicGeometry.Stack.ExistsQuasiDMPresentationOfIsAbsolutelyQuasiDM` and
`AlgebraicGeometry.Stack.IsAbsolutelyQuasiDMOfHasQuasiDMPresentation`. -/
@[stacks 06MF "the equivalence of (1) quasi-DM with (2) the existence of a surjective, flat,
  locally finitely presented, locally quasi-finite presentation by a scheme. Both implications
  are carried, as the hypotheses `hForward` (the structure theorem: Stacks 06MD, 06ME, 06G2,
  06G3 are absent) and `hBackward` (Stacks 06MB part (2) is present but the repackaging of the
  Section 04XB local quasi-finiteness of the chart into its HasRelativeProperty form is
  absent)"]
theorem isAbsolutelyQuasiDM_iff_hasQuasiDMPresentation
    (hForward : ExistsQuasiDMPresentationOfIsAbsolutelyQuasiDM.{u, w} B S hS hZ)
    (hBackward : IsAbsolutelyQuasiDMOfHasQuasiDMPresentation.{u, w} B S hS hZ)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳 ↔
      HasQuasiDMPresentation.{u, w} B S hS 𝒳 :=
  ⟨hForward 𝒳, hBackward 𝒳⟩

end AlgebraicGeometry.Stack

end
