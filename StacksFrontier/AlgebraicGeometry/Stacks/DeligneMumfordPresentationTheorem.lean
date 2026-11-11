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

## The implications

This file names the implications of both theorems as propositions. Those of **Stacks 06N3** are
proved downstream: (2) ⟹ (1) as
`AlgebraicGeometry.Stack.isAbsolutelyDMOfExistsEtalePresentation` and
`AlgebraicGeometry.Stack.isAbsolutelyDM_of_isDeligneMumfordStack`, off **Stacks 06MB**, part (1),
and (1) ⟹ (2) as `AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`, by the
étale chart construction near every finite type point; the equivalence itself is
`AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional` in
`StacksFrontier.AlgebraicGeometry.Stacks.AbsolutelyDMEtaleChartAssembly`. That construction uses
this file, so the equivalence is proved there and not here. Those of **Stacks 06MF** are proved in
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationUnconditional`, where the
equivalence is
`AlgebraicGeometry.Stack.isAbsolutelyQuasiDM_iff_hasQuasiDMPresentation_unconditional`.

Condition (2) of **Stacks 06MF** is spelled here with the stack-level properties
`AlgebraicGeometry.Stack.AlgebraicStacks.IsFlat` (**Stacks 06PW**) and
`...IsLocallyOfFinitePresentation` (**Stacks 06Q2**, part (1)), which is the form
**Stacks 06MB**, part (2), consumes.

## Main definitions

* `AlgebraicGeometry.Stack.HasQuasiDMPresentation`: condition (2) of **Stacks 06MF**.
* `AlgebraicGeometry.Stack.ExistsEtalePresentationOfIsAbsolutelyDM`,
  `AlgebraicGeometry.Stack.IsAbsolutelyDMOfExistsEtalePresentation`,
  `AlgebraicGeometry.Stack.ExistsQuasiDMPresentationOfIsAbsolutelyQuasiDM`,
  `AlgebraicGeometry.Stack.IsAbsolutelyQuasiDMOfHasQuasiDMPresentation`: the four
  implications, as propositions.

## Main results

* `AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack`: **Stacks 06N3**, from its
  two implications.

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

/-- **The implication (1) ⟹ (2) of Stacks 06N3, as a statement.** That a DM algebraic stack is
Deligne–Mumford, i.e. admits a surjective étale presentation by a scheme.

The source's proof builds an étale chart near each finite type point and takes the disjoint
union, through **Stacks 06MD**, **06N0**, **06N2**, **06G2** and **06G3**. It is proved as
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`. -/
abbrev ExistsEtalePresentationOfIsAbsolutelyDM : Prop :=
  ∀ 𝒳 : AlgebraicStacks.{u, w} B S hS, AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳 →
    IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val

/-- **The implication (2) ⟹ (1) of Stacks 06N3, as a statement.** That a Deligne–Mumford
algebraic stack is DM.

The mathematics is **Stacks 06MB**, part (1),
`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_of_isUnramified_flatCover`, together with
the bridge from the relative form of Section 04XB in which **Stacks 03YO** records its chart to
the smooth-diagram flatness and local finite presentation of **Stacks 06PW** and **06Q2**,
part (1), that **Stacks 06MB** asks for. It is proved as
`AlgebraicGeometry.Stack.isAbsolutelyDMOfExistsEtalePresentation`. -/
abbrev IsAbsolutelyDMOfExistsEtalePresentation : Prop :=
  ∀ 𝒳 : AlgebraicStacks.{u, w} B S hS, IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val →
    AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳

/-- **Stacks 06N3, from its two implications.** An algebraic stack is DM exactly when it is
Deligne–Mumford, given the two implications as arguments. Both are proved downstream, and the
equivalence with no argument is
`AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional`. -/
theorem isAbsolutelyDM_iff_isDeligneMumfordStack
    (hForward : ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS hZ)
    (hBackward : IsAbsolutelyDMOfExistsEtalePresentation.{u, w} B S hS hZ)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳 ↔
      IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val :=
  ⟨hForward 𝒳, hBackward 𝒳⟩

/-- **The implication (1) ⟹ (2) of Stacks 06MF, as a statement.** That a quasi-DM algebraic
stack admits a surjective, flat, locally finitely presented, locally quasi-finite presentation by
a scheme.

The source cuts out such a chart by a regular sequence in a smooth affine chart, using
**Stacks 06MD**, **06ME**, **06FX**, **06G2** and **06G3**. It is proved, pointwise in the
stack, as `AlgebraicGeometry.Stack.hasQuasiDMPresentation_of_isAbsolutelyQuasiDM`. -/
abbrev ExistsQuasiDMPresentationOfIsAbsolutelyQuasiDM : Prop :=
  ∀ 𝒳 : AlgebraicStacks.{u, w} B S hS, AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳 →
    HasQuasiDMPresentation.{u, w} B S hS 𝒳

/-- **The implication (2) ⟹ (1) of Stacks 06MF, as a statement.** That an algebraic stack with a
surjective, flat, locally finitely presented, locally quasi-finite presentation by a scheme is
quasi-DM.

This is **Stacks 06MB**, part (2),
`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyQuasiDM_of_isLocallyQuasiFinite_flatCover`,
and it is proved as `AlgebraicGeometry.Stack.isAbsolutelyQuasiDMOfHasQuasiDMPresentation`. -/
abbrev IsAbsolutelyQuasiDMOfHasQuasiDMPresentation : Prop :=
  ∀ 𝒳 : AlgebraicStacks.{u, w} B S hS, HasQuasiDMPresentation.{u, w} B S hS 𝒳 →
    AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳

end AlgebraicGeometry.Stack

end
