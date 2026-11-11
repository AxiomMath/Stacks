module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# A reduced one-point DM algebraic stack has an étale cover by a field (Stacks 06N0)

**Stacks 06N0** says that a DM, locally Noetherian, reduced algebraic stack `𝒵` whose point
space `|𝒵|` is a singleton admits a field `k` and a surjective étale 1-morphism
`Spec k ⟶ 𝒵`.

This is the step of the proof of **Stacks 06N3** (the theorem that a DM algebraic stack is
Deligne–Mumford) which produces the étale chart of the residual gerbe at a finite type point;
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationTheorem` carries that theorem's
substantial direction as a hypothesis, and this lemma is one of the five tags that hypothesis
names.

## Where it is proved

This module fixes the vocabulary: the hypothesis and the conclusion of the tag. The proof is
`AlgebraicGeometry.Stack.hasSurjectiveEtaleFieldSpectrumCover_unconditional` in
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordSingletonEtaleCoverUnconditional`, which
follows the source: **Stacks 06MP**, part (1) ⟹ (2), gives a surjective, flat, locally finitely
presented 1-morphism `Spec k ⟶ 𝒵`, and the groupoid of that flat presentation is divided by the
open and closed subgroupoid through the identity (**Stacks 06FF**, **06LZ**, **04S4**), whose
quotient is the spectrum of the field of invariants, étale over `𝒵`.

## Main definitions

* `AlgebraicGeometry.Stack.IsReducedLocallyNoetherianSingletonDM`: the hypothesis of
  **Stacks 06N0**.
* `AlgebraicGeometry.Stack.HasSurjectiveEtaleFieldSpectrumCover`: its conclusion.
* `AlgebraicGeometry.Stack.ExistsSurjectiveEtaleFieldCoverOfReducedSingletonDM`: the implication
  between them, over every algebraic stack.

## Implementation notes

DM-ness is the *absolute* property of **Stacks 050D**, part (5),
`AlgebraicGeometry.Stack.AlgebraicStacks.IsAbsolutelyDM`, as for every user of that part; the
ambient big fppf site must therefore contain the terminal scheme, which is the hypothesis `hZ`.
This matches the DM-ness used by
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationTheorem`.

Reducedness and local Noetherianity are `AlgebraicGeometry.Stack.IsReducedStack` and
`AlgebraicGeometry.Stack.IsLocallyNoetherianStack`, the existential scheme criteria of
**Stacks 04YF**, which is the vocabulary
`StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack` and
`StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe` already use. That `|𝒵|` is a singleton is
spelled as `Nonempty` together with `Subsingleton` of the point space of **Stacks 04XG**, the
same way those files spell it.

The spectrum of a field is `AlgebraicGeometry.Stack.FieldSpectrum`, an object of the site
presented with an isomorphism of its underlying scheme onto the spectrum of a field; this is the
vocabulary condition (3) of **Stacks 06MT** and **Stacks 06MP** are phrased in. Étaleness is
`AlgebraicGeometry.Stack.IsEtale` (**Stacks 0CIL**) and surjectivity is
`AlgebraicGeometry.Stack.IsSurjective` (**Stacks 04ZS**).

## References

* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 046T](https://stacks.math.columbia.edu/tag/046T)
* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 05VH](https://stacks.math.columbia.edu/tag/05VH)
* [Stacks Project, Tag 06FF](https://stacks.math.columbia.edu/tag/06FF)
* [Stacks Project, Tag 06LH](https://stacks.math.columbia.edu/tag/06LH)
* [Stacks Project, Tag 06LZ](https://stacks.math.columbia.edu/tag/06LZ)
* [Stacks Project, Tag 06MM](https://stacks.math.columbia.edu/tag/06MM)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The hypothesis of Stacks 06N0.** An algebraic stack over `S` which is DM in the absolute
sense of **Stacks 050D**, part (5), locally Noetherian, reduced, and whose point space is a
singleton. -/
abbrev IsReducedLocallyNoetherianSingletonDM (𝒵 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒵 ∧
    IsLocallyNoetherianStack B S hS 𝒵 ∧
      IsReducedStack B S hS 𝒵 ∧
        Nonempty (points B S hS 𝒵.val.val 𝒵.val.property) ∧
          Subsingleton (points B S hS 𝒵.val.val 𝒵.val.property)

/-- **The conclusion of Stacks 06N0.** There is a field `k` and a surjective étale 1-morphism
from the algebraic stack of `Spec k` to `𝒵`. -/
abbrev HasSurjectiveEtaleFieldSpectrumCover (𝒵 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  ∃ (F : FieldSpectrum B S hS) (f : schemeStack.{u, w} B S hS F.base ⟶ 𝒵),
    IsSurjective B S hS f ∧ IsEtale B S hS f

/-- **The implication of Stacks 06N0, as a proposition.** That every DM, locally Noetherian,
reduced algebraic stack with a one-point space admits a surjective étale 1-morphism from the
spectrum of a field. It holds:
`AlgebraicGeometry.Stack.hasSurjectiveEtaleFieldSpectrumCover_unconditional` proves it. -/
abbrev ExistsSurjectiveEtaleFieldCoverOfReducedSingletonDM : Prop :=
  ∀ 𝒵 : AlgebraicStacks.{u, w} B S hS,
    IsReducedLocallyNoetherianSingletonDM.{u, w} B S hS hZ 𝒵 →
      HasSurjectiveEtaleFieldSpectrumCover.{u, w} B S hS 𝒵

/-- The conclusion of **Stacks 06N0** read off the implication
`AlgebraicGeometry.Stack.ExistsSurjectiveEtaleFieldCoverOfReducedSingletonDM`. The tag itself is
`AlgebraicGeometry.Stack.hasSurjectiveEtaleFieldSpectrumCover_unconditional`, which needs no such
argument. -/
theorem hasSurjectiveEtaleFieldSpectrumCover
    (hCover : ExistsSurjectiveEtaleFieldCoverOfReducedSingletonDM.{u, w} B S hS hZ)
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (h𝒵 : IsReducedLocallyNoetherianSingletonDM.{u, w} B S hS hZ 𝒵) :
    HasSurjectiveEtaleFieldSpectrumCover.{u, w} B S hS 𝒵 :=
  hCover 𝒵 h𝒵

end AlgebraicGeometry.Stack

end
