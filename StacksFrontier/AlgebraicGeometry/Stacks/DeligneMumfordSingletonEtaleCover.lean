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

## What is proved and what is carried

The conclusion is carried, as the explicit hypothesis
`AlgebraicGeometry.Stack.ExistsSurjectiveEtaleFieldCoverOfReducedSingletonDM`. The statement is
stated in full and faithfully; what follows is exactly which inputs are missing and why no part
of the argument can be run without them.

The source's proof is a single chain, and its **first step is already unavailable**: it begins by
invoking **Stacks 06MP** (Properties of Stacks, `lemma-unique-point-better`) to get a surjective,
flat, locally finitely presented 1-morphism `Spec k ⟶ 𝒵`. The library states Stacks 06MP as an
equivalence in
`StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack` and proves only the direction
(2) ⟹ (1); the direction this lemma needs, (1) ⟹ (2), is not proved there, and that file's
implementation notes say why — the finite-presentation half is available but the *flatness* half
is the flatness half of **Stacks 06MM**, of which only the surjectivity half
(`AlgebraicGeometry.Stack.isSurjective_of_fieldSpectrum_cover`) is in the library. Since every
later step consumes the groupoid `(U, R, s, t, c)` built from that cover, nothing downstream can
be run first.

Three further cited inputs are also absent, so even granted the cover the chain would stop:

* **Stacks 06FF** (More on Groupoids in Spaces,
  `lemma-groupoid-on-field-dimension-equal-stabilizer`): for a groupoid on the spectrum of a
  field, `dim(R)` equals the dimension of the stabilizer. This is what turns DM-ness — which
  makes the stabilizer `G` unramified over `U`, hence of dimension `0` — into `dim(R) = 0`.
* **Stacks 06LZ** (Spaces over Fields, `lemma-locally-finite-type-dim-zero`): an algebraic space
  locally of finite type over a field and of dimension `0` is a scheme. This is what makes `R` a
  scheme, without which the rest of the argument — which works with `Spec A ⊆ R` and the
  finite flat equivalence relation `P` — has no object to work on.
* **Stacks 04S4** (Bootstrap, `lemma-divide-subgroupoid`): the division of the groupoid by the
  open subgroupoid `P`, producing the groupoid
  `(U̅, R̅, s̅, t̅, c̅)` of which `(U, R, s, t, c)` is the restriction. This is the step that makes
  the quotient morphism étale rather than merely flat.

The inputs that *are* available, and would be used by a proof once the four above are available, are
**Stacks 06LH** (`StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero`), **Stacks 05VH**
(`StacksFrontier.AlgebraicGeometry.Etale.UniversallyInjectiveUnramified.Basic`), **Stacks 03BM**
(`StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.AffineQuotient`), **Stacks 046T**
(`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.RestrictionCoverings`) and
the surjectivity half of **Stacks 06MM**
(`StacksFrontier.AlgebraicGeometry.Stacks.FieldSpectrumCoverSurjective`).

## A footnote in the source

The source attaches a footnote to the étaleness step of this proof: "We urge the reader to find
his/her own proof of this fact. In fact the argument has a lot in common with the final argument
of the proof of Bootstrap, Theorem 0ADV hence probably should be isolated into its own lemma
somewhere." The statement is not in doubt; the remark is about the proof's presentation.

## Main definitions

* `AlgebraicGeometry.Stack.IsReducedLocallyNoetherianSingletonDM`: the hypothesis of
  **Stacks 06N0**.
* `AlgebraicGeometry.Stack.HasSurjectiveEtaleFieldSpectrumCover`: its conclusion.
* `AlgebraicGeometry.Stack.ExistsSurjectiveEtaleFieldCoverOfReducedSingletonDM`: the carried
  implication.

## Main results

* `AlgebraicGeometry.Stack.hasSurjectiveEtaleFieldSpectrumCover`: **Stacks 06N0**.

## Implementation notes

DM-ness is the *absolute* property of **Stacks 050D**, part (5),
`AlgebraicGeometry.Stack.AlgebraicStacks.IsAbsolutelyDM`, as for every user of that part; the
ambient big fppf site must therefore contain the terminal scheme, which is the hypothesis `hZ`.
This matches the DM-ness used by
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationTheorem`, so this lemma's
conclusion is in the shape that file's carried hypothesis would consume.

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

/-- **Stacks 06N0, carried.** That a DM, locally Noetherian, reduced algebraic stack with a
one-point space admits a surjective étale 1-morphism from the spectrum of a field.

The source's proof begins by invoking the direction (1) ⟹ (2) of **Stacks 06MP** to produce a
surjective, flat, locally finitely presented 1-morphism from the spectrum of a field; only the
converse direction of Stacks 06MP is proved in this library, so the groupoid every later step
works with cannot be formed. **Stacks 06FF**, **06LZ** and **04S4** are absent as well. -/
abbrev ExistsSurjectiveEtaleFieldCoverOfReducedSingletonDM : Prop :=
  ∀ 𝒵 : AlgebraicStacks.{u, w} B S hS,
    IsReducedLocallyNoetherianSingletonDM.{u, w} B S hS hZ 𝒵 →
      HasSurjectiveEtaleFieldSpectrumCover.{u, w} B S hS 𝒵

/-- **Stacks 06N0.** A DM, locally Noetherian, reduced algebraic stack whose point space is a
singleton admits a field `k` and a surjective étale 1-morphism `Spec k ⟶ 𝒵`.

The implication is carried as the hypothesis `hCover`; see
`AlgebraicGeometry.Stack.ExistsSurjectiveEtaleFieldCoverOfReducedSingletonDM` for exactly which
cited inputs are absent and why no part of the chain can be run without them. -/
@[stacks 06N0 "a DM, locally Noetherian, reduced algebraic stack with a singleton point space \
admits a surjective etale 1-morphism from the spectrum of a field. The implication is carried \
as the hypothesis `hCover`: the source's first step is the direction (1) => (2) of Stacks 06MP, \
of which this library proves only the converse, and Stacks 06FF, 06LZ and 04S4 are absent too"]
theorem hasSurjectiveEtaleFieldSpectrumCover
    (hCover : ExistsSurjectiveEtaleFieldCoverOfReducedSingletonDM.{u, w} B S hS hZ)
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (h𝒵 : IsReducedLocallyNoetherianSingletonDM.{u, w} B S hS hZ 𝒵) :
    HasSurjectiveEtaleFieldSpectrumCover.{u, w} B S hS 𝒵 :=
  hCover 𝒵 h𝒵

end AlgebraicGeometry.Stack

end
