module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified

/-!
# An unramified morphism of algebraic spaces is locally quasi-finite (Stacks 05W0)

Stacks 05W0 has two assertions: that a morphism of algebraic spaces unramified at a point is
quasi-finite at that point, and the global consequence that an unramified morphism is locally
quasi-finite. The global one is proved here.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isUnramified`: **Stacks 05W0**, the global
  consequence.

## Implementation notes

Both conditions are the every-étale-chart condition of Stacks 03MJ — unramifiedness at
`AlgebraicGeometry.Unramified` and local quasi-finiteness at
`AlgebraicGeometry.LocallyOfFiniteType ⊓ AlgebraicGeometry.LocallyQuasiFinite` — so the statement
is `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_mono` at the corresponding implication between
properties of *scheme* morphisms, and that implication is instance synthesis from Mathlib's
`AlgebraicGeometry.Unramified` hierarchy together with
`AlgebraicGeometry.locallyQuasiFinite_of_unramified` (**Stacks 02V5**), both of which are
instances on a bare morphism. No pointwise reasoning and no fibre argument are involved, which is
why the global assertion does not wait on the pointwise one.

The pointwise assertion of 05W0 is **deliberately not stated**, and no part key is claimed for
it: it quantifies over the points of an algebraic space and over
`AlgebraicGeometry.Space.IsQuasiFiniteAt`, which is part (2) of Stacks 03XJ and which
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteType.lean` records as absent from this library. So
Stacks 05W0 is left PARTIAL, with the missing key named.

Stacks 05W0 is in Chapter 67 of the Stacks Project. It is a theorem, it
coins no notion, and it is stated over this library's own vocabulary.

## References

* [Stacks Project, Tag 02V5](https://stacks.math.columbia.edu/tag/02V5)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 05W0](https://stacks.math.columbia.edu/tag/05W0)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 05W0, the global consequence.** An unramified morphism of algebraic spaces over `S`
is locally quasi-finite: on every commuting square of étale scheme charts the induced scheme
morphism is unramified, hence locally of finite type and locally quasi-finite. -/
@[stacks 05W0 "global consequence",
  stacks 05W0 "an unramified morphism is locally quasi-finite", ega "IV 17.4.3"]
theorem isLocallyQuasiFinite_of_isUnramified {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (h : IsUnramified B S hS f) :
    IsLocallyQuasiFinite B S hS f :=
  holdsOnEveryEtaleChart_mono B S hS
    (fun g hg => by
      have : AlgebraicGeometry.Unramified g := hg
      exact ⟨inferInstance, inferInstance⟩)
    h

end AlgebraicGeometry.Space

end
