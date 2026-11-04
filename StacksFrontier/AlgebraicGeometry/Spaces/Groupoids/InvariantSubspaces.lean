module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# Invariant subspaces of a groupoid in algebraic spaces (Stacks 044F)

Let `G` be a groupoid in algebraic spaces over an algebraic space `B` over a scheme `S` of a big
fppf site, in the sense of Stacks 043W. A subspace of the space of objects of `G` is *invariant*
when the two ways of pulling it back to the space of arrows — along the source map and along the
target map — agree. Stacks 044F spells this out in three forms, one for each class of subspace.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsInvariantOpen`: **Stacks 044F**, part (1) —
  invariance of an open subspace of the object space.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsInvariantLocallyClosed`: **Stacks 044F**,
  part (2) — invariance of a locally closed subspace of the object space.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsInvariantMonomorphism`: **Stacks 044F**,
  part (3) — invariance of a monomorphism into the object space.

## DELIBERATE OWNERSHIP EXCEPTION — this is a Chapter 78 tag

Stacks 044F is `spaces-groupoids`, **Chapter 78**. It is stated here, as
`AlgebraicGeometry.GroupoidInAlgebraicSpaces` (Stacks 043W) is in `GroupoidInSpaces.lean` and
`AlgebraicGeometry.Stack.quotientStack` (Stacks 044Q) in `QuotientStack.lean`, because the
Chapter 97–100 results that restrict a groupoid to an invariant subspace — Stacks 04YN and
Stacks 0505 — cannot be stated without it.

## Implementation notes

Each of the first two predicates *includes* the condition that the subfunctor be a subspace of the
relevant kind; neither is the bare inverse-image condition. Part (1) is stated as an inequality of
subfunctors rather than an equality, which is the form the source gives: for an open subspace, an
arrow whose source lies in `W` has its target in `W`. Part (2) is an equality, because a locally
closed subspace is not determined by one inclusion.

Part (3) compares the two base changes of `i` to the space of arrows as objects of the slice
category over the space of arrows, which is what "equal as algebraic spaces over the arrow space"
means. Because `i` is a monomorphism, such an isomorphism over the arrow space is unique when it
exists, so `Nonempty` loses nothing. The two fibre products are the chosen
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct` of Stacks 02X2, each carrying its canonical
projection to the arrow space — `pullback.snd` for the target base change and `pullback.fst` for
the source base change, following the order in which the source states them.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044F](https://stacks.math.columbia.edu/tag/044F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}
  {B : AlgebraicSpaces site S hS}

/-- **Stacks 044F, part (1).** An open subspace of the object space of a groupoid in algebraic
spaces is *invariant* when every arrow whose source lies in it has its target in it. -/
@[stacks 044F "part (1): invariant open subspaces"]
abbrev IsInvariantOpen (G : GroupoidInAlgebraicSpaces site S hS B)
    (W : Subfunctor G.objects.obj) : Prop :=
  Space.IsOpenSubspace site S hS W ∧
    W.preimage G.source.hom ≤ W.preimage G.target.hom

/-- **Stacks 044F, part (2).** A locally closed subspace of the object space of a groupoid in
algebraic spaces is *invariant* when its inverse images under the source and the target map agree
as subspaces of the space of arrows. -/
@[stacks 044F "part (2): invariant locally closed subspaces"]
abbrev IsInvariantLocallyClosed (G : GroupoidInAlgebraicSpaces site S hS B)
    (Z : Subfunctor G.objects.obj) : Prop :=
  Space.IsLocallyClosedSubspace site S hS Z ∧
    Z.preimage G.target.hom = Z.preimage G.source.hom

/-- **Stacks 044F, part (3).** A monomorphism into the object space of a groupoid in algebraic
spaces is *invariant* when its base change along the target map and its base change along the
source map are isomorphic as algebraic spaces over the space of arrows. -/
@[stacks 044F "part (3): invariant monomorphisms"]
noncomputable abbrev IsInvariantMonomorphism (G : GroupoidInAlgebraicSpaces site S hS B)
    {T : AlgebraicSpaces site S hS} (i : T ⟶ G.objects) [Mono i] : Prop :=
  Nonempty
    ((Over.mk (ObjectProperty.homMk (pullback.snd i.hom G.target.hom) :
      AlgebraicSpaces.fiberProduct site S hS i G.target ⟶ G.arrows) : Over G.arrows) ≅
     (Over.mk (ObjectProperty.homMk (pullback.fst G.source.hom i.hom) :
      AlgebraicSpaces.fiberProduct site S hS G.source i ⟶ G.arrows) : Over G.arrows))

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
