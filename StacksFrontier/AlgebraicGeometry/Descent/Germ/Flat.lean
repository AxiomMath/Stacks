module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Basic

/-!
# Flat morphisms of germs of schemes

A morphism of germs of schemes `(X, x) → (S, s)` is *flat* when the induced homomorphism of
local rings `O_{S, s} → O_{X, x}` is flat. This is the property `𝒫` of morphisms of germs
whose étale locality on the source and target is Stacks 04ND, and it is the property with
which Stacks 03ML part (2) instantiates the pointed-chart lemma Stacks 04NC to define
flatness of a morphism of algebraic spaces at a point.

## Main definitions

* `AlgebraicGeometry.MorphismOfGerms.IsFlat` says that a morphism of germs of schemes is
  flat.

## Main results

There are no results beyond the definition.

## Implementation notes

As with `AlgebraicGeometry.MorphismOfGerms.IsEtale` and
`AlgebraicGeometry.MorphismOfGerms.IsSmooth` of Stacks 04QS, and with
`AlgebraicGeometry.HasFiberDimensionAt` of Stacks 04NL, the property is phrased as the
existence of a representative of the germ with the corresponding property of schemes, so that
no representative has to be chosen and no well-definedness lemma is needed: the condition is a
predicate on the quotient by construction. For a representative `g` defined on the open
neighbourhood `g.source` of the distinguished point, the homomorphism in question is Mathlib's
`AlgebraicGeometry.Scheme.Hom.stalkMap` of `g.hom` at that point, which goes from the stalk of
`S` at `g.hom ⟨X.point, g.mem_source⟩` — that is, at `S.point`, by `g.map_point` — to the stalk
of `g.source` at the distinguished point. The latter is the local ring `O_{X, x}` of the
source germ: the stalk of an open subscheme at a point agrees with the stalk of the ambient
scheme there, since `g.source.ι` is an open immersion. Flatness of a homomorphism of
commutative rings is Mathlib's `RingHom.Flat`, and
`AlgebraicGeometry.Flat.iff_flat_stalkMap` is the scheme-level statement that flatness of a
morphism is exactly flatness of all of its stalk maps.

The definition is an abbreviation, as its siblings in
`StacksFrontier/AlgebraicGeometry/Descent/Germ/Etale.lean` are, so that a client can use the
representative directly.

No Stacks tag is claimed here. Stacks 04ND is the *lemma* that this property is étale local on
the source and target, that is that it satisfies
`AlgebraicGeometry.MorphismOfGerms.IsEtaleLocalOnSourceAndTarget`; that lemma is not proved
here and this file must not be read as claiming it.

## References

* [Stacks Project, Tag 04NB](https://stacks.math.columbia.edu/tag/04NB)
* [Stacks Project, Tag 04ND](https://stacks.math.columbia.edu/tag/04ND)
* [Stacks Project, Tag 04QR](https://stacks.math.columbia.edu/tag/04QR)
-/

@[expose] public section

namespace AlgebraicGeometry

namespace MorphismOfGerms

universe u

/-- A morphism of germs of schemes is *flat* if it is represented on some open neighbourhood
of the distinguished point by a morphism of schemes whose homomorphism of local rings at that
point is flat. -/
abbrev IsFlat {X S : GermOfScheme.{u}} (f : MorphismOfGerms X S) : Prop :=
  ∃ g : Representative X S, mk g = f ∧
    (g.hom.stalkMap ⟨X.point, g.mem_source⟩).hom.Flat

end MorphismOfGerms

end AlgebraicGeometry

end
