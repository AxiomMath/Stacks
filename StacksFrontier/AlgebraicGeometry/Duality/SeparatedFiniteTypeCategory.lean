module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import StacksCore.Tactic.StacksAttribute

/-!
# Schemes separated and of finite type over a base

The schemes `X` over a scheme `S` whose structure morphism is separated and of finite type
form a category, with all morphisms of schemes over `S` between them. This is the category
written `FTS_S` in [Stacks, Tag 0F42], the setting in which the upper shriek functors are
constructed. There the base is assumed Noetherian; the category itself does not need that
hypothesis, so it is not imposed here and its users carry it as `[IsNoetherian S]`.

## Main definitions

* `AlgebraicGeometry.isSeparatedFiniteType` is the property of a morphism of schemes of
  being separated and of finite type.
* `AlgebraicGeometry.FTS` is the category of schemes separated and of finite type over a
  base, with morphisms over that base.

## Main results

* `AlgebraicGeometry.isSeparatedFiniteType_iff` splits the property into its three
  conditions.

## Implementation notes

Following the convention of `AlgebraicGeometry.LocallyOfFiniteType`, a morphism of finite
type is the two conditions `LocallyOfFiniteType` and `QuasiCompact` rather than a bundled
predicate, so `isSeparatedFiniteType` is the infimum of three Mathlib properties. It is an
`abbrev` so that the infimum unfolds reducibly, which is what lets the projections
`FTS.isSeparated_hom`, `FTS.locallyOfFiniteType_hom` and `FTS.quasiCompact_hom` and the
constructor `FTS.mk` be given by the anonymous-constructor terms below.

Note that typeclass synthesis does *not* see Mathlib's closure instances for an infimum
(`MorphismProperty.IsStableUnderComposition.inf` and friends) through this infimum: a goal
such as `isSeparatedFiniteType.IsMultiplicative` fails to synthesize even though each of
the three components has the instance. None of the material here needs those closure
properties -- the category structure on `FTS S` comes from `⊤` on the morphisms, not from
closure of the object property -- so they are not established; a consumer that needs one
must supply it.

`FTS S` is `CategoryTheory.MorphismProperty.Over` for that property with `⊤` on morphisms:
Mathlib's subcategory of `Over S` whose objects satisfy a property of the structure
morphism and whose morphisms satisfy a property of the underlying map, and `⊤` there is the
source's "morphisms of schemes over `S`" with no further condition.

## References

* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is separated and of finite type when it is separated, locally of
finite type and quasi-compact. -/
@[stacks 0F42 "the condition on the objects", sga "4 Vbis 5.3.1", sga "4 XVII 7.0.1"]
abbrev isSeparatedFiniteType : MorphismProperty Scheme.{u} :=
  @IsSeparated ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact

/-- A morphism of schemes is separated and of finite type if and only if it is separated,
locally of finite type and quasi-compact. -/
theorem isSeparatedFiniteType_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    isSeparatedFiniteType f ↔ IsSeparated f ∧ LocallyOfFiniteType f ∧ QuasiCompact f :=
  ⟨fun h ↦ ⟨h.1.1, h.1.2, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- The category of schemes separated and of finite type over `S`: its objects are the
schemes over `S` whose structure morphism is separated and of finite type, and its
morphisms are the morphisms of schemes over `S` between them. -/
@[stacks 0F42 "the category", sga "4 Vbis 5.3.1"]
abbrev FTS (S : Scheme.{u}) : Type (u + 1) :=
  isSeparatedFiniteType.Over ⊤ S

namespace FTS

variable {S : Scheme.{u}}

/-- The structure morphism of an object of `FTS S` is separated. -/
instance isSeparated_hom (X : FTS S) : IsSeparated X.hom := X.prop.1.1

/-- The structure morphism of an object of `FTS S` is locally of finite type. -/
instance locallyOfFiniteType_hom (X : FTS S) : LocallyOfFiniteType X.hom := X.prop.1.2

/-- The structure morphism of an object of `FTS S` is quasi-compact. -/
instance quasiCompact_hom (X : FTS S) : QuasiCompact X.hom := X.prop.2

/-- An object of `FTS S` is a scheme over `S` separated and of finite type over it. -/
@[sga "4 Vbis 5.3.1"]
abbrev mk {X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] : FTS S :=
  MorphismProperty.Over.mk ⊤ f ⟨⟨‹_›, ‹_›⟩, ‹_›⟩

end FTS

end AlgebraicGeometry
