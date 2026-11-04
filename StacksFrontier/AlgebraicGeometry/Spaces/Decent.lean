module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactMonomorphicFieldRepresentative

/-!
# Decent algebraic spaces, absolutely and relatively

An algebraic space over a scheme `S` is *decent* when every one of its points satisfies the
equivalent conditions of Stacks 03JV; equivalently, when it has property `(γ)` of
Stacks 03JX. It has property `(β)` of Stacks 03JX when every one of its points satisfies the
equivalent conditions of Stacks 03JU. A *morphism* of algebraic spaces has either property
when every base change of it along a scheme-valued point of its target has the corresponding
absolute property.

## Main definitions

* `AlgebraicGeometry.Space.HasFiniteRelationFibersAtEveryPoint` is property `(β)` of an
  algebraic space, and `AlgebraicGeometry.Space.IsDecentSpace` is decency of an algebraic
  space.
* `AlgebraicGeometry.Space.HasPropertyBeta` and `AlgebraicGeometry.Space.IsDecent` are the
  two relative conditions, for a morphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.IsDecentSpace.hasMonomorphicFieldRepresentative` and
  `AlgebraicGeometry.Space.HasFiniteRelationFibersAtEveryPoint.hasFiniteRelationFiberAt`
  read off the pointwise content of the two absolute conditions, and
  `AlgebraicGeometry.Space.IsDecent.hasMonomorphicFieldRepresentative`,
  `AlgebraicGeometry.Space.HasPropertyBeta.hasFiniteRelationFiberAt` do the same for the
  two relative ones.
* `AlgebraicGeometry.Space.isDecentSpace_of_isEmpty_points` and
  `AlgebraicGeometry.Space.hasFiniteRelationFibersAtEveryPoint_of_isEmpty_points`: both
  absolute conditions are vacuous on a presheaf with no points.

## Implementation notes

The two renames. Stacks 03I8 and 03KZ both call their condition "decent", one for a space
and one for a morphism, so the *object*-level predicate carries the suffix `Space`:
`IsDecentSpace` for 03I8 against `IsDecent` for 03KZ. This is exactly the convention F4 fixed
for `AlgebraicGeometry.Space.IsQuasiCompactSpace` (03E3, a space) against
`AlgebraicGeometry.Space.IsQuasiCompact` (03HE, a morphism). The "reasonable" and "very
reasonable" pairs of the same two tags carry the same rename; see
`StacksFrontier/AlgebraicGeometry/Spaces/Reasonable.lean`.

What the two absolute conditions are spelled as. Stacks 03I8 defines decency by "the
equivalent conditions of Lemma 03JV hold at every point" and 03JX's property `(β)` by "the
equivalent conditions of Lemma 03JU hold at every point", so each formalization must pick
one of those conditions. `IsDecentSpace` uses condition (4) of 03JV
(`AlgebraicGeometry.Space.HasQuasiCompactMonomorphicFieldRepresentative`) and
`HasFiniteRelationFibersAtEveryPoint` uses condition (1) of 03JU
(`AlgebraicGeometry.Space.HasFiniteRelationFiberAt`). Stacks 03JU is proved — its four
conditions are compared in
`StacksFrontier/AlgebraicGeometry/Spaces/RelationFibers.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/MonomorphicFieldRepresentative.lean`, so
`HasFiniteRelationFibersAtEveryPoint` agrees with every other formulation of property `(β)`.
**Stacks 03JV is not proved in this repository**: only its condition (4) is stated, so
`IsDecentSpace` agrees with the other formulations of decency modulo equivalences that are
still open here, and a proof of 03JV should record the resulting `Iff` beside this name.

The relative conditions quantify over *all* morphisms from a representable presheaf into the
target, as the source does — not over a chosen cover of it — and `T ×_Y X` is the pullback in
the presheaf category. All four predicates are kept as `abbrev`s, as in the source statements, so
their quantifiers and the absolute predicates underneath are directly available to
base-change and composition statements.

The remaining parts of 03I8 and 03KZ — "reasonable" and "very reasonable", absolutely and
relatively — are in `StacksFrontier/AlgebraicGeometry/Spaces/Reasonable.lean`, as
`AlgebraicGeometry.Space.IsReasonableSpace`,
`AlgebraicGeometry.Space.IsVeryReasonableSpace`, `AlgebraicGeometry.Space.IsReasonable` and
`AlgebraicGeometry.Space.IsVeryReasonable`. They are kept apart from this file because the
two notions have disjoint and substantial dependencies: decency rests on the points and
relation-fibres layer imported here, while reasonableness rests on Stacks 03JL
(`AlgebraicGeometry.Space.HasUniversallyBoundedFibers`) and through it on the finite
locally free layer, which no consumer of decency needs.

## References

* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03KZ](https://stacks.math.columbia.edu/tag/03KZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The absolute conditions -/

section Absolute

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 03KZ, property `(β)` for an algebraic space.** This is property `(β)` of
Stacks 03JX: every point of `F` satisfies the equivalent conditions of Stacks 03JU, taken
here in the form of condition (1), finiteness of one relation fibre in some étale chart. -/
@[stacks 03KZ "property beta for an algebraic space"]
abbrev HasFiniteRelationFibersAtEveryPoint : Prop :=
  ∀ x : points B S hS F, HasFiniteRelationFiberAt B S hS F x

/-- **Stacks 03I8, decent.** An algebraic space over `S` is *decent* when every one of its
points satisfies the equivalent conditions of Stacks 03JV, taken here in the form of
condition (4): a quasi-compact monomorphism from the spectrum of a field. -/
@[stacks 03I8 "decent"]
abbrev IsDecentSpace : Prop :=
  ∀ x : points B S hS F, HasQuasiCompactMonomorphicFieldRepresentative B S hS F x

/-- Property `(β)` gives condition (1) of Stacks 03JU at every point. -/
theorem HasFiniteRelationFibersAtEveryPoint.hasFiniteRelationFiberAt
    (h : HasFiniteRelationFibersAtEveryPoint B S hS F) (x : points B S hS F) :
    HasFiniteRelationFiberAt B S hS F x := h x

/-- A decent algebraic space has a monomorphic field-valued representative at every point,
which is condition (4) of Stacks 03JU. -/
theorem IsDecentSpace.hasMonomorphicFieldRepresentative
    (h : IsDecentSpace B S hS F) (x : points B S hS F) :
    HasMonomorphicFieldRepresentative B S hS F x :=
  (h x).hasMonomorphicFieldRepresentative B S hS F

/-- A presheaf with no points has property `(β)` vacuously. -/
theorem hasFiniteRelationFibersAtEveryPoint_of_isEmpty_points
    (h : IsEmpty (points B S hS F)) :
    HasFiniteRelationFibersAtEveryPoint B S hS F :=
  fun x ↦ h.elim x

/-- A presheaf with no points is decent vacuously. -/
theorem isDecentSpace_of_isEmpty_points (h : IsEmpty (points B S hS F)) :
    IsDecentSpace B S hS F :=
  fun x ↦ h.elim x

end Absolute

/-! ### The relative conditions -/

section Relative

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03KZ, property `(β)` for a morphism.** A morphism of algebraic spaces over `S`
has property `(β)` when every base change of it along a morphism from a representable
presheaf into its target has property `(β)`. -/
@[stacks 03KZ "property beta for a morphism"]
abbrev HasPropertyBeta (f : X ⟶ Y) : Prop :=
  ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
    HasFiniteRelationFibersAtEveryPoint B S hS (pullback g f)

/-- **Stacks 03KZ, decent morphism.** A morphism of algebraic spaces over `S` is *decent*
when every base change of it along a morphism from a representable presheaf into its target
is a decent algebraic space. -/
@[stacks 03KZ "decent morphism"]
abbrev IsDecent (f : X ⟶ Y) : Prop :=
  ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
    IsDecentSpace B S hS (pullback g f)

/-- A morphism with property `(β)` has condition (1) of Stacks 03JU at every point of every
represented base change. -/
theorem HasPropertyBeta.hasFiniteRelationFiberAt {f : X ⟶ Y} (h : HasPropertyBeta B S hS f)
    (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y)
    (x : points B S hS (pullback g f)) :
    HasFiniteRelationFiberAt B S hS (pullback g f) x := h T g x

/-- A decent morphism has a monomorphic field-valued representative at every point of every
represented base change, which is condition (4) of Stacks 03JU. -/
theorem IsDecent.hasMonomorphicFieldRepresentative {f : X ⟶ Y} (h : IsDecent B S hS f)
    (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y)
    (x : points B S hS (pullback g f)) :
    HasMonomorphicFieldRepresentative B S hS (pullback g f) x :=
  (h T g).hasMonomorphicFieldRepresentative B S hS (pullback g f) x

end Relative

end AlgebraicGeometry.Space

end
