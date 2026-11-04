module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Finite type and quasi-finite morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is *locally of finite type* when the
scheme morphism it induces in every commuting square of étale charts is locally of finite
type, and *of finite type* when it is in addition quasi-compact. It is *locally
quasi-finite* when those induced scheme morphisms are locally of finite type and locally
quasi-finite, and *quasi-finite* when it is in addition quasi-compact. It is *of finite
type at* a point `x` of its source, respectively *quasi-finite at* `x`, when some open
subspace of the source containing `x` is locally of finite type, respectively locally
quasi-finite, over the target.

## Main definitions

* `AlgebraicGeometry.Space.IsLocallyOfFiniteType` and
  `AlgebraicGeometry.Space.IsFiniteType` are local finite type and finite type.
* `AlgebraicGeometry.Space.IsLocallyQuasiFinite` and
  `AlgebraicGeometry.Space.IsQuasiFinite` are local quasi-finiteness and quasi-finiteness.
* `AlgebraicGeometry.Space.IsFiniteTypeAt` and
  `AlgebraicGeometry.Space.IsQuasiFiniteAt` are the pointwise versions, part (2) of
  Stacks 03XF and part (2) of Stacks 03XJ.

## Main results

* `AlgebraicGeometry.Space.isFiniteTypeAt_of_isOpenSubspace` and
  `AlgebraicGeometry.Space.isQuasiFiniteAt_of_isOpenSubspace` are the introduction rules
  for the pointwise conditions: an open subspace which is locally of finite type,
  respectively locally quasi-finite, witnesses the condition at each of its points.
* `AlgebraicGeometry.Space.IsFiniteTypeAt.exists_mem_range_pointsMap` and
  `AlgebraicGeometry.Space.IsQuasiFiniteAt.exists_mem_range_pointsMap` restate the
  pointwise definitions with the point condition as a membership in the image of the open
  subspace on points.

## Implementation notes

The two local conditions are the every-étale-chart condition
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of Stacks 03MJ, applied to the
corresponding scheme-morphism property; their equivalence with the condition on one
surjective chart is Stacks 03MJ and follows from étale locality of those properties on
source and target. For schemes, local quasi-finiteness combines local finite type with
Mathlib's `AlgebraicGeometry.LocallyQuasiFinite` fibre condition, so the tested property
is the infimum of the two morphism properties. Quasi-compactness is
`AlgebraicGeometry.Space.IsQuasiCompact`, the morphism property of Stacks 03HE. All
definitions in this file are abbreviations, which exposes the chart and conjunction
characterizations, and the neighbourhood data of the pointwise conditions, directly to
clients.

In parts (2) of Stacks 03XF and 03XJ an open neighbourhood of `x` is an open subspace `U`
of the source in the sense of Stacks 02YU (`AlgebraicGeometry.Space.IsOpenSubspace`, a
subfunctor which is an algebraic space with an open-immersion inclusion) together with a
point of `|U|` mapping to `x` under `AlgebraicGeometry.Space.pointsMap` of the inclusion.
The source's `f|_{X'}` is the composite `U.ι ≫ f`.

## References

* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03XF, part (1).** A morphism of algebraic spaces over `S` is *locally of
finite type* when every commuting square of étale scheme charts induces a scheme morphism
which is locally of finite type. -/
@[stacks 03XF "part (1): locally of finite type", ega "I 6.6.2"]
abbrev IsLocallyOfFiniteType (f : X ⟶ Y) : Prop :=
  HoldsOnEveryEtaleChart B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty Scheme.{u}) f

/-- **Stacks 03XF, part (3).** A morphism of algebraic spaces over `S` is *of finite type*
when it is locally of finite type and quasi-compact. -/
@[stacks 03XF "part (3): finite type"]
abbrev IsFiniteType (f : X ⟶ Y) : Prop :=
  IsLocallyOfFiniteType B S hS f ∧ IsQuasiCompact B S hS f

/-- **Stacks 03XJ, part (1).** A morphism of algebraic spaces over `S` is *locally
quasi-finite* when every commuting square of étale scheme charts induces a scheme morphism
which is locally of finite type and locally quasi-finite. -/
@[stacks 03XJ "part (1): locally quasi-finite morphisms"]
abbrev IsLocallyQuasiFinite (f : X ⟶ Y) : Prop :=
  HoldsOnEveryEtaleChart B S hS
    ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) f

/-- **Stacks 03XJ, part (3).** A morphism of algebraic spaces over `S` is *quasi-finite*
when it is locally quasi-finite and quasi-compact. -/
@[stacks 03XJ "part (3): quasi-finite morphisms"]
abbrev IsQuasiFinite (f : X ⟶ Y) : Prop :=
  IsLocallyQuasiFinite B S hS f ∧ IsQuasiCompact B S hS f

/-! ### Finite type and quasi-finiteness at a point -/

/-- **Stacks 03XF, part (2).** A morphism of algebraic spaces over `S` is *of finite type at*
a point `x` of its source when some open subspace of the source containing `x` is locally of
finite type over the target. -/
@[stacks 03XF "part (2): finite type at a point"]
abbrev IsFiniteTypeAt (f : X ⟶ Y) (x : points B S hS X) : Prop :=
  ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
    ∃ x' : points B S hS U.toFunctor,
      pointsMap B S hS U.toFunctor U.ι x' = x ∧
        IsLocallyOfFiniteType B S hS (U.ι ≫ f)

/-- **Stacks 03XJ, part (2).** A morphism of algebraic spaces over `S` is *quasi-finite at*
a point `x` of its source when some open subspace of the source containing `x` is locally
quasi-finite over the target. -/
@[stacks 03XJ "part (2): quasi-finite at a point"]
abbrev IsQuasiFiniteAt (f : X ⟶ Y) (x : points B S hS X) : Prop :=
  ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
    ∃ x' : points B S hS U.toFunctor,
      pointsMap B S hS U.toFunctor U.ι x' = x ∧
        IsLocallyQuasiFinite B S hS (U.ι ≫ f)

/-- An open subspace of the source which is locally of finite type over the target witnesses
finite type at each of its points. -/
theorem isFiniteTypeAt_of_isOpenSubspace {f : X ⟶ Y} (U : Subfunctor X)
    (hU : IsOpenSubspace B S hS U) (hf : IsLocallyOfFiniteType B S hS (U.ι ≫ f))
    (x' : points B S hS U.toFunctor) :
    IsFiniteTypeAt B S hS f (pointsMap B S hS U.toFunctor U.ι x') :=
  ⟨U, hU, x', rfl, hf⟩

/-- A locally quasi-finite open subspace of the source witnesses quasi-finiteness at each
of its points. -/
theorem isQuasiFiniteAt_of_isOpenSubspace {f : X ⟶ Y} (U : Subfunctor X)
    (hU : IsOpenSubspace B S hS U) (hf : IsLocallyQuasiFinite B S hS (U.ι ≫ f))
    (x' : points B S hS U.toFunctor) :
    IsQuasiFiniteAt B S hS f (pointsMap B S hS U.toFunctor U.ι x') :=
  ⟨U, hU, x', rfl, hf⟩

/-- Finite type at a point, with the point condition read as a membership in the image of the
open subspace on points. -/
theorem IsFiniteTypeAt.exists_mem_range_pointsMap {f : X ⟶ Y} {x : points B S hS X}
    (h : IsFiniteTypeAt B S hS f x) :
    ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
      IsLocallyOfFiniteType B S hS (U.ι ≫ f) ∧
        x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  obtain ⟨U, hU, x', hx', hf⟩ := h
  exact ⟨U, hU, hf, x', hx'⟩

/-- Quasi-finiteness at a point, with the point condition read as a membership in the image
of the open subspace on points. -/
theorem IsQuasiFiniteAt.exists_mem_range_pointsMap {f : X ⟶ Y} {x : points B S hS X}
    (h : IsQuasiFiniteAt B S hS f x) :
    ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
      IsLocallyQuasiFinite B S hS (U.ι ≫ f) ∧
        x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  obtain ⟨U, hU, x', hx', hf⟩ := h
  exact ⟨U, hU, hf, x', hx'⟩

end AlgebraicGeometry.Space

end
