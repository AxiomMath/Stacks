module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Composition

/-!
# The source square and the target square of a morphism of groupoids in algebraic spaces

Let `φ : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over an algebraic space `B` over a scheme `S` of a big fppf site, in the sense of Stacks 043W
part (2), written `f : U ⟶ U'` on objects and `f : R ⟶ R'` on arrows. It gives rise to two
squares,

```
R ⟶ R'          R ⟶ R'
|    |           |    |
s    s'          t    t'
v    v           v    v
U ⟶ U'          U ⟶ U'
```

and this file proves that either one is cartesian as soon as the other is: the inversion of a
groupoid interchanges the source and the target map, is an involution, and commutes with `φ`, so
the two squares differ only by composing two of their sides with isomorphisms.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.isPullback_target_of_isPullback_source` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.isPullback_source_of_isPullback_target`: the
  two implications.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.isPullback_target_iff_isPullback_source`: the
  resulting equivalence.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidInverse_groupoidInverse` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isIso_groupoidInverse`: the inversion
  `i : R ⟶ R` of a groupoid in algebraic spaces is an involution, hence an isomorphism.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.mapArrows_comp_groupoidInverse`: a morphism of
  groupoids commutes with the two inversions.
* `Deformation.inverseArrow_inverseArrow` and
  `Deformation.GroupoidInFunctors.Hom.mapArrows_app_inverseArrow`: the same two facts for a
  groupoid in functors, which is where they are proved.

## What this is for

Stacks 04ZN takes as its hypothesis that the square formed by the two **source** maps is
cartesian, and its proof begins by applying the inversions of the two groupoids to obtain the
square formed by the two **target** maps. That first step is what is proved here, and for an
arbitrary morphism of groupoids in algebraic spaces rather than only for the restriction of a
groupoid along an invariant subspace, which is the one case
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/InvariantRestrictionCartesian.lean` settles (it
proves both squares separately, from the two one-sided invariance conditions).

The target square is what the two conditional results of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/FunctorialityAuxiliarySpaces.lean` assume,
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isIso_toAuxObjects` and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_auxSource_of_isPullback_target`, which
are the identifications `(t, f) : R ≅ U''` and `R'' = R ×_{s, U, t} R` of the proof of
Stacks 04ZN. Two purely formal steps still separate the conclusion below from their hypothesis,
and neither is carried out here: those two state their square in the category of algebraic
spaces over `S` rather than in presheaves, which a full subcategory inclusion reflects
(`CategoryTheory.IsPullback.of_map_of_faithful`), and they state it transposed, with the two
target maps horizontal (`CategoryTheory.IsPullback.flip`).

Nothing here mentions quotient stacks, and nothing here carries the tag of Stacks 04ZN: the
content of that tag is the 2-fibre product property of the resulting square of quotient stacks,
which this library does not prove.

## Implementation notes

The inversion of a groupoid in algebraic spaces is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidInverse`, whose value at a point of a test
object is `Deformation.inverseArrow`, the inverse taken in the evaluated groupoid. Both facts
needed about it — that it is an involution, and that it commutes with a morphism of groupoids —
are therefore statements about one evaluated groupoid at a time, and both are proved by
transporting along `Deformation.GroupoidInFunctors.evaluationArrowEquiv`: the inverse of an
arrow, read as a point of the arrow functor, is the point underlying the categorical inverse, and
a morphism of groupoids evaluates to a functor, which preserves inverses.

`Deformation.inverseArrow_eq` is the transport principle that makes this usable. The inverse
arrow is *defined* through the identifications of the endpoints of `a` with `s(a)` and `t(a)` on
the nose; naming arbitrary identifications instead, as that lemma does, is what lets the inverse
of an already-inverted arrow, whose endpoints are known only up to the two equations
`s(i(a)) = t(a)` and `t(i(a)) = s(a)`, be written as a categorical inverse at all. The same
principle is available, for the big fppf site only, as
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.inverseArrow_transport` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/InertiaGroupoid.lean`; it is restated here for an
arbitrary base category, which is the generality the two proofs below are carried out in, and so
that this file does not depend on the inertia groupoid.

Once those are in hand the two squares are related without any further computation. The square
with `f : R ⟶ R'` on both horizontal sides and the two inversions on the vertical ones commutes,
because the arrow map respects the inversions, and its two vertical maps are isomorphisms, so it
is cartesian by `CategoryTheory.IsPullback.of_vert_isIso`. Pasting it on top of the source square
(`CategoryTheory.IsPullback.paste_vert`) gives a cartesian square whose vertical maps are
`i ≫ s = t` and `i' ≫ s' = t'`, which is the target square; pasting it on top of the target
square gives the source square the same way.

No identity morphism and no composite of the arrow maps appears, which is deliberate: the two
spellings `G.arrows.obj` and `G.toGroupoidInFunctors.arrows` of the arrow presheaf are
definitionally but not syntactically equal, so a statement mixing them — as `𝟙 G.objects.obj`
composed with a map out of `G.toGroupoidInFunctors.objects` does — is beyond the reach of
`rw [Category.comp_id]`. Here the only rewriting done is by `groupoidInverse_source` and
`groupoidInverse_target`, whose left-hand sides appear verbatim in the pasted square.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Deformation

universe u v w

variable {D : Type u} [Category.{v} D]

/-- The inverse of an arrow of an evaluated groupoid, read through *arbitrary* identifications
of the endpoints of the arrow rather than the definitional ones. This is the form in which
`Deformation.inverseArrow` can be applied to an arrow whose endpoints are known only up to two
equations, which is what both results below need. -/
theorem inverseArrow_eq (K : GroupoidInFunctors.{u, v, w} D) (T : D)
    {x y : K.Evaluation T} (a : K.arrows.obj T)
    (hx : K.source.app T a = x) (hy : K.target.app T a = y) :
    inverseArrow K T a =
      (K.evaluationArrowEquiv T y x
        (Groupoid.inv ((K.evaluationArrowEquiv T x y).symm ⟨a, hx, hy⟩))).1 := by
  cases hx
  cases hy
  unfold inverseArrow
  rfl

/-- The inverse of the point of the arrow functor underlying an arrow of an evaluated groupoid is
the point underlying the categorical inverse. This is `Deformation.inverseArrow_eq` with the
arrow, rather than the point, named; every statement below is first proved in this form and then
specialised, because an arbitrary point `a` occurs in the *type* of the arrow it names and so
cannot be substituted for. -/
theorem inverseArrow_val (K : GroupoidInFunctors.{u, v, w} D) (T : D)
    {x y : K.Evaluation T} (q : x ⟶ y) :
    inverseArrow K T (K.evaluationArrowEquiv T x y q).1 =
      (K.evaluationArrowEquiv T y x (Groupoid.inv q)).1 :=
  (inverseArrow_eq K T (K.evaluationArrowEquiv T x y q).1
        (K.evaluationArrowEquiv T x y q).2.1 (K.evaluationArrowEquiv T x y q).2.2).trans
    (congrArg (fun r : x ⟶ y => (K.evaluationArrowEquiv T y x (Groupoid.inv r)).1)
      ((Equiv.symm_apply_eq _).2 (Subtype.ext rfl)))

/-- Inversion of the arrows of an evaluated groupoid is an involution, for an arrow named by a
morphism of the evaluated groupoid. -/
theorem inverseArrow_inverseArrow_val (K : GroupoidInFunctors.{u, v, w} D) (T : D)
    {x y : K.Evaluation T} (q : x ⟶ y) :
    inverseArrow K T (inverseArrow K T (K.evaluationArrowEquiv T x y q).1) =
      (K.evaluationArrowEquiv T x y q).1 := by
  rw [inverseArrow_val, inverseArrow_val, Groupoid.inv_eq_inv, Groupoid.inv_eq_inv,
    IsIso.inv_inv]

/-- A property of the arrows of an evaluated groupoid that holds for every arrow named by a
morphism of the evaluated groupoid holds for every arrow. -/
private theorem forall_arrow_of_forall_evaluationArrowEquiv
    (K : GroupoidInFunctors.{u, v, w} D) (T : D) (P : K.arrows.obj T → Prop)
    (h : ∀ {x y : K.Evaluation T} (q : x ⟶ y), P (K.evaluationArrowEquiv T x y q).1)
    (a : K.arrows.obj T) : P a := by
  simpa using
    h ((K.evaluationArrowEquiv T (K.source.app T a) (K.target.app T a)).symm ⟨a, rfl, rfl⟩)

/-- Inversion of the arrows of an evaluated groupoid is an involution. -/
theorem inverseArrow_inverseArrow (K : GroupoidInFunctors.{u, v, w} D) (T : D)
    (a : K.arrows.obj T) : inverseArrow K T (inverseArrow K T a) = a :=
  forall_arrow_of_forall_evaluationArrowEquiv K T
    (fun a => inverseArrow K T (inverseArrow K T a) = a) (inverseArrow_inverseArrow_val K T) a

/-- A morphism of groupoids in functors commutes with the inversion of the arrows, for an arrow
named by a morphism of the evaluated groupoid: evaluation of a morphism is a functor, and a
functor preserves inverses. -/
theorem GroupoidInFunctors.Hom.mapArrows_app_inverseArrow_val
    {K L : GroupoidInFunctors.{u, v, w} D} (F : GroupoidInFunctors.Hom K L) (T : D)
    {x y : K.Evaluation T} (q : x ⟶ y) :
    F.mapArrows.app T (inverseArrow K T (K.evaluationArrowEquiv T x y q).1) =
      inverseArrow L T (F.mapArrows.app T (K.evaluationArrowEquiv T x y q).1) := by
  have hinv : (F.evaluation T).map (Groupoid.inv q) =
      Groupoid.inv ((F.evaluation T).map q) := by
    rw [Groupoid.inv_eq_inv, Groupoid.inv_eq_inv, Functor.map_inv]
  rw [inverseArrow_val, ← GroupoidInFunctors.Hom.evaluation_map_arrow F T (Groupoid.inv q),
    ← GroupoidInFunctors.Hom.evaluation_map_arrow F T q, inverseArrow_val, hinv]

/-- A morphism of groupoids in functors commutes with the inversion of the arrows. -/
theorem GroupoidInFunctors.Hom.mapArrows_app_inverseArrow
    {K L : GroupoidInFunctors.{u, v, w} D} (F : GroupoidInFunctors.Hom K L) (T : D)
    (a : K.arrows.obj T) :
    F.mapArrows.app T (inverseArrow K T a) = inverseArrow L T (F.mapArrows.app T a) :=
  forall_arrow_of_forall_evaluationArrowEquiv K T
    (fun a => F.mapArrows.app T (inverseArrow K T a) = inverseArrow L T (F.mapArrows.app T a))
    (GroupoidInFunctors.Hom.mapArrows_app_inverseArrow_val F T) a

end Deformation

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The inversion `i : R ⟶ R` of a groupoid in algebraic spaces is an involution. -/
theorem groupoidInverse_groupoidInverse (G : GroupoidInAlgebraicSpaces C S hS B) :
    groupoidInverse G ≫ groupoidInverse G = 𝟙 G.arrows.obj := by
  ext V a
  change (groupoidInverse G).app V ((groupoidInverse G).app V a) = a
  rw [groupoidInverse_app, groupoidInverse_app]
  exact Deformation.inverseArrow_inverseArrow G.toGroupoidInFunctors V a

/-- The inversion `i : R ⟶ R` of a groupoid in algebraic spaces is an isomorphism, being an
involution. -/
instance isIso_groupoidInverse (G : GroupoidInAlgebraicSpaces C S hS B) :
    IsIso (groupoidInverse G) :=
  ⟨⟨groupoidInverse G, groupoidInverse_groupoidInverse G, groupoidInverse_groupoidInverse G⟩⟩

/-- A morphism of groupoids in algebraic spaces commutes with the two inversions. -/
theorem Hom.mapArrows_comp_groupoidInverse {G H : GroupoidInAlgebraicSpaces C S hS B}
    (φ : Hom G H) :
    φ.toGroupoidHom.mapArrows ≫ groupoidInverse H =
      groupoidInverse G ≫ φ.toGroupoidHom.mapArrows := by
  have h : ∀ (V : (BigFppfOver C S hS)ᵒᵖ) (a : G.toGroupoidInFunctors.arrows.obj V),
      (groupoidInverse H).app V (φ.toGroupoidHom.mapArrows.app V a) =
        φ.toGroupoidHom.mapArrows.app V ((groupoidInverse G).app V a) := by
    intro V a
    have e₁ : (groupoidInverse H).app V (φ.toGroupoidHom.mapArrows.app V a) =
        Deformation.inverseArrow H.toGroupoidInFunctors V
          (φ.toGroupoidHom.mapArrows.app V a) := groupoidInverse_app H V _
    have e₂ : Deformation.inverseArrow H.toGroupoidInFunctors V
          (φ.toGroupoidHom.mapArrows.app V a) =
        φ.toGroupoidHom.mapArrows.app V
          (Deformation.inverseArrow G.toGroupoidInFunctors V a) :=
      (Deformation.GroupoidInFunctors.Hom.mapArrows_app_inverseArrow φ.toGroupoidHom V a).symm
    have e₃ : φ.toGroupoidHom.mapArrows.app V
          (Deformation.inverseArrow G.toGroupoidInFunctors V a) =
        φ.toGroupoidHom.mapArrows.app V ((groupoidInverse G).app V a) :=
      congrArg (fun z => φ.toGroupoidHom.mapArrows.app V z)
        (groupoidInverse_app G V a).symm
    exact e₁.trans (e₂.trans e₃)
  ext V a
  exact h V a

/-- The square formed twice by the arrow map of a morphism of groupoids in algebraic spaces and
twice by an inversion is cartesian: it commutes because the arrow map respects the inversions, and
both of its vertical maps are isomorphisms. -/
theorem Hom.isPullback_groupoidInverse {G H : GroupoidInAlgebraicSpaces C S hS B} (φ : Hom G H) :
    IsPullback (show G.arrows.obj ⟶ H.arrows.obj from φ.toGroupoidHom.mapArrows)
      (groupoidInverse G) (groupoidInverse H)
      (show G.arrows.obj ⟶ H.arrows.obj from φ.toGroupoidHom.mapArrows) :=
  IsPullback.of_vert_isIso ⟨Hom.mapArrows_comp_groupoidInverse φ⟩

/-- If the square formed by the arrow map of a morphism of groupoids in algebraic spaces, its
object map and the two **source** maps is cartesian, then so is the square formed by the same two
maps and the two **target** maps. This is the first step of the proof of Stacks 04ZN. -/
theorem Hom.isPullback_target_of_isPullback_source
    {G H : GroupoidInAlgebraicSpaces C S hS B} (φ : Hom G H)
    (hs : IsPullback φ.toGroupoidHom.mapArrows G.source.hom H.source.hom
      φ.toGroupoidHom.mapObjects) :
    IsPullback φ.toGroupoidHom.mapArrows G.target.hom H.target.hom
      φ.toGroupoidHom.mapObjects := by
  have hs' : IsPullback (show G.arrows.obj ⟶ H.arrows.obj from φ.toGroupoidHom.mapArrows)
      G.source.hom H.source.hom φ.toGroupoidHom.mapObjects := hs
  have key := (Hom.isPullback_groupoidInverse φ).paste_vert hs'
  rw [groupoidInverse_source G, groupoidInverse_source H] at key
  exact key

/-- The converse of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.isPullback_target_of_isPullback_source`, by the
same argument. -/
theorem Hom.isPullback_source_of_isPullback_target
    {G H : GroupoidInAlgebraicSpaces C S hS B} (φ : Hom G H)
    (ht : IsPullback φ.toGroupoidHom.mapArrows G.target.hom H.target.hom
      φ.toGroupoidHom.mapObjects) :
    IsPullback φ.toGroupoidHom.mapArrows G.source.hom H.source.hom
      φ.toGroupoidHom.mapObjects := by
  have ht' : IsPullback (show G.arrows.obj ⟶ H.arrows.obj from φ.toGroupoidHom.mapArrows)
      G.target.hom H.target.hom φ.toGroupoidHom.mapObjects := ht
  have key := (Hom.isPullback_groupoidInverse φ).paste_vert ht'
  rw [groupoidInverse_target G, groupoidInverse_target H] at key
  exact key

/-- For a morphism of groupoids in algebraic spaces the source square is cartesian if and only
if the target square is. -/
theorem Hom.isPullback_target_iff_isPullback_source
    {G H : GroupoidInAlgebraicSpaces C S hS B} (φ : Hom G H) :
    IsPullback φ.toGroupoidHom.mapArrows G.target.hom H.target.hom
        φ.toGroupoidHom.mapObjects ↔
      IsPullback φ.toGroupoidHom.mapArrows G.source.hom H.source.hom
        φ.toGroupoidHom.mapObjects :=
  ⟨φ.isPullback_source_of_isPullback_target, φ.isPullback_target_of_isPullback_source⟩

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
