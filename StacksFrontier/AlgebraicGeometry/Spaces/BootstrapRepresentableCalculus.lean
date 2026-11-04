module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Stability
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCriteria

/-!
# The calculus of morphisms representable by algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A morphism of presheaves on the big
fppf site of `S` is *representable by algebraic spaces* when each of its base changes along a
scheme-valued point of its target is an algebraic space over `S`
(`AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces`, Stacks 02YQ). This file proves
the closure properties of that notion which the Bootstrap chapter uses throughout: the notion
is stable under composition, and a property of morphisms of algebraic spaces carried by such a
morphism is carried by every base change of it.  Three further ones are imported here rather
than restated: base changing an algebraic space along such a morphism gives an algebraic
space, which is Stacks 03XY and is
`AlgebraicGeometry.Space.isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces`; the
source of such a morphism is an algebraic space as soon as its target is, which is
Stacks 02YS and is `AlgebraicGeometry.isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces`;
and the relative diagonal of such a morphism is representable by objects of the site — the
strengthening of Stacks 05LA from representability by algebraic spaces to representability by
schemes — which is
`AlgebraicGeometry.relativelyRepresentable_pullback_diagonal_of_isRepresentableByAlgebraicSpaces`.
The last two live in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentableByAlgebraicSpaces.lean`.

## Main results

* `AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces.comp` is Stacks 03Y1:
  representability by algebraic spaces is stable under composition. Untagged; the 03Y1 citation
  is on `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_comp`, which states the same
  thing.
* `AlgebraicGeometry.Space.HasProperty.of_isPullback` is Stacks 046F: in a fibre square of
  presheaves whose right-hand column is representable by algebraic spaces and has a property
  `P` of morphisms of algebraic spaces, the left-hand column is representable by algebraic
  spaces and has `P`.

## Implementation notes

**The property in Stacks 046F.** Stacks states 046F for a property as in Definition 03XZ,
that is one stable under base change and fppf local on the base. Only invariance under
isomorphism is used, so that is the hypothesis here; the statement is therefore more general
than the source's. Its conclusion includes representability by algebraic spaces of the base
change, which is `AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces.of_isPullback`
(Stacks 03Y0), supplied as the representability argument of
`AlgebraicGeometry.Space.HasProperty`.

## References

* [Stacks Project, Tag 02YQ](https://stacks.math.columbia.edu/tag/02YQ)
* [Stacks Project, Tag 02YS](https://stacks.math.columbia.edu/tag/02YS)
* [Stacks Project, Tag 03XY](https://stacks.math.columbia.edu/tag/03XY)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 03Y0](https://stacks.math.columbia.edu/tag/03Y0)
* [Stacks Project, Tag 03Y1](https://stacks.math.columbia.edu/tag/03Y1)
* [Stacks Project, Tag 046F](https://stacks.math.columbia.edu/tag/046F)
* [Stacks Project, Tag 05LA](https://stacks.math.columbia.edu/tag/05LA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 03Y1.** A composition of morphisms of presheaves on the big fppf site of `S` which
are representable by algebraic spaces is representable by algebraic spaces.

Untagged; the 03Y1 citation is on
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_comp` in
`StacksFrontier/AlgebraicGeometry/Spaces/Representable/Bootstrap/Stability.lean`, which states the
same thing. This is that statement in dot-notation form. -/
theorem IsRepresentableByAlgebraicSpaces.comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G} {b : G ⟶ H}
    (ha : IsRepresentableByAlgebraicSpaces B S hS a)
    (hb : IsRepresentableByAlgebraicSpaces B S hS b) :
    IsRepresentableByAlgebraicSpaces B S hS (a ≫ b) := by
  intro U ξ
  have hpaste := (IsPullback.of_hasPullback (pullback.snd ξ b) a).paste_horiz
    (IsPullback.of_hasPullback ξ b)
  exact (isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces B S hS a
    (pullback.snd ξ b) ha (hb U ξ)).of_iso hpaste.isoPullback

/-- **Stacks 046F.** In a Cartesian square of presheaves on the big fppf site of `S` whose
right-hand column `a` is representable by algebraic spaces and has a property `P` of morphisms
of algebraic spaces over `S`, the left-hand column `a'` is representable by algebraic spaces
(Stacks 03Y0) and has `P`.

Only invariance of `P` under isomorphism is used, which is weaker than the two conditions
Stacks imposes on `P` in Definition 03XZ. -/
@[stacks 046F]
theorem HasProperty.of_isPullback {P : MorphismProperty (AlgebraicSpaces B S hS)}
    [P.RespectsIso] {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G} {g : G' ⟶ G}
    {k : F' ⟶ F} {a' : F' ⟶ G'} (sq : IsPullback k a' a g)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a) (h : HasProperty B S hS P a ha) :
    HasProperty B S hS P a' (IsRepresentableByAlgebraicSpaces.of_isPullback sq ha) := by
  intro U ξ
  have hpb : IsPullback (pullback.fst ξ a') (pullback.snd ξ a' ≫ k) (ξ ≫ g) a :=
    ((IsPullback.of_hasPullback ξ a').flip.paste_horiz sq).flip
  have heq : (ObjectProperty.homMk (pullback.fst ξ a') :
      (⟨pullback ξ a', IsRepresentableByAlgebraicSpaces.of_isPullback sq ha U ξ⟩ :
        AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) =
      (ObjectProperty.isoMk (P := fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
          IsAlgebraicSpace B S hS F)
        (X := ⟨pullback ξ a', IsRepresentableByAlgebraicSpaces.of_isPullback sq ha U ξ⟩)
        (Y := ⟨pullback (ξ ≫ g) a, ha U (ξ ≫ g)⟩) hpb.isoPullback).hom ≫
        ObjectProperty.homMk (pullback.fst (ξ ≫ g) a) :=
    ObjectProperty.hom_ext _ (by simp [ObjectProperty.homMk, ObjectProperty.isoMk])
  rw [heq]
  exact MorphismProperty.RespectsIso.precomp _ _ _ (h U (ξ ≫ g))

end AlgebraicGeometry.Space

end
