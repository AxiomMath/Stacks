module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RelativeDiagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# Cancelling the second factor of a composite representable by algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of fppf sheaves on the big fppf site of `S`. **Stacks 0AQ0** says that if `X`, `Y`
and `Z` are formal algebraic spaces and `f ≫ g` is representable by algebraic spaces, then so
is `f`.

The content is Stacks 0AMN: `f` is a base change of the relative diagonal of `g` along a
morphism out of a base change of `f ≫ g`, so `f` is representable by algebraic spaces as soon
as the relative diagonal of `g` is. What the formal algebraic space hypotheses are for is to
supply that one input, which is Stacks 0AN2; nothing else in the argument uses them, so the
statements below take an arbitrary morphism of fppf sheaves and the diagonal condition as a
hypothesis.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_of_comp`:
  **Stacks 0AQ0**, with the representability of the relative diagonal of `g` — Stacks 0AN2 —
  as a hypothesis.
* `AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_of_comp_of_isAffineFormal`:
  **Stacks 0AQ0** unconditionally when `Y` is an affine formal algebraic space, which is the
  case in which this library has Stacks 0AN2.
* `AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_of_comp_of_mono`:
  **Stacks 0AQ0** unconditionally when `g` is a monomorphism, whose relative diagonal is an
  isomorphism.

## Implementation notes

Stacks 0AN2 is stated for the sheafified Yoneda embedding of the big fppf site, and concludes
representability *by objects of the site*, whereas Stacks 0AMN consumes representability *by
algebraic spaces* of the relative diagonal of the underlying morphism of presheaves. Two
bridges are therefore needed and are proved here.

The first is that a morphism of fppf sheaves representable by objects of the site has an
underlying morphism of presheaves representable by algebraic spaces. A scheme-valued point of
the target is a morphism out of a universe-lifted representable presheaf, and over the
subcanonical big fppf site that presheaf underlies a sheaf isomorphic to a sheafified
representable, so the point is transported to the sheaf category, where representability
supplies a cartesian square; the forgetful functor to presheaves preserves fibre products, so
the square stays cartesian, and its apex is a universe-lifted representable, hence an
algebraic space.

The second is that the relative diagonal of a morphism of sheaves and the relative diagonal
of the underlying morphism of presheaves agree up to the comparison isomorphism between the
underlying presheaf of a fibre product of sheaves and the fibre product of the underlying
presheaves. Representability by algebraic spaces is unchanged by composing with an
isomorphism, that being a base change.

## References

* [Stacks Project, Tag 0AMN](https://stacks.math.columbia.edu/tag/0AMN)
* [Stacks Project, Tag 0AN2](https://stacks.math.columbia.edu/tag/0AN2)
* [Stacks Project, Tag 0AQ0](https://stacks.math.columbia.edu/tag/0AQ0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### From representability by objects of the site to representability by algebraic spaces -/

/-- A morphism of fppf sheaves on the big fppf site of `S` which is representable by objects of
the site has an underlying morphism of presheaves which is representable by algebraic spaces
over `S`: a cartesian square in the sheaf category stays cartesian on underlying presheaves,
and a universe-lifted representable presheaf is an algebraic space. -/
theorem isRepresentableByAlgebraicSpacesULift_hom_of_relativelyRepresentable
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable f) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom := by
  have _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let e := Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)
  intro U ξ
  -- Transport the scheme-valued point `ξ` into the sheaf category.
  let ξ₀ : (GrothendieckTopology.uliftYoneda.{u + 1} (BigFppfOver.topology B S hS)).obj U ⟶ Y :=
    ObjectProperty.homMk ξ
  obtain ⟨V, snd, fst, hpb⟩ := hf ((e.app U).hom ≫ ξ₀)
  -- The point factors through the comparison isomorphism at `U`.
  have _ : IsIso (pullback.snd ((e.app U).hom).hom (pullback.fst ξ f.hom)) :=
    (IsPullback.of_hasPullback ((e.app U).hom).hom (pullback.fst ξ f.hom)).isIso_snd_of_isIso
      ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso (e.app U)).isIso_hom
  have hpaste := (IsPullback.of_hasPullback ((e.app U).hom).hom
    (pullback.fst ξ f.hom)).flip.paste_horiz (IsPullback.of_hasPullback ξ f.hom).flip
  exact Space.isAlgebraicSpaceULift_of_iso B S hS
    (((hpaste.isoIsPullback _ _
      (hpb.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))))).trans
      ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso (e.app V))).symm.trans
      (asIso (pullback.snd ((e.app U).hom).hom (pullback.fst ξ f.hom))))
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS V)

/-! ### The diagonal of a morphism of sheaves and of the underlying morphism of presheaves -/

/-- Representability by algebraic spaces of the relative diagonal of the underlying morphism of
presheaves follows from that of the underlying morphism of the relative diagonal: the forgetful
functor to presheaves preserves fibre products, so the two differ by composition with the
comparison isomorphism for the relative self-product, which is a base change. -/
theorem isRepresentableByAlgebraicSpacesULift_diagonal_hom
    {Y Z : FppfSheaf B S hS} (g : Y ⟶ Z)
    (hg : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (Limits.pullback.diagonal g).hom) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (Limits.pullback.diagonal g.hom) := by
  have hmap : IsPullback (Limits.pullback.fst g g).hom (Limits.pullback.snd g g).hom
      g.hom g.hom :=
    (IsPullback.of_hasPullback g g).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  have heq : (Limits.pullback.diagonal g).hom ≫ hmap.isoPullback.hom =
      Limits.pullback.diagonal g.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, hmap.isoPullback_hom_fst, pullback.diagonal_fst]
      exact congrArg (fun m : Y ⟶ Y => m.hom) (pullback.diagonal_fst g)
    · rw [Category.assoc, hmap.isoPullback_hom_snd, pullback.diagonal_snd]
      exact congrArg (fun m : Y ⟶ Y => m.hom) (pullback.diagonal_snd g)
  refine Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS (𝟙 Y.obj)
    (Limits.pullback.diagonal g.hom) (Limits.pullback.diagonal g).hom
    hmap.isoPullback.inv (IsPullback.of_horiz_isIso ⟨?_⟩) hg
  rw [Category.id_comp, ← heq, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-! ### Cancellation -/

/-- The cancellation engine behind Stacks 0AQ0. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of
fppf sheaves on the big fppf site of `S`. If `f ≫ g` is representable by algebraic spaces and
the relative diagonal of `g` is representable by objects of the site, then `f` is representable
by algebraic spaces.

**No tag is attached**, because `hdiag` is undischarged here: it is precisely Stacks 0AN2 for
`g`, so a registration on this declaration would claim 0AQ0 while assuming a whole other tag.
The tag sits on the three declarations that discharge it -- `…_of_comp_of_isAffineFormal` and
`…_of_comp_of_mono` below, and for an arbitrary formal algebraic space
`isRepresentableByAlgebraicSpacesULift_of_comp_of_isFormalAlgebraicSpace` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType`, the one module importing both this and
the module proving 0AN2. -/
theorem isRepresentableByAlgebraicSpacesULift_of_comp {X Y Z : FppfSheaf B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hdiag : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (Limits.pullback.diagonal g))
    (hcomp : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f.hom ≫ g.hom)) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom :=
  Space.isRepresentableByAlgebraicSpacesULift_of_comp B S hS f.hom g.hom
    (isRepresentableByAlgebraicSpacesULift_diagonal_hom B S hS g
      (isRepresentableByAlgebraicSpacesULift_hom_of_relativelyRepresentable B S hS _ hdiag))
    hcomp

/-- **Stacks 0AQ0** when the intermediate sheaf is an affine formal algebraic space. Let
`f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of fppf sheaves on the big fppf site of `S` with `Y`
an affine formal algebraic space. If `f ≫ g` is representable by algebraic spaces then so is
`f`, the relative diagonal of `g` being representable by Stacks 0AN2. -/
@[stacks 0AQ0 "for a second morphism whose source is an affine formal algebraic space"]
theorem isRepresentableByAlgebraicSpacesULift_of_comp_of_isAffineFormal
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hcomp : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f.hom ≫ g.hom)) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom :=
  isRepresentableByAlgebraicSpacesULift_of_comp B S hS f g
    (relativelyRepresentable_pullback_diagonal_of_isAffineFormal B S hS g hY) hcomp

/-- **Stacks 0AQ0** when the second morphism is a monomorphism. Its relative diagonal is then
an isomorphism, hence representable by objects of the site. -/
@[stacks 0AQ0 "for a second morphism which is a monomorphism of fppf sheaves"]
theorem isRepresentableByAlgebraicSpacesULift_of_comp_of_mono {X Y Z : FppfSheaf B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g]
    (hcomp : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f.hom ≫ g.hom)) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom :=
  isRepresentableByAlgebraicSpacesULift_of_comp B S hS f g
    (Functor.relativelyRepresentable.of_isIso _ (Limits.pullback.diagonal g)) hcomp

end AlgebraicGeometry.FormalSpace

end
