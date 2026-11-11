module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineUnconditional

/-!
# Sections of an algebraic space over a thickening-and-affine pushout

Let `i : X ⟶ X'` be a thickening and `f : X ⟶ Y` an affine morphism of schemes over `S`, and let
`Y' = Y ⨿_X X'` be their pushout.  Stacks 07SY says that the resulting square is a pushout in the
category of algebraic spaces over `S` as well.  This file records that conclusion in the shape its
consumers use: a *functor-of-points* statement.  For every algebraic space `P` over `S`, a
morphism out of `Y'` — equivalently, by Yoneda, a section of `P` over `Y'` — is the same thing as
a compatible pair consisting of a morphism out of `X'` and a morphism out of `Y`.

Both forms are stated as `ExistsUnique` rather than as an `IsPullback` of sets, because that is
how the gluing arguments consume them: a pair of sections is given and the glued section is
wanted, together with the fact that nothing else glues to the same pair.

## Main results

* `AlgebraicGeometry.Space.existsUnique_hom_of_isThickening_of_isAffineHom`: the morphism form.
* `AlgebraicGeometry.Space.existsUnique_section_of_isThickening_of_isAffineHom`: the section form.

## Implementation notes

The hypotheses are exactly those of
`AlgebraicGeometry.Space.isPushout_algebraicSpaces_of_isThickening_of_isAffineHom'`, the
statement of Stacks 07SY, so neither statement here assumes anything beyond its geometric
data.  Nothing mathematical is added: the morphism form is the universal property of
that pushout read in the full subcategory of presheaves cut out by `IsAlgebraicSpace`, and the
section form is the morphism form transported along `CategoryTheory.yonedaEquiv`.

Neither declaration carries `@[stacks 07SY]`.  That tag is carried by
`isPushout_algebraicSpaces_of_isThickening_of_isAffineHom`, and a second carrier of the same
assertion would say nothing the first does not.

The algebraic space is taken as a presheaf together with a proof that it is one, rather than as an
object of `AlgebraicGeometry.AlgebraicSpaces`, so that a consumer holding a presheaf — for
instance the Isom presheaf of a category fibred in groupoids, whose algebraicity is condition (2)
of Stacks 045G — can apply the statements without first bundling it.

## References

* [Stacks Project, Tag 07SY](https://stacks.math.columbia.edu/tag/07SY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The functor of points of an algebraic space on a thickening-and-affine pushout square.**
Let `i : X ⟶ X'` be a thickening and `f : X ⟶ Y` an affine morphism of schemes over `S` whose
pushout square is `a : X' ⟶ Y'`, `b : Y ⟶ Y'`.  For an algebraic space `P` over `S`, a pair of
morphisms `X' ⟶ P` and `Y ⟶ P` agreeing on `X` extends uniquely over `Y'`.

This is the universal property of the pushout of Stacks 07SY, read through the Yoneda embedding
of the site into presheaves. -/
theorem existsUnique_hom_of_isThickening_of_isAffineHom
    {X X' Y Y' : BigFppfOver B S hS}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hPushout : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b))
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (gX' : yoneda.obj X' ⟶ P) (gY : yoneda.obj Y ⟶ P)
    (hcompat : yoneda.map i ≫ gX' = yoneda.map f ≫ gY) :
    ∃! g : yoneda.obj Y' ⟶ P, yoneda.map a ≫ g = gX' ∧ yoneda.map b ≫ g = gY := by
  have hpo := isPushout_algebraicSpaces_of_isThickening_of_isAffineHom' B S hS i f a b hi hPushout
  set Ps : AlgebraicSpaces B S hS := ⟨P, hP⟩ with hPs
  let gX'' : (⟨yoneda.obj X', isAlgebraicSpace_yoneda B S hS X'⟩ : AlgebraicSpaces B S hS) ⟶ Ps :=
    ObjectProperty.homMk gX'
  let gY'' : (⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩ : AlgebraicSpaces B S hS) ⟶ Ps :=
    ObjectProperty.homMk gY
  have hw : (ObjectProperty.homMk (yoneda.map i) :
      (⟨yoneda.obj X, isAlgebraicSpace_yoneda B S hS X⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨yoneda.obj X', isAlgebraicSpace_yoneda B S hS X'⟩ : AlgebraicSpaces B S hS)) ≫ gX'' =
      (ObjectProperty.homMk (yoneda.map f) :
      (⟨yoneda.obj X, isAlgebraicSpace_yoneda B S hS X⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩ : AlgebraicSpaces B S hS)) ≫ gY'' :=
    ObjectProperty.hom_ext _ hcompat
  refine ⟨(hpo.desc gX'' gY'' hw).hom, ⟨?_, ?_⟩, ?_⟩
  · exact congrArg InducedCategory.Hom.hom (hpo.inl_desc gX'' gY'' hw)
  · exact congrArg InducedCategory.Hom.hom (hpo.inr_desc gX'' gY'' hw)
  · intro t ht
    have key : (ObjectProperty.homMk t :
        (⟨yoneda.obj Y', isAlgebraicSpace_yoneda B S hS Y'⟩ : AlgebraicSpaces B S hS) ⟶ Ps) =
        hpo.desc gX'' gY'' hw := by
      apply hpo.hom_ext
      · rw [hpo.inl_desc]
        exact ObjectProperty.hom_ext _ ht.1
      · rw [hpo.inr_desc]
        exact ObjectProperty.hom_ext _ ht.2
    exact congrArg InducedCategory.Hom.hom key

/-- **Sections of an algebraic space on a thickening-and-affine pushout square.**  Let
`i : X ⟶ X'` be a thickening and `f : X ⟶ Y` an affine morphism of schemes over `S` whose pushout
square is `a : X' ⟶ Y'`, `b : Y ⟶ Y'`.  For an algebraic space `P` over `S`, a section of `P` over
`X'` and a section over `Y` with the same restriction to `X` come from a unique section over `Y'`.

This is `AlgebraicGeometry.Space.existsUnique_hom_of_isThickening_of_isAffineHom` transported
along `CategoryTheory.yonedaEquiv`. -/
theorem existsUnique_section_of_isThickening_of_isAffineHom
    {X X' Y Y' : BigFppfOver B S hS}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hPushout : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b))
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (sX' : P.obj (op X')) (sY : P.obj (op Y))
    (hcompat : P.map i.op sX' = P.map f.op sY) :
    ∃! s : P.obj (op Y'), P.map a.op s = sX' ∧ P.map b.op s = sY := by
  obtain ⟨g, ⟨hga, hgb⟩, huniq⟩ :=
    existsUnique_hom_of_isThickening_of_isAffineHom B S hS i f a b hi hPushout P hP
      (yonedaEquiv.symm sX') (yonedaEquiv.symm sY)
      (yonedaEquiv.injective (by
        rw [← yonedaEquiv_naturality, ← yonedaEquiv_naturality, Equiv.apply_symm_apply,
          Equiv.apply_symm_apply]
        exact hcompat))
  refine ⟨yonedaEquiv g, ⟨?_, ?_⟩, ?_⟩
  · rw [yonedaEquiv_naturality, hga, Equiv.apply_symm_apply]
  · rw [yonedaEquiv_naturality, hgb, Equiv.apply_symm_apply]
  · intro t ht
    have h := huniq (yonedaEquiv.symm t) ⟨yonedaEquiv.injective (by
        rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact ht.1), yonedaEquiv.injective (by
        rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact ht.2)⟩
    rw [← h, Equiv.apply_symm_apply]

end AlgebraicGeometry.Space

end
