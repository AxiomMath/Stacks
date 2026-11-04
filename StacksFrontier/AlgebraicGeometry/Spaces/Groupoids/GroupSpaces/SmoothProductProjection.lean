module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits

/-!
# The projection of a product of algebraic spaces is smooth when one factor is

Let `B` and `P` be algebraic spaces over a scheme `S` of a big fppf site.  The projection
`B ⨯ P ⟶ B` is the base change of the structure morphism `P ⟶ S` along the structure morphism
`B ⟶ S`, because a binary product is the fibre product over the terminal presheaf, which is the
presheaf represented by the base.  So if `P ⟶ S` is smooth then so is `B ⨯ P ⟶ B`, by
Stacks 03ZE.

For `P` the functor of points on the site of an object `a` of the site this makes the structure
morphism of the group algebraic space `G_B = B ×_S G` of Stacks 043I smooth as soon as the
structure morphism of `G` is smooth as a morphism of schemes, which is the hypothesis that
Stacks 04TK asks for in
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStackOfAction_of_isSmooth`.

## Main results

* `AlgebraicGeometry.AlgebraicSpaces.isPullback_of_isPullback_hom`: a Cartesian square of
  presheaves whose four corners are algebraic spaces is Cartesian in the category of algebraic
  spaces.
* `AlgebraicGeometry.Space.isSmooth_prod_fst`: the projection `B ⨯ P ⟶ B` is smooth when the
  structure morphism of `P` is.
* `AlgebraicGeometry.Space.isSmooth_prod_fst_of_representableBy`: the same when `P` is
  represented by an object of the site whose structure morphism is smooth.
* `AlgebraicGeometry.Space.isSmooth_prod_fst_pointsOnSite`: the same for the functor of points
  on the site of a group scheme of the site, which is the shape
  `AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite` produces.
* `AlgebraicGeometry.Space.isSmooth_yoneda_map_mkIdTerminal_from`: the structure morphism of an
  object of the site is smooth as a morphism of algebraic spaces as soon as it is smooth as a
  morphism of schemes.

## Implementation notes

Base-change stability of smoothness, Stacks 03ZE, is stated for morphisms of the *category* of
algebraic spaces over `S`, while the product square lives in presheaves; the full subcategory
inclusion is fully faithful, hence reflects limits, and
`AlgebraicGeometry.AlgebraicSpaces.isPullback_of_isPullback_hom` transports the square.  It is
the converse of `AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`.

Nothing is assumed of `B`: it is an arbitrary algebraic space over `S`, not a scheme, and no
condition is imposed on the group object beyond smoothness of its structure morphism.

## References

* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
* [Stacks Project, Tag 043I](https://stacks.math.columbia.edu/tag/043I)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)

namespace AlgebraicSpaces

/-- A Cartesian square of presheaves on the big fppf site of `S` whose four corners are
algebraic spaces is Cartesian in the category of algebraic spaces over `S`.  This is the
converse of `AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`, and holds because the full
subcategory inclusion of the algebraic spaces reflects limits. -/
theorem isPullback_of_isPullback_hom {W X Y Z : AlgebraicSpaces 𝒞 S hS}
    {fst : W ⟶ X} {snd : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback fst.hom snd.hom f.hom g.hom) : IsPullback fst snd f g :=
  IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) sq

end AlgebraicSpaces

namespace Space

/-- Smoothness of morphisms of algebraic spaces over `S`, as a property of morphisms of the
category of algebraic spaces over `S`. -/
private abbrev smoothProperty : MorphismProperty (AlgebraicSpaces 𝒞 S hS) :=
  fun ⦃_ _ : AlgebraicSpaces 𝒞 S hS⦄ (f) => IsSmooth 𝒞 S hS f.hom

/-- **The projection of a product of algebraic spaces is smooth when the structure morphism of
the second factor is.** A binary product is the fibre product over the terminal presheaf, which
is the presheaf represented by the base, so the projection `B ⨯ P ⟶ B` is the base change of
the structure morphism of `P` along the structure morphism of `B`; smoothness is stable under
base change by Stacks 03ZE. -/
theorem isSmooth_prod_fst (B P : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B) (hP : IsAlgebraicSpace 𝒞 S hS P)
    (hsm : IsSmooth 𝒞 S hS ((isTerminal_yoneda_obj_base 𝒞 S hS).from P)) :
    IsSmooth 𝒞 S hS (prod.fst : B ⨯ P ⟶ B) :=
  (isSmooth_isStableUnderBaseChange 𝒞 S hS).of_isPullback
    (AlgebraicSpaces.isPullback_of_isPullback_hom 𝒞 S hS
      (W := ⟨B ⨯ P, isAlgebraicSpace_prod 𝒞 S hS hB hP⟩) (X := ⟨P, hP⟩) (Y := ⟨B, hB⟩)
      (Z := ⟨_, isAlgebraicSpace_yoneda 𝒞 S hS (Over.mk (𝟙 (𝒞.obj hS)))⟩)
      (fst := ObjectProperty.homMk prod.snd) (snd := ObjectProperty.homMk prod.fst)
      (f := ObjectProperty.homMk ((isTerminal_yoneda_obj_base 𝒞 S hS).from P))
      (g := ObjectProperty.homMk ((isTerminal_yoneda_obj_base 𝒞 S hS).from B))
      ((isTerminal_yoneda_obj_base 𝒞 S hS).isPullback_prod B P).flip)
    hsm

/-- **The projection `B ⨯ P ⟶ B` is smooth when `P` is represented by an object of the site
whose structure morphism is smooth.**  The representing isomorphism identifies the structure
morphism of `P` with the structure morphism of the representing object up to an isomorphism of
the source, and smoothness respects isomorphisms. -/
theorem isSmooth_prod_fst_of_representableBy (B P : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B) {a : BigFppfOver 𝒞 S hS} (r : P.RepresentableBy a)
    (hsm : IsSmooth 𝒞 S hS (yoneda.map (Over.mkIdTerminal.from a))) :
    IsSmooth 𝒞 S hS (prod.fst : B ⨯ P ⟶ B) := by
  have ha : IsAlgebraicSpace 𝒞 S hS (yoneda.obj a) := isAlgebraicSpace_yoneda 𝒞 S hS a
  have hP : IsAlgebraicSpace 𝒞 S hS P := isAlgebraicSpace_of_iso 𝒞 S hS r.toIso.symm ha
  have hbc : (smoothProperty 𝒞 S hS).IsStableUnderBaseChange :=
    isSmooth_isStableUnderBaseChange 𝒞 S hS
  let Pas : AlgebraicSpaces 𝒞 S hS := ⟨P, hP⟩
  let aas : AlgebraicSpaces 𝒞 S hS := ⟨yoneda.obj a, ha⟩
  let Tas : AlgebraicSpaces 𝒞 S hS :=
    ⟨_, isAlgebraicSpace_yoneda 𝒞 S hS (Over.mk (𝟙 (𝒞.obj hS)))⟩
  let e : Pas ⟶ aas := ObjectProperty.homMk r.toIso.inv
  have : IsIso e :=
    ⟨ObjectProperty.homMk r.toIso.hom, ObjectProperty.hom_ext _ r.toIso.inv_hom_id,
      ObjectProperty.hom_ext _ r.toIso.hom_inv_id⟩
  have h : (isTerminal_yoneda_obj_base 𝒞 S hS).from P =
      r.toIso.inv ≫ yoneda.map (Over.mkIdTerminal.from a) :=
    (isTerminal_yoneda_obj_base 𝒞 S hS).hom_ext _ _
  exact isSmooth_prod_fst 𝒞 S hS B P hB hP
    (h ▸ MorphismProperty.RespectsIso.precomp (smoothProperty 𝒞 S hS) e
      (ObjectProperty.homMk (yoneda.map (Over.mkIdTerminal.from a)) : aas ⟶ Tas) hsm)

/-- **The structure morphism of the group algebraic space `G_B = B ×_S G` of Stacks 043I is
smooth when the structure morphism of the group scheme `G` is.**  The algebraic space underlying
`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite` is `B ⨯ P` for `P` the
restriction to the site of the functor of points of `G`, which is represented by `G`. -/
theorem isSmooth_prod_fst_pointsOnSite (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B) (G : BigFppfOver 𝒞 S hS)
    (hG : GrpObj ((toSchemeOver 𝒞 S hS).obj G))
    (hsm : IsSmooth 𝒞 S hS (yoneda.map (Over.mkIdTerminal.from G))) :
    IsSmooth 𝒞 S hS (prod.fst : B ⨯ (pointsOnSite 𝒞 S hS G hG ⋙ forget GrpCat) ⟶ B) :=
  isSmooth_prod_fst_of_representableBy 𝒞 S hS B _ hB
    (pointsOnSiteRepresentableBy 𝒞 S hS G hG) hsm

/-- **The structure morphism of an object of the site is smooth as a morphism of algebraic
spaces as soon as it is smooth as a morphism of schemes.**  Smoothness of morphisms of schemes
is étale local on the source and the target, Stacks 04R3, so a representable morphism whose
underlying morphism of schemes is smooth satisfies the every-chart condition of Stacks 03MJ. -/
theorem isSmooth_yoneda_map_mkIdTerminal_from (a : BigFppfOver 𝒞 S hS)
    (h : Smooth ((BigFppfOver.toScheme 𝒞 S hS).map (Over.mkIdTerminal.from a))) :
    IsSmooth 𝒞 S hS (yoneda.map (Over.mkIdTerminal.from a)) :=
  holdsOnEveryEtaleChart_yoneda_map 𝒞 S hS Smooth.isEtaleLocalOnSourceAndTarget _ h

/-- The structure morphism of `AlgebraicGeometry.siteObject`, read through
`AlgebraicGeometry.BigFppfOver.toScheme`, is the prescribed morphism of schemes. -/
theorem toScheme_map_mkIdTerminal_from_siteObject {T : Scheme.{u}} (hT : 𝒞.Contains T)
    (b : T ⟶ S) :
    (BigFppfOver.toScheme 𝒞 S hS).map (Over.mkIdTerminal.from (siteObject 𝒞 S hS hT b)) = b := by
  have h : Over.mkIdTerminal.from (siteObject 𝒞 S hS hT b) =
      Over.homMk (ObjectProperty.homMk b : 𝒞.obj hT ⟶ 𝒞.obj hS) (by simp) :=
    Over.mkIdTerminal.hom_ext _ _
  rw [h]
  rfl

end Space

end AlgebraicGeometry

end
