module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionInverseImage
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.MorphismOfSites

/-!
# Stacks 03LQ at abelian coefficients

Let `h : U ⟶ V` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Stacks 03LQ identifies the inverse image of the morphism of small étale topoi
`h_{small}` of Stacks 03G2, part (3) with restriction along the postcomposition functor `j` of
Stacks 03LP:

`G|_{U_étale} = h_{small}^{-1} G`.

`AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRestrictionInverseImage.lean` proves this for
sheaves of sets, which is the form in which the source states it: a morphism of topoi is a pair
of adjoint functors between categories of sheaves of *sets*.  This file proves the same
identification for sheaves of *abelian groups*, where the left-hand side is the inverse image of
abelian sheaves attached to `h_{small}` by Stacks 04JC,
`CategoryTheory.Sites.abelianInverseImage`, and the right-hand side is restriction along `j` at
`AddCommGrpCat` coefficients, which is
`AlgebraicGeometry.Space.etaleAbelianRestriction` of
`StacksFrontier/AlgebraicGeometry/Spaces/SectionsWithSupportEtaleLocal.lean`.

This is the input recorded as missing by the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/HigherPushforwardBaseChange.lean` — where it is what
turns Stacks 03F3 for a localization into the statement about `i_{small}^{-1}` that Stacks 03LR
part (2) needs — and by those of
`StacksFrontier/AlgebraicGeometry/Spaces/SectionsWithSupportEtaleLocalHigher.lean`, which needs it
to move the comparison of Stacks 0A4P across a closed immersion.

## Main results

* `AlgebraicGeometry.Space.smallToposMorphism_abelianInverseImageIso`: **Stacks 03LQ at abelian
  coefficients.**
* `AlgebraicGeometry.Space.smallToposMorphism_abelianInverseImage_obj_obj`: the displayed
  formula on sections, `(h_{small}^{-1}G)(W) = G(jW)`, as abelian groups.

## Implementation notes

Nothing is reproved: the whole content is that the two sides are the images of the two sides of
the set-level statement under one and the same passage from sheaves of sets to abelian sheaves,
and that passage is functorial in the functor.

Precisely, an abelian sheaf is the same thing as an internal commutative group object in the
topos of sheaves of sets (Stacks 04JC, here `CategoryTheory.Sites.AbelianSheaf.equivalence`), and
a finite-product-preserving functor of topoi acts on commutative group objects by
`CategoryTheory.Functor.mapCommGrp`.  Both sides of the abelian statement are the conjugate of
`mapCommGrp` of the corresponding side of the set-level statement:

* for `h_{small}^{-1}` that is the definition of `CategoryTheory.Sites.abelianInverseImage`;
* for restriction along `j` it is
  `Stacks.Sites.AbelianPullback.abelianSheafPushforwardIso`, whose content is that restriction
  along a functor of sites is computed on sections, so that the comparison is the identity on
  sections and only additivity has to be checked.

So the set-level isomorphism `AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso` is
carried over by `CategoryTheory.Functor.mapCommGrpNatIso`, and the two conjugations are
collapsed by the second bullet.  Both functors preserve finite limits — the inverse image of a
morphism of topoi by definition, restriction along `j` because it has the left adjoint `j_!`
supplied by `CategoryTheory.Functor.sheafPullbackConstruction` — so both act on commutative
group objects, and the braidings are the cartesian ones of
`CategoryTheory.Functor.Braided.ofChosenFiniteProducts`, imported with the file-local instances
of `StacksFrontier/CategoryTheory/Sites/Simplicial/AbelianSumFormula/MorphismOfSites.lean` so that
the monoidal structures are the *same terms* those declarations were elaborated with.

The universe levels of the three intermediate terms in the proof are written out.  Left to
instance search, the coefficient universe of `CategoryTheory.Sites.AbelianSheaf.internalSheaf`
is still a metavariable when the `HasSheafify` side conditions of the sheaf category are
synthesized, and the elaboration fails on `UnivLE.{u + 1, max (u + 1) ?w}`.  The statement
itself needs no annotation; only the proof term does.

## References

* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] Stacks.Sites.AbelianPullback.cartesianMonoidalCategorySheaf
  Stacks.Sites.AbelianPullback.braidedCategorySheaf
  Stacks.Sites.AbelianPullback.braidedSheafToPresheaf
  Stacks.Sites.AbelianPullback.preservesFiniteLimitsSheafPushforward
  Stacks.Sites.AbelianPullback.braidedSheafPushforward
  Functor.Braided.ofChosenFiniteProducts

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : AlgebraicSpaces B S hS}

/-- The inverse image of a morphism of small étale topoi is left exact: that is one of the four
fields of a morphism of topoi.  It is the instance under which the inverse image acts on
commutative group objects, and it is the same term
`StacksFrontier/CategoryTheory/Sites/Modules/InverseImage/AbelianSheaf.lean` uses to define
`CategoryTheory.Sites.abelianInverseImage`. -/
noncomputable local instance preservesFiniteLimitsSmallToposMorphismInverseImage (h : U ⟶ V) :
    PreservesFiniteLimits (smallToposMorphism B S hS h).inverseImage :=
  (smallToposMorphism B S hS h).preservesFiniteLimits

/-- **Stacks 03LQ at abelian coefficients.** For an étale morphism `h : U ⟶ V` of algebraic
spaces, the inverse image of *abelian* sheaves along the morphism of small étale topoi
`h_{small}` of Stacks 03G2, part (3) is restriction along the postcomposition functor `j` of
Stacks 03LP, i.e. `G|_{U_étale} = h_{small}^{-1}G` for `G` an abelian sheaf.

`AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso` is the same statement for sheaves
of sets, which is the form the source states it in.  The right-hand side is
`AlgebraicGeometry.Space.etaleAbelianRestriction`.

Both sides are the conjugate, by the identification of abelian sheaves with commutative group
objects of the topos, of `CategoryTheory.Functor.mapCommGrp` of the corresponding set-level
functor: for the inverse image that is the definition of
`CategoryTheory.Sites.abelianInverseImage`, and for restriction along `j` it is
`Stacks.Sites.AbelianPullback.abelianSheafPushforwardIso`.  So the set-level isomorphism is
carried across by `CategoryTheory.Functor.mapCommGrpNatIso`. -/
@[stacks 03LQ "at abelian coefficients: h_small^{-1} of an abelian sheaf is restriction along j"]
noncomputable def smallToposMorphism_abelianInverseImageIso (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    Sites.abelianInverseImage (smallToposMorphism B S hS h) ≅
      (smallEtalePostcomp B S hS h hh).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS V.1) :=
  Functor.isoWhiskerLeft
      (Sites.AbelianSheaf.internalSheaf.{u, u + 1, u + 1} (SmallEtale.topology B S hS V.1))
      (Functor.isoWhiskerRight
        (Functor.mapCommGrpNatIso (smallToposMorphism_inverseImageIso B S hS h hh))
        (Sites.AbelianSheaf.externalSheaf.{u, u + 1, u + 1}
          (SmallEtale.topology B S hS U.1))) ≪≫
    Stacks.Sites.AbelianPullback.abelianSheafPushforwardIso.{u + 1, u + 1, u, u + 1, u}
      (smallEtalePostcomp B S hS h hh) (SmallEtale.topology B S hS U.1)
      (SmallEtale.topology B S hS V.1)

/-- **Stacks 03LP, the displayed formula for the inverse image, at abelian coefficients.** The
sections of `h_{small}^{-1}G` over an étale chart `W` of `U` are the sections of `G` over the
composite chart `jW`, as abelian groups.

This is `AlgebraicGeometry.Space.smallToposMorphism_abelianInverseImageIso` evaluated at `G` and
at `W`; on the right-hand side the sections of a restricted sheaf are the asserted ones by
definition. -/
@[stacks 03LP "the displayed formula for the inverse image, at abelian coefficients"]
noncomputable def smallToposMorphism_abelianInverseImage_obj_obj (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom)
    (G : Sheaf (SmallEtale.topology B S hS V.1) AddCommGrpCat.{u + 1})
    (W : SmallEtale B S hS U.1) :
    (((Sites.abelianInverseImage (smallToposMorphism B S hS h)).obj G).obj.obj (.op W)) ≅
      G.obj.obj (.op ((smallEtalePostcomp B S hS h hh).obj W)) :=
  (sheafToPresheaf (SmallEtale.topology B S hS U.1) AddCommGrpCat.{u + 1} ⋙
      (evaluation (SmallEtale B S hS U.1)ᵒᵖ AddCommGrpCat.{u + 1}).obj (.op W)).mapIso
    ((smallToposMorphism_abelianInverseImageIso B S hS h hh).app G)

end AlgebraicGeometry.Space

end
