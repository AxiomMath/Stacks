module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSiteCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite

/-!
# The small étale topos of a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and let `X` be a formal algebraic space over
`S`. Stacks 0DEA defines the three étale sites `X_étale`, `X_{spaces, étale}` and
`X_{affine, étale}` of `X` as the corresponding sites of its reduction `X_red`; in this library
they are `AlgebraicGeometry.FormalSpace.canonicalSmallEtale`,
`AlgebraicGeometry.FormalSpace.canonicalSpacesEtale` and
`AlgebraicGeometry.FormalSpace.canonicalAffineEtale`, read at the reduction that Stacks 0AIN
produces. Stacks 0DEB identifies their topoi:
`Sh(X_étale) = Sh(X_{spaces, étale}) = Sh(X_{affine, étale})`.

The source deduces this from Properties of Spaces, Lemmas 03G1 and 04JS, applied to the
algebraic space `X_red`, and so does this file:

* the inclusion `X_{red, étale} ⥤ X_{red, spaces, étale}` of étale scheme charts among algebraic
  spaces étale over `X_red` is special cocontinuous, Stacks 03G1
  (`AlgebraicGeometry.Space.comparisonFunctor_specialCocontinuous`);
* the inclusion `X_{red, affine, étale} ⥤ X_{red, étale}` of the étale charts with affine source
  is special cocontinuous, Stacks 04JS
  (`AlgebraicGeometry.Space.AffineEtale.inclusion_isSpecialCocontinuous`), which applies because
  `X_red` is an algebraic space.

A special cocontinuous functor is a dense subsite inclusion, so restriction along it is an
equivalence of sheaf categories by the Comparison Lemma
(`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`).

## Main definitions

* `AlgebraicGeometry.FormalSpace.Reduction.smallEtaleToposEquivSpacesEtale` and
  `AlgebraicGeometry.FormalSpace.Reduction.smallEtaleToposEquivAffineEtale`: the two
  identifications at an arbitrary reduction datum.
* `AlgebraicGeometry.FormalSpace.canonicalSmallEtaleToposEquivSpacesEtale` and
  `AlgebraicGeometry.FormalSpace.canonicalSmallEtaleToposEquivAffineEtale`: **Stacks 0DEB**,
  `Sh(X_étale) = Sh(X_{spaces, étale})` and `Sh(X_étale) = Sh(X_{affine, étale})`, for sheaves
  valued in any category with the limits that the Comparison Lemma asks for.
* `AlgebraicGeometry.FormalSpace.canonicalSmallEtaleToposEquivSpacesEtaleSets` and
  `AlgebraicGeometry.FormalSpace.canonicalSmallEtaleToposEquivAffineEtaleSets`: **Stacks 0DEB**
  for sheaves of sets, at `Type (u + 1)`, the universe of the topoi of Stacks 0DEC, part (3).

## Main results

* `AlgebraicGeometry.FormalSpace.Reduction.affineEtaleInclusion_isDenseSubsite`: the affine
  étale site of a formal algebraic space is a dense subsite of its small étale site.
* `AlgebraicGeometry.FormalSpace.canonicalSmallEtaleToposEquivSpacesEtale_inverse` and
  `AlgebraicGeometry.FormalSpace.canonicalSmallEtaleToposEquivAffineEtale_functor`: both
  identifications are restriction of sheaves along the inclusion of sites.

## Implementation notes

Both equivalences are written with `X_étale` as the common side, so that together they identify
all three topoi. The equivalence `Sh(X_{spaces, étale}) = Sh(X_{affine, étale})` is their
composite and is not given a separate name.

## References

* [Stacks Project, Tag 0DEB](https://stacks.math.columbia.edu/tag/0DEB)
* [Stacks Project, Tag 0DEA](https://stacks.math.columbia.edu/tag/0DEA)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe w w' u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : FppfSheaf B S hS}

/-! ### The identifications at a reduction datum -/

namespace Reduction

/-- The inclusion `X_étale ⥤ X_{spaces, étale}` of the small étale site of a formal algebraic
space into its spaces-étale site: the comparison functor of Stacks 03G1 for the reduction. -/
abbrev smallEtaleToSpacesEtale (R : Reduction B S hS X) : R.SmallEtale ⥤ R.SpacesEtale :=
  Space.comparisonFunctor B S hS R.space

/-- The inclusion `X_{affine, étale} ⥤ X_étale` of the affine étale site of a formal algebraic
space into its small étale site: the inclusion of the affine étale charts of the reduction. -/
abbrev affineEtaleInclusion (R : Reduction B S hS X) : R.AffineEtale ⥤ R.SmallEtale :=
  Space.AffineEtale.inclusion B S hS R.space.obj

/-- The affine étale site of a formal algebraic space is a dense subsite of its small étale site,
by Stacks 04JS applied to the reduction, which is an algebraic space. -/
instance affineEtaleInclusion_isDenseSubsite (R : Reduction B S hS X) :
    R.affineEtaleInclusion.IsDenseSubsite R.affineEtaleTopology R.smallEtaleTopology :=
  (Space.AffineEtale.inclusion_isSpecialCocontinuous B S hS R.space.obj R.space.property).2

/-- `Sh(X_étale) = Sh(X_{spaces, étale})` for a formal algebraic space with a given reduction:
restriction along the inclusion `X_étale ⥤ X_{spaces, étale}` is an equivalence, by Stacks 03G1
for the reduction. -/
noncomputable def smallEtaleToposEquivSpacesEtale (R : Reduction B S hS X) (A : Type w)
    [Category.{w'} A]
    [∀ Y, HasLimitsOfShape (StructuredArrow Y R.smallEtaleToSpacesEtale.op) A] :
    Sheaf R.smallEtaleTopology A ≌ Sheaf R.spacesEtaleTopology A :=
  Functor.IsDenseSubsite.sheafEquiv R.smallEtaleTopology R.spacesEtaleTopology
    R.smallEtaleToSpacesEtale A

/-- `Sh(X_étale) = Sh(X_{affine, étale})` for a formal algebraic space with a given reduction:
restriction along the inclusion `X_{affine, étale} ⥤ X_étale` is an equivalence, by Stacks 04JS
for the reduction. -/
noncomputable def smallEtaleToposEquivAffineEtale (R : Reduction B S hS X) (A : Type w)
    [Category.{w'} A]
    [∀ Y, HasLimitsOfShape (StructuredArrow Y R.affineEtaleInclusion.op) A] :
    Sheaf R.smallEtaleTopology A ≌ Sheaf R.affineEtaleTopology A :=
  (Functor.IsDenseSubsite.sheafEquiv R.affineEtaleTopology R.smallEtaleTopology
    R.affineEtaleInclusion A).symm

end Reduction

/-! ### Stacks 0DEB at the canonical reduction -/

variable (hX : IsFormalAlgebraicSpace B S hS X)

/-- **Stacks 0DEB**, `Sh(X_étale) = Sh(X_{spaces, étale})`. For a formal algebraic space `X` over
`S`, the topos of the small étale site `X_étale` of Stacks 0DEA, part (1), is equivalent to that
of the site `X_{spaces, étale}` of Stacks 0DEA, part (2): restriction along the inclusion of
étale scheme charts of `X_red` among algebraic spaces étale over `X_red` is an equivalence. This
holds for sheaves valued in any category `A` with the limits the Comparison Lemma asks for, which
includes sheaves of sets; see
`AlgebraicGeometry.FormalSpace.canonicalSmallEtaleToposEquivSpacesEtaleSets`. -/
@[stacks 0DEB "`Sh(X_étale) = Sh(X_spaces,étale)`, for sheaves in any category with the limits of
  the Comparison Lemma"]
noncomputable def canonicalSmallEtaleToposEquivSpacesEtale (A : Type w) [Category.{w'} A]
    [∀ Y, HasLimitsOfShape
      (StructuredArrow Y (canonicalReduction hX).smallEtaleToSpacesEtale.op) A] :
    Sheaf (canonicalSmallEtaleTopology hX) A ≌ Sheaf (canonicalSpacesEtaleTopology hX) A :=
  (canonicalReduction hX).smallEtaleToposEquivSpacesEtale A

/-- **Stacks 0DEB**, `Sh(X_étale) = Sh(X_{affine, étale})`. For a formal algebraic space `X` over
`S`, the topos of the small étale site `X_étale` of Stacks 0DEA, part (1), is equivalent to that
of the site `X_{affine, étale}` of Stacks 0DEA, part (3): restriction along the inclusion of the
étale charts of `X_red` with affine source is an equivalence. This holds for sheaves valued in
any category `A` with the limits the Comparison Lemma asks for, which includes sheaves of sets;
see `AlgebraicGeometry.FormalSpace.canonicalSmallEtaleToposEquivAffineEtaleSets`. -/
@[stacks 0DEB "`Sh(X_étale) = Sh(X_affine,étale)`, for sheaves in any category with the limits of
  the Comparison Lemma"]
noncomputable def canonicalSmallEtaleToposEquivAffineEtale (A : Type w) [Category.{w'} A]
    [∀ Y, HasLimitsOfShape
      (StructuredArrow Y (canonicalReduction hX).affineEtaleInclusion.op) A] :
    Sheaf (canonicalSmallEtaleTopology hX) A ≌ Sheaf (canonicalAffineEtaleTopology hX) A :=
  (canonicalReduction hX).smallEtaleToposEquivAffineEtale A

/-- The identification `Sh(X_étale) = Sh(X_{spaces, étale})` of Stacks 0DEB is restriction of
sheaves along the inclusion `X_étale ⥤ X_{spaces, étale}`. -/
theorem canonicalSmallEtaleToposEquivSpacesEtale_inverse (A : Type w) [Category.{w'} A]
    [∀ Y, HasLimitsOfShape
      (StructuredArrow Y (canonicalReduction hX).smallEtaleToSpacesEtale.op) A] :
    (canonicalSmallEtaleToposEquivSpacesEtale hX A).inverse =
      (canonicalReduction hX).smallEtaleToSpacesEtale.sheafPushforwardContinuous A
        (canonicalSmallEtaleTopology hX) (canonicalSpacesEtaleTopology hX) :=
  rfl

/-- The identification `Sh(X_étale) = Sh(X_{affine, étale})` of Stacks 0DEB is restriction of
sheaves along the inclusion `X_{affine, étale} ⥤ X_étale`. -/
theorem canonicalSmallEtaleToposEquivAffineEtale_functor (A : Type w) [Category.{w'} A]
    [∀ Y, HasLimitsOfShape
      (StructuredArrow Y (canonicalReduction hX).affineEtaleInclusion.op) A] :
    (canonicalSmallEtaleToposEquivAffineEtale hX A).functor =
      (canonicalReduction hX).affineEtaleInclusion.sheafPushforwardContinuous A
        (canonicalAffineEtaleTopology hX) (canonicalSmallEtaleTopology hX) :=
  rfl

/-- **Stacks 0DEB**, `Sh(X_étale) = Sh(X_{spaces, étale})`, for sheaves of sets. These are sets
in `Type (u + 1)`, the universe of the small étale topoi of Stacks 0DEC, part (3), which pass
through this identification. -/
@[stacks 0DEB "`Sh(X_étale) = Sh(X_spaces,étale)`, for sheaves of sets"]
noncomputable def canonicalSmallEtaleToposEquivSpacesEtaleSets :
    Sheaf (canonicalSmallEtaleTopology hX) (Type (u + 1)) ≌
      Sheaf (canonicalSpacesEtaleTopology hX) (Type (u + 1)) :=
  canonicalSmallEtaleToposEquivSpacesEtale hX (Type (u + 1))

/-- **Stacks 0DEB**, `Sh(X_étale) = Sh(X_{affine, étale})`, for sheaves of sets. These are sets
in `Type (u + 1)`, the universe of the small étale topoi of Stacks 0DEC, part (3). -/
@[stacks 0DEB "`Sh(X_étale) = Sh(X_affine,étale)`, for sheaves of sets"]
noncomputable def canonicalSmallEtaleToposEquivAffineEtaleSets :
    Sheaf (canonicalSmallEtaleTopology hX) (Type (u + 1)) ≌
      Sheaf (canonicalAffineEtaleTopology hX) (Type (u + 1)) :=
  canonicalSmallEtaleToposEquivAffineEtale hX (Type (u + 1))

end AlgebraicGeometry.FormalSpace

end
