module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverMorphism

/-!
# The projections of the scheme-theoretic image of Stacks 089J are proper

The cover of Stacks 089J is an open subscheme of the scheme-theoretic image `Z` of the
complement of the diagonals inside the `d`-fold fibre power of a projective compactification
`Y` of an étale chart, and the properness of the cover is checked through the `d` projections
`gᵢ : Z ⟶ Y`. That those projections are proper is
`AlgebraicGeometry.isProper_imageι_comp_overProdπ`, which is stated for the scheme-level
product `Stacks.Chow.overProd` and asks that the structure morphisms of the factors be proper.

This file transports that statement onto `AlgebraicGeometry.Space.chowProj`, the projection as
it is actually used, and supplies its hypothesis from projectivity of the compactification.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isProper_chowProj`: each projection
  `AlgebraicGeometry.Space.chowProj` of the scheme-theoretic image is proper as a morphism of
  schemes, provided the structure morphism of the compactification is proper.
* `AlgebraicGeometry.Space.isProper_chowProj_of_isProjectiveMorphism`: the same with the
  hypothesis replaced by projectivity of the structure morphism of the compactification, which
  is the form in which Stacks 089J has it.

## What is and is not proved

Stacks 089J is **not** proved here and no declaration in this file carries a Stacks attribute:
properness of a projection of a fibre power is
`AlgebraicGeometry.isProper_overProdπ`, properness of a projective morphism is Stacks 01WC in
the form `AlgebraicGeometry.isProper_of_isProjectiveMorphism`, and this file is the
identification of the object of the site with the scheme-level product, which is a
definitional unfolding (`AlgebraicGeometry.Space.overProdObj_toScheme`).

Properness of the morphism `X' ⟶ X` of Stacks 089J is **not** proved. The projections being
proper is one input of the valuative-criterion argument for that properness — through
`AlgebraicGeometry.exists_valuativeLift_of_isProper` applied to a projection — but the
argument also needs the valuative lift to be promoted to a morphism of the site and the
uniqueness clause of the refined valuative criterion, neither of which is here.

## References

* [Stacks Project, Tag 01WC](https://stacks.math.columbia.edu/tag/01WC)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (Wch : BigFppfOver B S hS)
    (c : yoneda.obj Wch ⟶ X.obj) (hc : IsEtale B S hS c) (hsep : IsSeparated B S hS c)
    (Yo : BigFppfOver B S hS) (j : Wch ⟶ Yo) (n : ℕ) (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅ (SpacesEtale.underlying B S hS X
      (SpacesEtale.diagonalComplement B S hS X
        (SpacesEtale.chartObj B S hS X Wch c hc) (n + 1) hsep)).obj)

/-- **Each projection of the scheme-theoretic image of Stacks 089J is proper**, provided the
structure morphism of the compactification is proper.

`AlgebraicGeometry.Space.chowProj` is by definition the closed immersion of the
scheme-theoretic image followed by a projection of
`AlgebraicGeometry.Space.overProdObj`, whose underlying scheme is the scheme-level product
`Stacks.Chow.overProd` of the structure morphisms of the factors by
`AlgebraicGeometry.Space.overProdObj_toScheme`; here every factor is the compactification
itself, so one hypothesis of properness serves for all of them and the statement is
`AlgebraicGeometry.isProper_imageι_comp_overProdπ`. -/
theorem isProper_chowProj (i : Fin (n + 1))
    (hYo : _root_.AlgebraicGeometry.IsProper (B.inclusion.map Yo.hom)) :
    _root_.AlgebraicGeometry.IsProper (chowProj B S hS X Wch c hc hsep Yo j n V e i) := by
  have : ∀ _ : Fin (n + 1), _root_.AlgebraicGeometry.IsProper
    (B.inclusion.map Yo.hom) := fun _ ↦ hYo
  exact isProper_imageι_comp_overProdπ (fun _ : Fin (n + 1) ↦ B.inclusion.map Yo.hom)
    ((BigFppfOver.toScheme B S hS).map
      (chowToOverProd B S hS X Wch c hc hsep Yo j n V e)) i

/-- **Each projection of the scheme-theoretic image of Stacks 089J is proper when the
compactification is projective over the base.**

This is `AlgebraicGeometry.Space.isProper_chowProj` with its hypothesis supplied by Stacks
01WC in the form `AlgebraicGeometry.isProper_of_isProjectiveMorphism`. It is the form Stacks
089J has the hypothesis in: the compactification `Y` of the affine étale chart produced by
`AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_of_isAffine_toSpec` comes with
a projective structure morphism. -/
theorem isProper_chowProj_of_isProjectiveMorphism (i : Fin (n + 1))
    (hYo : IsProjectiveMorphism (B.inclusion.map Yo.hom)) :
    _root_.AlgebraicGeometry.IsProper (chowProj B S hS X Wch c hc hsep Yo j n V e i) :=
  isProper_chowProj B S hS X Wch c hc hsep Yo j n V e i
    (isProper_of_isProjectiveMorphism _ hYo)

end AlgebraicGeometry.Space

end
