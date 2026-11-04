module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.CoefficientUniverse

/-!
# Proper base change for the higher direct images of a torsion sheaf

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of schemes with `f` proper, and let `F` be a torsion abelian sheaf on
`X_étale`. Then for every `q`

`g⁻¹ (R^q f_* F) ≅ R^q f'_* ((g')⁻¹ F)`.

This is the sheaf form of the proper base change theorem, [Stacks, Tag 095T]: the derived
statement `g⁻¹ Rf_* F ≅ Rf'_* (g')⁻¹ F`
(`Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isProper`) read in degree
`q`, the inverse image being exact.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageIsoOfIsProper`: the
  isomorphism above.

## References

* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) (g' : X' ⟶ X)
  (f' : X' ⟶ Y') (sq : IsPullback g' f' f g)

/-- Proper base change for the higher direct images of a torsion sheaf: for a cartesian square
`g' ≫ f = f' ≫ g` with `f` proper and a torsion abelian sheaf `F` on `X_étale`, the inverse image
along `g` of `R^q f_* F` is `R^q f'_*` of the inverse image of `F` along `g'`. -/
def etaleAbelianInverseImageRightDerivedDirectImageIsoOfIsProper
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (q : ℕ) :
    (etaleAbelianInverseImage.{u, 0} g).obj
        (((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj F) ≅
      ((etaleAbelianDirectImage.{u, 0} f').rightDerived q).obj
        ((etaleAbelianInverseImage.{u, 0} g').obj F) :=
  haveI := isIso_etaleAbelianSheafDerivedBaseChange_of_isProper f g g' f' sq F hF
  (etaleAbelianInverseImage.{u, 0} g).mapIso
      (etaleAbelianRightDerivedDirectImageIsoHomology.{0, u} f q F) ≪≫
    (((etaleAbelianInverseImage.{u, 0} g).mapDerivedCategoryHomologyIso q).app _).symm ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      (asIso (etaleAbelianSheafDerivedBaseChange.{u, 0} f g g' f' sq.w F)) ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((etaleAbelianDerivedDirectImage.{u, 0} f').mapIso
        (((etaleAbelianInverseImage.{u, 0} g').mapDerivedCategorySingleFunctor 0).app F)) ≪≫
    (etaleAbelianRightDerivedDirectImageIsoHomology.{0, u} f' q _).symm

end Stacks.EtaleCohomology

end
