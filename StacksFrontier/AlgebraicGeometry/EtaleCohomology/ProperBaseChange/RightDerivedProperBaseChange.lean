module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperGeometricFibreStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Proper base change for the higher direct images of a torsion sheaf

For a cartesian square

```
X' --g'--> X
|f'        |f
Y' --g---> Y
```

with `f` proper and `F` an abelian torsion sheaf on `X_étale`, the higher direct images satisfy
`g⁻¹ Rᵠf_* F ≅ Rᵠf'_* (g')⁻¹ F` for every `q`.

## Main definitions

* `Stacks.EtaleCohomology.rightDerivedDirectImageProperBaseChangeIso`: the isomorphism
  `g⁻¹ Rᵠf_* F ≅ Rᵠf'_* (g')⁻¹ F`.

## References

* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

section

attribute [local instance] HasDerivedCategory.standard

/-- **Proper base change for higher direct images.** For a cartesian square `X' = Y' ×_Y X` with
`f : X ⟶ Y` proper, projections `g' : X' ⟶ X` and `f' : X' ⟶ Y'`, and an abelian torsion sheaf
`F` on `X_étale`, `g⁻¹ Rᵠ f_* F ≅ Rᵠ f'_* (g')⁻¹ F` for every `q`. -/
@[sga "4 XII 5.1"]
def rightDerivedDirectImageProperBaseChangeIso {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (sq : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (q : ℕ) :
    (etaleAbelianInverseImage.{u, 0} g).obj
        (((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj F) ≅
      ((etaleAbelianDirectImage.{u, 0} f').rightDerived q).obj
        ((etaleAbelianInverseImage.{u, 0} g').obj F) :=
  have := isIso_etaleAbelianSheafDerivedBaseChange_of_isProper f g g' f' sq F hF
  letI := isGrothendieckAbelian_sheaf_smallEtale.{u, 0} X
  letI := isGrothendieckAbelian_sheaf_smallEtale.{u, 0} X'
  (etaleAbelianInverseImage.{u, 0} g).mapIso
      (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
        (etaleAbelianDirectImage.{u, 0} f) (etaleAbelianDerivedDirectImage.{u, 0} f)
        (etaleAbelianDerivedDirectImageUnit.{u, 0} f)
        (fun K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ ↦
          Stacks.DerivedFunctor.exists_quasiIso_isKInjective K) F q).symm ≪≫
    (((etaleAbelianInverseImage.{u, 0} g).mapDerivedCategoryHomologyIso q).app
      ((etaleAbelianDerivedDirectImage.{u, 0} f).obj
        ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
          F))).symm ≪≫
    (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
      (q : ℤ)).mapIso
      (asIso (etaleAbelianSheafDerivedBaseChange.{u, 0} f g g' f' sq.w F)) ≪≫
    (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
      (q : ℤ)).mapIso
      ((etaleAbelianDerivedDirectImage.{u, 0} f').mapIso
        (((etaleAbelianInverseImage.{u, 0} g').mapDerivedCategorySingleFunctor 0).app F)) ≪≫
    Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
      (etaleAbelianDirectImage.{u, 0} f') (etaleAbelianDerivedDirectImage.{u, 0} f')
      (etaleAbelianDerivedDirectImageUnit.{u, 0} f')
      (fun K : CochainComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ ↦
        Stacks.DerivedFunctor.exists_quasiIso_isKInjective K) _ q

end

end Stacks.EtaleCohomology

end
