module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstantCoefficientsEquivalence
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso

/-!
# The constant coefficients equivalence on complexes and on derived categories

`AlgebraicGeometry.ProEtale.coefficientModuleSheafEquivalence` identifies sheaves of modules over
the constant coefficient ring sheaf on the small pro-étale site of `X` with sheaves of `Λ`-modules.
Both of its functors are exact, being quasi-inverse equivalences of abelian categories, so the
identification carries to cochain complexes and to the unbounded derived categories. In particular
`AlgebraicGeometry.ProEtale.DerivedSheaves`, the category `D(X_proét, Λ)` of Stacks 09C5, is
equivalent to the derived category of sheaves of `Λ`-modules on the small pro-étale site.

## Main results

* `AlgebraicGeometry.ProEtale.isEquivalence_mapHomologicalComplex_toCoefficientModuleSheaf`: the
  identification on cochain complexes.
* `AlgebraicGeometry.ProEtale.derivedCoefficientModuleSheafEquivalence`: the identification on
  the unbounded derived categories.
* `AlgebraicGeometry.ProEtale.derivedCoefficientModuleSheafEquivalence_functor`: its functor is
  the derived functor of `AlgebraicGeometry.ProEtale.toCoefficientModuleSheaf`.

## Implementation notes

Both are instances of the general transport
`StacksDraft.DerivedRingIso.isEquivalence_mapHomologicalComplex` and
`StacksDraft.DerivedRingIso.mapDerivedCategoryEquivalence`, which take the equivalence presented
as two functors together with the two natural isomorphisms rather than as a
`CategoryTheory.Equivalence`, so that the exactness hypotheses are stated at the functors
themselves. The isomorphisms are
`AlgebraicGeometry.ProEtale.constantCoefficientsCounitIso` and
`AlgebraicGeometry.ProEtale.constantCoefficientsUnitIso`, reversed.

Exactness of the two functors is not hypothesized: it is found by instance search from
`AlgebraicGeometry.ProEtale.toCoefficientModuleSheaf_isEquivalence` and
`AlgebraicGeometry.ProEtale.moduleSheafOverConstantCoefficientsFunctor_isEquivalence`. Additivity
is `AlgebraicGeometry.ProEtale.toCoefficientModuleSheaf_additive` and
`AlgebraicGeometry.ProEtale.moduleSheafOverConstantCoefficientsFunctor_additive`.

## References

* [Stacks Project, Tag 09C5](https://stacks.math.columbia.edu/tag/09C5)
* [Stacks Project, Tag 09BE](https://stacks.math.columbia.edu/tag/09BE)
* [Stacks Project, Tag 093T](https://stacks.math.columbia.edu/tag/093T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

variable (X : Scheme.{u}) (Λ : Type r) [CommRing Λ]

/-- **The constant coefficients equivalence on cochain complexes.** A cochain complex of sheaves
of modules over the constant coefficient ring sheaf is the same thing as a cochain complex of
sheaves of `Λ`-modules. -/
theorem isEquivalence_mapHomologicalComplex_toCoefficientModuleSheaf :
    ((toCoefficientModuleSheaf.{u, r, w} X Λ).mapHomologicalComplex
      (ComplexShape.up ℤ)).IsEquivalence :=
  StacksDraft.DerivedRingIso.isEquivalence_mapHomologicalComplex
    (toCoefficientModuleSheaf.{u, r, w} X Λ)
    (moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ)
    (constantCoefficientsCounitIso.{u, r, w} X Λ).symm
    (constantCoefficientsUnitIso.{u, r, w} X Λ).symm

/-- **The constant coefficients equivalence on derived categories.** `D(X_proét, Λ)`, the derived
category of sheaves of modules over the constant coefficient ring sheaf, is equivalent to the
derived category of sheaves of `Λ`-modules on the small pro-étale site. -/
def derivedCoefficientModuleSheafEquivalence :
    DerivedSheaves.{u, r, w} X Λ ≌
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ)) :=
  StacksDraft.DerivedRingIso.mapDerivedCategoryEquivalence
    (toCoefficientModuleSheaf.{u, r, w} X Λ)
    (moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ)
    (constantCoefficientsCounitIso.{u, r, w} X Λ).symm
    (constantCoefficientsUnitIso.{u, r, w} X Λ).symm

/-- The functor of the equivalence of derived categories is the derived functor of
`AlgebraicGeometry.ProEtale.toCoefficientModuleSheaf`. -/
theorem derivedCoefficientModuleSheafEquivalence_functor :
    (derivedCoefficientModuleSheafEquivalence.{u, r, w} X Λ).functor =
      (toCoefficientModuleSheaf.{u, r, w} X Λ).mapDerivedCategory :=
  rfl

end AlgebraicGeometry.ProEtale

end
