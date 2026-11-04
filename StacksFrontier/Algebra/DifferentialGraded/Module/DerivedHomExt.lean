module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction
public import StacksFrontier.Algebra.DifferentialGraded.Module.ExtLinear
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomCohomology
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomShiftFunctor
public import StacksFrontier.CategoryTheory.Functor.Derived.CoresolutionCriterion
public import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology of derived Hom is Ext in the derived category

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. Tag 0CS5 asserts, for every `n`, an isomorphism of
`R`-modules

`H^n(RHom(N, M)) = Ext^n_{D(B,d)}(N, M) = Hom_{D(B,d)}(N, M[n])`,

functorial in `M` and contravariantly functorial in `N` with respect to the operation of
Tag 0BYV.

## Main definitions

* `DifferentialGradedModule.extFunctor`: `Ext^n_{D(B,d)}(N, -)`, as a functor `D(B,d) ⥤ Mod_R`.
* `DifferentialGradedModule.extCohomologyFunctor`: degree-`n` cohomology on `D(A, d)`, with
  values lifted to the universe of the morphism modules of a derived category.
* `DifferentialGradedModule.homShiftCohomologyFunctor`: the functor on `K(B, d)` whose right
  derived functor the left-hand side is, namely ordinary internal hom out of `N` read in
  `D(A, d)`, shifted by `n`, and then degree-`0` cohomology.
* `DifferentialGradedModule.extComparisonUnit`: the comparison from that functor to
  `Ext^n_{D(B,d)}(N, -)` read on `K(B, d)`.

## Main results

* `DifferentialGradedModule.homShiftCohomologyIso`: on `K(B, d)` the functor being derived is the
  `n`-shifted morphism module of the homotopy category — Tag 09LC and Tag 0FQR together.

## Implementation notes

The comparison map `DifferentialGradedModule.extComparisonUnit` on `K(B, d)` is assembled from
the identification of degree-zero cohomology of the internal hom with the morphism module of the
homotopy category (Tag 09LC, `DifferentialGradedModule.homCohomologyZeroNatIso`), the
commutation of the internal hom functor with the shift (Tag 0FQR,
`DifferentialGradedModule.homHomotopyCategoryFunctorShiftIso`), the restriction of degree-zero
cohomology on `D(A, d)` to `K(A, d)`
(`DifferentialGradedModule.degreeZeroCohomologyOnLocalizationIso'`) and the localization map on
morphism modules.

Cohomology of a differential graded module is a module in the universe `u` of the base ring,
while the morphism modules of the derived category lie in `Type (u + 1)`. Degree-zero cohomology
is therefore composed with `ModuleCat.uliftFunctor`, so that both sides are functors into
`ModuleCat.{u + 1} R`.

## References

* [Stacks Project, Tag 0CS5](https://stacks.math.columbia.edu/tag/0CS5); the derived functor is
  [Tag 09LI](https://stacks.math.columbia.edu/tag/09LI), the morphism-set computation is
  [Tag 09KY](https://stacks.math.columbia.edu/tag/09KY), the resolutions are
  [Tag 09KU](https://stacks.math.columbia.edu/tag/09KU), their orthogonality is
  [Tag 09KS](https://stacks.math.columbia.edu/tag/09KS) and the functoriality in `N` is
  [Tag 0BYV](https://stacks.math.columbia.edu/tag/0BYV).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A B : DifferentialGradedAlgebra.{u, u} R)
  (N : DifferentialGradedModule.{u, u, u} B) (L : BimoduleStructure A B N)

/-! ### The two functors -/

/-- `Ext^n_{D(B,d)}(N, -) = Hom_{D(B,d)}(N, (-)[n])`, as a functor `D(B, d) ⥤ Mod_R`. The
`R`-module structure on the morphisms of `D(B, d)` is the one of
`DifferentialGradedModule.instLinearDerivedCategory`. -/
def extFunctor (n : ℤ) : derivedCategory' B ⥤ ModuleCat.{u + 1} R :=
  CategoryTheory.shiftFunctor (derivedCategory' B) n ⋙
    (linearCoyoneda R (derivedCategory' B)).obj
      (Opposite.op ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj N)))

/-- Degree-`n` cohomology on `D(A, d)`: the `n`-shift followed by degree-zero cohomology, with
values lifted to the universe of the morphism modules of a derived category. -/
def extCohomologyFunctor (n : ℤ) : derivedCategory' A ⥤ ModuleCat.{u + 1} R :=
  CategoryTheory.shiftFunctor (derivedCategory' A) n ⋙
    (degreeZeroCohomologyOnLocalization' A ⋙ ModuleCat.uliftFunctor.{u + 1, u} R)

/-- The functor on `K(B, d)` whose right derived functor is the degree-`n` cohomology of derived
Hom: ordinary internal hom out of `N`, read in `D(A, d)`, and then degree-`n` cohomology. -/
def homShiftCohomologyFunctor (n : ℤ) : HomotopyCategory B ⥤ ModuleCat.{u + 1} R :=
  homToDerivedCategory A B N L ⋙ extCohomologyFunctor A n

/-! ### The comparison map on the homotopy category -/

/-- **Degree-`n` cohomology of ordinary internal hom is `Hom_{K(B,d)}(N, (-)[n])`.** This is
Tag 09LC, which identifies degree-zero cohomology of the internal hom with the morphism module of
the homotopy category, together with Tag 0FQR, which moves the shift across the internal hom. -/
def homShiftCohomologyIso (n : ℤ) :
    homHomotopyCategoryFunctor A B N L ⋙ ((quasiIsomorphisms' A).Q ⋙
        (CategoryTheory.shiftFunctor (derivedCategory' A) n ⋙
          degreeZeroCohomologyOnLocalization' A)) ≅
      CategoryTheory.shiftFunctor (HomotopyCategory B) n ⋙
        (linearCoyoneda R (HomotopyCategory B)).obj
          (Opposite.op ((toHomotopyCategory B).obj N)) :=
  Functor.isoWhiskerLeft (homHomotopyCategoryFunctor A B N L)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (((quasiIsomorphisms' A).Q.commShiftIso n).symm)
          (degreeZeroCohomologyOnLocalization' A) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (CategoryTheory.shiftFunctor (HomotopyCategory A) n)
          (degreeZeroCohomologyOnLocalizationIso' A)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (homHomotopyCategoryFunctorShiftIso A B N L n)
      (degreeZeroCohomologyOnHomotopy' A) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (CategoryTheory.shiftFunctor (HomotopyCategory B) n)
      (homCohomologyZeroNatIso A B N L)

/-- `DifferentialGradedModule.homShiftCohomologyIso` with values in the universe of the morphism
modules of a derived category. -/
def homShiftCohomologyUliftIso (n : ℤ) :
    homShiftCohomologyFunctor A B N L n ≅
      CategoryTheory.shiftFunctor (HomotopyCategory B) n ⋙
        ((linearCoyoneda R (HomotopyCategory B)).obj
            (Opposite.op ((toHomotopyCategory B).obj N)) ⋙
          ModuleCat.uliftFunctor.{u + 1, u} R) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.associator _ _ _).symm ≪≫ homShiftCohomologyIso A B N L n)
      (ModuleCat.uliftFunctor.{u + 1, u} R) ≪≫
    Functor.associator _ _ _

/-- `Ext^n_{D(B,d)}(N, -)` read on `K(B, d)`, with the shift moved to the homotopy category. -/
def extFunctorRestrictedIso (n : ℤ) :
    (quasiIsomorphisms' B).Q ⋙ extFunctor B N n ≅
      CategoryTheory.shiftFunctor (HomotopyCategory B) n ⋙
        ((quasiIsomorphisms' B).Q ⋙ (linearCoyoneda R (derivedCategory' B)).obj
          (Opposite.op ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj N)))) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (((quasiIsomorphisms' B).Q.commShiftIso n).symm) _ ≪≫
    Functor.associator _ _ _

/-- The localization functor on morphism modules, as a natural transformation of the two
co-Yoneda functors out of `N`. -/
def coyonedaLocalizationMap :
    (linearCoyoneda R (HomotopyCategory B)).obj
          (Opposite.op ((toHomotopyCategory B).obj N)) ⋙
        ModuleCat.uliftFunctor.{u + 1, u} R ⟶
      (quasiIsomorphisms' B).Q ⋙ (linearCoyoneda R (derivedCategory' B)).obj
        (Opposite.op ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj N))) where
  app X := ModuleCat.ofHom
    (((quasiIsomorphisms' B).Q.mapLinearMap R).comp
      (ULift.moduleEquiv (R := R)
        (M := ((toHomotopyCategory B).obj N ⟶ X))).toLinearMap)
  naturality _ _ g :=
    ModuleCat.hom_ext (LinearMap.ext fun f => (quasiIsomorphisms' B).Q.map_comp f.down g)

/-- **The comparison map of Tag 0CS5 on the homotopy category.** A degree-`n` cohomology class of
the ordinary internal hom out of `N` is a homotopy class of closed degree-`n` homogeneous maps
`N → M`, that is, a morphism `N ⟶ M[n]` of `K(B, d)`; the comparison sends it to its image in
`D(B, d)`. -/
def extComparisonUnit (n : ℤ) :
    homShiftCohomologyFunctor A B N L n ⟶
      (quasiIsomorphisms' B).Q ⋙ extFunctor B N n :=
  (homShiftCohomologyUliftIso A B N L n).hom ≫
    Functor.whiskerLeft (CategoryTheory.shiftFunctor (HomotopyCategory B) n)
      (coyonedaLocalizationMap B N) ≫
    (extFunctorRestrictedIso B N n).inv

end DifferentialGradedModule

end
