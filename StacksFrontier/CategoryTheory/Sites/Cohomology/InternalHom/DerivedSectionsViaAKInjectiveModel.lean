module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.DerivedGlobalSectionsOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Derived sections of the derived internal Hom, on a K-injective internal Hom complex

Let `(C, O)` be a ringed site, let `A` be a complex of `O`-modules and let `I` be a K-injective
complex of `O`-modules. If the internal Hom complex `SheafHom(A, I)` is itself K-injective, then
the degree-zero hypercohomology of the derived internal Hom `RSheafHom(A, I)` over an object `U`
of the site is the group of morphisms `A|_U ⟶ I|_U` in the derived category of `O|_U`-modules,
and its degree-zero global hypercohomology is the group of morphisms `A ⟶ I` in the derived
category of `O`-modules.

Both identifications are the composite of three comparisons:

1. a K-injective target computes the derived internal Hom, so `RSheafHom(A, I)` is the class of
   `SheafHom(A, I)` (`AlgebraicGeometry.RingedSite.derivedSheafHomComparison`, Stacks 0A97);
2. sections compute derived sections on a K-injective complex, applied to `SheafHom(A, I)`
   (`Stacks.Cohomology.ModuleSections.sectionsKInjectiveIso` and
   `Stacks.Cohomology.ModuleSections.globalSectionsKInjectiveIso`, Stacks 07A5);
3. the degree-zero cohomology of the complex of sections of the internal Hom complex into a
   K-injective complex is the group of derived-category morphisms
   (`AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom` and
   `AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom`, Stacks 0A94).

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquivOfKInjectiveHom`: the local
  identification.
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKInjectiveHom`: the global
  identification.

## Implementation notes

**This is not Stacks 08JA, and nothing here carries that tag.** Stacks 08JA asserts the two
identifications for arbitrary objects `L`, `M` of `D(O)`, and deduces them from the case treated
here by choosing a K-injective representative `I` of `M` and a *K-flat* representative `A` of
`L`, for which `SheafHom(A, I)` is K-injective by Stacks 0A96. That K-injectivity is the one
input of 08JA which is not available: it is proved in the source from the currying isomorphism
`SheafHom(K, SheafHom(A, I)) = SheafHom(Tot(K ⊗ A), I)` of Stacks 0A90 (2), which is not
formalized — `StacksDraft.Ch21.Sec34.HomComplexTensorCurrying` supplies only part (1) of
Stacks 0A90, the functoriality of the internal Hom complex. So the K-injectivity of
`SheafHom(A, I)` is carried here as a hypothesis, where discharging it by Stacks 0A96 together
with a K-flat resolution (`Stacks.SheafOfModules.exists_kFlat_quasiIso`, Stacks 06YS) and the
naturality of the three comparisons above is exactly what remains of 08JA.

The source of each identification is the degree-zero cohomology of an object of the derived
category of abelian groups, read through `DerivedCategory.homologyFunctor`; its target is a
group of morphisms, and the comparison is stated as an additive equivalence rather than a
bijection, as in Stacks 0A94. The restrictions `A|_U` and `I|_U` are the degreewise restrictions
`AlgebraicGeometry.RingedSite.restrictComplex`, again as in Stacks 0A94.

## References

* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- **Stacks 08JA over an object, on a K-injective internal Hom complex.** If `I` is K-injective
and the internal Hom complex `SheafHom(A, I)` is K-injective, then the degree-zero
hypercohomology over `U` of the derived internal Hom of the classes of `A` and `I` is the group
of morphisms `A|_U ⟶ I|_U` in the derived category of `O|_U`-modules. -/
noncomputable def derivedSheafHomSectionsEquivOfKInjectiveHom (U : X.C)
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] [((sheafHomComplex X A I).obj).IsKInjective] :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
            (DerivedCategory.Q.obj I))) : Type u) ≃+
      (DerivedCategory.Q.obj (restrictComplex X A U) ⟶
        DerivedCategory.Q.obj (restrictComplex X I U)) :=
  (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).mapIso
            (derivedSheafHomComparison X A I) ≪≫
          (sectionsKInjectiveIso X U ((sheafHomComplex X A I).obj)).symm) ≪≫
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).app
        (sectionComplex X (sheafHomComplex X A I).obj U)).addCommGroupIsoToAddEquiv).trans
    (sheafHomSectionHomologyEquivDerivedCategoryHom X A I U)

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 08JA globally, on a K-injective internal Hom complex.** If `I` is K-injective and
the internal Hom complex `SheafHom(A, I)` is K-injective, then the degree-zero global
hypercohomology of the derived internal Hom of the classes of `A` and `I` is the group of
morphisms `A ⟶ I` in the derived category of `O`-modules. -/
noncomputable def derivedSheafHomGlobalSectionsEquivOfKInjectiveHom
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] [((sheafHomComplex X A I).obj).IsKInjective] :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections X).obj
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
            (DerivedCategory.Q.obj I))) : Type u) ≃+
      (DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj I) :=
  (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
        ((derivedModuleGlobalSections X).mapIso (derivedSheafHomComparison X A I) ≪≫
          (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).symm) ≪≫
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).app
        (globalSectionsComplex X (sheafHomComplex X A I).obj)).addCommGroupIsoToAddEquiv).trans
    (sheafHomGlobalHomologyEquivDerivedCategoryHom X A I)

end AlgebraicGeometry.RingedSite

end
