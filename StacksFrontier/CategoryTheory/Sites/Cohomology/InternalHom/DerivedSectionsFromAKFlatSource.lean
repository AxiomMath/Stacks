module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsViaAKInjectiveModel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.KFlatIntoKInjectiveIsKInjective
import StacksCore.Tactic.StacksAttribute

/-! # Derived sections of the derived internal Hom out of a K-flat complex

Let `(C, O)` be a ringed site, let `A` be a K-flat complex of `O`-modules and let `I` be a
K-injective complex of `O`-modules. `StacksDraft.Ch21.Sec34.DerivedHomSectionsOnKInjectiveModel`
identifies the degree-zero hypercohomology of the derived internal Hom `RSheafHom(A, I)`, over an
object of the site and globally, with the groups of derived-category morphisms `A|_U ⟶ I|_U` and
`A ⟶ I`, under the hypothesis that the internal Hom complex `SheafHom(A, I)` is K-injective.
For a K-flat `A` that hypothesis is **Stacks 0A96**, which
`StacksDraft.Ch21.Sec34.KInjectiveSheafHomOfKFlat` proves; this file records the two
identifications with K-flatness of `A` in its place.

This is the step of Stacks 08JA at a chosen pair of representatives. Stacks 08JA itself asserts
the two identifications for arbitrary objects of the derived category, and deduces them from the
statements here by choosing a K-injective representative of one object and a K-flat
representative of the other (`Stacks.SheafOfModules.exists_kFlat_quasiIso`, Stacks 06YS) and
transporting along the naturality of the three comparisons listed in
`StacksDraft.Ch21.Sec34.DerivedHomSectionsOnKInjectiveModel`; that choice and that transport are
what remain of 08JA, and nothing here carries its tag.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquivOfKFlat`: the local identification.
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat`: the global
  identification.

## Implementation notes

The K-injectivity of `SheafHom(A, I)` is an instance argument of the two statements being
specialised, so it is introduced with `haveI` from
`AlgebraicGeometry.RingedSite.isKInjective_sheafHomComplex_of_isKFlat` before they are applied.

The derived category instance is `CategoryTheory.HasDerivedCategory.standard`, switched on
file-locally exactly as in `StacksDraft.Ch21.Sec34.DerivedHomSectionsOnKInjectiveModel`, so that
the two statements are read at the same spelling of the derived category as the results they
specialise.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **Stacks 08JA over an object, at a K-flat source and a K-injective target.** If `A` is
K-flat and `I` is K-injective, the degree-zero hypercohomology over `U` of the derived internal
Hom of the classes of `A` and `I` is the group of morphisms `A|_U ⟶ I|_U` in the derived
category of `O|_U`-modules. -/
noncomputable def derivedSheafHomSectionsEquivOfKFlat (U : X.C)
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [I.IsKInjective] :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
            (DerivedCategory.Q.obj I))) : Type u) ≃+
      (DerivedCategory.Q.obj (restrictComplex X A U) ⟶
        DerivedCategory.Q.obj (restrictComplex X I U)) :=
  haveI := isKInjective_sheafHomComplex_of_isKFlat X A I hA
  derivedSheafHomSectionsEquivOfKInjectiveHom X U A I

/-- **Stacks 08JA globally, at a K-flat source and a K-injective target.** If `A` is K-flat and
`I` is K-injective, the degree-zero global hypercohomology of the derived internal Hom of the
classes of `A` and `I` is the group of morphisms `A ⟶ I` in the derived category of
`O`-modules. -/
noncomputable def derivedSheafHomGlobalSectionsEquivOfKFlat
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [I.IsKInjective] :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections X).obj
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
            (DerivedCategory.Q.obj I))) : Type u) ≃+
      (DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj I) :=
  haveI := isKInjective_sheafHomComplex_of_isKFlat X A I hA
  derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X A I

end AlgebraicGeometry.RingedSite

end
