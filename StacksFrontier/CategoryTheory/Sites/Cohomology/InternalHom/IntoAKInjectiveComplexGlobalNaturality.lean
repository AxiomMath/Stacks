module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalHomNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplex

/-! # Naturality of the global computation of derived-category morphisms

Let `(C, O)` be a ringed site, let `L` be a complex of `O`-modules and let `I` be a K-injective
complex of `O`-modules. **Stacks 0A94** identifies the degree-zero cohomology of the global
sections of the internal Hom complex `SheafHom(L, I)` with `Hom_{D(O)}(L, I)`; that
identification is `AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom`.
That it is **natural in both variables** for the functoriality
`AlgebraicGeometry.RingedSite.homMap` of the internal Hom complex is
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalHomNaturality`, together with the
homotopy-category morphism `AlgebraicGeometry.RingedSite.sheafHomGlobalHomotopyCategoryHom` and
`AlgebraicGeometry.RingedSite.globalSectionsIso_homMap`. This file supplies the packaging of the
first two steps of Stacks 0A8Z that the consumers here read it through.

## Main definitions

* `AlgebraicGeometry.RingedSite.globalHomologyClassEquiv`: the degree-`n` cohomology of the
  global sections of `SheafHom(L, M)`, identified with the degree-`n` cohomology of the ordinary
  Hom complex of `L` and `M` — the first two steps of Stacks 0A8Z, with the universe lift
  removed.

## Main results

* `AlgebraicGeometry.RingedSite.globalHomologyClassEquiv_naturality`: it is natural in both
  variables for `homMap`.
* `AlgebraicGeometry.RingedSite.sheafHomGlobalHomotopyCategoryHom_eq_globalHomologyClassEquiv`:
  the homotopy-category morphism attached to a degree-zero class, read through it.

## Implementation notes

The global identification of Stacks 0A8Z carries a universe lift that the local one does not:
the complex of global sections of a complex of `O`-modules lives in the universe of the objects
of the site as well as that of the modules, so the `globalSectionsIso` field of
`AlgebraicGeometry.RingedSite.SheafHomComplex` compares it with the image of the Hom complex
under `AddCommGrpCat.uliftFunctor`. `globalHomologyClassEquiv` absorbs that lift, using
`CategoryTheory.ShortComplex.mapHomologyIso` and its naturality, so that the remaining steps
are literally those of the local argument.

The statements are given on the diagonal universes `RingedSite.{u, u, u}`, as the consumers of
the naturality need them; `globalSectionsIso_homMap_v`, which is the only input, is available in
greater universe generality.

## References

* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The degree-`n` cohomology of the global sections of the internal Hom complex from `L` to
`M`, identified with the degree-`n` cohomology of the ordinary Hom complex of `L` and `M`: the
global description of the internal Hom complex, followed by the universe lift of Stacks 0A8Z
read on homology. -/
noncomputable def globalHomologyClassEquiv
    (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    (globalSectionsComplex X (sheafHomComplex X L M).obj).homology n ≃+
      (L.HomComplex M).homology n :=
  (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
        (sheafHomComplex X L M).globalSectionsIso).addCommGroupIsoToAddEquiv).trans
    ((((L.HomComplex M).sc n).mapHomologyIso
        AddCommGrpCat.uliftFunctor.{u}).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- `globalHomologyClassEquiv` spelled out: the map induced on homology by the global
description, followed by the identification of the homology of the lifted Hom complex with that
of the Hom complex. -/
theorem globalHomologyClassEquiv_apply
    (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ)
    (η : (globalSectionsComplex X (sheafHomComplex X L M).obj).homology n) :
    globalHomologyClassEquiv X L M n η =
      AddEquiv.ulift ((((L.HomComplex M).sc n).mapHomologyIso AddCommGrpCat.uliftFunctor.{u}).hom
        (HomologicalComplex.homologyMap (sheafHomComplex X L M).globalSectionsIso.hom n η)) :=
  rfl

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **Stacks 0A8Z is `globalHomologyClassEquiv` followed by the identification of the
cohomology of a Hom complex with homotopy-category morphisms.** -/
theorem sheafHomComplexHomologyEquivHomotopyCategory_eq
    (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ)
    (η : (globalSectionsComplex X (sheafHomComplex X L M).obj).homology n) :
    sheafHomComplexHomologyEquivHomotopyCategory X L M n η =
      CohomologyClass.homAddEquiv (homologyAddEquiv L M n
        (globalHomologyClassEquiv X L M n η)) := rfl

/-- `globalHomologyClassEquiv` is natural in both variables for `homMap`: it carries the map
induced by `homMap k m` on global sections to the map induced by the pre- and postcomposition
morphism `homComplexConj k m` of Hom complexes. -/
theorem globalHomologyClassEquiv_naturality
    {L L' M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : L' ⟶ L) (m : M ⟶ M')
    (n : ℤ) (η : (globalSectionsComplex X (sheafHomComplex X L M).obj).homology n) :
    globalHomologyClassEquiv X L' M' n
        (HomologicalComplex.homologyMap (globalSectionsComplexMap X (homMap X k m)) n η) =
      HomologicalComplex.homologyMap (homComplexConj k m) n
        (globalHomologyClassEquiv X L M n η) := by
  have h1 : HomologicalComplex.homologyMap
        (globalSectionsComplexMap X (homMap X k m)) n ≫
          HomologicalComplex.homologyMap (sheafHomComplex X L' M').globalSectionsIso.hom n =
      HomologicalComplex.homologyMap (sheafHomComplex X L M).globalSectionsIso.hom n ≫
        HomologicalComplex.homologyMap
          ((AddCommGrpCat.uliftFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (homComplexConj k m)) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      globalSectionsIso_homMap]
  have h2 : HomologicalComplex.homologyMap
        ((AddCommGrpCat.uliftFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (homComplexConj k m)) n ≫
          (((L'.HomComplex M').sc n).mapHomologyIso AddCommGrpCat.uliftFunctor.{u}).hom =
      (((L.HomComplex M).sc n).mapHomologyIso AddCommGrpCat.uliftFunctor.{u}).hom ≫
        AddCommGrpCat.uliftFunctor.{u}.map
          (HomologicalComplex.homologyMap (homComplexConj k m) n) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n).map
        (homComplexConj k m)) AddCommGrpCat.uliftFunctor.{u}
  have e1 : HomologicalComplex.homologyMap (sheafHomComplex X L' M').globalSectionsIso.hom n
        (HomologicalComplex.homologyMap (globalSectionsComplexMap X (homMap X k m)) n η) =
      HomologicalComplex.homologyMap
          ((AddCommGrpCat.uliftFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (homComplexConj k m)) n
        (HomologicalComplex.homologyMap (sheafHomComplex X L M).globalSectionsIso.hom n η) :=
    ConcreteCategory.congr_hom h1 η
  have e2 : (((L'.HomComplex M').sc n).mapHomologyIso AddCommGrpCat.uliftFunctor.{u}).hom
        (HomologicalComplex.homologyMap
          ((AddCommGrpCat.uliftFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (homComplexConj k m)) n
          (HomologicalComplex.homologyMap (sheafHomComplex X L M).globalSectionsIso.hom n η)) =
      AddCommGrpCat.uliftFunctor.{u}.map (HomologicalComplex.homologyMap (homComplexConj k m) n)
        ((((L.HomComplex M).sc n).mapHomologyIso AddCommGrpCat.uliftFunctor.{u}).hom
          (HomologicalComplex.homologyMap (sheafHomComplex X L M).globalSectionsIso.hom n η)) :=
    ConcreteCategory.congr_hom h2 _
  rw [globalHomologyClassEquiv_apply, globalHomologyClassEquiv_apply]
  exact congrArg _
    ((congrArg (fun z => (((L'.HomComplex M').sc n).mapHomologyIso
      AddCommGrpCat.uliftFunctor.{u}).hom z) e1).trans e2)

/-- The cohomology class of the global section complex attached to `homMap k m` is the class
attached to the original one, precomposed with `k` and postcomposed with `m`. -/
theorem homologyAddEquiv_globalHomologyClassEquiv_homMap
    {L L' M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : L' ⟶ L) (m : M ⟶ M')
    (η : (globalSectionsComplex X (sheafHomComplex X L M).obj).homology 0) :
    homologyAddEquiv L' M' 0 (globalHomologyClassEquiv X L' M' 0
        (HomologicalComplex.homologyMap (globalSectionsComplexMap X (homMap X k m)) 0 η)) =
      cohomologyClassPrecomp k M' 0 (cohomologyClassPostcomp L m 0
        (homologyAddEquiv L M 0 (globalHomologyClassEquiv X L M 0 η))) := by
  rw [globalHomologyClassEquiv_naturality, homologyAddEquiv_conj]

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- `AlgebraicGeometry.RingedSite.sheafHomGlobalHomotopyCategoryHom` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalHomNaturality`, in terms of
`globalHomologyClassEquiv`. -/
theorem sheafHomGlobalHomotopyCategoryHom_eq_globalHomologyClassEquiv
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (η : (globalSectionsComplex X (sheafHomComplex X L I).obj).homology 0) :
    sheafHomGlobalHomotopyCategoryHom X L I η =
      (𝟙 _ ≫ CohomologyClass.homAddEquiv
          (homologyAddEquiv L I 0 (globalHomologyClassEquiv X L I 0 η))) ≫
        (HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).map
          ((shiftFunctorZero
            (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
            ℤ).app I).hom :=
  rfl

end AlgebraicGeometry.RingedSite

end
