module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModelIndependence

/-!
# The ingredients of the model-independence of Tag 08JA over an object of the site

Let `(C, O)` be a ringed site and `U` an object of `C`.  The degree-zero identification
`H⁰(U, RSheafHom(L, M)) = Hom_{D(O|_U)}(L|_U, M|_U)` of Tag 08JA,
`AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv`, is constructed by choosing a K-flat
complex representing `L` and a K-injective complex representing `M` and transporting the
identification at that pair.  This file assembles the inputs needed to see that the result does
not depend on those choices; the naturality itself is
`AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv_naturality` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsOverAnObjectNaturality`.

Everything below is the statement over `U` of a declaration that
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomTransport` and
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModelIndependence` make
for global sections.  All of them reduce to the naturality of Tag 0A94 in both variables, which
is available for morphisms of complexes as
`AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom_naturality`; that
is the one input of this file that is not a transcription.

## Main definitions

* `AlgebraicGeometry.RingedSite.sectionsOverObjectDerivedUnit` and
  `AlgebraicGeometry.RingedSite.sectionsOverObjectDerivedUnitNatTrans`: the comparison from the
  class of the complex of sections over `U` to derived sections over `U`, pointwise and as a
  natural transformation.

## Main results

* `AlgebraicGeometry.RingedSite.sectionsKInjectiveIso_hom_naturality` and
  `AlgebraicGeometry.RingedSite.sectionsKInjectiveIso_inv_naturality`: Tag 07A5 over `U` is
  natural on K-injective complexes.
* `AlgebraicGeometry.RingedSite.derivedSheafHom_comparison_sections_naturality`: the two
  comparisons out of which the degree-zero reading over `U` is built are natural for morphisms
  of complexes.
* `AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquivOfKInjectiveHom_apply_of_isKInjective`
  and `derivedSheafHomSectionsEquivOfKInjectiveHom_naturality_of_isKInjective`: Tag 08JA
  over `U` at a representative pair, unfolded, and its naturality in both variables for
  morphisms of complexes.
* `AlgebraicGeometry.RingedSite.restrictModelIso_hom_naturality`: the comparison of the class of
  a restricted complex with the restriction of a class is natural.  This is what transports the
  two defining equations of the common refinement to the slice over `U`, and is the only
  ingredient with no global counterpart.
* `AlgebraicGeometry.RingedSite.isIso_Q_map_restrictComplexMap`: restriction to the slice keeps
  the class of a morphism of complexes invertible.
* `AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv_apply_of_isKInjective` and
  `AlgebraicGeometry.RingedSite.transport_arg_eq_sections`: Tag 08JA over `U` at arbitrary
  objects, unfolded at the chosen models, and the identification of the two transports of the
  argument that the two applications of its naturality produce.

## Implementation notes

`AlgebraicGeometry.RingedSite.modelIso_route_eq_of_refinement` and
`AlgebraicGeometry.RingedSite.conj_of_refinement_of_category` mention no sections functor at all:
the first is a two-variable functoriality of the derived internal Hom and the second is a formal
identity in an arbitrary category, so they apply over `U` unchanged.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-! ### The comparison with derived sections over an object is natural -/

/-- **The comparison from sections over `U` to derived sections over `U`.** The class of the
complex of sections over `U` of a complex of `O`-modules maps canonically to its derived
sections over `U`; this is the unit of the derived functor, read through the identifications of
the localization with `Functor.mapHomologicalComplex`.  It is invertible on a K-injective
complex, which is `Stacks.Cohomology.ModuleSections.sectionsKInjectiveIso`. -/
def sectionsOverObjectDerivedUnit
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Q.obj (sectionComplex X H U) ⟶
      (Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
        (DerivedCategory.Q.obj H) :=
  ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).app (sectionComplex X H U)).inv ≫
    DerivedCategory.Qh.map
        (((Stacks.Cohomology.Localization.sectionsOverObject X U).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).app H).inv ≫
      (derivedSectionsOverObjectUnit X U).app
          ((HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).obj H) ≫
        (Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
          ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app H).hom

/-- **The comparison from sections over `U` to derived sections over `U`, as a natural
transformation.**  `AlgebraicGeometry.RingedSite.sectionsOverObjectDerivedUnit` is the composite
of four canonical morphisms, each the component of a natural transformation; this is the
composite of the four whiskerings. -/
def sectionsOverObjectDerivedUnitNatTrans :
    (Stacks.Cohomology.Localization.sectionsOverObject X U).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ Stacks.Cohomology.Localization.derivedSectionsOverObject X U :=
  Functor.whiskerLeft
      ((Stacks.Cohomology.Localization.sectionsOverObject X U).mapHomologicalComplex
        (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).inv ≫
    Functor.whiskerRight
        (((Stacks.Cohomology.Localization.sectionsOverObject X U).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).inv)
        DerivedCategory.Qh ≫
      Functor.whiskerLeft
          (HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ))
          (derivedSectionsOverObjectUnit X U) ≫
        Functor.whiskerRight
          (DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom
          (Stacks.Cohomology.Localization.derivedSectionsOverObject X U)

/-- The components of `AlgebraicGeometry.RingedSite.sectionsOverObjectDerivedUnitNatTrans` are
the comparisons `AlgebraicGeometry.RingedSite.sectionsOverObjectDerivedUnit`. -/
theorem sectionsOverObjectDerivedUnitNatTrans_app
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (sectionsOverObjectDerivedUnitNatTrans X U).app H = sectionsOverObjectDerivedUnit X U H := rfl

/-- **The comparison from sections over `U` to derived sections over `U` is natural** in the
complex, for morphisms of complexes. -/
theorem sectionsOverObjectDerivedUnit_naturality
    {H H' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : H ⟶ H') :
    DerivedCategory.Q.map (sectionComplexMap X U φ) ≫ sectionsOverObjectDerivedUnit X U H' =
      sectionsOverObjectDerivedUnit X U H ≫
        (Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
          (DerivedCategory.Q.map φ) :=
  (sectionsOverObjectDerivedUnitNatTrans X U).naturality φ

/-- **On a K-injective complex the comparison with derived sections over `U` is the isomorphism
of Tag 07A5.** Both are the same composite of four canonical morphisms, the invertible one among
them being inverted in `Stacks.Cohomology.ModuleSections.sectionsKInjectiveIso`. -/
theorem sectionsOverObjectDerivedUnit_eq_sectionsKInjectiveIso
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [H.IsKInjective] :
    sectionsOverObjectDerivedUnit X U H = (sectionsKInjectiveIso X U H).hom := rfl

/-- **Tag 07A5 over `U` is natural on K-injective complexes.** -/
theorem sectionsKInjectiveIso_hom_naturality
    {I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    (φ : I ⟶ I') :
    DerivedCategory.Q.map (sectionComplexMap X U φ) ≫ (sectionsKInjectiveIso X U I').hom =
      (sectionsKInjectiveIso X U I).hom ≫
        (@Stacks.Cohomology.Localization.derivedSectionsOverObject X U (_) (_)).map
          (DerivedCategory.Q.map φ) :=
  sectionsOverObjectDerivedUnit_naturality X U φ

/-- `AlgebraicGeometry.RingedSite.sectionsKInjectiveIso_hom_naturality` read on the inverses. -/
theorem sectionsKInjectiveIso_inv_naturality
    {I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    (φ : I ⟶ I') :
    (@Stacks.Cohomology.Localization.derivedSectionsOverObject X U (_) (_)).map
          (DerivedCategory.Q.map φ) ≫ (sectionsKInjectiveIso X U I').inv =
      (sectionsKInjectiveIso X U I).inv ≫ DerivedCategory.Q.map (sectionComplexMap X U φ) := by
  rw [Iso.comp_inv_eq, Category.assoc, sectionsKInjectiveIso_hom_naturality X U φ,
    Iso.inv_hom_id_assoc]


/-! ### Tag 08JA over an object, at a representative pair, is natural -/

/-- The two isomorphisms out of which the degree-zero reading of the derived hom over `U` is
built at a representative pair are natural in both variables for morphisms of complexes. -/
theorem derivedSheafHom_comparison_sections_naturality
    {A A' I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective]
    [((sheafHomComplex X A' I').obj).IsKInjective] (k : A' ⟶ A) (m : I ⟶ I') :
    (Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
          (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map k).op).app
              (DerivedCategory.Q.obj I) ≫
            ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
              (DerivedCategory.Q.map m)) ≫
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (derivedSheafHomComparison X A' I').hom ≫
          (sectionsKInjectiveIso X U ((sheafHomComplex X A' I').obj)).inv) =
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (derivedSheafHomComparison X A I).hom ≫
          (sectionsKInjectiveIso X U ((sheafHomComplex X A I).obj)).inv) ≫
        DerivedCategory.Q.map (sectionComplexMap X U (homMap X k m)) := by
  rw [Category.assoc, ← sectionsKInjectiveIso_inv_naturality X U (homMap X k m)]
  simp only [← Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, Category.assoc,
    derivedSheafHomComparison_naturality X k m]

/-- Tag 08JA over `U` at a representative pair, unfolded: the degree-zero reading of the
derived hom is the two comparisons followed by Tag 0A94. -/
theorem derivedSheafHomSectionsEquivOfKInjectiveHom_apply_of_isKInjective
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective]
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomSectionsEquivOfKInjectiveHom X U A I ξ =
      sheafHomSectionHomologyEquivDerivedCategoryHom X A I U
        (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).app
            (sectionComplex X (sheafHomComplex X A I).obj U)).hom
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
                (derivedSheafHomComparison X A I).hom ≫
              (sectionsKInjectiveIso X U ((sheafHomComplex X A I).obj)).inv) ξ)) := rfl

/-- **Tag 08JA over `U` at a representative pair is natural in both variables for morphisms of
complexes.** -/
theorem derivedSheafHomSectionsEquivOfKInjectiveHom_naturality_of_isKInjective
    {A A' I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective]
    [((sheafHomComplex X A' I').obj).IsKInjective] (k : A' ⟶ A) (m : I ⟶ I')
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomSectionsEquivOfKInjectiveHom X U A' I'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map k).op).app
                (DerivedCategory.Q.obj I) ≫
              ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
                (DerivedCategory.Q.map m))) ξ) =
      DerivedCategory.Q.map (restrictComplexMap X U k) ≫
        derivedSheafHomSectionsEquivOfKInjectiveHom X U A I ξ ≫
          DerivedCategory.Q.map (restrictComplexMap X U m) := by
  refine (derivedSheafHomSectionsEquivOfKInjectiveHom_apply_of_isKInjective X U A' I' _).trans ?_
  have h : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
          (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map k).op).app
              (DerivedCategory.Q.obj I) ≫
            ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
              (DerivedCategory.Q.map m))) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (derivedSheafHomComparison X A' I').hom ≫
          (sectionsKInjectiveIso X U ((sheafHomComplex X A' I').obj)).inv) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
              (derivedSheafHomComparison X A I).hom ≫
            (sectionsKInjectiveIso X U ((sheafHomComplex X A I).obj)).inv) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          (DerivedCategory.Q.map (sectionComplexMap X U (homMap X k m))) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (fun f => (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map f)
      (derivedSheafHom_comparison_sections_naturality X U k m)
  have hA : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (derivedSheafHomComparison X A' I').hom ≫
          (sectionsKInjectiveIso X U ((sheafHomComplex X A' I').obj)).inv)
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
          (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map k).op).app
              (DerivedCategory.Q.obj I) ≫
            ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
              (DerivedCategory.Q.map m))) ξ) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        (DerivedCategory.Q.map (sectionComplexMap X U (homMap X k m)))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
              (derivedSheafHomComparison X A I).hom ≫
            (sectionsKInjectiveIso X U ((sheafHomComplex X A I).obj)).inv) ξ) :=
    ConcreteCategory.congr_hom h ξ
  rw [hA]
  have hB : ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).app
        (sectionComplex X (sheafHomComplex X A' I').obj U)).hom
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        (DerivedCategory.Q.map (sectionComplexMap X U (homMap X k m)))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
              (derivedSheafHomComparison X A I).hom ≫
            (sectionsKInjectiveIso X U ((sheafHomComplex X A I).obj)).inv) ξ)) =
      HomologicalComplex.homologyMap (sectionComplexMap X U (homMap X k m)) 0
        (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).app
            (sectionComplex X (sheafHomComplex X A I).obj U)).hom
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
                (derivedSheafHomComparison X A I).hom ≫
              (sectionsKInjectiveIso X U ((sheafHomComplex X A I).obj)).inv) ξ)) :=
    ConcreteCategory.congr_hom
      ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.naturality
        (sectionComplexMap X U (homMap X k m)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (derivedSheafHomComparison X A I).hom ≫
          (sectionsKInjectiveIso X U ((sheafHomComplex X A I).obj)).inv) ξ)
  rw [hB]
  refine (sheafHomSectionHomologyEquivDerivedCategoryHom_naturality X k m U _).trans ?_
  rw [derivedSheafHomSectionsEquivOfKInjectiveHom_apply_of_isKInjective X U A I ξ]


/-! ### Transporting a representing isomorphism to the slice -/

/-- **The comparison of the class of a restricted complex with the restriction of a class is
natural.**  For a morphism `w : A ⟶ B` of complexes and representing isomorphisms `eA`, `eB`,
the class of the restriction of `w` is the restriction of the morphism that `w` represents. -/
theorem restrictModelIso_hom_naturality
    [PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    [PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (w : A ⟶ B)
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (eA : DerivedCategory.Q.obj A ≅ L) (eB : DerivedCategory.Q.obj B ≅ L') :
    DerivedCategory.Q.map (restrictComplexMap X U w) ≫ (restrictModelIso X U eB).hom =
      (restrictModelIso X U eA).hom ≫
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.map
          (eA.inv ≫ DerivedCategory.Q.map w ≫ eB.hom) := by
  have key : ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategoryFactors.app A).inv ≫
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.map
          (DerivedCategory.Q.map w) =
      DerivedCategory.Q.map (restrictComplexMap X U w) ≫
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategoryFactors.app B).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategoryFactors_hom_naturality w
  simp only [restrictModelIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    ← Functor.map_comp, Iso.hom_inv_id_assoc]
  rw [Functor.map_comp]
  conv_rhs => rw [← Category.assoc, key]
  rw [Category.assoc]

/-- The restriction to the slice over `U` of a morphism of complexes whose class is invertible
again has invertible class. -/
theorem isIso_Q_map_restrictComplexMap
    [PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    [PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (w : A ⟶ B)
    (hw : IsIso (DerivedCategory.Q.map w)) :
    IsIso (DerivedCategory.Q.map (restrictComplexMap X U w)) := by
  have h := restrictModelIso_hom_naturality X U w (Iso.refl (DerivedCategory.Q.obj A))
    (Iso.refl (DerivedCategory.Q.obj B))
  have : IsIso (DerivedCategory.Q.map (restrictComplexMap X U w) ≫
      (restrictModelIso X U (Iso.refl (DerivedCategory.Q.obj B))).hom) := by
    rw [h]
    have := hw
    have : IsIso (Iso.inv (Iso.refl (DerivedCategory.Q.obj A)) ≫ DerivedCategory.Q.map w ≫
        Iso.hom (Iso.refl (DerivedCategory.Q.obj B))) := by
      simpa using hw
    infer_instance
  exact IsIso.of_isIso_comp_right _ (restrictModelIso X U (Iso.refl (DerivedCategory.Q.obj B))).hom


/-! ### Tag 08JA over an object does not depend on the chosen models -/

section ModelIndependence

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)] in
/-- Two morphisms of `D(O)` applied in succession to a degree-zero class of derived sections
over `U` act as their composite. -/
theorem homologySectionsOverObject_map_comp_apply
    {Z Z' Z'' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : Z ⟶ Z') (b : Z' ⟶ Z'')
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj Z) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map b)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map a) x) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map (a ≫ b)) x := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  rfl

omit [PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)] in
/-- Tag 08JA over `U` at a K-flat source is Tag 08JA over `U` at a K-injective internal Hom
complex: K-flatness enters only through Tag 0A96. -/
theorem derivedSheafHomSectionsEquivOfKFlat_eq
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [I.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective] :
    derivedSheafHomSectionsEquivOfKFlat X U A I hA =
      derivedSheafHomSectionsEquivOfKInjectiveHom X U A I := rfl

/-- `AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv` with the identification at the
models written as the one for a K-injective internal Hom complex. -/
theorem derivedSheafHomSectionsEquiv_apply_of_isKInjective
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [((sheafHomComplex X (kFlatModel X L) (kInjectiveModel X M)).obj).IsKInjective]
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomSectionsEquiv X U L M ξ =
      ((restrictModelIso X U (kFlatModelIso X L)).inv ≫
          derivedSheafHomSectionsEquivOfKInjectiveHom X U (kFlatModel X L) (kInjectiveModel X M)
            ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
              ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
                (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
                  (kInjectiveModelIso X M)).hom) ξ)) ≫
        (restrictModelIso X U (kInjectiveModelIso X M)).hom :=
  Linear.homCongr_apply ℤ (restrictModelIso X U (kFlatModelIso X L))
    (restrictModelIso X U (kInjectiveModelIso X M))
    (derivedSheafHomSectionsEquivOfKInjectiveHom X U (kFlatModel X L) (kInjectiveModel X M)
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
          (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
            (kInjectiveModelIso X M)).hom) ξ))

omit [PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)] in
/-- `AlgebraicGeometry.RingedSite.modelIso_route_eq_of_refinement` read on a degree-zero class
of derived sections over `U`. -/
theorem transport_arg_eq_sections
    {L L' M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : L' ⟶ L) (ψ : M ⟶ M')
    {R : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (u : R ⟶ kFlatModel X L') (v : R ⟶ kFlatModel X L)
    (m : kInjectiveModel X M ⟶ kInjectiveModel X M')
    (hm : DerivedCategory.Q.map m =
      (kInjectiveModelIso X M).hom ≫ ψ ≫ (kInjectiveModelIso X M').inv)
    (huv : DerivedCategory.Q.map u ≫
      ((kFlatModelIso X L').hom ≫ φ ≫ (kFlatModelIso X L).inv) = DerivedCategory.Q.map v)
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map v).op).app
                (DerivedCategory.Q.obj (kInjectiveModel X M)) ≫
              ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj R))).map
                (DerivedCategory.Q.map m)))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
              (kInjectiveModelIso X M)).hom) ξ) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map u).op).app
                (DerivedCategory.Q.obj (kInjectiveModel X M')) ≫
              ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj R))).map
                (DerivedCategory.Q.map (𝟙 (kInjectiveModel X M')))))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
              (derivedSheafHomObjectsModelIso X (kFlatModelIso X L')
                (kInjectiveModelIso X M')).hom)
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
              (((derivedSheafHomBifunctor X).map φ.op).app M ≫
                ((derivedSheafHomBifunctor X).obj (op L')).map ψ)) ξ)) := by
  rw [homologySectionsOverObject_map_comp_apply, homologySectionsOverObject_map_comp_apply,
    homologySectionsOverObject_map_comp_apply]
  exact congrArg
    (fun f => (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map f) ξ)
    (modelIso_route_eq_of_refinement X φ ψ u v m hm huv)

end ModelIndependence


end AlgebraicGeometry.RingedSite

end
