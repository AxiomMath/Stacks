module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsOfTheHomComplexRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsOverAnObjectModelIndependence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplexGlobalValue

/-!
# Tag 08JA globally and over an object, compared under restriction

Let `(C, O)` be a ringed site, `U` an object of `C` and `L`, `M` objects of `D(O)`. **Stacks
08JA** identifies

`H⁰(C, RSheafHom(L, M)) = Hom_{D(O)}(L, M)` and
`H⁰(U, RSheafHom(L, M)) = Hom_{D(O|_U)}(L|_U, M|_U)`.

This file proves that the two identifications are **compatible under restriction**: the square

```
H⁰(C, RSheafHom(L, M)) ----> Hom_{D(O)}(L, M)
        |                           |
H⁰(U, RSheafHom(L, M)) ----> Hom_{D(O|_U)}(L|_U, M|_U)
```

commutes, where the left vertical map is the restriction
`Stacks.Cohomology.ModuleSections.derivedSectionsRestriction` of derived global sections to
derived sections over `U` and the right vertical map is restriction of morphisms to the slice
over `U`.

## Main results

* `AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv_mapHomotopyCategory`: morphisms
  into a K-injective complex are the same in the homotopy and the derived category, compatibly
  with restriction to a slice.
* `AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom_restriction`:
  **Stacks 0A94 globally is compatible with Stacks 0A94 over an object under restriction.**
* `AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquivOfKInjectiveHom_restriction`: the
  same for Stacks 08JA at a representative pair.
* `AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv_restriction`: **Stacks 08JA
  globally is compatible with Stacks 08JA over an object of the site under restriction of
  hypercohomology.**

## Implementation notes

The complex-level input is
`AlgebraicGeometry.RingedSite.sheafHomSectionHomotopyCategoryHom_globalSectionsComplexRestriction`
of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsOfTheHomComplexRestriction`,
which compares Stacks 0A8Z with Stacks 0A8Y in the homotopy category. Three steps carry it to
Stacks 08JA:

1. from the homotopy to the derived category. Every morphism of the homotopy category is the
   class of a morphism of complexes, and for the class of a morphism of complexes the comparison
   is `AlgebraicGeometry.RingedSite.restrictModelIso_hom_naturality` at the identity representing
   isomorphisms. This is Stacks 0A94.
2. from Stacks 0A94 to Stacks 08JA at a representative pair, which is the naturality of the two
   comparisons the degree-zero reading is built from: the one of Stacks 0A97 and the one of
   Stacks 07A5, the latter being
   `Stacks.Cohomology.ModuleSections.derivedSectionsRestriction_app_globalSectionsKInjectiveIso`.
3. from a representative pair to arbitrary objects, by transporting along the chosen K-flat and
   K-injective models. The transport is the naturality of the restriction of derived sections
   together with the algebra of `AlgebraicGeometry.RingedSite.restrictModelIso`,
   `restrictModelIso_conj`.

*Why the rewrites are term-mode.* Two of the rewrites this proof wants have a motive spanning
both the source and the target pair of objects, and `rw` overruns the heartbeat budget on them;
they are written with `congrArg` and `Eq.trans` instead, as in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsOverAnObjectNaturality`.

*What this does not say.* The restriction comparison of the **currying** isomorphism of
Stacks 08J9 is not needed and is not proved here: `Stacks.SheafOfModules.derivedCurryIso` is an
isomorphism in `D(O_X)`, so applying `H⁰(U, -)` to it gives the comparison over `U` directly.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe v₁ u₁ u

attribute [local instance] HasDerivedCategory.standard

/-! ### Morphisms into a K-injective complex, under restriction -/

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]

/-- The class in `D(O|_U)` of the restriction of a morphism of complexes is the restriction of
the class of that morphism, read through
`AlgebraicGeometry.RingedSite.restrictModelIso` at the identity. -/
theorem Q_map_restrictComplexMap_eq
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (w : A ⟶ B) :
    DerivedCategory.Q.map (restrictComplexMap X U w) =
      (restrictModelIso X U (Iso.refl (DerivedCategory.Q.obj A))).hom ≫
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapDerivedCategory.map
            (DerivedCategory.Q.map w) ≫
          (restrictModelIso X U (Iso.refl (DerivedCategory.Q.obj B))).inv := by
  have h := restrictModelIso_hom_naturality X U w (Iso.refl (DerivedCategory.Q.obj A))
    (Iso.refl (DerivedCategory.Q.obj B))
  simp only [Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id] at h
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact h

/-- **The identification of homotopy-category with derived-category morphisms into a K-injective
complex commutes with restriction to a slice.**  Every morphism of the homotopy category is the
class of a morphism of complexes, so this is
`AlgebraicGeometry.RingedSite.Q_map_restrictComplexMap_eq`. -/
theorem homotopyHomDerivedCategoryEquiv_mapHomotopyCategory
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    (θ : (HomotopyCategory.quotient
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj L ⟶
      (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj I) :
    homotopyHomDerivedCategoryEquiv (restrictComplex X L U) (restrictComplex X I U)
        (((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapHomotopyCategory
          (ComplexShape.up ℤ)).map θ) =
      (restrictModelIso X U (Iso.refl (DerivedCategory.Q.obj L))).hom ≫
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapDerivedCategory.map
            (homotopyHomDerivedCategoryEquiv L I θ) ≫
          (restrictModelIso X U (Iso.refl (DerivedCategory.Q.obj I))).inv := by
  obtain ⟨w, rfl⟩ := (HomotopyCategory.quotient
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ComplexShape.up ℤ)).map_surjective θ
  refine Eq.trans (congrArg (fun t ↦ homotopyHomDerivedCategoryEquiv
        (restrictComplex X L U) (restrictComplex X I U) t)
      (CategoryTheory.Functor.mapHomotopyCategory_map
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) w)) ?_
  rw [homotopyHomDerivedCategoryEquiv_quotient_map, homotopyHomDerivedCategoryEquiv_quotient_map]
  exact Q_map_restrictComplexMap_eq X U w

/-- **Tag 0A94 globally is compatible with Tag 0A94 over an object under restriction.** For `I`
K-injective, the morphism `L|_U ⟶ I|_U` of `D(O|_U)` attached to the restriction to `U` of a
degree-zero class of the global section complex of `SheafHom^•(L, I)` is the restriction of the
morphism `L ⟶ I` of `D(O)` attached to that class. -/
theorem sheafHomSectionHomologyEquivDerivedCategoryHom_restriction
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    (η : (globalSectionsComplex X (sheafHomComplex X L I).obj).homology 0) :
    sheafHomSectionHomologyEquivDerivedCategoryHom X L I U
        (HomologicalComplex.homologyMap
          (globalSectionsComplexRestriction X U (sheafHomComplex X L I).obj) 0 η) =
      (restrictModelIso X U (Iso.refl (DerivedCategory.Q.obj L))).hom ≫
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapDerivedCategory.map
            (sheafHomGlobalHomologyEquivDerivedCategoryHom X L I η) ≫
          (restrictModelIso X U (Iso.refl (DerivedCategory.Q.obj I))).inv := by
  rw [sheafHomSectionHomologyEquivDerivedCategoryHom_apply,
    sheafHomSectionHomotopyCategoryHom_globalSectionsComplexRestriction,
    sheafHomGlobalHomologyEquivDerivedCategoryHom_apply]
  exact homotopyHomDerivedCategoryEquiv_mapHomotopyCategory X U L I _

/-- **Conjugating by the comparisons with the identity representing isomorphisms.** A morphism
of `D(O)` between the classes of two complexes, restricted to the slice over `U` and read
through the comparisons at the identity, is conjugate to the restriction of its transport along
two representing isomorphisms. -/
private theorem restrictModelIso_conj
    {L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eA : DerivedCategory.Q.obj A ≅ L) (eI : DerivedCategory.Q.obj I ≅ M)
    (g : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj I) :
    ((restrictModelIso X U eA).inv ≫
          ((restrictModelIso X U (Iso.refl (DerivedCategory.Q.obj A))).hom ≫
            (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                U).mapDerivedCategory.map g ≫
              (restrictModelIso X U (Iso.refl (DerivedCategory.Q.obj I))).inv)) ≫
        (restrictModelIso X U eI).hom =
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.map
        ((eA.inv ≫ g) ≫ eI.hom) := by
  simp [restrictModelIso]

/-! ### Tag 08JA at a representative pair, under restriction -/

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

omit [PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- The two comparisons out of which the degree-zero reading of the derived hom is built at a
representative pair are carried into each other by the restriction of derived sections. -/
private theorem derivedSectionsRestriction_comparison
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective] :
    (derivedSectionsRestriction X U).app
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
            (DerivedCategory.Q.obj I)) ≫
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (derivedSheafHomComparison X A I).hom ≫
          (sectionsKInjectiveIso X U ((sheafHomComplex X A I).obj)).inv) =
      ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
          (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv) ≫
        DerivedCategory.Q.map
          (globalSectionsComplexRestriction X U (sheafHomComplex X A I).obj) := by
  have hnat := (derivedSectionsRestriction X U).naturality (derivedSheafHomComparison X A I).hom
  have hinv : (derivedSectionsRestriction X U).app
          (DerivedCategory.Q.obj (sheafHomComplex X A I).obj) ≫
        (sectionsKInjectiveIso X U ((sheafHomComplex X A I).obj)).inv =
      (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv ≫
        DerivedCategory.Q.map
          (globalSectionsComplexRestriction X U (sheafHomComplex X A I).obj) := by
    rw [Iso.eq_inv_comp, ← Category.assoc,
      derivedSectionsRestriction_app_globalSectionsKInjectiveIso X U
        ((sheafHomComplex X A I).obj), Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, ← hnat, Category.assoc, hinv, Category.assoc]

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **Tag 08JA at a representative pair, globally and over `U`, compared under restriction.**
For `I` K-injective with `SheafHom^•(A, I)` K-injective, the identification of the degree-zero
hypercohomology over `U` of `RSheafHom(Q A, Q I)` with `Hom_{D(O|_U)}(A|_U, I|_U)` carries the
restriction of a global class to the restriction of the morphism that class names globally. -/
theorem derivedSheafHomSectionsEquivOfKInjectiveHom_restriction
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective]
    (ζ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomSectionsEquivOfKInjectiveHom X U A I
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedSectionsRestriction X U).app
            (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
              (DerivedCategory.Q.obj I))) ζ) =
      (restrictModelIso X U (Iso.refl (DerivedCategory.Q.obj A))).hom ≫
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapDerivedCategory.map
            (derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X A I ζ) ≫
          (restrictModelIso X U (Iso.refl (DerivedCategory.Q.obj I))).inv := by
  rw [derivedSheafHomSectionsEquivOfKInjectiveHom_apply_of_isKInjective,
    derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_apply]
  have hmap : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (derivedSheafHomComparison X A I).hom ≫
          (sectionsKInjectiveIso X U ((sheafHomComplex X A I).obj)).inv)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedSectionsRestriction X U).app
            (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
              (DerivedCategory.Q.obj I))) ζ) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        (DerivedCategory.Q.map
          (globalSectionsComplexRestriction X U (sheafHomComplex X A I).obj))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
            (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv) ζ) := by
    simpa only [CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom
        (congrArg (fun f ↦ (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map f)
          (derivedSectionsRestriction_comparison X U A I)) ζ
  rw [hmap]
  have hFF := ConcreteCategory.congr_hom
    ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.naturality
      (globalSectionsComplexRestriction X U (sheafHomComplex X A I).obj))
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
        (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv) ζ)
  simp only [ConcreteCategory.comp_apply, Functor.comp_map, ← Iso.app_hom] at hFF
  rw [hFF]
  exact sheafHomSectionHomologyEquivDerivedCategoryHom_restriction X U A I _

/-! ### Tag 08JA globally and over an object, compared under restriction -/

/-- **Tag 08JA globally is compatible with Tag 08JA over an object of the site under restriction
of hypercohomology.** For arbitrary objects `L`, `M` of `D(O)` the square

```
H⁰(C, RSheafHom(L, M)) ----> Hom_{D(O)}(L, M)
        |                           |
H⁰(U, RSheafHom(L, M)) ----> Hom_{D(O|_U)}(L|_U, M|_U)
```

commutes: the left vertical map is the restriction
`Stacks.Cohomology.ModuleSections.derivedSectionsRestriction` of derived global sections to
derived sections over `U`, the right vertical map is restriction of morphisms to the slice over
`U`, and the two horizontal maps are the two assertions of Tag 08JA. -/
theorem derivedSheafHomSectionsEquiv_restriction
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomSectionsEquiv X U L M
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedSectionsRestriction X U).app
            (((derivedSheafHomBifunctor X).obj (op L)).obj M)) ξ) =
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.map
        (derivedSheafHomGlobalSectionsEquiv X L M ξ) := by
  have : ((sheafHomComplex X (kFlatModel X L) (kInjectiveModel X M)).obj).IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X _ _ (isKFlat_kFlatModel X L)
  have hT := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map f)
      ((derivedSectionsRestriction X U).naturality
        (derivedSheafHomObjectsModelIso X (kFlatModelIso X L) (kInjectiveModelIso X M)).hom)) ξ
  simp only [CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply] at hT
  have hstep := (congrArg (fun t ↦ derivedSheafHomSectionsEquivOfKInjectiveHom X U
      (kFlatModel X L) (kInjectiveModel X M) t) hT.symm).trans
    (derivedSheafHomSectionsEquivOfKInjectiveHom_restriction X U
      (kFlatModel X L) (kInjectiveModel X M)
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
            (kInjectiveModelIso X M)).hom) ξ))
  rw [derivedSheafHomSectionsEquiv_apply_of_isKInjective X U L M,
    derivedSheafHomGlobalSectionsEquiv_apply X L M,
    derivedSheafHomGlobalSectionsEquivOfKFlat_eq, hstep]
  exact restrictModelIso_conj X U (kFlatModelIso X L) (kInjectiveModelIso X M) _

end AlgebraicGeometry.RingedSite

end
