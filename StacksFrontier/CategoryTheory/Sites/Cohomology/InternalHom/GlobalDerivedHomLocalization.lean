module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplexGlobalNaturality

/-!
# The canonical map into the global derived hom, read on cohomology

Let `(C, O)` be a ringed site and let `F`, `G` be complexes of `O`-modules. The Hom complex
`Hom^•(F, G)` maps canonically to the global derived hom `RHom_O(F, G)` of Tag 0B6E; that map is
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom`, the composite of the global
description of the internal Hom complex (Tag 0A8Z), the unit of derived global sections and the
comparison with the derived internal Hom. This file shows that on degree-zero cohomology this
map is the localization functor `K(O) ⥤ D(O)` on morphism groups.

The statement is **at a representative pair**: the target `G` is K-injective and the internal
Hom complex `SheafHom(F, G)` is K-injective, which for a K-flat `F` holds by Tag 0A96. Under
these hypotheses both legs of the canonical map are invertible and the degree-zero cohomology of
the target is a morphism group of `D(O)`
(`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKInjectiveHom`).

## Main results

* `AlgebraicGeometry.RingedSite.sheafHomComplexUnit_eq_derivedSheafHomComparison_inv` and
  `AlgebraicGeometry.RingedSite.globalSectionsDerivedUnit_eq_globalSectionsKInjectiveIso`: on a
  K-injective target, and on a K-injective complex, the two comparisons out of which the
  canonical map is built are the inverses of the two isomorphisms out of which the degree-zero
  reading of the global derived hom is built.
* `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_comp`: consequently, at such a pair
  the canonical map composed with those two isomorphisms is the class of a *morphism of
  complexes*, namely the inverse of the global description of Tag 0A8Z.
* `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_zero`: **the degree-zero
  reading.** At a K-injective `G` with `SheafHom(F, G)` K-injective, the degree-zero cohomology
  of the canonical map is the localization functor on morphism groups: a degree-zero class of
  `Hom^•(F, G)` is a morphism `F ⟶ G` of the homotopy category by Tag 09LC, and its image in
  `Hom_{D(O)}(F, G)` under the degree-zero reading of `RHom_O(F, G)` is the image of that
  morphism under `K(O) ⥤ D(O)`.
* `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_zero_of_isKFlat`: the same
  statement with the K-injectivity of `SheafHom(F, G)` discharged by Tag 0A96 from the
  K-flatness of `F`, read at the identification
  `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat`.
* `AlgebraicGeometry.RingedSite.exists_Q_map_eq_comp_kInjectiveModelIso`: **every morphism of
  `D(O)` out of the class of a complex factors through the chosen K-injective model of its
  target, by the class of a morphism of complexes.** Its consequences for the chosen models are
  `AlgebraicGeometry.RingedSite.exists_Q_map_eq_kInjectiveModelIso_inv` and
  `AlgebraicGeometry.RingedSite.kFlatModelIso_hom_comp`.

## References

* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.ShortComplex CategoryTheory.Limits AlgebraicGeometry Opposite
open CochainComplex.HomComplex
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe v u

/-! ### The universe-lift layer -/

/-- The comparison isomorphism between the homology of a short complex and the homology of its
chosen left homology datum is the identity. -/
theorem homologyData_left_homologyIso {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (S : ShortComplex C) [S.HasHomology] :
    S.homologyData.left.homologyIso = Iso.refl _ := by
  ext
  dsimp only [LeftHomologyData.homologyIso, ShortComplex.leftHomologyIso, Iso.trans_hom,
    Iso.symm_hom, Iso.refl_hom]
  exact Iso.inv_hom_id _

/-- The degreewise universe lift of a complex of abelian groups, compared with the complex
itself, read on the short complex computing degree-`n` homology. This is
`AlgebraicGeometry.RingedSite.uliftComplexSelfIso` with its source written as the *image* of the
short complex under the universe lift rather than as the short complex of the lifted complex. -/
def uliftScHom (D : CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ) :
    (D.sc n).map AddCommGrpCat.uliftFunctor.{u, u} ⟶ D.sc n :=
  (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n).map
    (uliftComplexSelfIso D).hom

/-- **The universe lift is compatible with the chosen left homology datum**: `ULift.down` on
cycles and on homology is a left homology map datum for
`AlgebraicGeometry.RingedSite.uliftScHom`. -/
def uliftLeftHomologyMapData (D : CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ) :
    LeftHomologyMapData (uliftScHom D n)
      ((D.sc n).homologyData.left.map AddCommGrpCat.uliftFunctor.{u, u})
      ((D.sc n).homologyData.left) where
  φK := AddCommGrpCat.ofHom (AddEquiv.ulift (α := (D.sc n).homologyData.left.K)).toAddMonoidHom
  φH := AddCommGrpCat.ofHom (AddEquiv.ulift (α := (D.sc n).homologyData.left.H)).toAddMonoidHom
  commi := by
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro x; rfl
  commf' := by
    rw [LeftHomologyData.map_f']
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro x; rfl
  commπ := by
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro x; rfl

/-- **The homology of the comparison of a lifted complex with itself is the comparison on
homology.** The degree-`n` homology of `AlgebraicGeometry.RingedSite.uliftComplexSelfIso` is
`AlgebraicGeometry.RingedSite.uliftHomologyIso` followed by `ULift.down`. -/
theorem homologyMap_uliftComplexSelfIso_hom (D : CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ) :
    HomologicalComplex.homologyMap (uliftComplexSelfIso D).hom n =
      (uliftHomologyIso D n).hom ≫
        AddCommGrpCat.ofHom (AddEquiv.ulift (α := D.homology n)).toAddMonoidHom := by
  have h := (uliftLeftHomologyMapData D n).homologyMap_eq
  rwa [homologyData_left_homologyIso, Iso.refl_inv] at h

/-- **The two readings of the universe lift cancel.** Lifting a degree-`n` homology class along
`AlgebraicGeometry.RingedSite.uliftComplexSelfIso` and bringing it back down along
`AlgebraicGeometry.RingedSite.uliftHomologyIso` returns the class. -/
theorem uliftHomologyIso_homologyMap_uliftComplexSelfIso_inv
    (D : CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ) (ζ : D.homology n) :
    AddEquiv.ulift ((uliftHomologyIso D n).hom
      (HomologicalComplex.homologyMap (uliftComplexSelfIso D).inv n ζ)) = ζ := by
  have key : HomologicalComplex.homologyMap (uliftComplexSelfIso D).inv n ≫
      HomologicalComplex.homologyMap (uliftComplexSelfIso D).hom n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, Iso.inv_hom_id, HomologicalComplex.homologyMap_id]
  rw [homologyMap_uliftComplexSelfIso_hom] at key
  exact ConcreteCategory.congr_hom key ζ

variable (X : RingedSite.{u, u, u})

attribute [local instance] HasDerivedCategory.standard

/-- **The universe lift carried by Tag 0A8Z cancels against its inverse, on homology.** The
morphism of complexes which the canonical map
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` begins with, followed on homology by
the global description of the internal Hom complex and the universe comparison, is the
identity. -/
theorem globalSectionsIso_homologyMap_cancel
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ)
    (ζ : (F.HomComplex G).homology n) :
    AddEquiv.ulift ((uliftHomologyIso (F.HomComplex G) n).hom
      (HomologicalComplex.homologyMap (sheafHomComplex X F G).globalSectionsIso.hom n
        (HomologicalComplex.homologyMap ((uliftComplexSelfIso (F.HomComplex G)).inv ≫
          (sheafHomComplex X F G).globalSectionsIso.inv) n ζ))) = ζ := by
  simp only [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [ConcreteCategory.comp_apply]
  exact uliftHomologyIso_homologyMap_uliftComplexSelfIso_inv _ _ _

/-! ### The two comparisons of the canonical map are invertible at a representative pair -/

/-- **On a K-injective complex the comparison with derived global sections is the isomorphism of
Tag 07A5.** -/
theorem globalSectionsDerivedUnit_eq_globalSectionsKInjectiveIso
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [H.IsKInjective] :
    globalSectionsDerivedUnit X H = (globalSectionsKInjectiveIso X H).hom := rfl

/-- **On a K-injective target the comparison with the derived internal Hom is the inverse of the
comparison of Tag 0A97.** `AlgebraicGeometry.RingedSite.sheafHomComplexUnit` is the inverse of
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison`. -/
theorem sheafHomComplexUnit_eq_derivedSheafHomComparison_inv
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [G.IsKInjective] :
    sheafHomComplexUnit X F G = (derivedSheafHomComparison X F G).inv := rfl

/-- The canonical map `Hom^•(F, G) ⟶ RHom_O(F, G)` at a K-injective target, written with the two
comparisons of
`AlgebraicGeometry.RingedSite.globalSectionsDerivedUnit_eq_globalSectionsKInjectiveIso` and
`AlgebraicGeometry.RingedSite.sheafHomComplexUnit_eq_derivedSheafHomComparison_inv` in place of
the two units. -/
theorem homComplexToGlobalDerivedHom_eq
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [G.IsKInjective]
    [((sheafHomComplex X F G).obj).IsKInjective] :
    homComplexToGlobalDerivedHom X F G =
      DerivedCategory.Q.map ((uliftComplexSelfIso (F.HomComplex G)).inv ≫
          (sheafHomComplex X F G).globalSectionsIso.inv) ≫
        (globalSectionsKInjectiveIso X ((sheafHomComplex X F G).obj)).hom ≫
          (derivedModuleGlobalSections X).map (derivedSheafHomComparison X F G).inv := rfl

/-- **At a representative pair the canonical map is the class of a morphism of complexes.**
Composing `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` with the two isomorphisms
out of which the degree-zero reading of the global derived hom is built leaves only the inverse
of the global description of Tag 0A8Z, a morphism of complexes of abelian groups. -/
theorem homComplexToGlobalDerivedHom_comp
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [G.IsKInjective]
    [((sheafHomComplex X F G).obj).IsKInjective] :
    homComplexToGlobalDerivedHom X F G ≫
        ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X F G).hom ≫
          (globalSectionsKInjectiveIso X ((sheafHomComplex X F G).obj)).inv) =
      DerivedCategory.Q.map ((uliftComplexSelfIso (F.HomComplex G)).inv ≫
        (sheafHomComplex X F G).globalSectionsIso.inv) := by
  refine (congrArg (fun f => f ≫
      ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X F G).hom ≫
        (globalSectionsKInjectiveIso X ((sheafHomComplex X F G).obj)).inv))
    (homComplexToGlobalDerivedHom_eq X F G)).trans ?_
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.hom_inv_id, Category.comp_id]

/-! ### Factoring a morphism of `D(O)` through the chosen K-injective model -/

/-- **Every morphism of `D(O)` out of the class of a complex factors through the chosen
K-injective model of its target, by the class of a morphism of complexes.** For a complex `A`,
an object `L` of `D(O)` and a morphism `φ : Q A ⟶ L` there is a morphism of complexes
`h : A ⟶ kInjectiveModel L` with `φ = Q h ≫ kInjectiveModelIso L`. -/
theorem exists_Q_map_eq_comp_kInjectiveModelIso
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (φ : DerivedCategory.Q.obj A ⟶ L) :
    ∃ h : A ⟶ kInjectiveModel X L,
      DerivedCategory.Q.map h ≫ (kInjectiveModelIso X L).hom = φ := by
  obtain ⟨h, hh⟩ := exists_Q_map_eq_of_isKInjective X (φ ≫ (kInjectiveModelIso X L).inv)
  exact ⟨h, by rw [hh, Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩

/-- **The chosen K-injective model of the class of a complex is compared with it by the inverse
of the class of a morphism of complexes.** There is a morphism of complexes
`h : A ⟶ kInjectiveModel (Q A)` whose class is invertible and is the inverse of
`AlgebraicGeometry.RingedSite.kInjectiveModelIso`. -/
theorem exists_Q_map_eq_kInjectiveModelIso_inv
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ∃ h : A ⟶ kInjectiveModel X (DerivedCategory.Q.obj A),
      IsIso (DerivedCategory.Q.map h) ∧
        DerivedCategory.Q.map h = (kInjectiveModelIso X (DerivedCategory.Q.obj A)).inv := by
  obtain ⟨h, hh⟩ := exists_Q_map_eq_of_isKInjective X
    (kInjectiveModelIso X (DerivedCategory.Q.obj A)).inv
  exact ⟨h, by rw [hh]; infer_instance, hh⟩

/-! ### The degree-zero reading of the canonical map -/

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Tag 08JA at a representative pair, unfolded: the degree-zero reading of the global derived
hom is the two comparisons followed by Tag 0A94. -/
theorem derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_apply
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective]
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X A I ξ =
      sheafHomGlobalHomologyEquivDerivedCategoryHom X A I
        (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).app
            (globalSectionsComplex X (sheafHomComplex X A I).obj)).hom
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
              (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv) ξ)) := rfl

/-- **The canonical map `Hom^•(F, G) ⟶ RHom_O(F, G)` is the localization functor on degree-zero
cohomology.** Let `G` be K-injective and let the internal Hom complex `SheafHom(F, G)` be
K-injective — which for a K-flat `F` is Tag 0A96. The degree-zero cohomology of
`RHom_O(F, G)` is `Hom_{D(O)}(F, G)` by Tag 08JA
(`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKInjectiveHom`), the
degree-zero cohomology of `Hom^•(F, G)` is `Hom_{K(O)}(F, G)` by Tag 09LC, and the map between
them induced by `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` is the localization
functor `K(O) ⥤ D(O)`, read on a K-injective target by
`AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv`. -/
theorem homComplexToGlobalDerivedHom_homology_zero
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [G.IsKInjective]
    [((sheafHomComplex X F G).obj).IsKInjective]
    (η : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      (DerivedCategory.Q.obj (F.HomComplex G)) : Type u)) :
    derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X F G
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          (homComplexToGlobalDerivedHom X F G) η) =
      homotopyHomDerivedCategoryEquiv F G
        ((𝟙 _ ≫ CohomologyClass.homAddEquiv (homologyAddEquiv F G 0
              (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).app
                (F.HomComplex G)).hom η))) ≫
          (HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ)).map
            ((shiftFunctorZero
              (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
              ℤ).app
              G).hom) := by
  refine (derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_apply X F G _).trans ?_
  have hA : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X F G).hom ≫
          (globalSectionsKInjectiveIso X ((sheafHomComplex X F G).obj)).inv)
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        (homComplexToGlobalDerivedHom X F G) η) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        (DerivedCategory.Q.map ((uliftComplexSelfIso (F.HomComplex G)).inv ≫
          (sheafHomComplex X F G).globalSectionsIso.inv)) η := by
    have h := congrArg (fun f => (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map f)
      (homComplexToGlobalDerivedHom_comp X F G)
    rw [CategoryTheory.Functor.map_comp] at h
    exact ConcreteCategory.congr_hom h η
  rw [hA]
  have hB : ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).app
        (globalSectionsComplex X (sheafHomComplex X F G).obj)).hom
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        (DerivedCategory.Q.map ((uliftComplexSelfIso (F.HomComplex G)).inv ≫
          (sheafHomComplex X F G).globalSectionsIso.inv)) η) =
      HomologicalComplex.homologyMap ((uliftComplexSelfIso (F.HomComplex G)).inv ≫
          (sheafHomComplex X F G).globalSectionsIso.inv) 0
        (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).app
          (F.HomComplex G)).hom η) :=
    ConcreteCategory.congr_hom
      ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.naturality
        ((uliftComplexSelfIso (F.HomComplex G)).inv ≫
          (sheafHomComplex X F G).globalSectionsIso.inv)) η
  rw [hB, sheafHomGlobalHomologyEquivDerivedCategoryHom_apply,
    sheafHomGlobalHomotopyCategoryHom_eq]
  congr 3
  exact congrArg (fun z => CohomologyClass.homAddEquiv (homologyAddEquiv F G 0 z))
    (globalSectionsIso_homologyMap_cancel X F G 0 _)

/-! ### The chosen K-flat model -/

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]

/-- **The chosen K-flat model of the class of a complex is compared with it by the class of a
morphism of complexes composed with the inverse of such a class.** There is a morphism of
complexes `h : A ⟶ kInjectiveModel (Q A)` with invertible class such that
`AlgebraicGeometry.RingedSite.kFlatModelIso` followed by `Q h` is the class of the augmentation
`AlgebraicGeometry.RingedSite.kFlatModelMap` of the K-flat model into the K-injective one. -/
theorem kFlatModelIso_hom_comp
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ∃ h : A ⟶ kInjectiveModel X (DerivedCategory.Q.obj A),
      IsIso (DerivedCategory.Q.map h) ∧
        (kFlatModelIso X (DerivedCategory.Q.obj A)).hom ≫ DerivedCategory.Q.map h =
          DerivedCategory.Q.map (kFlatModelMap X (DerivedCategory.Q.obj A)) := by
  obtain ⟨h, hiso, hh⟩ := exists_Q_map_eq_kInjectiveModelIso_inv X A
  refine ⟨h, hiso, ?_⟩
  rw [hh, kFlatModelIso]
  simp only [Iso.trans_hom, asIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
  HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (ComplexShape.up ℤ)]

/-- **The canonical map `Hom^•(F, G) ⟶ RHom_O(F, G)` is the localization functor on degree-zero
cohomology, at a K-flat source and a K-injective target.** This is
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_zero`, where the
K-injectivity of `SheafHom(F, G)` holds by Tag 0A96, read at the identification
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat`. -/
theorem homComplexToGlobalDerivedHom_homology_zero_of_isKFlat
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hF : Stacks.SheafOfModules.IsKFlat X.O F) [G.IsKInjective]
    (η : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      (DerivedCategory.Q.obj (F.HomComplex G)) : Type u)) :
    derivedSheafHomGlobalSectionsEquivOfKFlat X F G hF
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          (homComplexToGlobalDerivedHom X F G) η) =
      homotopyHomDerivedCategoryEquiv F G
        ((𝟙 _ ≫ CohomologyClass.homAddEquiv (homologyAddEquiv F G 0
              (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).app
                (F.HomComplex G)).hom η))) ≫
          (HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ)).map
            ((shiftFunctorZero
              (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
              ℤ).app
              G).hom) :=
  have := isKInjective_sheafHomComplex_of_isKFlat X F G hF
  homComplexToGlobalDerivedHom_homology_zero X F G η

end AlgebraicGeometry.RingedSite

end
