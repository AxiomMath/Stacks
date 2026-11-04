module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Naturality of the global half of Stacks 0A94

Let `(C, O)` be a ringed site, `L` a complex of `O`-modules and `I` a K-injective complex of
`O`-modules. **Stacks 0A94** identifies the degree-zero cohomology of the global sections of the
internal Hom complex `SheafHom(L, I)` with `Hom_{D(O)}(L, I)`; that identification is
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom`. This file proves it
is **natural in both variables** — contravariantly in `L`, covariantly in `I` — for the
functoriality `AlgebraicGeometry.RingedSite.homMap` of the internal Hom complex.

The local half of the same statement, over an object of the site, already has its naturality in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplex`. The global half
is proved here by the same three steps, with one extra layer: globally the sections of the
internal Hom complex are the ordinary Hom complex *lifted* to the universe of the local section
complexes, so a degreewise universe lift sits between the global description and the Hom complex,
and the naturality of the homology of a functor-image short complex has to be moved across it.

## Main results

* `AlgebraicGeometry.RingedSite.globalSectionsIso_homMap`: the global description of the internal
  Hom complex carries `homMap k m` to the lift of `homComplexConj k m`, as a square of morphisms
  of complexes. This is the global companion of
  `AlgebraicGeometry.RingedSite.sectionsIso_homMap`.
* `AlgebraicGeometry.RingedSite.sheafHomGlobalHomotopyCategoryHom_naturality`: the
  homotopy-category morphism `L ⟶ I` attached to a degree-zero class of the global section
  complex is natural in both variables.
* `AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality`:
  **Stacks 0A94, global sections, naturality.**

## Implementation notes

*Why this was absent.* The local naturality is proved from
`AlgebraicGeometry.RingedSite.sectionsIso_homMap_v`, the compatibility of the `sectionsIso` field
of `AlgebraicGeometry.RingedSite.SheafHomComplex` with `homMap`, which Stacks 0A90 (1) supplies.
The corresponding compatibility of the `globalSectionsIso` field is
`AlgebraicGeometry.RingedSite.globalSectionsIso_homMap_v`, which *is* available — it was added to
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplex` after the
"What this file does not contain" sections of that module and of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects` were
written, and those sections, which say the global compatibility has no starting point, are stale.
Nothing beyond it was needed.

*The universe-lift layer.* `AlgebraicGeometry.RingedSite.SheafHomComplex.globalSectionsIso`
identifies `Γ(C, SheafHom^•(L, M))` not with `Hom^•(L, M)` but with its degreewise lift along
`AddCommGrpCat.uliftFunctor`, because the global sections of a sheaf of modules on a site live in
a larger universe than the sections over an object. On homology that lift is crossed by
`CategoryTheory.ShortComplex.mapHomologyIso`, and
`AlgebraicGeometry.RingedSite.ulift_mapHomologyIso_naturality` is the one statement needed about
it: the homology of the lift of a morphism of complexes is the lift of the homology of that
morphism, which is `CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality` read elementwise.

*The universes are the diagonal ones.* `AlgebraicGeometry.RingedSite.{u, u, u}` with modules in
`SheafOfModules.{u}`, as in the whole Section 34 cluster; see the implementation notes of
`StacksDraft.Ch21.Sec34.DerivedInternalHomOnASite`. The lifting functor is then
`AddCommGrpCat.uliftFunctor.{u, u}`, and keeping the universes apart makes the statement of
`AlgebraicGeometry.RingedSite.globalSectionsIso_homMap` time out in elaboration without buying a
consumer anything: every consumer of the global derived hom is already diagonal.

## References

* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-! ### The universe-lift layer on homology -/

/-- **The homology of a degreewise universe lift is the lift of the homology.** This is
`CategoryTheory.ShortComplex.mapHomologyIso` for the short complex that computes the degree-`n`
homology, with its type written at the lifted complex rather than at the lifted short complex —
the two are the same by the definition of `HomologicalComplex.homology`, and writing it this way
is what lets the identification be rewritten under a motive. -/
def uliftHomologyIso (A : CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ) :
    ((AddCommGrpCat.uliftFunctor.{u, u}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        A).homology n ≅
      AddCommGrpCat.uliftFunctor.{u, u}.obj (A.homology n) :=
  (A.sc n).mapHomologyIso AddCommGrpCat.uliftFunctor.{u, u}

/-- **The homology of a degreewise universe lift is the lift of the homology**, read on elements
and naturally in the morphism: the identification
`AlgebraicGeometry.RingedSite.uliftHomologyIso` carries the homology of the lift of a morphism of
complexes to the homology of that morphism. This is
`CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality` with the universe lift stripped off
both sides. -/
theorem ulift_mapHomologyIso_naturality {A B : CochainComplex AddCommGrpCat.{u} ℤ} (φ : A ⟶ B)
    (n : ℤ)
    (η : ((AddCommGrpCat.uliftFunctor.{u, u}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      A).homology n) :
    AddEquiv.ulift ((uliftHomologyIso B n).hom
        (HomologicalComplex.homologyMap
          ((AddCommGrpCat.uliftFunctor.{u, u}.mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ) n η)) =
      HomologicalComplex.homologyMap φ n
        (AddEquiv.ulift ((uliftHomologyIso A n).hom η)) :=
  congrArg AddEquiv.ulift (ConcreteCategory.congr_hom
    (ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n).map φ)
      AddCommGrpCat.uliftFunctor.{u, u}) η)

/-! ### The global description of the internal Hom complex is natural -/

/-- **The global description of the internal Hom complex carries `homMap k m` to the lift of
`homComplexConj k m`**, as a square of morphisms of complexes of abelian groups. This is
`AlgebraicGeometry.RingedSite.globalSectionsIso_homMap_v`, which is Stacks 0A90 (1) globally,
read as such a square; it is the global companion of
`AlgebraicGeometry.RingedSite.sectionsIso_homMap`. -/
theorem globalSectionsIso_homMap
    {K K' M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K' ⟶ K) (m : M ⟶ M') :
    globalSectionsComplexMap X (homMap X k m) ≫
        (sheafHomComplex X K' M').globalSectionsIso.hom =
      (sheafHomComplex X K M).globalSectionsIso.hom ≫
        (AddCommGrpCat.uliftFunctor.{u, u}.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (homComplexConj k m) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ULift.ext
  refine Cochain.ext _ _ fun p q hpq => ?_
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply]
  rw [globalSectionsIso_homMap_v X k m n p q hpq s]
  exact (homComplexConj_v k m n
    ((AddCommGrpCat.Hom.hom ((sheafHomComplex X K M).globalSectionsIso.hom.f n)) s).down
    p q hpq).symm

/-! ### Stacks 0A8Z globally, on elements and naturally -/

/-- Stacks 0A8Z is the global description of the internal Hom complex read on homology, the
universe lift stripped off, and the identification of the cohomology of a Hom complex with
homotopy-category morphisms. -/
theorem sheafHomComplexHomologyEquivHomotopyCategory_apply
    (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ)
    (η : (globalSectionsComplex X (sheafHomComplex X L M).obj).homology n) :
    sheafHomComplexHomologyEquivHomotopyCategory X L M n η =
      CohomologyClass.homAddEquiv (homologyAddEquiv L M n
        (AddEquiv.ulift ((uliftHomologyIso (L.HomComplex M) n).hom
          (HomologicalComplex.homologyMap
            (sheafHomComplex X L M).globalSectionsIso.hom n η)))) := rfl

/-- The cohomology class of the global section complex attached to `homMap k m` is the class
attached to the original one, precomposed with `k` and postcomposed with `m`. -/
private theorem homologyAddEquiv_globalSectionsIso_homMap
    {L L' I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : L' ⟶ L) (m : I ⟶ I')
    (η : (globalSectionsComplex X (sheafHomComplex X L I).obj).homology 0) :
    homologyAddEquiv L' I' 0
        (AddEquiv.ulift ((uliftHomologyIso (L'.HomComplex I') 0).hom
          (HomologicalComplex.homologyMap (sheafHomComplex X L' I').globalSectionsIso.hom 0
            (HomologicalComplex.homologyMap
              (globalSectionsComplexMap X (homMap X k m)) 0 η)))) =
      cohomologyClassPrecomp k I' 0
        (cohomologyClassPostcomp L m 0
          (homologyAddEquiv L I 0
            (AddEquiv.ulift ((uliftHomologyIso (L.HomComplex I) 0).hom
              (HomologicalComplex.homologyMap
                (sheafHomComplex X L I).globalSectionsIso.hom 0 η))))) := by
  have hsq : HomologicalComplex.homologyMap (globalSectionsComplexMap X (homMap X k m)) 0 ≫
        HomologicalComplex.homologyMap (sheafHomComplex X L' I').globalSectionsIso.hom 0 =
      HomologicalComplex.homologyMap (sheafHomComplex X L I).globalSectionsIso.hom 0 ≫
        HomologicalComplex.homologyMap
          ((AddCommGrpCat.uliftFunctor.{u, u}.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (homComplexConj k m)) 0 := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      globalSectionsIso_homMap]
  have hel : HomologicalComplex.homologyMap (sheafHomComplex X L' I').globalSectionsIso.hom 0
        (HomologicalComplex.homologyMap (globalSectionsComplexMap X (homMap X k m)) 0 η) =
      HomologicalComplex.homologyMap
        ((AddCommGrpCat.uliftFunctor.{u, u}.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (homComplexConj k m)) 0
        (HomologicalComplex.homologyMap (sheafHomComplex X L I).globalSectionsIso.hom 0 η) := by
    simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom hsq η
  rw [hel, ulift_mapHomologyIso_naturality, homologyAddEquiv_conj]

/-! ### Naturality of Stacks 0A94 globally -/

/-- The morphism `L ⟶ I` in the homotopy category of `O`-modules attached to a degree-zero class
of the global section complex of the internal Hom complex: Stacks 0A8Z in degree `0`, with the
degree-zero shift of the target normalised away. -/
def sheafHomGlobalHomotopyCategoryHom
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (η : (globalSectionsComplex X (sheafHomComplex X L I).obj).homology 0) :
    (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)).obj L ⟶
      (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj I :=
  (𝟙 _ ≫ sheafHomComplexHomologyEquivHomotopyCategory X L I 0 η) ≫
    (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).map
      ((shiftFunctorZero
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
          ℤ).app I).hom

/-- `sheafHomGlobalHomotopyCategoryHom` in terms of the cohomology class of the global section
complex. -/
theorem sheafHomGlobalHomotopyCategoryHom_eq
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (η : (globalSectionsComplex X (sheafHomComplex X L I).obj).homology 0) :
    sheafHomGlobalHomotopyCategoryHom X L I η =
      (𝟙 _ ≫ CohomologyClass.homAddEquiv (homologyAddEquiv L I 0
          (AddEquiv.ulift ((uliftHomologyIso (L.HomComplex I) 0).hom
            (HomologicalComplex.homologyMap
              (sheafHomComplex X L I).globalSectionsIso.hom 0 η))))) ≫
        (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).map
          ((shiftFunctorZero
            (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
              ℤ).app I).hom :=
  rfl

/-- **`sheafHomGlobalHomotopyCategoryHom` is natural in both variables for `homMap`.** -/
theorem sheafHomGlobalHomotopyCategoryHom_naturality
    {L L' I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : L' ⟶ L) (m : I ⟶ I')
    (η : (globalSectionsComplex X (sheafHomComplex X L I).obj).homology 0) :
    sheafHomGlobalHomotopyCategoryHom X L' I'
        (HomologicalComplex.homologyMap (globalSectionsComplexMap X (homMap X k m)) 0 η) =
      (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ)).map k ≫
        sheafHomGlobalHomotopyCategoryHom X L I η ≫
          (HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).map m := by
  rw [sheafHomGlobalHomotopyCategoryHom_eq X L' I' _,
    sheafHomGlobalHomotopyCategoryHom_eq X L I η, homologyAddEquiv_globalSectionsIso_homMap]
  simp only [CohomologyClass.homAddEquiv_apply, toHom_cohomologyClassPrecomp,
    toHom_cohomologyClassPostcomp, Category.id_comp, Category.assoc]
  have hz := (shiftFunctorZero
    (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      ℤ).hom.naturality m
  simp only [Iso.app_hom, Functor.id_map] at hz ⊢
  rw [← Functor.map_comp, ← Functor.map_comp, hz]

/-- Stacks 0A94 globally is Stacks 0A8Z in degree `0` followed by the identification of
homotopy-category with derived-category morphisms into a K-injective target. -/
theorem sheafHomGlobalHomologyEquivDerivedCategoryHom_apply
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    (η : (globalSectionsComplex X (sheafHomComplex X L I).obj).homology 0) :
    sheafHomGlobalHomologyEquivDerivedCategoryHom X L I η =
      homotopyHomDerivedCategoryEquiv L I (sheafHomGlobalHomotopyCategoryHom X L I η) := rfl

/-- **Stacks 0A94, global sections, naturality.** The identification of the degree-zero
cohomology of the global sections of `SheafHom(L, I)` with `Hom_{D(O)}(L, I)` is natural in both
variables: `homMap k m`, for `k : L' ⟶ L` and `m : I ⟶ I'`, acts on it by precomposition with `k`
and postcomposition with `m` in the derived category.

This is the global companion of
`AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom_naturality`, and it
is what a consumer identifying two such bijections of morphism groups needs. -/
@[stacks 0A94 "global sections, naturality"]
theorem sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality
    {L L' I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective] (k : L' ⟶ L) (m : I ⟶ I')
    (η : (globalSectionsComplex X (sheafHomComplex X L I).obj).homology 0) :
    sheafHomGlobalHomologyEquivDerivedCategoryHom X L' I'
        (HomologicalComplex.homologyMap (globalSectionsComplexMap X (homMap X k m)) 0 η) =
      DerivedCategory.Q.map k ≫ sheafHomGlobalHomologyEquivDerivedCategoryHom X L I η ≫
        DerivedCategory.Q.map m := by
  rw [sheafHomGlobalHomologyEquivDerivedCategoryHom_apply X L' I' _,
    sheafHomGlobalHomotopyCategoryHom_naturality, homotopyHomDerivedCategoryEquiv_naturality,
    sheafHomGlobalHomologyEquivDerivedCategoryHom_apply X L I η]

end AlgebraicGeometry.RingedSite

end
