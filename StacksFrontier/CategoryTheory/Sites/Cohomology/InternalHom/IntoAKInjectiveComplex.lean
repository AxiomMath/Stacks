module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexFunctoriality
public import StacksFrontier.Homology.HomComplex.RHom
import StacksCore.Tactic.StacksAttribute

/-!
# The internal Hom complex into a K-injective complex computes derived-category morphisms

Let `(C, O)` be a ringed site, `L` a complex of `O`-modules and `I` a K-injective complex of
`O`-modules. The degree-zero cohomology of the sections of the internal Hom complex
`SheafHom(L, I)` computes morphisms in the derived category — over an object `U` of the site it
gives `Hom_{D(O|_U)}(L|_U, I|_U)`, and globally `Hom_{D(O)}(L, I)`.

Both statements are the corresponding Hom-complex computations in the homotopy category
(Stacks 0A8Y locally, Stacks 0A8Z globally) composed with the fact that the localisation
functor from the homotopy category to the derived category is bijective on morphisms into a
K-injective object. On a slice site the hypothesis transports because the restriction of a
K-injective complex is K-injective, which is Stacks 08FI.

## Main definitions

* `AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv`: morphisms into a K-injective
  complex are the same in the homotopy and the derived category.
* `AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom` and
  `AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom`: the local and
  global computations, the two parts of Stacks 0A94.
* `homComplexConj`: pre- and postcomposition, as a morphism of Hom complexes.
* `AlgebraicGeometry.RingedSite.sheafHomSectionHomotopyCategoryHom`: the homotopy-category
  morphism `L|_U ⟶ I|_U` attached to a degree-zero class of the section complex.

## Main results

* `AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom_naturality`: the
  local identification of Stacks 0A94 is natural in both variables — contravariantly in `L` and
  covariantly in `I` — for the functoriality `AlgebraicGeometry.RingedSite.homMap` of the
  internal Hom complex.
* `homologyAddEquiv_conj`: on cohomology classes, `homComplexConj` is the composite of
  `cohomologyClassPrecomp` and `cohomologyClassPostcomp`.
* `AlgebraicGeometry.RingedSite.sectionsIso_homMap`: the local description of the internal Hom
  complex carries `homMap` to `homComplexConj`.

## Implementation notes

The objects of the derived category represented by the displayed complexes are written as
`DerivedCategory.Q.obj` of those complexes, and on a slice site the restrictions are
represented by the degreewise restrictions of the same complexes. The results are stated as
additive equivalences, expressing the canonical identifications of the source rather than a
mere bijection of the underlying sets. `HasDerivedCategory.standard` is used as a local
instance, so no choice of derived-category universe has to be threaded through the statements.

The naturality of the local identification is stated for the functoriality `homMap` of the
internal Hom complex, that is for morphisms of complexes in each variable, and not for arbitrary
morphisms of the derived category: the target of the identification is a group of
derived-category morphisms, so the square is the naturality of a bijection of *morphism groups*
and that is what a consumer identifying two such bijections needs.

## Where the global companion is

The companion naturality of `sheafHomGlobalHomologyEquivDerivedCategoryHom`, the global half of
Stacks 0A94, is proved in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalHomNaturality`, as
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality`. The
local statement here is proved from the compatibility of the `sectionsIso` field of
`AlgebraicGeometry.RingedSite.SheafHomComplex` with `AlgebraicGeometry.RingedSite.homMap`, which
is `AlgebraicGeometry.RingedSite.sectionsIso_homMap_v`; the analogous compatibility of the
`globalSectionsIso` field is `AlgebraicGeometry.RingedSite.globalSectionsIso_homMap_v` of the
`GlobalNaturality` section below, and that is the only input the global case needs. The one extra
step is the degreewise universe lift that `globalSectionsIso` carries and `sectionsIso` does not,
which has to be crossed on homology.

## References

* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v r w

section HomComplexConj

open CochainComplex.HomComplex

/-- Pre- and postcomposition with `f : K' ⟶ K` and `g : L ⟶ L'`, as a morphism of Hom complexes
`Hom^•(K, L) ⟶ Hom^•(K', L')`. Degreewise it sends a cochain `z` to `f ∘ z ∘ g`, which commutes
with the Hom-complex differential because `f` and `g` are morphisms of complexes. -/
noncomputable def homComplexConj {A : Type u} [Category.{v} A] [Abelian A]
    {K K' L L' : CochainComplex A ℤ} (f : K' ⟶ K) (g : L ⟶ L') :
    CochainComplex.HomComplex K L ⟶ CochainComplex.HomComplex K' L' where
  f n := AddCommGrpCat.ofHom
    { toFun := fun z ↦
        (Cochain.ofHom f).comp (z.comp (Cochain.ofHom g) (add_zero n)) (zero_add n)
      map_zero' := by cat_disch
      map_add' := by cat_disch }
  comm' i j hij := by
    subst j
    ext z
    exact (δ_ofHom_comp f _ (i + 1)).trans
      (congrArg (fun w ↦ (Cochain.ofHom f).comp w (zero_add (i + 1)))
        (δ_comp_ofHom z g (i + 1)))

/-- The identification `Hⁿ(Hom^•(K, L)) ≃+ CohomologyClass K L n` turns the map induced on
homology by `homComplexConj f g` into `cohomologyClassPrecomp f` applied to
`cohomologyClassPostcomp g`: the Hom complex is contravariant in its first and covariant in its
second variable, compatibly. -/
theorem homologyAddEquiv_conj {A : Type u} [Category.{v} A] [Abelian A]
    {K K' L L' : CochainComplex A ℤ} (f : K' ⟶ K) (g : L ⟶ L') (n : ℤ)
    (η : (K.HomComplex L).homology n) :
    homologyAddEquiv K' L' n (HomologicalComplex.homologyMap (homComplexConj f g) n η) =
      cohomologyClassPrecomp f L' n
        (cohomologyClassPostcomp K g n (homologyAddEquiv K L n η)) := by
  let h := leftHomologyData K L n
  let h' := leftHomologyData K' L' n
  have hπ : Function.Surjective (ConcreteCategory.hom ((K.HomComplex L).homologyπ n)) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z, rfl⟩ := hπ η
  let a : Cocycle K L n := h.cyclesIso.hom z
  have key : ∀ {K L : CochainComplex A ℤ} (w : (K.HomComplex L).cycles n),
      homologyAddEquiv K L n ((K.HomComplex L).homologyπ n w) =
        CohomologyClass.mk ((leftHomologyData K L n).cyclesIso.hom w : Cocycle K L n) :=
    fun w ↦ ConcreteCategory.congr_hom
      (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom _ _) w
  have hmap : h'.cyclesIso.hom ((HomologicalComplex.cyclesMap (homComplexConj f g) n) z) =
      (a.postcomp g).precomp f := by
    apply Subtype.ext
    have h1 := ConcreteCategory.congr_hom h'.cyclesIso_hom_comp_i
      ((HomologicalComplex.cyclesMap (homComplexConj f g) n) z)
    have h2 := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (homComplexConj f g) n) z
    have h3 := ConcreteCategory.congr_hom h.cyclesIso_hom_comp_i z
    simp only [ConcreteCategory.comp_apply] at h1 h2 h3
    refine h1.trans (h2.trans ?_)
    change (Cochain.ofHom f).comp
        ((((K.HomComplex L).iCycles n) z).comp (Cochain.ofHom g) (add_zero n)) (zero_add n) =
      (Cochain.ofHom f).comp ((a.1).comp (Cochain.ofHom g) (add_zero n)) (zero_add n)
    congr 2
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (homComplexConj f g) n) z
  simp only [ConcreteCategory.comp_apply] at hnat
  rw [hnat, show _ = CohomologyClass.mk a from key z, key, hmap,
    cohomologyClassPostcomp_mk, cohomologyClassPrecomp_mk]

end HomComplexConj

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

/-- For a K-injective complex `I` in an abelian category with a derived category, morphisms
`K ⟶ I` in the homotopy category are the same as morphisms `K ⟶ I` in the derived category:
the localisation functor out of the homotopy category is bijective on morphisms into a
K-injective object. -/
noncomputable def homotopyHomDerivedCategoryEquiv
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (K I : CochainComplex C ℤ) [I.IsKInjective] :
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I) ≃+
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj I) := by
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  exact (AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
      (CochainComplex.IsKInjective.Qh_map_bijective (q.obj K) I)).trans
    (CategoryTheory.Linear.homCongr ℤ ((DerivedCategory.quotientCompQhIso C).app K)
      ((DerivedCategory.quotientCompQhIso C).app I)).toAddEquiv

/-- **Stacks 0A94, sections over an object.** If `I` is K-injective then the degree-zero
cohomology of the sections over `U` of the internal Hom complex from `L` to `I` is the group of
morphisms `L|_U ⟶ I|_U` in the derived category of `O|_U`-modules.

This is Stacks 0A8Y in degree `0` followed by the identification of homotopy-category with
derived-category morphisms into a K-injective target; the restriction `I|_U` is K-injective by
Stacks 08FI. -/
@[stacks 0A94 "sections over an object"]
noncomputable def sheafHomSectionHomologyEquivDerivedCategoryHom
    (X : RingedSite.{u, u, u})
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] (U : X.C) :
    (sectionComplex X (sheafHomComplex X L I).obj U).homology 0 ≃+
      (DerivedCategory.Q.obj (restrictComplex X L U) ⟶
        DerivedCategory.Q.obj (restrictComplex X I U)) :=
  (sheafHomComplexSectionHomologyEquivHomotopyCategory X L I U 0).trans <| by
    letI : (restrictComplex X I U).IsKInjective :=
      Stacks.Cohomology.Localization.isKInjective_over X.J
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U I
    let q := HomotopyCategory.quotient
      (SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) (ComplexShape.up ℤ)
    exact (CategoryTheory.Linear.homCongr ℤ (Iso.refl _)
      (q.mapIso ((shiftFunctorZero _ ℤ).app (restrictComplex X I U)))).toAddEquiv.trans
        (homotopyHomDerivedCategoryEquiv (restrictComplex X L U)
          (restrictComplex X I U))

/-- **Stacks 0A94, global sections.** If `I` is K-injective then the degree-zero cohomology of
the global sections of the internal Hom complex from `L` to `I` is the group of morphisms
`L ⟶ I` in the derived category of `O`-modules.

This is Stacks 0A8Z in degree `0` followed by the same identification of homotopy-category with
derived-category morphisms into a K-injective target. -/
@[stacks 0A94 "global sections"]
noncomputable def sheafHomGlobalHomologyEquivDerivedCategoryHom
    (X : RingedSite.{u, v, r})
    [HasSheafify X.J AddCommGrpCat.{max u v w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (L I : CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    (globalSectionsComplex X (sheafHomComplex X L I).obj).homology 0 ≃+
      (DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj I) :=
  (sheafHomComplexHomologyEquivHomotopyCategory X L I 0).trans <| by
    let q := HomotopyCategory.quotient
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
    exact (CategoryTheory.Linear.homCongr ℤ (Iso.refl _)
      (q.mapIso ((shiftFunctorZero _ ℤ).app I))).toAddEquiv.trans
        (homotopyHomDerivedCategoryEquiv L I)

section Naturality

open Opposite CochainComplex.HomComplex

variable (X : RingedSite.{u, u, u})

/-- The morphism of section complexes over `U` induced by a morphism of complexes of
`O`-modules. -/
noncomputable abbrev sectionComplexMap (U : X.C)
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : A ⟶ B) :
    sectionComplex X A U ⟶ sectionComplex X B U :=
  ((sheafToPresheaf X.J AddCommGrpCat.{u} ⋙
      (evaluation X.Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
    (((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ)

/-- The local description of the internal Hom complex carries `homMap k m` to the pre- and
postcomposition `homComplexConj` of the restrictions of `k` and `m`. This is Stacks 0A90 (1),
`sectionsIso_homMap_v`, read as a square of morphisms of complexes. -/
lemma sectionsIso_homMap (U : X.C)
    {K K' M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K' ⟶ K) (m : M ⟶ M') :
    sectionComplexMap X U (homMap X k m) ≫ ((sheafHomComplex X K' M').sectionsIso U).hom =
      ((sheafHomComplex X K M).sectionsIso U).hom ≫
        homComplexConj (restrictComplexMap X U k) (restrictComplexMap X U m) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  refine Cochain.ext _ _ fun p q hpq => ?_
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply]
  exact (sectionsIso_homMap_v X k m U n p q hpq s).trans
    (cochainConj_v X U k m _ p q hpq).symm

section Localization

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- `homotopyHomDerivedCategoryEquiv` is the localisation functor out of the homotopy category,
conjugated by the identification of `DerivedCategory.Qh` on a quotient with
`DerivedCategory.Q`. -/
theorem homotopyHomDerivedCategoryEquiv_apply (K I : CochainComplex C ℤ) [I.IsKInjective]
    (θ : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I) :
    homotopyHomDerivedCategoryEquiv K I θ =
      (((DerivedCategory.quotientCompQhIso C).app K).inv ≫ DerivedCategory.Qh.map θ) ≫
        ((DerivedCategory.quotientCompQhIso C).app I).hom := rfl

/-- The identification of homotopy-category with derived-category morphisms into a K-injective
complex is natural in both variables: it carries pre- and postcomposition with the images in the
homotopy category to pre- and postcomposition with the images in the derived category. -/
theorem homotopyHomDerivedCategoryEquiv_naturality {K K' I I' : CochainComplex C ℤ}
    [I.IsKInjective] [I'.IsKInjective] (f : K' ⟶ K) (g : I ⟶ I')
    (θ : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I) :
    homotopyHomDerivedCategoryEquiv K' I'
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f ≫ θ ≫
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map g) =
      DerivedCategory.Q.map f ≫ homotopyHomDerivedCategoryEquiv K I θ ≫
        DerivedCategory.Q.map g := by
  have hf := (DerivedCategory.quotientCompQhIso C).inv.naturality f
  have hg := (DerivedCategory.quotientCompQhIso C).hom.naturality g
  rw [homotopyHomDerivedCategoryEquiv_apply, homotopyHomDerivedCategoryEquiv_apply]
  simp only [Iso.app_inv, Iso.app_hom, Functor.comp_map, Functor.map_comp,
    Category.assoc] at hf hg ⊢
  rw [hg, ← reassoc_of% hf]

end Localization

/-- Stacks 0A8Y is the local description of the internal Hom complex read on homology, followed
by the identification of the cohomology of a Hom complex with homotopy-category morphisms. -/
theorem sheafHomComplexSectionHomologyEquivHomotopyCategory_apply
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (n : ℤ)
    (η : (sectionComplex X (sheafHomComplex X L I).obj U).homology n) :
    sheafHomComplexSectionHomologyEquivHomotopyCategory X L I U n η =
      CohomologyClass.homAddEquiv
        (homologyAddEquiv (restrictComplex X L U) (restrictComplex X I U) n
          (HomologicalComplex.homologyMap ((sheafHomComplex X L I).sectionsIso U).hom n η)) := rfl

/-- The morphism `L|_U ⟶ I|_U` in the homotopy category of `O|_U`-modules attached to a
degree-zero class of the section complex of the internal Hom complex: Stacks 0A8Y in degree `0`,
with the degree-zero shift of the target normalised away. -/
noncomputable def sheafHomSectionHomotopyCategoryHom
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C)
    (η : (sectionComplex X (sheafHomComplex X L I).obj U).homology 0) :
    (HomotopyCategory.quotient
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
        (ComplexShape.up ℤ)).obj (restrictComplex X L U) ⟶
      (HomotopyCategory.quotient
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
        (ComplexShape.up ℤ)).obj (restrictComplex X I U) :=
  (𝟙 _ ≫ sheafHomComplexSectionHomologyEquivHomotopyCategory X L I U 0 η) ≫
    (HomotopyCategory.quotient
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
        (ComplexShape.up ℤ)).map
      ((shiftFunctorZero (CochainComplex
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ) ℤ).app
        (restrictComplex X I U)).hom

/-- `sheafHomSectionHomotopyCategoryHom` in terms of the cohomology class of the section
complex. -/
theorem sheafHomSectionHomotopyCategoryHom_eq
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C)
    (η : (sectionComplex X (sheafHomComplex X L I).obj U).homology 0) :
    sheafHomSectionHomotopyCategoryHom X L I U η =
      (𝟙 _ ≫ CohomologyClass.homAddEquiv
          (homologyAddEquiv (restrictComplex X L U) (restrictComplex X I U) 0
            (HomologicalComplex.homologyMap ((sheafHomComplex X L I).sectionsIso U).hom 0 η))) ≫
        (HomotopyCategory.quotient
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
            (ComplexShape.up ℤ)).map
          ((shiftFunctorZero (CochainComplex
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ) ℤ).app
            (restrictComplex X I U)).hom := rfl

/-- The cohomology class of the section complex attached to `homMap k m` is the class attached to
the original one, precomposed with `k|_U` and postcomposed with `m|_U`. -/
private theorem homologyAddEquiv_sectionsIso_homMap
    {L L' I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : L' ⟶ L) (m : I ⟶ I') (U : X.C)
    (η : (sectionComplex X (sheafHomComplex X L I).obj U).homology 0) :
    homologyAddEquiv (restrictComplex X L' U) (restrictComplex X I' U) 0
        (HomologicalComplex.homologyMap ((sheafHomComplex X L' I').sectionsIso U).hom 0
          (HomologicalComplex.homologyMap (sectionComplexMap X U (homMap X k m)) 0 η)) =
      cohomologyClassPrecomp (restrictComplexMap X U k) (restrictComplex X I' U) 0
        (cohomologyClassPostcomp (restrictComplex X L U) (restrictComplexMap X U m) 0
          (homologyAddEquiv (restrictComplex X L U) (restrictComplex X I U) 0
            (HomologicalComplex.homologyMap
              ((sheafHomComplex X L I).sectionsIso U).hom 0 η))) := by
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
    sectionsIso_homMap, HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply,
    homologyAddEquiv_conj]

/-- `sheafHomSectionHomotopyCategoryHom` is natural in both variables for `homMap`. -/
theorem sheafHomSectionHomotopyCategoryHom_naturality
    {L L' I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : L' ⟶ L) (m : I ⟶ I') (U : X.C)
    (η : (sectionComplex X (sheafHomComplex X L I).obj U).homology 0) :
    sheafHomSectionHomotopyCategoryHom X L' I' U
        (HomologicalComplex.homologyMap (sectionComplexMap X U (homMap X k m)) 0 η) =
      (HomotopyCategory.quotient
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
          (ComplexShape.up ℤ)).map (restrictComplexMap X U k) ≫
        sheafHomSectionHomotopyCategoryHom X L I U η ≫
          (HomotopyCategory.quotient
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
            (ComplexShape.up ℤ)).map (restrictComplexMap X U m) := by
  rw [sheafHomSectionHomotopyCategoryHom_eq X L' I' U _,
    sheafHomSectionHomotopyCategoryHom_eq X L I U η, homologyAddEquiv_sectionsIso_homMap]
  simp only [CohomologyClass.homAddEquiv_apply, toHom_cohomologyClassPrecomp,
    toHom_cohomologyClassPostcomp, Category.id_comp, Category.assoc]
  have hz := (shiftFunctorZero
    (CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ)
      ℤ).hom.naturality (restrictComplexMap X U m)
  simp only [Iso.app_hom, Functor.id_map] at hz ⊢
  rw [← Functor.map_comp, ← Functor.map_comp, hz]

/-- Stacks 0A94 over an object is Stacks 0A8Y in degree `0` followed by the identification of
homotopy-category with derived-category morphisms into a K-injective target. -/
theorem sheafHomSectionHomologyEquivDerivedCategoryHom_apply
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] (U : X.C)
    [(restrictComplex X I U).IsKInjective]
    (η : (sectionComplex X (sheafHomComplex X L I).obj U).homology 0) :
    sheafHomSectionHomologyEquivDerivedCategoryHom X L I U η =
      homotopyHomDerivedCategoryEquiv (restrictComplex X L U) (restrictComplex X I U)
        (sheafHomSectionHomotopyCategoryHom X L I U η) := rfl

/-- **Stacks 0A94, sections over an object, naturality.** The identification of the degree-zero
cohomology of the sections over `U` of `SheafHom(L, I)` with `Hom_{D(O|_U)}(L|_U, I|_U)` is
natural in both variables: `homMap k m`, for `k : L' ⟶ L` and `m : I ⟶ I'`, acts on it by
precomposition with `k|_U` and postcomposition with `m|_U` in the derived category. -/
@[stacks 0A94 "sections over an object, naturality"]
theorem sheafHomSectionHomologyEquivDerivedCategoryHom_naturality
    {L L' I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective] (k : L' ⟶ L) (m : I ⟶ I') (U : X.C)
    (η : (sectionComplex X (sheafHomComplex X L I).obj U).homology 0) :
    sheafHomSectionHomologyEquivDerivedCategoryHom X L' I' U
        (HomologicalComplex.homologyMap (sectionComplexMap X U (homMap X k m)) 0 η) =
      DerivedCategory.Q.map (restrictComplexMap X U k) ≫
        sheafHomSectionHomologyEquivDerivedCategoryHom X L I U η ≫
          DerivedCategory.Q.map (restrictComplexMap X U m) := by
  have : (restrictComplex X I U).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U I
  have : (restrictComplex X I' U).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U I'
  rw [sheafHomSectionHomologyEquivDerivedCategoryHom_apply X L' I' U _,
    sheafHomSectionHomotopyCategoryHom_naturality, homotopyHomDerivedCategoryEquiv_naturality,
    sheafHomSectionHomologyEquivDerivedCategoryHom_apply X L I U η]

end Naturality

section GlobalNaturality

open Opposite CochainComplex.HomComplex

variable (X : RingedSite.{u, v, r})

/-- The morphism of global section complexes induced by a morphism of complexes of
`O`-modules. -/
noncomputable abbrev globalSectionsComplexMap
    {A B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : A ⟶ B) :
    globalSectionsComplex X A ⟶ globalSectionsComplex X B :=
  ((abelianGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ)

/-- A global section is a compatible family, so `globalSectionsComplexMap` acts on it by
applying the morphism to each of its sections. -/
lemma globalSectionsComplexMap_val
    {A B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : A ⟶ B) (n : ℤ)
    (s : (globalSectionsComplex X A).X n) (U : X.C) :
    (AddCommGrpCat.Hom.hom ((globalSectionsComplexMap X φ).f n) s).val (op U) =
      ((φ.f n).val.app (op U)) (s.val (op U)) := rfl

/-- The global description of the internal Hom complex carries `homMap k m` to pre- and
postcomposition with `k` and `m`. This is the global-sections companion of Stacks 0A90 (1),
`sectionsIso_homMap_v`, read on the cochain determined by a global section. -/
lemma globalSectionsIso_homMap_v
    {K K' M M' : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K' ⟶ K) (m : M ⟶ M')
    (n p q : ℤ) (hpq : p + n = q)
    (s : (globalSectionsComplex X (sheafHomComplex X K M).obj).X n) :
    (AddCommGrpCat.Hom.hom ((sheafHomComplex X K' M').globalSectionsIso.hom.f n)
        (AddCommGrpCat.Hom.hom ((globalSectionsComplexMap X (homMap X k m)).f n) s)).down.v
          p q hpq =
      k.f p ≫ (AddCommGrpCat.Hom.hom ((sheafHomComplex X K M).globalSectionsIso.hom.f n)
        s).down.v p q hpq ≫ m.f q := by
  ext U x
  obtain ⟨U⟩ := U
  have key := sectionsIso_homMap_v X k m U n p q hpq
    (show ((sheafHomComplex X K M).obj.X n).val.obj (op U) from s.val (op U))
  rw [sheafHomComplex_globalSectionsIso_v_app X K' M' n p q hpq
      (AddCommGrpCat.Hom.hom ((globalSectionsComplexMap X (homMap X k m)).f n) s) U x,
    globalSectionsComplexMap_val, key]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  rw [sheafHomComplex_globalSectionsIso_v_app X K M n p q hpq s U _]
  rfl

end GlobalNaturality

section HomComplexConjComponents

open CochainComplex.HomComplex

/-- The components of `homComplexConj`: it sends a cochain `z` to `f ∘ z ∘ g` degreewise. This
is the Hom-complex counterpart of `cochainConj_v`. -/
lemma homComplexConj_v {A : Type u} [Category.{v} A] [Abelian A]
    {K K' L L' : CochainComplex A ℤ} (f : K' ⟶ K) (g : L ⟶ L') (n : ℤ)
    (z : Cochain K L n) (p q : ℤ) (hpq : p + n = q) :
    (AddCommGrpCat.Hom.hom ((homComplexConj f g).f n) z).v p q hpq =
      f.f p ≫ z.v p q hpq ≫ g.f q := by
  change ((Cochain.ofHom f).comp (z.comp (Cochain.ofHom g) (add_zero n)) (zero_add n)).v
    p q hpq = _
  rw [Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq,
    Cochain.comp_v z _ (add_zero n) p q q hpq (add_zero q), Cochain.ofHom_v, Cochain.ofHom_v]

end HomComplexConjComponents

end AlgebraicGeometry.RingedSite

end
