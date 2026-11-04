module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomLocalization

/-!
# Transporting the degree-zero reading of the global derived hom

Let `(C, O)` be a ringed site. The module
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomLocalization`
reads the canonical map `Hom^•(F, G) ⟶ RHom_O(F, G)` on degree-zero cohomology at a
*representative pair* — a K-flat source and a K-injective target. This file proves that the
degree-zero identification of Tag 08JA is **natural in both variables for morphisms of
complexes**, and that any morphism between the classes of two complexes is, after passing to a
K-flat refinement of its source, the class of a morphism of complexes composed with the inverse
of such a class.

## Main results

* `AlgebraicGeometry.RingedSite.globalSectionsDerivedUnit_naturality`: the comparison from
  global sections to derived global sections is natural; it is the component of the natural
  transformation `AlgebraicGeometry.RingedSite.globalSectionsDerivedUnitNatTrans`.
* `AlgebraicGeometry.RingedSite.globalSectionsKInjectiveIso_hom_naturality` and
  `AlgebraicGeometry.RingedSite.globalSectionsKInjectiveIso_inv_naturality`: the same for the
  isomorphism of Tag 07A5 on K-injective complexes.
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality`:
  **Tag 08JA at a representative pair is natural in both variables for morphisms of
  complexes** — contravariantly in the source, covariantly in the K-injective target.
* `AlgebraicGeometry.RingedSite.exists_kFlat_common_refinement`: **every morphism between the
  classes of two complexes is a morphism of complexes out of a K-flat refinement of its source.**
  For `θ : Q A ⟶ Q A'` there are a K-flat `R`, a morphism `u : R ⟶ A` whose class is invertible
  and a morphism `v : R ⟶ A'` with `Q u ≫ θ = Q v`.
* `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor_map_comp` and
  `AlgebraicGeometry.RingedSite.derivedSheafHomObjectsModelIso_hom`: the two-variable
  functoriality of the derived internal Hom, and the comparison with a pair of representatives
  read as a two-variable induced morphism.
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_apply`: Tag 08JA at arbitrary
  objects, unfolded as Tag 08JA at the chosen models conjugated by the two representing
  isomorphisms.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-! ### The comparison with derived global sections is natural -/

/-- **The comparison from global sections to derived global sections, as a natural
transformation.** It is the composite of the whiskerings of the four canonical natural
transformations whose components compose to
`AlgebraicGeometry.RingedSite.globalSectionsDerivedUnit`. -/
def globalSectionsDerivedUnitNatTrans :
    (moduleGlobalSections X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedModuleGlobalSections X :=
  Functor.whiskerLeft ((moduleGlobalSections X).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).inv ≫
    Functor.whiskerRight
        (((moduleGlobalSections X).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv)
        DerivedCategory.Qh ≫
      Functor.whiskerLeft
          (HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
          (derivedModuleGlobalSectionsUnit X) ≫
        Functor.whiskerRight
          (DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom
          (derivedModuleGlobalSections X)

/-- The components of `AlgebraicGeometry.RingedSite.globalSectionsDerivedUnitNatTrans` are the
comparisons `AlgebraicGeometry.RingedSite.globalSectionsDerivedUnit`. -/
theorem globalSectionsDerivedUnitNatTrans_app
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (globalSectionsDerivedUnitNatTrans X).app H = globalSectionsDerivedUnit X H := rfl

/-- **The comparison from global sections to derived global sections is natural** in the complex,
for morphisms of complexes. -/
theorem globalSectionsDerivedUnit_naturality
    {H H' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : H ⟶ H') :
    DerivedCategory.Q.map (globalSectionsComplexMap X φ) ≫ globalSectionsDerivedUnit X H' =
      globalSectionsDerivedUnit X H ≫
        (derivedModuleGlobalSections X).map (DerivedCategory.Q.map φ) :=
  (globalSectionsDerivedUnitNatTrans X).naturality φ

/-- **Tag 07A5 is natural on K-injective complexes**: the identification of the class of the
complex of global sections of a K-injective complex with its derived global sections is natural
for morphisms of complexes. -/
theorem globalSectionsKInjectiveIso_hom_naturality
    {I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    (φ : I ⟶ I') :
    DerivedCategory.Q.map (globalSectionsComplexMap X φ) ≫
        (globalSectionsKInjectiveIso X I').hom =
      (globalSectionsKInjectiveIso X I).hom ≫
        (derivedModuleGlobalSections X).map (DerivedCategory.Q.map φ) :=
  globalSectionsDerivedUnit_naturality X φ

/-- `AlgebraicGeometry.RingedSite.globalSectionsKInjectiveIso_hom_naturality` read on the
inverses. -/
theorem globalSectionsKInjectiveIso_inv_naturality
    {I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    (φ : I ⟶ I') :
    (derivedModuleGlobalSections X).map (DerivedCategory.Q.map φ) ≫
        (globalSectionsKInjectiveIso X I').inv =
      (globalSectionsKInjectiveIso X I).inv ≫
        DerivedCategory.Q.map (globalSectionsComplexMap X φ) := by
  rw [Iso.comp_inv_eq, Category.assoc, globalSectionsKInjectiveIso_hom_naturality X φ,
    Iso.inv_hom_id_assoc]

/-! ### Tag 08JA at a representative pair is natural -/

/-- The two isomorphisms out of which the degree-zero reading of the global derived hom is built
at a representative pair, the comparison of Tag 0A97 and the isomorphism of Tag 07A5, are natural
in both variables for morphisms of complexes: their composite carries the map induced by `k` and
`m` to the class of the morphism `AlgebraicGeometry.RingedSite.homMap` of internal Hom
complexes. -/
theorem derivedSheafHom_comparison_globalSections_naturality
    {A A' I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective]
    [((sheafHomComplex X A' I').obj).IsKInjective] (k : A' ⟶ A) (m : I ⟶ I') :
    (derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map k).op).app
              (DerivedCategory.Q.obj I) ≫
            ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
              (DerivedCategory.Q.map m)) ≫
        ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A' I').hom ≫
          (globalSectionsKInjectiveIso X ((sheafHomComplex X A' I').obj)).inv) =
      ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
          (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv) ≫
        DerivedCategory.Q.map (globalSectionsComplexMap X (homMap X k m)) := by
  rw [Category.assoc, ← globalSectionsKInjectiveIso_inv_naturality X (homMap X k m)]
  simp only [← Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, Category.assoc,
    derivedSheafHomComparison_naturality X k m]

/-! ### The ingredients of the model-independence of Tag 08JA -/

/-- **The morphisms induced on the derived internal Hom in both variables compose.** The
composite of two morphisms induced on `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` by
a contravariant and a covariant map is the morphism induced by the two composites. -/
theorem derivedSheafHomBifunctor_map_comp
    {L L' L'' M M' M'' :
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : L' ⟶ L) (ψ : M ⟶ M') (φ' : L'' ⟶ L') (ψ' : M' ⟶ M'') :
    (((derivedSheafHomBifunctor X).map φ.op).app M ≫
          ((derivedSheafHomBifunctor X).obj (op L')).map ψ) ≫
        (((derivedSheafHomBifunctor X).map φ'.op).app M' ≫
          ((derivedSheafHomBifunctor X).obj (op L'')).map ψ') =
      ((derivedSheafHomBifunctor X).map (φ' ≫ φ).op).app M ≫
        ((derivedSheafHomBifunctor X).obj (op L'')).map (ψ ≫ ψ') := by
  simp [op_comp, Functor.map_comp, NatTrans.comp_app, NatTrans.naturality_assoc]

/-- The comparison of the derived internal Hom of two objects with that of two representing
complexes is the morphism induced in both variables by the two representing isomorphisms, the
covariant one inverted. -/
theorem derivedSheafHomObjectsModelIso_hom
    {L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eA : DerivedCategory.Q.obj A ≅ L) (eI : DerivedCategory.Q.obj I ≅ M) :
    (derivedSheafHomObjectsModelIso X eA eI).hom =
      ((derivedSheafHomBifunctor X).map eA.hom.op).app M ≫
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map eI.inv := rfl

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Tag 08JA at a representative pair is natural in both variables for morphisms of
complexes.** For `k : A' ⟶ A` and `m : I ⟶ I'` with `I`, `I'` K-injective and the internal Hom
complexes `SheafHom(A, I)`, `SheafHom(A', I')` K-injective, the identification of the degree-zero
global hypercohomology of `RSheafHom` with a morphism group of `D(O)` carries the map induced by
`k` and `m` to precomposition with `Q k` and postcomposition with `Q m`. -/
theorem derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality
    {A A' I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective]
    [((sheafHomComplex X A' I').obj).IsKInjective] (k : A' ⟶ A) (m : I ⟶ I')
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X A' I'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map k).op).app
                (DerivedCategory.Q.obj I) ≫
              ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
                (DerivedCategory.Q.map m))) ξ) =
      DerivedCategory.Q.map k ≫
        derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X A I ξ ≫
          DerivedCategory.Q.map m := by
  refine (derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_apply X A' I' _).trans ?_
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, Category.assoc,
    derivedSheafHom_comparison_globalSections_naturality X k m]
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  erw [ConcreteCategory.congr_hom
    ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.naturality
      (globalSectionsComplexMap X (homMap X k m)))]
  refine (sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality X k m _).trans ?_
  rw [derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_apply X A I ξ, Functor.map_comp]
  rfl

/-! ### Refining the source of a morphism of the derived category -/

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **Every morphism between the classes of two complexes comes from a morphism of complexes out
of a K-flat refinement of its source.** For `θ : Q A ⟶ Q A'` there are a K-flat complex `R`, a
morphism `u : R ⟶ A` whose class is invertible and a morphism `v : R ⟶ A'` of complexes with
`Q u ≫ θ = Q v`. -/
theorem exists_kFlat_common_refinement
    {A A' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (θ : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj A') :
    ∃ (R : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (_ : Stacks.SheafOfModules.IsKFlat X.O R) (u : R ⟶ A) (v : R ⟶ A'),
      IsIso (DerivedCategory.Q.map u) ∧
        DerivedCategory.Q.map u ≫ θ = DerivedCategory.Q.map v := by
  obtain ⟨Y, s, hs, g, hθ⟩ := DerivedCategory.right_fac θ
  obtain ⟨R, r, hR, hr⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso X Y
  have hr' : IsIso (DerivedCategory.Q.map r) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hr
  refine ⟨R, hR, r ≫ s, r ≫ g, by rw [CategoryTheory.Functor.map_comp]; infer_instance, ?_⟩
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hθ, Category.assoc,
    IsIso.hom_inv_id_assoc]

/-! ### Tag 08JA at arbitrary objects, unfolded at the chosen models -/

/-- **Tag 08JA at arbitrary objects, unfolded at the chosen models.** The degree-zero
identification for arbitrary `L`, `M` is the identification at the chosen K-flat and K-injective
models, conjugated by the two representing isomorphisms. -/
theorem derivedSheafHomGlobalSectionsEquiv_apply
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv X L M ξ =
      ((kFlatModelIso X L).inv ≫
          derivedSheafHomGlobalSectionsEquivOfKFlat X (kFlatModel X L) (kInjectiveModel X M)
            (isKFlat_kFlatModel X L)
            ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
              ((derivedModuleGlobalSections X).map
                (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
                  (kInjectiveModelIso X M)).hom) ξ)) ≫
        (kInjectiveModelIso X M).hom :=
  Linear.homCongr_apply ℤ (kFlatModelIso X L) (kInjectiveModelIso X M)
    (derivedSheafHomGlobalSectionsEquivOfKFlat X (kFlatModel X L) (kInjectiveModel X M)
      (isKFlat_kFlatModel X L)
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
            (kInjectiveModelIso X M)).hom) ξ))

end AlgebraicGeometry.RingedSite

end
