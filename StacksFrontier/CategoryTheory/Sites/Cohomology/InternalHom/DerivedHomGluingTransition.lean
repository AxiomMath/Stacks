module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomGluingRestriction
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.KFlatIntoKInjectiveIsKInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Representatives
public import StacksFrontier.CategoryTheory.Sites.Glueing.AbsoluteGlueingAnySite

/-!
# Restricting a local class of the internal Hom complex along a morphism of the site

Let `(C, 𝒪)` be a ringed site, `L` a complex and `I` a K-injective complex of `𝒪`-modules, and
`a : Z ⟶ U` a morphism of `C`. By Stacks 0A94 the degree-zero classes of sections of
`SheafHom(L, I)` over `U` are the morphisms `L|_U ⟶ I|_U` of `D(𝒪_U)`. This file shows that
restricting a class from `U` to `Z` corresponds to restricting the morphism along `a`, and states
the gluing principle for morphisms of `D(𝒪)` with the compatibility on overlaps expressed in the
derived categories of the slices.

## Main definitions

* `AlgebraicGeometry.RingedSite.restrictComplexDerivedMapAlong`: the restriction along `a` of a
  morphism `L|_U ⟶ I|_U` of `D(𝒪_U)`, read as a morphism `L|_Z ⟶ I|_Z`.

## Main results

* `AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom_sectionComplexRes`:
  restricting a class along `a` corresponds to restricting the morphism along `a`.
* `AlgebraicGeometry.RingedSite.existsUnique_restrictComplexDerivedMap_eq_of_along`: morphisms of
  `D(𝒪)` glue from a family of morphisms over a covering family whose restrictions agree on every
  object mapping to two members (compare Stacks 0D66 for ringed spaces).
* `AlgebraicGeometry.RingedSite.eq_of_mapDerivedCategory_overFunctor_map_eq`: for objects `K`, `L`
  of `D(𝒪)` with `R𝓗om(K, L)` in `D^{≥ 0}`, morphisms `K ⟶ L` agreeing on the members of a
  covering family are equal.
* `AlgebraicGeometry.RingedSite.existsUnique_restrictQMap_overFunctor_eq`: for arbitrary complexes
  `P`, `I` with `R𝓗om(P, I)` in `D^{≥ 0}`, morphisms `P ⟶ I` of `D(𝒪)` glue uniquely from
  compatible families over a covering family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

/-- Restricting to `U` and then along `a` and `g` is restricting to `W`, whichever way the
comparisons are composed. -/
theorem overFunctorMap_comp_hom_eq {C : Type*} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U Z W : C} (a : Z ⟶ U) (g : W ⟶ Z) :
    Functor.isoWhiskerLeft (SheafOfModules.overFunctor.{u} R U)
        (CategoryTheory.SiteGlueing.overMapComp R a g) ≪≫
      SheafOfModules.overFunctorMap.{u} R (g ≫ a) =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (SheafOfModules.overFunctorMap.{u} R a)
        (SheafOfModules.overMap.{u} R g) ≪≫ SheafOfModules.overFunctorMap.{u} R g := by
  apply Iso.ext
  ext M ⟨b⟩ x
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.symm_hom, Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.hom_comp, LinearMap.comp_apply]
  have h1 : ∀ y, ModuleCat.Hom.hom (((SheafOfModules.overFunctorMap R (g ≫ a)).hom.app M).val.app
      (op b)) y = y := fun _ => rfl
  have h2 : ∀ y, ModuleCat.Hom.hom (((SheafOfModules.overFunctorMap R g).hom.app M).val.app
      (op b)) y = y := fun _ => rfl
  have h3 : ∀ y, ModuleCat.Hom.hom (((SheafOfModules.overMap R g).map
      ((SheafOfModules.overFunctorMap R a).hom.app M)).val.app (op b)) y = y := fun _ => rfl
  have h4 : ModuleCat.Hom.hom (((CategoryTheory.SiteGlueing.overMapComp R a g).hom.app
      ((SheafOfModules.overFunctor R U).obj M)).val.app (op b)) x = x := by
    rw [CategoryTheory.SiteGlueing.overMapComp_hom_app_val_app]
    have e : ((SheafOfModules.overFunctor R U).obj M).val.map ((Over.mapComp g a).hom.app b).op =
        M.val.map (𝟙 (op b.left)) := rfl
    rw [e, M.val.map_id]
    rfl
  exact (h1 _).trans (h4.trans ((h2 _).trans ((h3 _).trans rfl)).symm)

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- A morphism `L|_U ⟶ I|_U` of `D(𝒪_U)`, restricted along `a : Z ⟶ U` and read as a morphism
`L|_Z ⟶ I|_Z` of `D(𝒪_Z)`. -/
def restrictComplexDerivedMapAlong {U Z : X.C} (a : Z ⟶ U)
    (ψ : DerivedCategory.Q.obj (restrictComplex X L U) ⟶
      DerivedCategory.Q.obj (restrictComplex X I U)) :
    DerivedCategory.Q.obj (restrictComplex X L Z) ⟶
      DerivedCategory.Q.obj (restrictComplex X I Z) :=
  letI := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a
  letI := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a
  (restrictComplexOverMapIso X L a).inv ≫
    (SheafOfModules.overMap.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).mapDerivedCategory.map ψ ≫
      (restrictComplexOverMapIso X I a).hom

/-- The restriction along `a` of a morphism of complexes `L|_U ⟶ I|_U`, as a morphism
`L|_Z ⟶ I|_Z`. -/
abbrev restrictComplexHomAlong {U Z : X.C} (a : Z ⟶ U)
    (k : restrictComplex X L U ⟶ restrictComplex X I U) :
    restrictComplex X L Z ⟶ restrictComplex X I Z :=
  ((Stacks.SheafOfModules.overFunctorMapComplexIso
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).app L).inv ≫
    ((SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        a).mapHomologicalComplex (ComplexShape.up ℤ)).map k ≫
      ((Stacks.SheafOfModules.overFunctorMapComplexIso
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).app I).hom

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The restriction along `a` of the class of a morphism of complexes is the class of its
restriction. -/
theorem restrictComplexDerivedMapAlong_Q_map {U Z : X.C} (a : Z ⟶ U)
    (k : restrictComplex X L U ⟶ restrictComplex X I U) :
    restrictComplexDerivedMapAlong X L I a (DerivedCategory.Q.map k) =
      DerivedCategory.Q.map (restrictComplexHomAlong X L I a k) := by
  dsimp only [restrictComplexDerivedMapAlong, restrictComplexOverMapIso, Iso.trans_inv,
    Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom]
  rw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  rfl

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The restriction of a morphism of complexes along `a`, computed on sections: its value at an
object `W` over `Z` is the value of the original morphism at `W` viewed over `U`. -/
theorem restrictComplexMapAlong_f_val_app {U Z : X.C} (a : Z ⟶ U)
    (k : restrictComplex X L U ⟶ restrictComplex X I U) (p : ℤ) (W : Over Z)
    (x : ((L.X p).val.obj (op W.left))) :
    ((restrictComplexHomAlong X L I a k).f p).val.app (op W) x =
      ((k.f p).val.app (op ((Over.map a).obj W))) x :=
  rfl

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Every morphism of complexes `L|_U ⟶ I|_U` is the cochain of a degree-zero cycle of the
sections over `U` of the internal Hom complex. -/
theorem exists_cycles_sectionsIso_eq_ofHom {U : X.C}
    (g : restrictComplex X L U ⟶ restrictComplex X I U) :
    ∃ z : (sectionComplex X (sheafHomComplex X L I).obj U).cycles 0,
      ((sheafHomComplex X L I).sectionsIso U).hom.f 0
          ((sectionComplex X (sheafHomComplex X L I).obj U).iCycles 0 z) = Cochain.ofHom g := by
  let K := sectionComplex X (sheafHomComplex X L I).obj U
  let φ := (sheafHomComplex X L I).sectionsIso U
  let y : K.X 0 := φ.inv.f 0 (Cochain.ofHom g)
  have hy : K.d 0 1 y = 0 := by
    let c0 : ((restrictComplex X L U).HomComplex (restrictComplex X I U)).X 0 := Cochain.ofHom g
    have h : (φ.inv.f 0 ≫ K.d 0 1) c0 =
        (((restrictComplex X L U).HomComplex (restrictComplex X I U)).d 0 1 ≫ φ.inv.f 1) c0 := by
      rw [φ.inv.comm]
    have h2 : (((restrictComplex X L U).HomComplex (restrictComplex X I U)).d 0 1) c0 = 0 :=
      δ_ofHom g
    refine h.trans ?_
    rw [ConcreteCategory.comp_apply, h2, map_zero]
  obtain ⟨z, hz⟩ := (ShortComplex.mk (K.iCycles 0) (K.d 0 1) (K.iCycles_d 0 1)).ab_exact_iff.mp
    (ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel 0 1 (by simp))) y hy
  refine ⟨z, ?_⟩
  change φ.hom.f 0 (K.iCycles 0 z) = _
  rw [hz]
  change (φ.inv ≫ φ.hom).f 0 (Cochain.ofHom g) = _
  rw [φ.inv_hom_id]
  rfl

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The local description over `Z` of the restriction along `a` of a section over `U` whose
local description is the cochain of `g`. -/
theorem sectionsIso_sectionComplexRes_ofHom {U Z : X.C} (a : Z ⟶ U)
    (g : restrictComplex X L U ⟶ restrictComplex X I U)
    (s : ((sheafHomComplex X L I).obj.X 0).val.obj (op U))
    (hs : ((sheafHomComplex X L I).sectionsIso U).hom.f 0 s = Cochain.ofHom g) :
    ((sheafHomComplex X L I).sectionsIso Z).hom.f 0
        ((sectionComplexRes X (sheafHomComplex X L I).obj a).f 0 s) =
      Cochain.ofHom (restrictComplexHomAlong X L I a g) := by
  refine Cochain.ext₀ _ _ fun p => ?_
  refine SheafOfModules.hom_ext ?_
  ext ⟨W⟩ x
  have h1 := (sheafHomComplex X L I).restrict_natural a 0 p p (add_zero p) s W.hom x
  rw [hs, Cochain.ofHom_v] at h1
  rw [Cochain.ofHom_v]
  exact h1.symm

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Restricting a local class corresponds to restricting the morphism.** Under Stacks 0A94 over
`U` and over `Z`, the restriction along `a : Z ⟶ U` of a degree-zero class of sections over `U`
of `SheafHom(L, I)` is the restriction along `a` of the corresponding morphism of `D(𝒪_U)`. -/
theorem sheafHomSectionHomologyEquivDerivedCategoryHom_sectionComplexRes [I.IsKInjective]
    {U Z : X.C} (a : Z ⟶ U)
    (c : (sectionComplex X (sheafHomComplex X L I).obj U).homology 0) :
    sheafHomSectionHomologyEquivDerivedCategoryHom X L I Z
        (HomologicalComplex.homologyMap
          (sectionComplexRes X (sheafHomComplex X L I).obj a) 0 c) =
      restrictComplexDerivedMapAlong X L I a
        (sheafHomSectionHomologyEquivDerivedCategoryHom X L I U c) := by
  have : (restrictComplex X I U).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U I
  obtain ⟨g, hg⟩ := StacksDraft.DerivedHom.exists_eq_Q_map_of_isKInjective
    (restrictComplex X L U) (restrictComplex X I U)
    (sheafHomSectionHomologyEquivDerivedCategoryHom X L I U c)
  obtain ⟨z, hz⟩ := exists_cycles_sectionsIso_eq_ofHom X L I g
  have hcz : c = (sectionComplex X (sheafHomComplex X L I).obj U).homologyπ 0 z := by
    apply (sheafHomSectionHomologyEquivDerivedCategoryHom X L I U).injective
    rw [sheafHomSectionHomologyEquivDerivedCategoryHom_homologyπ_of_eq_ofHom X U L I g z hz, hg]
  have hc := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (sectionComplexRes X (sheafHomComplex X L I).obj a) 0) z
  simp only [ConcreteCategory.comp_apply] at hc
  have hz' : ((sheafHomComplex X L I).sectionsIso Z).hom.f 0
      ((sectionComplex X (sheafHomComplex X L I).obj Z).iCycles 0
        (HomologicalComplex.cyclesMap (sectionComplexRes X (sheafHomComplex X L I).obj a) 0 z)) =
      Cochain.ofHom (restrictComplexHomAlong X L I a g) := by
    rw [hc]
    exact sectionsIso_sectionComplexRes_ofHom X L I a g _ hz
  have h1 := sheafHomSectionHomologyEquivDerivedCategoryHom_homologyπ_of_eq_ofHom X Z L I
    (restrictComplexHomAlong X L I a g) _ hz'
  have h2 : HomologicalComplex.homologyMap (sectionComplexRes X (sheafHomComplex X L I).obj a) 0
      ((sectionComplex X (sheafHomComplex X L I).obj U).homologyπ 0 z) =
      (sectionComplex X (sheafHomComplex X L I).obj Z).homologyπ 0
        (HomologicalComplex.cyclesMap (sectionComplexRes X (sheafHomComplex X L I).obj a) 0 z) := by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
      ConcreteCategory.comp_apply]
  rw [hcz, h2, h1, ← hcz, ← hg, restrictComplexDerivedMapAlong_Q_map]

section Gluing

variable [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [∀ U : X.C, PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [∀ U : X.C, PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [I.IsKInjective] [(sheafHomComplex X L I).obj.IsKInjective]

/-- **Gluing morphisms of `D(𝒪)` when the internal Hom is in `D^{≥ 0}`.** If `SheafHom(L, I)` is
K-injective and lies in `D^{≥ 0}`, a family of morphisms `L|_{Y i} ⟶ I|_{Y i}` over a family
covering the site, whose restrictions to every object mapping to two members agree, is the family
of restrictions of a unique morphism `L ⟶ I` of `D(𝒪)`. -/
theorem existsUnique_restrictComplexDerivedMap_eq_of_along
    (hM : (DerivedCategory.Q.obj (sheafHomComplex X L I).obj).IsGE 0)
    {ι : Type*} {Y : ι → X.C} (hY : X.J.CoversTop Y)
    (α : ∀ i, DerivedCategory.Q.obj (restrictComplex X L (Y i)) ⟶
      DerivedCategory.Q.obj (restrictComplex X I (Y i)))
    (hα : ∀ (Z : X.C) (i j : ι) (a : Z ⟶ Y i) (b : Z ⟶ Y j),
      restrictComplexDerivedMapAlong X L I a (α i) =
        restrictComplexDerivedMapAlong X L I b (α j)) :
    ∃! d : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj I,
      ∀ i, restrictComplexDerivedMap X (Y i) d = α i :=
  existsUnique_restrictComplexDerivedMap_eq X L I hM hY α fun Z i j a b => by
    apply (sheafHomSectionHomologyEquivDerivedCategoryHom X L I Z).injective
    rw [sheafHomSectionHomologyEquivDerivedCategoryHom_sectionComplexRes,
      sheafHomSectionHomologyEquivDerivedCategoryHom_sectionComplexRes,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hα Z i j a b]

end Gluing

section DerivedObjects

variable [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- If `R𝓗om(K, L)` is in `D^{≥ 0}`, so is the internal Hom complex between the K-flat model of
`K` and the K-injective model of `L`. -/
theorem isGE_sheafHomComplex_kFlatModel_kInjectiveModel
    {K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hKL : (((derivedSheafHomBifunctor X).obj (op K)).obj L).IsGE 0) :
    (DerivedCategory.Q.obj
      (sheafHomComplex X (kFlatModel X K) (kInjectiveModel X L)).obj).IsGE 0 := by
  have : (sheafHomComplex X (kFlatModel X K) (kInjectiveModel X L)).obj.IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X _ _ (isKFlat_kFlatModel X K)
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((((derivedSheafHomBifunctor X).obj (op K)).mapIso (kInjectiveModelIso X L).symm ≪≫
      ((derivedSheafHomBifunctor X).mapIso
        (asIso (DerivedCategory.Q.map (kFlatModelMap X K)) ≪≫ kInjectiveModelIso X K).op).app
        (DerivedCategory.Q.obj (kInjectiveModel X L))) ≪≫
      derivedSheafHomComparison X _ _) 0

omit [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Morphisms of `D(𝒪)` are determined locally when `R𝓗om(K, L)` is in `D^{≥ 0}`.** Two
morphisms `K ⟶ L` with the same restrictions to the members of a family covering the site are
equal (compare Stacks 0D66 for ringed spaces). -/
theorem eq_of_mapDerivedCategory_overFunctor_map_eq
    [∀ U : X.C, PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    [∀ U : X.C, PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    {K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hKL : (((derivedSheafHomBifunctor X).obj (op K)).obj L).IsGE 0)
    {ι : Type*} {Y : ι → X.C} (hY : X.J.CoversTop Y) {d d' : K ⟶ L}
    (h : ∀ i, (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (Y i)).mapDerivedCategory.map d =
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (Y i)).mapDerivedCategory.map d') :
    d = d' := by
  let P := kFlatModel X K
  let I := kInjectiveModel X L
  have : (sheafHomComplex X P I).obj.IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X P I (isKFlat_kFlatModel X K)
  let eP : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map (kFlatModelMap X K)) ≪≫ kInjectiveModelIso X K
  let eI : DerivedCategory.Q.obj I ≅ L := kInjectiveModelIso X L
  have hM : (DerivedCategory.Q.obj (sheafHomComplex X P I).obj).IsGE 0 :=
    isGE_sheafHomComplex_kFlatModel_kInjectiveModel X hKL
  have key : eP.hom ≫ d ≫ eI.inv = eP.hom ≫ d' ≫ eI.inv :=
    eq_of_restrictComplexDerivedMap_eq X P I hM hY fun i => by
      dsimp only [restrictComplexDerivedMap]
      rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, h i]
  simpa using key

omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- The restriction of a morphism of `D(𝒪)` to the slice at `U` is the restriction functor on
that morphism, read through the canonical factorization. -/
theorem restrictComplexDerivedMap_eq_restrictQMap
    [∀ U : X.C, PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    [∀ U : X.C, PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    (U : X.C)
    {P I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (d : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I) :
    restrictComplexDerivedMap X U d =
      Stacks.DerivedCategoryComparisons.restrictQMap
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) d := rfl

omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- Restricting the inverse and then the forward map of an isomorphism of `D(𝒪)` gives the
identity. -/
theorem restrictComplexDerivedMap_inv_hom
    [∀ U : X.C, PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    [∀ U : X.C, PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    (U : X.C)
    {K K' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj K') :
    restrictComplexDerivedMap X U e.inv ≫ restrictComplexDerivedMap X U e.hom = 𝟙 _ := by
  rw [restrictComplexDerivedMap_eq_restrictQMap, restrictComplexDerivedMap_eq_restrictQMap,
    ← Stacks.DerivedCategoryComparisons.restrictQMap_comp, e.inv_hom_id,
    Stacks.DerivedCategoryComparisons.restrictQMap_id]

omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- The restriction along `a : Z ⟶ U` of a morphism of `D(𝒪_U)` is its transport along the
comparison `SheafOfModules.overFunctorMap` of the two restrictions. -/
theorem restrictComplexDerivedMapAlong_eq_transportQMap {U Z : X.C} (a : Z ⟶ U)
    (ψ : DerivedCategory.Q.obj (restrictComplex X L U) ⟶
      DerivedCategory.Q.obj (restrictComplex X I U)) :
    restrictComplexDerivedMapAlong X L I a ψ =
      letI := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a
      letI := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a
      Stacks.DerivedCategoryComparisons.transportQMap
        (SheafOfModules.overFunctorMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a) ψ := by
  simp only [restrictComplexDerivedMapAlong, restrictComplexOverMapIso,
    Stacks.DerivedCategoryComparisons.transportQMap,
    Stacks.DerivedCategoryComparisons.restrictQMap, Iso.trans_inv, Iso.trans_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom, Category.assoc]
  rfl

omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- Restriction along `a` of a restricted morphism is the restriction to the smaller object. -/
theorem restrictComplexDerivedMapAlong_restrictComplexDerivedMap
    [∀ U : X.C, PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    [∀ U : X.C, PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    {U Z : X.C} (a : Z ⟶ U) (d : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj I) :
    restrictComplexDerivedMapAlong X L I a (restrictComplexDerivedMap X U d) =
      restrictComplexDerivedMap X Z d := by
  let := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a
  let := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a
  rw [restrictComplexDerivedMapAlong_eq_transportQMap, restrictComplexDerivedMap_eq_restrictQMap,
    restrictComplexDerivedMap_eq_restrictQMap]
  exact Stacks.DerivedCategoryComparisons.transportQMap_restrictQMap _ d

omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- Restriction along `a` is compatible with composition. -/
theorem restrictComplexDerivedMapAlong_comp
    {J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {U Z : X.C} (a : Z ⟶ U)
    (ψ : DerivedCategory.Q.obj (restrictComplex X L U) ⟶
      DerivedCategory.Q.obj (restrictComplex X I U))
    (ψ' : DerivedCategory.Q.obj (restrictComplex X I U) ⟶
      DerivedCategory.Q.obj (restrictComplex X J U)) :
    restrictComplexDerivedMapAlong X L J a (ψ ≫ ψ') =
      restrictComplexDerivedMapAlong X L I a ψ ≫ restrictComplexDerivedMapAlong X I J a ψ' := by
  let := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a
  let := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a
  rw [restrictComplexDerivedMapAlong_eq_transportQMap,
    restrictComplexDerivedMapAlong_eq_transportQMap,
    restrictComplexDerivedMapAlong_eq_transportQMap]
  exact Stacks.DerivedCategoryComparisons.transportQMap_comp _ ψ ψ'

omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- Restriction along a composite `g ≫ a` is restriction along `a` followed by restriction
along `g`. -/
theorem restrictComplexDerivedMapAlong_comp_hom {U Z W : X.C} (a : Z ⟶ U) (g : W ⟶ Z)
    (ψ : DerivedCategory.Q.obj (restrictComplex X L U) ⟶
      DerivedCategory.Q.obj (restrictComplex X I U)) :
    restrictComplexDerivedMapAlong X L I (g ≫ a) ψ =
      restrictComplexDerivedMapAlong X L I g (restrictComplexDerivedMapAlong X L I a ψ) := by
  let := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a
  let := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a
  let := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) g
  let := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) g
  let := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (g ≫ a)
  let := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (g ≫ a)
  rw [restrictComplexDerivedMapAlong_eq_transportQMap,
    restrictComplexDerivedMapAlong_eq_transportQMap,
    restrictComplexDerivedMapAlong_eq_transportQMap,
    Stacks.DerivedCategoryComparisons.transportQMap_transportQMap,
    ← Stacks.DerivedCategoryComparisons.transportQMap_isoWhiskerLeft
      (CategoryTheory.SiteGlueing.overMapComp (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a g)]
  congr 1
  exact overFunctorMap_comp_hom_eq (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a g

/-- **Gluing morphisms of `D(𝒪)` when `R𝓗om(P, I)` is in `D^{≥ 0}`**, for arbitrary complexes `P`
and `I`: a family of morphisms `P|_{Y i} ⟶ I|_{Y i}` over a family covering the site, whose
restrictions to every object mapping to two members agree, is the family of restrictions of a
unique morphism `P ⟶ I` of `D(𝒪)` (compare Stacks 0D66 for ringed spaces). -/
theorem existsUnique_restrictComplexDerivedMap_eq_of_isGE
    [∀ U : X.C, PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    [∀ U : X.C, PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    (hLI : (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj L))).obj
      (DerivedCategory.Q.obj I)).IsGE 0)
    {ι : Type*} {Y : ι → X.C} (hY : X.J.CoversTop Y)
    (α : ∀ i, DerivedCategory.Q.obj (restrictComplex X L (Y i)) ⟶
      DerivedCategory.Q.obj (restrictComplex X I (Y i)))
    (hα : ∀ (Z : X.C) (i j : ι) (a : Z ⟶ Y i) (b : Z ⟶ Y j),
      restrictComplexDerivedMapAlong X L I a (α i) =
        restrictComplexDerivedMapAlong X L I b (α j)) :
    ∃! d : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj I,
      ∀ i, restrictComplexDerivedMap X (Y i) d = α i := by
  let P := kFlatModel X (DerivedCategory.Q.obj L)
  let J := kInjectiveModel X (DerivedCategory.Q.obj I)
  have : (sheafHomComplex X P J).obj.IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X P J (isKFlat_kFlatModel X _)
  let eP : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj L :=
    asIso (DerivedCategory.Q.map (kFlatModelMap X _)) ≪≫ kInjectiveModelIso X _
  let eI : DerivedCategory.Q.obj J ≅ DerivedCategory.Q.obj I := kInjectiveModelIso X _
  have hM : (DerivedCategory.Q.obj (sheafHomComplex X P J).obj).IsGE 0 :=
    isGE_sheafHomComplex_kFlatModel_kInjectiveModel X hLI
  let α' : ∀ i, DerivedCategory.Q.obj (restrictComplex X P (Y i)) ⟶
      DerivedCategory.Q.obj (restrictComplex X J (Y i)) := fun i =>
    restrictComplexDerivedMap X (Y i) eP.hom ≫ α i ≫ restrictComplexDerivedMap X (Y i) eI.inv
  have hα' : ∀ (Z : X.C) (i j : ι) (a : Z ⟶ Y i) (b : Z ⟶ Y j),
      restrictComplexDerivedMapAlong X P J a (α' i) =
        restrictComplexDerivedMapAlong X P J b (α' j) := fun Z i j a b => by
    simp only [α', restrictComplexDerivedMapAlong_comp,
      restrictComplexDerivedMapAlong_restrictComplexDerivedMap, hα Z i j a b]
  obtain ⟨d', hd', huniq⟩ :=
    existsUnique_restrictComplexDerivedMap_eq_of_along X P J hM hY α' hα'
  refine ⟨eP.inv ≫ d' ≫ eI.hom, fun i => ?_, fun d hd => ?_⟩
  · rw [restrictComplexDerivedMap_comp, restrictComplexDerivedMap_comp, hd' i]
    simp only [α', Category.assoc, restrictComplexDerivedMap_inv_hom, Category.comp_id]
    rw [← Category.assoc, restrictComplexDerivedMap_inv_hom, Category.id_comp]
  · have h := huniq (eP.hom ≫ d ≫ eI.inv) fun i => by
      rw [restrictComplexDerivedMap_comp, restrictComplexDerivedMap_comp, hd i]
    rw [← h]
    simp

end DerivedObjects

end AlgebraicGeometry.RingedSite

end
