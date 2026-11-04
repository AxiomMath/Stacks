module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomGluing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOverAnObjectNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplexGlobalValue
public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionResolution

/-!
# Restricting a global class of the internal Hom complex to an object of the site

Let `(C, 𝒪)` be a ringed site, `L` a complex and `I` a K-injective complex of `𝒪`-modules. By
Stacks 0A94 the degree-zero classes of global sections of `SheafHom(L, I)` are the morphisms
`L ⟶ I` of `D(𝒪)`, and those of sections over `U` are the morphisms `L|_U ⟶ I|_U` of `D(𝒪_U)`.
This file shows that restricting a class from `C` to `U` corresponds to restricting the morphism.

## Main results

* `RingedSite.sectionsIso_globalHomSection_val`: the section over `U` of the global section
  attached to `f : L ⟶ I` is the cochain of `f|_U`.
* `RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom_homologyπ_of_eq_ofHom`: Stacks 0A94
  over `U` at the class of a cocycle.
* `RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom_globalSectionsComplexProj`: the
  restriction of a global class corresponds to the restriction of the morphism.
* `RingedSite.eq_of_restrictComplexDerivedMap_eq` and
  `RingedSite.existsUnique_restrictComplexDerivedMap_eq`: when `SheafHom(L, I)` is K-injective and
  in `D^{≥ 0}`, morphisms `L ⟶ I` of `D(𝒪)` are determined by, and glue from, their restrictions
  to a covering family (compare Stacks 0D66 for ringed spaces).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The section over `U` of the global section attached to `f` is the cochain of `f|_U`.** -/
theorem sectionsIso_globalHomSection_val (f : L ⟶ I) :
    ((sheafHomComplex X L I).sectionsIso U).hom.f 0 ((globalHomSection X L I f).val (op U)) =
      Cochain.ofHom (restrictComplexMap X U f) := by
  refine Cochain.ext₀ _ _ fun p => ?_
  refine SheafOfModules.hom_ext ?_
  ext ⟨W⟩ x
  have h₁ := (sheafHomComplex X L I).restrict_natural W.hom 0 p p (add_zero p)
    ((globalHomSection X L I f).val (op U)) (𝟙 W.left) x
  have h₂ : ((sheafHomComplex X L I).obj.X 0).val.map W.hom.op
      ((globalHomSection X L I f).val (op U)) = (globalHomSection X L I f).val (op W.left) :=
    (globalHomSection X L I f).property W.hom.op
  rw [Category.id_comp, h₂] at h₁
  have h₃ := sheafHomComplex_globalSectionsIso_v_app X L I 0 p p (add_zero p)
    (globalHomSection X L I f) W.left x
  rw [globalSectionsIso_globalHomSection] at h₃
  refine h₁.trans (h₃.symm.trans ?_)
  simp only [Cochain.ofHom_v]
  rfl

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Stacks 0A94 over an object at the class of a cocycle.** The class of a degree-zero cycle of
the sections over `U` of `SheafHom(L, I)` whose cochain is `Cochain.ofHom g` corresponds to
`Q(g)`. -/
theorem sheafHomSectionHomologyEquivDerivedCategoryHom_homologyπ_of_eq_ofHom [I.IsKInjective]
    (g : restrictComplex X L U ⟶ restrictComplex X I U)
    (z : (sectionComplex X (sheafHomComplex X L I).obj U).cycles 0)
    (hz : ((sheafHomComplex X L I).sectionsIso U).hom.f 0
        ((sectionComplex X (sheafHomComplex X L I).obj U).iCycles 0 z) = Cochain.ofHom g) :
    sheafHomSectionHomologyEquivDerivedCategoryHom X L I U
        ((sectionComplex X (sheafHomComplex X L I).obj U).homologyπ 0 z) =
      DerivedCategory.Q.map g := by
  have : (restrictComplex X I U).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U I
  let φ := (sheafHomComplex X L I).sectionsIso U
  let K := restrictComplex X L U
  let M := restrictComplex X I U
  let w := HomologicalComplex.cyclesMap φ.hom 0 z
  have h1 : HomologicalComplex.homologyMap φ.hom 0
      ((sectionComplex X (sheafHomComplex X L I).obj U).homologyπ 0 z) =
      (K.HomComplex M).homologyπ 0 w :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality φ.hom 0) z
  have hi : (K.HomComplex M).iCycles 0 w = Cochain.ofHom g :=
    (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ.hom 0) z).trans hz
  have h5 : homologyAddEquiv K M 0 (((K.HomComplex M).sc 0).homologyπ w) =
      CohomologyClass.mk ((leftHomologyData K M 0).cyclesIso.hom w) :=
    ConcreteCategory.congr_hom
      (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom ((K.HomComplex M).sc 0)
        (leftHomologyData K M 0)) w
  have h6 : ((leftHomologyData K M 0).cyclesIso.hom w).1 = Cochain.ofHom g :=
    (ConcreteCategory.congr_hom (leftHomologyData K M 0).cyclesIso_hom_comp_i w).trans hi
  have hcl : homologyAddEquiv K M 0 (HomologicalComplex.homologyMap φ.hom 0
      ((sectionComplex X (sheafHomComplex X L I).obj U).homologyπ 0 z)) =
      CohomologyClass.mk (Cocycle.ofHom g) := by
    rw [h1]
    exact h5.trans (congrArg CohomologyClass.mk (Subtype.ext h6))
  rw [sheafHomSectionHomologyEquivDerivedCategoryHom_apply X L I U _,
    sheafHomSectionHomotopyCategoryHom_eq, hcl, Category.id_comp, Iso.app_hom,
    homAddEquiv_mk_ofHom_comp_shiftFunctorZero, homotopyHomDerivedCategoryEquiv_quotient_map]

section Restriction

variable
  [PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]

/-- **Restricting a global class corresponds to restricting the morphism.** Under Stacks 0A94,
globally and over `U`, the restriction to `U` of a degree-zero class of global sections of
`SheafHom(L, I)` is the restriction to `C/U` of the corresponding morphism `L ⟶ I` of `D(𝒪)`. -/
theorem sheafHomSectionHomologyEquivDerivedCategoryHom_globalSectionsComplexProj
    [I.IsKInjective] (c : (globalSectionsComplex X (sheafHomComplex X L I).obj).homology 0) :
    sheafHomSectionHomologyEquivDerivedCategoryHom X L I U
        (HomologicalComplex.homologyMap
          (globalSectionsComplexProj X (sheafHomComplex X L I).obj U) 0 c) =
      restrictComplexDerivedMap X U (sheafHomGlobalHomologyEquivDerivedCategoryHom X L I c) := by
  obtain ⟨f, hf⟩ := StacksDraft.DerivedHom.exists_eq_Q_map_of_isKInjective L I
    (sheafHomGlobalHomologyEquivDerivedCategoryHom X L I c)
  obtain rfl : c = globalHomologyClass X L I f := by
    rw [← symm_sheafHomGlobalHomologyEquivDerivedCategoryHom_Q_map, hf, AddEquiv.symm_apply_apply]
  rw [sheafHomGlobalHomologyEquivDerivedCategoryHom_globalHomologyClass,
    restrictComplexDerivedMap_Q_map, globalHomologyClass, ← ConcreteCategory.comp_apply,
    HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply]
  refine sheafHomSectionHomologyEquivDerivedCategoryHom_homologyπ_of_eq_ofHom X U L I _ _ ?_
  have hc := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (globalSectionsComplexProj X (sheafHomComplex X L I).obj U) 0) (globalHomCocycle X L I f)
  simp only [ConcreteCategory.comp_apply] at hc
  rw [hc, iCycles_globalHomCocycle]
  exact sectionsIso_globalHomSection_val X U L I f

end Restriction

omit U [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Restricting the value of a global section along `a : Z ⟶ U` gives its value at `Z`. -/
theorem globalSectionsComplexProj_comp_sectionComplexRes
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {U Z : X.C} (a : Z ⟶ U) :
    globalSectionsComplexProj X M U ≫ sectionComplexRes X M a =
      globalSectionsComplexProj X M Z := by
  ext n s
  exact s.property a.op

section Gluing

variable [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [∀ U : X.C, PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [∀ U : X.C, PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [I.IsKInjective] [(sheafHomComplex X L I).obj.IsKInjective]

omit U in
/-- **Morphisms of `D(𝒪)` are determined locally when the internal Hom is in `D^{≥ 0}`.** If
`SheafHom(L, I)` is K-injective and lies in `D^{≥ 0}`, two morphisms `L ⟶ I` of `D(𝒪)` with the
same restrictions to the members of a family covering the site are equal. -/
theorem eq_of_restrictComplexDerivedMap_eq
    (hM : (DerivedCategory.Q.obj (sheafHomComplex X L I).obj).IsGE 0)
    {ι : Type*} {Y : ι → X.C} (hY : X.J.CoversTop Y)
    {d d' : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj I}
    (h : ∀ i, restrictComplexDerivedMap X (Y i) d = restrictComplexDerivedMap X (Y i) d') :
    d = d' := by
  let e := sheafHomGlobalHomologyEquivDerivedCategoryHom X L I
  obtain ⟨c, -, hc⟩ := existsUnique_globalSectionsComplexProj_of_isKInjective X
    (sheafHomComplex X L I).obj hM hY
    (fun i => HomologicalComplex.homologyMap
      (globalSectionsComplexProj X (sheafHomComplex X L I).obj (Y i)) 0 (e.symm d))
    (fun Z i j a b => by
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        globalSectionsComplexProj_comp_sectionComplexRes,
        globalSectionsComplexProj_comp_sectionComplexRes])
  have h1 := hc (e.symm d) (fun _ => rfl)
  have h2 := hc (e.symm d') (fun i => by
    apply (sheafHomSectionHomologyEquivDerivedCategoryHom X L I (Y i)).injective
    rw [sheafHomSectionHomologyEquivDerivedCategoryHom_globalSectionsComplexProj,
      sheafHomSectionHomologyEquivDerivedCategoryHom_globalSectionsComplexProj,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, h i])
  exact e.symm.injective (h1.trans h2.symm)

omit U in
/-- **Gluing morphisms of `D(𝒪)` when the internal Hom is in `D^{≥ 0}`.** If `SheafHom(L, I)` is
K-injective and lies in `D^{≥ 0}`, a family of morphisms `L|_{Y i} ⟶ I|_{Y i}` over a family
covering the site, whose classes in `H^0(Γ(-, SheafHom(L, I)))` agree on every object mapping to
two members, is the family of restrictions of a unique morphism `L ⟶ I` of `D(𝒪)`. -/
theorem existsUnique_restrictComplexDerivedMap_eq
    (hM : (DerivedCategory.Q.obj (sheafHomComplex X L I).obj).IsGE 0)
    {ι : Type*} {Y : ι → X.C} (hY : X.J.CoversTop Y)
    (α : ∀ i, DerivedCategory.Q.obj (restrictComplex X L (Y i)) ⟶
      DerivedCategory.Q.obj (restrictComplex X I (Y i)))
    (hα : ∀ (Z : X.C) (i j : ι) (a : Z ⟶ Y i) (b : Z ⟶ Y j),
      HomologicalComplex.homologyMap (sectionComplexRes X (sheafHomComplex X L I).obj a) 0
          ((sheafHomSectionHomologyEquivDerivedCategoryHom X L I (Y i)).symm (α i)) =
        HomologicalComplex.homologyMap (sectionComplexRes X (sheafHomComplex X L I).obj b) 0
          ((sheafHomSectionHomologyEquivDerivedCategoryHom X L I (Y j)).symm (α j))) :
    ∃! d : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj I,
      ∀ i, restrictComplexDerivedMap X (Y i) d = α i := by
  obtain ⟨c, hc, -⟩ := existsUnique_globalSectionsComplexProj_of_isKInjective X
    (sheafHomComplex X L I).obj hM hY _ hα
  refine ⟨sheafHomGlobalHomologyEquivDerivedCategoryHom X L I c, fun i => ?_,
    fun d hd => eq_of_restrictComplexDerivedMap_eq X L I hM hY fun i => ?_⟩
  · rw [← sheafHomSectionHomologyEquivDerivedCategoryHom_globalSectionsComplexProj, hc i,
      AddEquiv.apply_symm_apply]
  · rw [hd i, ← sheafHomSectionHomologyEquivDerivedCategoryHom_globalSectionsComplexProj, hc i,
      AddEquiv.apply_symm_apply]

end Gluing

end AlgebraicGeometry.RingedSite

end
