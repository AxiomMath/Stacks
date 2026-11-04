module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
public import StacksFrontier.Homology.Injectives.KInjective.RealizeDerivedIso

/-!
# Sections of a K-injective complex which is acyclic in negative degrees

Let `(C, 𝒪)` be a ringed site and `M` a K-injective complex of `𝒪`-modules whose cohomology
sheaves vanish in negative degrees. Then the cohomology presheaves `U ↦ H^i(Γ(U, M))` of the
underlying complex of presheaves vanish for `i < 0`, and `U ↦ H^0(Γ(U, M))` is a sheaf.

Applied to the internal Hom complex `SheafHom(A, I)` of a K-flat `A` into a K-injective `I`,
whose sections over `U` compute `Hom_{D(𝒪_U)}(A|_U, I|_U)` (Stacks 0A94), this is the gluing
principle for morphisms of the derived category: when `R𝓗om(K, L)` lies in `D^{≥ 0}`, the rule
`U ↦ Hom(K|_U, L|_U)` is a sheaf (compare Stacks 0D66 for ringed spaces).

## Main results

* `CochainComplex.exists_homotopyEquiv_isStrictlyGE_of_isKInjective`: a K-injective complex
  which is `≥ n` in the derived category is homotopy equivalent to a complex vanishing in
  degrees `< n`.
* `AlgebraicGeometry.RingedSite.isZero_homology_presheafComplex_of_isKInjective`: the negative
  cohomology presheaves vanish.
* `AlgebraicGeometry.RingedSite.isSheaf_homology_presheafComplex_of_isKInjective`: the
  degree-zero cohomology presheaf is a sheaf.
* `AlgebraicGeometry.RingedSite.existsUnique_globalSectionsComplexProj_of_isKInjective`: over a
  family of objects covering the site, compatible classes in `H^0(Γ(Y i, M))` come from a unique
  class in `H^0(Γ(C, M))`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A] [EnoughInjectives A]

/-- **A K-injective complex which is `≥ n` in the derived category is homotopy equivalent to a
complex vanishing in degrees `< n`**: an injective resolution, vanishing below `n`, of a complex
representing it (Stacks 013K) is K-injective, and a quasi-isomorphism between K-injective
complexes is a homotopy equivalence. -/
theorem exists_homotopyEquiv_isStrictlyGE_of_isKInjective (M : CochainComplex A ℤ)
    [M.IsKInjective] (n : ℤ) (hM : (DerivedCategory.Q.obj M).IsGE n) :
    ∃ (J : CochainComplex A ℤ), J.IsStrictlyGE n ∧ Nonempty (HomotopyEquiv M J) := by
  obtain ⟨K, e, hK⟩ := hM
  obtain ⟨R, -, hR⟩ := exists_injectiveResolution_isStrictlyGE n K
  have : R.cocomplex.IsStrictlyGE n := hR
  have : R.cocomplex.IsKInjective := isKInjective_of_injective R.cocomplex n
  have : QuasiIso R.ι := R.quasiIso
  let e' : DerivedCategory.Q.obj M ≅ DerivedCategory.Q.obj R.cocomplex :=
    e ≪≫ asIso (DerivedCategory.Q.map R.ι)
  obtain ⟨φ, hφ, -⟩ := exists_quasiIso_of_isKInjective_of_iso M R.cocomplex e'
  obtain ⟨h, -⟩ := (IsKInjective.quasiIso_iff φ).1 hφ
  exact ⟨R.cocomplex, hR, ⟨h⟩⟩

end CochainComplex

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The complex of presheaves of abelian groups underlying a complex of `𝒪`-modules: its
cohomology at `U` is the cohomology of the sections over `U`. -/
abbrev presheafComplex
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    CochainComplex (X.Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ :=
  ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
    sheafToPresheaf X.J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj M

variable [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- The cohomology presheaves of a complex vanishing in degrees `< 0` vanish in degrees `< 0`. -/
theorem isZero_homology_presheafComplex_of_isStrictlyGE
    (J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsStrictlyGE 0] (i : ℤ) (hi : i < 0) : IsZero ((presheafComplex X J).homology i) :=
  (HomologicalComplex.ExactAt.of_isZero
    (Functor.map_isZero (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
      sheafToPresheaf X.J AddCommGrpCat.{u}) (J.isZero_of_isStrictlyGE 0 i hi))).isZero_homology

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- The degree-zero cohomology presheaf of a complex vanishing in degrees `< 0` is the kernel of
the first differential, a sheaf. -/
theorem isSheaf_homology_presheafComplex_of_isStrictlyGE
    (J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsStrictlyGE 0] :
    Presheaf.IsSheaf X.J ((presheafComplex X J).homology 0) := by
  have hz : (presheafComplex X J).d (-1) 0 = 0 :=
    (Functor.map_isZero (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
      sheafToPresheaf X.J AddCommGrpCat.{u})
        (J.isZero_of_isStrictlyGE 0 (-1) (by omega))).eq_of_src _ _
  refine (Presheaf.isSheaf_of_iso_iff
    ((presheafComplex X J).isoHomologyπ (-1) 0 (by simp) hz)).1 ?_
  refine ObjectProperty.prop_of_isLimit (P := Presheaf.IsSheaf X.J (A := AddCommGrpCat.{u}))
    ((presheafComplex X J).cyclesIsKernel 0 1 (by simp)) ?_
  rintro (_ | _)
  · exact ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj (J.X 0)).cond
  · exact ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj (J.X 1)).cond

/-- **The negative cohomology presheaves of a K-injective complex acyclic in negative degrees
vanish**: `H^i(Γ(U, M)) = 0` for `i < 0` and every `U`. -/
theorem isZero_homology_presheafComplex_of_isKInjective
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [M.IsKInjective]
    (hM : (DerivedCategory.Q.obj M).IsGE 0) (i : ℤ) (hi : i < 0) :
    IsZero ((presheafComplex X M).homology i) := by
  obtain ⟨J, hJ, ⟨h⟩⟩ := CochainComplex.exists_homotopyEquiv_isStrictlyGE_of_isKInjective M 0 hM
  exact (isZero_homology_presheafComplex_of_isStrictlyGE X J i hi).of_iso
    (((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
      sheafToPresheaf X.J AddCommGrpCat.{u}).mapHomotopyEquiv h).toHomologyIso i)

/-- **The degree-zero cohomology presheaf of a K-injective complex acyclic in negative degrees is
a sheaf**: `U ↦ H^0(Γ(U, M))`. -/
theorem isSheaf_homology_presheafComplex_of_isKInjective
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [M.IsKInjective]
    (hM : (DerivedCategory.Q.obj M).IsGE 0) :
    Presheaf.IsSheaf X.J ((presheafComplex X M).homology 0) := by
  obtain ⟨J, hJ, ⟨h⟩⟩ := CochainComplex.exists_homotopyEquiv_isStrictlyGE_of_isKInjective M 0 hM
  exact (Presheaf.isSheaf_of_iso_iff
    (((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
      sheafToPresheaf X.J AddCommGrpCat.{u}).mapHomotopyEquiv h).toHomologyIso 0)).2
    (isSheaf_homology_presheafComplex_of_isStrictlyGE X J)

/-- A sheaf of abelian groups has an underlying sheaf of types. -/
private lemma isSheaf_forget_of_isSheaf {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (hF : Presheaf.IsSheaf J F) :
    Presheaf.IsSheaf J (F ⋙ CategoryTheory.forget AddCommGrpCat.{u}) :=
  (Presheaf.isSheaf_iff_isSheaf_forget J F (CategoryTheory.forget AddCommGrpCat.{u})).1 hF

/-- **Gluing sections of the degree-zero cohomology of a K-injective complex acyclic in negative
degrees.** Over a family of objects covering the site, a compatible family of classes in
`H^0(Γ(Y i, M))` comes from a unique compatible family over all objects. -/
theorem existsUnique_section_homology_presheafComplex_of_isKInjective
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [M.IsKInjective]
    (hM : (DerivedCategory.Q.obj M).IsGE 0) {ι : Type*} {Y : ι → X.C} (hY : X.J.CoversTop Y)
    {x : Presheaf.FamilyOfElementsOnObjects
      ((presheafComplex X M).homology 0 ⋙ CategoryTheory.forget AddCommGrpCat.{u}) Y}
    (hx : x.IsCompatible) :
    ∃! s : ((presheafComplex X M).homology 0 ⋙ CategoryTheory.forget AddCommGrpCat.{u}).sections,
      ∀ i, s.1 (op (Y i)) = x i :=
  hx.existsUnique_section hY
    (isSheaf_forget_of_isSheaf (isSheaf_homology_presheafComplex_of_isKInjective X M hM))

section GlobalGluing

/-- Evaluation of a global section of a sheaf of abelian groups at an object of the site. -/
def globalSectionsProj (U : X.C) :
    abelianGlobalSectionsFunctor.{u} X ⟶
      sheafToPresheaf X.J AddCommGrpCat.{u} ⋙ (evaluation X.Cᵒᵖ AddCommGrpCat.{u}).obj (op U) where
  app _ := AddCommGrpCat.ofHom
    { toFun := fun s => s.val (op U)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality _ _ _ := rfl

/-- The map from the global sections of a complex of `𝒪`-modules to its sections over `U`. -/
abbrev globalSectionsComplexProj
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) : globalSectionsComplex X M ⟶ sectionComplex X M U :=
  (NatTrans.mapHomologicalComplex (globalSectionsProj X U) (ComplexShape.up ℤ)).app
    (underlyingComplex X M)

/-- Restriction of the sections of a complex of `𝒪`-modules along a morphism of the site. -/
abbrev sectionComplexRes
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {U V : X.C} (f : V ⟶ U) : sectionComplex X M U ⟶ sectionComplex X M V :=
  (NatTrans.mapHomologicalComplex (Functor.whiskerLeft (sheafToPresheaf X.J AddCommGrpCat.{u})
    ((evaluation X.Cᵒᵖ AddCommGrpCat.{u}).map f.op)) (ComplexShape.up ℤ)).app
      (underlyingComplex X M)

/-- On a complex of abelian groups vanishing in degree `-1`, a degree-zero class is determined by
its cocycle. -/
private def classCocycle (K : CochainComplex AddCommGrpCat.{u} ℤ) (hK : IsZero (K.X (-1))) :
    K.homology 0 ⟶ K.X 0 :=
  (K.isoHomologyπ (-1) 0 (by simp) (hK.eq_of_src _ _)).inv ≫ K.iCycles 0

private lemma classCocycle_injective (K : CochainComplex AddCommGrpCat.{u} ℤ)
    (hK : IsZero (K.X (-1))) : Function.Injective (classCocycle K hK) := by
  rw [← AddCommGrpCat.mono_iff_injective]
  dsimp only [classCocycle]
  infer_instance

private lemma homologyπ_classCocycle (K : CochainComplex AddCommGrpCat.{u} ℤ)
    (hK : IsZero (K.X (-1))) : K.homologyπ 0 ≫ classCocycle K hK = K.iCycles 0 := by
  have h : K.homologyπ 0 = (K.isoHomologyπ (-1) 0 (by simp) (hK.eq_of_src _ _)).hom := rfl
  simp only [classCocycle, h, Iso.hom_inv_id_assoc]

private lemma exists_classCocycle_eq (K : CochainComplex AddCommGrpCat.{u} ℤ)
    (hK : IsZero (K.X (-1))) (y : K.X 0) (hy : K.d 0 1 y = 0) :
    ∃ c, classCocycle K hK c = y := by
  let k : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ K.X 0 :=
    AddCommGrpCat.ofHom ((zmultiplesHom _ y).comp AddEquiv.ulift.toAddMonoidHom)
  have hk : k ≫ K.d 0 1 = 0 := by
    ext
    simp [k, hy]
  refine ⟨K.homologyπ 0 (K.liftCycles k 1 (by simp) hk ⟨1⟩), ?_⟩
  rw [← ConcreteCategory.comp_apply, homologyπ_classCocycle, ← ConcreteCategory.comp_apply,
    HomologicalComplex.liftCycles_i]
  exact one_zsmul y

private lemma classCocycle_naturality {K L : CochainComplex AddCommGrpCat.{u} ℤ}
    (hK : IsZero (K.X (-1))) (hL : IsZero (L.X (-1))) (f : K ⟶ L) :
    HomologicalComplex.homologyMap f 0 ≫ classCocycle L hL = classCocycle K hK ≫ f.f 0 := by
  rw [← cancel_epi (K.homologyπ 0), HomologicalComplex.homologyπ_naturality_assoc,
    homologyπ_classCocycle, HomologicalComplex.cyclesMap_i, ← Category.assoc,
    homologyπ_classCocycle]

private lemma classCocycle_congr {K K' L : CochainComplex AddCommGrpCat.{u} ℤ}
    (hK : IsZero (K.X (-1))) (hK' : IsZero (K'.X (-1))) (hL : IsZero (L.X (-1)))
    {f : K ⟶ L} {f' : K' ⟶ L} {c : K.homology 0} {c' : K'.homology 0}
    (h : HomologicalComplex.homologyMap f 0 c = HomologicalComplex.homologyMap f' 0 c') :
    f.f 0 (classCocycle K hK c) = f'.f 0 (classCocycle K' hK' c') := by
  simpa only [← ConcreteCategory.comp_apply, classCocycle_naturality hK hL f,
    classCocycle_naturality hK' hL f'] using congrArg (classCocycle L hL) h

variable {X} in
omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- A global section of a sheaf of abelian groups is determined by its values on a family of
objects covering the site. -/
lemma abelianGlobalSection_ext {F : Sheaf X.J AddCommGrpCat.{u}} {ι : Type*} {Y : ι → X.C}
    (hY : X.J.CoversTop Y) {s t : (abelianGlobalSectionsFunctor.{u} X).obj F}
    (h : ∀ i, s.val (op (Y i)) = t.val (op (Y i))) : s = t := by
  let G : Sheaf X.J (Type u) := ⟨F.val ⋙ CategoryTheory.forget AddCommGrpCat.{u},
    isSheaf_forget_of_isSheaf F.cond⟩
  have key : (⟨s.val, fun f => s.property f⟩ : G.val.sections) = ⟨t.val, fun f => t.property f⟩ :=
    hY.sections_ext G h
  exact Subtype.ext (congrArg Subtype.val key)

variable {X} in
omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- A compatible family of sections of a sheaf of abelian groups over a family of objects
covering the site comes from a global section. -/
lemma exists_abelianGlobalSection {F : Sheaf X.J AddCommGrpCat.{u}} {ι : Type*} {Y : ι → X.C}
    (hY : X.J.CoversTop Y) (y : ∀ i, F.val.obj (op (Y i)))
    (hy : ∀ (Z : X.C) (i j : ι) (a : Z ⟶ Y i) (b : Z ⟶ Y j),
      F.val.map a.op (y i) = F.val.map b.op (y j)) :
    ∃ s : (abelianGlobalSectionsFunctor.{u} X).obj F, ∀ i, s.val (op (Y i)) = y i := by
  obtain ⟨t, ht, -⟩ := Presheaf.FamilyOfElementsOnObjects.IsCompatible.existsUnique_section
    (F := F.val ⋙ CategoryTheory.forget AddCommGrpCat.{u}) (x := y) (fun Z i j a b => hy Z i j a b)
    hY (isSheaf_forget_of_isSheaf F.cond)
  exact ⟨⟨t.val, fun f => t.property f⟩, ht⟩

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
private lemma isZero_globalSectionsComplex_X
    (J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsStrictlyGE 0] : IsZero ((globalSectionsComplex X J).X (-1)) :=
  Functor.map_isZero (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
    abelianGlobalSectionsFunctor.{u} X) (J.isZero_of_isStrictlyGE 0 (-1) (by omega))

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
private lemma isZero_sectionComplex_X
    (J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsStrictlyGE 0] (U : X.C) : IsZero ((sectionComplex X J U).X (-1)) :=
  Functor.map_isZero (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
    sheafToPresheaf X.J AddCommGrpCat.{u} ⋙ (evaluation X.Cᵒᵖ AddCommGrpCat.{u}).obj (op U))
    (J.isZero_of_isStrictlyGE 0 (-1) (by omega))

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
private lemma globalSectionsComplexProj_injective_of_isStrictlyGE
    (J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsStrictlyGE 0]
    {ι : Type*} {Y : ι → X.C} (hY : X.J.CoversTop Y) (c c' : (globalSectionsComplex X J).homology 0)
    (h : ∀ i, HomologicalComplex.homologyMap (globalSectionsComplexProj X J (Y i)) 0 c =
      HomologicalComplex.homologyMap (globalSectionsComplexProj X J (Y i)) 0 c') : c = c' := by
  apply classCocycle_injective _ (isZero_globalSectionsComplex_X X J)
  refine abelianGlobalSection_ext hY fun i => ?_
  have hK := isZero_globalSectionsComplex_X X J
  exact classCocycle_congr hK hK (isZero_sectionComplex_X X J (Y i)) (h i)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
private lemma exists_globalSectionsComplexProj_of_isStrictlyGE
    (J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsStrictlyGE 0]
    {ι : Type*} {Y : ι → X.C} (hY : X.J.CoversTop Y)
    (x : ∀ i, (sectionComplex X J (Y i)).homology 0)
    (hx : ∀ (Z : X.C) (i j : ι) (a : Z ⟶ Y i) (b : Z ⟶ Y j),
      HomologicalComplex.homologyMap (sectionComplexRes X J a) 0 (x i) =
        HomologicalComplex.homologyMap (sectionComplexRes X J b) 0 (x j)) :
    ∃ c, ∀ i, HomologicalComplex.homologyMap (globalSectionsComplexProj X J (Y i)) 0 c = x i := by
  have hK := isZero_globalSectionsComplex_X X J
  have hKi := isZero_sectionComplex_X X J
  let y : ∀ i, (sectionComplex X J (Y i)).X 0 := fun i => classCocycle _ (hKi (Y i)) (x i)
  have hy : ∀ (Z : X.C) (i j : ι) (a : Z ⟶ Y i) (b : Z ⟶ Y j),
      (sectionComplexRes X J a).f 0 (y i) = (sectionComplexRes X J b).f 0 (y j) := by
    intro Z i j a b
    exact classCocycle_congr (hKi _) (hKi _) (hKi Z) (hx Z i j a b)
  obtain ⟨s, hs⟩ := exists_abelianGlobalSection
    (F := (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj (J.X 0)) hY y hy
  have hds : (globalSectionsComplex X J).d 0 1 s = 0 := by
    refine abelianGlobalSection_ext hY fun i => ?_
    have h1 := ConcreteCategory.congr_hom ((globalSectionsComplexProj X J (Y i)).comm 0 1) s
    simp only [ConcreteCategory.comp_apply] at h1
    refine h1.symm.trans ?_
    change (sectionComplex X J (Y i)).d 0 1 (s.val (op (Y i))) = 0
    rw [hs i]
    simp only [y, classCocycle, ← ConcreteCategory.comp_apply, Category.assoc,
      HomologicalComplex.iCycles_d, comp_zero]
    rfl
  obtain ⟨c, hc⟩ := exists_classCocycle_eq _ hK s hds
  refine ⟨c, fun i => classCocycle_injective _ (hKi (Y i)) ?_⟩
  rw [← ConcreteCategory.comp_apply, classCocycle_naturality hK (hKi (Y i)),
    ConcreteCategory.comp_apply, hc]
  exact hs i

private lemma homologyMap_natTrans_comm {D : Type*} [Category D] [Preadditive D]
    {F G : D ⥤ AddCommGrpCat.{u}} [F.Additive] [G.Additive] (α : F ⟶ G)
    {M J : CochainComplex D ℤ} (φ : M ⟶ J) (n : ℤ)
    (c : ((F.mapHomologicalComplex _).obj M).homology n) :
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app J) n
        (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) n c) =
      HomologicalComplex.homologyMap ((G.mapHomologicalComplex _).map φ) n
        (HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app M) n c) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    NatTrans.mapHomologicalComplex_naturality]

/-- **Gluing degree-zero classes of global sections of a K-injective complex acyclic in negative
degrees.** Let `M` be a K-injective complex of `𝒪`-modules with `Q(M) ∈ D^{≥ 0}`, and `Y` a family
of objects covering the site. A family of classes `x i ∈ H^0(Γ(Y i, M))` agreeing on every object
mapping to two members comes from a unique class in `H^0(Γ(C, M))`. -/
theorem existsUnique_globalSectionsComplexProj_of_isKInjective
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [M.IsKInjective]
    (hM : (DerivedCategory.Q.obj M).IsGE 0) {ι : Type*} {Y : ι → X.C} (hY : X.J.CoversTop Y)
    (x : ∀ i, (sectionComplex X M (Y i)).homology 0)
    (hx : ∀ (Z : X.C) (i j : ι) (a : Z ⟶ Y i) (b : Z ⟶ Y j),
      HomologicalComplex.homologyMap (sectionComplexRes X M a) 0 (x i) =
        HomologicalComplex.homologyMap (sectionComplexRes X M b) 0 (x j)) :
    ∃! c, ∀ i, HomologicalComplex.homologyMap (globalSectionsComplexProj X M (Y i)) 0 c = x i := by
  obtain ⟨J, hJ, ⟨h⟩⟩ := CochainComplex.exists_homotopyEquiv_isStrictlyGE_of_isKInjective M 0 hM
  let h' := (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomotopyEquiv h
  let eG := ((abelianGlobalSectionsFunctor.{u} X).mapHomotopyEquiv h').toHomologyIso 0
  let eS := fun U : X.C => ((sheafToPresheaf X.J AddCommGrpCat.{u} ⋙
    (evaluation X.Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomotopyEquiv h').toHomologyIso 0
  have hG : ∀ (U : X.C) (c : (globalSectionsComplex X M).homology 0),
      HomologicalComplex.homologyMap (globalSectionsComplexProj X J U) 0 (eG.hom c) =
        (eS U).hom (HomologicalComplex.homologyMap (globalSectionsComplexProj X M U) 0 c) :=
    fun U c => homologyMap_natTrans_comm (globalSectionsProj X U) h'.hom 0 c
  have hR : ∀ {U V : X.C} (f : V ⟶ U) (c : (sectionComplex X M U).homology 0),
      HomologicalComplex.homologyMap (sectionComplexRes X J f) 0 ((eS U).hom c) =
        (eS V).hom (HomologicalComplex.homologyMap (sectionComplexRes X M f) 0 c) :=
    fun f c => homologyMap_natTrans_comm _ h'.hom 0 c
  obtain ⟨c, hc⟩ := exists_globalSectionsComplexProj_of_isStrictlyGE X J hY
    (fun i => (eS (Y i)).hom (x i)) (fun Z i j a b => by rw [hR, hR, hx Z i j a b])
  have hinv : ∀ c, eG.hom (eG.inv c) = c := fun c => by
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  refine ⟨eG.inv c, fun i => ?_, fun c' hc' => ?_⟩
  · apply (ConcreteCategory.bijective_of_isIso (eS (Y i)).hom).1
    rw [← hG, hinv]
    exact hc i
  · apply (ConcreteCategory.bijective_of_isIso eG.hom).1
    rw [hinv]
    refine globalSectionsComplexProj_injective_of_isStrictlyGE X J hY _ _ fun i => ?_
    rw [hG, hc' i, hc i]

end GlobalGluing

end AlgebraicGeometry.RingedSite

end
