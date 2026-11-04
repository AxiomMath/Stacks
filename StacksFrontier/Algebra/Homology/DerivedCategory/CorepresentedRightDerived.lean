module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# The right derived functor of a corepresented functor

Let `Γ : C ⥤ Mod_R` be an additive functor and `U` an object of `C` with an element
`ε : R ⟶ Γ U` such that `s ↦ ε ≫ Γ s` is a bijection `Hom(U, M) ≃ Hom_R(R, Γ M)` for every `M`
(so `Γ = Hom(U, -)`, the case of global sections and `U = 𝒪_X`). If a right derived functor
`RΓ` of `Γ` is computed by K-injective complexes, then for every `M ∈ D(C)` the map

`Hom_{D(C)}(U[0], M) ⟶ Hom_R(R, H⁰(RΓ M))`, `x ↦ u ≫ H⁰(RΓ x)`,

is bijective, where `u : R ⟶ H⁰(RΓ(U[0]))` is the class of `ε`. That is,
`H⁰(RΓ M) = Hom_{D(C)}(U[0], M)`.

## Main results

* `CategoryTheory.CorepresentedRightDerived.bijective_homToHomology`: if `C` has K-injective
  resolutions, the map `Hom_{D(C)}(U[0], M) ⟶ Hom_R(R, H⁰(RΓ M))` is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CorepresentedRightDerived

universe w w' v u t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {R : Type t} [Ring R] [HasDerivedCategory.{w'} (ModuleCat.{t} R)]
  (Γ : C ⥤ ModuleCat.{t} R) [Γ.Additive] (U : C) (ε : ModuleCat.of R R ⟶ Γ.obj U)

/-- `U` placed in degree `0`. -/
abbrev single₀ : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj U

/-- `H⁰` of the image in `D(Mod_R)` of a complex is the homology of the complex. -/
def homologyQhIso (L : CochainComplex (ModuleCat.{t} R) ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj L)) ≅ L.homology 0 :=
  (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{t} R) 0).app _ ≪≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{t} R) (ComplexShape.up ℤ) 0).app L

/-- The isomorphism `homologyQhIso` is natural in the complex. -/
theorem homologyQhIso_naturality {L L' : CochainComplex (ModuleCat.{t} R) ℤ} (f : L ⟶ L') :
    (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f)) ≫
      (homologyQhIso L').hom = (homologyQhIso L).hom ≫ HomologicalComplex.homologyMap f 0 := by
  have h₁ := (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{t} R) 0).hom.naturality
    ((HomotopyCategory.quotient _ _).map f)
  have h₂ := (HomotopyCategory.homologyFunctorFactors (ModuleCat.{t} R)
    (ComplexShape.up ℤ) 0).hom.naturality f
  dsimp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂
  change _ ≫ ((DerivedCategory.homologyFunctorFactorsh (ModuleCat.{t} R) 0).hom.app _ ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{t} R) (ComplexShape.up ℤ) 0).hom.app
        L') =
    ((DerivedCategory.homologyFunctorFactorsh (ModuleCat.{t} R) 0).hom.app _ ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{t} R) (ComplexShape.up ℤ) 0).hom.app
        L) ≫ _
  rw [← Category.assoc, h₁, Category.assoc, h₂]
  exact (Category.assoc _ _ _).symm

/-- The inverse of `homologyQhIso` is natural in the complex. -/
theorem homologyQhIso_inv_naturality {L L' : CochainComplex (ModuleCat.{t} R) ℤ} (f : L ⟶ L') :
    (homologyQhIso L).inv ≫ (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f)) =
      HomologicalComplex.homologyMap f 0 ≫ (homologyQhIso L').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← homologyQhIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

variable {Γ U}

/-- The class in `H⁰(Γ L)` of a morphism `R ⟶ Γ(L⁰)` killed by the differential. -/
def cls (L : CochainComplex C ℤ) (k : ModuleCat.of R R ⟶ Γ.obj (L.X 0))
    (hk : k ≫ Γ.map (L.d 0 1) = 0) :
    ModuleCat.of R R ⟶ ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homology 0 :=
  ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).liftCycles k 1 (by simp) hk ≫
    ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homologyπ 0

omit [HasDerivedCategory C] [HasDerivedCategory (ModuleCat R)] in
/-- The class `cls` of a difference is the difference of the classes. -/
theorem cls_sub (L : CochainComplex C ℤ) (k k' : ModuleCat.of R R ⟶ Γ.obj (L.X 0))
    (hk : k ≫ Γ.map (L.d 0 1) = 0) (hk' : k' ≫ Γ.map (L.d 0 1) = 0) :
    cls L k hk - cls L k' hk' =
      cls L (k - k') (by rw [Preadditive.sub_comp, hk, hk', sub_zero]) := by
  simp only [cls, ← Preadditive.sub_comp]
  congr 1
  rw [← cancel_mono (HomologicalComplex.iCycles _ 0)]
  simp

omit [HasDerivedCategory C] [HasDerivedCategory (ModuleCat R)] in
/-- Equal morphisms `R ⟶ Γ(L⁰)` have equal classes `cls`. -/
theorem cls_congr (L : CochainComplex C ℤ) {k k' : ModuleCat.of R R ⟶ Γ.obj (L.X 0)}
    (hk : k ≫ Γ.map (L.d 0 1) = 0) (h : k = k') :
    cls L k hk = cls L k' (h ▸ hk) := by
  subst h
  rfl

omit [HasDerivedCategory C] [HasDerivedCategory (ModuleCat R)] in
/-- The class of `k` maps under `φ` to the class of `k ≫ Γ(φ⁰)`. -/
theorem cls_naturality {L L' : CochainComplex C ℤ} (φ : L ⟶ L')
    (k : ModuleCat.of R R ⟶ Γ.obj (L.X 0)) (hk : k ≫ Γ.map (L.d 0 1) = 0) :
    cls L k hk ≫ HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex _).map φ) 0 =
      cls L' (k ≫ Γ.map (φ.f 0)) (by
        rw [Category.assoc, ← Γ.map_comp, φ.comm, Γ.map_comp, reassoc_of% hk,
          Limits.zero_comp]) := by
  simp only [cls, Category.assoc, HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  rfl

omit [HasDerivedCategory C] [HasDerivedCategory (ModuleCat R)] in
/-- The image under `Γ` of a cycle `s : U ⟶ I⁰`, precomposed with `ε`, is killed by the
differential. -/
theorem comp_map_d_eq_zero {I : CochainComplex C ℤ} {s : U ⟶ I.X 0}
    (hs : ∀ k, (ComplexShape.up ℤ).Rel 0 k → s ≫ I.d 0 k = 0) :
    (ε ≫ Γ.map s) ≫ Γ.map (I.d 0 1) = 0 := by
  rw [Category.assoc, ← Γ.map_comp, hs 1 rfl, Γ.map_zero, Limits.comp_zero]

variable (Γ U)

/-- The class `u₀ ∈ H⁰(Γ(U[0]))` of `ε`. -/
def unitCls : ModuleCat.of R R ⟶
    ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (single₀ U)).homology 0 :=
  cls (single₀ U) (ε ≫ Γ.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 U).inv)
    (by simp)

omit [HasDerivedCategory C] [HasDerivedCategory (ModuleCat R)] in
/-- The unit class maps under a cycle `s : U ⟶ I⁰` to the class of `ε ≫ Γ s`. -/
theorem unitCls_comp_homologyMap_mkHomFromSingle (I : CochainComplex C ℤ) (s : U ⟶ I.X 0)
    (hs : ∀ k, (ComplexShape.up ℤ).Rel 0 k → s ≫ I.d 0 k = 0) :
    unitCls Γ U ε ≫ HomologicalComplex.homologyMap
        ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.mkHomFromSingle s hs)) 0 =
      cls I (ε ≫ Γ.map s) (comp_map_d_eq_zero ε hs) := by
  rw [unitCls, cls_naturality]
  exact cls_congr I _ (by rw [Category.assoc, ← Γ.map_comp,
    HomologicalComplex.mkHomFromSingle_f, Iso.inv_hom_id_assoc])

variable (RΓ : DerivedCategory C ⥤ DerivedCategory (ModuleCat.{t} R))
  (α : Γ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RΓ)

/-- The class `u ∈ H⁰(RΓ(U[0]))` of `ε`. -/
def unitDerived : ModuleCat.of R R ⟶ (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).obj
    (RΓ.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj (single₀ U)))) :=
  unitCls Γ U ε ≫ (homologyQhIso _).inv ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).map
      (α.app ((HomotopyCategory.quotient _ _).obj (single₀ U)))

/-- The map `Hom_{D(C)}(U[0], M) ⟶ Hom_R(R, H⁰(RΓ M))`. -/
def homToHomology (M : DerivedCategory C)
    (x : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj (single₀ U)) ⟶ M) :
    ModuleCat.of R R ⟶ (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).obj (RΓ.obj M) :=
  unitDerived Γ U ε RΓ α ≫ (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).map (RΓ.map x)

/-- `homToHomology` is compatible with postcomposition by a morphism `g : M ⟶ M'`. -/
theorem homToHomology_comp {M M' : DerivedCategory C}
    (x : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj (single₀ U)) ⟶ M)
    (g : M ⟶ M') :
    homToHomology Γ U ε RΓ α M' (x ≫ g) =
      homToHomology Γ U ε RΓ α M x ≫ (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).map
        (RΓ.map g) := by
  simp [homToHomology]

/-- The map on a morphism coming from a cycle `s : U ⟶ I⁰`. -/
theorem homToHomology_mkHomFromSingle (I : CochainComplex C ℤ) (s : U ⟶ I.X 0)
    (hs : ∀ k, (ComplexShape.up ℤ).Rel 0 k → s ≫ I.d 0 k = 0) :
    homToHomology Γ U ε RΓ α _ (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (HomologicalComplex.mkHomFromSingle s hs))) =
      cls I (ε ≫ Γ.map s) (by rw [Category.assoc, ← Γ.map_comp, hs 1 rfl, Γ.map_zero,
        Limits.comp_zero]) ≫
        (homologyQhIso _).inv ≫ (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).map
          (α.app ((HomotopyCategory.quotient _ _).obj I)) := by
  let σ := HomologicalComplex.mkHomFromSingle s hs
  have hα : α.app ((HomotopyCategory.quotient _ _).obj (single₀ U)) ≫
      RΓ.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map σ)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map σ)) ≫
        α.app ((HomotopyCategory.quotient _ _).obj I) :=
    (α.naturality ((HomotopyCategory.quotient _ _).map σ)).symm
  have h1 : (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).map
        (α.app ((HomotopyCategory.quotient _ _).obj (single₀ U))) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).map
        (RΓ.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map σ))) =
      (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map σ))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).map
          (α.app ((HomotopyCategory.quotient _ _).obj I)) := by
    rw [← Functor.map_comp, hα]
    exact Functor.map_comp _ _ _
  change unitCls Γ U ε ≫ (homologyQhIso _).inv ≫
    ((DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).map
        (α.app ((HomotopyCategory.quotient _ _).obj (single₀ U))) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).map
        (RΓ.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map σ)))) = _
  refine (congrArg (fun t => unitCls Γ U ε ≫ (homologyQhIso _).inv ≫ t) h1).trans ?_
  rw [← Category.assoc ((homologyQhIso _).inv), homologyQhIso_inv_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (unitCls Γ U ε), unitCls_comp_homologyMap_mkHomFromSingle]

omit [HasDerivedCategory C] in
/-- A morphism `U[0] ⟶ I` whose degree-zero component is a boundary is null-homotopic. -/
theorem quotient_map_mkHomFromSingle_eq_zero (I : CochainComplex C ℤ) (h : U ⟶ I.X (-1))
    (hs : ∀ k, (ComplexShape.up ℤ).Rel 0 k → (h ≫ I.d (-1) 0) ≫ I.d 0 k = 0) :
    (HomotopyCategory.quotient _ _).map (HomologicalComplex.mkHomFromSingle (h ≫ I.d (-1) 0) hs) =
      0 := by
  let hh : ∀ i j, (ComplexShape.up ℤ).Rel j i → ((single₀ U).X i ⟶ I.X j) := fun i j hij =>
    if hi : i = 0 then (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 U i hi).hom ≫
      h ≫ eqToHom (congrArg I.X (by simp only [ComplexShape.up_Rel] at hij; omega)) else 0
  have heq : HomologicalComplex.mkHomFromSingle (h ≫ I.d (-1) 0) hs =
      Homotopy.nullHomotopicMap' hh := by
    refine HomologicalComplex.from_single_hom_ext ?_
    rw [HomologicalComplex.mkHomFromSingle_f,
      Homotopy.nullHomotopicMap'_f (k₂ := -1) (k₁ := 0) (k₀ := 1) (by simp) (by simp)]
    simp [hh, HomologicalComplex.singleObjXSelf]
  rw [HomotopyCategory.eq_of_homotopy _ _ ((Homotopy.ofEq heq).trans (Homotopy.nullHomotopy' hh)),
    Functor.map_zero]

variable (hε : ∀ M : C, Function.Bijective (fun s : U ⟶ M => ε ≫ Γ.map s))
  (hα : ∀ I : CochainComplex C ℤ, I.IsKInjective →
    IsIso (α.app ((HomotopyCategory.quotient _ _).obj I)))

include hε in
omit [HasDerivedCategory C] [HasDerivedCategory (ModuleCat R)] in
/-- A morphism `s : U ⟶ M` with `ε ≫ Γ s = 0` is zero. -/
theorem eq_zero_of_comp_eq_zero {M : C} (s : U ⟶ M) (hs : ε ≫ Γ.map s = 0) : s = 0 :=
  (hε M).1 (by simpa using hs)

/-- Every morphism `U[0] ⟶ I` in `D(C)` to a K-injective complex comes from a cycle
`s : U ⟶ I⁰`. -/
theorem exists_eq_Qh_map_mkHomFromSingle (I : CochainComplex C ℤ) [I.IsKInjective]
    (x : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj (single₀ U)) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)) :
    ∃ (s : U ⟶ I.X 0) (hs : ∀ k, (ComplexShape.up ℤ).Rel 0 k → s ≫ I.d 0 k = 0),
      x = DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (HomologicalComplex.mkHomFromSingle s hs)) := by
  obtain ⟨g, rfl⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj (single₀ U)) I).2 x
  obtain ⟨σ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨(HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 U).inv ≫ σ.f 0,
    fun k hk => by rw [Category.assoc, σ.comm]; simp, ?_⟩
  congr 2
  refine HomologicalComplex.from_single_hom_ext ?_
  rw [HomologicalComplex.mkHomFromSingle_f, Iso.hom_inv_id_assoc]

include hε in
omit [HasDerivedCategory C] [HasDerivedCategory (ModuleCat R)] in
/-- Cycles `s₁ s₂ : U ⟶ I⁰` with equal classes in `H⁰(Γ I)` differ by a boundary. -/
theorem exists_comp_d_eq_sub_of_cls_eq (I : CochainComplex C ℤ) {s₁ s₂ : U ⟶ I.X 0}
    (hs₁ : ∀ k, (ComplexShape.up ℤ).Rel 0 k → s₁ ≫ I.d 0 k = 0)
    (hs₂ : ∀ k, (ComplexShape.up ℤ).Rel 0 k → s₂ ≫ I.d 0 k = 0)
    (hcls : cls I (ε ≫ Γ.map s₁)
        (by rw [Category.assoc, ← Γ.map_comp, hs₁ 1 rfl, Γ.map_zero, Limits.comp_zero]) =
      cls I (ε ≫ Γ.map s₂)
        (by rw [Category.assoc, ← Γ.map_comp, hs₂ 1 rfl, Γ.map_zero, Limits.comp_zero])) :
    ∃ h : U ⟶ I.X (-1), h ≫ I.d (-1) 0 = s₁ - s₂ := by
  let L := (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have h0 := (cls_sub I _ _ _ _).symm.trans (sub_eq_zero.2 hcls)
  have hexact : (ShortComplex.mk (L.toCycles (-1) 0) (L.homologyπ 0)
      (L.toCycles_comp_homologyπ (-1) 0)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (L.homologyIsCokernel (-1) 0 (by simp))
  let c := L.liftCycles (ε ≫ Γ.map s₁ - ε ≫ Γ.map s₂) 1 (by simp)
    (by
      rw [Preadditive.sub_comp, sub_eq_zero]
      exact (comp_map_d_eq_zero ε hs₁).trans (comp_map_d_eq_zero ε hs₂).symm)
  let t' := hexact.liftFromProjective c h0
  have ht' : t' ≫ L.d (-1) 0 = ε ≫ Γ.map s₁ - ε ≫ Γ.map s₂ := by
    rw [← L.toCycles_i (-1) 0, ← Category.assoc, hexact.liftFromProjective_comp c h0]
    exact L.liftCycles_i _ _ _ _
  obtain ⟨h, hh : ε ≫ Γ.map h = t'⟩ := (hε (I.X (-1))).2 t'
  refine ⟨h, (hε (I.X 0)).1 ?_⟩
  change ε ≫ Γ.map (h ≫ I.d (-1) 0) = ε ≫ Γ.map (s₁ - s₂)
  rwa [Γ.map_comp, ← Category.assoc, hh, Γ.map_sub, Preadditive.comp_sub]

include hε in
omit [HasDerivedCategory C] [HasDerivedCategory (ModuleCat R)] in
/-- Cycles `s₁ s₂ : U ⟶ I⁰` with equal classes in `H⁰(Γ I)` give homotopic morphisms
`U[0] ⟶ I`. -/
theorem quotient_map_mkHomFromSingle_eq_of_cls_eq (I : CochainComplex C ℤ) {s₁ s₂ : U ⟶ I.X 0}
    (hs₁ : ∀ k, (ComplexShape.up ℤ).Rel 0 k → s₁ ≫ I.d 0 k = 0)
    (hs₂ : ∀ k, (ComplexShape.up ℤ).Rel 0 k → s₂ ≫ I.d 0 k = 0)
    (hcls : cls I (ε ≫ Γ.map s₁)
        (by rw [Category.assoc, ← Γ.map_comp, hs₁ 1 rfl, Γ.map_zero, Limits.comp_zero]) =
      cls I (ε ≫ Γ.map s₂)
        (by rw [Category.assoc, ← Γ.map_comp, hs₂ 1 rfl, Γ.map_zero, Limits.comp_zero])) :
    (HomotopyCategory.quotient _ _).map (HomologicalComplex.mkHomFromSingle s₁ hs₁) =
      (HomotopyCategory.quotient _ _).map (HomologicalComplex.mkHomFromSingle s₂ hs₂) := by
  obtain ⟨h, hd⟩ := exists_comp_d_eq_sub_of_cls_eq Γ U ε hε I hs₁ hs₂ hcls
  have hs : ∀ k, (ComplexShape.up ℤ).Rel 0 k → (h ≫ I.d (-1) 0) ≫ I.d 0 k = 0 := fun k hk => by
    rw [hd, Preadditive.sub_comp, hs₁ k hk, hs₂ k hk, sub_zero]
  have hsub : HomologicalComplex.mkHomFromSingle s₁ hs₁ -
      HomologicalComplex.mkHomFromSingle s₂ hs₂ =
        HomologicalComplex.mkHomFromSingle (h ≫ I.d (-1) 0) hs := by
    refine HomologicalComplex.from_single_hom_ext ?_
    rw [HomologicalComplex.sub_f_apply, HomologicalComplex.mkHomFromSingle_f,
      HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.mkHomFromSingle_f, hd,
      Preadditive.comp_sub]
  rw [← sub_eq_zero, ← Functor.map_sub, hsub, quotient_map_mkHomFromSingle_eq_zero U I h hs]

/-- Postcomposition with the forward map of an isomorphism is bijective. -/
private theorem bijective_comp_hom_of_iso {D : Type*} [Category D] {X Y Z : D} (g : Y ≅ Z) :
    Function.Bijective (fun x : X ⟶ Y => x ≫ g.hom) :=
  ⟨fun _ _ h => (cancel_mono g.hom).1 h, fun y => ⟨y ≫ g.inv, by simp⟩⟩

include hε hα in
/-- For a K-injective complex `I`, the map `homToHomology` at `I` is bijective. -/
theorem bijective_homToHomology_of_isKInjective (I : CochainComplex C ℤ) [I.IsKInjective] :
    Function.Bijective (homToHomology Γ U ε RΓ α
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))) := by
  have := hα I inferInstance
  let L := (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  let T : L.homology 0 ⟶ (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).obj
      (RΓ.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))) :=
    (homologyQhIso L).inv ≫ (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).map
      (α.app ((HomotopyCategory.quotient _ _).obj I))
  have : IsIso T := IsIso.comp_isIso' inferInstance
    (Functor.map_isIso (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0)
      (α.app ((HomotopyCategory.quotient _ _).obj I)))
  refine ⟨fun x₁ x₂ hx => ?_, fun y => ?_⟩
  · obtain ⟨s₁, hs₁, rfl⟩ := exists_eq_Qh_map_mkHomFromSingle U I x₁
    obtain ⟨s₂, hs₂, rfl⟩ := exists_eq_Qh_map_mkHomFromSingle U I x₂
    rw [homToHomology_mkHomFromSingle, homToHomology_mkHomFromSingle] at hx
    rw [quotient_map_mkHomFromSingle_eq_of_cls_eq Γ U ε hε I hs₁ hs₂ ((cancel_mono T).1 hx)]
  · obtain ⟨c, hc⟩ := Projective.factors (y ≫ inv T) (L.homologyπ 0)
    obtain ⟨s, hsk : ε ≫ Γ.map s = c ≫ L.iCycles 0⟩ := (hε (I.X 0)).2 (c ≫ L.iCycles 0)
    have hs : ∀ k, (ComplexShape.up ℤ).Rel 0 k → s ≫ I.d 0 k = 0 := by
      rintro k rfl
      refine eq_zero_of_comp_eq_zero Γ U ε hε _ ?_
      rw [Γ.map_comp, ← Category.assoc]
      change (ε ≫ Γ.map s) ≫ L.d 0 1 = 0
      rw [hsk, Category.assoc, L.iCycles_d, Limits.comp_zero]
    refine ⟨_, (homToHomology_mkHomFromSingle Γ U ε RΓ α I s hs).trans ?_⟩
    change cls I (ε ≫ Γ.map s) _ ≫ T = y
    have hcls : cls I (ε ≫ Γ.map s) (comp_map_d_eq_zero ε hs) = c ≫ L.homologyπ 0 := by
      unfold cls
      congr 1
      rw [← cancel_mono (L.iCycles 0), L.liftCycles_i, hsk]
    rw [hcls, hc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

include hε hα in
/-- **`H⁰(RΓ M) = Hom_{D(C)}(U[0], M)`.** If `C` has K-injective resolutions, the map
`Hom_{D(C)}(U[0], M) ⟶ Hom_R(R, H⁰(RΓ M))`, `x ↦ u ≫ H⁰(RΓ x)`, is bijective. -/
theorem bijective_homToHomology
    (hres : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (M : DerivedCategory C) : Function.Bijective (homToHomology Γ U ε RΓ α M) := by
  obtain ⟨I, f, hI, hf⟩ := hres (DerivedCategory.Q.objPreimage M)
  let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) ≅ M :=
    (DerivedCategory.quotientCompQhIso C).app I ≪≫ (asIso (DerivedCategory.Q.map f)).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso M
  have key : homToHomology Γ U ε RΓ α M = (fun z => z ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).map (RΓ.map e.hom)) ∘
      homToHomology Γ U ε RΓ α _ ∘ (fun x => x ≫ e.inv) := by
    funext x
    simp only [Function.comp_apply, ← homToHomology_comp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  rw [key]
  exact (bijective_comp_hom_of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{t} R) 0).mapIso (RΓ.mapIso e))).comp
    ((bijective_homToHomology_of_isKInjective Γ U ε RΓ α hε hα I).comp
      (bijective_comp_hom_of_iso e.symm))

end CategoryTheory.CorepresentedRightDerived

end
