module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativeDualizingModuleMap
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.Homology.HomComplex.RHom.SingleBaseChangeUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompat
public meta import StacksFrontier.Tactic.HEqCongr
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.Localization

/-!
# The trace of a finite morphism and restriction to an open

Let `h : T ⟶ T₁` be a finite morphism and `i : X ⟶ T`, `i₁ : X ⟶ T₁` open immersions with
`i ≫ h = i₁` cartesian over `𝟙 X`, so that `h` is an isomorphism over `X`. On `H⁰`, the map
`i^*a_h(K) ⟶ a_{𝟙}(i₁^*K) = i₁^*K` of [Stacks, Tag 0A9L] is the restriction to `X` of the trace
`h_*H⁰(a_h K) ⟶ H⁰(K)`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits DerivedCategory

universe u

namespace Stacks.SmallDerivedCategory

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] {C₂ : Type*} [Category* C₂] [Abelian C₂]
  {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} [F.Additive] [G.Additive] [HasDerivedCategory C₁]
  [HasDerivedCategory C₂] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (adj : F ⊣ G) (RG : DerivedCategory C₂ ⥤ DerivedCategory C₁)
  (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RG)

omit [F.Additive] [G.Additive] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- `x ≫ βX ≫ R.map f` rewritten through the factorizations `x = a₁ ≫ b₁ ≫ c₁`, `a₁ = su ≫ t`,
`cR = τ ≫ cR'` and the commutative square `c₁ ≫ βX = βY ≫ R.map cR`. -/
theorem unit_single_chase {E E' : Type*} [Category E] [Category E'] (R : E' ⥤ E)
    {e₀ e₀₁ e₁₁ e₁₂ e₁ : E} {o₁ o₂ o₂' o₃ : E'}
    (x : e₀ ⟶ e₁) (a₁ : e₀ ⟶ e₁₁) (b₁ : e₁₁ ⟶ e₁₂) (c₁ : e₁₂ ⟶ e₁) (hx : x = a₁ ≫ b₁ ≫ c₁)
    (βX : e₁ ⟶ R.obj o₁) (βY : e₁₂ ⟶ R.obj o₂) (cR : o₂ ⟶ o₁)
    (hβ : c₁ ≫ βX = βY ≫ R.map cR) (f : o₁ ⟶ o₃)
    (su : e₀ ⟶ e₀₁) (t : e₀₁ ⟶ e₁₁) (hsu : su ≫ t = a₁)
    (τ : o₂ ⟶ o₂') (cR' : o₂' ⟶ o₁) (hτ : τ ≫ cR' = cR) :
    x ≫ βX ≫ R.map f = su ≫ ((t ≫ b₁) ≫ βY ≫ R.map τ) ≫ R.map (cR' ≫ f) := by
  subst hx hsu hτ
  simp only [Category.assoc, R.map_comp]
  rw [reassoc_of% hβ, R.map_comp]
  simp

omit [F.Additive] [G.Additive] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- `k ≫ m ≫ fac ≫ n ≫ p = y` when `m`, `n` and `p` are identities and `k ≫ fac = y`. -/
theorem single_iso_chase {E : Type*} [Category E] {a b c : E} (k : a ⟶ b) (m : b ⟶ b)
    (hm : m = 𝟙 b) (fac : b ⟶ c) (n : c ⟶ c) (hn : n = 𝟙 c) (p : c ⟶ c) (hp : p = 𝟙 c)
    (y : a ⟶ c) (h2 : k ≫ fac = y) : k ≫ m ≫ fac ≫ n ≫ p = y := by
  subst hm hn hp
  simpa using h2

/-- The comparison `F(M)[0] ≅ F.mapDerivedCategory (M[0])` through homotopy categories. -/
private theorem mapDerivedCategorySingleFunctor_inv_app_eq (M : C₁) :
    (F.mapDerivedCategorySingleFunctor 0).inv.app M =
      Qh.map (Stacks.DerivedFunctor.singleMapHomotopyCategoryInv F M) ≫
        F.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.singleFunctor C₁ 0).obj M) := by
  refine (Iso.eq_comp_inv (F.mapDerivedCategoryFactorsh.app _)).mpr ?_
  have h := F.mapDerivedCategoryFactorsh_hom_app
    ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) 0).obj M)
  have h2 := F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app M
  refine (congrArg (_ ≫ ·) h).trans ?_
  refine single_iso_chase _ _ ?_ _ _ ?_ _ ?_ _ h2
  · exact (congrArg F.mapDerivedCategory.map rfl).trans (CategoryTheory.Functor.map_id _ _)
  · rfl
  · exact (congrArg Qh.map rfl).trans (CategoryTheory.Functor.map_id _ _)

/-- **The derived unit at `M[0]`** is the unit of `F ⊣ G` at `M`, followed by `G(F M)[0] ⟶
RG(F(M)[0])` and the comparison `F(M)[0] ≅ F.mapDerivedCategory (M[0])`. -/
theorem descendedUnit_app_single (M : C₁) :
    (descendedUnit adj RG β).app ((singleFunctor C₁ 0).obj M) =
      (singleFunctor C₁ 0).map (adj.unit.app M) ≫
        Stacks.DerivedFunctor.singleDerivedUnit G RG β (F.obj M) ≫
          RG.map ((F.mapDerivedCategorySingleFunctor 0).inv.app M) := by
  have hw : (descendedUnit adj RG β).app ((singleFunctor C₁ 0).obj M) =
      (homotopyDescendedUnit adj RG β).app ((HomotopyCategory.quotient C₁ _).obj
        ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) 0).obj M)) :=
    NatTrans.congr_app (whiskerLeft_descendedUnit adj RG β)
      ((HomotopyCategory.singleFunctor C₁ 0).obj M)
  rw [hw, homotopyDescendedUnit_eq]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [homotopyAdjunction_unit_app_quotient]
  have e1 : (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) 0).obj M)) = 𝟙 _ := rfl
  have e2 : (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
      ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) 0).obj M) = 𝟙 _ := rfl
  have e3 : (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) 0).obj M)) ≫
      (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
          ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) 0).obj M)) = 𝟙 _ :=
    (congrArg (fun z => (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) 0).obj M)) ≫ z)
      ((congrArg (G.mapHomotopyCategory (ComplexShape.up ℤ)).map e2).trans
        (CategoryTheory.Functor.map_id _ _))).trans ((Category.comp_id _).trans e1)
  refine (congrArg (fun z => Qh.map ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).map
    ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
      ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) 0).obj M)) ≫ z) ≫ _) e3).trans ?_
  refine (congrArg (fun z => Qh.map z ≫ _) (Category.comp_id _)).trans ?_
  have hu := Adjunction.mapHomologicalComplex_unit_app_single adj (ComplexShape.up ℤ) 0 M
  have hu' : (adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
      ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) 0).obj M) =
      (HomologicalComplex.single C₁ (ComplexShape.up ℤ) 0).map (adj.unit.app M) ≫
        (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).inv.app (F.obj M) ≫
        (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M) := by
    rw [← hu]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  rw [hu', Stacks.DerivedFunctor.singleDerivedUnit, Stacks.DerivedFunctor.mapSingleQhIso_inv_app,
    mapDerivedCategorySingleFunctor_inv_app_eq]
  have hβ := β.naturality ((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M))
  simp only [Functor.comp_map] at hβ
  have s1 : (singleFunctorIsoCompQh C₁ 0).hom.app (G.obj (F.obj M)) =
      (DerivedCategory.quotientCompQhIso C₁).inv.app
        ((CochainComplex.singleFunctor C₁ 0).obj (G.obj (F.obj M))) :=
    Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app 0 _
  have s2 := (singleFunctorIsoCompQh C₂ 0).inv_hom_id_app (F.obj M)
  rw [Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app] at s2
  refine unit_single_chase RG _ ((Qh (C := C₁)).map ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).map
    ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) 0).map (adj.unit.app M)))) _ _ ?_ _ _ _ hβ
    _ _ _ ?_ _ _ ?_
  · simp only [Functor.map_comp]
    rfl
  · refine (congrArg (_ ≫ ·) s1).trans ?_
    exact Category.comp_id _
  · have q1 : (DerivedCategory.quotientCompQhIso C₂).inv.app
        ((CochainComplex.singleFunctor C₂ 0).obj (F.obj M)) = 𝟙 _ := rfl
    have s2' : (singleFunctorIsoCompQh C₂ 0).inv.app (F.obj M) = 𝟙 _ :=
      (Category.comp_id _).symm.trans ((congrArg (_ ≫ ·) q1).symm.trans s2)
    exact (congrArg (· ≫ _) s2').trans (Category.id_comp _)

end Stacks.SmallDerivedCategory

namespace Stacks.DerivedFunctor

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
  (w : A ⥤ B) [w.Additive] (Rw : DerivedCategory A ⥤ DerivedCategory B)
  (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ Rw)

/-- `w(X)[0] ⟶ Rw(X[0])` is natural in `X`. -/
theorem singleDerivedUnit_naturality {M M' : A} (φ : M ⟶ M') :
    (singleFunctor B 0).map (w.map φ) ≫ singleDerivedUnit w Rw α M' =
      singleDerivedUnit w Rw α M ≫ Rw.map ((singleFunctor A 0).map φ) := by
  have h₁ := (mapSingleQhIso w 0).inv.naturality φ
  have h₂ := α.naturality ((HomotopyCategory.singleFunctor A 0).map φ)
  have h₃ := (singleFunctorIsoCompQh A 0).inv.naturality φ
  simp only [Functor.comp_map] at h₁ h₂ h₃
  simp only [singleDerivedUnit, Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, ← Rw.map_comp, ← Rw.map_comp, h₃]

end Stacks.DerivedFunctor

namespace Stacks.Duality

open DerivedPushforward

/-- **The counit of `Rh_* ⊣ a_h` restricted to an open, through the map of Tag 0A9L**: for the
map `γ` built from the restriction adjunctions and the mate `ξ` of the square of direct
images, `j^*(Tr_h) = β ≫ Rf_*(γ) ≫ Tr_f`. -/
theorem map_counit_eq_restrictionMap {Ct Ct₁ Cx Cx' : Type*} [Category Ct] [Category Ct₁]
    [Category Cx] [Category Cx']
    {Li : Ct ⥤ Cx} {Ri : Cx ⥤ Ct} {Lj : Ct₁ ⥤ Cx'} {Rj : Cx' ⥤ Ct₁} {Rh : Ct ⥤ Ct₁}
    {a : Ct₁ ⥤ Ct} {Rf : Cx ⥤ Cx'} {a' : Cx' ⥤ Cx}
    (adjI : Li ⊣ Ri) (adjJ : Lj ⊣ Rj) (adjH : Rh ⊣ a) (adjF : Rf ⊣ a')
    (σ : Ri ⋙ Rh ⟶ Rf ⋙ Rj) (ξ : a' ⋙ Ri ⟶ Rj ⋙ a) [IsIso ξ]
    (hξ : ∀ N, Rh.map (ξ.app N) ≫ adjH.counit.app (Rj.obj N) =
      σ.app (a'.obj N) ≫ Rj.map (adjF.counit.app N))
    (K : Ct₁) (γK : Li.obj (a.obj K) ⟶ a'.obj (Lj.obj K))
    (hγ : γK = Li.map (a.map (adjJ.unit.app K)) ≫ Li.map ((inv ξ).app (Lj.obj K)) ≫
      adjI.counit.app (a'.obj (Lj.obj K))) :
    Lj.map (adjH.counit.app K) =
      (Lj.map (Rh.map (adjI.unit.app (a.obj K))) ≫ Lj.map (σ.app (Li.obj (a.obj K))) ≫
        adjJ.counit.app (Rf.obj (Li.obj (a.obj K)))) ≫ Rf.map γK ≫
        adjF.counit.app (Lj.obj K) := by
  have h1 : adjI.unit.app (a.obj K) ≫ Ri.map γK =
      a.map (adjJ.unit.app K) ≫ (inv ξ).app (Lj.obj K) := by
    have n1 := adjI.unit_naturality (a.map (adjJ.unit.app K))
    have n2 := adjI.unit_naturality ((inv ξ).app (Lj.obj K))
    have t := adjI.right_triangle_components (a'.obj (Lj.obj K))
    rw [hγ, Ri.map_comp, Ri.map_comp, reassoc_of% n1, reassoc_of% n2, t, Category.comp_id]
  have h2 : Rh.map ((inv ξ).app (Lj.obj K)) ≫ σ.app (a'.obj (Lj.obj K)) ≫
      Rj.map (adjF.counit.app (Lj.obj K)) = adjH.counit.app (Rj.obj (Lj.obj K)) := by
    rw [← hξ, ← Category.assoc, ← Rh.map_comp]
    simp
  have h3 := adjH.counit.naturality (adjJ.unit.app K)
  simp only [Functor.comp_map, Functor.id_map, Functor.id_obj, Functor.comp_obj] at h3
  have h4 := adjJ.counit.naturality (Rf.map γK)
  simp only [Functor.comp_map, Functor.id_map] at h4
  have h5 := σ.naturality γK
  simp only [Functor.comp_map] at h5
  have h6 := adjJ.counit.naturality (adjF.counit.app (Lj.obj K))
  simp only [Functor.comp_map, Functor.id_map] at h6
  calc Lj.map (adjH.counit.app K)
      = Lj.map (adjH.counit.app K) ≫ Lj.map (adjJ.unit.app K) ≫ adjJ.counit.app (Lj.obj K) := by
        simp
    _ = Lj.map (Rh.map (a.map (adjJ.unit.app K)) ≫ adjH.counit.app (Rj.obj (Lj.obj K))) ≫
          adjJ.counit.app (Lj.obj K) := by
        rw [h3, Lj.map_comp, Category.assoc]
    _ = Lj.map (Rh.map (adjI.unit.app (a.obj K) ≫ Ri.map γK) ≫ σ.app (a'.obj (Lj.obj K)) ≫
          Rj.map (adjF.counit.app (Lj.obj K))) ≫ adjJ.counit.app (Lj.obj K) := by
        rw [h1, Rh.map_comp, Category.assoc, h2]
    _ = _ := by
        have h5' := congrArg Lj.map h5
        simp only [Lj.map_comp] at h5'
        simp only [Rh.map_comp, Lj.map_comp, Category.assoc]
        rw [reassoc_of% h5']
        simp only [Functor.id_obj, Functor.comp_obj] at h6
        rw [h6, reassoc_of% h4]

section Single

variable {Z : Scheme.{u}} [CompactSpace Z] [QuasiSeparatedSpace Z]

/-- `N[0]` as an object of `D_QCoh`. -/
abbrev singleQCoh (N : Z.Modules) [N.IsQuasicoherent] : quasiCoherentDerivedCategory Z :=
  ⟨(singleFunctor Z.Modules 0).obj N, derivedCategoryB_singleFunctor_obj N inferInstance⟩

/-- The unit `g_*N[0] ⟶ Rg_*(N[0])`. -/
abbrev singlePushforwardUnit {Z' : Scheme.{u}} (g : Z ⟶ Z') (N : Z.Modules) :=
  Stacks.DerivedFunctor.singleDerivedUnit (Scheme.Modules.pushforward g) (derivedPushforward g)
    (derivedPushforwardUnit g) N

/-- The congruence isomorphism of the pushforward at `rfl` is the identity. -/
private theorem pushforwardCongr_refl_hom_app_eq_id {Z Z' : Scheme.{u}} (g : Z ⟶ Z')
    (N : Z.Modules) : (Scheme.Modules.pushforwardCongr (rfl : g = g)).hom.app N = 𝟙 _ := by
  ext U x
  simp

/-- For `e : g₁ = g₂`, the unit `g₁_*N[0] ⟶ Rg₁_*(N[0])` followed by `Rg₁_* ≅ Rg₂_*` on `D_QCoh`
is `g₁_*N ≅ g₂_*N` followed by the unit `g₂_*N[0] ⟶ Rg₂_*(N[0])`. -/
theorem singlePushforwardUnit_comp_congr {Z' : Scheme.{u}} [CompactSpace Z']
    [QuasiSeparatedSpace Z']
    {g₁ g₂ : Z ⟶ Z'} (e : g₁ = g₂) (N : Z.Modules) [N.IsQuasicoherent] :
    singlePushforwardUnit g₁ N ≫ ((quasiCoherentDerivedPushforwardCongr e
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app (singleQCoh N)).hom =
      (singleFunctor Z'.Modules 0).map ((Scheme.Modules.pushforwardCongr e).hom.app N) ≫
        singlePushforwardUnit g₂ N := by
  subst e
  rw [pushforwardCongr_refl_hom_app_eq_id]
  simp only [quasiCoherentDerivedPushforwardCongr, Iso.refl_hom, NatTrans.id_app,
    ObjectProperty.FullSubcategory.id_hom, CategoryTheory.Functor.map_id, Category.id_comp]
  exact Category.comp_id _

omit [CompactSpace Z] [QuasiSeparatedSpace Z] in
/-- Two morphisms `x y : P ⟶ g_*N` are equal once `x[0]` and `y[0]` agree after the unit
`g_*N[0] ⟶ Rg_*(N[0])`. -/
theorem singleFunctor_map_injective_of_comp {Z' : Scheme.{u}} (g : Z ⟶ Z') (N : Z.Modules)
    {P : Z'.Modules} (x y : P ⟶ (Scheme.Modules.pushforward g).obj N)
    (h : (singleFunctor Z'.Modules 0).map x ≫ singlePushforwardUnit g N =
      (singleFunctor Z'.Modules 0).map y ≫ singlePushforwardUnit g N) : x = y := by
  have hH := congrArg (fun φ => (homologyFunctor Z'.Modules 0).map φ ≫
    (FiniteTrace.singleDerivedPushforwardHomologyIso g).hom.app N) h
  simp only [Functor.map_comp, Category.assoc,
    FiniteTrace.homology_map_singleDerivedUnit_comp_singleDerivedPushforwardHomologyIso] at hH
  have n₁ := (singleFunctorCompHomologyFunctorIso Z'.Modules 0).hom.naturality x
  have n₂ := (singleFunctorCompHomologyFunctorIso Z'.Modules 0).hom.naturality y
  simp only [Functor.comp_map, Functor.id_map] at n₁ n₂
  rw [n₁, n₂] at hH
  exact (Iso.cancel_iso_hom_left ((singleFunctorCompHomologyFunctorIso Z'.Modules 0).app P) x y).mp hH

/-- **`R(𝟙_Z)_* ≅ 𝟭` at `N[0]` is the identification `𝟙_*N = N`** through
`N[0] ⟶ R(𝟙_Z)_*(N[0])`. -/
theorem singlePushforwardUnit_comp_quasiCoherentDerivedPushforwardIdIsoOfComp (N : Z.Modules)
    [N.IsQuasicoherent] :
    singlePushforwardUnit (𝟙 Z) N ≫
        ((quasiCoherentDerivedPushforwardIdIsoOfComp Z).hom.app (singleQCoh N)).hom =
      (singleFunctor Z.Modules 0).map ((Scheme.Modules.pushforwardId Z).hom.app N) := by
  obtain ⟨σ, hσ⟩ : ∃ σ, (singleFunctor Z.Modules 0).map σ = singlePushforwardUnit (𝟙 Z) N ≫
      ((quasiCoherentDerivedPushforwardIdIsoOfComp Z).hom.app (singleQCoh N)).hom :=
    ⟨_, (singleFunctor Z.Modules 0).map_preimage _⟩
  have hA := Stacks.DerivedFunctor.singleDerivedUnit_comp (Scheme.Modules.pushforward (𝟙 Z))
    (Scheme.Modules.pushforward (𝟙 Z)) (Scheme.Modules.pushforward (𝟙 Z ≫ 𝟙 Z))
    (Scheme.Modules.pushforwardComp (𝟙 Z) (𝟙 Z)) (derivedPushforward (𝟙 Z))
    (derivedPushforwardUnit (𝟙 Z)) (derivedPushforward (𝟙 Z)) (derivedPushforwardUnit (𝟙 Z))
    (derivedPushforward (𝟙 Z ≫ 𝟙 Z)) (derivedPushforwardUnit (𝟙 Z ≫ 𝟙 Z))
    (derivedPushforwardCompIso (𝟙 Z) (𝟙 Z))
    (derivedPushforwardUnit_comp_derivedPushforwardCompIso_hom (𝟙 Z) (𝟙 Z)) N
  have hB := congrArg (fun φ => φ.hom)
    (quasiCoherentDerivedPushforwardCompIso_id_comp (𝟙 Z) (singleQCoh N))
  have hC := singlePushforwardUnit_comp_congr (Category.id_comp (𝟙 Z)) N
  have hn := Stacks.DerivedFunctor.singleDerivedUnit_naturality (Scheme.Modules.pushforward (𝟙 Z))
    (derivedPushforward (𝟙 Z)) (derivedPushforwardUnit (𝟙 Z)) σ
  have hB' : (derivedPushforwardCompIso (𝟙 Z) (𝟙 Z)).hom.app ((singleFunctor Z.Modules 0).obj N) ≫
      ((quasiCoherentDerivedPushforwardCongr (Category.id_comp (𝟙 Z))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app (singleQCoh N)).hom =
      (derivedPushforward (𝟙 Z)).map
        ((quasiCoherentDerivedPushforwardIdIsoOfComp Z).hom.app (singleQCoh N)).hom := hB
  have key : (singleFunctor Z.Modules 0).map
      ((Scheme.Modules.pushforwardComp (𝟙 Z) (𝟙 Z)).inv.app N ≫
        (Scheme.Modules.pushforward (𝟙 Z)).map (X := (Scheme.Modules.pushforward (𝟙 Z)).obj N)
          (Y := N) σ) ≫ singlePushforwardUnit (𝟙 Z) N =
      (singleFunctor Z.Modules 0).map
        ((Scheme.Modules.pushforwardCongr (Category.id_comp (𝟙 Z))).hom.app N) ≫
        singlePushforwardUnit (𝟙 Z) N := by
    rw [Functor.map_comp, Category.assoc, hn, hσ, Functor.map_comp, ← hB', ← hC]
    exact (reassoc_of% hA) _
  have hσ' := singleFunctor_map_injective_of_comp (𝟙 Z) N _ _ key
  have hσ'' : σ = (Scheme.Modules.pushforwardId Z).hom.app N := by
    ext U x
    refine (congrArg (fun φ => (Scheme.Modules.Hom.app φ U) x) hσ').trans ?_
    refine (congrArg (fun f => (ConcreteCategory.hom f) x)
      (Scheme.Modules.pushforwardCongr_hom_app_app (M := N) (Category.id_comp (𝟙 Z)) U)).trans ?_
    exact congrArg (fun f => (ConcreteCategory.hom f) x)
      ((congrArg N.presheaf.map (Subsingleton.elim _ (𝟙 _))).trans (N.presheaf.map_id _))
  rw [← hσ, hσ'']

end Single

section UnitSingle

variable {X T T₁ : Scheme.{u}} {i : X ⟶ T} {i₁ : X ⟶ T₁} [IsOpenImmersion i] [IsOpenImmersion i₁]
  {h : T ⟶ T₁} (sq : IsPullback i (𝟙 X) h i₁)

/-- The unit of `j^* ⊣ Rj_*` at `M[0]` is the unit of `j^* ⊣ j_*` at `M`, read through
`j_*(M|_U)[0] ⟶ Rj_*((M|_U)[0])`. -/
theorem derivedRestrictPushforwardAdjunction_unit_app_single {V Z : Scheme.{u}} (j : V ⟶ Z)
    [IsOpenImmersion j] (M : Z.Modules) :
    (OpenImmersion.derivedRestrictPushforwardAdjunction j).unit.app
        ((singleFunctor Z.Modules 0).obj M) =
      (singleFunctor Z.Modules 0).map ((Scheme.Modules.restrictAdjunction j).unit.app M) ≫
        singlePushforwardUnit j ((Scheme.Modules.restrictFunctor j).obj M) ≫
          (derivedPushforward j).map
            (((Scheme.Modules.restrictFunctor j).mapDerivedCategorySingleFunctor 0).inv.app M) := by
  rw [OpenImmersion.derivedRestrictPushforwardAdjunction_unit_eq_descendedUnit]
  exact Stacks.SmallDerivedCategory.descendedUnit_app_single _ _ _ M

/-- `w(X)[0] ⟶ Rw(X[0])` along equal morphisms. -/
theorem singlePushforwardUnit_comp_eqToHom {Z Z' : Scheme.{u}} {g₁ g₂ : Z ⟶ Z'} (e : g₁ = g₂)
    (N : Z.Modules) :
    singlePushforwardUnit g₁ N ≫
        (eqToIso (congrArg (fun g : Z ⟶ Z' => derivedPushforward g) e)).hom.app
          ((singleFunctor Z.Modules 0).obj N) =
      (singleFunctor Z'.Modules 0).map ((Scheme.Modules.pushforwardCongr e).hom.app N) ≫
        singlePushforwardUnit g₂ N := by
  subst e
  rw [pushforwardCongr_refl_hom_app_eq_id]
  simp

/-- `(h_*M)|_X ≅ M|_X` for the cartesian square, at `M`, with its type spelled through the two
restriction functors. -/
def restrictPushforwardIsoApp (M : T.Modules) :
    (Scheme.Modules.restrictFunctor i₁).obj ((Scheme.Modules.pushforward h).obj M) ≅
      (Scheme.Modules.restrictFunctor i).obj M :=
  (restrictPushforwardIsoOfIsPullback sq).app M

omit [IsOpenImmersion i] [IsOpenImmersion i₁] in
/-- Two composites of restriction maps of a presheaf on opens between the same opens agree. -/
theorem presheaf_map_map_apply {Z : Scheme.{u}} (F : Z.Opensᵒᵖ ⥤ Ab.{u}) {a b c d : Z.Opensᵒᵖ}
    (f₁ : a ⟶ b) (f₂ : b ⟶ c) (g₁ : a ⟶ d) (g₂ : d ⟶ c) (x : F.obj a) :
    F.map f₂ (F.map f₁ x) = F.map g₂ (F.map g₁ x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← F.map_comp, ← F.map_comp,
    Subsingleton.elim (f₁ ≫ f₂) (g₁ ≫ g₂)]

include sq in
/-- The unit of restriction along `i₁` at `h_*M`, followed by the restriction of `h_*M` along the
cartesian square, is `h_*` of the unit of restriction along `i`. -/
theorem pushforward_map_restrictAdjunction_unit_comp (M : T.Modules) :
    (Scheme.Modules.pushforward h).map ((Scheme.Modules.restrictAdjunction i).unit.app M) ≫
        (Scheme.Modules.pushforwardComp i h).hom.app _ ≫
          (Scheme.Modules.pushforwardCongr sq.w).hom.app _ ≫
            (Scheme.Modules.pushforwardComp (𝟙 X) i₁).inv.app _ =
      (Scheme.Modules.restrictAdjunction i₁).unit.app ((Scheme.Modules.pushforward h).obj M) ≫
        (Scheme.Modules.pushforward i₁).map ((restrictPushforwardIsoApp sq M).hom ≫
          (Scheme.Modules.pushforwardId X).inv.app ((Scheme.Modules.restrictFunctor i).obj M)) := by
  ext U x
  have hw : i ≫ h = i₁ := sq.w.trans (Category.id_comp _)
  have h₁ : i ''ᵁ (i₁ ⁻¹ᵁ U) ≤ i ''ᵁ (i ⁻¹ᵁ (h ⁻¹ᵁ U)) := by
    rw [← hw]; exact le_rfl
  refine Eq.trans (b := M.presheaf.map (homOfLE h₁).op
    (M.presheaf.map (homOfLE (i.image_preimage_le (h ⁻¹ᵁ U))).op x)) rfl ?_
  refine (presheaf_map_map_apply M.presheaf _ _
    ((TopologicalSpace.Opens.map h.base).map (homOfLE (i₁.image_preimage_le U))).op
    (homOfLE (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback sq.flip
      (i₁ ⁻¹ᵁ U)).le).op x).trans ?_
  rfl

omit [IsOpenImmersion i] [IsOpenImmersion i₁] in
/-- `derivedPushforwardSquareIso g' f' f g w` is `derivedPushforwardCompIso g' f`, followed by the
identification `R(g' ≫ f)_* = R(f' ≫ g)_*` and the inverse of `derivedPushforwardCompIso f' g`. -/
theorem derivedPushforwardSquareIso_eq {X' X'' Y' Y'' : Scheme.{u}} (g' : X' ⟶ X'')
    (f' : X' ⟶ Y') (f : X'' ⟶ Y'') (g : Y' ⟶ Y'') (w : g' ≫ f = f' ≫ g) :
    derivedPushforwardSquareIso g' f' f g w = derivedPushforwardCompIso g' f ≪≫
      eqToIso (congrArg (fun h : X' ⟶ Y'' => derivedPushforward h) w) ≪≫
        (derivedPushforwardCompIso f' g).symm := by
  unfold derivedPushforwardSquareIso; rfl

omit [IsOpenImmersion i] [IsOpenImmersion i₁] in
/-- The component of `A ≪≫ B ≪≫ E.symm` at `K` is `A.hom.app K ≫ B.hom.app K ≫ E.inv.app K`. -/
theorem iso_trans_trans_symm_hom_app {C D : Type*} [Category C] [Category D] {F G H I : C ⥤ D}
    (A : F ≅ G) (B : G ≅ H) (E : I ≅ H) (K : C) :
    (A ≪≫ B ≪≫ E.symm).hom.app K = A.hom.app K ≫ B.hom.app K ≫ E.inv.app K := rfl

omit [IsOpenImmersion i] [IsOpenImmersion i₁] in
/-- The component at `K` of `derivedPushforwardSquareIso g' f' f g w` is that of
`derivedPushforwardCompIso g' f`, followed by the identification `R(g' ≫ f)_* = R(f' ≫ g)_*` and
the inverse of `derivedPushforwardCompIso f' g`. -/
theorem derivedPushforwardSquareIso_hom_app {X' X'' Y' Y'' : Scheme.{u}} (g' : X' ⟶ X'')
    (f' : X' ⟶ Y') (f : X'' ⟶ Y'') (g : Y' ⟶ Y'') (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory X'.Modules) :
    (derivedPushforwardSquareIso g' f' f g w).hom.app K =
      (derivedPushforwardCompIso g' f).hom.app K ≫
        (eqToIso (congrArg (fun h : X' ⟶ Y'' => derivedPushforward h) w)).hom.app K ≫
          (derivedPushforwardCompIso f' g).inv.app K := by
  rw [derivedPushforwardSquareIso_eq]
  exact iso_trans_trans_symm_hom_app _ _ _ K

omit [IsOpenImmersion i] [IsOpenImmersion i₁] in
/-- Naturality of `τ : F₁ ⋙ G₁ ⟶ F₂ ⋙ G₂` at `f`, with the composite functors unfolded. -/
theorem natTrans_naturality_comp {C D D' E : Type*} [Category C] [Category D] [Category D']
    [Category E] {F₁ : C ⥤ D} {G₁ : D ⥤ E} {F₂ : C ⥤ D'} {G₂ : D' ⥤ E}
    (τ : F₁ ⋙ G₁ ⟶ F₂ ⋙ G₂) {X Y : C}
    (f : X ⟶ Y) : G₁.map (F₁.map f) ≫ τ.app Y = τ.app X ≫ G₂.map (F₂.map f) :=
  τ.naturality f

omit [IsOpenImmersion i] [IsOpenImmersion i₁] in
private theorem unitSH_chase {E C : Type*} [Category E] [Category C] (Fs : C ⥤ E)
    {c0 c1 c2 c3 c4 c5 : C}
    {P1 P1a P1b P2 P3 P3' Q1 Q2 R0 R1 W : E}
    (uh : Fs.obj c0 ⟶ P1) (Dη : P1 ⟶ P2) (σA : P2 ⟶ P3)
    (Dsη : P1 ⟶ P1a) (Dui : P1a ⟶ P1b) (Dκ : P1b ⟶ P2) (hDη : Dη = Dsη ≫ Dui ≫ Dκ)
    (a : c0 ⟶ c1) (uhP : Fs.obj c1 ⟶ P1a) (hn : Fs.map a ≫ uhP = uh ≫ Dsη)
    (σB : P1b ⟶ P3') (Dκ' : P3' ⟶ P3) (hσ : Dκ ≫ σA = σB ≫ Dκ')
    (c1' : P1b ⟶ Q1) (e : Q1 ⟶ Q2) (c2' : Q2 ⟶ P3') (hσdef : σB = c1' ≫ e ≫ c2')
    (b : c1 ⟶ c2) (u_ih : Fs.obj c2 ⟶ Q1) (hK1a : uhP ≫ Dui ≫ c1' = Fs.map b ≫ u_ih)
    (c : c2 ⟶ c3) (u_1i : Fs.obj c3 ⟶ Q2) (heq : u_ih ≫ e = Fs.map c ≫ u_1i)
    (d : c3 ⟶ c4) (u_i₁ : Fs.obj c4 ⟶ R1) (Du1 : R1 ⟶ P3')
    (hK1b : u_1i ≫ c2' = Fs.map d ≫ u_i₁ ≫ Du1)
    (e' : c0 ⟶ c5) (φ : c5 ⟶ c4) (hS : a ≫ b ≫ c ≫ d = e' ≫ φ)
    (u₁M : Fs.obj c5 ⟶ R0) (Dsφ : R0 ⟶ R1) (hn₁ : Fs.map φ ≫ u_i₁ = u₁M ≫ Dsφ)
    (η₁ : Fs.obj c0 ⟶ W) (Dρ : W ⟶ P3) (Dκ₁ : R0 ⟶ W) (hη₁ : η₁ = Fs.map e' ≫ u₁M ≫ Dκ₁)
    (hDρ : Dκ₁ ≫ Dρ = Dsφ ≫ Du1 ≫ Dκ') :
    uh ≫ Dη ≫ σA = η₁ ≫ Dρ := by
  rw [hDη, hη₁]
  calc uh ≫ (Dsη ≫ Dui ≫ Dκ) ≫ σA = (uh ≫ Dsη) ≫ Dui ≫ (Dκ ≫ σA) := by
        simp only [Category.assoc]
    _ = Fs.map a ≫ (uhP ≫ Dui ≫ c1') ≫ e ≫ c2' ≫ Dκ' := by
        rw [← hn, hσ, hσdef]; simp only [Category.assoc]
    _ = Fs.map a ≫ Fs.map b ≫ Fs.map c ≫ Fs.map d ≫ u_i₁ ≫ Du1 ≫ Dκ' := by
        rw [hK1a]; simp only [Category.assoc]; rw [reassoc_of% heq, reassoc_of% hK1b]
    _ = Fs.map (a ≫ b ≫ c ≫ d) ≫ u_i₁ ≫ Du1 ≫ Dκ' := by simp only [Functor.map_comp, Category.assoc]
    _ = _ := by
        rw [hS, Functor.map_comp]; simp only [Category.assoc]; rw [reassoc_of% hn₁, hDρ]

include sq in
/-- **The base change map of direct images along the cartesian square, at `M[0]`**: transposed
along `i₁^* ⊣ Ri₁_*`, `Rh_*(M[0]) ⟶ Rh_* Ri_* i^*(M[0]) ≅ Ri₁_* R𝟙_* i^*(M[0])` restricts on
`h_*M[0]` to the restriction `(h_*M)|_X ≅ M|_X` of direct images. -/
theorem singlePushforwardUnit_comp_unit_comp_squareIso (M : T.Modules) :
    singlePushforwardUnit h M ≫
        (derivedPushforward h).map ((OpenImmersion.derivedRestrictPushforwardAdjunction i).unit.app
          ((singleFunctor T.Modules 0).obj M)) ≫
        (derivedPushforwardSquareIso i (𝟙 X) h i₁ sq.w).hom.app
          ((OpenImmersion.derivedRestrict i).obj ((singleFunctor T.Modules 0).obj M)) =
      (OpenImmersion.derivedRestrictPushforwardAdjunction i₁).unit.app
          ((singleFunctor T₁.Modules 0).obj ((Scheme.Modules.pushforward h).obj M)) ≫
        (derivedPushforward i₁).map
          (((Scheme.Modules.restrictFunctor i₁).mapDerivedCategorySingleFunctor 0).hom.app
              ((Scheme.Modules.pushforward h).obj M) ≫
            (singleFunctor X.Modules 0).map ((restrictPushforwardIsoApp sq M).hom ≫
              (Scheme.Modules.pushforwardId X).inv.app ((Scheme.Modules.restrictFunctor i).obj M)) ≫
            singlePushforwardUnit (𝟙 X) ((Scheme.Modules.restrictFunctor i).obj M) ≫
            (derivedPushforward (𝟙 X)).map
              (((Scheme.Modules.restrictFunctor i).mapDerivedCategorySingleFunctor 0).inv.app
                M)) := by
  have hS0 := pushforward_map_restrictAdjunction_unit_comp sq M
  generalize (restrictPushforwardIsoApp sq M).hom ≫
    (Scheme.Modules.pushforwardId X).inv.app ((Scheme.Modules.restrictFunctor i).obj M) = βθ
    at hS0 ⊢
  have hK1a := Stacks.DerivedFunctor.singleDerivedUnit_comp (Scheme.Modules.pushforward i)
    (Scheme.Modules.pushforward h) (Scheme.Modules.pushforward (i ≫ h))
    (Scheme.Modules.pushforwardComp i h) (derivedPushforward h) (derivedPushforwardUnit h)
    (derivedPushforward i) (derivedPushforwardUnit i) (derivedPushforward (i ≫ h))
    (derivedPushforwardUnit (i ≫ h)) (derivedPushforwardCompIso i h)
    (derivedPushforwardUnit_comp_derivedPushforwardCompIso_hom i h)
    ((Scheme.Modules.restrictFunctor i).obj M)
  have hK1b := Stacks.DerivedFunctor.singleDerivedUnit_comp (Scheme.Modules.pushforward (𝟙 X))
    (Scheme.Modules.pushforward i₁) (Scheme.Modules.pushforward (𝟙 X ≫ i₁))
    (Scheme.Modules.pushforwardComp (𝟙 X) i₁) (derivedPushforward i₁) (derivedPushforwardUnit i₁)
    (derivedPushforward (𝟙 X)) (derivedPushforwardUnit (𝟙 X)) (derivedPushforward (𝟙 X ≫ i₁))
    (derivedPushforwardUnit (𝟙 X ≫ i₁)) (derivedPushforwardCompIso (𝟙 X) i₁)
    (derivedPushforwardUnit_comp_derivedPushforwardCompIso_hom (𝟙 X) i₁)
    ((Scheme.Modules.restrictFunctor i).obj M)
  refine unitSH_chase (singleFunctor T₁.Modules 0)
    (Dsη := (derivedPushforward h).map ((singleFunctor T.Modules 0).map
      ((Scheme.Modules.restrictAdjunction i).unit.app M)))
    (Dui := (derivedPushforward h).map
      (singlePushforwardUnit i ((Scheme.Modules.restrictFunctor i).obj M)))
    (Dκ := (derivedPushforward h).map ((derivedPushforward i).map
      (((Scheme.Modules.restrictFunctor i).mapDerivedCategorySingleFunctor 0).inv.app M)))
    (Du1 := (derivedPushforward i₁).map
      (singlePushforwardUnit (𝟙 X) ((Scheme.Modules.restrictFunctor i).obj M)))
    (Dsφ := (derivedPushforward i₁).map ((singleFunctor X.Modules 0).map βθ))
    (Dκ₁ := (derivedPushforward i₁).map
      (((Scheme.Modules.restrictFunctor i₁).mapDerivedCategorySingleFunctor 0).inv.app
        ((Scheme.Modules.pushforward h).obj M)))
    (uhP := singlePushforwardUnit h
      ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.restrictFunctor i).obj M)))
    (σB := (derivedPushforwardSquareIso i (𝟙 X) h i₁ sq.w).hom.app
      ((singleFunctor X.Modules 0).obj ((Scheme.Modules.restrictFunctor i).obj M)))
    (Dκ' := (derivedPushforward i₁).map ((derivedPushforward (𝟙 X)).map
      (((Scheme.Modules.restrictFunctor i).mapDerivedCategorySingleFunctor 0).inv.app M)))
    (c1' := (derivedPushforwardCompIso i h).hom.app
      ((singleFunctor X.Modules 0).obj ((Scheme.Modules.restrictFunctor i).obj M)))
    (e := (eqToIso (congrArg (fun g : X ⟶ T₁ => derivedPushforward g) sq.w)).hom.app
      ((singleFunctor X.Modules 0).obj ((Scheme.Modules.restrictFunctor i).obj M)))
    (c2' := (derivedPushforwardCompIso (𝟙 X) i₁).inv.app
      ((singleFunctor X.Modules 0).obj ((Scheme.Modules.restrictFunctor i).obj M)))
    (u_ih := singlePushforwardUnit (i ≫ h) ((Scheme.Modules.restrictFunctor i).obj M))
    (u_1i := singlePushforwardUnit (𝟙 X ≫ i₁) ((Scheme.Modules.restrictFunctor i).obj M))
    (u_i₁ := singlePushforwardUnit i₁
      ((Scheme.Modules.pushforward (𝟙 X)).obj ((Scheme.Modules.restrictFunctor i).obj M)))
    (u₁M := singlePushforwardUnit i₁
      ((Scheme.Modules.restrictFunctor i₁).obj ((Scheme.Modules.pushforward h).obj M)))
    (hDη := ?_) (hn := ?_) (hσ := ?_) (hσdef := ?_) (heq := ?_) (hn₁ := ?_) (hη₁ := ?_)
    (hK1a := ?_) (hK1b := ?_) (hS := hS0) (hDρ := ?_)
  · rw [derivedRestrictPushforwardAdjunction_unit_app_single, Functor.map_comp, Functor.map_comp]
  · exact Stacks.DerivedFunctor.singleDerivedUnit_naturality (Scheme.Modules.pushforward h)
      (derivedPushforward h) (derivedPushforwardUnit h)
      ((Scheme.Modules.restrictAdjunction i).unit.app M)
  · exact natTrans_naturality_comp (F₁ := derivedPushforward i) (G₁ := derivedPushforward h)
      (F₂ := derivedPushforward (𝟙 X)) (G₂ := derivedPushforward i₁)
      (derivedPushforwardSquareIso i (𝟙 X) h i₁ sq.w).hom
      (X := (singleFunctor X.Modules 0).obj ((Scheme.Modules.restrictFunctor i).obj M))
      (Y := (OpenImmersion.derivedRestrict i).obj ((singleFunctor T.Modules 0).obj M))
      (((Scheme.Modules.restrictFunctor i).mapDerivedCategorySingleFunctor 0).inv.app M)
  · exact derivedPushforwardSquareIso_hom_app _ _ _ _ _ _
  · rw [show singlePushforwardUnit (i ≫ h) ((Scheme.Modules.restrictFunctor i).obj M) = _ from
      hK1a.symm]
    simp
  · exact singlePushforwardUnit_comp_eqToHom sq.w _
  · rw [show singlePushforwardUnit (𝟙 X ≫ i₁) ((Scheme.Modules.restrictFunctor i).obj M) = _ from
      hK1b.symm]
    simp
  · exact Stacks.DerivedFunctor.singleDerivedUnit_naturality
      (Scheme.Modules.pushforward i₁) (derivedPushforward i₁) (derivedPushforwardUnit i₁) _
  · exact derivedRestrictPushforwardAdjunction_unit_app_single i₁ _
  · simp only [← Functor.map_comp, Iso.inv_hom_id_app_assoc]

end UnitSingle

section BaseChangeSingle

variable {X T T₁ : Scheme.{u}} {i : X ⟶ T} {i₁ : X ⟶ T₁} [IsOpenImmersion i] [IsOpenImmersion i₁]
  {h : T ⟶ T₁} (sq : IsPullback i (𝟙 X) h i₁)
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace T] [QuasiSeparatedSpace T]
  [CompactSpace T₁] [QuasiSeparatedSpace T₁] [QuasiCompact h] [QuasiSeparated h]

variable (i i₁ h) in
/-- `i₁^* Rh_* N ⟶ R(𝟙_X)_* i^* N`, the transpose of `Rh_*(N ⟶ Ri_* i^* N) ≅ Ri₁_* R(𝟙_X)_* i^* N`
along `i₁^* ⊣ Ri₁_*`. -/
abbrev restrictPushforwardBaseChange (w : i ≫ h = 𝟙 X ≫ i₁) (N : quasiCoherentDerivedCategory T) :
    (OpenImmersion.restrictedDerivedRestrict i₁).obj
      ((quasiCoherentDerivedPushforward h
        (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).obj N) ⟶
    (OpenImmersion.restrictedDerivedRestrict i).obj N :=
  (OpenImmersion.restrictedDerivedRestrict i₁).map
      ((quasiCoherentDerivedPushforward h
          (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).map
        ((OpenImmersion.quasiCoherentDerivedRestrictAdjunction i
          (OpenImmersion.isQuasicoherent_homology_derivedRestrict i)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs i)).unit.app N)) ≫
    (OpenImmersion.restrictedDerivedRestrict i₁).map
      ((quasiCoherentDerivedPushforwardSquareIso i (𝟙 X) h i₁
        (isQuasicoherent_homology_derivedPushforward_of_qcqs i)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs h)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs i₁) w).hom.app
          ((OpenImmersion.restrictedDerivedRestrict i).obj N)) ≫
    (OpenImmersion.quasiCoherentDerivedRestrictAdjunction i₁
          (OpenImmersion.isQuasicoherent_homology_derivedRestrict i₁)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs i₁)).counit.app
      ((quasiCoherentDerivedPushforward (𝟙 X)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X))).obj
          ((OpenImmersion.restrictedDerivedRestrict i).obj N)) ≫
    (quasiCoherentDerivedPushforwardIdIsoOfComp X).hom.app
      ((OpenImmersion.restrictedDerivedRestrict i).obj N)

/-- Restriction to an open on `D_QCoh` is restriction on the ambient derived categories. -/
theorem restrictedDerivedRestrict_map_hom {V Z : Scheme.{u}} (j : V ⟶ Z) [IsOpenImmersion j]
    {N N' : quasiCoherentDerivedCategory Z} (f : N ⟶ N') :
      ((OpenImmersion.restrictedDerivedRestrict j).map f).hom =
        (OpenImmersion.derivedRestrict j).map f.hom := rfl

omit [IsOpenImmersion i] [IsOpenImmersion i₁] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace T] [QuasiSeparatedSpace T] [CompactSpace T₁] [QuasiSeparatedSpace T₁]
  [QuasiCompact h] [QuasiSeparated h] in
/-- Transposing `u ≫ x ≫ y = η ≫ R(g)` along `L ⊣ R`. -/
theorem adjunction_counit_chase {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R)
    {a b b' : C} {d e : D} (u : a ⟶ b) (x : b ⟶ b') (y : b' ⟶ R.obj d) (g : L.obj a ⟶ d)
    (hx : u ≫ x ≫ y = adj.unit.app a ≫ R.map g) (k : d ⟶ e) (r : L.obj a ⟶ e) (hr : g ≫ k = r) :
    L.map u ≫ L.map x ≫ L.map y ≫ adj.counit.app d ≫ k = r := by
  have h := congrArg (fun z => L.map z ≫ adj.counit.app d ≫ k) hx
  simp only [Functor.map_comp, Category.assoc, Adjunction.counit_naturality_assoc,
    Adjunction.left_triangle_components_assoc] at h
  exact h.trans hr

/-- **`i₁^*(h_*M[0] ⟶ Rh_*(M[0]))` followed by `i₁^*Rh_*(M[0]) ⟶ i^*(M[0])`** is
`i₁^*((h_*M)[0]) ≅ ((h_*M)|_X)[0] ≅ (M|_X)[0] ≅ i^*(M[0])`, by the restriction
`(h_*M)|_X ≅ M|_X` of direct images along the cartesian square. -/
theorem restrict_map_singlePushforwardUnit_comp_restrictPushforwardBaseChange (M : T.Modules)
    [M.IsQuasicoherent] :
    (OpenImmersion.derivedRestrict i₁).map (singlePushforwardUnit h M) ≫
        (restrictPushforwardBaseChange i i₁ h sq.w (singleQCoh M)).hom =
      ((Scheme.Modules.restrictFunctor i₁).mapDerivedCategorySingleFunctor 0).hom.app
          ((Scheme.Modules.pushforward h).obj M) ≫
        (singleFunctor X.Modules 0).map (restrictPushforwardIsoApp sq M).hom ≫
        ((Scheme.Modules.restrictFunctor i).mapDerivedCategorySingleFunctor 0).inv.app M := by
  have hP2 := singlePushforwardUnit_comp_unit_comp_squareIso sq M
  have hM : ((Scheme.Modules.restrictFunctor i).obj M).IsQuasicoherent := inferInstance
  have hP3 := singlePushforwardUnit_comp_quasiCoherentDerivedPushforwardIdIsoOfComp
    ((Scheme.Modules.restrictFunctor i).obj M)
  have hB : (restrictPushforwardBaseChange i i₁ h sq.w (singleQCoh M)).hom =
      (OpenImmersion.derivedRestrict i₁).map ((derivedPushforward h).map
        ((OpenImmersion.derivedRestrictPushforwardAdjunction i).unit.app
          ((singleFunctor T.Modules 0).obj M))) ≫
      (OpenImmersion.derivedRestrict i₁).map
        ((derivedPushforwardSquareIso i (𝟙 X) h i₁ sq.w).hom.app
          ((OpenImmersion.derivedRestrict i).obj ((singleFunctor T.Modules 0).obj M))) ≫
      (OpenImmersion.derivedRestrictPushforwardAdjunction i₁).counit.app
        ((derivedPushforward (𝟙 X)).obj
          ((OpenImmersion.derivedRestrict i).obj ((singleFunctor T.Modules 0).obj M))) ≫
      ((quasiCoherentDerivedPushforwardIdIsoOfComp X).hom.app
        ((OpenImmersion.restrictedDerivedRestrict i).obj (singleQCoh M))).hom := by
    have hu : ((OpenImmersion.quasiCoherentDerivedRestrictAdjunction i
          (OpenImmersion.isQuasicoherent_homology_derivedRestrict i)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs i)).unit.app (singleQCoh M)).hom =
        (OpenImmersion.derivedRestrictPushforwardAdjunction i).unit.app
          ((singleFunctor T.Modules 0).obj M) :=
      map_liftDerivedRestrictPushforwardAdjunction_unit_app i _ _ _ _ _
    have hc : ((OpenImmersion.quasiCoherentDerivedRestrictAdjunction i₁
          (OpenImmersion.isQuasicoherent_homology_derivedRestrict i₁)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs i₁)).counit.app
          ((quasiCoherentDerivedPushforward (𝟙 X)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X))).obj
              ((OpenImmersion.restrictedDerivedRestrict i).obj (singleQCoh M)))).hom =
        (OpenImmersion.derivedRestrictPushforwardAdjunction i₁).counit.app
          ((derivedPushforward (𝟙 X)).obj
            ((OpenImmersion.derivedRestrict i).obj ((singleFunctor T.Modules 0).obj M))) :=
      map_liftDerivedRestrictPushforwardAdjunction_counit_app i₁ _ _ _ _ _
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.FullSubcategory.comp_hom]
    refine congrArg₂ (· ≫ ·) ?_ ?_
    · exact congrArg (OpenImmersion.derivedRestrict i₁).map (congrArg (derivedPushforward h).map hu)
    · refine congrArg₂ (· ≫ ·) ?_ (congrArg (· ≫ _) hc)
      exact (restrictedDerivedRestrict_map_hom i₁ _).trans
        (congrArg (OpenImmersion.derivedRestrict i₁).map
          ((quasiCoherentDerivedPushforwardSquareIso_hom_app_hom _ _ _ _ _ _ _ _ _ _).trans
            (eq_of_heq (by heq_congr))))
  rw [hB]
  refine adjunction_counit_chase (OpenImmersion.derivedRestrictPushforwardAdjunction i₁)
    _ _ _ _ hP2 _ _ ?_
  have hn := congrArg InducedCategory.Hom.hom
    ((quasiCoherentDerivedPushforwardIdIsoOfComp X).hom.naturality
      (ObjectProperty.homMk (X := singleQCoh ((Scheme.Modules.restrictFunctor i).obj M))
        (Y := (OpenImmersion.restrictedDerivedRestrict i).obj (singleQCoh M))
        (((Scheme.Modules.restrictFunctor i).mapDerivedCategorySingleFunctor 0).inv.app M)))
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom] at hn
  have hn' : (derivedPushforward (𝟙 X)).map
        (((Scheme.Modules.restrictFunctor i).mapDerivedCategorySingleFunctor 0).inv.app M) ≫
      ((quasiCoherentDerivedPushforwardIdIsoOfComp X).hom.app
        ((OpenImmersion.restrictedDerivedRestrict i).obj (singleQCoh M))).hom =
      ((quasiCoherentDerivedPushforwardIdIsoOfComp X).hom.app
        (singleQCoh ((Scheme.Modules.restrictFunctor i).obj M))).hom ≫
        ((Scheme.Modules.restrictFunctor i).mapDerivedCategorySingleFunctor 0).inv.app M := hn
  simp only [Category.assoc]
  rw [hn', reassoc_of% hP3, ← Functor.map_comp_assoc, Category.assoc, Iso.inv_hom_id_app]
  exact congrArg (_ ≫ ·) (congrArg (· ≫ _) (congrArg (singleFunctor X.Modules 0).map
    (Category.comp_id _)))

omit [IsOpenImmersion i] [IsOpenImmersion i₁] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace T] [QuasiSeparatedSpace T] [CompactSpace T₁] [QuasiSeparatedSpace T₁]
  [QuasiCompact h] [QuasiSeparated h] in
/-- The diagram chase of `restrict_map_singleDerivedPushforwardHomologyIso_inv_comp`. -/
theorem restrict_homology_base_change_chase {E C : Type*} [Category E] [Category C] (G : C ⥤ E)
    {P HP0 HRh : C} {HdRRh HdRP0 Hi W Mx Q1 Q2 : E}
    (s1i : P ⟶ HP0) (s1 : HP0 ⟶ P) (hs1 : s1i ≫ s1 = 𝟙 P) (Hu : HP0 ⟶ HRh) (r0i : P ⟶ HRh)
    (hr0 : r0i = s1i ≫ Hu) (R1i_R : G.obj HRh ⟶ HdRRh) (R1i_P : G.obj HP0 ⟶ HdRP0)
    (R1h_P : HdRP0 ⟶ G.obj HP0) (hR1 : R1i_P ≫ R1h_P = 𝟙 _) (Hdu : HdRP0 ⟶ HdRRh)
    (hnat : G.map Hu ≫ R1i_R = R1i_P ≫ Hdu) (HB : HdRRh ⟶ Hi) (Ri : Hi ⟶ W) (rs : W ⟶ Mx)
    (Hk1 : HdRP0 ⟶ Q1) (Hsb : Q1 ⟶ Q2) (Hki : Q2 ⟶ Hi) (hstar : Hdu ≫ HB = Hk1 ≫ Hsb ≫ Hki)
    (scM : Q2 ⟶ Mx) (hf4 : Hki ≫ Ri ≫ rs = scM) (scP : Q1 ⟶ G.obj P) (β : G.obj P ⟶ Mx)
    (hf5 : Hsb ≫ scM = scP ≫ β) (hf6 : Hk1 ≫ scP = R1h_P ≫ G.map s1) :
    G.map r0i ≫ R1i_R ≫ HB ≫ Ri ≫ rs = β := by
  subst hr0
  rw [G.map_comp, Category.assoc, reassoc_of% hnat, reassoc_of% hstar, hf4, hf5, reassoc_of% hf6,
    reassoc_of% hR1, ← G.map_comp_assoc, hs1, G.map_id, Category.id_comp]

/-- **On `H⁰`, `i₁^*Rh_*(M[0]) ⟶ i^*(M[0])` is the restriction `(h_*M)|_X ≅ M|_X`** of direct
images along the cartesian square, read through `R⁰h_* = h_*`, `H⁰(i^*(-)) = H⁰(-)|_X` and
`H⁰(M[0]) = M`. -/
theorem restrict_map_singleDerivedPushforwardHomologyIso_inv_comp (M : T.Modules)
    [M.IsQuasicoherent] :
    (Scheme.Modules.restrictFunctor i₁).map
        ((FiniteTrace.singleDerivedPushforwardHomologyIso h).inv.app M) ≫
      (((Scheme.Modules.restrictFunctor i₁).mapDerivedCategoryHomologyIso 0).inv.app
        ((derivedPushforward h).obj ((singleFunctor T.Modules 0).obj M))) ≫
      (homologyFunctor X.Modules 0).map
        (restrictPushforwardBaseChange i i₁ h sq.w (singleQCoh M)).hom ≫
      (((Scheme.Modules.restrictFunctor i).mapDerivedCategoryHomologyIso 0).hom.app
        ((singleFunctor T.Modules 0).obj M)) ≫
      (Scheme.Modules.restrictFunctor i).map
        ((singleFunctorCompHomologyFunctorIso T.Modules 0).hom.app M) =
    (restrictPushforwardIsoApp sq M).hom := by
  have hstar := congrArg (homologyFunctor X.Modules 0).map
    (restrict_map_singlePushforwardUnit_comp_restrictPushforwardBaseChange sq M)
  simp only [Functor.map_comp] at hstar
  have hf1 :=
    FiniteTrace.homology_map_singleDerivedUnit_comp_singleDerivedPushforwardHomologyIso h M
  have hf4 := Stacks.MapDerivedHomologyCompat.homology_map_mapDerivedCategorySingleFunctor_hom_app
    (Scheme.Modules.restrictFunctor i) M
  have hf6 := Stacks.MapDerivedHomologyCompat.homology_map_mapDerivedCategorySingleFunctor_hom_app
    (Scheme.Modules.restrictFunctor i₁) ((Scheme.Modules.pushforward h).obj M)
  have hf5 := (singleFunctorCompHomologyFunctorIso X.Modules 0).hom.naturality
    (restrictPushforwardIsoApp sq M).hom
  have hnat := natTrans_naturality_comp
    ((Scheme.Modules.restrictFunctor i₁).mapDerivedCategoryHomologyIso 0).inv
    (singlePushforwardUnit h M)
  refine restrict_homology_base_change_chase (Scheme.Modules.restrictFunctor i₁)
    (s1i := (singleFunctorCompHomologyFunctorIso T₁.Modules 0).inv.app
      ((Scheme.Modules.pushforward h).obj M))
    (s1 := (singleFunctorCompHomologyFunctorIso T₁.Modules 0).hom.app
      ((Scheme.Modules.pushforward h).obj M))
    (Hu := (homologyFunctor T₁.Modules 0).map (singlePushforwardUnit h M))
    (R1i_P := ((Scheme.Modules.restrictFunctor i₁).mapDerivedCategoryHomologyIso 0).inv.app
      ((singleFunctor T₁.Modules 0).obj ((Scheme.Modules.pushforward h).obj M)))
    (R1h_P := ((Scheme.Modules.restrictFunctor i₁).mapDerivedCategoryHomologyIso 0).hom.app
      ((singleFunctor T₁.Modules 0).obj ((Scheme.Modules.pushforward h).obj M)))
    (Hdu := (homologyFunctor X.Modules 0).map
      ((OpenImmersion.derivedRestrict i₁).map (singlePushforwardUnit h M)))
    (Hk1 := (homologyFunctor X.Modules 0).map
      (((Scheme.Modules.restrictFunctor i₁).mapDerivedCategorySingleFunctor 0).hom.app
        ((Scheme.Modules.pushforward h).obj M)))
    (Hsb := (homologyFunctor X.Modules 0).map
      ((singleFunctor X.Modules 0).map (restrictPushforwardIsoApp sq M).hom))
    (Hki := (homologyFunctor X.Modules 0).map
      (((Scheme.Modules.restrictFunctor i).mapDerivedCategorySingleFunctor 0).inv.app M))
    (scM := (singleFunctorCompHomologyFunctorIso X.Modules 0).hom.app
      ((Scheme.Modules.restrictFunctor i).obj M))
    (scP := (singleFunctorCompHomologyFunctorIso X.Modules 0).hom.app
      ((Scheme.Modules.restrictFunctor i₁).obj ((Scheme.Modules.pushforward h).obj M)))
    (hs1 := Iso.inv_hom_id_app _ _) (hr0 := ?_) (hR1 := Iso.inv_hom_id_app _ _)
    (hnat := hnat) (hstar := hstar) (hf4 := ?_) (hf5 := hf5) (hf6 := hf6)
  · rw [← Iso.cancel_iso_hom_right _ _ ((FiniteTrace.singleDerivedPushforwardHomologyIso h).app M),
      Iso.app_hom,
      Iso.inv_hom_id_app, Category.assoc, hf1, Iso.inv_hom_id_app]
    rfl
  · rw [← hf4, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    exact (congrArg (· ≫ _) ((homologyFunctor X.Modules 0).map_id _)).trans (Category.id_comp _)

end BaseChangeSingle

section TraceRestriction

variable {X T T₁ : Scheme.{u}} {i : X ⟶ T} {i₁ : X ⟶ T₁} [IsOpenImmersion i] [IsOpenImmersion i₁]
  {h : T ⟶ T₁} (sq : IsPullback i (𝟙 X) h i₁)
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace T] [QuasiSeparatedSpace T]
  [CompactSpace T₁] [QuasiSeparatedSpace T₁]

omit [IsOpenImmersion i] [IsOpenImmersion i₁] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace T] [QuasiSeparatedSpace T] [CompactSpace T₁] [QuasiSeparatedSpace T₁] in
/-- `R(γ) ≫ ε = e ≫ γ ≫ (e⁻¹ ≫ ε)` for an isomorphism `e` natural against `γ`. -/
theorem iso_natural_chase {C : Type*} [Category C] {Q Q' W W' Z : C} (Rγ : Q ⟶ Q') (ε : Q' ⟶ Z)
    (e : Q ⟶ W) (γ : W ⟶ W') (e' : Q' ⟶ W') (ei : W' ⟶ Q') (hn : Rγ ≫ e' = e ≫ γ)
    (hei : e' ≫ ei = 𝟙 _) (idI : W' ⟶ Z) (hid : idI = ei ≫ ε) : Rγ ≫ ε = e ≫ γ ≫ idI := by
  rw [hid, ← reassoc_of% hn, reassoc_of% hei]

/-- On `D_QCoh`, `i₁^*(Rh_* a_h K ⟶ K)` is `i₁^*Rh_* a_h K ⟶ i^* a_h K` followed by the map of
Tag 0A9L and `a_{𝟙} ≅ 𝟭`. -/
theorem restrict_map_twistedAdj_counit_app [IsProper h] (K : quasiCoherentDerivedCategory T₁) :
    (OpenImmersion.restrictedDerivedRestrict i₁).map ((FiniteTrace.twistedAdj h).counit.app K) =
      restrictPushforwardBaseChange i i₁ h sq.w ((FiniteTrace.twisted h).obj K) ≫
        (twistedInverseImageRestrictionMapOfIsPullback h i₁ i sq).app K ≫
        (twistedInverseImageIdIsoOfComp X).hom.app
          ((OpenImmersion.restrictedDerivedRestrict i₁).obj K) := by
  have h1 := map_counit_eq_restrictionMap
    (OpenImmersion.quasiCoherentDerivedRestrictAdjunction i
      (OpenImmersion.isQuasicoherent_homology_derivedRestrict i)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs i))
    (OpenImmersion.quasiCoherentDerivedRestrictAdjunction i₁
      (OpenImmersion.isQuasicoherent_homology_derivedRestrict i₁)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs i₁))
    (FiniteTrace.twistedAdj h) (FiniteTrace.twistedAdj (𝟙 X))
    (quasiCoherentDerivedPushforwardSquareIso i (𝟙 X) h i₁
      (isQuasicoherent_homology_derivedPushforward_of_qcqs i)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs h)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X))
      (isQuasicoherent_homology_derivedPushforward_of_qcqs i₁) sq.w).hom
    (twistedInverseImagePushforwardBaseChange i (𝟙 X) h i₁
      (isQuasicoherent_homology_derivedPushforward_of_qcqs i)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs h)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X))
      (isQuasicoherent_homology_derivedPushforward_of_qcqs i₁) sq)
    (fun N => mateEquiv_counit _ _ _ N) K
    ((twistedInverseImageRestrictionMapOfIsPullback h i₁ i sq).app K)
    (by simp [OpenImmersion.twistedInverseImageRestrictionMap])
  have h2 := twistedInverseImageIdIsoOfComp_hom_app X
    ((OpenImmersion.restrictedDerivedRestrict i₁).obj K)
  have h3 := (quasiCoherentDerivedPushforwardIdIsoOfComp X).hom.naturality
    ((twistedInverseImageRestrictionMapOfIsPullback h i₁ i sq).app K)
  have key : (quasiCoherentDerivedPushforward (𝟙 X)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X))).map
        ((twistedInverseImageRestrictionMapOfIsPullback h i₁ i sq).app K) ≫
      (FiniteTrace.twistedAdj (𝟙 X)).counit.app
        ((OpenImmersion.restrictedDerivedRestrict i₁).obj K) =
      (quasiCoherentDerivedPushforwardIdIsoOfComp X).hom.app _ ≫
        (twistedInverseImageRestrictionMapOfIsPullback h i₁ i sq).app K ≫
        (twistedInverseImageIdIsoOfComp X).hom.app
          ((OpenImmersion.restrictedDerivedRestrict i₁).obj K) :=
    iso_natural_chase _ _ _ _ _ _ h3 (Iso.hom_inv_id_app _ _) _ h2
  rw [h1, key]
  simp only [Category.assoc]

omit [IsOpenImmersion i] [IsOpenImmersion i₁] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace T] [QuasiSeparatedSpace T] [CompactSpace T₁] [QuasiSeparatedSpace T₁] in
/-- Pasting four commutative squares. -/
theorem four_square_chase {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : C}
    (x : A₀ ⟶ B₀) (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄)
    (a' : B₀ ⟶ B₁) (b' : B₁ ⟶ B₂) (c' : B₂ ⟶ B₃) (d' : B₃ ⟶ B₄)
    (p : A₁ ⟶ B₁) (q : A₂ ⟶ B₂) (r : A₃ ⟶ B₃) (y : A₄ ⟶ B₄)
    (h₁ : x ≫ a' = a ≫ p) (h₂ : p ≫ b' = b ≫ q) (h₃ : q ≫ c' = c ≫ r) (h₄ : r ≫ d' = d ≫ y) :
    x ≫ a' ≫ b' ≫ c' ≫ d' = (a ≫ b ≫ c ≫ d) ≫ y := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]
  simp only [Category.assoc]

variable [QuasiCompact h] [QuasiSeparated h] in
omit [QuasiSeparatedSpace X] in
/-- `i₁^* Rh_* N ⟶ i^* N` is natural in `N`. -/
theorem restrictPushforwardBaseChange_naturality {N N' : quasiCoherentDerivedCategory T}
    (f : N ⟶ N') :
    (OpenImmersion.restrictedDerivedRestrict i₁).map
        ((quasiCoherentDerivedPushforward h
          (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).map f) ≫
      restrictPushforwardBaseChange i i₁ h sq.w N' =
    restrictPushforwardBaseChange i i₁ h sq.w N ≫
      (OpenImmersion.restrictedDerivedRestrict i).map f := by
  have hU := (OpenImmersion.quasiCoherentDerivedRestrictAdjunction i
    (OpenImmersion.isQuasicoherent_homology_derivedRestrict i)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs i)).unit.naturality f
  have hσ := (quasiCoherentDerivedPushforwardSquareIso i (𝟙 X) h i₁
        (isQuasicoherent_homology_derivedPushforward_of_qcqs i)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs h)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs i₁) sq.w).hom.naturality
      ((OpenImmersion.restrictedDerivedRestrict i).map f)
  have hε := (OpenImmersion.quasiCoherentDerivedRestrictAdjunction i₁
    (OpenImmersion.isQuasicoherent_homology_derivedRestrict i₁)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs i₁)).counit.naturality
      ((quasiCoherentDerivedPushforward (𝟙 X)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X))).map
          ((OpenImmersion.restrictedDerivedRestrict i).map f))
  have he := (quasiCoherentDerivedPushforwardIdIsoOfComp X).hom.naturality
      ((OpenImmersion.restrictedDerivedRestrict i).map f)
  refine four_square_chase _ _ _ _ _ _ _ _ _
    (p := (OpenImmersion.restrictedDerivedRestrict i₁).map
      ((quasiCoherentDerivedPushforward h
          (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).map
        ((quasiCoherentDerivedPushforward i
            (isQuasicoherent_homology_derivedPushforward_of_qcqs i)).map
          ((OpenImmersion.restrictedDerivedRestrict i).map f))))
    (q := (OpenImmersion.restrictedDerivedRestrict i₁).map
      ((quasiCoherentDerivedPushforward i₁
          (isQuasicoherent_homology_derivedPushforward_of_qcqs i₁)).map
        ((quasiCoherentDerivedPushforward (𝟙 X)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X))).map
          ((OpenImmersion.restrictedDerivedRestrict i).map f))))
    (r := (quasiCoherentDerivedPushforward (𝟙 X)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X))).map
          ((OpenImmersion.restrictedDerivedRestrict i).map f))
    _ ?_ ?_ hε he
  · rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (OpenImmersion.restrictedDerivedRestrict i₁).map
      (congrArg (quasiCoherentDerivedPushforward h
        (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).map hU)
  · rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (OpenImmersion.restrictedDerivedRestrict i₁).map hσ

omit [IsOpenImmersion i] [IsOpenImmersion i₁] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace T] [QuasiSeparatedSpace T] [CompactSpace T₁] [QuasiSeparatedSpace T₁] in
/-- The diagram chase of `homology_map_twistedInverseImageRestrictionMap_eq_trace`. -/
theorem trace_restriction_chase {E C : Type*} [Category E] [Category C] (G : C ⥤ E)
    {P Q R' : C} {A B D W Z V : E}
    (tr : P ⟶ R') (r0i : P ⟶ Q) (Hx : Q ⟶ R') (ht : tr = r0i ≫ Hx)
    (R1i : G.obj Q ⟶ A) (R1hP : A ⟶ G.obj Q) (hR1 : R1i ≫ R1hP = 𝟙 _)
    (HdRx : A ⟶ Z) (R1h : Z ⟶ G.obj R') (hn1 : HdRx ≫ R1h = R1hP ≫ G.map Hx)
    (HB : A ⟶ B) (HdRℓ : B ⟶ D) (Hφ : D ⟶ Z) (hd : HdRx = HB ≫ HdRℓ ≫ Hφ)
    (RihM : B ⟶ W) (resHℓ : W ⟶ V) (RihK : D ⟶ V) (RiiK : V ⟶ D) (hRi : RihK ≫ RiiK = 𝟙 _)
    (hn2 : HdRℓ ≫ RihK = RihM ≫ resHℓ) (rsc : W ⟶ V) (hl : resHℓ = rsc)
    (β : G.obj P ⟶ V) (hSH : G.map r0i ≫ R1i ≫ HB ≫ RihM ≫ rsc = β) :
    β ≫ RiiK ≫ Hφ ≫ R1h = G.map tr := by
  subst ht hl hSH
  have e1 : G.map Hx = R1i ≫ HdRx ≫ R1h := by rw [hn1, reassoc_of% hR1]
  have e2 : HdRℓ = RihM ≫ resHℓ ≫ RiiK := by rw [← reassoc_of% hn2, hRi, Category.comp_id]
  rw [G.map_comp, e1, hd, e2]
  simp only [Category.assoc]

variable [QuasiCompact h] [QuasiSeparated h] in
/-- **On `H⁰`, the map of Tag 0A9L followed by `a_{𝟙} ≅ 𝟭` is the restriction of the trace**: for
`i ≫ h = i₁` cartesian over `𝟙 X` and `a_h K` in degrees `≥ 0`, the composite
`H⁰(a_h K)|_X ≅ H⁰(i^* a_h K) ⟶ H⁰(i₁^* K) ≅ H⁰(K)|_X` is `(h_*H⁰(a_h K))|_X ⟶ H⁰(K)|_X`, the
restriction of `Tr_h`. -/
theorem homology_map_twistedInverseImageRestrictionMap_eq_trace [IsProper h]
    (K : quasiCoherentDerivedCategory T₁) [((FiniteTrace.twisted h).obj K).obj.IsGE 0] :
    ((Scheme.Modules.restrictFunctor i).mapDerivedCategoryHomologyIso 0).inv.app
        ((FiniteTrace.twisted h).obj K).obj ≫
      (homologyFunctor X.Modules 0).map
        ((twistedInverseImageRestrictionMapOfIsPullback h i₁ i sq).app K ≫
          (twistedInverseImageIdIsoOfComp X).hom.app
            ((OpenImmersion.restrictedDerivedRestrict i₁).obj K)).hom ≫
      ((Scheme.Modules.restrictFunctor i₁).mapDerivedCategoryHomologyIso 0).hom.app K.obj =
    (restrictPushforwardIsoApp sq (FiniteTrace.zeroTwisted h K)).inv ≫
      (Scheme.Modules.restrictFunctor i₁).map (FiniteTrace.trace K) := by
  have : (FiniteTrace.zeroTwisted h K).IsQuasicoherent := ((FiniteTrace.twisted h).obj K).2 0
  rw [Iso.eq_inv_comp]
  have hSH := restrict_map_singleDerivedPushforwardHomologyIso_inv_comp sq
    (FiniteTrace.zeroTwisted h K)
  have hl := FiniteTrace.homology_map_liftSingle K (𝟙 (FiniteTrace.zeroTwisted h K))
  have hn2 := natTrans_naturality_comp
    ((Scheme.Modules.restrictFunctor i).mapDerivedCategoryHomologyIso 0).hom
    (FiniteTrace.liftSingle K (𝟙 (FiniteTrace.zeroTwisted h K)))
  have hn1 := natTrans_naturality_comp
    ((Scheme.Modules.restrictFunctor i₁).mapDerivedCategoryHomologyIso 0).hom
    ((derivedPushforward h).map (FiniteTrace.liftSingle K (𝟙 (FiniteTrace.zeroTwisted h K))) ≫
      ((FiniteTrace.twistedAdj h).counit.app K).hom)
  have hq : (OpenImmersion.restrictedDerivedRestrict i₁).map
        ((quasiCoherentDerivedPushforward h
            (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).map
          (ObjectProperty.homMk (X := singleQCoh (FiniteTrace.zeroTwisted h K))
            (Y := (FiniteTrace.twisted h).obj K)
            (FiniteTrace.liftSingle K (𝟙 (FiniteTrace.zeroTwisted h K))))) ≫
      (OpenImmersion.restrictedDerivedRestrict i₁).map ((FiniteTrace.twistedAdj h).counit.app K) =
      restrictPushforwardBaseChange i i₁ h sq.w (singleQCoh (FiniteTrace.zeroTwisted h K)) ≫
        (OpenImmersion.restrictedDerivedRestrict i).map
          (ObjectProperty.homMk (X := singleQCoh (FiniteTrace.zeroTwisted h K))
            (Y := (FiniteTrace.twisted h).obj K)
            (FiniteTrace.liftSingle K (𝟙 (FiniteTrace.zeroTwisted h K)))) ≫
        (twistedInverseImageRestrictionMapOfIsPullback h i₁ i sq).app K ≫
          (twistedInverseImageIdIsoOfComp X).hom.app
            ((OpenImmersion.restrictedDerivedRestrict i₁).obj K) := by
    rw [restrict_map_twistedAdj_counit_app sq K, ← Category.assoc,
      restrictPushforwardBaseChange_naturality sq, Category.assoc]
  have hq' := congrArg InducedCategory.Hom.hom hq
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom] at hq'
  have hd : (OpenImmersion.derivedRestrict i₁).map
      ((derivedPushforward h).map (FiniteTrace.liftSingle K (𝟙 (FiniteTrace.zeroTwisted h K))) ≫
        ((FiniteTrace.twistedAdj h).counit.app K).hom) =
      (restrictPushforwardBaseChange i i₁ h sq.w (singleQCoh (FiniteTrace.zeroTwisted h K))).hom ≫
        (OpenImmersion.derivedRestrict i).map
          (FiniteTrace.liftSingle K (𝟙 (FiniteTrace.zeroTwisted h K))) ≫
        ((twistedInverseImageRestrictionMapOfIsPullback h i₁ i sq).app K ≫
          (twistedInverseImageIdIsoOfComp X).hom.app
            ((OpenImmersion.restrictedDerivedRestrict i₁).obj K)).hom :=
    ((OpenImmersion.derivedRestrict i₁).map_comp _ _).trans hq'
  refine trace_restriction_chase (Scheme.Modules.restrictFunctor i₁)
    (tr := FiniteTrace.trace K)
    (r0i := (FiniteTrace.singleDerivedPushforwardHomologyIso h).inv.app
      (FiniteTrace.zeroTwisted h K))
    (Hx := (homologyFunctor T₁.Modules 0).map
      ((derivedPushforward h).map (FiniteTrace.liftSingle K (𝟙 (FiniteTrace.zeroTwisted h K))) ≫
        ((FiniteTrace.twistedAdj h).counit.app K).hom))
    (ht := rfl)
    (R1i := ((Scheme.Modules.restrictFunctor i₁).mapDerivedCategoryHomologyIso 0).inv.app
      ((derivedPushforward h).obj ((singleFunctor T.Modules 0).obj (FiniteTrace.zeroTwisted h K))))
    (R1hP := ((Scheme.Modules.restrictFunctor i₁).mapDerivedCategoryHomologyIso 0).hom.app
      ((derivedPushforward h).obj ((singleFunctor T.Modules 0).obj (FiniteTrace.zeroTwisted h K))))
    (hR1 := Iso.inv_hom_id_app _ _)
    (HdRx := (homologyFunctor X.Modules 0).map ((OpenImmersion.derivedRestrict i₁).map
      ((derivedPushforward h).map (FiniteTrace.liftSingle K (𝟙 (FiniteTrace.zeroTwisted h K))) ≫
        ((FiniteTrace.twistedAdj h).counit.app K).hom)))
    (hn1 := hn1)
    (HB := (homologyFunctor X.Modules 0).map
      (restrictPushforwardBaseChange i i₁ h sq.w (singleQCoh (FiniteTrace.zeroTwisted h K))).hom)
    (HdRℓ := (homologyFunctor X.Modules 0).map ((OpenImmersion.derivedRestrict i).map
          (FiniteTrace.liftSingle K (𝟙 (FiniteTrace.zeroTwisted h K)))))
    (hd := by rw [hd, Functor.map_comp, Functor.map_comp])
    (RihM := ((Scheme.Modules.restrictFunctor i).mapDerivedCategoryHomologyIso 0).hom.app
      ((singleFunctor T.Modules 0).obj (FiniteTrace.zeroTwisted h K)))
    (resHℓ := (Scheme.Modules.restrictFunctor i).map ((homologyFunctor T.Modules 0).map
      (FiniteTrace.liftSingle K (𝟙 (FiniteTrace.zeroTwisted h K)))))
    (RihK := ((Scheme.Modules.restrictFunctor i).mapDerivedCategoryHomologyIso 0).hom.app
      ((FiniteTrace.twisted h).obj K).obj)
    (hRi := Iso.hom_inv_id_app _ _) (hn2 := hn2)
    (rsc := (Scheme.Modules.restrictFunctor i).map
      ((singleFunctorCompHomologyFunctorIso T.Modules 0).hom.app (FiniteTrace.zeroTwisted h K)))
    (hl := by rw [hl]; exact congrArg (Scheme.Modules.restrictFunctor i).map (Category.comp_id _))
    (hSH := hSH)

end TraceRestriction

end Stacks.Duality
