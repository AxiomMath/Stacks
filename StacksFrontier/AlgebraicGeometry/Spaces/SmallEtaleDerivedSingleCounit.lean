module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedModulePushforwardSingle
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeUnderived
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTransposeBaseChange
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorDegreeZero
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.Homology.DerivedIndexing.Composite
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit

/-!
# The derived counit at a direct image in degree zero (Stacks 0FPI)

For a morphism `f : X ⟶ Y` of algebraic spaces and an `𝒪_X`-module `H`, consider the map
`Lf^*((f_*H)[0]) ⟶ Lf^*Rf_*(H[0]) ⟶ H[0]` built from the canonical map `(f_*H)[0] ⟶ Rf_*(H[0])`
and the counit of `Lf^* ⊣ Rf_*`. By Stacks 0FPI it factors through the comparison
`Lf^* ⟶ f^*` on the homotopy category, followed by the degreewise counit `f^*f_* ⟶ id`.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardSingleToDerived_counit_eq_homotopy`: that
  factorization, for any `f` and any `H`.
* `Stacks.DerivedSingleCounit.single_counit`: the underived half of the identification, for
  abstract data (exact functors, the two degreewise adjunctions `P ⊣ F` and `mp ⊣ w` with
  `F = w`, and a comparison `Qh ⋙ L ⟶ P ⋙ Qh`): the right-hand side above equals the comparison
  `L((F H)[0]) ⟶ (mp F H)[0]` followed by the counit of `mp ⊣ w` in degree `0`.
* `CategoryTheory.Adjunction.map_comp_map_comp_counit`: the bookkeeping step, for an arbitrary
  adjunction, which moves a morphism of the form `R(d)` past the counit.

## Implementation notes

The proofs rewrite only with the lemmas that define the terms involved
(`AlgebraicGeometry.Space.derivedModulePushforwardUnit_eq_totalRightDerivedUnit`,
`AlgebraicGeometry.Space.smallEtaleDerivedModuleAdjunction_counit_fac`) and apply abstract
lemmas with their arguments left to unification. Restating these terms by hand gives spellings
whose instance arguments differ from the defining ones, and the kernel then times out checking
that they agree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward pushforwardOnHomotopy
  sourceQuasiIso pullbackMapHomotopy pushforwardMapHomotopy pullbackAdjPushforwardMapHomotopy)

universe u

/-! ### The underived half, for abstract data -/

namespace Stacks.DerivedSingleCounit

variable {A Bc : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  [Category Bc] [Abelian Bc] [HasDerivedCategory Bc]

omit [HasDerivedCategory A] [HasDerivedCategory Bc] in
/-- Degreewise: `P(s) ≫ ε_T = pm ≫ (single-map iso) ≫ ε_M` on the complex `(F H)[0]`. -/
theorem complex_counit (F : A ⥤ Bc) [F.Additive] (P mp : Bc ⥤ A) [P.Additive] [mp.Additive]
    (adjT : P ⊣ F) (adjM : mp ⊣ F) (H : A) :
    (P.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app H) ≫
      (NatTrans.mapHomologicalComplex adjT.counit (ComplexShape.up ℤ)).app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj H) =
    (NatIso.mapHomologicalComplex (adjT.leftAdjointUniq adjM) (ComplexShape.up ℤ)).hom.app
        ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj (F.obj H)) ≫
      (HomologicalComplex.singleMapHomologicalComplex mp (ComplexShape.up ℤ) 0).hom.app (F.obj H) ≫
        (HomologicalComplex.single A (ComplexShape.up ℤ) 0).map (adjM.counit.app H) := by
  ext i
  by_cases hi : i = 0
  · subst hi
    simp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_X, Functor.id_obj,
      HomologicalComplex.singleMapHomologicalComplex, NatIso.ofComponents_inv_app,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, ↓reduceDIte,
      NatTrans.mapHomologicalComplex_app_f, NatIso.ofComponents_hom_app,
      NatIso.mapHomologicalComplex_hom_app_f, HomologicalComplex.single_map_f_self]
    rw [← Adjunction.leftAdjointUniq_hom_app_counit adjT adjM, ← Category.assoc,
      (adjT.leftAdjointUniq adjM).hom.naturality, Category.assoc]
    congr 1
    have aux : ∀ (Z : A) (_ : Z = H) (D₀ : A) (p : D₀ = mp.obj (F.obj Z))
        (q : D₀ = mp.obj (F.obj H)) (r : H = Z),
        eqToHom p ≫ adjM.counit.app Z = eqToHom q ≫ adjM.counit.app H ≫ eqToHom r := by
      rintro Z rfl D₀ rfl q r
      simp
    rw [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.singleObjXIsoOfEq, eqToIso.hom,
      eqToIso.inv, eqToHom_map, eqToHom_trans_assoc]
    refine aux _ ?_ _ _ _ _
    simp
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_tgt _ _

omit [HasDerivedCategory A] in
/-- The inverse of `mapSingleQhIso` at `H`. -/
theorem mapSingleQhIso_inv_app (w : A ⥤ Bc) [w.Additive] (H : A) :
    (Stacks.DerivedFunctor.mapSingleQhIso w 0).inv.app H =
      (DerivedCategory.quotientCompQhIso Bc).inv.app
          ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj (w.obj H)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient Bc (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex w (ComplexShape.up ℤ) 0).inv.app
            H)) := by
  simp only [Functor.comp_obj, DerivedFunctor.mapSingleQhIso, Functor.isoWhiskerLeft_trans,
    Iso.trans_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv,
    Category.assoc, NatTrans.comp_app, Functor.whiskerLeft_app,
    DerivedIndexing.singleFunctorIsoCompQh_hom_app, Functor.whiskerRight_app,
    HomotopyCategory.quotient_obj_singleFunctors_obj,
    DerivedIndexing.singleFunctorPostcompQuotientIso_hom_app, CategoryTheory.Functor.map_id,
    Functor.comp_map, DerivedIndexing.mapHomotopyCategoryFactors_inv_app,
    DerivedIndexing.singleFunctorPostcompQuotientIso_inv_app, Category.comp_id,
    DerivedCategory.Q_obj_single_obj]
  exact congrArg (_ ≫ ·) ((Category.id_comp _).trans ((congrArg (_ ≫ ·)
    (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)))

/-- The inverse of `singleFunctorIsoCompQh` at `H`. -/
theorem singleFunctorIsoCompQh_inv_app (H : A) :
    (DerivedCategory.singleFunctorIsoCompQh A 0).inv.app H =
      (DerivedCategory.quotientCompQhIso A).hom.app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj H) := by
  have h := Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app (C := A) 0 H
  exact Iso.inv_ext (f := (DerivedCategory.singleFunctorIsoCompQh A 0).app H)
    ((congrArg (· ≫ _) h).trans ((DerivedCategory.quotientCompQhIso A).inv_hom_id_app _))

/-- Moving the comparison `quotient ⋙ Qh ≅ Q` past an identity of complexes. -/
theorem quotientCompQhIso_shape {X Y Z X₁ X₂ : CochainComplex A ℤ} (g₁ : X ⟶ Y) (g₂ : Y ⟶ Z)
    (m₁ : X ⟶ X₁) (m₂ : X₁ ⟶ X₂) (m₃ : X₂ ⟶ Z) (h : g₁ ≫ g₂ = m₁ ≫ m₂ ≫ m₃) :
    (HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map g₁ ≫
        (HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map g₂ ≫
        (DerivedCategory.quotientCompQhIso A).hom.app Z =
      (DerivedCategory.quotientCompQhIso A).hom.app X ≫ DerivedCategory.Q.map m₁ ≫
        DerivedCategory.Q.map m₂ ≫ DerivedCategory.Q.map m₃ := by
  rw [← Functor.map_comp_assoc, (DerivedCategory.quotientCompQhIso A).hom.naturality, h]
  simp

/-- The bookkeeping shape of `single_counit`. -/
theorem single_counit_shape {D₁ D₂ : Type*} [Category D₁] [Category D₂] (L : D₁ ⥤ D₂)
    {X₀ X₁ X₂ : D₁} (a : X₀ ⟶ X₁) (θ : X₁ ⟶ X₂) {Y₁ Y₂ Y₃ Y₄ Y₅ Y₆ Y₇ : D₂}
    (c₂ : L.obj X₂ ⟶ Y₂) (ε : Y₂ ⟶ Y₃) (t : Y₃ ⟶ Y₇) (c₁ : L.obj X₁ ⟶ Y₁) (Pθ : Y₁ ⟶ Y₂)
    (k : Y₁ ⟶ Y₄) (m₁ : Y₄ ⟶ Y₅) (m₂ : Y₅ ⟶ Y₆) (j : Y₆ ⟶ Y₆) (m₃ : Y₆ ⟶ Y₇)
    (hj : j = 𝟙 _) (hn : L.map θ ≫ c₂ = c₁ ≫ Pθ) (hD : Pθ ≫ ε ≫ t = k ≫ m₁ ≫ m₂ ≫ m₃) :
    L.map ((a ≫ θ) ≫ 𝟙 X₂) ≫ c₂ ≫ ε ≫ t =
      L.map (𝟙 X₀) ≫ (L.map a ≫ c₁ ≫ k ≫ m₁) ≫ m₂ ≫ j ≫ m₃ := by
  subst hj
  simp only [Category.comp_id, Functor.map_comp, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.assoc]
  rw [reassoc_of% hn, hD]

/-- **The underived half of Stacks 0FPI at a direct image in degree `0`**, for abstract data:
exact functors, the degreewise adjunctions `P ⊣ F` and `mp ⊣ w` with `F = w`, a functor `L`
between the derived categories and a comparison `Qh ⋙ L ⟶ P ⋙ Qh`. -/
theorem single_counit (F w : A ⥤ Bc) [F.Additive] [w.Additive] (hF : F = w) (P mp : Bc ⥤ A)
    [P.Additive] [mp.Additive] (adjT : P ⊣ F) (adjM : mp ⊣ w)
    (L : DerivedCategory Bc ⥤ DerivedCategory A)
    (cmp : DerivedCategory.Qh ⋙ L ⟶ P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (E : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh =
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) (H : A) :
    L.map ((Stacks.DerivedFunctor.mapSingleQhIso w 0).inv.app H ≫
        (eqToHom E).app ((HomotopyCategory.singleFunctor A 0).obj H)) ≫
      cmp.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.singleFunctor A 0).obj H)) ≫
      DerivedCategory.Qh.map ((adjT.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app
        ((HomotopyCategory.singleFunctor A 0).obj H)) ≫
      (DerivedCategory.singleFunctorIsoCompQh A 0).inv.app H =
    L.map ((DerivedCategory.singleFunctorIsoCompQ Bc 0).hom.app (w.obj H)) ≫
      (L.map ((DerivedCategory.quotientCompQhIso Bc).inv.app
          ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj (w.obj H))) ≫
        cmp.app ((HomotopyCategory.quotient Bc (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj (w.obj H))) ≫
        (DerivedCategory.quotientCompQhIso A).hom.app
          ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj (w.obj H))) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (adjT.leftAdjointUniq (adjM.ofNatIsoRight (eqToIso hF).symm)) (ComplexShape.up ℤ)).hom.app
            ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj (w.obj H)))) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex mp (ComplexShape.up ℤ) 0).hom.app
        (w.obj H)) ≫
      (DerivedCategory.singleFunctorIsoCompQ A 0).inv.app (mp.obj (w.obj H)) ≫
      (DerivedCategory.singleFunctor A 0).map (adjM.counit.app H) := by
  subst hF
  have hadj : adjM.ofNatIsoRight (eqToIso rfl).symm = adjM := by
    ext X
    simp [Adjunction.ofNatIsoRight]
  rw [hadj]
  simp only [eqToHom_refl, NatTrans.id_app]
  rw [mapSingleQhIso_inv_app, singleFunctorIsoCompQh_inv_app]
  refine single_counit_shape L _ _ _ _ _ _ _ _ _ _ _ _ rfl
    (cmp.naturality ((HomotopyCategory.quotient Bc (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app H))) ?_
  exact quotientCompQhIso_shape _ _ _ _ _ (complex_counit F P mp adjT adjM H)

end Stacks.DerivedSingleCounit

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard SheafOfModules.instAbelian

/-- **Moving `R(d)` past the counit of `L ⊣ R`**: if `L(b) ≫ ε = r₁ ≫ r₂` then
`L(a ≫ (e ≫ b) ≫ R(d)) ≫ ε = L(a ≫ e) ≫ r₁ ≫ r₂ ≫ d`, by naturality of the counit. -/
theorem _root_.CategoryTheory.Adjunction.map_comp_map_comp_counit {C D : Type*} [Category* C]
    [Category* D] {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R) {A A' A'' : D} {Y₀ Y₁ : C}
    (a : A ⟶ A') (e : A' ⟶ A'') (b : A'' ⟶ R.obj Y₀) (d : Y₀ ⟶ Y₁) {Z : C}
    {r₁ : L.obj A'' ⟶ Z} {r₂ : Z ⟶ Y₀} (h : L.map b ≫ adj.counit.app Y₀ = r₁ ≫ r₂) :
    L.map (a ≫ (e ≫ b) ≫ R.map d) ≫ adj.counit.app Y₁ = L.map (a ≫ e) ≫ r₁ ≫ r₂ ≫ d := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.comp_map, adj.counit.naturality, ← Category.assoc (L.map b), h]
  simp only [Category.assoc, Functor.id_map]

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **The canonical map `(f_*M)[0] ⟶ RF(M[0])` at `M`**: the comparison
`(f_*M)[0] ≅ Qh(f_*(M[0]))`, then the unit `α` of `RF` at `M[0]`, then `RF` of the comparison
`Qh(M[0]) ≅ M[0]`. -/
theorem modulePushforwardSingleToRightDerived_app (f : X ⟶ Y)
    (RF : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF) (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforwardSingleToRightDerived B S hS f RF α).app M =
      (Stacks.DerivedFunctor.mapSingleQhIso (modulePushforward B S hS f) 0).inv.app M ≫
        α.app ((HomotopyCategory.singleFunctor _ 0).obj M) ≫
          RF.map ((DerivedCategory.singleFunctorIsoCompQh _ 0).inv.app M) := by
  simp [modulePushforwardSingleToRightDerived]

/-- **Stacks 0FPI at a direct image in degree `0`.** For `f : X ⟶ Y` and an `𝒪_X`-module `H`, the
map `Lf^*((f_*H)[0]) ⟶ Lf^*Rf_*(H[0]) ⟶ H[0]`, built from the canonical map
`AlgebraicGeometry.Space.modulePushforwardSingleToDerived` and the counit of `Lf^* ⊣ Rf_*`, is
the following composite: the identification of `(f_*H)[0]` with the image of `f_*(H[0])` from
the homotopy category, the comparison `Lf^* ⟶ f^*` of the derived pullback there, the
degreewise counit `f^*f_*(H[0]) ⟶ H[0]`, and the identification of the image of `H[0]` with
`H[0]`. -/
theorem modulePushforwardSingleToDerived_counit_eq_homotopy (f : X ⟶ Y)
    (H : Modules.{u, u} B S hS X.1 X.2) :
    (smallEtaleDerivedModulePullback B S hS f).map
        ((modulePushforwardSingleToDerived B S hS f).app H) ≫
      (smallEtaleDerivedModuleAdjunction B S hS f).counit.app
        ((DerivedCategory.singleFunctor _ 0).obj H) =
    (smallEtaleDerivedModulePullback B S hS f).map
        ((Stacks.DerivedFunctor.mapSingleQhIso (modulePushforward B S hS f) 0).inv.app H ≫
          (eqToHom (mapHomotopyCategory_modulePushforward_comp_Qh_eq B S hS f)).app
            ((HomotopyCategory.singleFunctor _ 0).obj H)) ≫
      (smallEtaleDerivedModulePullbackComparison B S hS f).app
        ((smallEtalePushforwardMapHomotopy B S hS f).obj
          ((HomotopyCategory.singleFunctor _ 0).obj H)) ≫
      DerivedCategory.Qh.map ((smallEtaleMapHomotopyAdjunction B S hS f).counit.app
          ((HomotopyCategory.singleFunctor _ 0).obj H)) ≫
      (DerivedCategory.singleFunctorIsoCompQh _ 0).inv.app H := by
  rw [modulePushforwardSingleToDerived, modulePushforwardSingleToRightDerived_app,
    derivedModulePushforwardUnit_eq_totalRightDerivedUnit]
  exact (smallEtaleDerivedModuleAdjunction B S hS f).map_comp_map_comp_counit _ _ _ _
    (smallEtaleDerivedModuleAdjunction_counit_fac B S hS f _)


end AlgebraicGeometry.Space
