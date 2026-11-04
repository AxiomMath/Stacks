module

public import StacksFrontier.Homology.DerivedIndexing.StandardComparison
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.CochainComplexPlusDerivedUnit

/-!
# The degree-zero comparison of the two indexings against the derived-functor unit

Let `F : 𝒜 ⥤ ℬ` be an additive functor, `𝒜` with enough injectives, and `M` an object of `𝒜`.
Mathlib's degree-zero right derived functor receives `F M` through
`CategoryTheory.Functor.toRightDerivedZero`; the `ℤ`-indexed one `H⁰(RF(M[0]))` receives it
through the derived-functor unit `F(M[0]) ⟶ RF(M[0])` on bounded below complexes
(`CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit`), applied to the class of `x ∈ F M`
as a cocycle of `F(M[0])`. This file proves that the comparison
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard` of the two indexings carries
the first to the second.

## Main definitions

* `Stacks.DerivedIndexing.singleCyclesHom`: `F M` as the degree-zero cycles of `F(M[0])`.

## Main results

* `Stacks.DerivedIndexing.toRightDerivedZero_comp_derivedPlusToStandard_inv`: **the comparison of
  the indexings in degree zero is the derived-functor unit on classes of global sections.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape
open Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.DerivedIndexing

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A : Type*} {B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]

/-- Cancelling an isomorphism across a junction, with every object and morphism a variable. -/
private theorem comp_eq_of_mono {C : Type*} [Category* C] {p q r s : C} (a a' : p ⟶ q) (b : q ⟶ r)
    (m : r ⟶ s) [Mono m] (t : q ⟶ s) (x : p ⟶ r) (ha : a = a') (hb : b ≫ m = t)
    (hx : x ≫ m = a' ≫ t) : a ≫ b = x := by
  rw [← cancel_mono m, Category.assoc, hb, ha, hx]

/-- The unit against an inverse unit, with every object and morphism a variable. -/
private theorem unit_cancel {C D : Type*} [Category* C] [Category* D] (R : C ⥤ D) {p q x : C}
    {o r s : D} (i : o ⟶ r) (u : r ⟶ R.obj p) (a : p ⟶ q) (b : q ⟶ x) (c : p ⟶ x)
    (u' : s ⟶ R.obj x) [IsIso u'] (v : r ⟶ s) (hJ : a ≫ b = c) (hn : v ≫ u' = u ≫ R.map c) :
    (i ≫ u ≫ R.map a) ≫ R.map b ≫ inv u' = i ≫ v := by
  rw [Category.assoc, Category.assoc, ← Category.assoc (R.map a), ← R.map_comp, hJ,
    ← Category.assoc u, ← hn, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The assembly of `ι_map_unit_comp_resolutionDerivedComparison_hom`, with every object and
morphism a variable. -/
private theorem assemble_aux {C D : Type*} [Category* C] [Category* D] (ι : C ⥤ D)
    {a b c e : C} {z : D} (u : a ⟶ b) (d : b ⟶ c) (x : a ⟶ e) (y : e ⟶ c) (q : ι.obj c ⟶ z)
    (x' : ι.obj a ⟶ ι.obj e) (y' : ι.obj e ⟶ ι.obj c) (q₀ : ι.obj e ⟶ ι.obj a)
    (m : ι.obj a ⟶ z) (hU : u ≫ d = x ≫ y) (hx : ι.map x = x') (hy : ι.map y = y')
    (hN : y' ≫ q = q₀ ≫ m) (hxx : x' ≫ q₀ = 𝟙 _) : ι.map u ≫ ι.map d ≫ q = m := by
  rw [← Category.assoc, ← ι.map_comp, hU, ι.map_comp, hx, hy, Category.assoc, hN,
    ← Category.assoc, hxx, Category.id_comp]

/-- Two cancellations, with every object and morphism a variable. -/
private theorem cancel_aux {C : Type*} [Category* C] {p q r s : C} (u : p ⟶ q) (v : q ⟶ p)
    (f : p ⟶ r) (w : r ⟶ s) (w' : s ⟶ r) (huv : u ≫ v = 𝟙 _) (hw : w ≫ w' = 𝟙 _) :
    u ≫ v ≫ (f ≫ w) ≫ w' = f := by
  rw [reassoc_of% huv, Category.assoc, hw, Category.comp_id]

/-- **The derived-functor unit at `M[0]` against an injective resolution of `M`**: read in the
unbounded derived category through the comparison `resolutionDerivedComparison` of `RF(M[0])`
with `Q` of the image under `F` of the extension of the resolution, the unit is the localization
of the image under `F` of the augmentation `M[0] ⟶ I`. -/
theorem ι_map_unit_comp_resolutionDerivedComparison_hom {M : A} (I : InjectiveResolution M) :
    DerivedCategory.Plus.ι.map
        ((Functor.mapCochainComplexPlusDerivedUnit F).app ((singlePlusFunctor A 0).obj M)) ≫
      (resolutionDerivedComparison F I).hom =
    DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (resolutionSingleHom I)) := by
  have hJ : (DerivedCategory.Plus.quotientCompQhIso A).hom.app ((singlePlusFunctor A 0).obj M) ≫
      (resolutionDerivedIso I).hom = DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.quotient A).map (resolutionSinglePlusHom I)) := by
    apply DerivedCategory.Plus.ι.map_injective
    have h₁ := ι_map_quotientCompQhIso_hom_app ((singlePlusFunctor A 0).obj M)
    have h₂ := Q_map_resolutionSingleHom I
    have h₃ := DerivedCategory.quotientCompQhIso_hom_naturality (resolutionSingleHom I)
    refine (DerivedCategory.Plus.ι.map_comp _ _).trans ?_
    exact @comp_eq_of_mono _ _ _ _ _ _ _ _ _ _ (inferInstanceAs (Mono
      ((DerivedCategory.quotientCompQhIso A).app
        (I.cocomplex.extend ComplexShape.embeddingUpNat)).hom)) _ _ h₁ h₂ h₃
  have hU : (Functor.mapCochainComplexPlusDerivedUnit F).app ((singlePlusFunctor A 0).obj M) ≫
      (derivedPlusResolutionIso F I).hom =
      (DerivedCategory.Plus.quotientCompQhIso B).inv.app
          (F.mapCochainComplexPlus.obj ((singlePlusFunctor A 0).obj M)) ≫
        DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlus.map
          ((HomotopyCategory.Plus.quotient A).map (resolutionSinglePlusHom I))) := by
    have hn := F.rightDerivedFunctorPlusUnit.naturality
      ((HomotopyCategory.Plus.quotient A).map (resolutionSinglePlusHom I))
    simp only [Functor.comp_map] at hn
    rw [Functor.mapCochainComplexPlusDerivedUnit_app]
    show _ ≫ (F.rightDerivedFunctorPlus.map (resolutionDerivedIso I).hom ≫
      inv (F.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus I)))) = _
    exact unit_cancel F.rightDerivedFunctorPlus _ _ _ _ _ _ _ hJ hn
  have hN := DerivedCategory.quotientCompQhIso_hom_naturality
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (resolutionSingleHom I))
  rw [resolutionDerivedComparison_hom]
  exact assemble_aux DerivedCategory.Plus.ι _ _ _ _ _ _ _ _ _ hU
    (ι_map_quotientCompQhIso_inv_app _) rfl hN (Iso.inv_hom_id_app _ _)

/-- **An object as the degree-zero cycles of the image of the complex it spans in degree zero**:
`F M ⟶ Z⁰(F(M[0]))`. -/
def singleCyclesHom (M : A) :
    F.obj M ⟶ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor A 0).obj M)).cycles 0 :=
  HomologicalComplex.liftCycles _
    (F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv) 1 (by simp) (by simp)

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B] in
/-- The inclusion of the cycles after `singleCyclesHom`. -/
@[reassoc (attr := simp)]
theorem singleCyclesHom_iCycles (M : A) :
    singleCyclesHom F M ≫ HomologicalComplex.iCycles _ 0 =
      F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B] in
/-- The degree-zero component of the image under `F` of the augmentation of an injective
resolution, read through the extensions. -/
theorem map_resolutionSingleHom_f_zero (M : A) (I : InjectiveResolution M) :
    F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (resolutionSingleHom I) ≫
          (derivedMapExtendIso F ComplexShape.embeddingUpNat I.cocomplex).hom).f 0 ≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendXIso
          ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).hom =
      F.map (I.ι.f 0) := by
  have hf : ComplexShape.embeddingUpNat.f 0 = 0 := rfl
  rw [← mapExtendIso_inv_eq_derivedMapExtendIso_hom]
  simp only [Functor.mapHomologicalComplex_obj_X, resolutionSingleHom, Functor.map_comp,
    Category.assoc, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.extendSingleIso_inv_f _ _ _ _ hf,
    CochainComplex.single₀_obj_zero, CochainComplex.single₀ObjXSelf, Iso.refl_inv,
    Category.id_comp,
    HomologicalComplex.extendMap_f _ _ hf,
    mapExtendIso_inv_f_eq F ComplexShape.embeddingUpNat I.cocomplex hf,
    Iso.inv_hom_id, Category.comp_id, Iso.map_inv_hom_id_assoc]
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp]
  exact congrArg F.map (cancel_aux _ _ _ _ _ (Iso.inv_hom_id _) (Iso.inv_hom_id _))

/-- The chase behind `toRightDerivedZero'_eq`, with every object and morphism a variable. -/
private theorem chase_aux {C : Type*} [Category* C] {p s z₁ z₂ k e x : C} (cyc : p ⟶ z₁)
    (c : z₁ ⟶ z₂) (eI : z₂ ⟶ k) (iK : k ⟶ x) (iE : z₂ ⟶ e) (xI : e ⟶ x) (iS : z₁ ⟶ s)
    (φ : s ⟶ e) (g : p ⟶ s) (X : p ⟶ x) (hE : eI ≫ iK = iE ≫ xI) (hC : c ≫ iE = iS ≫ φ)
    (hS : cyc ≫ iS = g) (hg : g ≫ φ ≫ xI = X) : (cyc ≫ c ≫ eI) ≫ iK = X := by
  rw [Category.assoc, Category.assoc, hE, reassoc_of% hC, reassoc_of% hS, hg]

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B] in
/-- The cycles-level content of `toRightDerivedZero_comp_derivedPlusToStandard_inv`. -/
theorem toRightDerivedZero'_eq (M : A) (I : InjectiveResolution M) :
    I.toRightDerivedZero' F =
      singleCyclesHom F M ≫ HomologicalComplex.cyclesMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (resolutionSingleHom I) ≫
          (derivedMapExtendIso F ComplexShape.embeddingUpNat I.cocomplex).hom) 0 ≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendCyclesIso
          ComplexShape.embeddingUpNat (j := 0) (j' := 0) rfl).hom := by
  rw [← cancel_mono (HomologicalComplex.iCycles _ 0)]
  exact (I.toRightDerivedZero'_comp_iCycles F).trans (chase_aux _ _ _ _ _ _ _ _ _ _
    (HomologicalComplex.extendCyclesIso_hom_iCycles _ _ _)
    (HomologicalComplex.cyclesMap_i _ _) (singleCyclesHom_iCycles F M)
    (map_resolutionSingleHom_f_zero F M I)).symm

/-- The algebra of `toRightDerivedZero_comp_derivedPlusToStandard_inv`, with every object and
morphism a variable. -/
private theorem key_aux {C : Type*} [Category* C] {p z h₁ d₁ d₂ d₃ d₄ h₂ h₃ H zE zK : C}
    (cyc : p ⟶ z) (πs : z ⟶ h₁) (fi : h₁ ⟶ d₁) (u : d₁ ⟶ d₂) (a : d₂ ⟶ d₃) (q : d₃ ⟶ d₄)
    (fh : d₄ ⟶ h₂) (m : h₂ ⟶ h₃) (eh : h₃ ⟶ H) (Qg : d₁ ⟶ d₄) (hg : h₁ ⟶ h₂) (cm : z ⟶ zE)
    (eC : zE ⟶ zK) (πK : zK ⟶ H) (d' : p ⟶ zK)
    (k₁ : u ≫ a ≫ q = Qg) (k₂ : fi ≫ Qg ≫ fh = hg) (k₃ : πs ≫ hg ≫ m ≫ eh = cm ≫ eC ≫ πK)
    (k₄ : cyc ≫ cm ≫ eC = d') :
    (cyc ≫ πs ≫ fi ≫ u) ≫ a ≫ q ≫ fh ≫ 𝟙 _ ≫ m ≫ eh = d' ≫ πK := by
  simp only [Category.assoc, Category.id_comp]
  rw [reassoc_of% k₁, reassoc_of% k₂, k₃, reassoc_of% k₄]

/-- A functor applied to a three-fold composite, with every object and morphism a variable. -/
private theorem map_three {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D) {p q r s : C}
    (x : p ⟶ q) (y : q ⟶ r) (z : r ⟶ s) (yz : q ⟶ s) (w : p ⟶ s) (hyz : yz = y ≫ z)
    (h : x ≫ yz = w) : H.map x ≫ H.map y ≫ H.map z = H.map w := by
  rw [← H.map_comp, ← H.map_comp, ← hyz, h]

/-- The final step of `toRightDerivedZero_comp_derivedPlusToStandard_inv`, with every object and
morphism a variable. -/
private theorem finish_aux {C : Type*} [Category* C] {p q r s t : C} (T : p ⟶ q) (E : r ≅ q)
    (R : p ⟶ r) (a : r ⟶ s) (b : s ⟶ t) (c : t ⟶ q) (d : p ⟶ t) (hE : E.hom = a ≫ b ≫ c)
    (hT : T = d ≫ c) (key : R ≫ a ≫ b = d) : T ≫ E.inv = R := by
  rw [Iso.comp_inv_eq, hE, hT, ← key]
  simp only [Category.assoc]

/-- **The comparison of the two indexings of the right derived functors in degree zero is the
derived-functor unit on classes of global sections.** For `x ∈ F M`, the class of
`toRightDerivedZero x` in `H⁰(RF(M[0]))` is the image under the derived-functor unit
`F(M[0]) ⟶ RF(M[0])` of the class of `x` as a degree-zero cocycle of `F(M[0])`. -/
theorem toRightDerivedZero_comp_derivedPlusToStandard_inv (M : A) :
    F.toRightDerivedZero.app M ≫ (derivedPlusToStandard F 0).inv.app M =
      singleCyclesHom F M ≫ HomologicalComplex.homologyπ _ 0 ≫
        (DerivedCategory.homologyFunctorFactors B 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor B 0).map
          ((Functor.mapCochainComplexPlusDerivedUnit F).app ((singlePlusFunctor A 0).obj M)) := by
  let I := injectiveResolution M
  have e₀ : (derivedPlusToStandard F 0).inv.app M =
      (derivedPlusToStandardObjOfResolution F I 0).inv :=
    congrArg Iso.inv (derivedPlusToStandard_app_eq F I 0)
  let g := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (resolutionSingleHom I)
  let d := (derivedMapExtendIso F ComplexShape.embeddingUpNat I.cocomplex).hom
  have k₁ := map_three (DerivedCategory.homologyFunctor B 0) _ _ _ _ _
    (resolutionDerivedComparison_hom F I) (ι_map_unit_comp_resolutionDerivedComparison_hom F I)
  have k₂ : (DerivedCategory.homologyFunctorFactors B 0).inv.app _ ≫
      (DerivedCategory.homologyFunctor B 0).map (DerivedCategory.Q.map g) ≫
        (DerivedCategory.homologyFunctorFactors B 0).hom.app _ =
      HomologicalComplex.homologyMap g 0 := by
    rw [← Functor.comp_map, (DerivedCategory.homologyFunctorFactors B 0).hom.naturality,
      Iso.inv_hom_id_app_assoc]
    rfl
  have k₃ : HomologicalComplex.homologyπ _ 0 ≫ HomologicalComplex.homologyMap g 0 ≫
      HomologicalComplex.homologyMap d 0 ≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat (j := 0) (j' := 0) rfl).hom =
      HomologicalComplex.cyclesMap (g ≫ d) 0 ≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendCyclesIso
          ComplexShape.embeddingUpNat (j := 0) (j' := 0) rfl).hom ≫
        HomologicalComplex.homologyπ _ 0 := by
    have hx := HomologicalComplex.homologyπ_extendHomologyIso_hom
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ComplexShape.embeddingUpNat
        (j := 0) (j' := 0) rfl
    rw [HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.homologyπ_naturality_assoc, hx,
      ← HomologicalComplex.cyclesMap_comp_assoc]
  have k₄ := (toRightDerivedZero'_eq F M I).symm
  rw [e₀]
  exact finish_aux _ _ _ _ _ _ _ rfl ((I.toRightDerivedZero_eq F).trans
      (Category.assoc _ _ _).symm)
    (key_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k₁ k₂ k₃ k₄)

end Stacks.DerivedIndexing
