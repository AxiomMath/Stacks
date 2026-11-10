module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.InjectiveDimension.Criteria
public import StacksFrontier.Algebra.Homology.InjectiveDimension.Noetherian
public import StacksFrontier.CategoryTheory.Abelian.Projective.Dimension
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension

/-!
# Gorenstein rings (Stacks chapter Dualizing Complexes)

A Noetherian local ring `A` is *Gorenstein* when `A`, viewed as a complex concentrated in
degree zero, is a dualizing complex for itself; a Noetherian ring is Gorenstein when all of
its localizations at prime ideals are Gorenstein local rings.

Every regular local ring is Gorenstein, hence so is every regular ring, and a Noetherian local
ring is Gorenstein exactly when `Ext^i(κ, A)` vanishes for all large `i`, where `κ` is the
residue field.

## Main definitions

* `Dualizing.IsGorensteinLocalRing` — the Gorenstein predicate for Noetherian local rings.
* `Dualizing.IsGorensteinRing` — the Gorenstein predicate for arbitrary Noetherian rings.

## Main results

* `Dualizing.IsRegularLocalRing.isGorensteinLocalRing` — a regular local ring is Gorenstein.
* `Dualizing.IsRegularRing.isGorensteinRing` — a regular ring is Gorenstein.
* `Dualizing.isGorensteinLocalRing_iff_residueField_ext_vanishing` — Gorensteinness is
  eventual vanishing of `Ext` from the residue field to the regular module.

## References

* [Stacks Project, Tag 0AWX](https://stacks.math.columbia.edu/tag/0AWX)
* [Stacks Project, Tag 0BJI](https://stacks.math.columbia.edu/tag/0BJI)
* [Stacks Project, Tag 0DW7](https://stacks.math.columbia.edu/tag/0DW7)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- A Noetherian local ring is Gorenstein when the ring as a
complex concentrated in degree zero is a dualizing complex. -/
@[stacks 0DW7 "(1)"]
abbrev IsGorensteinLocalRing (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : Prop :=
  Dualizing.IsDualizingComplex
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))

/-- A Noetherian ring is Gorenstein when its localization at
every prime ideal is a Gorenstein local ring. -/
@[stacks 0DW7 "(2)"]
abbrev IsGorensteinRing (A : Type u) [CommRing A] [IsNoetherianRing A] : Prop :=
  ∀ (p : Ideal A) [p.IsPrime], IsGorensteinLocalRing (Localization.AtPrime p)

private theorem regularLocal_hasFiniteInjectiveDimension (A : Type u) [CommRing A]
    [IsRegularLocalRing A] :
    ∃ n : ℕ, HasInjectiveDimensionLE (ModuleCat.of A A) n := by
  let d := (IsLocalRing.maximalIdeal A).spanFinrank
  have hdim : ringKrullDim A = (d : WithBot ℕ∞) := by
    simpa [d] using (IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)).symm
  have hreg : IsRegularRing A :=
    ((IsLocalRing.isRegularRing_tfae (R := A)).out 1 3).mp
      (inferInstance : IsRegularLocalRing A)
  have hinput : IsRegularRing A ∧ ringKrullDim A = (d : WithBot ℕ∞) := ⟨hreg, hdim⟩
  have hgl : (⨆ M : ModuleCat.{u} A, projectiveDimension M) = (d : WithBot ℕ∞) :=
    ((isRegularRing_tfae (R := A) d).out 1 2).mpr hinput
  refine ⟨d, ModuleCat.hasInjectiveDimensionLE_of_quotients (ModuleCat.of A A) d ?_⟩
  intro I
  let M : ModuleCat.{u} A := ModuleCat.of A (Shrink.{u, u} (A ⧸ I))
  have hpd : projectiveDimension M ≤ (d : WithBot ℕ∞) := by
    rw [← hgl]
    exact le_iSup (fun N : ModuleCat.{u} A ↦ projectiveDimension N) M
  have hpdlt : projectiveDimension M < ((d + 1 : ℕ) : WithBot ℕ∞) := by
    change projectiveDimension M < (d : WithBot ℕ∞) + 1
    exact (ENat.WithBot.lt_add_one_iff (n := projectiveDimension M) (m := d)).2 hpd
  let : HasProjectiveDimensionLT M (d + 1) :=
    (projectiveDimension_lt_iff).mp hpdlt
  let : HasExt.{u} (ModuleCat.{u} A) := inferInstance
  exact HasProjectiveDimensionLT.subsingleton M (d + 1) (d + 1)
    (le_refl _) (ModuleCat.of A A)

private noncomputable def homothetyBase {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) :
    (CochainComplex.singleFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of A) ⟶
      CochainComplex.HomComplex I I := by
  let f : A →ₗ[A] CochainComplex.HomComplex.Cochain I I 0 := {
    toFun := fun a ↦ a • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)
    map_add' := by intro x y; simp [add_smul]
    map_smul' := by intro r x; simp [mul_smul]
  }
  exact HomologicalComplex.mkHomFromSingle (AddCommGrpCat.ofHom f.toAddMonoidHom) (by
    intro k hk
    have hk' : (1 : ℤ) = k := by simpa using hk
    subst k
    ext a
    change CochainComplex.HomComplex.δ 0 1
      (a • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) = 0
    simp)

private theorem base_homology_class {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (x : A) :
    CochainComplex.HomComplex.homologyAddEquiv I I 0
      (HomologicalComplex.homologyMap (homothetyBase I) 0
        ((HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (AddCommGrpCat.of A)).inv.hom x)) =
      CochainComplex.HomComplex.CohomologyClass.mk
        ⟨x • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I), by
          change CochainComplex.HomComplex.δ 0 1
            (x • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) = 0
          simp⟩ := by
  classical
  let : (I.HomComplex I).HasHomology 0 := inferInstance
  let hd := CochainComplex.HomComplex.leftHomologyData' I I
    ((ComplexShape.up ℤ).prev 0) 0 ((ComplexShape.up ℤ).next 0) (by simp) (by simp)
  let iso := (I.HomComplex I).homologyIsoSc'
    ((ComplexShape.up ℤ).prev 0) 0 ((ComplexShape.up ℤ).next 0) rfl rfl
  have hiso : iso = Iso.refl _ := by
    simp [iso]
  have hmap :
      (((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
          (AddCommGrpCat.of A)).inv ≫ HomologicalComplex.cyclesMap (homothetyBase I) 0 ≫
        (HomologicalComplex.cyclesIsoSc' (I.HomComplex I)
          ((ComplexShape.up ℤ).prev 0) 0 ((ComplexShape.up ℤ).next 0) (by simp) (by simp)).hom ≫
        hd.cyclesIso.hom) ≫ hd.i) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (AddCommGrpCat.of A)).inv ≫
        (homothetyBase I).f 0 := by
    simp only [Category.assoc, hd.cyclesIso_hom_comp_i,
      HomologicalComplex.cyclesIsoSc'_hom_iCycles]
    have hcyc := HomologicalComplex.cyclesMap_i (homothetyBase I) 0
    change ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
        (AddCommGrpCat.of A)).inv ≫
      (HomologicalComplex.cyclesMap (homothetyBase I) 0 ≫
        (I.HomComplex I).iCycles 0)) = _
    rw [hcyc, ← Category.assoc]
    change ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
        (AddCommGrpCat.of A)).inv ≫
      ((HomologicalComplex.single AddCommGrpCat (ComplexShape.up ℤ) 0).obj
        (AddCommGrpCat.of A)).iCycles 0) ≫ (homothetyBase I).f 0 = _
    rw [HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles]
  have heq : CochainComplex.HomComplex.homologyAddEquiv I I 0 =
      (iso.trans hd.homologyIso).addCommGroupIsoToAddEquiv := by
    ext z
    rw [hiso]
    rfl
  rw [heq]
  rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ]
  simp only [← ConcreteCategory.comp_apply]
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
  change AddCommGrpCat.Hom.hom
      (HomologicalComplex.homologyπ (I.HomComplex I) 0 ≫ iso.hom ≫ hd.homologyIso.hom)
      (AddCommGrpCat.Hom.hom
        (((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
          (AddCommGrpCat.of A)).inv ≫ HomologicalComplex.cyclesMap (homothetyBase I) 0)) x) = _
  rw [← Category.assoc, HomologicalComplex.π_homologyIsoSc'_hom,
    Category.assoc, hd.homologyπ_comp_homologyIso_hom]
  rw [← ConcreteCategory.comp_apply]
  have hc : AddCommGrpCat.Hom.hom
      ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
          (AddCommGrpCat.of A)).inv ≫ HomologicalComplex.cyclesMap (homothetyBase I) 0 ≫
        (HomologicalComplex.cyclesIsoSc' (I.HomComplex I)
          ((ComplexShape.up ℤ).prev 0) 0 ((ComplexShape.up ℤ).next 0) (by simp) (by simp)).hom ≫
        hd.cyclesIso.hom) x =
      ⟨x • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I), by
        change CochainComplex.HomComplex.δ 0 1
          (x • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) = 0
        simp⟩ := by
    apply CochainComplex.HomComplex.Cocycle.ext
    have hval := congrArg (fun f : AddCommGrpCat.of A ⟶
        AddCommGrpCat.of (CochainComplex.HomComplex.Cochain I I 0) ↦ f.hom x) hmap
    change (AddCommGrpCat.Hom.hom
      ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
          (AddCommGrpCat.of A)).inv ≫ HomologicalComplex.cyclesMap (homothetyBase I) 0 ≫
        (HomologicalComplex.cyclesIsoSc' (I.HomComplex I)
          ((ComplexShape.up ℤ).prev 0) 0 ((ComplexShape.up ℤ).next 0) (by simp) (by simp)).hom ≫
        hd.cyclesIso.hom ≫ hd.i)) x = _
    exact hval
  rw [ConcreteCategory.comp_apply]
  change (AddCommGrpCat.Hom.hom hd.π)
    ((AddCommGrpCat.Hom.hom
      ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
          (AddCommGrpCat.of A)).inv ≫ HomologicalComplex.cyclesMap (homothetyBase I) 0 ≫
        (HomologicalComplex.cyclesIsoSc' (I.HomComplex I)
          ((ComplexShape.up ℤ).prev 0) 0 ((ComplexShape.up ℤ).next 0) (by simp) (by simp)).hom ≫
        hd.cyclesIso.hom)) x) = _
  rw [congrArg (AddCommGrpCat.Hom.hom hd.π) hc]
  simp [hd, CochainComplex.HomComplex.leftHomologyData',
    CochainComplex.HomComplex.CohomologyClass.mk]
  rfl

private noncomputable def derivedHomEquiv {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (a n : ℤ) [I.IsStrictlyGE a]
    [∀ i, Injective (I.X i)] :
    (I.HomComplex I).homology n ≃+
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).obj I) ⟶
       DerivedCategory.Qh.obj
         ((HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).obj (I⟦n⟧))) := by
  let X := (HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).obj I
  let Y := (HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).obj (I⟦n⟧)
  let e₁ : (I.HomComplex I).homology n ≃+ CochainComplex.HomComplex.CohomologyClass I I n :=
    CochainComplex.HomComplex.homologyAddEquiv I I n
  let e₂ : CochainComplex.HomComplex.CohomologyClass I I n ≃+ (X ⟶ Y) :=
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv
  let qh : (X ⟶ Y) →+ (DerivedCategory.Qh.obj X ⟶ DerivedCategory.Qh.obj Y) :=
    DerivedCategory.Qh.mapAddHom
  let f : (I.HomComplex I).homology n →+ (DerivedCategory.Qh.obj X ⟶ DerivedCategory.Qh.obj Y) :=
    qh.comp (e₂.toAddMonoidHom.comp e₁.toAddMonoidHom)
  exact AddEquiv.ofBijective f ((Dualizing.homComplex_represents_derivedHom I a n).comp
    e₁.bijective)

private def regularModuleScalarEnd {A : Type u} [CommRing A] :
    A →+ (ModuleCat.of A A ⟶ ModuleCat.of A A) where
  toFun x := ModuleCat.ofHom ((LinearMap.lsmul A A) x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

private theorem regularModuleScalarEnd_bijective {A : Type u} [CommRing A] :
    Function.Bijective (regularModuleScalarEnd (A := A)) := by
  constructor
  · intro x y h
    simpa [regularModuleScalarEnd, LinearMap.lsmul_apply] using
      congrArg (fun f : ModuleCat.of A A ⟶ ModuleCat.of A A ↦ f.hom 1) h
  · intro f
    refine ⟨f.hom 1, ?_⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    calc
      ((regularModuleScalarEnd (A := A) (f.hom 1)).hom) z = f.hom 1 * z := by
        simp [regularModuleScalarEnd, LinearMap.lsmul_apply, smul_eq_mul]
      _ = z • f.hom 1 := by simp [smul_eq_mul, mul_comm]
      _ = f.hom (z • (1 : A)) := (map_smul f.hom z 1).symm
      _ = f.hom z := by simp

private theorem regularModuleDerivedScalar_bijective {A : Type u} [CommRing A] :
    Function.Bijective (fun x : A =>
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
        (regularModuleScalarEnd x)) := by
  let F := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  constructor
  · intro x y hxy
    exact regularModuleScalarEnd_bijective.injective (F.map_injective hxy)
  · intro f
    obtain ⟨g, rfl⟩ := F.map_surjective f
    obtain ⟨x, hx⟩ := regularModuleScalarEnd_bijective.surjective g
    exact ⟨x, by simp [F, hx]⟩

private theorem homothety_cocycle_shift0 {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (x : A) :
    CochainComplex.HomComplex.Cocycle.equivHomShift.symm
      (⟨x • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I), by
        change CochainComplex.HomComplex.δ 0 1
          (x • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) = 0
        simp⟩ : CochainComplex.HomComplex.Cocycle I I 0) =
      x • ((shiftFunctorZero (CochainComplex (ModuleCat.{u} A) ℤ) ℤ).inv.app I) := by
  change CochainComplex.HomComplex.Cocycle.equivHomShift.symm
    (CochainComplex.HomComplex.Cocycle.mk
      (x • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) 1 (zero_add 1) (by simp)) = _
  rw [CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply]
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  simp [CochainComplex.HomComplex.Cocycle.homOf,
    CochainComplex.HomComplex.Cocycle.rightShift,
    CochainComplex.HomComplex.Cochain.rightShift_v,
    CochainComplex.HomComplex.Cochain.ofHom,
    CochainComplex.shiftFunctorZero_inv_app_f, HomologicalComplex.XIsoOfEq]

private theorem derivedHomEquiv_apply {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (a n : ℤ)
    [I.IsStrictlyGE a] [∀ i, Injective (I.X i)] (z : (I.HomComplex I).homology n) :
    derivedHomEquiv I a n z =
      DerivedCategory.Qh.map
        (CochainComplex.HomComplex.CohomologyClass.homAddEquiv
          (CochainComplex.HomComplex.homologyAddEquiv I I n z)) := rfl

private theorem derivedHom_shift_subsingleton {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ)
    (hI : Nonempty (DerivedCategory.Q.obj I ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))
    (n : ℤ) (hn : n ≠ 0) :
    Subsingleton
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).obj I) ⟶
       DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).obj (I⟦n⟧))) := by
  let P := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let q := HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)
  rcases hI with ⟨e⟩
  let eI : DerivedCategory.Q.obj I ≅ DerivedCategory.Q.obj P :=
    e ≪≫ ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app
      (ModuleCat.of A A)).symm
  let eSrc : DerivedCategory.Qh.obj (q.obj I) ≅ DerivedCategory.Q.obj P :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app I ≪≫ eI
  let eTgt : DerivedCategory.Qh.obj (q.obj (I⟦n⟧)) ≅
      DerivedCategory.Q.obj (P⟦n⟧) :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app (I⟦n⟧) ≪≫
      (DerivedCategory.Q.commShiftIso n).app I ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) n).mapIso eI ≪≫
      ((DerivedCategory.Q.commShiftIso n).app P).symm
  have hP : Subsingleton (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (P⟦n⟧)) := by
    by_cases hneg : n < 0
    · let : P.IsStrictlyLE 0 := inferInstance
      let : (P⟦n⟧).IsStrictlyGE (-n) :=
        CochainComplex.isStrictlyGE_shift P 0 n (-n) (by omega)
      exact DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE P
        (P⟦n⟧) 0 (-n) (by omega)
    · have hpos : 0 < n := by omega
      let : Projective (ModuleCat.of A A) :=
        ModuleCat.projective_of_free (Module.Basis.singleton Unit A)
      let : (P⟦n⟧).IsStrictlyLE (-n) :=
        CochainComplex.isStrictlyLE_shift P 0 n (-n) (by omega)
      exact subsingleton_of_forall_eq 0 fun f ↦
        DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective f (-n) (by omega)
  exact Equiv.subsingleton (Iso.homCongr eSrc eTgt)

private theorem homothetyBase_quasiIso {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ)
    (hI : Nonempty (DerivedCategory.Q.obj I ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))
    (a : ℤ) [I.IsStrictlyGE a] [∀ i, Injective (I.X i)] :
    QuasiIso (homothetyBase I) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hn : n = 0
  · subst n
    let P := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
    let q := HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)
    rcases hI with ⟨e⟩
    let eSrc : DerivedCategory.Qh.obj (q.obj I) ≅ P :=
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app I ≪≫ e
    let zI : I ≅ I⟦(0 : ℤ)⟧ :=
      ((shiftFunctorZero (CochainComplex (ModuleCat.{u} A) ℤ) ℤ).app I).symm
    let zD : DerivedCategory.Qh.obj (q.obj I) ≅
        DerivedCategory.Qh.obj (q.obj (I⟦(0 : ℤ)⟧)) :=
      DerivedCategory.Qh.mapIso (q.mapIso zI)
    let eTgt : DerivedCategory.Qh.obj (q.obj (I⟦(0 : ℤ)⟧)) ≅ P := zD.symm ≪≫ eSrc
    let E : (I.HomComplex I).homology 0 ≃ (P ⟶ P) :=
      (derivedHomEquiv I a 0).toEquiv.trans (Iso.homCongr eSrc eTgt)
    let sIso := HomologicalComplex.singleObjHomologySelfIso
      (ComplexShape.up ℤ) 0 (AddCommGrpCat.of A)
    let g (x : A) := HomologicalComplex.homologyMap (homothetyBase I) 0
      (sIso.inv.hom x)
    have hE (x : A) : E (g x) =
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
          (regularModuleScalarEnd x) := by
      dsimp [E, g]
      rw [derivedHomEquiv_apply, base_homology_class]
      let c : CochainComplex.HomComplex.Cocycle I I 0 :=
        ⟨x • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I), by
          change CochainComplex.HomComplex.δ 0 1
            (x • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) = 0
          simp⟩
      change (Iso.homCongr eSrc eTgt)
        (DerivedCategory.Qh.map
          (CochainComplex.HomComplex.CohomologyClass.toHom
            (CochainComplex.HomComplex.CohomologyClass.mk c))) = _
      rw [CochainComplex.HomComplex.CohomologyClass.toHom_mk,
        homothety_cocycle_shift0]
      have hreg : regularModuleScalarEnd x = x • (𝟙 (ModuleCat.of A A)) := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        simp [regularModuleScalarEnd, LinearMap.lsmul_apply, smul_eq_mul]
      simp [Iso.homCongr_apply, eSrc, eTgt, zD, zI, P, q, Functor.map_smul]
      simp [hreg, Functor.map_smul]
    have hbij : Function.Bijective g := by
      constructor
      · intro x y hxy
        apply regularModuleDerivedScalar_bijective.injective
        change (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
            (regularModuleScalarEnd x) =
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
            (regularModuleScalarEnd y)
        rw [← hE x, ← hE y, hxy]
      · intro y
        obtain ⟨x, hx⟩ := regularModuleDerivedScalar_bijective.surjective (E y)
        exact ⟨x, E.injective ((hE x).trans hx)⟩
    apply (ConcreteCategory.isIso_iff_bijective _).2
    constructor
    · intro x y hxy
      have hs : Function.Injective sIso.hom.hom := by
        intro a b hab
        simpa using congrArg sIso.inv.hom hab
      apply hs
      apply hbij.injective
      simpa [g, sIso] using hxy
    · intro y
      obtain ⟨x, hx⟩ := hbij.surjective y
      refine ⟨sIso.inv.hom x, ?_⟩
      simpa [g, sIso] using hx
  · let : Subsingleton (((CochainComplex.singleFunctor AddCommGrpCat 0).obj
        (AddCommGrpCat.of A)).homology n) :=
      AddCommGrpCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0
          (AddCommGrpCat.of A) n hn)
    let : Subsingleton (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).obj I) ⟶
      DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).obj (I⟦n⟧))) :=
      derivedHom_shift_subsingleton I hI n hn
    let : Subsingleton ((I.HomComplex I).homology n) :=
      Equiv.subsingleton (derivedHomEquiv I a n).toEquiv
    exact (ConcreteCategory.isIso_iff_bijective _).2
      ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- The cohomology modules of the regular module `A` in the derived category are finite. -/
private lemma finiteCohomology_single_regularModule (A : Type u) [CommRing A]
    [IsNoetherianRing A] (i : ℤ) :
    Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) := by
  let M : ModuleCat.{u} A :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
  by_cases hi : i = 0
  · subst i
    let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).app
      (ModuleCat.of A A)
    let f : A →ₗ[A] ↑M := ModuleCat.homEquiv e.inv
    have hf : Function.Surjective f := by
      intro x; refine ⟨ModuleCat.homEquiv e.hom x, ?_⟩
      change e.inv (e.hom x) = x
      exact congrArg (fun g : M ⟶ M ↦ g x) e.hom_inv_id
    let : Module.Finite A A := Module.Finite.self A
    exact Module.Finite.of_surjective f hf
  · let : ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A A)).IsGE 0 := inferInstance
    let : ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A A)).IsLE 0 := inferInstance
    let N := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).obj
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
    have hz : Limits.IsZero N := by
      by_cases hlt : i < 0
      · exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 i hlt
      · have hgt : 0 < i := by omega
        exact DerivedCategory.Plus.isZero_homology_of_isLE _ 0 i hgt
    have hzero : ∀ x : ↑N, x = 0 := fun x ↦ by
      simpa using (congrArg (fun f : N ⟶ N ↦ f x) (hz.eq_of_tgt (0 : N ⟶ N) (𝟙 N))).symm
    have htop : (⊤ : Submodule A (↑N)) = ⊥ := by ext x; simp [hzero x]
    change Module.Finite A (↑N)
    exact Module.Finite.of_fg_top (htop.symm ▸ Submodule.fg_bot)

/-- A regular local ring is Gorenstein. -/
@[stacks 0AWX "regular local rings"]
public theorem IsRegularLocalRing.isGorensteinLocalRing (A : Type u) [CommRing A]
    [IsRegularLocalRing A] : IsGorensteinLocalRing A := by
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let L := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let : Small.{u} A := inferInstance
  have hrep : Nonempty (DerivedCategory.Q.obj L ≅ K) :=
    ⟨(DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app
        (ModuleCat.of A A) |>.symm⟩
  have hbounded : ∃ a b : ℤ, L.IsStrictlyGE a ∧ L.IsStrictlyLE b :=
    ⟨0, 0, inferInstance, inferInstance⟩
  have hterms : ∀ i : ℤ, ∃ n : ℕ, HasInjectiveDimensionLE (L.X i) n := by
    intro i
    by_cases hi : i = 0
    · subst i
      exact regularLocal_hasFiniteInjectiveDimension A
    · have hzero : Limits.IsZero (L.X i) :=
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
          (ModuleCat.of A A) i hi
      let : HasInjectiveDimensionLT (L.X i) 0 :=
        Limits.IsZero.hasInjectiveDimensionLT_zero hzero
      refine ⟨0, ?_⟩
      change HasInjectiveDimensionLT (L.X i) 1
      exact hasInjectiveDimensionLT_of_ge (L.X i) 0 1 (by omega)
  have hfid₀ : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K :=
    (StacksDraft.InjectiveDimension.hasFiniteInjectiveDimension_of_bounded K).2
      L hrep hbounded hterms
  have hcoh := finiteCohomology_single_regularModule A
  refine ⟨hfid₀, hcoh, ?_⟩
  intro I hI hInj hBounds
  rcases hBounds with ⟨a, b, hGE, hLE⟩
  let : I.IsStrictlyGE a := hGE
  let : ∀ i, Injective (I.X i) := hInj
  have hlift : QuasiIso
      (((AddCommGrpCat.uliftFunctor.{u, u}).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (homothetyBase I)) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
      (homothetyBase I) (AddCommGrpCat.uliftFunctor.{u, u})).2 (homothetyBase_quasiIso I hI a)
  let srcIso := (CategoryTheory.Functor.mapCochainComplexSingleFunctor
    (AddCommGrpCat.uliftFunctor.{u, u}) 0).app (AddCommGrpCat.of A)
  let liftedBase := ((AddCommGrpCat.uliftFunctor.{u, u}).mapHomologicalComplex
    (ComplexShape.up ℤ)).map (homothetyBase I)
  let transported := srcIso.inv ≫ liftedBase
  have hmap : transported = Dualizing.homothety I := by
    apply HomologicalComplex.from_single_hom_ext
    ext a
    change ULift.up (a.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) =
      ULift.up (a.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I))
    rfl
  have htransported : QuasiIso transported := by
    let : QuasiIso srcIso.inv := by infer_instance
    let : QuasiIso liftedBase := hlift
    exact inferInstance
  rw [← hmap]
  exact htransported

/-- A regular ring is Gorenstein. -/
@[stacks 0AWX "regular rings"]
public theorem IsRegularRing.isGorensteinRing (A : Type u) [CommRing A]
    [IsRegularRing A] : IsGorensteinRing A := by
  intro p hp
  let : IsRegularLocalRing (Localization.AtPrime p) :=
    IsRegularRing.isRegularLocalRing_of_isLocalization p (Localization.AtPrime p)
  exact IsRegularLocalRing.isGorensteinLocalRing (Localization.AtPrime p)

private lemma finiteInjectiveDimension_plus_single_iff (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A))
    (Kplus : DerivedCategory.Plus (ModuleCat.{u} A))
    (hK : DerivedCategory.Plus.ι.obj Kplus = K) :
    StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K ↔
      StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
        (DerivedCategory.Plus.ι.obj Kplus) := by cases hK; rfl

private lemma exists_quasiIso_regular_single_to_injective_representative
    (A : Type u) [CommRing A] [HasDerivedCategory (ModuleCat.{u} A)]
    (I : CochainComplex (ModuleCat.{u} A) ℤ)
    (hI : Nonempty (DerivedCategory.Q.obj I ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))
    (hIinj : ∀ i : ℤ, Injective (I.X i))
    (hIbd : ∃ a b : ℤ, I.IsStrictlyGE a ∧ I.IsStrictlyLE b) :
    ∃ f : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶ I,
      QuasiIso f := by
  let P : CochainComplex (ModuleCat.{u} A) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  obtain ⟨a, b, hGE, hLE⟩ := hIbd
  let : I.IsStrictlyGE a := hGE
  let : I.IsStrictlyLE b := hLE
  let : ∀ i : ℤ, Injective (I.X i) := hIinj
  let : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  let q := HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)
  let eObj : DerivedCategory.Q.obj I ≅ DerivedCategory.Q.obj P :=
    (Classical.choice hI) ≪≫
      (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app (ModuleCat.of A A)
  let e : DerivedCategory.Qh.obj (q.obj P) ≅ DerivedCategory.Qh.obj (q.obj I) :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P ≪≫
      eObj.symm ≪≫
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app I).symm
  have hfq : Function.Surjective (DerivedCategory.Qh.map :
      (q.obj P ⟶ q.obj I) → _) :=
    (CochainComplex.IsKInjective.Qh_map_bijective (q.obj P) I).surjective
  obtain ⟨g, hg⟩ := hfq e.hom
  obtain ⟨f, hf⟩ := q.map_surjective g
  have hq : IsIso (DerivedCategory.Q.map f) := by
    have he : IsIso (DerivedCategory.Qh.map (q.map f)) := by
      rw [hf, hg]
      infer_instance
    have hn := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.naturality f
    change DerivedCategory.Qh.map (q.map f) ≫ _ = _ ≫ DerivedCategory.Q.map f at hn
    have hleft : IsIso (DerivedCategory.Qh.map (q.map f) ≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app I).hom) := by
      infer_instance
    have hcomp : IsIso
        (((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P).hom ≫
          DerivedCategory.Q.map f) := hn.symm ▸ hleft
    let s := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P |>.hom
    let : IsIso (s ≫ DerivedCategory.Q.map f) := hcomp
    exact IsIso.of_isIso_comp_left s (DerivedCategory.Q.map f)
  exact ⟨f, (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) f).1 hq⟩

private noncomputable def single_hom_eval_equiv {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    CochainComplex.HomComplex.Cochain
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) I n
        ≃ₗ[A] I.X n := by
  let h : (0 : ℤ) + n = n := by omega
  let e := CochainComplex.HomComplex.Cochain.fromSingleEquiv
    (X := ModuleCat.of A A) (K := I) h
  refine
    { toFun := fun z ↦ e z 1
      invFun := fun x ↦ e.symm (ModuleCat.ofHom (LinearMap.toSpanSingleton A (↑(I.X n)) x))
      left_inv := by
        intro z
        apply e.injective
        simp only [AddEquiv.apply_symm_apply]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change (LinearMap.toSpanSingleton A (↑(I.X n)) (e z 1)) x = (e z) x
        rw [LinearMap.toSpanSingleton_apply]
        rw [show x = x • (1 : A) by simp, LinearMap.map_smul]
        simp
      right_inv := by
        intro x
        simp [e, LinearMap.toSpanSingleton_apply]
      map_add' := by
        intro x y
        simp [e]
      map_smul' := by
        intro a z
        have he : e (a • z) = a • e z := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          simp [e, CochainComplex.HomComplex.Cochain.fromSingleEquiv,
            CochainComplex.HomComplex.Cochain.smul_v, Linear.comp_smul]
        rw [he]
        simp }

private noncomputable def single_hom_complex_iso {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex.HomComplexR A
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) I ≅ I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (single_hom_eval_equiv I n).toModuleIso)
    (by
      intro i j hij
      have hij' : i + 1 = j := by simpa using hij
      subst j
      ext z
      have hh : (0 : ℤ) + i = i := by omega
      have hh' : (0 : ℤ) + (i + 1) = i + 1 := by omega
      change CochainComplex.HomComplex.Cochain
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) I i at z
      let f := (CochainComplex.HomComplex.Cochain.fromSingleEquiv
        (X := ModuleCat.of A A) (K := I) hh) z
      have hz : CochainComplex.HomComplex.Cochain.fromSingleMk f hh = z := by
        dsimp [f]
        exact (CochainComplex.HomComplex.Cochain.fromSingleEquiv hh).symm_apply_apply z
      rw [← hz]
      change I.d i (i + 1)
          (((CochainComplex.HomComplex.Cochain.fromSingleEquiv hh)
            (CochainComplex.HomComplex.Cochain.fromSingleMk f hh)) 1) =
        (((CochainComplex.HomComplex.Cochain.fromSingleEquiv hh')
            (CochainComplex.HomComplex.δ i (i + 1)
              (CochainComplex.HomComplex.Cochain.fromSingleMk f hh))) 1)
      rw [CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk,
        CochainComplex.HomComplex.Cochain.δ_fromSingleMk f hh (i + 1) (i + 1) hh']
      rw [CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
      simp)

private noncomputable def regularHomMap {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶ I) :
    (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶
      CochainComplex.HomComplexR A
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) I := by
  let z : CochainComplex.HomComplex.Cochain
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) I 0 :=
    CochainComplex.HomComplex.Cochain.ofHom f
  exact HomologicalComplex.mkHomFromSingle
    (ModuleCat.ofHom (LinearMap.toSpanSingleton A
      (↑((CochainComplex.HomComplexR A
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) I).X 0)) z)) (by
      intro k hk
      have hk' : (1 : ℤ) = k := by simpa using hk
      subst k
      ext
      change CochainComplex.HomComplex.δ 0 1 ((1 : A) •
        CochainComplex.HomComplex.Cochain.ofHom f) = 0
      simp)

private theorem regularHomMap_quasiIso {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶ I)
    (hf : QuasiIso f) : QuasiIso (regularHomMap I f) := by
  let e := single_hom_complex_iso I
  have hcomp : regularHomMap I f ≫ e.hom = f := by
    apply HomologicalComplex.hom_ext
    intro n
    by_cases hn : n = 0
    · subst n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      let e₀ := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)
      let aa : A := e₀.hom a
      change (single_hom_eval_equiv I 0
        (LinearMap.toSpanSingleton A
          (↑((CochainComplex.HomComplexR A
            ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) I).X 0))
          (CochainComplex.HomComplex.Cochain.ofHom f) aa)) = f.f 0 aa
      change ((ModuleCat.Hom.hom
          ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).inv ≫
            ((aa • CochainComplex.HomComplex.Cochain.ofHom f).v 0 0 (by omega))))
          ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).inv (1 : A))) =
        f.f 0 aa
      have harg : aa • e₀.inv (1 : A) = a := by
        calc
          aa • e₀.inv (1 : A) = e₀.inv (aa • (1 : A)) :=
            (LinearMap.map_smul e₀.inv.hom aa (1 : A)).symm
          _ = e₀.inv aa := by congr 1; simp [smul_eq_mul]
          _ = a := by simp [aa, e₀]
      simp only [HomologicalComplex.single, ↓dreduceIte, HomologicalComplex.singleObjXSelf,
        HomologicalComplex.singleObjXIsoOfEq, CochainComplex.HomComplex.Cochain.smul_v,
        CochainComplex.HomComplex.Cochain.ofHom_v]
      change aa • (f.f 0).hom (e₀.inv (1 : A)) = (f.f 0).hom a
      rw [← harg]
      exact (LinearMap.map_smul (f.f 0).hom aa (e₀.inv (1 : A))).symm
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (ModuleCat.of A A) n hn).eq_of_src _ _
  have : QuasiIso (regularHomMap I f ≫ e.hom) := by
    rw [hcomp]
    exact hf
  exact quasiIso_of_comp_right (regularHomMap I f) e.hom

private def moduleForget (A : Type u) [Ring A] : ModuleCat.{u} A ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}

private instance moduleForget_additive (A : Type u) [Ring A] : (moduleForget A).Additive := by
  change (forget₂ (ModuleCat.{u} A) AddCommGrpCat).Additive
  infer_instance

private noncomputable instance moduleForget_preservesHomology (A : Type u) [Ring A] :
    (moduleForget A).PreservesHomology := by
  let F := moduleForget A
  let : F.Additive := moduleForget_additive A
  exact Functor.preservesHomology_of_map_exact F (fun S hS ↦ by
    simpa [F, moduleForget] using (S.exact_iff_exact_map_forget₂).mp hS)

private instance moduleForget_reflectsIsomorphisms (A : Type u) [Ring A] :
    (moduleForget A).ReflectsIsomorphisms :=
  CategoryTheory.reflectsIsomorphisms_forget₂ _ _

private noncomputable def liftedSourceIso {A : Type u} [CommRing A] :
    ((AddCommGrpCat.uliftFunctor.{u, u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((moduleForget A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) ≅
      (CochainComplex.singleFunctor AddCommGrpCat.{u} 0).obj
        (AddCommGrpCat.of (ULift.{u} A)) := by
  let U := AddCommGrpCat.uliftFunctor.{u, u}
  let F := moduleForget A
  exact Functor.mapIso (U.mapHomologicalComplex (ComplexShape.up ℤ))
      ((F.mapCochainComplexSingleFunctor 0).app (ModuleCat.of A A)) ≪≫
    (U.mapCochainComplexSingleFunctor 0).app (F.obj (ModuleCat.of A A))

private theorem liftedSourceIso_inv_zero_apply {A : Type u} [CommRing A]
    (a : ULift.{u} A) :
    ((liftedSourceIso (A := A)).inv.f 0) a = a := by
  let U := AddCommGrpCat.uliftFunctor.{u, u}
  let F := moduleForget A
  let eF := F.mapCochainComplexSingleFunctor 0
  let eU := U.mapCochainComplexSingleFunctor 0
  change ((eU.app (F.obj (ModuleCat.of A A))).inv.f 0)
    (((U.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((eF.app (ModuleCat.of A A)).inv)).f 0 a) = a
  simp [eF, eU, Functor.mapCochainComplexSingleFunctor,
    HomologicalComplex.singleMapHomologicalComplex, HomologicalComplex.single]
  rfl


private noncomputable def liftedPrecomp {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶ I) :
    Dualizing.liftedEndomorphismComplex I ⟶
      ((AddCommGrpCat.uliftFunctor.{u, u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((moduleForget A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (CochainComplex.HomComplexR A
            ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) I)) :=
  ((AddCommGrpCat.uliftFunctor.{u, u}).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (((moduleForget A).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (Stacks.HomComplex.TensorHomMap.precomp A
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) I I f))

private theorem liftedPrecomp_quasiIso {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶ I)
    [QuasiIso f] [I.IsKInjective] : QuasiIso (liftedPrecomp I f) := by
  let F := moduleForget A
  let : F.Additive := moduleForget_additive A
  let U := AddCommGrpCat.uliftFunctor.{u, u}
  let p := Stacks.HomComplex.TensorHomMap.precomp A
    ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) I I f
  have hp : QuasiIso p :=
    StacksDraft.DerivedHom.Construction.precomp_quasiIso_of_isKInjective
      (R := A) (K := I) (K' := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A A)) (I := I) f
  have hpF : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map p) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology p F).2 hp
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map p) U).2 hpF

private noncomputable def liftedRegularHomMap {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶ I) :
    (CochainComplex.singleFunctor AddCommGrpCat.{u} 0).obj
      (AddCommGrpCat.of (ULift.{u} A)) ⟶
      ((AddCommGrpCat.uliftFunctor.{u, u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((moduleForget A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (CochainComplex.HomComplexR A
            ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) I)) :=
  (liftedSourceIso (A := A)).inv ≫
    ((AddCommGrpCat.uliftFunctor.{u, u}).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((moduleForget A).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (regularHomMap I f))

private theorem liftedRegularHomMap_quasiIso {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶ I)
    (hf : QuasiIso f) : QuasiIso (liftedRegularHomMap I f) := by
  let F := moduleForget A
  let : F.Additive := moduleForget_additive A
  let U := AddCommGrpCat.uliftFunctor.{u, u}
  have hF : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (regularHomMap I f)) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
      (regularHomMap I f) F).2 (regularHomMap_quasiIso I f hf)
  have hU : QuasiIso ((U.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (regularHomMap I f))) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (regularHomMap I f)) U).2 hF
  let : QuasiIso ((liftedSourceIso (A := A)).inv) := inferInstance
  change QuasiIso ((liftedSourceIso (A := A)).inv ≫
    ((U.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (regularHomMap I f))))
  exact quasiIso_comp _ _

private theorem homothety_comp_liftedPrecomp {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶ I) :
    Dualizing.homothety I ≫ liftedPrecomp I f = liftedRegularHomMap I f := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    apply AddCommGrpCat.hom_ext
    ext a
    let aa : A := ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (AddCommGrpCat.of (ULift.{u} A))).hom a).down
    change ULift.up ((CochainComplex.HomComplex.Cochain.ofHom f).comp
        (aa • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) (zero_add 0)) =
      _
    apply ULift.ext
    have hcoef : aa =
        (ModuleCat.Hom.hom
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).hom)
          (((AddCommGrpCat.Hom.hom (𝟙 (AddCommGrpCat.of A)))
            (AddEquiv.ulift ((AddCommGrpCat.Hom.hom
              (𝟙 (AddCommGrpCat.of (ULift.{u} A)))) a)))) := by
      dsimp [aa, HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
      rfl
    simp [liftedRegularHomMap, CategoryTheory.Functor.mapHomologicalComplex,
      AddCommGrpCat.uliftFunctor, moduleForget, liftedSourceIso,
      Functor.mapCochainComplexSingleFunctor, HomologicalComplex.singleMapHomologicalComplex,
      HomologicalComplex.single, CochainComplex.HomComplex.Cochain.comp_smul]
    simp [regularHomMap]
    simp [hcoef, AddEquiv.ulift, Equiv.ulift, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.single]
    rfl
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
      (AddCommGrpCat.of (ULift.{u} A)) n hn).eq_of_src _ _

/-- A Noetherian local ring is Gorenstein precisely when its
Ext groups from the residue field to the regular module vanish in high degrees. -/
@[stacks 0BJI]
public theorem isGorensteinLocalRing_iff_residueField_ext_vanishing
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    IsGorensteinLocalRing A ↔
      ∃ b : ℤ, ∀ i : ℤ, b < i →
        Subsingleton
          (DerivedCategory.Ext
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A (Shrink.{u} (A ⧸ IsLocalRing.maximalIdeal A))))
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) i) := by
  let K : DerivedCategory (ModuleCat.{u} A) :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let Kplus : DerivedCategory.Plus (ModuleCat.{u} A) :=
    (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  have hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).obj Kplus) :=
    finiteCohomology_single_regularModule A
  have hcrit :=
    StacksDraft.InjectiveDimension.hasFiniteInjectiveDimension_iff_residueField_ext_vanishing
      Kplus hK
  have hfinite :
      StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K ↔
        StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
          (DerivedCategory.Plus.ι.obj Kplus) :=
    finiteInjectiveDimension_plus_single_iff A K Kplus rfl
  change Dualizing.IsDualizingComplex K ↔
    ∃ b : ℤ, ∀ i : ℤ, b < i →
      Subsingleton
        (DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A (Shrink.{u} (A ⧸ IsLocalRing.maximalIdeal A))))
          K i)
  constructor
  · intro h
    exact hcrit.mp (hfinite.mp h.finiteInjectiveDimension)
  · intro hExt
    have hdim := hcrit.mpr hExt
    refine ⟨hfinite.mpr hdim, ?_, ?_⟩
    · exact finiteCohomology_single_regularModule A
    · intro I hI hIinj hIbd
      change Nonempty (DerivedCategory.Q.obj I ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) at hI
      obtain ⟨f, hf⟩ := exists_quasiIso_regular_single_to_injective_representative
        A I hI hIinj hIbd
      obtain ⟨a, b, hGE, hLE⟩ := hIbd
      let : I.IsStrictlyGE a := hGE
      let : I.IsStrictlyLE b := hLE
      let : ∀ i : ℤ, Injective (I.X i) := hIinj
      let : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
      let : QuasiIso f := hf
      have : QuasiIso (Dualizing.homothety I ≫ liftedPrecomp I f) := by
        rw [homothety_comp_liftedPrecomp]
        exact liftedRegularHomMap_quasiIso I f hf
      let : QuasiIso (liftedPrecomp I f) := liftedPrecomp_quasiIso I f
      exact quasiIso_of_comp_right (Dualizing.homothety I) (liftedPrecomp I f)

end Dualizing
