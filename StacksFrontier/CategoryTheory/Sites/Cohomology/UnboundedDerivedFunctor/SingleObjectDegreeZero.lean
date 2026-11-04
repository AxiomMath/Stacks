module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObjectNaturality

/-!
# The comparison `H⁰(RF(M[0])) ≅ R⁰F(M)` on the classes of elements of `F M`

`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso` identifies the degree-`0` cohomology
of a right derived functor applied to an object placed in degree `0` with the classical right
derived functor `R⁰F`, which receives `F M` through `CategoryTheory.Functor.toRightDerivedZero`.
On the other side `F M` is the degree-`0` cohomology of `F(M[0])`, and the unit of the right
derived functor carries it to `H⁰(RF(M[0]))`. The comparison carries the first map to the second.

## Main definitions

* `Stacks.DerivedFunctor.singleZeroClass`: the class of `F M` in `H⁰(F(M[0]))`.

## Main results

* `Stacks.DerivedFunctor.toRightDerivedZero_comp_homologyTotalRightDerivedSingleIso_inv`:
  `toRightDerivedZero` followed by the inverse of `homologyTotalRightDerivedSingleIso` is the
  class of `F M` followed by the unit of the right derived functor at `M[0]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedFunctor

universe v u vB uB wD wE

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wD} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wE} B]
  (F : A ⥤ B) [F.Additive]

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B] in
/-- `F M`, as the degree-`0` term of `F(M[0])`, consists of cocycles. -/
lemma singleZeroClass_d (M : A) :
    F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor A 0).obj M)).d 0 1 = 0 := by
  dsimp
  rw [← F.map_comp, comp_zero, F.map_zero]

/-- **The class of `F M` in `H⁰(F(M[0]))`**: `F M` is the degree-`0` term of `F(M[0])`, all of
whose elements are cocycles, followed by the cohomology of the derived category. -/
def singleZeroClass (M : A) :
    F.obj M ⟶ (DerivedCategory.homologyFunctor B 0).obj (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor A 0).obj M))) :=
  ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor A 0).obj M)).liftCycles
    (F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv) 1 (by simp)
      (singleZeroClass_d F M) ≫
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor A 0).obj M)).homologyπ 0 ≫
    (DerivedCategory.homologyFunctorFactors B 0).inv.app _

/-- Two composites into `Y₃` agree when they are related by the given commuting squares. -/
private lemma cycles_chase {V : Type*} [Category* V] {P C₁ C₂ C₃ Y₁ Y₂ Y₃ X' L₁ : V}
    (a : P ⟶ C₁) (b : C₁ ⟶ C₂) (c : C₂ ⟶ C₃) (i : C₃ ⟶ Y₃) (i' : C₂ ⟶ Y₂) (m : Y₂ ⟶ Y₃)
    (i'' : C₁ ⟶ Y₁) (x : Y₁ ⟶ Y₂) (f : P ⟶ Y₁) (g : Y₁ ⟶ Y₃) (l : P ⟶ L₁) (n : L₁ ⟶ C₃)
    (iL : L₁ ⟶ X') (s : P ⟶ X') (t : X' ⟶ Y₃)
    (h₁ : c ≫ i = i' ≫ m) (h₂ : b ≫ i' = i'' ≫ x) (h₃ : a ≫ i'' = f) (h₄ : x ≫ m = g)
    (k₁ : n ≫ i = iL ≫ t) (k₂ : l ≫ iL = s) (k₃ : s ≫ t = f ≫ g) :
    (a ≫ b ≫ c) ≫ i = (l ≫ n) ≫ i := by
  simp only [Category.assoc]
  rw [h₁, reassoc_of% h₂, reassoc_of% h₃, h₄, k₁, reassoc_of% k₂, k₃]

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- **The cocycles of the degree-zero class, through the chosen injective resolution**: the
cocycle `F(ι)(x)` of `F` of the chosen resolution, read on the extension by zero, is the image
of the cocycle `x` of `F(M[0])` under `F` of the augmentation. -/
theorem toRightDerivedZero'_extendCyclesIso_inv_cyclesMap (M : A) :
    (injectiveResolution M).toRightDerivedZero' F ≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution M).cocomplex).extendCyclesIso ComplexShape.embeddingUpNat
            (rfl : ComplexShape.embeddingUpNat.f 0 = 0)).inv ≫
        HomologicalComplex.cyclesMap (Stacks.DerivedIndexing.mapExtendIso F
          ComplexShape.embeddingUpNat (injectiveResolution M).cocomplex).hom 0 =
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor A 0).obj M)).liftCycles
        (F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv) 1 (by simp)
          (singleZeroClass_d F M) ≫
        HomologicalComplex.cyclesMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (injectiveResolution M).ι') 0 := by
  let J := (injectiveResolution M).cocomplex
  let FJ := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj J
  have h₁ := HomologicalComplex.cyclesMap_i (Stacks.DerivedIndexing.mapExtendIso F
    ComplexShape.embeddingUpNat J).hom 0
  have h₂ := HomologicalComplex.extendCyclesIso_inv_iCycles FJ ComplexShape.embeddingUpNat
    (rfl : ComplexShape.embeddingUpNat.f 0 = 0)
  have h₃ := InjectiveResolution.toRightDerivedZero'_comp_iCycles (injectiveResolution M) F
  have h₄ := Stacks.DerivedIndexing.mapExtendIso_hom_f_eq F ComplexShape.embeddingUpNat J
    (rfl : ComplexShape.embeddingUpNat.f 0 = 0)
  have k₁ := HomologicalComplex.cyclesMap_i ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (injectiveResolution M).ι') 0
  have k₃ : F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv ≫
      F.map ((injectiveResolution M).ι'.f 0) =
      F.map ((injectiveResolution M).ι.f 0) ≫
        F.map (((injectiveResolution M).cochainComplexXIso 0 0 rfl).inv) := by
    rw [← F.map_comp, ← F.map_comp, InjectiveResolution.ι'_f_zero, Iso.inv_hom_id_assoc]
    rfl
  exact (cancel_mono (HomologicalComplex.iCycles _ 0)).1 (cycles_chase _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ h₁ h₂ h₃ ((congrArg (_ ≫ ·) h₄).trans (Iso.inv_hom_id_assoc _ _)) k₁
    (HomologicalComplex.liftCycles_i _ _ _ _ (singleZeroClass_d F M)) k₃)

/-- Two composites into `H₄` agree when they are related by the given commuting squares and the
retraction `ci ≫ ch = 𝟙`. -/
private lemma rd_chase {V : Type*} [Category* V] {P C₀ H₀ H₁ C₁ H₂ H₃ C₂ H₄ L₁ : V}
    (td : P ⟶ H₁) (a : P ⟶ C₀) (b : C₀ ⟶ H₀) (ci : H₀ ⟶ H₁) (ch : H₁ ⟶ H₀) (d : H₀ ⟶ H₂)
    (e : H₂ ⟶ H₃) (g : H₃ ⟶ H₄) (x : C₀ ⟶ C₁) (πe : C₁ ⟶ H₂) (y : C₁ ⟶ C₂) (π' : C₂ ⟶ H₃)
    (l₁ : P ⟶ L₁) (l₂ : L₁ ⟶ C₂) (htd : td = a ≫ b ≫ ci)
    (hc : ci ≫ ch = 𝟙 H₀) (h4 : b ≫ d = x ≫ πe) (h5 : πe ≫ e = y ≫ π')
    (h6 : a ≫ x ≫ y = l₁ ≫ l₂) :
    td ≫ ch ≫ d ≫ e ≫ g = l₁ ≫ l₂ ≫ π' ≫ g := by
  subst htd
  simp only [Category.assoc]
  rw [reassoc_of% hc, reassoc_of% h4, reassoc_of% h5, ← reassoc_of% h6]

/-- Two composites into `D₃` agree when they are related by the given commuting squares. -/
private lemma zc_chase {V : Type*} [Category* V] {P Z₁ Z₂ D₁ D₂ H₁ H₂ C₂ Y₂ D₃ : V}
    (zc : P ⟶ D₁) (l : P ⟶ Z₁) (πL : Z₁ ⟶ Z₂) (hfi : Z₂ ⟶ D₁) (qc : D₁ ⟶ D₂) (fu : D₂ ⟶ D₃)
    (hcfi : Z₂ ⟶ H₁) (hffi : H₁ ⟶ D₂) (hch : H₁ ⟶ H₂) (hffi' : H₂ ⟶ D₃) (hx : Z₂ ⟶ Y₂)
    (hcfi' : Y₂ ⟶ H₂) (cm : Z₁ ⟶ C₂) (π' : C₂ ⟶ Y₂) (hzc : zc = l ≫ πL ≫ hfi)
    (m1 : hfi ≫ qc = hcfi ≫ hffi) (m2 : hffi ≫ fu = hch ≫ hffi') (m3 : hcfi ≫ hch = hx ≫ hcfi')
    (m4 : πL ≫ hx = cm ≫ π') :
    zc ≫ qc ≫ fu = (l ≫ cm ≫ π' ≫ hcfi') ≫ hffi' := by
  subst hzc
  simp only [Category.assoc]
  rw [reassoc_of% m1, m2, reassoc_of% m3, reassoc_of% m4]

/-- If `w.hom = x.hom ≫ y.hom ≫ z.inv`, then `y.inv ≫ x.inv = z.inv ≫ w.inv`. -/
private lemma inv_square {V : Type*} [Category* V] {P Q R S : V} (x : P ≅ Q)
    (y : Q ≅ R) (z : S ≅ R) (w : P ≅ S) (h : w.hom = x.hom ≫ y.hom ≫ z.inv) :
    y.inv ≫ x.inv = z.inv ≫ w.inv := by
  rw [Iso.eq_comp_inv, Category.assoc, h]
  simp

/-- If `e.hom = a.hom ≫ b.hom ≫ c.hom ≫ d.hom`, then `e.inv = d.inv ≫ c.inv ≫ b.inv ≫ a.inv`. -/
private lemma inv_eq_of_hom_eq {V : Type*} [Category* V] {X P Q R Y : V} (e : X ≅ Y) (a : X ≅ P)
    (b : P ≅ Q) (c : Q ≅ R) (d : R ≅ Y) (h : e.hom = a.hom ≫ b.hom ≫ c.hom ≫ d.hom) :
    e.inv = d.inv ≫ c.inv ≫ b.inv ≫ a.inv := by
  rw [← cancel_epi e.hom, Iso.hom_inv_id, h]
  simp

/-- Two composites into `Z` agree when they are related by the given commuting squares and the
retraction `rq ≫ rs = 𝟙`. -/
private lemma zero_chase {V : Type*} [Category* V] {P Q₁ Q₂ Q₃ Q₄ R₁ R₂ S₁ Z : V}
    (td : P ⟶ Q₁) (rd : Q₁ ⟶ Q₂) (hf : Q₂ ⟶ Q₃) (ar : Q₃ ⟶ Q₄) (ri : Q₄ ⟶ Z)
    (pre : P ⟶ Q₂) (zc : P ⟶ R₁) (qc : R₁ ⟶ R₂) (fu : R₂ ⟶ Q₃) (as : R₂ ⟶ S₁) (rq : S₁ ⟶ Q₄)
    (rs : Q₄ ⟶ S₁) (rsq : S₁ ⟶ Z)
    (h1 : td ≫ rd = pre) (h4 : zc ≫ qc ≫ fu = pre ≫ hf) (hn : fu ≫ ar = as ≫ rq)
    (hri : ri = rs ≫ rsq) (hrq : rq ≫ rs = 𝟙 S₁) :
    td ≫ rd ≫ hf ≫ ar ≫ ri = zc ≫ qc ≫ as ≫ rsq := by
  rw [← Category.assoc td, h1, ← Category.assoc pre, ← h4, hri]
  simp only [Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hrq]

omit [EnoughInjectives A] [HasDerivedCategory A] in
variable (B) in
/-- The two factorisations of the cohomology of the derived category through complexes, at the
image of a complex, related by the comparison of the two localizations. -/
theorem homologyFunctorFactors_inv_app_comp_quotientCompQhIso_inv (L : CochainComplex B ℤ)
    (n : ℤ) :
    (DerivedCategory.homologyFunctorFactors B n).inv.app L ≫
        (DerivedCategory.homologyFunctor B n).map
          ((DerivedCategory.quotientCompQhIso B).inv.app L) =
      (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) n).inv.app L ≫
        (DerivedCategory.homologyFunctorFactorsh B n).inv.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L) :=
  inv_square ((DerivedCategory.homologyFunctor B n).mapIso
      ((DerivedCategory.quotientCompQhIso B).app L))
    ((DerivedCategory.homologyFunctorFactors B n).app L)
    ((HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) n).app L)
    ((DerivedCategory.homologyFunctorFactorsh B n).app
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L))
    (DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj (C := B) L n)

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- `toRightDerivedZero`, read through `rightDerivedIsoRes`, is the class of `F M` carried by
`F` of the augmentation of the chosen injective resolution into the homotopy category. -/
theorem toRightDerivedZero_app_comp_rightDerivedIsoRes_hom_app (M : A) :
    F.toRightDerivedZero.app M ≫ (Stacks.DerivedIndexing.rightDerivedIsoRes F 0).hom.app M =
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor A 0).obj M)).liftCycles
        (F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv) 1 (by simp)
          (singleZeroClass_d F M) ≫
        HomologicalComplex.cyclesMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (injectiveResolution M).ι') 0 ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (injectiveResolution M).cochainComplex).homologyπ 0 ≫
        (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) ((0 : ℕ) : ℤ)).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (injectiveResolution M).cochainComplex) := by
  let J := (injectiveResolution M).cocomplex
  let FJ := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj J
  rw [Stacks.DerivedIndexing.rightDerivedIsoRes_hom_app_eq, extendMapHomologyIso_hom_eq]
  exact rd_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl
    (Iso.inv_hom_id_app (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) 0) FJ)
    (HomologicalComplex.homologyπ_extendHomologyIso_inv FJ ComplexShape.embeddingUpNat
      (rfl : ComplexShape.embeddingUpNat.f 0 = 0))
    (HomologicalComplex.homologyπ_naturality (Stacks.DerivedIndexing.mapExtendIso F
      ComplexShape.embeddingUpNat J).hom 0)
    (toRightDerivedZero'_extendCyclesIso_inv_cyclesMap F M)

variable (RF : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

/-- The inverse of `homologyTotalRightDerivedSingleIso` in degree `0`, through the chosen
injective resolutions. -/
theorem homologyTotalRightDerivedSingleIso_inv_eq (M : A) :
    (homologyTotalRightDerivedSingleIso F RF α hres M 0).inv =
      (Stacks.DerivedIndexing.rightDerivedIsoRes F 0).hom.app M ≫
        (DerivedCategory.homologyFunctorFactorsh B ((0 : ℕ) : ℤ)).inv.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj (Stacks.DerivedIndexing.resH.obj M)) ≫
        (DerivedCategory.homologyFunctor B ((0 : ℕ) : ℤ)).map
          (α.app (Stacks.DerivedIndexing.resH.obj M)) ≫
        (DerivedCategory.homologyFunctor B ((0 : ℕ) : ℤ)).map
          (RF.map ((singleIsoResCompQh (A := A)).inv.app M)) := by
  rw [homologyTotalRightDerivedSingleIso_eq]
  exact inv_eq_of_hom_eq _ ((DerivedCategory.homologyFunctor B ((0 : ℕ) : ℤ)).mapIso
      (RF.mapIso ((singleIsoResCompQh (A := A)).app M)))
    ((DerivedCategory.homologyFunctor B ((0 : ℕ) : ℤ)).mapIso
      ((resCompUnitIso F RF α hres).symm.app M))
    ((DerivedCategory.homologyFunctorFactorsh B ((0 : ℕ) : ℤ)).app _)
    ((Stacks.DerivedIndexing.rightDerivedIsoRes F 0).symm.app M)
    (singleCompDerivedCompHomologyIsoRightDerived_hom_app_res F RF α hres 0 M)

/-- **The comparison `H⁰(RF(M[0])) ≅ R⁰F(M)` on classes**: `toRightDerivedZero`, followed by
the inverse of `homologyTotalRightDerivedSingleIso`, is the class of `F M` in `H⁰(F(M[0]))`
followed by the unit of the right derived functor at `M[0]`. -/
theorem toRightDerivedZero_comp_homologyTotalRightDerivedSingleIso_inv (M : A) :
    F.toRightDerivedZero.app M ≫ (homologyTotalRightDerivedSingleIso F RF α hres M 0).inv =
      singleZeroClass F M ≫
        (DerivedCategory.homologyFunctor B ((0 : ℕ) : ℤ)).map
          ((DerivedCategory.quotientCompQhIso B).inv.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((CochainComplex.singleFunctor A 0).obj M))) ≫
        (DerivedCategory.homologyFunctor B ((0 : ℕ) : ℤ)).map
          (α.app ((HomotopyCategory.singleFunctor A 0).obj M)) ≫
        (DerivedCategory.homologyFunctor B ((0 : ℕ) : ℤ)).map
          (RF.map ((DerivedCategory.singleFunctorIsoCompQh A 0).inv.app M)) := by
  let HD := DerivedCategory.homologyFunctor B ((0 : ℕ) : ℤ)
  let eI := (asIso (Functor.whiskerRight (Stacks.DerivedIndexing.resUnit (C := A))
    DerivedCategory.Qh)).app M
  let L := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((CochainComplex.singleFunctor A 0).obj M)
  let φ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (injectiveResolution M).ι'
  have m1 := homologyFunctorFactors_inv_app_comp_quotientCompQhIso_inv B L ((0 : ℕ) : ℤ)
  have m2 := (DerivedCategory.homologyFunctorFactorsh B ((0 : ℕ) : ℤ)).inv.naturality
    ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map φ)
  have m3 := (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ)
    ((0 : ℕ) : ℤ)).inv.naturality φ
  have m4 := HomologicalComplex.homologyπ_naturality φ ((0 : ℕ) : ℤ)
  have h4 := zc_chase (singleZeroClass F M) _ _ _ _ (HD.map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map φ))) _ _ _ _ _ _ _ _ rfl m1
    m2.symm m3.symm m4
  have hn := α.naturality (Stacks.DerivedIndexing.resUnit.app M)
  have hn' : HD.map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map φ)) ≫
        HD.map (α.app (Stacks.DerivedIndexing.resH.obj M)) =
      HD.map (α.app ((HomotopyCategory.singleFunctor A 0).obj M)) ≫ HD.map (RF.map eI.hom) :=
    (HD.map_comp _ _).symm.trans ((congrArg HD.map hn).trans (HD.map_comp _ _))
  have hri : HD.map (RF.map ((singleIsoResCompQh (A := A)).inv.app M)) =
      HD.map (RF.map eI.inv) ≫
        HD.map (RF.map ((DerivedCategory.singleFunctorIsoCompQh A 0).inv.app M)) :=
    (congrArg HD.map (RF.map_comp _ _)).trans (HD.map_comp _ _)
  have hrq : HD.map (RF.map eI.hom) ≫ HD.map (RF.map eI.inv) = 𝟙 _ := by
    rw [← HD.map_comp, ← RF.map_comp, eI.hom_inv_id, RF.map_id, HD.map_id]
  rw [homologyTotalRightDerivedSingleIso_inv_eq]
  exact zero_chase _ _ _ _ _ _ _ _ _ _ _ _ _
    (toRightDerivedZero_app_comp_rightDerivedIsoRes_hom_app F M) h4 hn' hri hrq

end Stacks.DerivedFunctor
