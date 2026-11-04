module

public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
import StacksCore.Tactic.StacksAttribute

/-! # The unbounded right derived functor on a single object

Let `A` and `B` be abelian categories, `A` with enough injectives, and let `F : A ⥤ B` be
additive. For an object `M` of `A`, placed in degree `a` of the derived category, the degree-`m`
cohomology of the unbounded right derived functor of `F` is the classical right derived functor
`R^{m-a} F (M)`, where `R^n F` is Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`.

## Main results

* `Stacks.DerivedFunctor.mapHomologicalComplexExtendNatIso`: applying an additive functor
  degreewise commutes with extending a `ℕ`-indexed cochain complex to a `ℤ`-indexed one.
* `Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso`: `H^n(RF(M[0])) ≅ R^n F (M)`.
* `Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso`:
  `H^m(RF(M[a])) ≅ R^{m-a} F (M)`.
* `Stacks.DerivedFunctor.isZero_homologyTotalRightDerived_single_of_rightDerived_isZero`: if the
  higher classical right derived functors vanish on `M`, then `RF(M[a])` has no cohomology above
  degree `a`.
* `Stacks.DerivedFunctor.homologyTotalRightDerivedSingleSelfIso`: for a left exact `F`,
  `H^a(RF(M[a])) ≅ F (M)`.

## Implementation notes

The right derived functor is taken as data, as a pair `(RF, α)` with `RF.IsRightDerivedFunctor α`
for the quasi-isomorphisms of the homotopy category, since any two are uniquely isomorphic
compatibly with their units; the shifted statement additionally needs the shift-commutation
datum, which `CategoryTheory.Functor.IsRightDerivedFunctor.commShift` supplies.

## References

* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedFunctor

universe v u vB uB wG wD wE

section Extend

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type uB} [Category.{vB} B] [Abelian B]

/-- Applying an additive functor degreewise commutes with the extension of a `ℕ`-indexed cochain
complex to a `ℤ`-indexed one by zero objects in the negative degrees. -/
def mapHomologicalComplexExtendNatIso (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℕ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat) ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
        ComplexShape.embeddingUpNat := by
  let e := ComplexShape.embeddingUpNat
  let FK := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let φ (i : ℤ) : F.obj ((K.extend e).X i) ≅ (FK.extend e).X i :=
    if hi : 0 ≤ i then
      F.mapIso (K.extendXIso e (i := i.toNat) (by simpa [e] using Int.toNat_of_nonneg hi)) ≪≫
        (FK.extendXIso e (i := i.toNat) (by simpa [e] using Int.toNat_of_nonneg hi)).symm
    else
      (F.map_isZero (K.isZero_extend_X e i (by intro n; simp [e]; omega))).isoZero ≪≫
        (FK.isZero_extend_X e i (by intro n; simp [e]; omega)).isoZero.symm
  refine HomologicalComplex.Hom.isoOfComponents φ ?_
  intro i j hij
  by_cases hi : 0 ≤ i
  · have hj : 0 ≤ j := by change i + 1 = j at hij; omega
    dsimp only [φ]
    rw [dite_eq_left hi, dite_eq_left hj]
    dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    change _ = F.map ((K.extend e).d i j) ≫ _
    rw [K.extend_d_eq e (i := i.toNat) (j := j.toNat)
      (by simpa [e] using Int.toNat_of_nonneg hi)
      (by simpa [e] using Int.toNat_of_nonneg hj),
      FK.extend_d_eq e (i := i.toNat) (j := j.toNat)
      (by simpa [e] using Int.toNat_of_nonneg hi)
      (by simpa [e] using Int.toNat_of_nonneg hj)]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
    simp only [← Functor.mapIso_inv, ← Functor.mapIso_hom, Iso.inv_hom_id_assoc]
    rfl
  · exact (F.map_isZero (K.isZero_extend_X e i (by intro n; simp [e]; omega))).eq_of_src _ _

end Extend

section Single

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wD} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wE} B]

/-- For an object `M` placed in degree `0` of the unbounded derived category, the degree-`n`
cohomology of a right derived functor of `F` is the classical right derived functor `R^n F (M)`.
Here `hres` is the existence of K-injective resolutions. -/
def homologyTotalRightDerivedSingleIso (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (M : A) (n : ℕ) :
    (DerivedCategory.homologyFunctor B (n : ℤ)).obj
        (RF.obj ((DerivedCategory.singleFunctor A 0).obj M)) ≅
      (F.rightDerived n).obj M := by
  let I := injectiveResolution M
  let K := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I.cochainComplex
  have hI : I.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective I.cochainComplex 0
  have : IsIso (α.app K) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hres).2
        DerivedCategory.Qh RF α I.cochainComplex hI
  let e : (DerivedCategory.singleFunctor A 0).obj M ≅ DerivedCategory.Qh.obj K :=
    (DerivedCategory.singleFunctorIsoCompQ A 0).app M ≪≫
      asIso (DerivedCategory.Q.map I.ι') ≪≫
      ((DerivedCategory.quotientCompQhIso A).app I.cochainComplex).symm
  let e' : RF.obj ((DerivedCategory.singleFunctor A 0).obj M) ≅
      DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex) :=
    RF.mapIso e ≪≫ (asIso (α.app K)).symm ≪≫
      DerivedCategory.Qh.mapIso
        ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I.cochainComplex) ≪≫
      (DerivedCategory.quotientCompQhIso B).app _
  exact (DerivedCategory.homologyFunctor B (n : ℤ)).mapIso e' ≪≫
    (DerivedCategory.homologyFunctorFactors B (n : ℤ)).app _ ≪≫
    (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ)).mapIso
      (mapHomologicalComplexExtendNatIso F I.cocomplex) ≪≫
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (by rfl) ≪≫
    (I.isoRightDerivedObj F n).symm

/-- For an object `M` placed in degree `a` of the unbounded derived category, the degree-`m`
cohomology of a right derived functor of `F` is the classical right derived functor `R^n F (M)`,
where `n = m - a`. -/
def homologyTotalRightDerivedSingleShiftIso (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (M : A) (a m : ℤ) (n : ℕ) (hn : m - a = n) :
    (DerivedCategory.homologyFunctor B m).obj
        (RF.obj ((DerivedCategory.singleFunctor A a).obj M)) ≅
      (F.rightDerived n).obj M := by
  letI := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
  let e : (DerivedCategory.singleFunctor A a).obj M ≅
      ((DerivedCategory.singleFunctor A 0).obj M)⟦-a⟧ :=
    ((DerivedCategory.singleFunctors A).shiftIso (-a) a 0 (by omega)).symm.app M
  exact (DerivedCategory.homologyFunctor B m).mapIso
      (RF.mapIso e ≪≫ (RF.commShiftIso (-a)).app _) ≪≫
    ((DerivedCategory.homologyFunctor B 0).shiftIso (-a) m (n : ℤ) (by omega)).app _ ≪≫
    homologyTotalRightDerivedSingleIso F RF α hres M n

/-- If the higher classical right derived functors of `F` vanish on `M`, then a right derived
functor of `F` applied to `M` placed in degree `a` has no cohomology above degree `a`. -/
lemma isZero_homologyTotalRightDerived_single_of_rightDerived_isZero (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (M : A) (hM : ∀ p : ℕ, 0 < p → IsZero ((F.rightDerived p).obj M))
    (a m : ℤ) (ham : a < m) :
    IsZero ((DerivedCategory.homologyFunctor B m).obj
      (RF.obj ((DerivedCategory.singleFunctor A a).obj M))) := by
  exact IsZero.of_iso (hM (m - a).toNat (by omega))
    (homologyTotalRightDerivedSingleShiftIso F RF α hres M a m (m - a).toNat (by omega))

/-- For a left exact `F`, a right derived functor of `F` applied to `M` placed in degree `a` has
degree-`a` cohomology `F (M)`. -/
def homologyTotalRightDerivedSingleSelfIso (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (M : A) (a : ℤ) :
    (DerivedCategory.homologyFunctor B a).obj
        (RF.obj ((DerivedCategory.singleFunctor A a).obj M)) ≅ F.obj M :=
  homologyTotalRightDerivedSingleShiftIso F RF α hres M a a 0 (by omega) ≪≫
    F.rightDerivedZeroIsoSelf.app M

end Single

end Stacks.DerivedFunctor

end
