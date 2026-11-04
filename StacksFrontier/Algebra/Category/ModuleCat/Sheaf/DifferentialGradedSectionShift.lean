module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeAdmissible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeDescEquiv
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionModule
public import StacksFrontier.Algebra.DifferentialGraded.Module.Bijective
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestrictionShift

/-!
# The sections of the shift of a differential graded module

Let `(A, d)` be a sheaf of differential graded algebras on a site, let `M` be a right
differential graded `A`-module and let `M[1]` be its degree-one shift, whose degree-`n` piece is
`M^{n + 1}` and whose right action is that of `M`. Taking sections over an object `U` commutes
with the shift: the differential graded `A(U)`-module of sections of `M[1]` is the shift of the
module `M(U)` of sections of `M`, by the isomorphism which sends a section of `M[1]^n = M^{n + 1}`
in the summand of degree `n` to the same section in the summand of degree `n + 1`. This
identification is compatible with restriction of sections.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.shiftSectionsIso`: the isomorphism
  `M[1](U) ≅ M(U)[1]` of differential graded `A(U)`-modules.

## Main results

* `SheafOfModules.DifferentialGradedModule.sectionModuleRestriction_shiftSectionsHom`: the
  identification commutes with restriction of sections.
-/

@[expose] public noncomputable section

open CategoryTheory

universe t a v u

namespace SheafOfModules

namespace DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R} (M : DifferentialGradedModule.{t, a, a} A) (U : Cᵒᵖ)

/-- The identification of the degree-`n` sections of the shift with the degree-`n + 1` sections
of the module. -/
def shiftSectionsApp (n : ℤ) : (shift M).sectionsPiece U n →+ M.sectionsPiece U (n + 1) :=
  AddMonoidHom.mk' (fun x ↦ ((shiftPackage M).xIso n).hom.val.app U x) fun x y ↦ map_add _ x y

/-- The identification `shiftSectionsApp` is evaluation of the degree-`n` component of the shift
isomorphism at `U`. -/
theorem shiftSectionsApp_apply (n : ℤ) (x : (shift M).sectionsPiece U n) :
    shiftSectionsApp M U n x = ((shiftPackage M).xIso n).hom.val.app U x :=
  rfl

/-- The identification of the total sections of the shift with the total sections of the
module, raising the degree by one. -/
def shiftSectionsAdd : (shift M).totalSections U →+ M.totalSections U :=
  DirectSum.toAddMonoid fun n ↦
    (DirectSum.of (M.sectionsPiece U) (n + 1)).comp (shiftSectionsApp M U n)

/-- `shiftSectionsAdd` sends a section of degree `n` of the shift to the same section in degree
`n + 1` of the module. -/
@[simp] theorem shiftSectionsAdd_of (n : ℤ) (x : (shift M).sectionsPiece U n) :
    shiftSectionsAdd M U (DirectSum.of ((shift M).sectionsPiece U) n x) =
      DirectSum.of (M.sectionsPiece U) (n + 1) (shiftSectionsApp M U n x) :=
  DirectSum.toAddMonoid_of _ n x

/-- The inverse identification on the degree-`p` sections of the module. -/
def shiftSectionsInvApp (p : ℤ) : M.sectionsPiece U p →+ (shift M).sectionsPiece U (p - 1) :=
  AddMonoidHom.mk'
    (fun y ↦ ((shiftPackage M).xIso (p - 1)).inv.val.app U
      (castHom M.complex.X (show p = p - 1 + 1 by omega) U y))
    fun x y ↦ by rw [map_add, map_add]

/-- The inverse identification of the total sections, lowering the degree by one. -/
def shiftSectionsInvAdd : M.totalSections U →+ (shift M).totalSections U :=
  DirectSum.toAddMonoid fun p ↦
    (DirectSum.of ((shift M).sectionsPiece U) (p - 1)).comp (shiftSectionsInvApp M U p)

/-- `shiftSectionsInvAdd` sends a section of degree `p` of the module to the corresponding
section in degree `p - 1` of the shift. -/
@[simp] theorem shiftSectionsInvAdd_of (p : ℤ) (y : M.sectionsPiece U p) :
    shiftSectionsInvAdd M U (DirectSum.of (M.sectionsPiece U) p y) =
      DirectSum.of ((shift M).sectionsPiece U) (p - 1) (shiftSectionsInvApp M U p y) :=
  DirectSum.toAddMonoid_of _ p y

private theorem shiftSections_iso_inv_hom {X Y : SheafOfModules.{a} R} (e : X ≅ Y)
    (x : X.val.obj U) :
    e.inv.val.app U (e.hom.val.app U x) = x := by
  simp [← comp_val_app_apply]

private theorem shiftSections_iso_hom_inv {X Y : SheafOfModules.{a} R} (e : X ≅ Y)
    (y : Y.val.obj U) :
    e.hom.val.app U (e.inv.val.app U y) = y := by
  simp [← comp_val_app_apply]

private theorem heq_xIso_inv_castHom {m n : ℤ} (hmn : m = n) (h : n + 1 = m + 1)
    (y : M.sectionsPiece U (n + 1)) :
    HEq (((shiftPackage M).xIso m).inv.val.app U (castHom M.complex.X h U y))
      (((shiftPackage M).xIso n).inv.val.app U y) := by
  subst hmn
  rfl

/-- `shiftSectionsInvAdd` is a left inverse of `shiftSectionsAdd`. -/
theorem shiftSectionsInvAdd_shiftSectionsAdd (x : (shift M).totalSections U) :
    shiftSectionsInvAdd M U (shiftSectionsAdd M U x) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of n p =>
      rw [shiftSectionsAdd_of, shiftSectionsInvAdd_of]
      refine of_heq (show n + 1 - 1 = n by omega) ?_
      refine (heq_xIso_inv_castHom M U (show n + 1 - 1 = n by omega) _ _).trans ?_
      exact heq_of_eq (shiftSections_iso_inv_hom U _ p)

/-- `shiftSectionsInvAdd` is a right inverse of `shiftSectionsAdd`. -/
theorem shiftSectionsAdd_shiftSectionsInvAdd (y : M.totalSections U) :
    shiftSectionsAdd M U (shiftSectionsInvAdd M U y) = y := by
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of p q =>
      rw [shiftSectionsInvAdd_of, shiftSectionsAdd_of]
      refine of_heq (show p - 1 + 1 = p by omega) ?_
      show HEq (((shiftPackage M).xIso (p - 1)).hom.val.app U
        (((shiftPackage M).xIso (p - 1)).inv.val.app U
          (castHom M.complex.X (show p = p - 1 + 1 by omega) U q))) q
      rw [shiftSections_iso_hom_inv]
      exact heq_castHom M.complex.X _ U q

/-- The identification of the total sections is compatible with the right actions. -/
theorem shiftSectionsAdd_act (x : (shift M).totalSections U)
    (s : A.toGradedAlgebra.totalSections U) :
    shiftSectionsAdd M U ((shift M).act U x s) = M.act U (shiftSectionsAdd M U x) s := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply, hx, hy]
  | of n p =>
      induction s using DirectSum.induction_on with
      | zero => simp only [map_zero]
      | add s s' hs hs' => simp only [map_add, hs, hs']
      | of i q =>
          rw [act_of, actOn_of, shiftSectionsAdd_of, shiftSectionsAdd_of, act_of, actOn_of]
          refine of_heq (show n + i + 1 = n + 1 + i by omega) ?_
          rw [shiftSectionsApp_apply, ShiftPackage.xIso_mul]
          exact heq_castHom M.complex.X _ U _

/-- The identification of the total sections is compatible with the differentials, the
differential of the shift being minus the differential of the module. -/
theorem shiftSectionsAdd_sectionD (x : (shift M).totalSections U) :
    shiftSectionsAdd M U ((shift M).sectionD U x) = -M.sectionD U (shiftSectionsAdd M U x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, neg_zero]
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  | of n p =>
      rw [sectionD_of, shiftSectionsAdd_of, shiftSectionsAdd_of, sectionD_of, ← map_neg]
      congr 1
      rw [shiftSectionsApp_apply, sectionDApp_apply, sectionDApp_apply, shiftSectionsApp_apply]
      have h := congrArg (fun φ : (M.complex.X (n + 1)) ⟶ (M.complex.X (n + 1 + 1)) ↦
        φ.val.app U (((shiftPackage M).xIso n).hom.val.app U p)) ((shiftPackage M).xIso_d n)
      simp only [comp_val_app_apply] at h
      rw [shiftSections_iso_inv_hom] at h
      rw [h]
      rfl

/-- **The sections of the shift are the shift of the sections**, as a homomorphism of
differential graded `A(U)`-modules. -/
def shiftSectionsHom :
    (shift M).sectionModule U ⟶
      (CategoryTheory.shiftFunctor (_root_.DifferentialGradedModule.{a, a, a}
        (A.sectionAlgebra U)) (1 : ℤ)).obj (M.sectionModule U) where
  toFun := uliftIntLinear (shiftSectionsAdd M U)
  map_smul x s := shiftSectionsAdd_act M U x s
  map_grading := by
    rintro n x ⟨p, rfl⟩
    change shiftSectionsAdd M U (DirectSum.of ((shift M).sectionsPiece U) n p) ∈
      Stacks.ExternalGrading.intSummand (M.sectionsPiece U) (n + 1)
    rw [shiftSectionsAdd_of]
    exact Stacks.ExternalGrading.of_mem_intSummand _ (n + 1) _
  map_d := LinearMap.ext fun (x : (shift M).totalSections U) ↦ by
    have h : ∀ y : (M.sectionModule U).M,
        ((CategoryTheory.shiftFunctor (_root_.DifferentialGradedModule.{a, a, a}
          (A.sectionAlgebra U)) (1 : ℤ)).obj (M.sectionModule U)).d y = -M.sectionD U y := by
      intro y
      change ((1 : ℤ).negOnePow • (M.sectionModule U).d) y = _
      rw [LinearMap.smul_apply, Int.negOnePow_one, Units.smul_def]
      simp only [Units.val_neg, Units.val_one, neg_smul, one_smul]
      rfl
    exact (shiftSectionsAdd_sectionD M U x).trans (h _).symm

/-- The underlying map of `shiftSectionsHom` is `shiftSectionsAdd`. -/
@[simp] theorem shiftSectionsHom_toFun (x : (shift M).totalSections U) :
    (shiftSectionsHom M U).toFun x = shiftSectionsAdd M U x :=
  rfl

/-- **The isomorphism `M[1](U) ≅ M(U)[1]`** of differential graded `A(U)`-modules. -/
def shiftSectionsIso :
    (shift M).sectionModule U ≅
      (CategoryTheory.shiftFunctor (_root_.DifferentialGradedModule.{a, a, a}
        (A.sectionAlgebra U)) (1 : ℤ)).obj (M.sectionModule U) :=
  _root_.DifferentialGradedModule.Hom.isoOfBijective (shiftSectionsHom M U)
    ⟨Function.LeftInverse.injective (g := shiftSectionsInvAdd M U)
      (shiftSectionsInvAdd_shiftSectionsAdd M U),
      Function.RightInverse.surjective (g := shiftSectionsInvAdd M U)
      (shiftSectionsAdd_shiftSectionsInvAdd M U)⟩

/-- The forward map of `shiftSectionsIso` is `shiftSectionsHom`. -/
@[simp] theorem shiftSectionsIso_hom : (shiftSectionsIso M U).hom = shiftSectionsHom M U :=
  rfl

/-- **The identification `M[1](U) ≅ M(U)[1]` commutes with restriction of sections**: restricting
the sections of the shift and then identifying is identifying and then restricting the sections
of the module, read through the commutation of restriction of scalars with the shift. -/
theorem sectionModuleRestriction_shiftSectionsHom {V : Cᵒᵖ} (a : V ⟶ U) :
    (shift M).sectionModuleRestriction a ≫
        _root_.DifferentialGradedModule.restrictScalarsHom (A.sectionRestriction a)
          (shiftSectionsHom M U) =
      shiftSectionsHom M V ≫
        (CategoryTheory.shiftFunctor _ (1 : ℤ)).map (M.sectionModuleRestriction a) ≫
        _root_.DifferentialGradedModule.restrictScalarsShiftInv (A.sectionRestriction a) 1
          (M.sectionModule U) := by
  refine _root_.DifferentialGradedModule.Hom.ext (LinearMap.ext fun x ↦ ?_)
  show shiftSectionsAdd M U ((shift M).sectionRestrictAdd a x) =
    M.sectionRestrictAdd a (shiftSectionsAdd M V x)
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of n p =>
      rw [sectionRestrictAdd_of, shiftSectionsAdd_of, shiftSectionsAdd_of, sectionRestrictAdd_of]
      congr 1
      rw [shiftSectionsApp_apply, sectionRestrictApp_apply, sectionRestrictApp_apply,
        shiftSectionsApp_apply]
      exact PresheafOfModules.naturality_apply ((shiftPackage M).xIso n).hom.val a p

end DifferentialGradedModule

end SheafOfModules

end
