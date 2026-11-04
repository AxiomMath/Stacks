module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAxiomA
public import StacksFrontier.CategoryTheory.DifferentialGraded.ExactFunctor
public import StacksFrontier.CategoryTheory.DifferentialGraded.Triangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCone
import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.ShiftFunctorStrict

/-!
# Axiom (B) for sheaf differential graded modules

Let `X` be a ringed site and let `A` be a sheaf of differential graded algebras on it. The
differential graded category `SheafOfModules.DifferentialGradedModule.dgCategoryData A` of right
differential graded `A`-modules, constructed for axiom (A), carries differential graded shift
functors in every integer degree together with compatible identifications of its Hom complexes.
This file constructs them and proves axiom (B) for that category.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.CanonicalShiftAxiomB`: axiom (B) for the differential
  graded category of right differential graded modules, pinned to the *canonical* shifts, namely
  the ones whose underlying complex is the shift of the underlying complex and whose right action
  is unchanged.
* `SheafOfModules.DifferentialGradedModule.asModule`,
  `SheafOfModules.DifferentialGradedModule.asObject`,
  `SheafOfModules.DifferentialGradedModule.asCochain`: the identifications of the objects and the
  homogeneous morphisms of that differential graded category with right differential graded
  modules and with action-linear cochains, read off from `DGCategoryData`.

## Main results

* `SheafOfModules.DifferentialGradedModule.shiftAxiomB`: axiom (B) holds, with the canonical
  shifts.

## Implementation notes

The shift of a module by `n` has the shifted underlying complex and the unchanged right action;
the shift of a homogeneous morphism of degree `k` has the unchanged component maps multiplied by
`(-1)^(n*k)`, and the Hom-complex identification has unchanged component maps. The degree-one
object shift therefore agrees with the shift `SheafOfModules.DifferentialGradedModule.shift`
fixed in the cone construction for tag 0FS5, which is the field `shift_one` of
`CanonicalShiftAxiomB`; this is what makes the cone sequence of axiom (C) comparable with these
shifts.

Pinning the shifts is the reason `CanonicalShiftAxiomB` is a structure rather than a bare
`CategoryTheory.DGCategory.ShiftAxiomB`: the latter asserts only that *some* shifts exist, and
the cone situation of tag 0FS6 needs the ones described above.

Since the objects and homogeneous morphisms of `dgCategoryData A` are identified with right
differential graded modules and action-linear cochains only up to an equality of types, all the
work happens under transports; the heterogeneous equalities below are those transports, and
nothing in them is a statement about differential graded modules that is not already a statement
about their underlying complexes and actions.

## References

* [Stacks Project, Tag 0FS4](https://stacks.math.columbia.edu/tag/0FS4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex

namespace SheafOfModules.DifferentialGradedModule

universe u v w t

/-- Transporting along `h` and then along `h.symm` is the identity. -/
theorem transport_cancel {α β : Type t} (h : α = β) (x : α) :
    h.symm ▸ (h ▸ x) = x := by cases h; rfl

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- Regard an object of the sheaf-module DG category as a DG module. -/
noncomputable def asModule
    (M : (dgCategoryData.{u, v, w} A).category.Obj) :
    DifferentialGradedModule.{u, v, w} A :=
  (dgCategoryData.{u, v, w} A).objects ▸ M

/-- Regard a DG module as an object of its DG category.

Deliberately not reducible: as an `abbrev` the two transport-level `rfl`s closing
`canonicalShiftAxiomB`'s shift-map clauses fail, one side elaborating through `Eq.mpr` and the
other through `cast`. -/
noncomputable def asObject (M : DifferentialGradedModule.{u, v, w} A) :
    (dgCategoryData.{u, v, w} A).category.Obj :=
  (dgCategoryData.{u, v, w} A).objects.symm ▸ M

/-- The two object transports cancel. -/
theorem asObject_asModule
    (M : (dgCategoryData.{u, v, w} A).category.Obj) :
    asObject A (asModule A M) = M :=
  transport_cancel (dgCategoryData.{u, v, w} A).objects M

/-- The cochain underlying a homogeneous morphism in the sheaf-module DG category. -/
noncomputable def asCochain
    {M N : (dgCategoryData.{u, v, w} A).category.Obj} {k : ℤ}
    (f : (dgCategoryData.{u, v, w} A).category.Hom
      M N k) :
    Cochain (asModule A M).complex (asModule A N).complex k := by
  let f' : (dgCategoryData.{u, v, w} A).category.Hom
      (asObject A (asModule A M)) (asObject A (asModule A N)) k := by
    rw [asObject_asModule A M, asObject_asModule A N]
    exact f
  exact ((dgCategoryData.{u, v, w} A).homs
    (asModule A M) (asModule A N) k ▸ f').val

/-- Axiom (B), pinned to the canonical shifts of sheaf DG modules. -/
structure CanonicalShiftAxiomB where
  /-- The shift functors and Hom-complex identifications of axiom (B). -/
  axiomB : DGCategory.ShiftAxiomB
    (dgCategoryData.{u, v, w} A).category
  /-- The shift of `M` by `n` has underlying complex the shift of the complex of `M` by `n`. -/
  shifted_complex : ∀ (n : ℤ) (M : DifferentialGradedModule.{u, v, w} A),
    (asModule A ((axiomB.shiftFunctor n).obj (asObject A M))).complex =
      (CochainComplex.shiftFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).obj M.complex
  /-- The right action of `A` on the shift of `M` by `n` in degree `p` is the action on `M` in
  degree `p + n`. -/
  shifted_action : ∀ (n : ℤ) (M : DifferentialGradedModule.{u, v, w} A)
      (p q : ℤ) (U : X.Cᵒᵖ),
    HEq (((asModule A ((axiomB.shiftFunctor n).obj (asObject A M))).mul p q).app U)
      ((M.mul (p + n) q).app U)
  /-- The shift by `1` is `SheafOfModules.DifferentialGradedModule.shift`. -/
  shift_one : ∀ (M : DifferentialGradedModule.{u, v, w} A),
    asModule A ((axiomB.shiftFunctor 1).obj (asObject A M)) =
      shift M
  /-- The shift by `n` of a morphism `f` of degree `k` has components those of `f`, shifted by
  `n` and multiplied by `(-1)^(n*k)`. -/
  shifted_map : ∀ (n k : ℤ) (M N : DifferentialGradedModule.{u, v, w} A)
      (f : (dgCategoryData.{u, v, w} A).category.Hom
        (asObject A M) (asObject A N) k)
      (p q : ℤ) (h : p + k = q),
    HEq ((asCochain A ((axiomB.shiftFunctor n).map f)).v p q h)
      ((Int.negOnePow (n * k) : ℤ) •
        (asCochain A f).v (p + n) (q + n) (by omega))
  /-- The identification of morphisms of degree `k + n` into `N` with morphisms of degree `k` into
  the shift of `N` by `n` leaves the component maps unchanged. -/
  toShift_components : ∀ (n k : ℤ) (M N : DifferentialGradedModule.{u, v, w} A)
      (f : (dgCategoryData.{u, v, w} A).category.Hom
        (asObject A M) (asObject A N) (k + n))
      (p q : ℤ) (h : p + k = q),
    HEq ((asCochain A ((axiomB.toShift n (asObject A M) (asObject A N) k) f)).v p q h)
      ((asCochain A f).v p (q + n) (by omega))

private theorem fixedShift_complex {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M : DifferentialGradedModule.{u, v, w} A) :
    (shift M).complex =
      (CochainComplex.shiftFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 1).obj M.complex :=
  (shiftPackage M).shifted_complex

private theorem fixedShift_action {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M : DifferentialGradedModule.{u, v, w} A) (p q : ℤ) (U : X.Cᵒᵖ) :
    HEq (((shift M).mul p q).app U) ((M.mul (p + 1) q).app U) :=
  (shiftPackage M).shifted_action p q U

private def castBilinearMapTarget {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {M P P' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {N : SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (h : P = P') (f : BilinearMap M N P) :
    BilinearMap M N P' := by
  subst P'
  exact f

private lemma castBilinearMapTarget_eval_heq {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {M P P' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {N : SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (h : P = P') (f : BilinearMap M N P) (U : X.Cᵒᵖ)
    (x : M.val.obj U) (a : N.val.obj U) :
    HEq ((castBilinearMapTarget h f).app U x a) ((f.app U x) a) := by cases h; rfl

private lemma castBilinearMapTarget_app_heq {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {M P P' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {N : SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (h : P = P') (f : BilinearMap M N P) (U : X.Cᵒᵖ) :
    HEq ((castBilinearMapTarget h f).app U) (f.app U) := by cases h; rfl

private lemma dependent_apply2_heq {ι κ : Type u} {B : ι → Type v} {C : κ → Type w}
    (f : ∀ i j, B i → C j) {i i' j j'} (hi : i = i') (hj : j = j')
    {x : B i} {y : B i'} (hxy : HEq x y) : HEq (f i j x) (f i' j' y) := by
  subst i' j'
  obtain rfl := eq_of_heq hxy
  rfl

private lemma gradedCast_neg_heq {ι : Type u} {B : ι → Type v} {i j : ι}
    [∀ i, AddGroup (B i)] (h : i = j) (x : B i) :
    HEq (-(SheafOfModules.gradedCast B h x)) (-x) := by subst j; rfl

private lemma sheafMap_neg_apply {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {P Q : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : P ⟶ Q) (U : X.Cᵒᵖ)
    (x : P.val.obj U) :
    (ConcreteCategory.hom ((-f).val.app U)) x =
      -(ConcreteCategory.hom (f.val.app U) x) := by
  change (ConcreteCategory.hom ((-f.val).app U)) x = _
  simp

private lemma sheafMap_scalarNeg_apply {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {P Q : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : P ⟶ Q) (U : X.Cᵒᵖ)
    (x : P.val.obj U) :
    (ConcreteCategory.hom (((-1 : ℤˣ) • f).val.app U)) x =
      -(ConcreteCategory.hom (f.val.app U) x) := by
  have h : (-1 : ℤˣ) • f = -f := by simp
  have h' := congrArg (fun g => ConcreteCategory.hom (g.val.app U)) h
  calc
    (ConcreteCategory.hom (((-1 : ℤ) • f).val.app U)) x =
        (ConcreteCategory.hom ((-f).val.app U)) x := congrArg (fun g => g x) h'
    _ = -(ConcreteCategory.hom (f.val.app U) x) := sheafMap_neg_apply f U x

private lemma dependent_add_heq {ι : Type u} {B : ι → Type v} [∀ i, Add (B i)]
    {i j : ι} (h : i = j) {x₁ y₁ : B i} {x₂ y₂ : B j}
    (hx : HEq x₁ x₂) (hy : HEq y₁ y₂) : HEq (x₁ + y₁) (x₂ + y₂) := by
  subst j
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  rfl

@[implicit_reducible] private noncomputable def shiftedModule
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M : DifferentialGradedModule.{u, v, w} A) (s : ℤ) :
    DifferentialGradedModule.{u, v, w} A := by
  let C := (CochainComplex.shiftFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) s).obj M.complex
  let μ (p q : ℤ) : BilinearMap (C.X p) (A.complex.X q) (C.X (p + q)) :=
    castBilinearMapTarget
      (congrArg M.complex.X (show (p + s) + q = (p + q) + s by omega))
      (M.mul (p + s) q)
  exact {
    complex := C
    mul := μ
    mul_assoc := by
      intro p q r U x a b
      let i := (p + q) + s
      let j := (p + s) + q
      have hij : i = j := by dsimp [i, j]; omega
      have hx : HEq ((μ p q).app U x a) ((M.mul (p + s) q).app U x a) :=
        castBilinearMapTarget_eval_heq
          (congrArg M.complex.X (show (p + s) + q = (p + q) + s by omega))
          (M.mul (p + s) q) U x a
      have h₁ := castBilinearMapTarget_eval_heq
        (congrArg M.complex.X (show ((p + q) + s) + r = ((p + q) + r) + s by omega))
        (M.mul ((p + q) + s) r) U ((μ p q).app U x a) b
      have h₂ := castBilinearMapTarget_eval_heq
        (congrArg M.complex.X (show (p + s) + (q + r) = (p + (q + r)) + s by omega))
        (M.mul (p + s) (q + r)) U x ((A.mul q r).app U a b)
      have hm := heq_dependent_apply
        (fun d : ℤ => fun y : (M.complex.X d).val.obj U => ((M.mul d r).app U y) b)
        hij hx
      exact h₁.trans (hm.trans ((M.mul_assoc (p + s) q r U x a b).trans h₂.symm))
    mul_one := by
      intro p U x
      exact (castBilinearMapTarget_eval_heq
        (congrArg M.complex.X (show (p + s) + 0 = (p + 0) + s by omega))
        (M.mul (p + s) 0) U x (A.one.eval U)).trans (M.mul_one (p + s) U x)
    leibniz := by
      intro p q U x a
      have hmul := castBilinearMapTarget_eval_heq
        (congrArg M.complex.X (show (p + s) + q = (p + q) + s by omega))
        (M.mul (p + s) q) U x a
      have hAction2 : HEq
          (((μ p (q + 1)).app U) x ((A.complex.d q (q + 1)).val.app U a))
          (((M.mul (p + s) (q + 1)).app U) x
            ((A.complex.d q (q + 1)).val.app U a)) :=
        castBilinearMapTarget_eval_heq
          (congrArg M.complex.X (show (p + s) + (q + 1) = (p + (q + 1)) + s by omega))
          (M.mul (p + s) (q + 1)) U x ((A.complex.d q (q + 1)).val.app U a)
      let tgt₁ := SheafOfModules.gradedCast (fun d => (C.X d).val.obj U)
        (add_right_comm p 1 q) (((μ (p + 1) q).app U)
          ((C.d p (p + 1)).val.app U x) a)
      have hC : HEq
          (((μ (p + 1) q).app U) ((C.d p (p + 1)).val.app U x) a) tgt₁ := by
        dsimp [tgt₁]
        exact (gradedCast_heq (T := fun d => (C.X d).val.obj U)
          (add_right_comm p 1 q)
          (((μ (p + 1) q).app U) ((C.d p (p + 1)).val.app U x) a)).symm
      let src₂ := (p.negOnePow : ℤ) • SheafOfModules.gradedCast
        (fun d => (M.complex.X d).val.obj U) (add_assoc (p + s) q 1).symm
        (((M.mul (p + s) (q + 1)).app U x)
          ((A.complex.d q (q + 1)).val.app U a))
      let tgt₂ := (p.negOnePow : ℤ) • SheafOfModules.gradedCast
        (fun d => (C.X d).val.obj U) (add_assoc p q 1).symm
        (((μ p (q + 1)).app U) x ((A.complex.d q (q + 1)).val.app U a))
      have hSecond : HEq src₂ tgt₂ := by
        have hRaw : HEq
            (SheafOfModules.gradedCast
              (fun d => (M.complex.X d).val.obj U) (add_assoc (p + s) q 1).symm
              (((M.mul (p + s) (q + 1)).app U x)
                ((A.complex.d q (q + 1)).val.app U a)))
            (SheafOfModules.gradedCast
              (fun d => (C.X d).val.obj U) (add_assoc p q 1).symm
              (((μ p (q + 1)).app U) x ((A.complex.d q (q + 1)).val.app U a))) :=
          (gradedCast_heq (T := fun d => (M.complex.X d).val.obj U)
              (add_assoc (p + s) q 1).symm
              (((M.mul (p + s) (q + 1)).app U x)
                ((A.complex.d q (q + 1)).val.app U a))).trans
            (hAction2.symm.trans (gradedCast_heq (T := fun d => (C.X d).val.obj U)
              (add_assoc p q 1).symm
              (((μ p (q + 1)).app U) x ((A.complex.d q (q + 1)).val.app U a))).symm)
        dsimp [C] at hRaw ⊢
        exact heq_dependent_apply
            (fun d : ℤ => fun y : (M.complex.X d).val.obj U =>
              (p.negOnePow : ℤ) • y)
          (show (p + s + q) + 1 = (p + q + 1) + s by omega) hRaw
      have hSum : ∀ src₁ : (M.complex.X (p + s + q + 1)).val.obj U,
          HEq src₁ tgt₁ → HEq (src₁ + src₂) (tgt₁ + tgt₂) := fun src₁ hFirst => by
        dsimp [C] at hFirst hSecond
        have hR := dependent_add_heq (B := fun d => (M.complex.X d).val.obj U)
          (show (p + s + q) + 1 = (p + q + 1) + s by omega) hFirst hSecond
        dsimp [src₂, tgt₁, tgt₂] at hR
        exact hR
      rcases Int.even_or_odd s with hEven | hOdd
      · have hsign : (p + s).negOnePow = p.negOnePow := by
          rw [Int.negOnePow_add, Int.negOnePow_even s hEven]
          simp
        have h := M.leibniz (p + s) q U x a
        rw [hsign] at h
        have hL : HEq
            (((C.d (p + q) (p + q + 1)).val.app U) ((μ p q).app U x a))
            (((M.complex.d (p + s + q) (p + s + q + 1)).val.app U)
              ((M.mul (p + s) q).app U x a)) := by
          dsimp [C, μ]
          simp only [Int.negOnePow_even s hEven, one_smul]
          exact dependent_apply2_heq
            (fun d e : ℤ => fun y : (M.complex.X d).val.obj U =>
              (M.complex.d d e).val.app U y)
            (show p + q + s = p + s + q by omega)
            (show p + q + 1 + s = p + s + q + 1 by omega) hmul
        have hShiftD : HEq
            (((C.d p (p + 1)).val.app U) x)
            (((M.complex.d (p + s) (p + s + 1)).val.app U) x) := by
          have hEnd : p + 1 + s = p + s + 1 := by omega
          dsimp [C]
          simp only [Int.negOnePow_even s hEven, one_smul]
          exact dependent_apply2_heq
            (fun d e : ℤ => fun y : (M.complex.X d).val.obj U =>
              (M.complex.d d e).val.app U y) rfl hEnd HEq.rfl
        have hAction1 : HEq
            (((μ (p + 1) q).app U) ((C.d p (p + 1)).val.app U x) a)
            (((M.mul (p + s + 1) q).app U)
              ((M.complex.d (p + s) (p + s + 1)).val.app U x) a) := by
          dsimp [μ]
          exact (castBilinearMapTarget_eval_heq
            (congrArg M.complex.X (show (p + 1 + s) + q = (p + 1 + q) + s by omega))
            (M.mul (p + 1 + s) q) U ((C.d p (p + 1)).val.app U x) a).trans
            (heq_dependent_apply
              (fun d : ℤ => fun y : (M.complex.X d).val.obj U =>
                (M.mul d q).app U y a)
              (show p + 1 + s = p + s + 1 by omega) hShiftD)
        have hFirst := (gradedCast_heq (T := fun d => (M.complex.X d).val.obj U)
          (add_right_comm (p + s) 1 q)
          (((M.mul (p + s + 1) q).app U)
            ((M.complex.d (p + s) (p + s + 1)).val.app U x) a)).trans
          (hAction1.symm.trans hC)
        exact eq_of_heq (hL.trans ((heq_of_eq h).trans (hSum _ hFirst)))
      · have hsign : (p + s).negOnePow = -p.negOnePow := by
          rw [Int.negOnePow_add, Int.negOnePow_odd s hOdd]
          simp
        have h := M.leibniz (p + s) q U x a
        have h :
            -(((M.complex.d (p + s + q) (p + s + q + 1)).val.app U)
              (((M.mul (p + s) q).app U) x a)) =
            -SheafOfModules.gradedCast (fun d => (M.complex.X d).val.obj U)
                (add_right_comm (p + s) 1 q)
                (((M.mul (p + s + 1) q).app U)
                  ((M.complex.d (p + s) (p + s + 1)).val.app U x) a) +
              src₂ := by
          have h' := congrArg Neg.neg h
          rw [hsign] at h'
          simp only [neg_add, Units.val_neg, neg_smul, neg_neg] at h'
          exact h'
        have hL : HEq
            (((C.d (p + q) (p + q + 1)).val.app U) ((μ p q).app U x a))
            (-(((M.complex.d (p + s + q) (p + s + q + 1)).val.app U)
              ((M.mul (p + s) q).app U x a))) := by
          dsimp [C, μ]
          rw [Int.negOnePow_odd s hOdd]
          have hD := dependent_apply2_heq
            (fun d e : ℤ => fun y : (M.complex.X d).val.obj U =>
              (ConcreteCategory.hom (((-1 : ℤˣ) • M.complex.d d e).val.app U)) y)
            (show p + q + s = p + s + q by omega)
            (show p + q + 1 + s = p + s + q + 1 by omega) hmul
          exact hD.trans (heq_of_eq (sheafMap_scalarNeg_apply
            (M.complex.d (p + s + q) (p + s + q + 1)) U
            (((M.mul (p + s) q).app U) x a)))
        have hShiftD : HEq
            (((C.d p (p + 1)).val.app U) x)
            (-((M.complex.d (p + s) (p + s + 1)).val.app U x)) := by
          have hEnd : p + 1 + s = p + s + 1 := by omega
          dsimp [C]
          rw [Int.negOnePow_odd s hOdd]
          let x' : (M.complex.X (p + s)).val.obj U := x
          have hD := dependent_apply2_heq
            (fun d e : ℤ => fun y : (M.complex.X d).val.obj U =>
              (ConcreteCategory.hom (((-1 : ℤˣ) • M.complex.d d e).val.app U)) y)
            (i := p + s) (i' := p + s)
            (j := p + 1 + s) (j' := p + s + 1) (x := x') (y := x')
            rfl hEnd HEq.rfl
          exact hD.trans (heq_of_eq (sheafMap_scalarNeg_apply
            (M.complex.d (p + s) (p + s + 1)) U x))
        have hAction1 : HEq
            (((μ (p + 1) q).app U) ((C.d p (p + 1)).val.app U x) a)
            (-((((M.mul (p + s + 1) q).app U)
              ((M.complex.d (p + s) (p + s + 1)).val.app U x)) a)) := by
          dsimp [μ]
          have hCast := castBilinearMapTarget_eval_heq
            (congrArg M.complex.X (show (p + 1 + s) + q = (p + 1 + q) + s by omega))
            (M.mul (p + 1 + s) q) U ((C.d p (p + 1)).val.app U x) a
          have hMap := heq_dependent_apply
            (fun d : ℤ => fun y : (M.complex.X d).val.obj U =>
              ((M.mul d q).app U y) a)
            (show p + 1 + s = p + s + 1 by omega) hShiftD
          have hNeg :
              ((((M.mul (p + s + 1) q).app U)
                (-((M.complex.d (p + s) (p + s + 1)).val.app U x))) a) =
              -((((M.mul (p + s + 1) q).app U)
                ((M.complex.d (p + s) (p + s + 1)).val.app U x)) a) := by
            simp
          exact hCast.trans (hMap.trans (heq_of_eq hNeg))
        have hFirst := (gradedCast_neg_heq (B := fun d => (M.complex.X d).val.obj U)
          (add_right_comm (p + s) 1 q)
          (((M.mul (p + s + 1) q).app U)
            ((M.complex.d (p + s) (p + s + 1)).val.app U x) a)).trans
          (hAction1.symm.trans hC)
        exact eq_of_heq (hL.trans ((heq_of_eq h).trans (hSum _ hFirst)))
  }

private theorem shiftedModule_complex {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M : DifferentialGradedModule.{u, v, w} A) (s : ℤ) :
    (shiftedModule M s).complex =
      (CochainComplex.shiftFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) s).obj M.complex := rfl

private theorem shiftedModule_action {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M : DifferentialGradedModule.{u, v, w} A) (s p q : ℤ) (U : X.Cᵒᵖ)
    (x : ((shiftedModule M s).complex.X p).val.obj U)
    (a : (A.complex.X q).val.obj U) :
    HEq ((((shiftedModule M s).mul p q).app U) x a)
      (((M.mul (p + s) q).app U) x a) :=
  castBilinearMapTarget_eval_heq
    (congrArg M.complex.X (show (p + s) + q = (p + q) + s by omega))
    (M.mul (p + s) q) U x a

private theorem shiftedModule_action_map {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M : DifferentialGradedModule.{u, v, w} A) (s p q : ℤ) (U : X.Cᵒᵖ) :
    HEq (((shiftedModule M s).mul p q).app U) ((M.mul (p + s) q).app U) := by
  change HEq ((castBilinearMapTarget
      (congrArg M.complex.X (show (p + s) + q = (p + q) + s by omega))
      (M.mul (p + s) q)).app U) ((M.mul (p + s) q).app U)
  exact castBilinearMapTarget_app_heq _ _ U

private lemma dependent_value_heq {ι : Type*} {B : ι → Sort*}
    (f : ∀ i, B i) {i j : ι} (h : i = j) : HEq (f i) (f j) := by subst j; rfl

private lemma module_ext {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {M N : DifferentialGradedModule.{u, v, w} A}
    (hc : M.complex = N.complex)
    (hm : ∀ p q U, HEq ((M.mul p q).app U) ((N.mul p q).app U)) : M = N := by
  rcases M with ⟨MC, μ, ma, mo, ml⟩
  rcases N with ⟨NC, ν, na, no, nl⟩
  dsimp only at hc hm
  subst NC
  have hμ : μ = ν := by
    funext p q
    have ha : (μ p q).app = (ν p q).app := funext (fun U => eq_of_heq (hm p q U))
    have hext : ∀ (f g : BilinearMap (MC.X p) (A.complex.X q)
        (MC.X (p + q))), f.app = g.app → f = g := by
      rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h
      cases h
      rfl
    exact hext _ _ ha
  subst ν
  rfl

private lemma shiftedModule_zero {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M : DifferentialGradedModule.{u, v, w} A) : shiftedModule M 0 = M := by
  apply module_ext
  · apply HomologicalComplex.ext_of_iso
      ((CochainComplex.shiftFunctorZero'
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0 rfl).app M.complex)
    · intro p
      simp
  · intro p q U
    exact (shiftedModule_action_map M 0 p q U).trans
      (dependent_value_heq (fun p => (M.mul p q).app U) (add_zero p))

private lemma shiftedModule_one {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M : DifferentialGradedModule.{u, v, w} A) : shiftedModule M 1 = shift M := by
  apply module_ext
  · exact (shiftedModule_complex M 1).trans (fixedShift_complex M).symm
  · intro p q U
    exact (shiftedModule_action_map M 1 p q U).trans (fixedShift_action M p q U).symm

private lemma shiftedModule_add {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M : DifferentialGradedModule.{u, v, w} A) (n m : ℤ) :
    shiftedModule M (n + m) = shiftedModule (shiftedModule M m) n := by
  apply module_ext
  · apply HomologicalComplex.ext_of_iso
      ((CochainComplex.shiftFunctorAdd'
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        m n (n + m) (add_comm m n)).app M.complex)
    · intro p
      dsimp
      congr 1
      omega
  · intro p q U
    have h := (shiftedModule_action_map (shiftedModule M m) n p q U).trans
      (shiftedModule_action_map M m (p + n) q U)
    exact (shiftedModule_action_map M (n + m) p q U).trans
      ((h.trans (dependent_value_heq (fun p => (M.mul p q).app U) (add_assoc p n m))).symm)

/-- Applying `eqToHom h` for an equality `h : P = Q` of sheaves of modules to a section `x` gives
a section heterogeneously equal to `x`. -/
lemma sheaf_eqToHom_apply_heq {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {P Q : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (h : P = Q) (U : X.Cᵒᵖ)
    (x : P.val.obj U) : HEq ((eqToHom h).val.app U x) x := by cases h; rfl

private noncomputable def shiftHom {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    HomogeneousMap A (shiftedModule M n) M n := by
  refine ⟨Cochain.mk (fun p q h => eqToHom (congrArg M.complex.X h)), ?_⟩
  intro p q m hpq U x a
  have h₁ := sheaf_eqToHom_apply_heq
    (congrArg M.complex.X (show p + m + n = q + m by omega)) U
    (((shiftedModule M n).mul p m).app U x a)
  have h₂ := shiftedModule_action M n p m U x a
  have h₃ := heq_dependent_apply
    (fun d => fun x : (M.complex.X d).val.obj U => (M.mul d m).app U x a)
    hpq (sheaf_eqToHom_apply_heq (congrArg M.complex.X hpq) U x).symm
  exact h₁.trans (h₂.trans h₃)

private noncomputable def shiftInv {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    HomogeneousMap A M (shiftedModule M n) (-n) := by
  refine ⟨Cochain.mk (fun p q h =>
    eqToHom (congrArg M.complex.X (show p = q + n by omega))), ?_⟩
  intro p q m hpq U x a
  have hpn : p = q + n := by omega
  let y := (eqToHom (congrArg M.complex.X hpn)).val.app U x
  have h₁ := sheaf_eqToHom_apply_heq
    (congrArg M.complex.X (show p + m = q + m + n by omega)) U
    ((M.mul p m).app U x a)
  have h₂ := heq_dependent_apply
    (fun d => fun x : (M.complex.X d).val.obj U => (M.mul d m).app U x a)
    hpn (sheaf_eqToHom_apply_heq (congrArg M.complex.X hpn) U x).symm
  have h₃ := shiftedModule_action M n q m U y a
  exact h₁.trans (h₂.trans h₃.symm)

private lemma shiftHom_comp_shiftInv {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    (shiftHom M n).val.comp (shiftInv M n).val (add_neg_cancel n) =
      Cochain.ofHom (𝟙 (shiftedModule M n).complex) := by
  apply Cochain.ext₀
  intro p
  rw [Cochain.comp_v _ _ _ p (p + n) p rfl (by omega)]
  simp [shiftHom, shiftInv]

private lemma shiftInv_comp_shiftHom {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    (shiftInv M n).val.comp (shiftHom M n).val (neg_add_cancel n) =
      Cochain.ofHom (𝟙 M.complex) := by
  apply Cochain.ext₀
  intro p
  rw [Cochain.comp_v _ _ _ p (p - n) p (by omega) (by omega)]
  simp [shiftHom, shiftInv]

/-- The DG module corresponding to an object of the DG category of `D`. -/
abbrev moduleOf (D : DGCategoryData.{u, v, w} A)
    (M : D.category.Obj) : DifferentialGradedModule.{u, v, w} A := D.objects ▸ M

/-- `moduleObject` is a left inverse of `moduleOf`. -/
lemma moduleObject_moduleOf (D : DGCategoryData.{u, v, w} A)
    (M : D.category.Obj) : moduleObject A D (moduleOf A D M) = M :=
  transport_cancel D.objects M

/-- The homogeneous map of DG modules corresponding to a homogeneous morphism of the DG category
of `D`. -/
def homogeneousOf (D : DGCategoryData.{u, v, w} A)
    {M N : D.category.Obj} {k : ℤ} (f : D.category.Hom M N k) :
    HomogeneousMap A (moduleOf A D M) (moduleOf A D N) k := by
  let f' : D.category.Hom (moduleObject A D (moduleOf A D M))
      (moduleObject A D (moduleOf A D N)) k := by
    rw [moduleObject_moduleOf A D M, moduleObject_moduleOf A D N]
    exact f
  exact D.homs (moduleOf A D M) (moduleOf A D N) k ▸ f'

/-- `homogeneousOf` is bijective. -/
lemma homogeneousOf_bijective
    (D : DGCategoryData.{u, v, w} A)
    (M N : D.category.Obj) (k : ℤ) :
    Function.Bijective (homogeneousOf A D (M := M) (N := N) (k := k)) := by
  rcases D with ⟨C, ho, hh, _hadd, hd, hc, hi⟩
  rcases C with ⟨O, H, ac, mo, d, da, ds, dd, c, ca, cb, cs, ct, dl, ass, id, il, ir, di⟩
  dsimp only at ho
  subst O
  have he : H = HomogeneousMap A := by
    funext M N n
    exact hh M N n
  subst H
  exact Function.bijective_id

/-- The bijection between homogeneous morphisms of degree `k` of the DG category of `D` and
homogeneous maps of degree `k` of the corresponding DG modules, given by `homogeneousOf`. -/
noncomputable def homogeneousEquiv
    (D : DGCategoryData.{u, v, w} A)
    (M N : D.category.Obj) (k : ℤ) :
    D.category.Hom M N k ≃
      HomogeneousMap A (moduleOf A D M) (moduleOf A D N) k :=
  Equiv.ofBijective (homogeneousOf A D) (homogeneousOf_bijective A D M N k)

/-- The cochain underlying the homogeneous map `homogeneousOf A D f`. -/
abbrev cochainOf (D : DGCategoryData.{u, v, w} A)
    {M N : D.category.Obj} {k : ℤ} (f : D.category.Hom M N k) :=
  (homogeneousOf A D f).val

/-- `cochainOf` sends the composite `g ∘ f` to the composite of cochains of `f` and `g`. -/
lemma cochainOf_comp
    (D : DGCategoryData.{u, v, w} A)
    {M N P : D.category.Obj} {m n k : ℤ} (h : m + n = k)
    (g : D.category.Hom N P m) (f : D.category.Hom M N n) :
    cochainOf A D (D.category.comp h g f) =
      (cochainOf A D f).comp (cochainOf A D g) (by omega) := by
  rcases D with ⟨C, ho, hh, _hadd, hd, hc, hi⟩
  rcases C with ⟨O, H, ac, mo, d, da, ds, dd, c, ca, cb, cs, ct, dl, ass, id, il, ir, di⟩
  dsimp only at ho
  subst O
  have he : H = HomogeneousMap A := by
    funext M N n
    exact hh M N n
  subst H
  exact eq_of_heq (hc M N P m n k h g f)

/-- `cochainOf` is injective. -/
lemma cochainOf_injective
    (D : DGCategoryData.{u, v, w} A)
    {M N : D.category.Obj} {k : ℤ} : Function.Injective
      (cochainOf A D (M := M) (N := N) (k := k)) :=
  Subtype.val_injective.comp (homogeneousOf_bijective A D M N k).injective

private lemma cochainOf_id
    (D : DGCategoryData.{u, v, w} A)
    (M : D.category.Obj) : cochainOf A D (D.category.id M) =
      Cochain.ofHom (𝟙 (moduleOf A D M).complex) := by
  rcases D with ⟨C, ho, hh, _hadd, hd, hc, hi⟩
  rcases C with ⟨O, H, ac, mo, d, da, ds, dd, c, ca, cb, cs, ct, dl, ass, id, il, ir, di⟩
  dsimp only at ho
  subst O
  have he : H = HomogeneousMap A := by
    funext M N n
    exact hh M N n
  subst H
  exact eq_of_heq (hi M)

private lemma cochainOf_d
    (D : DGCategoryData.{u, v, w} A)
    {M N : D.category.Obj} {k : ℤ} (f : D.category.Hom M N k) :
    cochainOf A D (D.category.d f) = δ k (k + 1) (cochainOf A D f) := by
  rcases D with ⟨C, ho, hh, _hadd, hd, hc, hi⟩
  rcases C with ⟨O, H, ac, mo, d, da, ds, dd, c, ca, cb, cs, ct, dl, ass, id, il, ir, di⟩
  dsimp only at ho
  subst O
  have he : H = HomogeneousMap A := by
    funext M N n
    exact hh M N n
  subst H
  exact eq_of_heq (hd M N k f)

/-- `cochainOf` sends the zero morphism to the zero cochain. -/
lemma cochainOf_zero
    (D : DGCategoryData.{u, v, w} A)
    (M N : D.category.Obj) (k : ℤ) :
    cochainOf A D (0 : D.category.Hom M N k) = 0 := by
  let z := (homogeneousEquiv A D N N 0).symm
    ⟨0, actionLinear_zero A (moduleOf A D N) (moduleOf A D N) 0⟩
  have hz : cochainOf A D z = 0 :=
    congrArg Subtype.val ((homogeneousEquiv A D N N 0).apply_symm_apply _)
  have h := cochainOf_comp A D (zero_add k) z (0 : D.category.Hom M N k)
  simpa only [DGCategory.comp_zero_right, hz, Cochain.comp_zero] using h

/-- Two homogeneous morphisms into a binary biproduct in a DG category are equal if their
composites with both projections are equal. -/
lemma biproduct_hom_ext_to {R : Type*} [CommRing R] (D : DGCategory R)
    {M N P : D.Obj} (B : DGCategory.BinaryBiproductData D M N)
    {k : ℤ} (f g : D.Hom P B.pt k)
    (hp : D.comp (zero_add k) B.fst f = D.comp (zero_add k) B.fst g)
    (hq : D.comp (zero_add k) B.snd f = D.comp (zero_add k) B.snd g) : f = g := by
  calc
    f = D.comp (zero_add k) (D.id B.pt) f := (D.id_comp f).symm
    _ = D.comp (zero_add k) (D.comp rfl B.inl B.fst + D.comp rfl B.inr B.snd) f := by
      rw [B.fst_inl_add_snd_inr]
    _ = D.comp (zero_add k) (D.comp rfl B.inl B.fst + D.comp rfl B.inr B.snd) g := by
      simp only [D.comp_add_left, ← D.assoc (zero_add k) (zero_add k) rfl (zero_add k), hp, hq]
    _ = g := by rw [B.fst_inl_add_snd_inr, D.id_comp]

/-- `cochainOf` is additive, given a binary biproduct of `M` with itself. -/
lemma cochainOf_add
    (D : DGCategoryData.{u, v, w} A)
    {M N : D.category.Obj} {k : ℤ}
    (B : DGCategory.BinaryBiproductData D.category M M)
    (f g : D.category.Hom M N k) :
    cochainOf A D (f + g) = cochainOf A D f + cochainOf A D g := by
  let C := D.category
  let i := B.inl
  let j := B.inr
  let p := B.fst
  let q := B.snd
  let c := (homogeneousEquiv A D M B.pt 0).symm
    ⟨cochainOf A D i + cochainOf A D j,
      actionLinear_add A _ _ (homogeneousOf A D i).property (homogeneousOf A D j).property⟩
  have hc : cochainOf A D c = cochainOf A D i + cochainOf A D j :=
    congrArg Subtype.val ((homogeneousEquiv A D M B.pt 0).apply_symm_apply _)
  have hcp : C.comp rfl p c = C.id M := by
    apply cochainOf_injective A D
    rw [cochainOf_comp, hc, Cochain.add_comp, ← cochainOf_comp A D (rfl : (0 : ℤ) + 0 = 0),
      ← cochainOf_comp A D (rfl : (0 : ℤ) + 0 = 0),
      B.inl_fst, B.inr_fst, cochainOf_zero]
    simp only [add_zero]
    all_goals rfl
  have hcq : C.comp rfl q c = C.id M := by
    apply cochainOf_injective A D
    rw [cochainOf_comp, hc, Cochain.add_comp, ← cochainOf_comp A D (rfl : (0 : ℤ) + 0 = 0),
      ← cochainOf_comp A D (rfl : (0 : ℤ) + 0 = 0),
      B.inl_snd, B.inr_snd, cochainOf_zero]
    simp only [zero_add]
    all_goals rfl
  have hc' : c = i + j := by
    apply biproduct_hom_ext_to C B
    · rw [C.comp_add_right, hcp, B.inl_fst, B.inr_fst, add_zero]
    · rw [C.comp_add_right, hcq, B.inl_snd, B.inr_snd, zero_add]
  let fp := C.comp (add_zero k) f p
  let gq := C.comp (add_zero k) g q
  let r := (homogeneousEquiv A D B.pt N k).symm
    ⟨cochainOf A D fp + cochainOf A D gq,
      actionLinear_add A _ _ (homogeneousOf A D fp).property (homogeneousOf A D gq).property⟩
  have hr : cochainOf A D r = cochainOf A D fp + cochainOf A D gq :=
    congrArg Subtype.val ((homogeneousEquiv A D B.pt N k).apply_symm_apply _)
  have hri : C.comp (add_zero k) r i = f := by
    apply cochainOf_injective A D
    rw [cochainOf_comp, hr, Cochain.comp_add,
      ← cochainOf_comp A D (add_zero k), ← cochainOf_comp A D (add_zero k)]
    dsimp only [fp, gq]
    rw [← C.assoc rfl (add_zero k) (add_zero k) (add_zero k),
      ← C.assoc rfl (add_zero k) (add_zero k) (add_zero k),
      B.inl_fst, B.inl_snd, C.comp_id, C.comp_zero_right, cochainOf_zero, add_zero]
  have hrj : C.comp (add_zero k) r j = g := by
    apply cochainOf_injective A D
    rw [cochainOf_comp, hr, Cochain.comp_add,
      ← cochainOf_comp A D (add_zero k), ← cochainOf_comp A D (add_zero k)]
    dsimp only [fp, gq]
    rw [← C.assoc rfl (add_zero k) (add_zero k) (add_zero k),
      ← C.assoc rfl (add_zero k) (add_zero k) (add_zero k),
      B.inr_fst, B.inr_snd, C.comp_zero_right, C.comp_id, cochainOf_zero, zero_add]
  have hrc : C.comp (add_zero k) r c = f + g := by
    rw [hc', C.comp_add_right, hri, hrj]
  rw [← hrc, cochainOf_comp, hc, Cochain.add_comp,
    ← cochainOf_comp A D (add_zero k), ← cochainOf_comp A D (add_zero k), hri, hrj]

private noncomputable def cochainOfAddHom
    (D : DGCategoryData.{u, v, w} A)
    (B : ∀ M, Nonempty (DGCategory.BinaryBiproductData D.category M M))
    (M N : D.category.Obj) (k : ℤ) :
    D.category.Hom M N k →+ Cochain (moduleOf A D M).complex (moduleOf A D N).complex k where
  toFun := cochainOf A D
  map_zero' := cochainOf_zero A D M N k
  map_add' := cochainOf_add A D (Classical.choice (B M))

private lemma cochainOf_zsmul
    (D : DGCategoryData.{u, v, w} A)
    (B : ∀ M, Nonempty (DGCategory.BinaryBiproductData D.category M M))
    {M N : D.category.Obj} {k : ℤ} (s : ℤ) (f : D.category.Hom M N k) :
    cochainOf A D (s • f) = s • cochainOf A D f :=
  (cochainOfAddHom A D B M N k).map_zsmul s f

private lemma cochainOf_sign
    (D : DGCategoryData.{u, v, w} A)
    (B : ∀ M, Nonempty (DGCategory.BinaryBiproductData D.category M M))
    {M N : D.category.Obj} {k : ℤ} (s : ℤ) (f : D.category.Hom M N k) :
    cochainOf A D ((-1 : (CategoryTheory.Limits.limit X.O.obj : CommRingCat)) ^ s.natAbs • f) =
      (s.negOnePow : ℤ) • cochainOf A D f := by
  rw [← Int.coe_negOnePow, Int.cast_smul_eq_zsmul]
  exact cochainOf_zsmul A D B _ f

private noncomputable def homogeneousTo
    (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    (f : HomogeneousMap A M N k) :
    D.category.Hom (moduleObject A D M) (moduleObject A D N) k :=
  D.homs M N k ▸ f

private noncomputable def shiftObjectOf
    (D : DGCategoryData.{u, v, w} A)
    (n : ℤ) (M : D.category.Obj) : D.category.Obj :=
  moduleObject A D (shiftedModule (moduleOf A D M) n)

private lemma moduleOf_shiftObjectOf
    (D : DGCategoryData.{u, v, w} A)
    (n : ℤ) (M : D.category.Obj) :
    moduleOf A D (shiftObjectOf A D n M) = shiftedModule (moduleOf A D M) n :=
  transport_cancel D.objects.symm _

private noncomputable def shiftHomOf
    (D : DGCategoryData.{u, v, w} A)
    (n : ℤ) (M : D.category.Obj) : D.category.Hom (shiftObjectOf A D n M) M n :=
  cast (congrArg (fun N => D.category.Hom (shiftObjectOf A D n M) N n)
    (moduleObject_moduleOf A D M)) (homogeneousTo A D (shiftHom (moduleOf A D M) n))

private noncomputable def shiftInvOf
    (D : DGCategoryData.{u, v, w} A)
    (n : ℤ) (M : D.category.Obj) : D.category.Hom M (shiftObjectOf A D n M) (-n) :=
  cast (congrArg (fun N => D.category.Hom N (shiftObjectOf A D n M) (-n))
    (moduleObject_moduleOf A D M)) (homogeneousTo A D (shiftInv (moduleOf A D M) n))

private lemma cochainOf_shiftHomOf
    (D : DGCategoryData.{u, v, w} A)
    (n : ℤ) (M : D.category.Obj) :
    HEq (cochainOf A D (shiftHomOf A D n M)) (shiftHom (moduleOf A D M) n).val := by
  rcases D with ⟨C, ho, hh, _hadd, hd, hc, hi⟩
  rcases C with ⟨O, H, ac, mo, d, da, ds, dd, c, ca, cb, cs, ct, dl, ass, id, il, ir, di⟩
  dsimp only at ho
  subst O
  have he : H = HomogeneousMap A := by
    funext M N n
    exact hh M N n
  subst H
  rfl

private lemma cochainOf_shiftInvOf
    (D : DGCategoryData.{u, v, w} A)
    (n : ℤ) (M : D.category.Obj) :
    HEq (cochainOf A D (shiftInvOf A D n M)) (shiftInv (moduleOf A D M) n).val := by
  rcases D with ⟨C, ho, hh, _hadd, hd, hc, hi⟩
  rcases C with ⟨O, H, ac, mo, d, da, ds, dd, c, ca, cb, cs, ct, dl, ass, id, il, ir, di⟩
  dsimp only at ho
  subst O
  have he : H = HomogeneousMap A := by
    funext M N n
    exact hh M N n
  subst H
  rfl

private noncomputable def shiftMapOf
    (D : DGCategoryData.{u, v, w} A)
    (n : ℤ) {M N : D.category.Obj} {k : ℤ} (f : D.category.Hom M N k) :
    D.category.Hom (shiftObjectOf A D n M) (shiftObjectOf A D n N) k :=
  (-1 : (CategoryTheory.Limits.limit X.O.obj : CommRingCat)) ^ (n * k).natAbs •
    D.category.comp (by omega) (shiftInvOf A D n N)
      (D.category.comp (rfl : k + n = k + n) f (shiftHomOf A D n M))

private lemma cochain_comp_heq {C : Type*} [Category C] [Preadditive C]
    {F F' G G' H H' : CochainComplex C ℤ} (hF : F = F') (hG : G = G') (hH : H = H')
    {m n k : ℤ} {f : Cochain F G m} {f' : Cochain F' G' m}
    {g : Cochain G H n} {g' : Cochain G' H' n} (hf : HEq f f') (hg : HEq g g')
    (h : m + n = k) : HEq (f.comp g h) (f'.comp g' h) := by
  subst F' G' H'
  cases hf; cases hg
  rfl

private lemma cochain_smul_heq {C : Type*} [Category C] [Preadditive C]
    {F F' G G' : CochainComplex C ℤ} (hF : F = F') (hG : G = G')
    {k : ℤ} {f : Cochain F G k} {f' : Cochain F' G' k} (hf : HEq f f') (s : ℤ) :
    HEq (s • f) (s • f') := by
  subst F' G'
  cases hf
  rfl

private lemma cochain_delta_heq {C : Type*} [Category C] [Preadditive C]
    {F F' G G' : CochainComplex C ℤ} (hF : F = F') (hG : G = G')
    {k : ℤ} {f : Cochain F G k} {f' : Cochain F' G' k} (hf : HEq f f') :
    HEq (δ k (k + 1) f) (δ k (k + 1) f') := by
  subst F' G'
  cases hf
  rfl

private lemma shift_conjugation {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M N : DifferentialGradedModule.{u, v, w} A) (n k : ℤ)
    (f : Cochain M.complex N.complex k) :
    ((shiftHom M n).val.comp f (by omega : n + k = k + n)).comp
      (shiftInv N n).val (by omega) = f.shift n := by
  apply Cochain.ext
  intro p q hpq
  rw [Cochain.comp_v _ _ _ p (q + n) q (by omega) (by omega),
    Cochain.comp_v _ _ _ p (p + n) (q + n) rfl (by omega), Cochain.shift_v']
  simp [shiftHom, shiftInv]

private lemma cochainOf_shiftMapOf
    (D : DGCategoryData.{u, v, w} A)
    (B : ∀ M, Nonempty (DGCategory.BinaryBiproductData D.category M M))
    (n : ℤ) {M N : D.category.Obj} {k : ℤ} (f : D.category.Hom M N k) :
    HEq (cochainOf A D (shiftMapOf A D n f))
      ((Int.negOnePow (n * k) : ℤ) • (cochainOf A D f).shift n) := by
  unfold shiftMapOf
  rw [cochainOf_sign A D B, cochainOf_comp, cochainOf_comp]
  have hM := congrArg DifferentialGradedModule.complex (moduleOf_shiftObjectOf A D n M)
  have hN := congrArg DifferentialGradedModule.complex (moduleOf_shiftObjectOf A D n N)
  have hc := cochain_comp_heq hM rfl hN
    (cochain_comp_heq hM rfl rfl (cochainOf_shiftHomOf A D n M) (HEq.refl (cochainOf A D f))
      (by omega : n + k = k + n))
    (cochainOf_shiftInvOf A D n N) (by omega : (k + n) + -n = k)
  exact (cochain_smul_heq hM hN hc (Int.negOnePow (n * k))).trans
    (heq_of_eq (congrArg (fun z => (Int.negOnePow (n * k) : ℤ) • z)
      (shift_conjugation (moduleOf A D M) (moduleOf A D N) n k (cochainOf A D f))))

private lemma signed_shift_delta {C : Type*} [Category C] [Preadditive C]
    {F G : CochainComplex C ℤ} {k : ℤ} (f : Cochain F G k) (n : ℤ) :
    δ k (k + 1) ((Int.negOnePow (n * k) : ℤ) • f.shift n) =
      (Int.negOnePow (n * (k + 1)) : ℤ) • (δ k (k + 1) f).shift n := by
  simp only [δ_smul, Cochain.δ_shift, Units.smul_def, smul_smul,
    mul_add, _root_.mul_one, Int.negOnePow_add, Units.val_mul]

private lemma shiftMapOf_d
    (D : DGCategoryData.{u, v, w} A)
    (B : ∀ M, Nonempty (DGCategory.BinaryBiproductData D.category M M))
    (n : ℤ) {M N : D.category.Obj} {k : ℤ} (f : D.category.Hom M N k) :
    shiftMapOf A D n (D.category.d f) = D.category.d (shiftMapOf A D n f) := by
  apply cochainOf_injective A D
  apply eq_of_heq
  have hl := cochainOf_shiftMapOf A D B n (D.category.d f)
  rw [cochainOf_d] at hl
  rw [cochainOf_d]
  have hr := cochain_delta_heq
    (congrArg DifferentialGradedModule.complex (moduleOf_shiftObjectOf A D n M))
    (congrArg DifferentialGradedModule.complex (moduleOf_shiftObjectOf A D n N))
    (cochainOf_shiftMapOf A D B n f)
  rw [signed_shift_delta] at hr
  exact hl.trans hr.symm

private lemma cochain_shift_comp {C : Type*} [Category C] [Preadditive C]
    {F G H : CochainComplex C ℤ} {k l m : ℤ}
    (f : Cochain F G k) (g : Cochain G H l) (h : k + l = m) (n : ℤ) :
    (f.comp g h).shift n = (f.shift n).comp (g.shift n) h := by
  apply Cochain.ext
  intro p q hpq
  rw [Cochain.shift_v', Cochain.comp_v _ _ _ (p + n) (p + k + n) (q + n)
    (by omega) (by omega), Cochain.comp_v _ _ _ p (p + k) q rfl (by omega),
    Cochain.shift_v', Cochain.shift_v']

private lemma signed_shift_comp {C : Type*} [Category C] [Preadditive C]
    {F G H : CochainComplex C ℤ} {k l m : ℤ}
    (f : Cochain F G k) (g : Cochain G H l) (h : k + l = m) (n : ℤ) :
    (Int.negOnePow (n * m) : ℤ) • (f.comp g h).shift n =
      ((Int.negOnePow (n * k) : ℤ) • f.shift n).comp
        ((Int.negOnePow (n * l) : ℤ) • g.shift n) h := by
  rw [Cochain.smul_comp, Cochain.comp_smul, smul_smul, cochain_shift_comp]
  subst m
  simp only [mul_add, Int.negOnePow_add, Units.val_mul]

private lemma shiftMapOf_comp
    (D : DGCategoryData.{u, v, w} A)
    (B : ∀ M, Nonempty (DGCategory.BinaryBiproductData D.category M M))
    (n : ℤ) {M N P : D.category.Obj} {k l m : ℤ} (h : k + l = m)
    (g : D.category.Hom N P k) (f : D.category.Hom M N l) :
    shiftMapOf A D n (D.category.comp h g f) =
      D.category.comp h (shiftMapOf A D n g) (shiftMapOf A D n f) := by
  apply cochainOf_injective A D
  apply eq_of_heq
  have hl := cochainOf_shiftMapOf A D B n (D.category.comp h g f)
  rw [cochainOf_comp, signed_shift_comp] at hl
  rw [cochainOf_comp]
  have hr := cochain_comp_heq
    (congrArg DifferentialGradedModule.complex (moduleOf_shiftObjectOf A D n M))
    (congrArg DifferentialGradedModule.complex (moduleOf_shiftObjectOf A D n N))
    (congrArg DifferentialGradedModule.complex (moduleOf_shiftObjectOf A D n P))
    (cochainOf_shiftMapOf A D B n f) (cochainOf_shiftMapOf A D B n g) (by omega : l + k = m)
  exact hl.trans hr.symm

private lemma cochain_id_heq {C : Type*} [Category C] [Preadditive C]
    {F G : CochainComplex C ℤ} (h : F = G) :
    HEq (Cochain.ofHom (𝟙 F)) (Cochain.ofHom (𝟙 G)) := by
  subst G
  rfl

private lemma shiftInvOf_comp_shiftHomOf
    (D : DGCategoryData.{u, v, w} A)
    (n : ℤ) (M : D.category.Obj) :
    D.category.comp (neg_add_cancel n) (shiftInvOf A D n M) (shiftHomOf A D n M) =
      D.category.id (shiftObjectOf A D n M) := by
  apply cochainOf_injective A D
  rw [cochainOf_comp, cochainOf_id]
  apply eq_of_heq
  have hM := congrArg DifferentialGradedModule.complex (moduleOf_shiftObjectOf A D n M)
  have h := cochain_comp_heq hM rfl hM
    (cochainOf_shiftHomOf A D n M) (cochainOf_shiftInvOf A D n M) (add_neg_cancel n)
  rw [shiftHom_comp_shiftInv] at h
  exact h.trans (cochain_id_heq hM).symm

private lemma shiftHomOf_comp_shiftInvOf
    (D : DGCategoryData.{u, v, w} A)
    (n : ℤ) (M : D.category.Obj) :
    D.category.comp (add_neg_cancel n) (shiftHomOf A D n M) (shiftInvOf A D n M) =
      D.category.id M := by
  apply cochainOf_injective A D
  rw [cochainOf_comp, cochainOf_id]
  apply eq_of_heq
  have hM := congrArg DifferentialGradedModule.complex (moduleOf_shiftObjectOf A D n M)
  have h := cochain_comp_heq rfl hM rfl
    (cochainOf_shiftInvOf A D n M) (cochainOf_shiftHomOf A D n M) (neg_add_cancel n)
  rw [shiftInv_comp_shiftHom] at h
  exact h

private lemma cochain_shift_id {C : Type*} [Category C] [Preadditive C]
    (F : CochainComplex C ℤ) (n : ℤ) :
    (Cochain.ofHom (𝟙 F)).shift n = Cochain.ofHom (𝟙 (F⟦n⟧)) := by
  apply Cochain.ext₀
  intro p
  rw [Cochain.shift_v']
  simp

private noncomputable def shiftDGFunctor
    (D : DGCategoryData.{u, v, w} A)
    (B : ∀ M, Nonempty (DGCategory.BinaryBiproductData D.category M M))
    (n : ℤ) : DGCategory.DGFunctor D.category D.category where
  obj := shiftObjectOf A D n
  map := shiftMapOf A D n
  map_add f g := by
    simp only [shiftMapOf, D.category.comp_add_left, D.category.comp_add_right, smul_add]
  map_smul r f := by
    simp only [shiftMapOf, D.category.comp_smul_left, D.category.comp_smul_right]
    exact smul_comm _ _ _
  map_d := shiftMapOf_d A D B n
  map_comp := shiftMapOf_comp A D B n
  map_id M := by
    apply cochainOf_injective A D
    apply eq_of_heq
    have h := cochainOf_shiftMapOf A D B n (D.category.id M)
    rw [cochainOf_id, mul_zero, Int.negOnePow_zero, Units.val_one, one_smul,
      cochain_shift_id] at h
    rw [cochainOf_id]
    exact h.trans (cochain_id_heq
      (congrArg DifferentialGradedModule.complex
        (moduleOf_shiftObjectOf A D n M))).symm

private lemma shiftObjectOf_zero
    (D : DGCategoryData.{u, v, w} A)
    (M : D.category.Obj) : shiftObjectOf A D 0 M = M := by
  apply (Equiv.cast D.objects).injective
  change moduleOf A D (shiftObjectOf A D 0 M) = moduleOf A D M
  rw [moduleOf_shiftObjectOf, shiftedModule_zero]

private lemma shiftObjectOf_add
    (D : DGCategoryData.{u, v, w} A)
    (n m : ℤ) (M : D.category.Obj) :
    shiftObjectOf A D (n + m) M = shiftObjectOf A D n (shiftObjectOf A D m M) := by
  apply (Equiv.cast D.objects).injective
  change moduleOf A D (shiftObjectOf A D (n + m) M) =
    moduleOf A D (shiftObjectOf A D n (shiftObjectOf A D m M))
  rw [moduleOf_shiftObjectOf, moduleOf_shiftObjectOf, moduleOf_shiftObjectOf, shiftedModule_add]

private noncomputable def shiftHomEquiv
    (D : DGCategoryData.{u, v, w} A)
    (n : ℤ) (M N : D.category.Obj) (k : ℤ) :
    D.category.Hom M N (k + n) ≃ₗ[(CategoryTheory.Limits.limit X.O.obj : CommRingCat)]
      D.category.Hom M (shiftObjectOf A D n N) k where
  toFun f := D.category.comp (by omega) (shiftInvOf A D n N) f
  invFun f := D.category.comp (by omega) (shiftHomOf A D n N) f
  left_inv f := by
    dsimp only
    rw [D.category.assoc (show -n + (k + n) = k by omega)
      (show n + k = k + n by omega) (add_neg_cancel n) (zero_add (k + n)),
      shiftHomOf_comp_shiftInvOf, D.category.id_comp]
  right_inv f := by
    dsimp only
    rw [D.category.assoc (show n + k = k + n by omega)
      (show -n + (k + n) = k by omega) (neg_add_cancel n) (zero_add k),
      shiftInvOf_comp_shiftHomOf, D.category.id_comp]
  map_add' := D.category.comp_add_right _ _
  map_smul' r f := D.category.comp_smul_right _ r _ f

private lemma cochain_rightShift_eq_comp {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M N : DifferentialGradedModule.{u, v, w} A) (n k : ℤ)
    (f : Cochain M.complex N.complex (k + n)) :
    f.comp (shiftInv N n).val (by omega : (k + n) + -n = k) = f.rightShift n k rfl := by
  apply Cochain.ext
  intro p q hpq
  rw [Cochain.comp_v _ _ _ p (q + n) q (by omega) (by omega),
    Cochain.rightShift_v _ n k rfl p q hpq (q + n) (by omega)]
  simp [shiftInv, CochainComplex.shiftFunctorObjXIso]

private lemma cochainOf_shiftHomEquiv
    (D : DGCategoryData.{u, v, w} A)
    (n : ℤ) (M N : D.category.Obj) (k : ℤ) (f : D.category.Hom M N (k + n)) :
    HEq (cochainOf A D (shiftHomEquiv A D n M N k f))
      ((cochainOf A D f).rightShift n k rfl) := by
  change HEq (cochainOf A D (D.category.comp _ (shiftInvOf A D n N) f)) _
  rw [cochainOf_comp]
  have hN := congrArg DifferentialGradedModule.complex (moduleOf_shiftObjectOf A D n N)
  have h := cochain_comp_heq rfl rfl hN (HEq.refl (cochainOf A D f))
    (cochainOf_shiftInvOf A D n N) (by omega : (k + n) + -n = k)
  exact h.trans (heq_of_eq (cochain_rightShift_eq_comp (moduleOf A D M) (moduleOf A D N) n k _))

private lemma cochainOf_d'
    (D : DGCategoryData.{u, v, w} A)
    {M N : D.category.Obj} {k l : ℤ} (h : k + 1 = l) (f : D.category.Hom M N k) :
    cochainOf A D (D.category.d' h f) = δ k l (cochainOf A D f) := by
  subst l
  exact cochainOf_d A D f

private lemma shiftHomEquiv_d
    (D : DGCategoryData.{u, v, w} A)
    (B : ∀ M, Nonempty (DGCategory.BinaryBiproductData D.category M M))
    (n : ℤ) (M N : D.category.Obj) (k : ℤ) (f : D.category.Hom M N (k + n)) :
    shiftHomEquiv A D n M N (k + 1) (D.category.d' (by omega) f) =
      (-1 : (CategoryTheory.Limits.limit X.O.obj : CommRingCat)) ^ n.natAbs •
        D.category.d (shiftHomEquiv A D n M N k f) := by
  apply cochainOf_injective A D
  apply eq_of_heq
  have hl := cochainOf_shiftHomEquiv A D n M N (k + 1) (D.category.d' (by omega) f)
  rw [cochainOf_d'] at hl
  rw [cochainOf_sign A D B, cochainOf_d]
  have hN := congrArg DifferentialGradedModule.complex (moduleOf_shiftObjectOf A D n N)
  have hr := cochain_smul_heq rfl hN
    (cochain_delta_heq rfl hN (cochainOf_shiftHomEquiv A D n M N k f)) (n.negOnePow : ℤ)
  rw [Cochain.δ_rightShift _ n k (k + 1) rfl ((k + 1) + n) rfl] at hr
  simp only [Units.smul_def, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_smul] at hr
  exact hl.trans hr.symm

private lemma shiftHomEquiv_comp_right
    (D : DGCategoryData.{u, v, w} A)
    (n : ℤ) {M N P : D.category.Obj} {l m : ℤ}
    (g : D.category.Hom N P (m + n)) (f : D.category.Hom M N l) :
    shiftHomEquiv A D n M P (m + l) (D.category.comp (by omega) g f) =
      D.category.comp rfl (shiftHomEquiv A D n N P m g) f :=
  D.category.assoc (by omega) (by omega) (by omega) rfl _ g f

private lemma cochain_v_heq {C : Type*} [Category C] [Preadditive C]
    {F G : CochainComplex C ℤ} {k : ℤ} (f : Cochain F G k)
    {p p' q q' : ℤ} (hp : p = p') (hq : q = q') (h : p + k = q) (h' : p' + k = q') :
    HEq (f.v p q h) (f.v p' q' h') := by
  subst p' q'
  rfl

private lemma cochain_ext_heq {C : Type*} [Category C] [Preadditive C]
    {F F' G G' : CochainComplex C ℤ} (hF : F = F') (hG : G = G')
    {k : ℤ} {f : Cochain F G k} {g : Cochain F' G' k}
    (h : ∀ p q hpq, HEq (f.v p q hpq) (g.v p q hpq)) : HEq f g := by
  subst F' G'
  exact heq_of_eq (Cochain.ext _ _ (fun p q hpq => eq_of_heq (h p q hpq)))

private lemma cochain_shift_heq {C : Type*} [Category C] [Preadditive C]
    {F F' G G' : CochainComplex C ℤ} (hF : F = F') (hG : G = G')
    {k : ℤ} {f : Cochain F G k} {g : Cochain F' G' k} (h : HEq f g) (n : ℤ) :
    HEq (f.shift n) (g.shift n) := by
  subst F' G'
  cases h
  rfl

private lemma cochainOf_heq_injective
    (D : DGCategoryData.{u, v, w} A)
    {M M' N N' : D.category.Obj} (hM : M = M') (hN : N = N')
    {k : ℤ} {f : D.category.Hom M N k} {g : D.category.Hom M' N' k}
    (h : HEq (cochainOf A D f) (cochainOf A D g)) : HEq f g := by
  subst M' N'
  exact heq_of_eq (cochainOf_injective A D (eq_of_heq h))

private lemma signed_shift_zero {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M N : DifferentialGradedModule.{u, v, w} A) {k : ℤ}
    (f : Cochain M.complex N.complex k) :
    HEq ((Int.negOnePow (0 * k) : ℤ) • f.shift 0) f := by
  apply cochain_ext_heq
    (congrArg DifferentialGradedModule.complex (shiftedModule_zero M))
    (congrArg DifferentialGradedModule.complex (shiftedModule_zero N))
  intro p q hpq
  simp only [zero_mul, Int.negOnePow_zero, Units.val_one, one_smul, Cochain.shift_v']
  exact cochain_v_heq f (add_zero p) (add_zero q) _ _

private lemma signed_shift_add {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M N : DifferentialGradedModule.{u, v, w} A) {k : ℤ}
    (f : Cochain M.complex N.complex k) (n m : ℤ) :
    HEq ((Int.negOnePow ((n + m) * k) : ℤ) • f.shift (n + m))
      ((Int.negOnePow (n * k) : ℤ) •
        ((Int.negOnePow (m * k) : ℤ) • f.shift m).shift n) := by
  apply cochain_ext_heq
    (congrArg DifferentialGradedModule.complex (shiftedModule_add M n m))
    (congrArg DifferentialGradedModule.complex (shiftedModule_add N n m))
  intro p q hpq
  simp only [Cochain.smul_v, Cochain.shift_v', add_mul, Int.negOnePow_add,
    Units.val_mul, smul_smul]
  exact cochain_v_heq (((Int.negOnePow (n * k) : ℤ) * (Int.negOnePow (m * k) : ℤ)) • f)
    (add_assoc p n m).symm (add_assoc q n m).symm _ _

private lemma shiftMapOf_zero
    (D : DGCategoryData.{u, v, w} A)
    (B : ∀ M, Nonempty (DGCategory.BinaryBiproductData D.category M M))
    {M N : D.category.Obj} {k : ℤ} (f : D.category.Hom M N k) :
    HEq (shiftMapOf A D 0 f) f := by
  apply cochainOf_heq_injective A D (shiftObjectOf_zero A D M) (shiftObjectOf_zero A D N)
  exact (cochainOf_shiftMapOf A D B 0 f).trans
    (signed_shift_zero (moduleOf A D M) (moduleOf A D N) (cochainOf A D f))

private lemma shiftMapOf_add
    (D : DGCategoryData.{u, v, w} A)
    (B : ∀ M, Nonempty (DGCategory.BinaryBiproductData D.category M M))
    (n m : ℤ) {M N : D.category.Obj} {k : ℤ} (f : D.category.Hom M N k) :
    HEq (shiftMapOf A D (n + m) f) (shiftMapOf A D n (shiftMapOf A D m f)) := by
  apply cochainOf_heq_injective A D (shiftObjectOf_add A D n m M) (shiftObjectOf_add A D n m N)
  have hM := congrArg DifferentialGradedModule.complex (moduleOf_shiftObjectOf A D m M)
  have hN := congrArg DifferentialGradedModule.complex (moduleOf_shiftObjectOf A D m N)
  have hr := (cochainOf_shiftMapOf A D B n (shiftMapOf A D m f)).trans
    (cochain_smul_heq (congrArg (fun F => F⟦n⟧) hM) (congrArg (fun F => F⟦n⟧) hN)
      (cochain_shift_heq hM hN (cochainOf_shiftMapOf A D B m f) n) (Int.negOnePow (n * k)))
  exact (cochainOf_shiftMapOf A D B (n + m) f).trans
    ((signed_shift_add (moduleOf A D M) (moduleOf A D N) (cochainOf A D f) n m).trans hr.symm)

private lemma cochain_rightShift_comp_left {C : Type*} [Category C] [Preadditive C]
    {F G H : CochainComplex C ℤ} {n l m : ℤ}
    (f : Cochain F G (l + n)) (g : Cochain G H m) :
    (f.comp g (by omega : (l + n) + m = (m + l) + n)).rightShift n (m + l) rfl =
      (f.rightShift n l rfl).comp (g.shift n) (by omega : l + m = m + l) := by
  apply Cochain.ext
  intro p q hpq
  rw [Cochain.rightShift_v _ n (m + l) rfl p q hpq (q + n) (by omega),
    Cochain.comp_v _ _ _ p (p + l + n) (q + n) (by omega) (by omega),
    Cochain.comp_v _ _ _ p (p + l) q rfl (by omega),
    Cochain.rightShift_v _ n l rfl p (p + l) rfl (p + l + n) (by omega),
    Cochain.shift_v']
  simp [CochainComplex.shiftFunctorObjXIso]

private lemma shiftHomEquiv_comp_left
    (D : DGCategoryData.{u, v, w} A)
    (B : ∀ M, Nonempty (DGCategory.BinaryBiproductData D.category M M))
    (n : ℤ) {M N P : D.category.Obj} {l m : ℤ}
    (g : D.category.Hom N P m) (f : D.category.Hom M N (l + n)) :
    shiftHomEquiv A D n M P (m + l) (D.category.comp (by omega) g f) =
      (-1 : (CategoryTheory.Limits.limit X.O.obj : CommRingCat)) ^ (n * m).natAbs •
        D.category.comp rfl (shiftMapOf A D n g) (shiftHomEquiv A D n M N l f) := by
  apply cochainOf_injective A D
  apply eq_of_heq
  have hl := cochainOf_shiftHomEquiv A D n M P (m + l) (D.category.comp (by omega) g f)
  rw [cochainOf_comp, cochain_rightShift_comp_left] at hl
  rw [cochainOf_sign A D B, cochainOf_comp]
  have hN := congrArg DifferentialGradedModule.complex (moduleOf_shiftObjectOf A D n N)
  have hP := congrArg DifferentialGradedModule.complex (moduleOf_shiftObjectOf A D n P)
  have hr := cochain_smul_heq rfl hP
    (cochain_comp_heq rfl hN hP (cochainOf_shiftHomEquiv A D n M N l f)
      (cochainOf_shiftMapOf A D B n g) (by omega : l + m = m + l)) (Int.negOnePow (n * m))
  simp only [Cochain.comp_smul, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_smul] at hr
  exact hl.trans hr.symm

/-- `shiftObjectOf` by `n + m` is the shift by `n` followed by the shift by `m`. -/
private lemma shiftObjectOf_add_comm
    (D : DGCategoryData.{u, v, w} A) (n m : ℤ) (M : D.category.Obj) :
    shiftObjectOf A D (n + m) M = shiftObjectOf A D m (shiftObjectOf A D n M) := by
  rw [add_comm n m]
  exact shiftObjectOf_add A D m n M

/-- `shiftMapOf` by `n + m` is the shift by `n` followed by the shift by `m`. -/
private lemma shiftMapOf_add_comm
    (D : DGCategoryData.{u, v, w} A)
    (B : ∀ M, Nonempty (DGCategory.BinaryBiproductData D.category M M))
    (n m : ℤ) {M N : D.category.Obj} {k : ℤ} (f : D.category.Hom M N k) :
    HEq (shiftMapOf A D (n + m) f) (shiftMapOf A D m (shiftMapOf A D n f)) := by
  rw [add_comm n m]
  exact shiftMapOf_add A D B m n f

private lemma shiftOnComp_zero
    (D : DGCategoryData.{u, v, w} A)
    (B : ∀ M, Nonempty (DGCategory.BinaryBiproductData D.category M M)) :
    (shiftDGFunctor A D B 0).onComp = 𝟭 D.category.Comp := by
  apply Functor.hext (shiftObjectOf_zero A D)
  intro M N f
  exact DGCategory.cocycle_heq_of_val_heq _ _ (shiftObjectOf_zero A D M) (shiftObjectOf_zero A D N)
    (shiftMapOf_zero A D B f.val)

private lemma shiftOnComp_add
    (D : DGCategoryData.{u, v, w} A)
    (B : ∀ M, Nonempty (DGCategory.BinaryBiproductData D.category M M)) (n m : ℤ) :
    (shiftDGFunctor A D B (n + m)).onComp =
      (shiftDGFunctor A D B n).onComp ⋙ (shiftDGFunctor A D B m).onComp := by
  apply Functor.hext (shiftObjectOf_add_comm A D n m)
  intro M N f
  exact DGCategory.cocycle_heq_of_val_heq _ _ (shiftObjectOf_add_comm A D n m M)
    (shiftObjectOf_add_comm A D n m N) (shiftMapOf_add_comm A D B n m f.val)

private lemma shiftOnK_zero
    (D : DGCategoryData.{u, v, w} A)
    (B : ∀ M, Nonempty (DGCategory.BinaryBiproductData D.category M M)) :
    (shiftDGFunctor A D B 0).onK = 𝟭 D.category.K := by
  apply Functor.hext (shiftObjectOf_zero A D)
  intro M N f
  refine Quotient.inductionOn f (fun f => ?_)
  exact D.category.homotopyClass_heq (shiftObjectOf_zero A D M) (shiftObjectOf_zero A D N)
    (shiftMapOf_zero A D B f.val)

private lemma shiftOnK_add
    (D : DGCategoryData.{u, v, w} A)
    (B : ∀ M, Nonempty (DGCategory.BinaryBiproductData D.category M M)) (n m : ℤ) :
    (shiftDGFunctor A D B (n + m)).onK =
      (shiftDGFunctor A D B n).onK ⋙ (shiftDGFunctor A D B m).onK := by
  apply Functor.hext (shiftObjectOf_add_comm A D n m)
  intro M N f
  refine Quotient.inductionOn f (fun f => ?_)
  exact D.category.homotopyClass_heq (shiftObjectOf_add_comm A D n m M)
    (shiftObjectOf_add_comm A D n m N) (shiftMapOf_add_comm A D B n m f.val)

@[instance_reducible] private noncomputable def strictHasShift {C : Type*} [Category C]
    (F : ℤ → C ⥤ C) (h0 : F 0 = 𝟭 C) (ha : ∀ n m, F (n + m) = F n ⋙ F m) :
    HasShift C ℤ :=
  hasShiftMk C ℤ {
    F := F
    zero := eqToIso h0
    add := fun n m => eqToIso (ha n m)
    assoc_hom_app := by
      intro n m k X
      simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans]
    zero_add_hom_app := by
      intro n X
      simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_map, eqToHom_trans]
    add_zero_hom_app := by
      intro n X
      simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_trans] }

private noncomputable def moduleShiftAxiomB
    (D : DGCategoryData.{u, v, w} A)
    (B : ∀ M, Nonempty (DGCategory.BinaryBiproductData D.category M M)) :
    DGCategory.ShiftAxiomB D.category where
  shiftFunctor := shiftDGFunctor A D B
  compShift := strictHasShift (fun n => (shiftDGFunctor A D B n).onComp)
    (shiftOnComp_zero A D B) (shiftOnComp_add A D B)
  kShift := strictHasShift (fun n => (shiftDGFunctor A D B n).onK)
    (shiftOnK_zero A D B) (shiftOnK_add A D B)
  compShift_functor _ := rfl
  kShift_functor _ := rfl
  zero_obj := shiftObjectOf_zero A D
  add_obj := shiftObjectOf_add A D
  zero_map := shiftMapOf_zero A D B
  add_map := shiftMapOf_add A D B
  toShift := shiftHomEquiv A D
  toShift_d := shiftHomEquiv_d A D B
  toShift_comp_right := shiftHomEquiv_comp_right A D
  toShift_comp_left := shiftHomEquiv_comp_left A D B

private lemma cochain_eval_heq {C : Type*} [Category C] [Preadditive C]
    {F F' G G' : CochainComplex C ℤ} (hF : F = F') (hG : G = G')
    {k : ℤ} {f : Cochain F G k} {g : Cochain F' G' k} (h : HEq f g)
    (p q : ℤ) (hpq : p + k = q) : HEq (f.v p q hpq) (g.v p q hpq) := by
  subst F' G'
  cases h
  rfl

private lemma cochain_rightShift_v {C : Type*} [Category C] [Preadditive C]
    {F G : CochainComplex C ℤ} {n k : ℤ} (f : Cochain F G (k + n))
    (p q : ℤ) (hpq : p + k = q) :
    (f.rightShift n k rfl).v p q hpq = f.v p (q + n) (by omega) := by
  rw [Cochain.rightShift_v _ n k rfl p q hpq (q + n) (by omega)]
  simp [CochainComplex.shiftFunctorObjXIso]

/-- The canonical shift data, constructed. Stated as a `def` producing the structure rather
than as `Nonempty (...)` plus `Classical.choice`: the construction below pins the canonical
choice `axiomB := moduleShiftAxiomB A D B`, and routing it through `Nonempty` would discard
exactly that and leave `shiftAxiomB` an arbitrary inhabitant. -/
private noncomputable def canonicalShiftAxiomB : CanonicalShiftAxiomB.{u, v, w} A := by
  let D := dgCategoryData.{u, v, w} A
  let B := fun M => hasBinaryBiproducts A M M
  have hM (n : ℤ) (M : DifferentialGradedModule.{u, v, w} A) :
      asModule A (shiftObjectOf A D n (asObject A M)) = shiftedModule M n :=
    (moduleOf_shiftObjectOf A D n (asObject A M)).trans
      (congrArg (fun M => shiftedModule M n) (transport_cancel D.objects.symm M))
  refine {
    axiomB := moduleShiftAxiomB A D B
    shifted_complex := ?_
    shifted_action := ?_
    shift_one := ?_
    shifted_map := ?_
    toShift_components := ?_ }
  · intro n M
    change (asModule A (shiftObjectOf A D n (asObject A M))).complex = _
    rw [hM]
    rfl
  · intro n M p q U
    change HEq (((asModule A (shiftObjectOf A D n (asObject A M))).mul p q).app U) _
    rw [hM]
    exact shiftedModule_action_map M n p q U
  · intro M
    exact (hM 1 M).trans (shiftedModule_one M)
  · intro n k M N f p q hpq
    have h := cochain_eval_heq
      (congrArg DifferentialGradedModule.complex
        (moduleOf_shiftObjectOf A D n (asObject A M)))
      (congrArg DifferentialGradedModule.complex
        (moduleOf_shiftObjectOf A D n (asObject A N)))
      (cochainOf_shiftMapOf A D B n f) p q hpq
    simp only [Cochain.smul_v, Cochain.shift_v'] at h
    convert h using 0
    simp [moduleShiftAxiomB, shiftDGFunctor, cochainOf,
      homogeneousOf, moduleOf, moduleObject, asCochain, asModule, asObject, D, shiftedModule]
    rfl
  · intro n k M N f p q hpq
    have h := cochain_eval_heq rfl
      (congrArg DifferentialGradedModule.complex
        (moduleOf_shiftObjectOf A D n (asObject A N)))
      (cochainOf_shiftHomEquiv A D n (asObject A M) (asObject A N) k f) p q hpq
    simp only [cochain_rightShift_v] at h
    convert h using 0
    simp [moduleShiftAxiomB, shiftDGFunctor, cochainOf,
      homogeneousOf, moduleOf, moduleObject, asCochain, asModule, asObject, D, shiftedModule]
    rfl

/-- The canonical DG shifts and Hom-complex shift isomorphisms for sheaf DG modules. -/
@[stacks 0FS4 "axiom_b", no_expose]
noncomputable def shiftAxiomB : CanonicalShiftAxiomB.{u, v, w} A :=
  canonicalShiftAxiomB A

/-- **The translation of `K(Mod(A, d))` carried by axiom (B) is strict**: its two coherence
isomorphisms `shiftFunctorZero` and `shiftFunctorAdd` are the `eqToIso`s of the equalities of
functors `(-)[0] = 𝟭` and `(-)[n + m] = (-)[n] ⋙ (-)[m]`, which hold on the nose because the
differential graded shifts of axiom (B) are strict on objects and heterogeneously strict on
homogeneous morphisms.

This is the hypothesis `DGCategory.ShiftAxiomB.IsStrictKShift` of Tag 0FQF, and having it means
a functor of differential graded categories commuting with the shift induces an exact functor on
the homotopy categories *for the translation this development already uses*, with no
strictification step. -/
theorem isStrictKShift_shiftAxiomB :
    (shiftAxiomB.{u, v, w} A).axiomB.IsStrictKShift :=
  ⟨⟨shiftOnK_zero A (dgCategoryData.{u, v, w} A) _, ShiftMkCore.shiftFunctorZero_eq _⟩,
    fun a b => ⟨shiftOnK_add A (dgCategoryData.{u, v, w} A) _ a b,
      ShiftMkCore.shiftFunctorAdd_eq _ a b⟩⟩

end SheafOfModules.DifferentialGradedModule
