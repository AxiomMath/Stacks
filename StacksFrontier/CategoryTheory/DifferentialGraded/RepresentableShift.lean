module

public import StacksFrontier.Algebra.DifferentialGraded.Module.Shift
public import StacksFrontier.CategoryTheory.DifferentialGraded.Representable
public import StacksFrontier.CategoryTheory.DifferentialGraded.Triangulated
public import StacksFrontier.Algebra.NegOnePowSmul

/-!
# The shift comparison for the representable differential graded module

Let `A` be a differential graded category with the shift functors of axiom (B) and let `x` be an
object. The identification `A.Hom x y (k + n) ≃ A.Hom x (y[n]) k` of axiom (B) assembles into an
isomorphism `Hom(x, y[n]) ≅ Hom(x, y)[n]` of differential graded modules over the endomorphism
algebra of `x`: it matches the right actions because the identification is composition on the
right, and it matches the differentials because axiom (B) multiplies the differential of the
shift by `(-1)^n`, which is exactly the sign in the differential of a shifted module.

## Main definitions

* `DGCategory.ShiftComparisonData`: a shift on objects and identifications of Hom modules,
  with their sign law and their compatibility with composition on the right.
* `DGCategory.ShiftAxiomB.toShiftComparisonData`: axiom (B) supplies that data.
* `DGCategory.repShiftLinearEquiv`: the underlying linear comparison.
* `DGCategory.representableShiftIso`: the isomorphism `Hom(x, y[n]) ≅ Hom(x, y)[n]` of
  differential graded modules.

## Main results

* `DGCategory.repShiftLinearEquiv_of` and `DGCategory.repShiftLinearEquiv_symm_of`: the
  comparison sends a degree-`k` morphism into `y[n]` to the corresponding degree-`k + n`
  morphism into `y`.
* `DGCategory.repShiftLinearEquiv_repActionLinear`: the comparison is linear over the
  endomorphism algebra.
* `DGCategory.repShiftLinearEquiv_repDifferential`: the comparison carries the differential to
  `(-1)^n` times the differential.
-/

@[expose] public section

open CategoryTheory

namespace DGCategory

universe w v u

variable {R : Type u} [CommRing R]

/-- The reindexing of `ℤ` whose inverse is translation by `n`. -/
@[reducible] public def shiftIndexEquiv (n : ℤ) : ℤ ≃ ℤ where
  toFun k := k - n
  invFun k := k + n
  left_inv := fun k => by simp
  right_inv := fun k => by simp

/-- The inverse of `shiftIndexEquiv n` is translation by `n`. -/
@[simp] public theorem shiftIndexEquiv_symm_apply (n k : ℤ) :
    (shiftIndexEquiv n).symm k = k + n := rfl

/-- A shift on objects of a differential graded category together with `R`-linear
identifications `A.Hom x y (k + n) ≃ A.Hom x (y[n]) k` which multiply the differential by
`(-1)^n` and do not change composition on the right. -/
public structure ShiftComparisonData (A : DGCategory.{w, v, u} R) where
  /-- The shift on objects, `y ↦ y[n]`. -/
  obj : ℤ → A.Obj → A.Obj
  /-- A degree `k + n` morphism `x ⟶ y` is a degree `k` morphism `x ⟶ y[n]`. -/
  toShift : ∀ (n : ℤ) (x y : A.Obj) (k : ℤ), A.Hom x y (k + n) ≃ₗ[R] A.Hom x (obj n y) k
  /-- The identification multiplies the differential by `(-1)^n`. -/
  toShift_d : ∀ (n : ℤ) (x y : A.Obj) (k : ℤ) (f : A.Hom x y (k + n)),
    toShift n x y (k + 1) (A.d' (by omega : (k + n) + 1 = (k + 1) + n) f) =
      (-1 : R) ^ n.natAbs • A.d (toShift n x y k f)
  /-- The identification does not change composition on the right. -/
  toShift_comp_right : ∀ (n : ℤ) {x y z : A.Obj} {l m : ℤ}
    (g : A.Hom y z (m + n)) (f : A.Hom x y l),
    toShift n x z (m + l) (A.comp (by omega : (m + n) + l = (m + l) + n) g f) =
      A.comp (by omega : m + l = m + l) (toShift n y z m g) f

/-- Axiom (B) supplies the data the shift comparison needs. -/
public def ShiftAxiomB.toShiftComparisonData {A : DGCategory.{w, v, u} R}
    (S : ShiftAxiomB A) : ShiftComparisonData A where
  obj n y := (S.shiftFunctor n).obj y
  toShift := S.toShift
  toShift_d := S.toShift_d
  toShift_comp_right := S.toShift_comp_right

variable (A : DGCategory.{w, v, u} R) (x : A.Obj)

/-- The underlying linear comparison `Hom(x, y[n]) ≃ Hom(x, y)[n]`: in degree `k` it is the
identification of axiom (B) of a degree-`k` morphism into `y[n]` with a degree-`k + n` morphism
into `y`. -/
public noncomputable def repShiftLinearEquiv (S : ShiftComparisonData A) (n : ℤ) (y : A.Obj) :
    repTotal A x (S.obj n y) ≃ₗ[R] repTotal A x y :=
  (DirectSum.congrLinearEquiv (R := R)
      (N := repFamily A x (S.obj n y))
      (P := fun k : ℤ => repFamily A x y ((shiftIndexEquiv n).symm k))
      fun k : ℤ => (S.toShift n x y k).symm).trans
    (DirectSum.lequivCongrLeft R (shiftIndexEquiv n)).symm

/-- The inverse of the reindexing by `shiftIndexEquiv n` sends the summand of index `k` to the
summand of index `k + n`. -/
private lemma lequivCongrLeft_symm_of (n k : ℤ) (V : ℤ → Type*)
    [∀ i, AddCommMonoid (V i)] [∀ i, Module R (V i)] (a : V (k + n)) :
    (DirectSum.lequivCongrLeft R (shiftIndexEquiv n)).symm
        (DirectSum.of (fun j : ℤ => V ((shiftIndexEquiv n).symm j)) k a) =
      DirectSum.of V (k + n) a := by
  classical
  rw [← DirectSum.lof_eq_of R ℤ (fun j : ℤ => V ((shiftIndexEquiv n).symm j)) k a]
  exact Eq.trans (DirectSum.lequivCongrLeft_symm_lof R)
    (DirectSum.lof_eq_of R ℤ V (k + n) a)

/-- The comparison sends a degree-`k` morphism into `y[n]` to the corresponding degree-`k + n`
morphism into `y`. -/
public theorem repShiftLinearEquiv_of (S : ShiftComparisonData A) (n : ℤ) (y : A.Obj) (k : ℤ)
    (f : A.Hom x (S.obj n y) k) :
    repShiftLinearEquiv A x S n y
        (DirectSum.of (repFamily A x (S.obj n y)) k f) =
      DirectSum.of (repFamily A x y) (k + n) ((S.toShift n x y k).symm f) := by
  classical
  have h₁ : repShiftLinearEquiv A x S n y
      (DirectSum.of (repFamily A x (S.obj n y)) k f) =
      (DirectSum.lequivCongrLeft R (shiftIndexEquiv n)).symm
        (DirectSum.of (fun j : ℤ => repFamily A x y ((shiftIndexEquiv n).symm j)) k
          ((S.toShift n x y k).symm f)) := by
    simp only [repShiftLinearEquiv, LinearEquiv.trans_apply,
      DirectSum.coe_congrLinearEquiv, DirectSum.lmap_of]
    rfl
  exact h₁.trans (lequivCongrLeft_symm_of n k (repFamily A x y) ((S.toShift n x y k).symm f))

/-- The inverse comparison sends a degree-`k + n` morphism into `y` to the corresponding
degree-`k` morphism into `y[n]`. -/
public theorem repShiftLinearEquiv_symm_of (S : ShiftComparisonData A) (n : ℤ) (y : A.Obj) (k : ℤ)
    (g : A.Hom x y (k + n)) :
    (repShiftLinearEquiv A x S n y).symm (DirectSum.of (repFamily A x y) (k + n) g) =
      DirectSum.of (repFamily A x (S.obj n y)) k (S.toShift n x y k g) := by
  rw [LinearEquiv.symm_apply_eq, repShiftLinearEquiv_of, LinearEquiv.symm_apply_apply]

/-- The comparison is linear over the endomorphism algebra of `x`: the identification
of axiom (B) does not change composition on the right. -/
public theorem repShiftLinearEquiv_repActionLinear (S : ShiftComparisonData A) (n : ℤ) (y : A.Obj)
    (a : endTotal A x) (z : repTotal A x (S.obj n y)) :
    repShiftLinearEquiv A x S n y (repActionLinear A x (S.obj n y) a z) =
      repActionLinear A x y a (repShiftLinearEquiv A x S n y z) := by
  classical
  induction z using DirectSum.induction_on with
  | zero => simp
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | of k f =>
    induction a using DirectSum.induction_on with
    | zero => simp
    | add a₁ a₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
    | of i b =>
      rw [repActionLinear_of, repShiftLinearEquiv_of, repShiftLinearEquiv_of,
        repActionLinear_of]
      refine DirectSum.of_eq_of_heq (by lia) ?_
      have hcr := S.toShift_comp_right n (x := x) (y := x) (z := y) (l := i) (m := k)
        ((S.toShift n x y k).symm f) b
      rw [LinearEquiv.apply_symm_apply] at hcr
      have hgoal : A.comp (by lia : (k + n) + i = (k + i) + n)
          ((S.toShift n x y k).symm f) b =
          (S.toShift n x y (k + i)).symm (A.comp (by lia : k + i = k + i) f b) :=
        ((S.toShift n x y (k + i)).symm_apply_eq.mpr hcr.symm).symm
      refine (heq_of_eq hgoal.symm).trans ?_
      exact comp_heq (by lia : (k + i) + n = (k + n) + i)
        ((S.toShift n x y k).symm f) b


/-- Acting twice by `(-1) ^ m` is the identity. -/
private lemma neg_one_pow_smul_involutive {W : Type*} [AddCommGroup W] [Module R W] (m : ℕ)
    (w : W) : ((-1 : R) ^ m) • (((-1 : R) ^ m) • w) = w := by
  rw [smul_smul, ← pow_add,
    show ((-1 : R)) ^ (m + m) = 1 from Even.neg_one_pow ⟨m, rfl⟩, one_smul]

/-- The comparison carries the differential of `Hom(x, y[n])` to `(-1)^n` times that of
`Hom(x, y)`, which is the differential of the shifted module. -/
public theorem repShiftLinearEquiv_repDifferential (S : ShiftComparisonData A) (n : ℤ) (y : A.Obj)
    (z : repTotal A x (S.obj n y)) :
    repShiftLinearEquiv A x S n y (repDifferential A x (S.obj n y) z) =
      ((-1 : R) ^ n.natAbs) •
        repDifferential A x y (repShiftLinearEquiv A x S n y z) := by
  classical
  induction z using DirectSum.induction_on with
  | zero => simp
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂, smul_add]
  | of k f =>
    rw [repDifferential_of, repShiftLinearEquiv_of, repShiftLinearEquiv_of,
      repDifferential_of]
    have hd := S.toShift_d n x y k ((S.toShift n x y k).symm f)
    rw [LinearEquiv.apply_symm_apply] at hd
    have hkey : (S.toShift n x y (k + 1)).symm (A.d f) =
        ((-1 : R) ^ n.natAbs) •
          A.d' (by lia : (k + n) + 1 = (k + 1) + n) ((S.toShift n x y k).symm f) := by
      rw [LinearEquiv.symm_apply_eq, map_smul, hd, neg_one_pow_smul_involutive]
    rw [hkey, ← DirectSum.lof_eq_of R ℤ (repFamily A x y) ((k + 1) + n),
      ← DirectSum.lof_eq_of R ℤ (repFamily A x y) ((k + n) + 1), map_smul]
    refine congrArg (fun w => ((-1 : R) ^ n.natAbs) • w) ?_
    rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]
    exact DirectSum.of_eq_of_heq (by lia)
      (eqRec_heq (by lia : (k + n) + 1 = (k + 1) + n)
        (A.d ((S.toShift n x y k).symm f)))

/-- The comparison `Hom(x, y[n]) ⟶ Hom(x, y)[n]`, as a homomorphism of differential graded
modules over the endomorphism algebra of `x`. -/
public noncomputable def repShiftHom (S : ShiftComparisonData A) (n : ℤ) (y : A.Obj) :
    representableModule A x (S.obj n y) ⟶
      (representableModule A x y).shift n where
  toFun := (repShiftLinearEquiv A x S n y).toLinearMap
  map_smul z a := repShiftLinearEquiv_repActionLinear A x S n y a z
  map_grading k z hz := by
    obtain ⟨f, rfl⟩ := (DirectSum.mem_rangeGrading R
      (repFamily A x (S.obj n y)) k _).mp hz
    change repShiftLinearEquiv A x S n y _ ∈ DirectSum.rangeGrading R (repFamily A x y) (k + n)
    rw [repShiftLinearEquiv_of]
    exact ⟨_, DirectSum.lof_eq_of R ℤ (repFamily A x y) (k + n) _⟩
  map_d := by
    refine LinearMap.ext fun z => ?_
    change repShiftLinearEquiv A x S n y
        (repDifferential A x (S.obj n y) z) =
      (n.negOnePow • repDifferential A x y) (repShiftLinearEquiv A x S n y z)
    rw [LinearMap.smul_apply, Units.smul_def, negOnePow_smul_eq (R := R)]
    exact repShiftLinearEquiv_repDifferential A x S n y z

/-- The inverse comparison `Hom(x, y)[n] ⟶ Hom(x, y[n])`. -/
public noncomputable def repShiftInvHom (S : ShiftComparisonData A) (n : ℤ) (y : A.Obj) :
    (representableModule A x y).shift n ⟶
      representableModule A x (S.obj n y) where
  toFun := (repShiftLinearEquiv A x S n y).symm.toLinearMap
  map_smul z a := by
    have h := repShiftLinearEquiv_repActionLinear A x S n y a
      ((repShiftLinearEquiv A x S n y).symm z)
    rw [LinearEquiv.apply_symm_apply] at h
    exact (LinearEquiv.symm_apply_eq _).mpr h.symm
  map_grading k z hz := by
    obtain ⟨g, rfl⟩ := (DirectSum.mem_rangeGrading R (repFamily A x y) (k + n) _).mp hz
    change (repShiftLinearEquiv A x S n y).symm _ ∈
      DirectSum.rangeGrading R (repFamily A x (S.obj n y)) k
    rw [repShiftLinearEquiv_symm_of]
    exact ⟨_, DirectSum.lof_eq_of R ℤ (repFamily A x (S.obj n y)) k _⟩
  map_d := by
    refine LinearMap.ext fun z => ?_
    change (repShiftLinearEquiv A x S n y).symm
        ((n.negOnePow • repDifferential A x y) z) =
      repDifferential A x (S.obj n y)
        ((repShiftLinearEquiv A x S n y).symm z)
    have h := repShiftLinearEquiv_repDifferential A x S n y
      ((repShiftLinearEquiv A x S n y).symm z)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [LinearMap.smul_apply, Units.smul_def, negOnePow_smul_eq (R := R), ← h,
      LinearEquiv.symm_apply_apply]

/-- **The shift comparison for the representable differential graded module.** The
identification of axiom (B) is an isomorphism `Hom(x, y[n]) ≅ Hom(x, y)[n]` of differential
graded modules over the endomorphism algebra of `x`. -/
public noncomputable def representableShiftIso (S : ShiftComparisonData A) (n : ℤ) (y : A.Obj) :
    representableModule A x (S.obj n y) ≅
      (representableModule A x y).shift n where
  hom := repShiftHom A x S n y
  inv := repShiftInvHom A x S n y
  hom_inv_id := by
    refine DifferentialGradedModule.Hom.ext (LinearMap.ext fun z => ?_)
    exact (repShiftLinearEquiv A x S n y).symm_apply_apply z
  inv_hom_id := by
    refine DifferentialGradedModule.Hom.ext (LinearMap.ext fun z => ?_)
    exact (repShiftLinearEquiv A x S n y).apply_symm_apply z

end DGCategory
