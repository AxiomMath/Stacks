module

public import StacksFrontier.Algebra.DGA.Abelian
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.KFlat.Basic
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Iso
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.FreeResolution.FreeDGA
public import StacksFrontier.Algebra.DGA.FreeResolution.CellStage
import all StacksFrontier.Algebra.DGA.FreeResolution.FreeDGA
import all StacksFrontier.Algebra.DGA.FreeResolution.CellStage

/-!
# The limit of the cell stages and its quasi-isomorphism

The directed colimit of the cell stages of the free graded resolution decomposes as the direct
sum of its graded pieces, so it is a differential graded algebra; it maps quasi-isomorphically
to the given one.

## Main definitions

* `Stacks.DGA.ModelsComplex` identifies the complex underlying a differential graded algebra.

## Implementation notes

The quasi-isomorphism is witnessed on cochain complexes identified degreewise with the
graded pieces, retaining compatibility with the differential and the algebra map.
The file ends with the generators of the limit and the maps from the free algebras on the
generators of each stage, used to show that the limit is free as a graded algebra.

## References

* [Stacks Project, Tag 0BZ7](https://stacks.math.columbia.edu/tag/0BZ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits


universe u v

namespace Stacks.DGA

variable {R : Type u} [CommRing R]

private noncomputable def CellStage.limitDecompose
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    letI := CellStage.directedSystem B
    DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
      (fun i j h => CellStage.transition B i j h) →ₗ[R]
      DirectSum ℤ (fun n : ℤ => ↥(CellStage.limitGrading B n)) := by
  letI := CellStage.directedSystem B
  exact DirectLimit.Module.lift R ℕ
    (fun i : ℕ => (CellStage.at B i).dga.A)
    (fun i j h => CellStage.transition B i j h)
    (fun i => CellStage.limitDecomposeStage B i)
    (fun i j h x => CellStage.limitDecomposeStage_transition B i j h x)

private theorem CellStage.limitDecompose_of_mem
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (n : ℤ) (x : letI := CellStage.directedSystem B
      DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun i j h => CellStage.transition B i j h))
    (hx : x ∈ CellStage.limitGrading B n) :
    CellStage.limitDecompose B x =
      DirectSum.lof R ℤ (fun n : ℤ => ↥(CellStage.limitGrading B n)) n ⟨x, hx⟩ := by
  let := CellStage.directedSystem B
  obtain ⟨i, a, ha, rfl⟩ := CellStage.limitGrading_exists_of B n x hx
  change CellStage.limitDecomposeStage B i a = _
  exact CellStage.limitDecomposeStage_of_mem B i n a ha

private theorem CellStage.limitDecompose_left_inv
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    letI := CellStage.directedSystem B
    Function.LeftInverse
      (DirectSum.coeAddMonoidHom (CellStage.limitGrading B))
      (CellStage.limitDecompose B) := by
  let := CellStage.directedSystem B
  intro z
  induction z using DirectLimit.induction with
  | _ i x =>
      change (DirectSum.coeAddMonoidHom (CellStage.limitGrading B))
        (CellStage.limitDecompose B
          (DirectLimit.Module.of R ℕ
            (fun j : ℕ => (CellStage.at B j).dga.A)
            (fun j k h => CellStage.transition B j k h) i x)) = _
      induction x using DirectSum.Decomposition.inductionOn
          (CellStage.at B i).dga.grading with
      | zero =>
          change (DirectSum.coeAddMonoidHom (CellStage.limitGrading B))
            (CellStage.limitDecompose B
              ((DirectLimit.Module.of R ℕ
                (fun j : ℕ => (CellStage.at B j).dga.A)
                (fun j k h => CellStage.transition B j k h) i) 0)) =
              (DirectLimit.Module.of R ℕ
                (fun j : ℕ => (CellStage.at B j).dga.A)
                (fun j k h => CellStage.transition B j k h) i) 0
          simp only [map_zero]
      | @homogeneous n x =>
          rw [CellStage.limitDecompose_of_mem B n _
            (CellStage.limitGrading_of_mem B n i x x.property)]
          rw [DirectSum.lof_eq_of, DirectSum.coeAddMonoidHom_of]
          rfl
      | add x y hx hy =>
          change (DirectSum.coeAddMonoidHom (CellStage.limitGrading B))
            (CellStage.limitDecompose B
              ((DirectLimit.Module.of R ℕ
                (fun j : ℕ => (CellStage.at B j).dga.A)
                (fun j k h => CellStage.transition B j k h) i) (x + y))) =
              (DirectLimit.Module.of R ℕ
                (fun j : ℕ => (CellStage.at B j).dga.A)
                (fun j k h => CellStage.transition B j k h) i) (x + y)
          simp only [map_add]
          exact congrArg₂ (· + ·) hx hy

private theorem CellStage.limitDecompose_right_inv
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    letI := CellStage.directedSystem B
    Function.RightInverse
      (DirectSum.coeAddMonoidHom (CellStage.limitGrading B))
      (CellStage.limitDecompose B) := by
  let := CellStage.directedSystem B
  intro z
  induction z using DirectSum.induction_on with
  | zero => simp
  | of n x =>
      rw [DirectSum.coeAddMonoidHom_of]
      rw [CellStage.limitDecompose_of_mem B n x.1 x.2]
      rfl
  | add x y hx hy =>
      simp only [map_add, hx, hy]

private theorem CellStage.limitDifferential_mem_grading
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (n : ℤ) (z : letI := CellStage.directedSystem B
      DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun _ _ h => CellStage.transition B _ _ h))
    (hz : z ∈ CellStage.limitGrading B n) :
    CellStage.limitDifferential B z ∈ CellStage.limitGrading B (n + 1) := by
  let := CellStage.directedSystem B
  obtain ⟨i, x, hx, rfl⟩ := CellStage.limitGrading_exists_of B n z hz
  rw [CellStage.limitDifferential_of]
  exact CellStage.limitGrading_of_mem B (n + 1) i _
    ((CellStage.at B i).dga.d_mem n x hx)

/-- Images of stage elements multiply as the image of the product of their transitions. -/
private theorem CellStage.limit_of_mul_of
    (B : DifferentialGradedAlgebra.{u, max u v} R) {i j k : ℕ} (hik : i ≤ k) (hjk : j ≤ k)
    (a : (CellStage.at B i).dga.A) (b : (CellStage.at B j).dga.A) :
    letI := CellStage.directedSystem B
    DirectLimit.Module.of R ℕ (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun i j h => CellStage.transition B i j h) i a *
      DirectLimit.Module.of R ℕ (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun i j h => CellStage.transition B i j h) j b =
    DirectLimit.Module.of R ℕ (fun i : ℕ => (CellStage.at B i).dga.A)
      (fun i j h => CellStage.transition B i j h) k
      (CellStage.transition B i k hik a * CellStage.transition B j k hjk b) := by
  let := CellStage.directedSystem B
  change DirectLimit.Algebra.of (fun i : ℕ => (CellStage.at B i).dga.A)
      (fun i j h => CellStage.transition B i j h) i a *
    DirectLimit.Algebra.of (fun i : ℕ => (CellStage.at B i).dga.A)
      (fun i j h => CellStage.transition B i j h) j b = _
  rw [← DirectLimit.Algebra.of_f (G := fun i : ℕ => (CellStage.at B i).dga.A)
      (f := fun i j h => CellStage.transition B i j h) hik a,
    ← DirectLimit.Algebra.of_f (G := fun i : ℕ => (CellStage.at B i).dga.A)
      (f := fun i j h => CellStage.transition B i j h) hjk b, ← map_mul]
  rfl

/-- Images of a stage element at stages `i ≤ k` agree after applying the transition. -/
private theorem CellStage.limit_of_transition
    (B : DifferentialGradedAlgebra.{u, max u v} R) {i k : ℕ} (h : i ≤ k)
    (x : (CellStage.at B i).dga.A) :
    letI := CellStage.directedSystem B
    DirectLimit.Module.of R ℕ (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun i j h => CellStage.transition B i j h) i x =
      DirectLimit.Module.of R ℕ (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun i j h => CellStage.transition B i j h) k (CellStage.transition B i k h x) := by
  let := CellStage.directedSystem B
  exact (DirectLimit.Module.of_f (hij := h)).symm

/-- The map to the target sends the image of a stage element to its image under the stage map. -/
private theorem CellStage.limitToTarget_of
    (B : DifferentialGradedAlgebra.{u, max u v} R) (i : ℕ) (x : (CellStage.at B i).dga.A) :
    letI := CellStage.directedSystem B
    CellStage.limitToTarget B
      (DirectLimit.Module.of R ℕ (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun i j h => CellStage.transition B i j h) i x) = (CellStage.at B i).toTarget x := by
  let := CellStage.directedSystem B
  rw [CellStage.limitToTarget]
  exact DirectLimit.Algebra.lift_of ..

private theorem CellStage.limitGrading_mul_mem
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (n m : ℤ)
    (x y : letI := CellStage.directedSystem B
      DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun _ _ h => CellStage.transition B _ _ h))
    (hx : x ∈ CellStage.limitGrading B n)
    (hy : y ∈ CellStage.limitGrading B m) :
    x * y ∈ CellStage.limitGrading B (n + m) := by
  let := CellStage.directedSystem B
  obtain ⟨i, a, ha, rfl⟩ := CellStage.limitGrading_exists_of B n x hx
  obtain ⟨j, b, hb, rfl⟩ := CellStage.limitGrading_exists_of B m y hy
  rw [CellStage.limit_of_mul_of B (le_max_left i j) (le_max_right i j)]
  exact CellStage.limitGrading_of_mem B (n + m) _ _ (SetLike.mul_mem_graded
    ((CellStage.transition_isDGAMorphism B i _ (le_max_left i j)).1 n a ha)
    ((CellStage.transition_isDGAMorphism B j _ (le_max_right i j)).1 m b hb))


private theorem CellStage.limitToTarget_mem_grading
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (n : ℤ) (z : letI := CellStage.directedSystem B
      DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun _ _ h => CellStage.transition B _ _ h))
    (hz : z ∈ CellStage.limitGrading B n) :
    CellStage.limitToTarget B z ∈ B.grading n := by
  let := CellStage.directedSystem B
  obtain ⟨i, x, hx, rfl⟩ := CellStage.limitGrading_exists_of B n z hz
  rw [CellStage.limitToTarget_of]
  exact (CellStage.at B i).toTarget_isDGAMorphism.1 n x hx


private theorem CellStage.limitGrading_one_mem
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    letI := CellStage.directedSystem B
    (1 : DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
      (fun _ _ h => CellStage.transition B _ _ h)) ∈
      CellStage.limitGrading B 0 := by
  let := CellStage.directedSystem B
  rw [DirectLimit.one_def 0]
  exact CellStage.limitGrading_of_mem B 0 0 1
    (SetLike.one_mem_graded (CellStage.at B 0).dga.grading)

private theorem CellStage.limitDifferential_leibniz
    (B : DifferentialGradedAlgebra.{u, max u v} R) (n m : ℤ)
    (a b : letI := CellStage.directedSystem B
      DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun _ _ h => CellStage.transition B _ _ h))
    (ha : a ∈ CellStage.limitGrading B n)
    (hb : b ∈ CellStage.limitGrading B m) :
    CellStage.limitDifferential B (a * b) =
      CellStage.limitDifferential B a * b +
        (n.negOnePow : ℤ) • (a * CellStage.limitDifferential B b) := by
  let := CellStage.directedSystem B
  obtain ⟨i, x, hx, rfl⟩ := CellStage.limitGrading_exists_of B n a ha
  obtain ⟨j, y, hy, rfl⟩ := CellStage.limitGrading_exists_of B m b hb
  have hik := le_max_left i j
  have hjk := le_max_right i j
  have hstage := (CellStage.at B (max i j)).dga.leibniz n m _ _
    ((CellStage.transition_isDGAMorphism B i _ hik).1 n x hx)
    ((CellStage.transition_isDGAMorphism B j _ hjk).1 m y hy)
  rw [CellStage.limit_of_mul_of B hik hjk, CellStage.limitDifferential_of,
    CellStage.limitDifferential_of, CellStage.limitDifferential_of,
    CellStage.limit_of_mul_of B hik hjk, CellStage.limit_of_mul_of B hik hjk, hstage,
    (CellStage.transition_isDGAMorphism B i _ hik).2 x,
    (CellStage.transition_isDGAMorphism B j _ hjk).2 y, map_add, map_zsmul]


private noncomputable def CellStage.limitDGA
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    DifferentialGradedAlgebra.{u, max u v} R := by
  letI := CellStage.directedSystem B
  letI : GradedAlgebra (CellStage.limitGrading B) := {
    one_mem := CellStage.limitGrading_one_mem B
    mul_mem := by
      intro n m x y hx hy
      exact CellStage.limitGrading_mul_mem B n m x y hx hy
    decompose' := CellStage.limitDecompose B
    left_inv := CellStage.limitDecompose_left_inv B
    right_inv := CellStage.limitDecompose_right_inv B }
  exact {
    A := DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
      (fun i j h => CellStage.transition B i j h)
    grading := CellStage.limitGrading B
    d := CellStage.limitDifferential B
    d_comp_d := CellStage.limitDifferential_sq_zero B
    d_mem := CellStage.limitDifferential_mem_grading B
    leibniz := CellStage.limitDifferential_leibniz B }

private theorem CellStage.limitToTarget_isDGAMorphism
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    IsDGAMorphism (CellStage.limitDGA B) B (CellStage.limitToTarget B) := by
  constructor
  · exact CellStage.limitToTarget_mem_grading B
  · exact CellStage.limitToTarget_commutes_d B

/-- The cochain complex `C` models the differential graded algebra `A`: each term `C.X n` is
identified with the degree-`n` piece of `A`, compatibly with the differentials. -/
public structure ModelsComplex
    (A : DifferentialGradedAlgebra.{u, max u v} R)
    (C : CochainComplex (ModuleCat.{max u v} R) ℤ) where
  /-- The identification of the degree-`n` term of `C` with the degree-`n` piece of `A`. -/
  equiv : ∀ n : ℤ, (C.X n : Type (max u v)) ≃ₗ[R] A.grading n
  /-- The identifications carry the differential of `C` to the differential of `A`. -/
  d_compatible : ∀ (n : ℤ) (x : C.X n),
    ((equiv (n + 1)) (C.d n (n + 1) x)).1 = A.d ((equiv n x).1)

/-! The next two helpers make explicit the routine bridge from the internally graded carrier
of a DGA to a cochain complex of its homogeneous pieces. -/

private noncomputable def gradedComplex
    (A : DifferentialGradedAlgebra.{u, max u v} R) :
    CochainComplex (ModuleCat.{max u v} R) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of R (A.grading n))
    (fun n => ModuleCat.ofHom {
      toFun := fun x => ⟨A.d x.1, A.d_mem n x.1 x.2⟩
      map_add' x y := Subtype.ext (map_add A.d x.1 y.1)
      map_smul' r x := Subtype.ext (map_smul A.d r x.1) })
    (by
      intro n
      apply ModuleCat.hom_ext
      ext x
      change A.d (A.d x.1) = 0
      have h := LinearMap.congr_fun A.d_comp_d x.1
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h)

private theorem CellStage.initial_d_zero
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    ((CellStage.initial B).dga).d = 0 := by
  change freeWordDifferentialLinear (R := R)
    (fun s : Σ n : ℤ, {y : B.A // y ∈ B.grading n ∧ B.d y = 0} => s.1)
    (fun _ => 0) = 0
  exact freeWordDifferentialLinear_zero _

private theorem CellStage.initial_cycles_surjective
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    ∀ (n : ℤ) (y : B.A), y ∈ B.grading n → B.d y = 0 →
      ∃ x : (CellStage.at B 0).dga.A,
        x ∈ (CellStage.at B 0).dga.grading n ∧
        (CellStage.at B 0).dga.d x = 0 ∧
        (CellStage.at B 0).toTarget x = y := by
  intro n y hy hdy
  let s : (CellStage.at B 0).S := ⟨n, ⟨y, hy, hdy⟩⟩
  let x : (CellStage.at B 0).dga.A := monoidWord [s]
  refine ⟨x, ?_, ?_, ?_⟩
  · have hm := monoidWord_mem_grade (R := R)
      (CellStage.at B 0).degree [s]
    change x ∈ AddMonoidAlgebra.gradeBy R
      (freeWordDegree (CellStage.at B 0).degree) n
    have hs : ([s].map (CellStage.at B 0).degree).sum = n := by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rfl
    exact hs ▸ hm
  · have hd : (CellStage.at B 0).dga.d = 0 := CellStage.initial_d_zero B
    rw [hd]
    rfl
  · change freeZeroDGA_map B (CellStage.at B 0).degree
      (CellStage.at B 0).b x = y
    rw [show x = monoidWord [s] from rfl,
      freeZeroDGA_map_letter]
    rfl

private theorem CellStage.limit_cycles_surjective
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    letI := CellStage.directedSystem B
    ∀ (n : ℤ) (y : B.A), y ∈ B.grading n → B.d y = 0 →
      ∃ z : DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun _ _ h => CellStage.transition B _ _ h),
        z ∈ CellStage.limitGrading B n ∧
        CellStage.limitDifferential B z = 0 ∧
        CellStage.limitToTarget B z = y := by
  let := CellStage.directedSystem B
  intro n y hy hdy
  obtain ⟨x, hx, hdx, hfx⟩ := CellStage.initial_cycles_surjective B n y hy hdy
  let z := DirectLimit.Module.of R ℕ
    (fun i : ℕ => (CellStage.at B i).dga.A)
    (fun i j h => CellStage.transition B i j h) 0 x
  refine ⟨z, CellStage.limitGrading_of_mem B n 0 x hx, ?_, ?_⟩
  · rw [show z = DirectLimit.Module.of R ℕ
        (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun i j h => CellStage.transition B i j h) 0 x from rfl,
      CellStage.limitDifferential_of]
    change (DirectLimit.Module.of R ℕ
      (fun i : ℕ => (CellStage.at B i).dga.A)
      (fun i j h => CellStage.transition B i j h) 0)
        ((CellStage.at B 0).dga.d x) = 0
    rw [hdx, map_zero]
  · rw [CellStage.limitToTarget_of]
    exact hfx

private theorem CellStage.limit_kills_kernel
    (B : DifferentialGradedAlgebra.{u, max u v} R) (n : ℤ)
    (z : letI := CellStage.directedSystem B
      DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun _ _ h => CellStage.transition B _ _ h))
    (hz : z ∈ CellStage.limitGrading B n)
    (hdz : CellStage.limitDifferential B z = 0)
    (hbound : ∃ y : B.A, y ∈ B.grading (n - 1) ∧
      B.d y = CellStage.limitToTarget B z) :
    ∃ w, w ∈ CellStage.limitGrading B (n - 1) ∧
      CellStage.limitDifferential B w = z := by
  let := CellStage.directedSystem B
  obtain ⟨i, x, hx, rfl⟩ := CellStage.limitGrading_exists_of B n z hz
  have hdx : (DirectLimit.Module.of R ℕ
      (fun i : ℕ => (CellStage.at B i).dga.A)
      (fun i j h => CellStage.transition B i j h) i)
      ((CellStage.at B i).dga.d x) = 0 := by
    rw [← CellStage.limitDifferential_of]
    exact hdz
  have hdx' : (⟦⟨i, (CellStage.at B i).dga.d x⟩⟧ :
      DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun i j h => CellStage.transition B i j h)) = 0 := by
    simpa only [DirectLimit.Module.of, LinearMap.coe_mk, AddHom.coe_mk] using hdx
  obtain ⟨j, hij, hj⟩ := (DirectLimit.exists_eq_zero
    (f := fun i j h => CellStage.transition B i j h)
    ⟨i, (CellStage.at B i).dga.d x⟩).mp hdx'
  let xj := CellStage.transition B i j hij x
  have hxj : xj ∈ (CellStage.at B j).dga.grading n :=
    (CellStage.transition_isDGAMorphism B i j hij).1 n x hx
  have hdxj : (CellStage.at B j).dga.d xj = 0 := by
    rw [← (CellStage.transition_isDGAMorphism B i j hij).2 x]
    exact hj
  have hboundj : ∃ y : B.A, y ∈ B.grading (n - 1) ∧
      B.d y = (CellStage.at B j).toTarget xj := by
    obtain ⟨y, hy, hdy⟩ := hbound
    exact ⟨y, hy, by
      rw [CellStage.transition_toTarget B i j hij x, ← CellStage.limitToTarget_of]
      exact hdy⟩
  obtain ⟨w, hw, hdw⟩ := CellStage.next_kills_kernel_at B j n xj hxj hdxj hboundj
  let w' := DirectLimit.Module.of R ℕ
    (fun i : ℕ => (CellStage.at B i).dga.A)
    (fun i j h => CellStage.transition B i j h) (j + 1) w
  refine ⟨w', CellStage.limitGrading_of_mem B (n - 1) (j + 1) w hw, ?_⟩
  rw [show w' = DirectLimit.Module.of R ℕ
    (fun i : ℕ => (CellStage.at B i).dga.A)
    (fun i j h => CellStage.transition B i j h) (j + 1) w from rfl,
    CellStage.limitDifferential_of]
  change (DirectLimit.Module.of R ℕ
    (fun i : ℕ => (CellStage.at B i).dga.A)
    (fun i j h => CellStage.transition B i j h) (j + 1))
      ((CellStage.at B (j + 1)).dga.d w) = _
  rw [hdw]
  have hstep : CellStage.transition B j (j + 1) (Nat.le_succ j) xj =
      CellStage.inclusion B (CellStage.at B j) xj := by
    rw [CellStage.transition_step B j j (le_refl j), CellStage.transition_self]
    rfl
  rw [← hstep, ← CellStage.limit_of_transition, ← CellStage.limit_of_transition]

private noncomputable def gradedComplexModels
    (A : DifferentialGradedAlgebra.{u, max u v} R) :
    ModelsComplex A (gradedComplex A) where
  equiv n := LinearEquiv.refl R (A.grading n)
  d_compatible n x := by
    simp only [gradedComplex, CochainComplex.of_d]
    rfl

private noncomputable def gradedComplexMap
    {A B : DifferentialGradedAlgebra.{u, max u v} R}
    (f : A.A →ₐ[R] B.A) (hf : IsDGAMorphism A B f) :
    gradedComplex A ⟶ gradedComplex B :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom {
    toFun := fun x => ⟨f x.1, hf.1 n x.1 x.2⟩
    map_add' x y := Subtype.ext (map_add f.toLinearMap x.1 y.1)
    map_smul' r x := Subtype.ext (map_smul f.toLinearMap r x.1) })
    (by
      intro n
      apply ModuleCat.hom_ext
      ext x
      simp only [gradedComplex, CochainComplex.of_d]
      exact Subtype.ext (hf.2 x.1).symm)

/-- The differential of `gradedComplex A` is the differential of `A` on the underlying elements. -/
private theorem gradedComplex_d_val
    (A : DifferentialGradedAlgebra.{u, max u v} R) {n : ℤ} (x : (gradedComplex A).X n) :
    (((gradedComplex A).d n (n + 1)).hom x).1 = A.d x.1 := by
  simp only [gradedComplex, CochainComplex.of_d]
  rfl

private theorem shortComplex_quasiIso_of_cycle_boundaries
    {S T : ShortComplex (ModuleCat.{max u v} R)} (f : S ⟶ T)
    (hinj : ∀ x : S.X₂, S.g x = 0 → f.τ₂ x ∈ LinearMap.range T.f.hom →
      x ∈ LinearMap.range S.f.hom)
    (hsurj : ∀ y : T.X₂, T.g y = 0 → ∃ x : S.X₂,
      S.g x = 0 ∧ y - f.τ₂ x ∈ LinearMap.range T.f.hom) :
    ShortComplex.QuasiIso f := by
  let c : LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
    (f.τ₂.hom.comp (LinearMap.ker S.g.hom).subtype).codRestrict _ (by
      intro x
      have h := ConcreteCategory.congr_hom f.comm₂₃ x.val
      change T.g (f.τ₂ x.val) = f.τ₃ (S.g x.val) at h
      change T.g (f.τ₂ x.val) = 0
      rw [h, show S.g x.val = 0 from x.property, map_zero])
  have hc : LinearMap.range S.moduleCatToCycles ≤
      (LinearMap.range T.moduleCatToCycles).comap c := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f.τ₁ x, Subtype.ext (ConcreteCategory.congr_hom f.comm₁₂ x)⟩
  let q := (LinearMap.range S.moduleCatToCycles).mapQ
    (LinearMap.range T.moduleCatToCycles) c hc
  let data : ShortComplex.LeftHomologyMapData f
      S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData := {
    φK := ModuleCat.ofHom c
    φH := ModuleCat.ofHom q
    commi := by ext x; rfl
    commf' := by
      ext x
      exact Subtype.ext (ConcreteCategory.congr_hom f.comm₁₂ x).symm
    commπ := by ext x; rfl }
  rw [data.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective q
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨x, rfl⟩ := (LinearMap.range S.moduleCatToCycles).mkQ_surjective x
    change (LinearMap.range T.moduleCatToCycles).mkQ (c x) = 0 at hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx ⊢
    obtain ⟨y, hy⟩ := hx
    have hxy : f.τ₂ x.val ∈ LinearMap.range T.f.hom :=
      ⟨y, congrArg Subtype.val hy⟩
    obtain ⟨z, hz⟩ := hinj x.val x.property hxy
    exact ⟨z, Subtype.ext hz⟩
  · intro y
    obtain ⟨y, rfl⟩ := (LinearMap.range T.moduleCatToCycles).mkQ_surjective y
    obtain ⟨x, hx, z, hz⟩ := hsurj y.val y.property
    refine ⟨(LinearMap.range S.moduleCatToCycles).mkQ ⟨x, hx⟩, ?_⟩
    change (LinearMap.range T.moduleCatToCycles).mkQ (c ⟨x, hx⟩) =
      (LinearMap.range T.moduleCatToCycles).mkQ y
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine ⟨-z, ?_⟩
    apply Subtype.ext
    change T.f (-z) = f.τ₂ x - y.val
    rw [map_neg, hz]
    abel

private theorem gradedComplexMap_quasiIso_of_cycle_conditions
    {A B : DifferentialGradedAlgebra.{u, max u v} R}
    (f : A.A →ₐ[R] B.A) (hf : IsDGAMorphism A B f)
    (hsurj : ∀ (n : ℤ) (y : B.A), y ∈ B.grading n → B.d y = 0 →
      ∃ x : A.A, x ∈ A.grading n ∧ A.d x = 0 ∧ f x = y)
    (hinj : ∀ (n : ℤ) (x : A.A), x ∈ A.grading n → A.d x = 0 →
      (∃ y : B.A, y ∈ B.grading (n - 1) ∧ B.d y = f x) →
      ∃ z : A.A, z ∈ A.grading (n - 1) ∧ A.d z = x) :
    QuasiIso (gradedComplexMap f hf) := by
  constructor
  intro n
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, m + 1 = n := ⟨n - 1, by omega⟩
  rw [quasiIsoAt_iff' (gradedComplexMap f hf) m (m + 1) ((m + 1) + 1)
    (by simp) (by simp)]
  apply shortComplex_quasiIso_of_cycle_boundaries
  · intro x hx hbound
    obtain ⟨y, hy⟩ := hbound
    obtain ⟨z, hz, hdz⟩ := hinj (m + 1) x.1 x.2
      ((gradedComplex_d_val A x).symm.trans (congrArg Subtype.val hx))
      ⟨y.1, by simpa using y.2,
        (gradedComplex_d_val B y).symm.trans (congrArg Subtype.val hy)⟩
    exact ⟨⟨z, by simpa using hz⟩, Subtype.ext ((gradedComplex_d_val A _).trans hdz)⟩
  · intro y hdy
    obtain ⟨x, hx, hdx, hfx⟩ := hsurj (m + 1) y.1 y.2
      ((gradedComplex_d_val B y).symm.trans (congrArg Subtype.val hdy))
    refine ⟨⟨x, hx⟩, Subtype.ext ((gradedComplex_d_val A ⟨x, hx⟩).trans hdx), ?_⟩
    convert Submodule.zero_mem _
    exact sub_eq_zero.mpr (Subtype.ext hfx).symm

private theorem gradedComplexMap_models
    {A B : DifferentialGradedAlgebra.{u, max u v} R}
    (f : A.A →ₐ[R] B.A) (hf : IsDGAMorphism A B f) (n : ℤ)
    (x : (gradedComplex A).X n) :
    ((gradedComplexModels B).equiv n ((gradedComplexMap f hf).f n x)).1 =
      f (((gradedComplexModels A).equiv n x).1) := by
  rfl

private theorem resolution_witnesses_of_gradedComplex
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (A : DifferentialGradedAlgebra.{u, max u v} R)
    (f : A.A →ₐ[R] B.A) (hfree : IsFreeGradedAlgebra A)
    (hflat : (gradedComplex A).KFlat)
    (hf : IsDGAMorphism A B f)
    (hq : QuasiIso (gradedComplexMap f hf)) :
    ∃ (A : DifferentialGradedAlgebra.{u, max u v} R)
      (f : A.A →ₐ[R] B.A)
      (CA CB : CochainComplex (ModuleCat.{max u v} R) ℤ)
      (eA : ModelsComplex A CA) (eB : ModelsComplex B CB)
      (g : CA ⟶ CB),
      IsFreeGradedAlgebra A ∧
        CA.KFlat ∧
        IsDGAMorphism A B f ∧
        (∀ (n : ℤ) (x : CA.X n),
          (eB.equiv n (g.f n x)).1 = f ((eA.equiv n x).1)) ∧
        QuasiIso g :=
  ⟨A, f, gradedComplex A, gradedComplex B,
    gradedComplexModels A, gradedComplexModels B,
    gradedComplexMap f hf, hfree, hflat, hf,
    gradedComplexMap_models f hf, hq⟩

private theorem CellStage.limitToTarget_quasiIso
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    QuasiIso (gradedComplexMap (A := CellStage.limitDGA B) (B := B)
      (CellStage.limitToTarget B)
      (CellStage.limitToTarget_isDGAMorphism B)) := by
  let := CellStage.directedSystem B
  exact gradedComplexMap_quasiIso_of_cycle_conditions _ _ (CellStage.limit_cycles_surjective B)
    (CellStage.limit_kills_kernel B)

private abbrev CellStage.limitAlphabet
    (B : DifferentialGradedAlgebra.{u, max u v} R) : Type (max u v) :=
  (CellStage.initial B).S ⊕
    Σ i : ℕ, CellStage.nextAlphabet B (CellStage.at B i)

private noncomputable def CellStage.stageLetter
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    (i : ℕ) → (CellStage.at B i).S → CellStage.limitAlphabet B
  | 0 => Sum.inl
  | i + 1 => Sum.elim (CellStage.stageLetter B i)
      (fun t => Sum.inr ⟨i, t⟩)

private theorem CellStage.stageLetter_inclusion
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i : ℕ) (s : (CellStage.at B i).S) :
    CellStage.stageLetter B (i + 1) (Sum.inl s) =
      CellStage.stageLetter B i s := rfl

private theorem CellStage.stageLetter_new
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i : ℕ) (t : CellStage.nextAlphabet B (CellStage.at B i)) :
    CellStage.stageLetter B (i + 1) (Sum.inr t) =
      Sum.inr ⟨i, t⟩ := rfl

private noncomputable def CellStage.limitDegree
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    CellStage.limitAlphabet B → ℤ
  | Sum.inl s => (CellStage.initial B).degree s
  | Sum.inr ⟨i, t⟩ => (CellStage.at B (i + 1)).degree (Sum.inr t)

private theorem CellStage.limitDegree_stageLetter
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i : ℕ) (s : (CellStage.at B i).S) :
    CellStage.limitDegree B (CellStage.stageLetter B i s) =
      (CellStage.at B i).degree s := by
  induction i with
  | zero => rfl
  | succ i ih =>
      cases s with
      | inl s => exact ih s
      | inr t => rfl

private noncomputable def CellStage.limitLetter
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    CellStage.limitAlphabet B →
      (letI := CellStage.directedSystem B
       DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
         (fun i j h => CellStage.transition B i j h)) := by
  letI := CellStage.directedSystem B
  intro s
  cases s with
  | inl s =>
      exact DirectLimit.Algebra.of
        (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun i j h => CellStage.transition B i j h) 0 (monoidWord [s])
  | inr q =>
      exact DirectLimit.Algebra.of
        (fun i : ℕ => (CellStage.at B i).dga.A)
        (fun i j h => CellStage.transition B i j h) (q.1 + 1)
        (monoidWord [Sum.inr q.2])

private noncomputable def CellStage.limitFreeMap
    (B : DifferentialGradedAlgebra.{u, max u v} R) :
    FreeAlgebra R (CellStage.limitAlphabet B) →ₐ[R]
      (letI := CellStage.directedSystem B
       DirectLimit (fun i : ℕ => (CellStage.at B i).dga.A)
         (fun i j h => CellStage.transition B i j h)) := by
  letI := CellStage.directedSystem B
  exact FreeAlgebra.lift R (CellStage.limitLetter B)

private noncomputable def CellStage.stageFreeMap
    (B : DifferentialGradedAlgebra.{u, max u v} R) (i : ℕ) :
    (CellStage.at B i).dga.A →ₐ[R]
      FreeAlgebra R (CellStage.limitAlphabet B) :=
  (FreeAlgebra.lift R
    (fun s => FreeAlgebra.ι R (CellStage.stageLetter B i s))).comp
      (freeAlgebraWordEquiv (R := R)
        (S := (CellStage.at B i).S)).symm.toAlgHom

private theorem CellStage.stageFreeMap_monoidWord
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i : ℕ) (w : List (CellStage.at B i).S) :
    CellStage.stageFreeMap B i (monoidWord w) =
      word (w.map (CellStage.stageLetter B i)) := by
  change (FreeAlgebra.lift R
    (fun s => FreeAlgebra.ι R (CellStage.stageLetter B i s)))
      ((freeAlgebraWordEquiv (R := R)
        (S := (CellStage.at B i).S)).symm (monoidWord w)) = _
  calc
    _ = (FreeAlgebra.lift R
      (fun s => FreeAlgebra.ι R (CellStage.stageLetter B i s)))
      ((freeAlgebraWordEquiv (R := R)
        (S := (CellStage.at B i).S)).symm
        (freeAlgebraWordEquiv (R := R)
          (S := (CellStage.at B i).S) (word w))) :=
        congrArg (fun a => (FreeAlgebra.lift R
          (fun s => FreeAlgebra.ι R (CellStage.stageLetter B i s)))
          ((freeAlgebraWordEquiv (R := R)
            (S := (CellStage.at B i).S)).symm a))
          (freeAlgebraWordEquiv_word (R := R) w).symm
    _ = (FreeAlgebra.lift R
      (fun s => FreeAlgebra.ι R (CellStage.stageLetter B i s))) (word w) := by
        rw [AlgEquiv.symm_apply_apply]
    _ = word (w.map (CellStage.stageLetter B i)) := by
        rw [map_word]
        simp only [FreeAlgebra.lift_ι_apply, word, List.foldl_map]

private theorem hom_eq_on_monoidWord
    {S : Type (max u v)} {T : Type (max u v)} [Ring T] [Algebra R T]
    (f g : AddMonoidAlgebra R (Additive (FreeMonoid S)) →ₐ[R] T)
    (h : ∀ w : List S, f (monoidWord w) = g (monoidWord w))
    (x : AddMonoidAlgebra R (Additive (FreeMonoid S))) : f x = g x := by
  have hx : x ∈ Submodule.span R (Set.range (monoidWord (R := R) (S := S))) := by
    rw [monoidWord_span_eq_top]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact h w
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using congrArg₂ (· + ·) ihx ihy
  | smul r x hx ihx =>
      simpa only [map_smul] using congrArg (r • ·) ihx

private theorem CellStage.stageFreeMap_inclusion
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i : ℕ) (x : (CellStage.at B i).dga.A) :
    CellStage.stageFreeMap B (i + 1)
      (CellStage.inclusion B (CellStage.at B i) x) =
        CellStage.stageFreeMap B i x := by
  apply hom_eq_on_monoidWord (R := R)
    ((CellStage.stageFreeMap B (i + 1)).comp
      (CellStage.inclusion B (CellStage.at B i)))
    (CellStage.stageFreeMap B i) _ x
  intro w
  let ι : (CellStage.at B i).S → (CellStage.at B (i + 1)).S := Sum.inl
  change CellStage.stageFreeMap B (i + 1)
    (freeWordMap (R := R) ι (monoidWord w)) = _
  rw [freeWordMap_monoidWord, CellStage.stageFreeMap_monoidWord]
  calc
    word ((w.map ι).map (CellStage.stageLetter B (i + 1))) =
        word (w.map (CellStage.stageLetter B i)) := by
      congr 1
      simp only [List.map_map]
      exact List.map_congr_left (fun s _ => CellStage.stageLetter_inclusion B i s)
    _ = CellStage.stageFreeMap B i (monoidWord w) :=
      (CellStage.stageFreeMap_monoidWord B i w).symm

private theorem CellStage.stageFreeMap_transition
    (B : DifferentialGradedAlgebra.{u, max u v} R)
    (i j : ℕ) (hij : i ≤ j) (x : (CellStage.at B i).dga.A) :
    CellStage.stageFreeMap B j (CellStage.transition B i j hij x) =
      CellStage.stageFreeMap B i x := by
  induction j generalizing i with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst i
      rw [CellStage.transition_self]
      rfl
  | succ j ih =>
      by_cases h : i ≤ j
      · rw [CellStage.transition_step B i j h]
        change CellStage.stageFreeMap B (j + 1)
          (CellStage.inclusion B (CellStage.at B j)
            (CellStage.transition B i j h x)) = _
        rw [CellStage.stageFreeMap_inclusion, ih i h]
      · have hi : i = j + 1 := by omega
        subst i
        rw [CellStage.transition_self]
        rfl

end Stacks.DGA

end
