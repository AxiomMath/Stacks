module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Tactic.IntervalCases
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.CochainComplex
public import StacksFrontier.Algebra.DifferentialGraded.Opposite

/-!
# Left differential graded modules and graded opposition

A *left* differential graded module over a differential graded algebra `(A, d)` over a
commutative ring `R` is a graded left `A`-module with a square-zero degree-`+1` differential
satisfying the left Leibniz rule `d (a x) = (d a) x + (-1)^{deg a} a (d x)`. Taking the graded
opposite of `A` identifies left `A`-modules with right modules over `A^opp`: the underlying
graded complex is unchanged and the action is transported with the Koszul sign. This
identification is an equivalence of categories, and it is why the chapter can restrict attention
to right modules.

## Main definitions

* `DifferentialGraded.LeftModule`: a left differential graded module.
* `DifferentialGraded.LeftModule.Hom`: a morphism of left differential graded modules, and the
  resulting category.
* `DifferentialGraded.OppositeEquivalence`: the specification of the canonical
  equivalence — an equivalence of categories together with the identification of the underlying
  graded complexes and the signed formula for the transported action.

## Main results

* `DifferentialGraded.leftRightEquivalence`: graded opposition is such an equivalence.

## Implementation notes

Left modules are defined independently of right modules, with their own left Leibniz rule,
rather than as right modules over the opposite — otherwise the statement would be a tautology.
The equivalence is specified rather than merely asserted to exist: its fields record that it
fixes the underlying graded complex and its differential, that it is natural, and that it
transports the action by the Koszul sign `(-1)^{deg a · deg x}`. Since the opposite algebra may
have a different Lean carrier, the canonical `R`-linear identification of its underlying graded
module with that of `A`, supplied by `DifferentialGradedAlgebra.opposite`, appears explicitly in
the action formula.

The quadratic Koszul sign `(-1)^{n(n+1)/2}` appearing in the comparison of the two sign
conventions is `DifferentialGraded.koszulQuadraticSign`, computed by cases on
`n % 4`.

## References

* [Stacks Project, Tag 0FQ0](https://stacks.math.columbia.edu/tag/0FQ0)
-/

@[expose] public section

open CategoryTheory

namespace DifferentialGraded

universe u v w

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}

/-- A left differential graded module over `A`. -/
public structure LeftModule (A : DifferentialGradedAlgebra.{u, v} R) where
  /-- The underlying type of the module. -/
  M : Type u
  [addCommGroup : AddCommGroup M]
  [module : Module R M]
  [amodule : Module A.A M]
  [isScalarTower : IsScalarTower R A.A M]
  /-- The grading: the `R`-submodule of elements of each degree. -/
  grading : ℤ → Submodule R M
  [decomposition : DirectSum.Decomposition grading]
  smul_mem : ∀ (m n : ℤ) (a : A.A) (x : M),
    a ∈ A.grading m → x ∈ grading n → a • x ∈ grading (m + n)
  /-- The differential, of degree `+1`. -/
  d : M →ₗ[R] M
  d_comp_d : d ∘ₗ d = 0
  d_mem : ∀ (n : ℤ) (x : M), x ∈ grading n → d x ∈ grading (n + 1)
  leibniz : ∀ (m n : ℤ) (a : A.A) (x : M),
    a ∈ A.grading m → x ∈ grading n →
      d (a • x) = A.d a • x + (m.negOnePow : ℤ) • (a • d x)

attribute [instance] LeftModule.addCommGroup LeftModule.module LeftModule.amodule
  LeftModule.isScalarTower LeftModule.decomposition

/-- A degree-zero, action-linear chain map of left differential graded modules. -/
@[ext]
public structure LeftModule.Hom (M N : LeftModule A) where
  /-- The underlying `R`-linear map. -/
  toFun : M.M →ₗ[R] N.M
  map_smul : ∀ (a : A.A) (x : M.M), toFun (a • x) = a • toFun x
  map_grading : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → toFun x ∈ N.grading n
  map_d : toFun ∘ₗ M.d = N.d ∘ₗ toFun

namespace LeftModule

/-- Identity morphism of a left differential graded module. -/
public def Hom.id (M : LeftModule A) : Hom M M where
  toFun := LinearMap.id
  map_smul := by intros; rfl
  map_grading := by intros; assumption
  map_d := by rfl

/-- Composition of left differential graded module morphisms. -/
public def Hom.comp {M N P : LeftModule A} (g : Hom N P) (f : Hom M N) :
    Hom M P where
  toFun := g.toFun ∘ₗ f.toFun
  map_smul := by intro a x; simp [f.map_smul, g.map_smul]
  map_grading := by intro n x hx; exact g.map_grading n _ (f.map_grading n x hx)
  map_d := by
    ext x
    have hf := LinearMap.congr_fun f.map_d x
    have hg := LinearMap.congr_fun g.map_d (f.toFun x)
    exact (congrArg g.toFun hf).trans hg

/-- Left differential graded `A`-modules form a category. -/
public instance : Category (LeftModule A) where
  Hom M N := Hom M N
  id M := Hom.id M
  comp f g := Hom.comp g f
  id_comp := by intro M N f; ext x; rfl
  comp_id := by intro M N f; ext x; rfl
  assoc := by intro M N P Q f g h; ext x; rfl

end LeftModule

/-- An equivalence which realizes the graded-opposite action on every left module. -/
public structure OppositeEquivalence (R : Type u) [CommRing R]
    (A : DifferentialGradedAlgebra.{u, v} R) where
  /-- The equivalence from left modules over `A` to right modules over the graded opposite. -/
  equivalence : LeftModule A ≌
    DifferentialGradedModule.{u, v, u}
      (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra
  /-- The identification of the underlying module of the image of `M` with that of `M`. -/
  underlying (M : LeftModule A) :
    (equivalence.functor.obj M).M ≃ₗ[R] M.M
  grading (M : LeftModule A) (n : ℤ)
      (x : (equivalence.functor.obj M).M) :
    x ∈ (equivalence.functor.obj M).grading n ↔ underlying M x ∈ M.grading n
  differential (M : LeftModule A)
      (x : (equivalence.functor.obj M).M) :
    underlying M ((equivalence.functor.obj M).d x) = M.d (underlying M x)
  naturality {M N : LeftModule A} (f : M ⟶ N)
      (x : (equivalence.functor.obj M).M) :
    underlying N ((equivalence.functor.map f).toFun x) =
      f.toFun (underlying M x)
  action (M : LeftModule A) (m n : ℤ)
      (a : (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra.A)
      (x : (equivalence.functor.obj M).M)
      (ha : a ∈ (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra.grading m)
      (hx : x ∈ (equivalence.functor.obj M).grading n) :
    underlying M (MulOpposite.op a • x) =
      (m * n).negOnePow • ((DifferentialGradedAlgebra.opposite R A).equiv a • underlying M x)

/-- The quadratic Koszul sign `(-1)^{n(n+1)/2}`, computed from `n % 4`. -/
public def koszulQuadraticSign (n : ℤ) : ℤˣ :=
  if n % 4 = 2 ∨ n % 4 = 3 then -1 else 1

private lemma intNegOnePowModTwo (n : ℤ) : n.negOnePow = (n % 2).negOnePow := by
  have hn : n = 2 * (n / 2) + n % 2 := by omega
  rw [hn, Int.negOnePow_add, Int.negOnePow_two_mul]
  simp

private lemma koszulQuadraticSign_add (m n : ℤ) :
    koszulQuadraticSign (m + n) = (m * n).negOnePow * koszulQuadraticSign m *
      koszulQuadraticSign n := by
  have hm0 : 0 ≤ m % 4 := Int.emod_nonneg _ (by decide)
  have hm1 : m % 4 < 4 := Int.emod_lt _ (by decide)
  have hn0 : 0 ≤ n % 4 := Int.emod_nonneg _ (by decide)
  have hn1 : n % 4 < 4 := Int.emod_lt _ (by decide)
  interval_cases hm : m % 4 <;> interval_cases hn : n % 4
  all_goals
    have hmp : m % 2 = (m % 4) % 2 := by omega
    have hnp : n % 2 = (n % 4) % 2 := by omega
    unfold koszulQuadraticSign
    rw [Int.add_emod]
    simp only [hm, hn]
    rw [intNegOnePowModTwo, Int.mul_emod]
    rw [hmp, hnp, hm, hn]
    norm_num [Int.negOnePow]

private lemma koszulQuadraticSign_square (n : ℤ) :
    koszulQuadraticSign n * koszulQuadraticSign n = 1 := by
  unfold koszulQuadraticSign
  split <;> norm_num

private lemma intNegOnePow_square (n : ℤ) : n.negOnePow * n.negOnePow = 1 := by
  rw [← Int.negOnePow_add]
  rw [show n + n = 2 * n by ring, Int.negOnePow_two_mul]

/-- `(-1)^{mn} (-1)^m = (-1)^{m(n+1)}`. -/
public lemma intNegOnePow_mul_succ (m n : ℤ) :
    (m * n).negOnePow * m.negOnePow = (m * (n + 1)).negOnePow := by
  rw [← Int.negOnePow_add]
  congr 1
  ring

/-- `(-1)^n (-1)^{(m+1)n} = (-1)^{mn}`. -/
public lemma intNegOnePow_diff_succ (m n : ℤ) :
    n.negOnePow * ((m + 1) * n).negOnePow = (m * n).negOnePow := by
  rw [← Int.negOnePow_add]
  have h : n + (m + 1) * n = 2 * n + m * n := by ring
  rw [h, Int.negOnePow_add, Int.negOnePow_two_mul, one_mul]

/-- Casting a product identity of integer units to a ring. -/
private lemma intCast_units_mul {S : Type*} [Ring S] {a b c : ℤˣ} (h : a * b = c) :
    ((a : ℤ) : S) * ((b : ℤ) : S) = ((c : ℤ) : S) := by
  rw [← Int.cast_mul, ← Units.val_mul, h]

private lemma units_smul_eq_intCast_smul (M : Type*) [AddCommGroup M]
    [Module R M] (u : ℤˣ) (x : M) :
    u • x = ((u : ℤ) : R) • x := by
  rw [Units.smul_def]
  exact (Int.cast_smul_eq_zsmul R (u : ℤ) x).symm

/-- The quadratic Koszul sign of `m + n` times `(-1)^{mn}` is the product of the quadratic Koszul
signs of `m` and `n`. -/
public lemma koszulQuadraticSign_mul_add (m n : ℤ) :
    koszulQuadraticSign (m + n) * (m * n).negOnePow =
      koszulQuadraticSign m * koszulQuadraticSign n := by
  rw [koszulQuadraticSign_add]
  calc
    (m * n).negOnePow * koszulQuadraticSign m * koszulQuadraticSign n *
        (m * n).negOnePow =
        ((m * n).negOnePow * (m * n).negOnePow) *
          (koszulQuadraticSign m * koszulQuadraticSign n) := by ac_rfl
    _ = 1 * (koszulQuadraticSign m * koszulQuadraticSign n) := by
      rw [intNegOnePow_square]
    _ = _ := by simp

private lemma koszulQuadraticSign_mul_prod (m n : ℤ) :
    koszulQuadraticSign m * koszulQuadraticSign n * koszulQuadraticSign (m + n) =
      (m * n).negOnePow := by
  rw [koszulQuadraticSign_add]
  calc
    koszulQuadraticSign m * koszulQuadraticSign n *
        ((m * n).negOnePow * koszulQuadraticSign m * koszulQuadraticSign n) =
        (m * n).negOnePow *
          (koszulQuadraticSign m * koszulQuadraticSign m) *
            (koszulQuadraticSign n * koszulQuadraticSign n) := by ac_rfl
    _ = (m * n).negOnePow := by
      rw [koszulQuadraticSign_square, koszulQuadraticSign_square]
      simp

/-- The `R`-linear map multiplying each homogeneous element of degree `n` by the quadratic Koszul
sign of `n`. -/
public noncomputable def gradedSignTwist (R : Type u) [CommRing R] (M : Type w)
    [AddCommGroup M] [Module R M] (g : ℤ → Submodule R M)
    [DirectSum.Decomposition g] : M →ₗ[R] M :=
  (DirectSum.toModule R ℤ M
    (fun n => ((koszulQuadraticSign n : ℤ) : R) • (g n).subtype)).comp
      (DirectSum.decomposeLinearEquiv g).toLinearMap

/-- On an element of degree `n`, `gradedSignTwist` is multiplication by the quadratic Koszul
sign of `n`. -/
public lemma gradedSignTwist_apply_mem (R : Type u) [CommRing R] (M : Type w)
    [AddCommGroup M] [Module R M] (g : ℤ → Submodule R M)
    [DirectSum.Decomposition g] {n : ℤ} {x : M} (hx : x ∈ g n) :
    gradedSignTwist R M g x = ((koszulQuadraticSign n : ℤ) : R) • x := by
  unfold gradedSignTwist
  simp only [LinearMap.comp_apply]
  have h := DirectSum.decomposeLinearEquiv_apply_coe g n ⟨x, hx⟩
  change (DirectSum.toModule R ℤ M
      (fun n => ((koszulQuadraticSign n : ℤ) : R) • (g n).subtype))
        ((DirectSum.decomposeLinearEquiv g) x) = _
  change DirectSum.decomposeLinearEquiv g x = _ at h
  rw [h, DirectSum.toModule_lof]
  rfl

/-- `gradedSignTwist` is an involution. -/
public lemma gradedSignTwist_involutive (R : Type u) [CommRing R] (M : Type w)
    [AddCommGroup M] [Module R M] (g : ℤ → Submodule R M)
    [DirectSum.Decomposition g] : Function.Involutive (gradedSignTwist R M g) := by
  intro x
  induction x using DirectSum.Decomposition.inductionOn g with
  | zero => simp [gradedSignTwist]
  | @homogeneous n x =>
      have hx : (((koszulQuadraticSign n : ℤ) : R) • (x : M)) ∈ g n :=
        (g n).smul_mem _ x.property
      rw [gradedSignTwist_apply_mem R M g x.property,
        gradedSignTwist_apply_mem R M g hx]
      simp only [smul_smul]
      rw [intCast_units_mul (koszulQuadraticSign_square n), Units.val_one, Int.cast_one, one_smul]
  | add a b ha hb => simp [map_add, ha, hb]

/-- `gradedSignTwist` as an `R`-linear automorphism, its own inverse. -/
public noncomputable def gradedSignTwistEquiv (R : Type u) [CommRing R] (M : Type w)
    [AddCommGroup M] [Module R M] (g : ℤ → Submodule R M)
    [DirectSum.Decomposition g] : M ≃ₗ[R] M :=
  LinearEquiv.ofInvolutive (gradedSignTwist R M g)
    (gradedSignTwist_involutive R M g)

private lemma gradedSignTwistEquiv_apply_mem (R : Type u) [CommRing R] (M : Type w)
    [AddCommGroup M] [Module R M] (g : ℤ → Submodule R M)
    [DirectSum.Decomposition g] {n : ℤ} {x : M} (hx : x ∈ g n) :
    gradedSignTwistEquiv R M g x = ((koszulQuadraticSign n : ℤ) : R) • x :=
  gradedSignTwist_apply_mem R M g hx

/-- The action `T →+* End_R M` obtained from an action of `S` by precomposing with a ring
isomorphism `T ≃+* S` and conjugating by a linear automorphism `Q` of `M`. -/
public noncomputable def conjugatedModuleAction {S T M : Type*}
    [Semiring S] [Semiring T] [AddCommGroup M] [Module R M]
    (e : T ≃+* S) (Q : M ≃ₗ[R] M) (ρ : S →+* Module.End R M) :
    T →+* Module.End R M :=
  (Q.conjRingEquiv.toRingHom).comp (ρ.comp e.toRingHom)

/-- The scalar action of `S` on `M` as a ring homomorphism `S →+* End_R M`. -/
public def moduleActionRingHom (S M : Type*) [Semiring S] [AddCommGroup M]
    [Module R M] [Module S M] [SMulCommClass R S M] :
    S →+* Module.End R M where
  toFun s :=
    { toFun := fun x => s • x
      map_add' := fun x y => smul_add s x y
      map_smul' := fun r x => (smul_comm r s x).symm }
  map_one' := by ext x; exact one_smul S x
  map_mul' s t := by ext x; exact mul_smul s t x
  map_zero' := by ext x; exact zero_smul S x
  map_add' s t := by ext x; exact add_smul s t x

/-- The ring isomorphism from the graded opposite algebra to the ordinary opposite ring of `A`,
given on homogeneous elements by the quadratic Koszul sign twist. -/
public noncomputable def gradedOppositeRingEquiv (R : Type u) [CommRing R]
    (A : DifferentialGradedAlgebra.{u, v} R) :
    (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra.A ≃+* MulOpposite A.A := by
  let B := (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra
  let Q := gradedSignTwist R B.A B.grading
  have hQ := gradedSignTwist_involutive R B.A B.grading
  refine
    { toFun := fun x => MulOpposite.op ((DifferentialGradedAlgebra.opposite R A).equiv (Q x))
      invFun := fun x => Q ((DifferentialGradedAlgebra.opposite R A).equiv.symm x.unop)
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      map_add' := ?_ }
  · intro x
    change Q ((DifferentialGradedAlgebra.opposite R A).equiv.symm
      ((DifferentialGradedAlgebra.opposite R A).equiv (Q x))) = x
    rw [LinearEquiv.symm_apply_apply]
    exact hQ x
  · intro x
    change MulOpposite.op ((DifferentialGradedAlgebra.opposite R A).equiv
      (Q (Q ((DifferentialGradedAlgebra.opposite R A).equiv.symm x.unop)))) = x
    rw [hQ, LinearEquiv.apply_symm_apply]
    simp
  · intro x y
    induction x using DirectSum.Decomposition.inductionOn B.grading with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add, MulOpposite.op_add, add_mul, hx, hy]
    | @homogeneous m x =>
      induction y using DirectSum.Decomposition.inductionOn B.grading with
      | zero => simp
      | add y z hy hz =>
        simp only [map_add, MulOpposite.op_add, mul_add, hy, hz]
      | @homogeneous n y =>
        have hxy : (x : B.A) * (y : B.A) ∈ B.grading (m + n) :=
          SetLike.mul_mem_graded x.property y.property
        rw [gradedSignTwist_apply_mem R B.A B.grading hxy,
          gradedSignTwist_apply_mem R B.A B.grading x.property,
          gradedSignTwist_apply_mem R B.A B.grading y.property]
        apply congrArg MulOpposite.op
        rw [map_smul, (DifferentialGradedAlgebra.opposite R A).map_mul_of_mem m n x y
          x.property y.property]
        have hsign : ((koszulQuadraticSign (m + n) : ℤ) : R) *
            ((m * n).negOnePow : ℤ) =
              ((koszulQuadraticSign m : ℤ) : R) *
                ((koszulQuadraticSign n : ℤ) : R) := by
          rw [← Int.cast_mul, ← Int.cast_mul]
          exact congrArg (Int.cast : ℤ → R)
            (congrArg Units.val (koszulQuadraticSign_mul_add m n))
        simp only [MulOpposite.unop_op, LinearEquiv.map_smul]
        rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R (m * n).negOnePow.val
          ((DifferentialGradedAlgebra.opposite R A).equiv y *
            (DifferentialGradedAlgebra.opposite R A).equiv x),
          smul_smul, hsign, smul_mul_smul_comm]
        simp [mul_comm]
  · intro x y
    simp only [map_add, MulOpposite.op_add]

/-- The ring isomorphism from the opposite ring of the graded opposite algebra to `A`, induced by
`gradedOppositeRingEquiv`. -/
public noncomputable def gradedOppositeModuleRingEquiv (R : Type u) [CommRing R]
    (A : DifferentialGradedAlgebra.{u, v} R) :
    MulOpposite (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra.A ≃+* A.A :=
  (RingEquiv.op (gradedOppositeRingEquiv R A)).trans (RingEquiv.opOp A.A).symm

/-- The right action of the graded opposite algebra on a left module `M`: the left action of `A`
transported along `gradedOppositeModuleRingEquiv` and conjugated by the sign twist of `M`. -/
public noncomputable def leftToRightAction (M : LeftModule A) :
    MulOpposite (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra.A →+*
      Module.End R M.M := by
  letI : Semiring A.A := A.ring.toSemiring
  exact conjugatedModuleAction (gradedOppositeModuleRingEquiv R A)
    (gradedSignTwistEquiv R M.M M.grading) (moduleActionRingHom A.A M.M)

/-- The left action of `A` on a right module `M` over the graded opposite algebra: the right action
transported along `gradedOppositeModuleRingEquiv` and conjugated by the sign twist of `M`. -/
public noncomputable def rightToLeftAction
    (M : DifferentialGradedModule
      (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra) :
    A.A →+* Module.End R M.M := by
  let B := (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra
  letI : Semiring (MulOpposite B.A) := inferInstance
  exact conjugatedModuleAction (gradedOppositeModuleRingEquiv R A).symm
    (gradedSignTwistEquiv R M.M M.grading)
    (moduleActionRingHom (MulOpposite B.A) M.M)

private lemma gradedOppositeModuleRingEquiv_algebraMap (r : R) :
    gradedOppositeModuleRingEquiv R A
      (algebraMap R
        (MulOpposite (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra.A) r) =
      algebraMap R A.A r := by
  let B := (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra
  have h0 : (algebraMap R B.A r) ∈ B.grading 0 := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (B.grading 0).smul_mem _ (SetLike.one_mem_graded B.grading)
  change (DifferentialGradedAlgebra.opposite R A).equiv
    (gradedSignTwist R B.A B.grading (algebraMap R B.A r)) = algebraMap R A.A r
  rw [gradedSignTwist_apply_mem R B.A B.grading h0]
  calc
    (DifferentialGradedAlgebra.opposite R A).equiv
        (((koszulQuadraticSign 0 : ℤ) : R) • (algebraMap R B.A r)) =
        ((koszulQuadraticSign 0 : ℤ) : R) •
          (DifferentialGradedAlgebra.opposite R A).equiv (algebraMap R B.A r) :=
            (DifferentialGradedAlgebra.opposite R A).equiv.map_smul _ _
    _ = (DifferentialGradedAlgebra.opposite R A).equiv (algebraMap R B.A r) := by
      simp [koszulQuadraticSign]
    _ = _ := by
      rw [Algebra.algebraMap_eq_smul_one, (DifferentialGradedAlgebra.opposite R A).equiv.map_smul,
        DifferentialGradedAlgebra.Opposite.map_one, Algebra.algebraMap_eq_smul_one]

private lemma leftToRight_smul_def (M : LeftModule A)
    (s : MulOpposite (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra.A)
    (x : M.M) :
    (Module.compHom M.M (leftToRightAction (R := R) (A := A) M)).smul s x =
      gradedSignTwistEquiv R M.M M.grading
        ((gradedOppositeModuleRingEquiv R A s) • gradedSignTwistEquiv R M.M M.grading x) := by
  rfl

private lemma rightToLeft_smul_def
    (M : DifferentialGradedModule
      (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra) (a : A.A) (x : M.M) :
    (Module.compHom M.M (rightToLeftAction (R := R) (A := A) M)).smul a x =
      gradedSignTwistEquiv R M.M M.grading
        ((gradedOppositeModuleRingEquiv R A).symm a • gradedSignTwistEquiv R M.M M.grading x) := by
  rfl

/-- Scalars of `R` act through `leftToRightAction` by the original `R`-module structure. -/
public lemma leftToRight_base_smul (M : LeftModule A) (r : R) (x : M.M) :
    (leftToRightAction (R := R) (A := A) M
      (algebraMap R
        (MulOpposite (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra.A) r)) x =
        r • x := by
  change (Module.compHom M.M (leftToRightAction (R := R) (A := A) M)).smul _ _ = _
  rw [leftToRight_smul_def, gradedOppositeModuleRingEquiv_algebraMap, algebraMap_smul, map_smul]
  exact congrArg (fun y => r • y) (gradedSignTwist_involutive R M.M M.grading x)

/-- Scalars of `R` act through `rightToLeftAction` by the original `R`-module structure. -/
public lemma rightToLeft_base_smul
    (M : DifferentialGradedModule
      (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra) (r : R) (x : M.M) :
    (rightToLeftAction (R := R) (A := A) M (algebraMap R A.A r)) x = r • x := by
  change (Module.compHom M.M (rightToLeftAction (R := R) (A := A) M)).smul _ _ = _
  rw [rightToLeft_smul_def]
  have hbase : (gradedOppositeModuleRingEquiv R A).symm (algebraMap R A.A r) =
      algebraMap R
        (MulOpposite (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra.A)
        r := by
    apply (gradedOppositeModuleRingEquiv R A).injective
    simpa using (gradedOppositeModuleRingEquiv_algebraMap (R := R) (A := A) r).symm
  rw [hbase, algebraMap_smul]
  change gradedSignTwist R M.M M.grading
      (r • gradedSignTwist R M.M M.grading x) = r • x
  rw [map_smul]
  exact congrArg (fun y => r • y) (gradedSignTwist_involutive R M.M M.grading x)

private lemma gradedOppositeModuleRingEquiv_op_mem
    {m : ℤ} {a : (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra.A}
    (ha : a ∈ (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra.grading m) :
    gradedOppositeModuleRingEquiv R A (MulOpposite.op a) =
      ((koszulQuadraticSign m : ℤ) : R) • (DifferentialGradedAlgebra.opposite R A).equiv a := by
  let B := (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra
  change (DifferentialGradedAlgebra.opposite R A).equiv (gradedSignTwist R B.A B.grading a) = _
  rw [gradedSignTwist_apply_mem R B.A B.grading ha, LinearEquiv.map_smul]

/-- The product of the quadratic Koszul signs of `m`, `n` and `m + n` is `(-1)^{mn}`. -/
private lemma koszulQuadraticSign_cast_mul_prod (m n : ℤ) :
    ((koszulQuadraticSign m : ℤ) : R) * ((koszulQuadraticSign n : ℤ) : R) *
      ((koszulQuadraticSign (m + n) : ℤ) : R) = ((m * n).negOnePow : ℤ) := by
  simpa only [Units.val_mul, Int.cast_mul] using
    intCast_units_mul (S := R) (koszulQuadraticSign_mul_prod m n)

/-- Scalars pulled out of both sides of a product `(c • y) • (d • x)`. -/
private lemma smul_smul_smul_eq_mul_smul {S M : Type*} [AddCommGroup M] [Module R M] [SMul R S]
    [SMul S M] [IsScalarTower R S M] [SMulCommClass R S M] (c d : R) (y : S) (x : M) :
    (c • y) • (d • x) = (c * d) • (y • x) := by
  rw [smul_assoc, ← smul_comm d y x, smul_smul]

/-- The equivalence of the graded opposite preserves degrees. -/
private lemma opposite_equiv_symm_mem {m : ℤ} {a : A.A} (ha : a ∈ A.grading m) :
    (DifferentialGradedAlgebra.opposite R A).equiv.symm a ∈
      (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra.grading m := by
  rw [DifferentialGradedAlgebra.Opposite.mem_grading_iff]
  simpa using ha

/-- For `a` of degree `m` in the graded opposite algebra and `x` of degree `n`, the transported
right action of `a` on `x` is `(-1)^{mn}` times the left action of the corresponding element of
`A`. -/
public lemma leftToRightAction_apply_mem (M : LeftModule A)
    {m n : ℤ} {a : (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra.A}
    {x : M.M}
    (ha : a ∈ (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra.grading m)
    (hx : x ∈ M.grading n) :
    (leftToRightAction (R := R) (A := A) M (MulOpposite.op a)) x =
      (m * n).negOnePow • ((DifferentialGradedAlgebra.opposite R A).equiv a • x) := by
  change (Module.compHom M.M (leftToRightAction (R := R) (A := A) M)).smul
    (MulOpposite.op a) x = _
  rw [leftToRight_smul_def, gradedOppositeModuleRingEquiv_op_mem ha,
    gradedSignTwistEquiv_apply_mem R M.M M.grading hx]
  have hax : (DifferentialGradedAlgebra.opposite R A).equiv a • x ∈ M.grading (m + n) :=
    M.smul_mem m n _ _ (by simpa using ha) hx
  rw [smul_smul_smul_eq_mul_smul, map_smul,
    gradedSignTwistEquiv_apply_mem R M.M M.grading hax, smul_smul,
    koszulQuadraticSign_cast_mul_prod, units_smul_eq_intCast_smul (R := R)]

/-- For `a` of degree `m` in `A` and `x` of degree `n`, the transported left action of `a` on
`x` is `(-1)^{mn}` times the right action of the corresponding element of the graded opposite
algebra. -/
public lemma rightToLeftAction_apply_mem
    (M : DifferentialGradedModule
      (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra)
    {m n : ℤ} {a : A.A} {x : M.M} (ha : a ∈ A.grading m) (hx : x ∈ M.grading n) :
    (rightToLeftAction (R := R) (A := A) M a) x =
      (m * n).negOnePow •
        (MulOpposite.op ((DifferentialGradedAlgebra.opposite R A).equiv.symm a) • x) := by
  let B := (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra
  let b := (DifferentialGradedAlgebra.opposite R A).equiv.symm a
  have hb : b ∈ B.grading m := opposite_equiv_symm_mem ha
  have hscaled : ((koszulQuadraticSign m : ℤ) : R) • b ∈ B.grading m :=
    (B.grading m).smul_mem _ hb
  have hinv : (gradedOppositeModuleRingEquiv R A).symm a =
      MulOpposite.op (((koszulQuadraticSign m : ℤ) : R) • b) := by
    apply (gradedOppositeModuleRingEquiv R A).injective
    rw [RingEquiv.apply_symm_apply, gradedOppositeModuleRingEquiv_op_mem hscaled]
    rw [LinearEquiv.map_smul]
    rw [smul_smul, intCast_units_mul (koszulQuadraticSign_square m), Units.val_one, Int.cast_one,
      one_smul]
    simp [b]
  change (Module.compHom M.M (rightToLeftAction (R := R) (A := A) M)).smul a x = _
  rw [rightToLeft_smul_def, hinv, gradedSignTwistEquiv_apply_mem R M.M M.grading hx]
  have hbx : (MulOpposite.op b) • x ∈ M.grading (m + n) := by
    simpa [add_comm] using M.smul_mem n m x b hx hb
  rw [show MulOpposite.op (((koszulQuadraticSign m : ℤ) : R) • b) =
      ((koszulQuadraticSign m : ℤ) : R) • MulOpposite.op b by rfl,
    smul_smul_smul_eq_mul_smul, map_smul,
    gradedSignTwistEquiv_apply_mem R M.M M.grading hbx, smul_smul,
    koszulQuadraticSign_cast_mul_prod, units_smul_eq_intCast_smul (R := R)]

/-- A left module over `A`, viewed as a right module over the graded opposite algebra. -/
@[implicit_reducible] public noncomputable def leftToRightObject (M : LeftModule A) :
    DifferentialGradedModule
      (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra := by
  let B := (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra
  letI : Module (MulOpposite B.A) M.M := Module.compHom M.M (leftToRightAction M)
  letI : IsScalarTower R (MulOpposite B.A) M.M :=
    IsScalarTower.of_algebraMap_smul fun r x => leftToRight_base_smul M r x
  refine
    { M := M.M
      grading := M.grading
      decomposition := M.decomposition
      smul_mem := ?_
      d := M.d
      d_comp_d := M.d_comp_d
      d_mem := M.d_mem
      leibniz := ?_ }
  · intro n m x a hx ha
    change (leftToRightAction M (MulOpposite.op a)) x ∈ M.grading (n + m)
    rw [leftToRightAction_apply_mem M (m := m) (n := n) ha hx, Units.smul_def]
    simpa [add_comm] using
      zsmul_mem (M.smul_mem m n _ _ (by simpa using ha) hx) _
  · intro n m x a hx ha
    change M.d ((leftToRightAction M (MulOpposite.op a)) x) =
      (leftToRightAction M (MulOpposite.op a)) (M.d x) +
        (n.negOnePow : ℤˣ) •
          ((leftToRightAction M (MulOpposite.op (B.d a))) x)
    have haA : (DifferentialGradedAlgebra.opposite R A).equiv a ∈ A.grading m := by
      simpa using ha
    rw [leftToRightAction_apply_mem M ha hx,
      leftToRightAction_apply_mem M ha (M.d_mem n x hx),
      leftToRightAction_apply_mem M (B.d_mem m a ha) hx]
    rw [Units.smul_def, map_zsmul M.d]
    rw [M.leibniz m n ((DifferentialGradedAlgebra.opposite R A).equiv a) x haA hx]
    rw [(DifferentialGradedAlgebra.opposite R A).map_d a]
    simp only [Units.smul_def, smul_add, smul_smul]
    have hA : (m * n).negOnePow.val * m.negOnePow.val =
        (m * (n + 1)).negOnePow.val :=
      congrArg Units.val (intNegOnePow_mul_succ m n)
    have hB : n.negOnePow.val * ((m + 1) * n).negOnePow.val =
        (m * n).negOnePow.val :=
      congrArg Units.val (intNegOnePow_diff_succ m n)
    rw [hA, hB, add_comm]

/-- A right module over the graded opposite algebra, viewed as a left module over `A`. -/
@[implicit_reducible] public noncomputable def rightToLeftObject
    (M : DifferentialGradedModule
      (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra) : LeftModule A := by
  let B := (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra
  let _ : Module A.A M.M := Module.compHom M.M (rightToLeftAction M)
  letI : IsScalarTower R A.A M.M :=
    IsScalarTower.of_algebraMap_smul fun r x => rightToLeft_base_smul M r x
  refine
    { M := M.M
      grading := M.grading
      decomposition := M.decomposition
      smul_mem := ?_
      d := M.d
      d_comp_d := M.d_comp_d
      d_mem := M.d_mem
      leibniz := ?_ }
  · intro m n a x ha hx
    change (rightToLeftAction M a) x ∈ M.grading (m + n)
    rw [rightToLeftAction_apply_mem M ha hx, Units.smul_def]
    simpa [add_comm] using zsmul_mem (M.smul_mem n m x
      ((DifferentialGradedAlgebra.opposite R A).equiv.symm a) hx (by simpa using ha)) _
  · intro m n a x ha hx
    let b := (DifferentialGradedAlgebra.opposite R A).equiv.symm a
    have hb : b ∈ B.grading m := by
      rw [DifferentialGradedAlgebra.Opposite.mem_grading_iff]
      simpa [b] using ha
    have hdb : B.d b = (DifferentialGradedAlgebra.opposite R A).equiv.symm (A.d a) := by
      apply (DifferentialGradedAlgebra.opposite R A).equiv.injective
      rw [DifferentialGradedAlgebra.Opposite.map_d]
      simp [b]
    change M.d ((rightToLeftAction M a) x) =
      (rightToLeftAction M (A.d a)) x +
        (m.negOnePow : ℤˣ) • ((rightToLeftAction M a) (M.d x))
    rw [rightToLeftAction_apply_mem M ha hx,
      rightToLeftAction_apply_mem M (A.d_mem m a ha) hx,
      rightToLeftAction_apply_mem M ha (M.d_mem n x hx)]
    rw [Units.smul_def, map_zsmul M.d]
    rw [M.leibniz_apply n x hx b]
    rw [hdb]
    simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul R, smul_add, smul_smul]
    have h₁ : (m * n).negOnePow * n.negOnePow = ((m + 1) * n).negOnePow := by
      rw [← Int.negOnePow_add]
      exact congrArg Int.negOnePow (by ring : m * n + n = (m + 1) * n)
    have h₂ : m.negOnePow * (m * (n + 1)).negOnePow = (m * n).negOnePow := by
      calc
        m.negOnePow * (m * (n + 1)).negOnePow =
            m.negOnePow * ((m * n).negOnePow * m.negOnePow) := by
              rw [intNegOnePow_mul_succ]
        _ = (m * n).negOnePow * (m.negOnePow * m.negOnePow) := by ac_rfl
        _ = (m * n).negOnePow := by rw [intNegOnePow_square, mul_one]
    have h₁R : ((m * n).negOnePow.val : R) * (n.negOnePow.val : R) =
        (((m + 1) * n).negOnePow.val : R) := by
      rw [← Int.cast_mul]
      exact congrArg (Int.cast : ℤ → R) (congrArg Units.val h₁)
    have h₂R : (m.negOnePow.val : R) *
        ((m * (n + 1)).negOnePow.val : R) = ((m * n).negOnePow.val : R) := by
      rw [← Int.cast_mul]
      exact congrArg (Int.cast : ℤ → R) (congrArg Units.val h₂)
    rw [h₁R, h₂R]
    dsimp only [b]
    rw [add_comm]

private lemma gradedSignTwistEquiv_natural {M N : Type w}
    [AddCommGroup M] [Module R M] (gM : ℤ → Submodule R M)
    [DirectSum.Decomposition gM]
    [AddCommGroup N] [Module R N] (gN : ℤ → Submodule R N)
    [DirectSum.Decomposition gN]
    (f : M →ₗ[R] N)
    (hf : ∀ n x, x ∈ gM n → f x ∈ gN n) (x : M) :
    gradedSignTwistEquiv R N gN (f x) = f (gradedSignTwistEquiv R M gM x) := by
  induction x using DirectSum.Decomposition.inductionOn gM with
  | zero => simp [gradedSignTwistEquiv]
  | @homogeneous n x =>
      rw [gradedSignTwistEquiv_apply_mem R N gN (hf n x x.property),
        gradedSignTwistEquiv_apply_mem R M gM x.property, f.map_smul]
  | add x y hx hy => simp [hx, hy]

/-- The functor from left modules over `A` to right modules over the graded opposite algebra; it is
the identity on underlying linear maps. -/
@[implicit_reducible] public noncomputable def leftToRightFunctor :
    LeftModule A ⥤ DifferentialGradedModule
      (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra where
  obj := leftToRightObject
  map {M N} f :=
    { toFun := f.toFun
      map_smul := by
        intro x a
        change f.toFun (gradedSignTwistEquiv R M.M M.grading
            (gradedOppositeModuleRingEquiv R A (MulOpposite.op a) •
              gradedSignTwistEquiv R M.M M.grading x)) =
          gradedSignTwistEquiv R N.M N.grading
            (gradedOppositeModuleRingEquiv R A (MulOpposite.op a) •
              gradedSignTwistEquiv R N.M N.grading (f.toFun x))
        calc
          _ = gradedSignTwistEquiv R N.M N.grading
              (f.toFun (gradedOppositeModuleRingEquiv R A (MulOpposite.op a) •
                gradedSignTwistEquiv R M.M M.grading x)) := by
                  symm
                  exact gradedSignTwistEquiv_natural (gM := M.grading)
                    (gN := N.grading) f.toFun f.map_grading _
          _ = gradedSignTwistEquiv R N.M N.grading
              (gradedOppositeModuleRingEquiv R A (MulOpposite.op a) •
                f.toFun (gradedSignTwistEquiv R M.M M.grading x)) := by
                  rw [f.map_smul]
          _ = _ :=
            congrArg (gradedSignTwistEquiv R N.M N.grading)
              (congrArg (fun y =>
                gradedOppositeModuleRingEquiv R A (MulOpposite.op a) • y)
                (gradedSignTwistEquiv_natural (gM := M.grading)
                  (gN := N.grading) f.toFun f.map_grading x).symm)
      map_grading := f.map_grading
      map_d := f.map_d }
  map_id := by intro M; apply DifferentialGradedModule.Hom.ext; rfl
  map_comp := by intro M N P f g; apply DifferentialGradedModule.Hom.ext; rfl

/-- The functor from right modules over the graded opposite algebra to left modules over `A`; it is
the identity on underlying linear maps. -/
@[implicit_reducible] public noncomputable def rightToLeftFunctor :
    DifferentialGradedModule
      (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra ⥤
      LeftModule A where
  obj := rightToLeftObject
  map {M N} f :=
    { toFun := f.toFun
      map_smul := by
        intro a x
        change f.toFun (gradedSignTwistEquiv R M.M M.grading
            ((gradedOppositeModuleRingEquiv R A).symm a •
              gradedSignTwistEquiv R M.M M.grading x)) =
          gradedSignTwistEquiv R N.M N.grading
            ((gradedOppositeModuleRingEquiv R A).symm a •
              gradedSignTwistEquiv R N.M N.grading (f.toFun x))
        calc
          _ = gradedSignTwistEquiv R N.M N.grading
              (f.toFun ((gradedOppositeModuleRingEquiv R A).symm a •
                gradedSignTwistEquiv R M.M M.grading x)) := by
                  symm
                  exact gradedSignTwistEquiv_natural (gM := M.grading)
                    (gN := N.grading) f.toFun f.map_grading _
          _ = gradedSignTwistEquiv R N.M N.grading
              ((gradedOppositeModuleRingEquiv R A).symm a •
                f.toFun (gradedSignTwistEquiv R M.M M.grading x)) := by
                  congr 1
                  simpa only [MulOpposite.op_unop] using
                    f.map_smul _ (MulOpposite.unop
                      ((gradedOppositeModuleRingEquiv R A).symm a))
          _ = _ :=
            congrArg (gradedSignTwistEquiv R N.M N.grading)
              (congrArg (fun y => (gradedOppositeModuleRingEquiv R A).symm a • y)
                (gradedSignTwistEquiv_natural (gM := M.grading)
                  (gN := N.grading) f.toFun f.map_grading x).symm)
      map_grading := f.map_grading
      map_d := f.map_d }
  map_id := by intro M; apply LeftModule.Hom.ext; rfl
  map_comp := by intro M N P f g; apply LeftModule.Hom.ext; rfl

private lemma rightToLeft_leftToRight_action (M : LeftModule A)
    (a : A.A) (x : M.M) :
    (rightToLeftAction (R := R) (A := A) (leftToRightObject (R := R) (A := A) M) a) x =
      a • x := by
  let B := (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra
  let _ : Module (MulOpposite B.A) M.M :=
    Module.compHom M.M (leftToRightAction M)
  change gradedSignTwistEquiv R M.M M.grading
    ((gradedOppositeModuleRingEquiv R A).symm a •
      gradedSignTwistEquiv R M.M M.grading x) = a • x
  have hF := leftToRight_smul_def (R := R) (A := A) M
    ((gradedOppositeModuleRingEquiv R A).symm a)
    (gradedSignTwistEquiv R M.M M.grading x)
  simp only [RingEquiv.apply_symm_apply] at hF
  have hQ : Function.Involutive (gradedSignTwistEquiv R M.M M.grading) :=
    gradedSignTwist_involutive R M.M M.grading
  refine (congrArg (gradedSignTwistEquiv R M.M M.grading) hF).trans ?_
  rw [hQ, hQ]

private lemma leftToRight_rightToLeft_action
    (M : DifferentialGradedModule
      (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra)
    (s : MulOpposite (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra.A)
    (x : M.M) :
    (leftToRightAction (R := R) (A := A) (rightToLeftObject (R := R) (A := A) M) s) x =
      s • x := by
  let _ : Module A.A M.M := Module.compHom M.M (rightToLeftAction M)
  change gradedSignTwistEquiv R M.M M.grading
    ((gradedOppositeModuleRingEquiv R A) s •
      gradedSignTwistEquiv R M.M M.grading x) = s • x
  have hG := rightToLeft_smul_def (R := R) (A := A) M
    ((gradedOppositeModuleRingEquiv R A) s)
    (gradedSignTwistEquiv R M.M M.grading x)
  simp only [RingEquiv.symm_apply_apply] at hG
  have hQ : Function.Involutive (gradedSignTwistEquiv R M.M M.grading) :=
    gradedSignTwist_involutive R M.M M.grading
  refine (congrArg (gradedSignTwistEquiv R M.M M.grading) hG).trans ?_
  rw [hQ, hQ]

/-- The unit isomorphism of the equivalence, given by the identity map of the underlying module. -/
public noncomputable def leftRightUnitIso (M : LeftModule A) :
    M ≅ (rightToLeftFunctor (R := R) (A := A)).obj
      ((leftToRightFunctor (R := R) (A := A)).obj M) where
  hom :=
    { toFun := LinearMap.id
      map_smul := by
        intro a x
        dsimp [LinearMap.id]
        exact (rightToLeft_leftToRight_action (R := R) (A := A) M a x).symm
      map_grading := fun _ _ hx => hx
      map_d := rfl }
  inv :=
    { toFun := LinearMap.id
      map_smul := by
        intro a x
        dsimp [LinearMap.id]
        exact rightToLeft_leftToRight_action (R := R) (A := A) M a x
      map_grading := fun _ _ hx => hx
      map_d := rfl }
  hom_inv_id := by apply LeftModule.Hom.ext; rfl
  inv_hom_id := by apply LeftModule.Hom.ext; rfl

/-- The counit isomorphism of the equivalence, given by the identity map of the underlying
module. -/
public noncomputable def leftRightCounitIso
    (M : DifferentialGradedModule
      (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra) :
    ((rightToLeftFunctor (R := R) (A := A) ⋙
      leftToRightFunctor (R := R) (A := A)).obj M) ≅ M where
  hom :=
    { toFun := LinearMap.id
      map_smul := by
        intro x a
        dsimp [LinearMap.id]
        exact leftToRight_rightToLeft_action (R := R) (A := A) M
          (MulOpposite.op a) x
      map_grading := fun _ _ hx => hx
      map_d := rfl }
  inv :=
    { toFun := LinearMap.id
      map_smul := by
        intro x a
        dsimp [LinearMap.id]
        exact (leftToRight_rightToLeft_action (R := R) (A := A) M
          (MulOpposite.op a) x).symm
      map_grading := fun _ _ hx => hx
      map_d := rfl }
  hom_inv_id := by apply DifferentialGradedModule.Hom.ext; rfl
  inv_hom_id := by apply DifferentialGradedModule.Hom.ext; rfl

/-- Graded opposition is an equivalence from left differential graded `A`-modules to
right differential graded modules over the graded opposite algebra. -/
@[stacks 0FQ0]
public noncomputable def leftRightEquivalence (R : Type u) [CommRing R]
    (A : DifferentialGradedAlgebra.{u, v} R) : OppositeEquivalence R A := by
  let E : LeftModule A ≌
      DifferentialGradedModule
        (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra := by
    refine
      { functor := leftToRightFunctor (R := R) (A := A)
        inverse := rightToLeftFunctor (R := R) (A := A)
        unitIso := NatIso.ofComponents
          (fun M => leftRightUnitIso (R := R) (A := A) M) ?_
        counitIso := NatIso.ofComponents
          (fun M => leftRightCounitIso (R := R) (A := A) M) ?_
        functor_unitIso_comp := ?_ }
    · intro M N f
      apply LeftModule.Hom.ext
      rfl
    · intro M N f
      apply DifferentialGradedModule.Hom.ext
      rfl
    · intro M
      apply DifferentialGradedModule.Hom.ext
      rfl
  refine
    { equivalence := E
      underlying := fun M => by
        dsimp [E, leftToRightFunctor, leftToRightObject]
        exact LinearEquiv.refl R M.M
      grading := ?_
      differential := ?_
      naturality := ?_
      action := ?_ }
  · intro M n x
    rfl
  · intro M x
    rfl
  · intro M N f x
    rfl
  · intro M m n a x ha hx
    dsimp [E, leftToRightFunctor, leftToRightObject]
    exact leftToRightAction_apply_mem M ha hx

end DifferentialGraded
