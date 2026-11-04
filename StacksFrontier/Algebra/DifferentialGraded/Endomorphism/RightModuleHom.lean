module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.Basic
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.LeftModule
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.OppositeHom
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.TotalComplex
public import StacksFrontier.Algebra.DifferentialGraded.LeftModule

/-!
# Right modules on a complex versus homomorphisms into the opposite endomorphism algebra

Let `R` be a commutative ring, `A` a differential graded `R`-algebra and `M` a cochain complex of
`R`-modules. A right differential graded `A`-module structure on `M` is the same thing as a
homomorphism of differential graded algebras from `A` into the graded opposite of the endomorphism
differential graded algebra of `M`. On homogeneous elements the correspondence is the signed
formula `x · a = (-1)^{|a||x|} φ(a)(x)`, which is the content of
`DifferentialGradedModule.IsSignedAction`.

## Main definitions

* `DifferentialGradedModule.IsSignedAction`: the signed-action equation relating a homomorphism
  into the opposite endomorphism algebra to a right module structure.

## Main results

* `DifferentialGradedModule.existsUnique_isSignedAction`: a right differential graded module whose
  underlying complex is identified with `M` determines a unique such homomorphism.
* `DifferentialGradedModule.exists_rightModule_isSignedAction`: every such homomorphism arises
  from a right differential graded module whose underlying complex is `M`.

## References

* [Stacks Project, Tag 0FQ5](https://stacks.math.columbia.edu/tag/0FQ5)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex
open scoped DirectSum

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R]

/-- The graded opposite datum of the endomorphism differential graded algebra of `M`. -/
noncomputable abbrev oppEndOpposite (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    DifferentialGradedAlgebra.Opposite R (endomorphismDGA M).algebra :=
  DifferentialGradedAlgebra.opposite R (endomorphismDGA M).algebra

/-- The graded opposite of the endomorphism differential graded algebra of `M`. -/
noncomputable abbrev oppEndAlgebra (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    DifferentialGradedAlgebra R :=
  (oppEndOpposite M).toDifferentialGradedAlgebra

/-- The signed-action equation: a homomorphism `τ` from `A` into the graded opposite of the
endomorphism algebra of `M` acts on a homogeneous element `x` of degree `p` of a right differential
graded module `L` identified with `M` by `(-1)^{np} x a`. -/
def IsSignedAction (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (L : DifferentialGradedModule A)
    (i : L.toCochainComplex ≅ M) (τ : A.Hom (oppEndAlgebra M)) : Prop :=
  ∀ (n p : ℤ) (a : A.grading n) (x : L.grading p),
    ((endomorphismDGA M).cochainEquiv n
      ⟨(oppEndOpposite M).equiv (τ.toAlgebraHom a),
        ((oppEndOpposite M).mem_grading_iff n (τ.toAlgebraHom a)).mp
          (τ.map_grading n a a.property)⟩).v p (p + n) (by omega) (i.hom.f p x) =
      (n * p).negOnePow • i.hom.f (p + n)
        (⟨MulOpposite.op (a : A.A) • (x : L.M),
          L.smul_mem p n (x : L.M) (a : A.A) x.property a.property⟩ : L.grading (p + n))

/-- The cochain of `M` attached to a homogeneous element of `A` by `τ`. -/
noncomputable def oppEndCochain (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) (n : ℤ)
    (a : A.grading n) : Cochain M M n :=
  (endomorphismDGA M).cochainEquiv n
    ⟨(oppEndOpposite M).equiv (τ.toAlgebraHom a),
      ((oppEndOpposite M).mem_grading_iff n (τ.toAlgebraHom a)).mp
        (τ.map_grading n a a.property)⟩

/-- `oppEndCochain` is `R`-linear in the homogeneous element. -/
noncomputable def oppEndCochainLinear (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) (n : ℤ) :
    A.grading n →ₗ[R] Cochain M M n where
  toFun := oppEndCochain A M τ n
  map_add' a b := by
    have hs : (⟨(oppEndOpposite M).equiv (τ.toAlgebraHom (a + b)),
        ((oppEndOpposite M).mem_grading_iff n (τ.toAlgebraHom (a + b))).mp
          (τ.map_grading n (a + b) (a + b).property)⟩ :
          (endomorphismDGA M).algebra.grading n) =
        (⟨(oppEndOpposite M).equiv (τ.toAlgebraHom a),
          ((oppEndOpposite M).mem_grading_iff n (τ.toAlgebraHom a)).mp
            (τ.map_grading n a a.property)⟩ : (endomorphismDGA M).algebra.grading n) +
        ⟨(oppEndOpposite M).equiv (τ.toAlgebraHom b),
          ((oppEndOpposite M).mem_grading_iff n (τ.toAlgebraHom b)).mp
            (τ.map_grading n b b.property)⟩ := by
      apply Subtype.ext
      simp
    have h := congrArg ((endomorphismDGA M).cochainEquiv n) hs
    conv_rhs at h => rw [map_add]
    exact h
  map_smul' r a := by
    have hs : (⟨(oppEndOpposite M).equiv (τ.toAlgebraHom (r • a)),
        ((oppEndOpposite M).mem_grading_iff n (τ.toAlgebraHom (r • a))).mp
          (τ.map_grading n (r • a) (r • a).property)⟩ :
          (endomorphismDGA M).algebra.grading n) =
        r • (⟨(oppEndOpposite M).equiv (τ.toAlgebraHom a),
          ((oppEndOpposite M).mem_grading_iff n (τ.toAlgebraHom a)).mp
            (τ.map_grading n a a.property)⟩ : (endomorphismDGA M).algebra.grading n) := by
      apply Subtype.ext
      simp
    have h := congrArg ((endomorphismDGA M).cochainEquiv n) hs
    conv_rhs at h => rw [map_smul]
    exact h

/-- The signed right action of a homogeneous element of `A` on the total module of `M`. -/
noncomputable def oppEndAction (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) (n : ℤ)
    (a : A.grading n) : totalModule M →ₗ[R] totalModule M :=
  signedTotalCochain M n (oppEndCochain A M τ n a)

/-- The signed action of `a` of degree `n` on the image of `x : M.X p` in the total module is
the image in degree `p + n` of `(-1)^{np}` times the cochain of `a` applied to `x`. -/
theorem oppEndAction_lof (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) (n p : ℤ)
    (a : A.grading n) (x : M.X p) :
    oppEndAction A M τ n a (DirectSum.lof R ℤ (fun q => M.X q) p x) =
      DirectSum.lof R ℤ (fun q => M.X q) (p + n)
        ((((n * p).negOnePow.val : ℤ) : R) •
          (((oppEndCochain A M τ n a).v p (p + n) (by omega)).hom x)) :=
  signedTotalCochain_lof M n p (oppEndCochain A M τ n a) x

/-- `oppEndAction_lof`, with the target degree `q = p + n` given separately. -/
theorem oppEndAction_lof_of_eq (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) (n p q : ℤ)
    (h : p + n = q) (a : A.grading n) (x : M.X p) :
    oppEndAction A M τ n a (DirectSum.lof R ℤ (fun j => M.X j) p x) =
      DirectSum.lof R ℤ (fun j => M.X j) q
        ((n * p).negOnePow • (oppEndCochain A M τ n a).v p q h x) := by
  subst q
  simpa only [Units.smul_def, Int.cast_smul_eq_zsmul] using oppEndAction_lof A M τ n p a x

/-- The signed right action of `A` on the total module of `M`, as an `R`-linear map. -/
noncomputable def oppEndActionLinear (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) (n : ℤ) :
    A.grading n →ₗ[R] Module.End R (totalModule M) :=
  (signedTotalCochainLinear M n).comp (oppEndCochainLinear A M τ n)

/-- The signed right action of all of `A` on the total module of `M`. -/
noncomputable def oppEndActionTotal (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) :
    A.A →ₗ[R] Module.End R (totalModule M) :=
  (DirectSum.toModule R ℤ (Module.End R (totalModule M)) (oppEndActionLinear A M τ)).comp
    (DirectSum.decomposeLinearEquiv A.grading).toLinearMap

/-- On a homogeneous element of degree `n`, the total action is `oppEndAction` in degree `n`. -/
theorem oppEndActionTotal_apply_of_mem (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) (n : ℤ) (a : A.A)
    (ha : a ∈ A.grading n) :
    oppEndActionTotal A M τ a = oppEndAction A M τ n ⟨a, ha⟩ := by
  have hdecomp : (DirectSum.decomposeLinearEquiv A.grading) a =
      DirectSum.lof R ℤ (fun i => A.grading i) n ⟨a, ha⟩ :=
    DirectSum.decomposeLinearEquiv_apply_coe A.grading n ⟨a, ha⟩
  rw [oppEndActionTotal, LinearMap.comp_apply]
  show DirectSum.toModule R ℤ (Module.End R (totalModule M)) (oppEndActionLinear A M τ)
      ((DirectSum.decomposeLinearEquiv A.grading) a) = _
  rw [hdecomp, DirectSum.toModule_lof, oppEndActionLinear, LinearMap.comp_apply]
  rfl

/-- The cochain of a product `a * b` of homogeneous elements of degrees `n` and `m` is
`(-1)^{nm}` times the composite `(oppEndCochain a).comp (oppEndCochain b)`. -/
theorem oppEndCochain_mul (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) (n m : ℤ)
    (a : A.grading n) (b : A.grading m) :
    oppEndCochain A M τ (m + n)
        ⟨(a : A.A) * (b : A.A), by
          simpa only [add_comm] using SetLike.mul_mem_graded a.property b.property⟩ =
      (((n * m).negOnePow.val : ℤ) : R) •
        ((oppEndCochain A M τ n a).comp (oppEndCochain A M τ m b) (by omega)) := by
  let E := endomorphismDGA M
  let O := oppEndOpposite M
  let oa : (oppEndAlgebra M).grading n := ⟨τ.toAlgebraHom a, τ.map_grading n a a.property⟩
  let ob : (oppEndAlgebra M).grading m := ⟨τ.toAlgebraHom b, τ.map_grading m b b.property⟩
  let ea : E.algebra.grading n := ⟨O.equiv oa, (O.mem_grading_iff n oa).mp oa.property⟩
  let eb : E.algebra.grading m := ⟨O.equiv ob, (O.mem_grading_iff m ob).mp ob.property⟩
  let z : E.algebra.grading (m + n) :=
    ⟨(eb : E.algebra.A) * (ea : E.algebra.A), SetLike.mul_mem_graded eb.property ea.property⟩
  have hs : (⟨O.equiv (τ.toAlgebraHom ((a : A.A) * (b : A.A))),
      (O.mem_grading_iff (m + n) (τ.toAlgebraHom ((a : A.A) * (b : A.A)))).mp
        (τ.map_grading (m + n) ((a : A.A) * (b : A.A))
          (by simpa only [add_comm] using SetLike.mul_mem_graded a.property b.property))⟩ :
        E.algebra.grading (m + n)) = ((n * m).negOnePow : R) • z := by
    apply Subtype.ext
    show O.equiv (τ.toAlgebraHom ((a : A.A) * (b : A.A))) = _
    rw [map_mul]
    simpa [Algebra.smul_def, z, oa, ob, Units.smul_def, Int.coe_negOnePow] using
      O.map_mul_of_mem n m (τ.toAlgebraHom a) (τ.toAlgebraHom b) oa.property ob.property
  have hm : E.cochainEquiv (m + n) z =
      (E.cochainEquiv n ea).comp (E.cochainEquiv m eb) (by omega) :=
    E.map_mul m n eb ea
  show E.cochainEquiv (m + n)
      ⟨O.equiv (τ.toAlgebraHom ((a : A.A) * (b : A.A))),
        (O.mem_grading_iff (m + n) (τ.toAlgebraHom ((a : A.A) * (b : A.A)))).mp
          (τ.map_grading (m + n) ((a : A.A) * (b : A.A))
            (by simpa only [add_comm] using SetLike.mul_mem_graded a.property b.property))⟩ = _
  rw [hs, map_smul, hm]
  rfl

/-- The signed action of a product `a * b` of homogeneous elements is the action of `a` followed
by the action of `b`. -/
theorem oppEndAction_mul (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) (n m : ℤ)
    (a : A.grading n) (b : A.grading m) :
    oppEndAction A M τ (m + n)
        ⟨(a : A.A) * (b : A.A), by
          simpa only [add_comm] using SetLike.mul_mem_graded a.property b.property⟩ =
      oppEndAction A M τ m b ∘ₗ oppEndAction A M τ n a := by
  show signedTotalCochain M (m + n)
      (oppEndCochain A M τ (m + n)
        ⟨(a : A.A) * (b : A.A), by
          simpa only [add_comm] using SetLike.mul_mem_graded a.property b.property⟩) = _
  rw [oppEndCochain_mul, signedTotalCochain_smul, signedTotalCochain_comp]
  have hrR : ((-1 : R) ^ (n * m).natAbs) * ((-1 : R) ^ (n * m).natAbs) = 1 := by
    have hr : (((n * m).negOnePow.val : ℤ) : R) * (((n * m).negOnePow.val : ℤ) : R) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, ← Int.negOnePow_add,
        show n * m + n * m = 2 * (n * m) by ring, Int.negOnePow_two_mul]
      simp
    simpa [Int.coe_negOnePow] using hr
  simp only [Int.coe_negOnePow, smul_smul, hrR, one_smul, oppEndAction]

/-- The total action of `a * b` is the total action of `a` followed by that of `b`. -/
theorem oppEndActionTotal_mul (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) (a b : A.A) :
    oppEndActionTotal A M τ (a * b) =
      oppEndActionTotal A M τ b ∘ₗ oppEndActionTotal A M τ a := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp [oppEndActionTotal]
  | add a a' ha ha' => simp only [add_mul, map_add, ha, ha', LinearMap.comp_add]
  | @homogeneous n a =>
    induction b using DirectSum.Decomposition.inductionOn A.grading with
    | zero => simp [oppEndActionTotal]
    | add b b' hb hb' => simp only [mul_add, map_add, hb, hb', LinearMap.add_comp]
    | @homogeneous m b =>
      have hab : (a : A.A) * (b : A.A) ∈ A.grading (m + n) := by
        simpa only [add_comm] using SetLike.mul_mem_graded a.property b.property
      rw [oppEndActionTotal_apply_of_mem A M τ (m + n) _ hab,
        oppEndActionTotal_apply_of_mem A M τ n a a.property,
        oppEndActionTotal_apply_of_mem A M τ m b b.property]
      exact oppEndAction_mul A M τ n m a b

/-- The total action of `1` is the identity. -/
theorem oppEndActionTotal_one (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) :
    oppEndActionTotal A M τ 1 = 1 := by
  let E := endomorphismDGA M
  let O := oppEndOpposite M
  have h1 : (1 : A.A) ∈ A.grading 0 := SetLike.one_mem_graded A.grading
  have hc : oppEndCochain A M τ 0 ⟨1, h1⟩ = Cochain.ofHom (𝟙 M) := by
    rw [← E.map_one]
    show E.cochainEquiv 0
        ⟨O.equiv (τ.toAlgebraHom 1),
          (O.mem_grading_iff 0 (τ.toAlgebraHom 1)).mp (τ.map_grading 0 1 h1)⟩ =
      E.cochainEquiv 0 ⟨1, SetLike.one_mem_graded E.algebra.grading⟩
    apply congrArg (E.cochainEquiv 0)
    apply Subtype.ext
    simp [O.map_one]
  rw [oppEndActionTotal_apply_of_mem A M τ 0 1 h1]
  show signedTotalCochain M 0 (oppEndCochain A M τ 0 ⟨1, h1⟩) = 1
  rw [hc]
  exact signedTotalCochain_id M

/-- The signed right action, as a ring homomorphism out of the opposite of `A`. -/
noncomputable def oppEndActionRingHom (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) :
    MulOpposite A.A →+* Module.End R (totalModule M) where
  toFun a := oppEndActionTotal A M τ (MulOpposite.unop a)
  map_zero' := map_zero (oppEndActionTotal A M τ)
  map_add' _ _ := map_add (oppEndActionTotal A M τ) _ _
  map_one' := by simpa using oppEndActionTotal_one A M τ
  map_mul' a b := by
    rw [Module.End.mul_eq_comp]
    exact oppEndActionTotal_mul A M τ (MulOpposite.unop b) (MulOpposite.unop a)

/-- The total action of the image of `r : R` in `A` is multiplication by `r`. -/
theorem oppEndActionTotal_algebraMap (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) (r : R) :
    oppEndActionTotal A M τ (algebraMap R A.A r) =
      r • (1 : Module.End R (totalModule M)) := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, oppEndActionTotal_one]

/-- The total action of a homogeneous element of degree `n` carries the degree `p` part of the
total module into the degree `p + n` part. -/
theorem oppEndActionTotal_mem_grading (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) (n p : ℤ)
    (a : A.A) (ha : a ∈ A.grading n) (x : totalGrading M p) :
    oppEndActionTotal A M τ a (x : totalModule M) ∈ totalGrading M (p + n) := by
  rcases x.property with ⟨y, hy⟩
  rw [← hy]
  show oppEndActionTotal A M τ a (DirectSum.lof R ℤ (fun q ↦ M.X q) p y) ∈
    LinearMap.range (DirectSum.lof R ℤ (fun q ↦ M.X q) (p + n))
  rw [oppEndActionTotal_apply_of_mem A M τ n a ha]
  exact ⟨_, (oppEndAction_lof A M τ n p ⟨a, ha⟩ y).symm⟩

/-- The cochain of the differential of a homogeneous element `a` of degree `n` is the
differential `δ n (n + 1)` of the cochain of `a`. -/
theorem oppEndCochain_map_d (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) (n : ℤ)
    (a : A.grading n) :
    oppEndCochain A M τ (n + 1) ⟨A.d a, A.d_mem n (a : A.A) a.property⟩ =
      δ n (n + 1) (oppEndCochain A M τ n a) := by
  let E := endomorphismDGA M
  let O := oppEndOpposite M
  let oa : (oppEndAlgebra M).grading n := ⟨τ.toAlgebraHom a, τ.map_grading n a a.property⟩
  let ea : E.algebra.grading n := ⟨O.equiv oa, (O.mem_grading_iff n _).mp oa.property⟩
  have hs : (⟨O.equiv (τ.toAlgebraHom (A.d (a : A.A))),
      (O.mem_grading_iff (n + 1) _).mp
        (τ.map_grading (n + 1) (A.d (a : A.A)) (A.d_mem n _ a.property))⟩ :
        E.algebra.grading (n + 1)) =
      ⟨E.algebra.d (ea : E.algebra.A), E.algebra.d_mem n _ ea.property⟩ := by
    apply Subtype.ext
    show O.equiv (τ.toAlgebraHom (A.d (a : A.A))) = _
    rw [τ.map_d, O.map_d]
  show E.cochainEquiv (n + 1) ⟨O.equiv (τ.toAlgebraHom (A.d (a : A.A))), _⟩ = _
  rw [congrArg (E.cochainEquiv (n + 1)) hs, E.map_d n ea]
  simp [oppEndCochain, E, O, oa, ea]

/-- The Leibniz rule for the signed action of a homogeneous element `a` of degree `n` on an
element of degree `p` of the total module: `d(x a) = (d x) a + (-1)^p x (d a)`. -/
theorem oppEndAction_leibniz (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) (n p : ℤ)
    (a : A.grading n) (x : M.X p) :
    totalDifferential M
        (oppEndAction A M τ n a (DirectSum.lof R ℤ (fun q => M.X q) p x)) =
      oppEndAction A M τ n a
          (totalDifferential M (DirectSum.lof R ℤ (fun q => M.X q) p x)) +
        (p.negOnePow : R) •
          oppEndAction A M τ (n + 1) ⟨A.d a, A.d_mem n a a.property⟩
            (DirectSum.lof R ℤ (fun q => M.X q) p x) := by
  let f := oppEndCochain A M τ n a
  rw [oppEndAction_lof_of_eq A M τ n p (p + n) rfl, totalDifferential_lof,
    totalDifferential_lof, oppEndAction_lof_of_eq A M τ n (p + 1) (p + n + 1) (by omega),
    oppEndAction_lof_of_eq A M τ (n + 1) p (p + n + 1) (by omega), oppEndCochain_map_d,
    δ_v n (n + 1) rfl f p (p + n + 1) (by omega) (p + n) (p + 1) (by omega) rfl]
  have hs₁ : p.negOnePow * ((n + 1) * p).negOnePow = (n * p).negOnePow := by
    rw [← Int.negOnePow_add, show p + (n + 1) * p = n * p + 2 * p by ring, Int.negOnePow_add,
      Int.negOnePow_two_mul, mul_one]
  have hs₂ : (n * p).negOnePow * (n + 1).negOnePow = -(n * (p + 1)).negOnePow := by
    rw [← Int.negOnePow_add, show n * p + (n + 1) = n * (p + 1) + 1 by ring, Int.negOnePow_add,
      Int.negOnePow_one, mul_neg, mul_one]
  rw [Int.cast_smul_eq_zsmul]
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, Units.smul_def, ModuleCat.hom_zsmul,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_zsmul, smul_add,
    ← mul_smul, ← Units.val_mul, ← mul_assoc, hs₁, hs₂, Units.val_neg, neg_smul, map_add]
  dsimp only [f, ModuleCat.Hom.hom]
  abel

/-- The signed-action equation determines the homomorphism. -/
theorem hom_eq_of_isSignedAction (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (L : DifferentialGradedModule A)
    (i : L.toCochainComplex ≅ M) (τ σ : A.Hom (oppEndAlgebra M))
    (hτ : IsSignedAction A M L i τ) (hσ : IsSignedAction A M L i σ) : τ = σ := by
  have hhomogeneous {n : ℤ} (a : A.grading n) : τ.toAlgebraHom a = σ.toAlgebraHom a := by
    let E := endomorphismDGA M
    let O := oppEndOpposite M
    have hco : E.cochainEquiv n
        ⟨O.equiv (τ.toAlgebraHom a),
          (O.mem_grading_iff n (τ.toAlgebraHom a)).mp (τ.map_grading n a a.property)⟩ =
        E.cochainEquiv n
        ⟨O.equiv (σ.toAlgebraHom a),
          (O.mem_grading_iff n (σ.toAlgebraHom a)).mp (σ.map_grading n a a.property)⟩ := by
      ext p q hpq x
      have hq : q = p + n := by omega
      subst q
      let y : L.grading p := i.inv.f p x
      have h₁ := hτ n p a y
      have h₂ := hσ n p a y
      have hy : i.hom.f p y = x := by
        show i.hom.f p (i.inv.f p x) = x
        exact congrArg (fun f ↦ f.hom x) (congrArg (fun f ↦ f.f p) i.inv_hom_id)
      rw [hy] at h₁ h₂
      exact h₁.trans h₂.symm
    exact O.equiv.injective (congrArg Subtype.val ((E.cochainEquiv n).injective hco))
  have hmap : τ.toAlgebraHom = σ.toAlgebraHom := by
    refine AlgHom.ext fun a ↦ ?_
    induction a using DirectSum.Decomposition.inductionOn A.grading with
    | zero => simp
    | homogeneous a => exact hhomogeneous a
    | add a b ha hb => simp [ha, hb]
  cases τ with
  | mk τmap τgrading τd =>
    cases σ with
    | mk σmap σgrading σd =>
      have hm : τmap = σmap := hmap
      subst σmap
      rfl


/-- A right differential graded `A`-module whose underlying complex is identified with `M`
determines a unique homomorphism of differential graded algebras from `A` into the graded opposite
of the endomorphism algebra of `M`, namely the one satisfying the signed-action equation. -/
@[stacks 0FQ5 "module to homomorphism"]
theorem existsUnique_isSignedAction (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (L : DifferentialGradedModule A)
    (i : L.toCochainComplex ≅ M) :
    ∃! τ : A.Hom (oppEndAlgebra M), IsSignedAction A M L i τ := by
  let O := DifferentialGradedAlgebra.opposite R A
  let OO := DifferentialGradedAlgebra.opposite R O.toDifferentialGradedAlgebra
  let idO : O.toDifferentialGradedAlgebra.Hom O.toDifferentialGradedAlgebra :=
    ⟨AlgHom.id R _, fun _ _ h ↦ h, fun _ ↦ rfl⟩
  let φ := DifferentialGradedAlgebra.oppositeHom OO
    (DifferentialGradedAlgebra.Opposite.involution A O) idO
  let N := restrictScalars φ L
  let F := DifferentialGraded.leftRightEquivalence R O.toDifferentialGradedAlgebra
  let K := F.equivalence.inverse.obj N
  let P := F.equivalence.functor.obj K
  let c : P ≅ N := F.equivalence.counitIso.app N
  let U := F.underlying K
  let e := DifferentialGraded.LeftModule.oppositeGradingEquiv O.toDifferentialGradedAlgebra K
  let k := DifferentialGraded.LeftModule.oppositeCochainIso O.toDifferentialGradedAlgebra K
  let j := k ≪≫ (forgetToCochainComplex _).mapIso c ≪≫ i
  let act := DifferentialGraded.LeftModule.leftAction O.toDifferentialGradedAlgebra K M j
  let f := (DifferentialGradedAlgebra.leftActionEquivHom O.toDifferentialGradedAlgebra M).val act
  let τ := DifferentialGradedAlgebra.oppositeHom
    (DifferentialGradedAlgebra.Opposite.involution A O) (oppEndOpposite M) f
  have hτ : IsSignedAction A M L i τ := by
    intro n p a x
    let b : O.toDifferentialGradedAlgebra.grading n :=
      ⟨O.equiv.symm a, (O.mem_grading_iff n _).mpr (by simp)⟩
    let y : P.grading p := c.inv.gradedMap p x
    let z : K.grading p := (e p).symm y
    have hcx : c.hom.gradedMap p y = x :=
      Subtype.ext (congrArg (fun h : N ⟶ N ↦ h.toFun (x : L.M)) c.inv_hom_id)
    have hj : j.hom.f p z = i.hom.f p x := by
      show i.hom.f p (c.hom.gradedMap p (e p ((e p).symm y))) = _
      rw [LinearEquiv.apply_symm_apply, hcx]
    have hf := (DifferentialGradedAlgebra.leftActionEquivHom
      O.toDifferentialGradedAlgebra M).property act n b
    have heval := DifferentialGraded.LeftModule.leftAction_apply
      O.toDifferentialGradedAlgebra K M j n p b z
    show ((endomorphismDGA M).cochainEquiv n ⟨_, _⟩).v p (p + n) (by omega) (i.hom.f p x) = _
    have hval : (oppEndOpposite M).equiv (τ.toAlgebraHom a) = f.toAlgebraHom b := by
      simp [τ, DifferentialGradedAlgebra.oppositeHom,
        DifferentialGradedAlgebra.Opposite.involution, b]
    simp only [hval]
    rw [hf, ← hj, heval]
    show i.hom.f (p + n) (c.hom.gradedMap (p + n)
      (e (p + n) ⟨(b : O.toDifferentialGradedAlgebra.A) • (z : K.M), by
        simpa only [add_comm] using K.smul_mem n p b z b.property z.property⟩)) = _
    have hz : (z : K.M) = U (y : P.M) := rfl
    let aa := OO.equiv.symm (b : O.toDifferentialGradedAlgebra.A)
    have haa : aa ∈ OO.toDifferentialGradedAlgebra.grading n :=
      (OO.mem_grading_iff n aa).mpr (by
        simpa only [aa, LinearEquiv.apply_symm_apply] using b.property)
    have haction : U.symm ((b : O.toDifferentialGradedAlgebra.A) • (z : K.M)) =
        (n * p).negOnePow • (MulOpposite.op aa • (y : P.M)) := by
      apply U.injective
      simp only [LinearEquiv.apply_symm_apply, Units.smul_def, map_zsmul]
      rw [F.action K n p aa y haa y.property]
      simp only [aa, OO, LinearEquiv.apply_symm_apply, Units.smul_def, smul_smul,
        ← Units.val_mul, ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul, Units.val_one,
        one_smul, hz, U]
    have hscalar : φ.toAlgebraHom aa = (a : A.A) := by
      simp [φ, DifferentialGradedAlgebra.oppositeHom,
        DifferentialGradedAlgebra.Opposite.involution, idO, aa, b]
    have heq : c.hom.gradedMap (p + n)
        (e (p + n) ⟨(b : O.toDifferentialGradedAlgebra.A) • (z : K.M), by
          simpa only [add_comm] using K.smul_mem n p b z b.property z.property⟩) =
        (n * p).negOnePow •
          (⟨MulOpposite.op (a : A.A) • (x : L.M),
            L.smul_mem p n x a x.property a.property⟩ : L.grading (p + n)) := by
      apply Subtype.ext
      show c.hom.toFun (U.symm ((b : O.toDifferentialGradedAlgebra.A) • (z : K.M))) = _
      rw [haction]
      simp only [Units.smul_def, map_zsmul, c.hom.map_smul]
      show (n * p).negOnePow.val •
        (@SMul.smul (MulOpposite A.A) L.M inferInstance
          (MulOpposite.op (φ.toAlgebraHom aa)) (c.hom.toFun (c.inv.toFun (x : L.M)))) = _
      rw [hscalar]
      have hcx : c.hom.toFun (c.inv.toFun (x : L.M)) = (x : L.M) :=
        congrArg (fun h : N ⟶ N ↦ h.toFun (x : L.M)) c.inv_hom_id
      rw [hcx]
      rfl
    rw [heq]
    exact map_zsmul (i.hom.f (p + n)).hom _ _
  exact ⟨τ, hτ, fun σ hσ ↦ hom_eq_of_isSignedAction A M L i σ τ hσ hτ⟩

/-- Every homomorphism of differential graded algebras from `A` into the graded opposite of the
endomorphism algebra of `M` arises from a right differential graded `A`-module whose underlying
complex is `M`, with the action given by the signed-action equation. -/
@[stacks 0FQ5 "homomorphism to module"]
theorem exists_rightModule_isSignedAction (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (τ : A.Hom (oppEndAlgebra M)) :
    ∃ (L : DifferentialGradedModule A) (i : L.toCochainComplex ≅ M), IsSignedAction A M L i τ := by
  let _ : Module (MulOpposite A.A) (totalModule M) :=
    Module.compHom (totalModule M) (oppEndActionRingHom A M τ)
  have hbase : ∀ (r : R) (x : totalModule M), (algebraMap R (MulOpposite A.A) r) • x = r • x := by
    intro r x
    show oppEndActionRingHom A M τ (algebraMap R (MulOpposite A.A) r) x = r • x
    simp [oppEndActionRingHom, oppEndActionTotal_algebraMap]
  let _ : IsScalarTower R (MulOpposite A.A) (totalModule M) :=
    IsScalarTower.of_algebraMap_smul hbase
  let L : DifferentialGradedModule A := {
    M := totalModule M
    grading := totalGrading M
    decomposition := DirectSum.rangeGradingDecomposition R (fun q ↦ M.X q)
    smul_mem := by
      intro p n x a hx ha
      show oppEndActionTotal A M τ a x ∈ totalGrading M (p + n)
      exact oppEndActionTotal_mem_grading A M τ n p a ha ⟨x, hx⟩
    d := totalDifferential M
    d_comp_d := totalDifferential_square M
    d_mem := by
      intro p x hx
      rcases hx with ⟨y, rfl⟩
      rw [totalDifferential_lof]
      exact ⟨(M.d p (p + 1)).hom y, rfl⟩
    leibniz := by
      intro p n x a hx ha
      rcases hx with ⟨y, rfl⟩
      show totalDifferential M
          (oppEndActionTotal A M τ a (DirectSum.lof R ℤ (fun q ↦ M.X q) p y)) =
        oppEndActionTotal A M τ a
            (totalDifferential M (DirectSum.lof R ℤ (fun q ↦ M.X q) p y)) +
          (p.negOnePow : ℤ) • oppEndActionTotal A M τ (A.d a)
            (DirectSum.lof R ℤ (fun q ↦ M.X q) p y)
      rw [oppEndActionTotal_apply_of_mem A M τ n a ha,
        oppEndActionTotal_apply_of_mem A M τ (n + 1) (A.d a) (A.d_mem n a ha),
        ← Int.cast_smul_eq_zsmul R (p.negOnePow : ℤ)]
      simpa [Int.coe_negOnePow] using oppEndAction_leibniz A M τ n p ⟨a, ha⟩ y }
  let i : L.toCochainComplex ≅ M :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ (totalComponentEquiv M p).symm.toModuleIso) (by
        intro p q hpq
        apply ModuleCat.hom_ext
        ext x
        rcases x.property with ⟨y, hy⟩
        have hx : x = totalComponentEquiv M p y :=
          Subtype.ext (by rw [totalComponentEquiv_coe]; exact hy.symm)
        subst x
        have hq : p + 1 = q := hpq
        subst q
        have hmem : totalDifferential M (totalComponentEquiv M p y : totalModule M) ∈
            totalGrading M (p + 1) := by
          rw [totalComponentEquiv_coe, totalDifferential_lof]
          exact ⟨(M.d p (p + 1)).hom y, rfl⟩
        have hdiff : (⟨totalDifferential M (totalComponentEquiv M p y : totalModule M), hmem⟩ :
              totalGrading M (p + 1)) =
            totalComponentEquiv M (p + 1) ((M.d p (p + 1)).hom y) := by
          apply Subtype.ext
          show totalDifferential M (totalComponentEquiv M p y : totalModule M) =
            (totalComponentEquiv M (p + 1) ((M.d p (p + 1)).hom y) : totalModule M)
          rw [totalComponentEquiv_coe, totalComponentEquiv_coe, totalDifferential_lof]
        simp only [LinearEquiv.toModuleIso_hom, DifferentialGradedModule.toCochainComplex_d,
          DifferentialGradedModule.gradedDifferential]
        show (M.d p (p + 1)).hom
            ((totalComponentEquiv M p).symm (totalComponentEquiv M p y)) =
          (totalComponentEquiv M (p + 1)).symm
            ⟨totalDifferential M (totalComponentEquiv M p y : totalModule M), hmem⟩
        rw [LinearEquiv.symm_apply_apply, hdiff, LinearEquiv.symm_apply_apply])
  refine ⟨L, i, fun n p a x ↦ ?_⟩
  obtain ⟨y, hy⟩ := (totalComponentEquiv M p).surjective x
  subst x
  show (oppEndCochain A M τ n a).v p (p + n) (by omega)
      ((totalComponentEquiv M p).symm (totalComponentEquiv M p y)) =
    (n * p).negOnePow • (totalComponentEquiv M (p + n)).symm
      ⟨oppEndActionTotal A M τ a (totalComponentEquiv M p y : totalModule M), _⟩
  rw [LinearEquiv.symm_apply_apply]
  have hact : (⟨oppEndActionTotal A M τ a (totalComponentEquiv M p y : totalModule M),
      L.smul_mem p n _ _ (totalComponentEquiv M p y).property a.property⟩ :
      totalGrading M (p + n)) =
      totalComponentEquiv M (p + n)
        ((n * p).negOnePow • (oppEndCochain A M τ n a).v p (p + n) (by omega) y) := by
    apply Subtype.ext
    show oppEndActionTotal A M τ a (totalComponentEquiv M p y : totalModule M) =
      ((totalComponentEquiv M (p + n)
        ((n * p).negOnePow •
          (oppEndCochain A M τ n a).v p (p + n) (by omega) y)) : totalModule M)
    rw [totalComponentEquiv_coe, totalComponentEquiv_coe,
      oppEndActionTotal_apply_of_mem A M τ n a a.property]
    exact oppEndAction_lof_of_eq A M τ n p (p + n) rfl a y
  rw [hact, LinearEquiv.symm_apply_apply, smul_smul, ← Int.negOnePow_add, ← two_mul,
    Int.negOnePow_two_mul, one_smul]

end DifferentialGradedModule
