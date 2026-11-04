module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleOfTensor

/-!
# A differential graded bimodule is a module over the graded tensor product

Let `A` and `B` be differential graded algebras over a commutative ring `R` and let `M` be a
differential graded `(A, B)`-bimodule. Its left `A`-action and its right `B`-action commute up to
the Koszul sign, so together they make the module underlying `M` a right differential graded
module over the graded tensor product `Aᵒᵖ ⊗ B`, with `x · (a ⊗ b) = (-1)^{|a||x|} a x b`.

## Main definitions

* `DifferentialGraded.Bimodule.toLeftModule`: the left differential graded `A`-module underlying a
  bimodule.
* `DifferentialGraded.Bimodule.tensorActionAlgHom`: the two actions, combined into an algebra
  homomorphism from the graded tensor product into the opposite endomorphism algebra.
* `DifferentialGraded.Bimodule.toTensorModule`: the resulting right differential graded module
  over the graded tensor product.

## Main results

* `DifferentialGraded.Bimodule.factorActions_antiCommute`: the two factors anticommute by the
  Koszul sign, which is what lets them be combined.
* `DifferentialGraded.Bimodule.tensorAction_tmul_formula`: the action of a pure tensor on a
  homogeneous element is the signed composite of the two actions.
* `DifferentialGraded.Bimodule.tensorAction_smul_mem` and
  `DifferentialGraded.Bimodule.tensorAction_leibniz`: the combined action respects the grading and
  the Leibniz rule.

## Implementation notes

Both actions are presented as algebra homomorphisms into the opposite of the endomorphism algebra
of the module underlying `M`, so that `DifferentialGraded.liftTensorActionAlgHom` applies; the left
action is transported there through graded opposition, which is where the Koszul sign enters. The
grading and Leibniz conditions are then checked on pure tensors and extended to the whole graded
tensor product by `Submodule.span_induction` over the definition of its grading.

## References

* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R]

namespace DifferentialGraded.Bimodule

variable (A : DifferentialGradedAlgebra R) (B : DifferentialGradedAlgebra R)

/-- The left differential graded `A`-module underlying a differential graded bimodule. -/
noncomputable abbrev toLeftModule (M : Bimodule A B) : LeftModule A := by
  let L := M.leftAction.1
  let φ := leftActionAlgHom A B M.rightModule L
  letI : Module A.A M.rightModule.M := Module.compHom M.rightModule.M φ.toRingHom
  haveI : IsScalarTower R A.A M.rightModule.M := ⟨fun r a x ↦ by
    change (φ (r • a)) x = r • ((φ a) x)
    simp [φ, map_smul]⟩
  refine {
    M := M.rightModule.M
    grading := M.rightModule.grading
    d := M.rightModule.d
    d_comp_d := M.rightModule.d_comp_d
    smul_mem := ?_
    d_mem := M.rightModule.d_mem
    leibniz := ?_ }
  · intro n p a x ha hx
    change (φ a) x ∈ M.rightModule.grading (n + p)
    change leftActionTotal A B M.rightModule L a x ∈ _
    simpa only [add_comm] using
      leftActionTotal_apply_mem A B M.rightModule L ⟨a, ha⟩ ⟨x, hx⟩
  · intro n p a x ha hx
    exact leftActionTotal_leibniz A B M.rightModule L ⟨a, ha⟩ x

/-- The grading of `toLeftModule` is the grading of the bimodule. -/
theorem toLeftModule_grading (M : Bimodule A B) (p : ℤ) :
    (toLeftModule A B M).grading p = M.rightModule.grading p := rfl

/-- The underlying module of `toLeftModule` is the underlying module of the bimodule. -/
noncomputable abbrev leftUnderlyingEquiv (M : Bimodule A B) :
    M.rightModule.M ≃ₗ[R] (toLeftModule A B M).M :=
  LinearEquiv.refl R M.rightModule.M

/-- `leftUnderlyingEquiv` is the identity on elements. -/
@[simp]
theorem leftUnderlyingEquiv_apply (M : Bimodule A B) (x : M.rightModule.M) :
    leftUnderlyingEquiv A B M x = x := rfl

/-- The inverse of `leftUnderlyingEquiv` is the identity on elements. -/
@[simp]
theorem leftUnderlyingEquiv_symm_apply (M : Bimodule A B) (x : (toLeftModule A B M).M) :
    (leftUnderlyingEquiv A B M).symm x = x := rfl

/-- The transported action of a homogeneous element of the graded opposite of `A` on a homogeneous
element is the Koszul-signed left action of `A`. -/
private theorem unop_transport_leftAction_apply (M : Bimodule A B) {m p : ℤ}
    (a : (oppAlgebra A).grading m) (x : M.rightModule.grading p) :
    MulOpposite.unop
        (transportRightActionAlgHom
          (((leftRightEquivalence R A).underlying (toLeftModule A B M)).trans
            (leftUnderlyingEquiv A B M).symm)
          (DifferentialGradedModule.rightActionAlgHom (oppAlgebra A)
            ((leftRightEquivalence R A).equivalence.functor.obj (toLeftModule A B M)))
          (a : (oppAlgebra A).A)) (x : M.rightModule.M) =
      (m * p).negOnePow •
        leftActionTotal A B M.rightModule M.leftAction.1
          ((DifferentialGradedAlgebra.opposite R A).equiv (a : (oppAlgebra A).A))
          (x : M.rightModule.M) := by
  let C := oppAlgebra A
  let E := leftRightEquivalence R A
  let L := toLeftModule A B M
  let P := E.equivalence.functor.obj L
  let _ : Module A.A L.M := L.amodule
  let _ : IsScalarTower R A.A L.M := L.isScalarTower
  let i := leftUnderlyingEquiv A B M
  let e := (E.underlying L).trans i.symm
  let aa : A.grading m := ⟨(DifferentialGradedAlgebra.opposite R A).equiv (a : C.A),
    (DifferentialGradedAlgebra.opposite R A).mem_grading_iff m (a : C.A) |>.mp a.property⟩
  let xp : P.grading p := ⟨(E.underlying L).symm (i x),
    (E.grading L p _).mpr (by simp [i])⟩
  have hsmul (y : L.M) :
      (aa : A.A) • y = leftActionTotal A B M.rightModule M.leftAction.1 (aa : A.A) y := by
    change leftActionAlgHom A B M.rightModule M.leftAction.1 (aa : A.A) y = _
    rfl
  have hfa := E.action L m p (a : C.A) xp a.property xp.property
  have hfaE : E.underlying L (MulOpposite.op (a : C.A) • (xp : P.M)) =
      (m * p).negOnePow • (DifferentialGradedAlgebra.opposite R A).equiv (a : C.A) • i x := by
    simpa [xp] using hfa
  have hfa' : e (MulOpposite.op (a : C.A) • (xp : P.M)) =
      (m * p).negOnePow • leftActionTotal A B M.rightModule M.leftAction.1 (aa : A.A) x := by
    calc
      _ = i.symm (E.underlying L (MulOpposite.op (a : C.A) • (xp : P.M))) := rfl
      _ = i.symm ((m * p).negOnePow •
          (DifferentialGradedAlgebra.opposite R A).equiv (a : C.A) • i x) :=
        congrArg i.symm hfaE
      _ = (m * p).negOnePow • (aa : A.A) • (x : L.M) := by simp [i, aa]
      _ = _ := by rw [hsmul]
  have hxe : e.symm (x : M.rightModule.M) = xp := by
    simp [e, xp, i, LinearEquiv.refl]
  rw [transportRightActionAlgHom_apply]
  change e (MulOpposite.op (a : C.A) • e.symm (x : M.rightModule.M)) = _
  rw [hxe, hfa']

/-- The left and right actions on a differential graded bimodule anticommute by the Koszul sign,
once the left action is transported to a right action of the graded opposite. -/
theorem factorActions_antiCommute (M : Bimodule A B) {m n : ℤ}
    (a : (oppAlgebra A).grading m) (b : B.grading n) :
    let E := leftRightEquivalence R A
    let P := E.equivalence.functor.obj (toLeftModule A B M)
    let e := (E.underlying (toLeftModule A B M)).trans (leftUnderlyingEquiv A B M).symm
    transportRightActionAlgHom e (DifferentialGradedModule.rightActionAlgHom (oppAlgebra A) P)
          (a : (oppAlgebra A).A) *
        DifferentialGradedModule.rightActionAlgHom B M.rightModule (b : B.A) =
      (-1 : ℤˣ) ^ (n * m) •
        (DifferentialGradedModule.rightActionAlgHom B M.rightModule (b : B.A) *
          transportRightActionAlgHom e
            (DifferentialGradedModule.rightActionAlgHom (oppAlgebra A) P)
            (a : (oppAlgebra A).A)) := by
  let C := oppAlgebra A
  let E := leftRightEquivalence R A
  let L := toLeftModule A B M
  let P := E.equivalence.functor.obj L
  let _ : Module A.A L.M := L.amodule
  let _ : IsScalarTower R A.A L.M := L.isScalarTower
  let i := leftUnderlyingEquiv A B M
  let e := (E.underlying L).trans i.symm
  apply MulOpposite.unop_injective
  ext x
  induction x using DirectSum.Decomposition.inductionOn M.rightModule.grading with
  | zero => simp [DifferentialGradedModule.rightActionAlgHom_apply]
  | add x y hx hy => simp only [map_add, hx, hy]
  | @homogeneous p x =>
    let aa : A.grading m := ⟨(DifferentialGradedAlgebra.opposite R A).equiv (a : C.A),
      (DifferentialGradedAlgebra.opposite R A).mem_grading_iff m (a : C.A) |>.mp a.property⟩
    have hxb : MulOpposite.op (b : B.A) • (x : M.rightModule.M) ∈
        M.rightModule.grading (p + n) :=
      M.rightModule.smul_mem p n x b x.property b.property
    have hraw := leftActionTotal_commutes A B M.rightModule
      M.leftAction.1 M.leftAction.2 aa b x
    rw [MulOpposite.unop_mul, Module.End.mul_eq_comp, LinearMap.comp_apply,
      DifferentialGradedModule.rightActionAlgHom_apply, unop_units_smul_apply]
    simp only [MulOpposite.unop_mul, Module.End.mul_eq_comp, LinearMap.comp_apply,
      DifferentialGradedModule.rightActionAlgHom_apply]
    rw [unop_transport_leftAction_apply A B M a x,
      unop_transport_leftAction_apply A B M a ⟨_, hxb⟩]
    rw [hraw]
    have hsign : (m * p).negOnePow = (n * m).negOnePow * (m * (p + n)).negOnePow := by
      rw [← Int.negOnePow_add]
      have h : n * m + m * (p + n) = m * p + 2 * (m * n) := by ring
      rw [h, Int.negOnePow_add, Int.negOnePow_two_mul]
      simp
    rw [hsign]
    rw [smul_comm, smul_smul]

/-- The two actions on a differential graded bimodule, combined into an algebra homomorphism from
the graded tensor product into the opposite endomorphism algebra. -/
noncomputable def tensorActionAlgHom (M : Bimodule A B) :
    (tensorAlgebra A B).A →ₐ[R] MulOpposite (Module.End R M.rightModule.M) := by
  let C := oppAlgebra A
  let E := leftRightEquivalence R A
  let L := toLeftModule A B M
  let P := E.equivalence.functor.obj L
  let e := (E.underlying L).trans (leftUnderlyingEquiv A B M).symm
  let f := transportRightActionAlgHom e (DifferentialGradedModule.rightActionAlgHom C P)
  let g := DifferentialGradedModule.rightActionAlgHom B M.rightModule
  exact liftTensorActionAlgHom M.rightModule.M f g (by
    intro i j a b
    exact factorActions_antiCommute A B M a b)

/-- A pure tensor `a ⊗ b` of the tensor algebra acts on the bimodule by the transported action of
`a`, followed by the right action of `b`. -/
theorem tensorActionAlgHom_tmul_smul (M : Bimodule A B) (a : (oppAlgebra A).A) (b : B.A)
    (x : M.rightModule.M) :
    letI := moduleOfAlgHom (tensorAlgebra A B) M.rightModule.M (tensorActionAlgHom A B M)
    (MulOpposite.op (GradedTensorProduct.tmul (R := R) (𝒜 := (oppAlgebra A).grading)
        (ℬ := B.grading) a b : (tensorAlgebra A B).A) :
        MulOpposite (tensorAlgebra A B).A) • x =
      MulOpposite.unop (DifferentialGradedModule.rightActionAlgHom B M.rightModule b)
        (MulOpposite.unop
          (transportRightActionAlgHom
            (((leftRightEquivalence R A).underlying (toLeftModule A B M)).trans
              (leftUnderlyingEquiv A B M).symm)
            (DifferentialGradedModule.rightActionAlgHom (oppAlgebra A)
              ((leftRightEquivalence R A).equivalence.functor.obj (toLeftModule A B M))) a)
          x) := by
  let C := oppAlgebra A
  let T := tensorAlgebra A B
  let E := leftRightEquivalence R A
  let L := toLeftModule A B M
  let P := E.equivalence.functor.obj L
  let e := (E.underlying L).trans (leftUnderlyingEquiv A B M).symm
  let f := transportRightActionAlgHom e (DifferentialGradedModule.rightActionAlgHom C P)
  let g := DifferentialGradedModule.rightActionAlgHom B M.rightModule
  let F := tensorActionAlgHom A B M
  let _ := moduleOfAlgHom T M.rightModule.M F
  let h : ∀ ⦃i j⦄ (a : C.grading i) (b : B.grading j),
      f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a) := by
    intro i j a b
    exact factorActions_antiCommute A B M a b
  exact liftedTensorAction_smul_tmul M.rightModule.M f g h a b x

/-- The combined action of a pure tensor on a homogeneous element is the signed composite of the
left and right actions. -/
theorem tensorAction_tmul_formula (M : Bimodule A B) {m n p : ℤ}
    (a : (oppAlgebra A).grading m) (b : B.grading n) (x : M.rightModule.grading p) :
    letI := moduleOfAlgHom (tensorAlgebra A B) M.rightModule.M (tensorActionAlgHom A B M)
    (MulOpposite.op (GradedTensorProduct.tmul (R := R) (𝒜 := (oppAlgebra A).grading)
        (ℬ := B.grading) (a : (oppAlgebra A).A) (b : B.A) : (tensorAlgebra A B).A) :
        MulOpposite (tensorAlgebra A B).A) • (x : M.rightModule.M) =
      (m * p).negOnePow •
        leftActionTotal A B M.rightModule M.leftAction.1
          ((DifferentialGradedAlgebra.opposite R A).equiv a)
          (MulOpposite.op (b : B.A) • (x : M.rightModule.M)) := by
  let C := oppAlgebra A
  let T := tensorAlgebra A B
  let E := leftRightEquivalence R A
  let L := toLeftModule A B M
  let P := E.equivalence.functor.obj L
  let _ : Module A.A L.M := L.amodule
  let _ : IsScalarTower R A.A L.M := L.isScalarTower
  let i := leftUnderlyingEquiv A B M
  let e := (E.underlying L).trans i.symm
  let f := transportRightActionAlgHom e (DifferentialGradedModule.rightActionAlgHom C P)
  let g := DifferentialGradedModule.rightActionAlgHom B M.rightModule
  let F := tensorActionAlgHom A B M
  let _ := moduleOfAlgHom T M.rightModule.M F
  let h : ∀ ⦃i j⦄ (a : C.grading i) (b : B.grading j),
      f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a) := by
    intro i j a b
    exact factorActions_antiCommute A B M a b
  let aa : A.grading m := ⟨(DifferentialGradedAlgebra.opposite R A).equiv (a : C.A),
    (DifferentialGradedAlgebra.opposite R A).mem_grading_iff m (a : C.A) |>.mp a.property⟩
  have hT := tensorActionAlgHom_tmul_smul A B M (a : C.A) (b : B.A) (x : M.rightModule.M)
  show (MulOpposite.op (GradedTensorProduct.tmul (R := R)
      (𝒜 := C.grading) (ℬ := B.grading) (a : C.A) (b : B.A) : T.A) :
      MulOpposite T.A) • (x : M.rightModule.M) = _
  rw [hT, unop_transport_leftAction_apply A B M a x,
    DifferentialGradedModule.rightActionAlgHom_apply, smul_comm]
  rw [← leftActionTotal_commutes A B M.rightModule
    M.leftAction.1 M.leftAction.2 aa b (x : M.rightModule.M)]

/-- The combined action respects the grading. -/
theorem tensorAction_smul_mem (M : Bimodule A B) {p q : ℤ} (t : (tensorAlgebra A B).A)
    (ht : t ∈ (tensorAlgebra A B).grading q) (x : M.rightModule.M)
    (hx : x ∈ M.rightModule.grading p) :
    letI := moduleOfAlgHom (tensorAlgebra A B) M.rightModule.M (tensorActionAlgHom A B M)
    (MulOpposite.op t : MulOpposite (tensorAlgebra A B).A) • x ∈
      M.rightModule.grading (p + q) := by
  let C := oppAlgebra A
  let T := tensorAlgebra A B
  let F := tensorActionAlgHom A B M
  let _ := moduleOfAlgHom T M.rightModule.M F
  let _ := moduleOfAlgHom_isScalarTower T M.rightModule.M F
  change t ∈ DifferentialGradedAlgebra.tensorProductGrading C B q at ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨i, j, a, b, ha, hb, hij, rfl⟩ := ht
    let aa : C.grading i := ⟨a, ha⟩
    let bb : B.grading j := ⟨b, hb⟩
    show (MulOpposite.op (GradedTensorProduct.tmul (R := R)
      (𝒜 := C.grading) (ℬ := B.grading) a b) : MulOpposite T.A) • x ∈
      M.rightModule.grading (p + q)
    have hformula := tensorAction_tmul_formula A B M aa bb ⟨x, hx⟩
    have hformula' : (MulOpposite.op (GradedTensorProduct.tmul (R := R)
        (𝒜 := C.grading) (ℬ := B.grading) a b) : MulOpposite T.A) • x =
        (i * p).negOnePow • leftActionTotal A B M.rightModule M.leftAction.1
          ((DifferentialGradedAlgebra.opposite R A).equiv (aa : C.A))
          (MulOpposite.op (bb : B.A) • x) := by
      simpa only [aa, bb] using hformula
    rw [hformula']
    have hright : MulOpposite.op (b : B.A) • x ∈ M.rightModule.grading (p + j) :=
      M.rightModule.smul_mem p j x b hx hb
    have hleft : leftActionTotal A B M.rightModule M.leftAction.1
        ((DifferentialGradedAlgebra.opposite R A).equiv (a : C.A))
        (MulOpposite.op (b : B.A) • x) ∈ M.rightModule.grading ((p + j) + i) := by
      let aaa : A.grading i := ⟨(DifferentialGradedAlgebra.opposite R A).equiv (a : C.A),
        (DifferentialGradedAlgebra.opposite R A).mem_grading_iff i (a : C.A) |>.mp ha⟩
      exact leftActionTotal_apply_mem A B M.rightModule M.leftAction.1 aaa ⟨_, hright⟩
    rw [Units.smul_def]
    have hdeg : (p + j) + i = p + q := by omega
    exact zsmul_mem (by simpa [hdeg] using hleft) _
  | zero => simp
  | add s t hs ht ihs iht =>
    show (MulOpposite.op (s + t) : MulOpposite T.A) • x ∈ _
    simp only [MulOpposite.op_add, add_smul]
    exact (M.rightModule.grading (p + q)).add_mem ihs iht
  | smul r t ht ih =>
    show (MulOpposite.op (r • t) : MulOpposite T.A) • x ∈ _
    have hscalar : (MulOpposite.op (r • t) : MulOpposite T.A) =
        algebraMap R (MulOpposite T.A) r * MulOpposite.op t := by
      simp [Algebra.smul_def, ← MulOpposite.op_mul, Algebra.commutes]
      rfl
    rw [hscalar, mul_smul, IsScalarTower.algebraMap_smul]
    exact (M.rightModule.grading (p + q)).smul_mem r ih

/-- The Leibniz rule for the combined action of a pure tensor. -/
theorem tensorAction_tmul_leibniz (M : Bimodule A B) {m n p : ℤ}
    (a : (oppAlgebra A).grading m) (b : B.grading n) (x : M.rightModule.grading p) :
    letI := moduleOfAlgHom (tensorAlgebra A B) M.rightModule.M (tensorActionAlgHom A B M)
    M.rightModule.d
        ((MulOpposite.op (GradedTensorProduct.tmul (R := R) (𝒜 := (oppAlgebra A).grading)
          (ℬ := B.grading) (a : (oppAlgebra A).A) (b : B.A) : (tensorAlgebra A B).A) :
            MulOpposite (tensorAlgebra A B).A) • (x : M.rightModule.M)) =
      ((MulOpposite.op (GradedTensorProduct.tmul (R := R) (𝒜 := (oppAlgebra A).grading)
          (ℬ := B.grading) (a : (oppAlgebra A).A) (b : B.A) : (tensorAlgebra A B).A) :
            MulOpposite (tensorAlgebra A B).A) • M.rightModule.d (x : M.rightModule.M)) +
        (p.negOnePow : ℤ) •
          ((MulOpposite.op ((tensorAlgebra A B).d (GradedTensorProduct.tmul (R := R)
            (𝒜 := (oppAlgebra A).grading) (ℬ := B.grading) (a : (oppAlgebra A).A) (b : B.A)) :
              (tensorAlgebra A B).A) : MulOpposite (tensorAlgebra A B).A) •
            (x : M.rightModule.M)) := by
  let C := oppAlgebra A
  let T := tensorAlgebra A B
  let F := tensorActionAlgHom A B M
  let _ := moduleOfAlgHom T M.rightModule.M F
  let _ := moduleOfAlgHom_isScalarTower T M.rightModule.M F
  show M.rightModule.d
      ((MulOpposite.op (GradedTensorProduct.tmul (R := R)
        (𝒜 := C.grading) (ℬ := B.grading) (a : C.A) (b : B.A) : T.A) :
          MulOpposite T.A) • (x : M.rightModule.M)) =
    ((MulOpposite.op (GradedTensorProduct.tmul (R := R)
        (𝒜 := C.grading) (ℬ := B.grading) (a : C.A) (b : B.A) : T.A) :
          MulOpposite T.A) • M.rightModule.d (x : M.rightModule.M)) +
      (p.negOnePow : ℤ) •
        ((MulOpposite.op (T.d (GradedTensorProduct.tmul (R := R)
          (𝒜 := C.grading) (ℬ := B.grading) (a : C.A) (b : B.A))) :
            MulOpposite T.A) • (x : M.rightModule.M))
  let aa : A.grading m := ⟨(DifferentialGradedAlgebra.opposite R A).equiv (a : C.A),
    (DifferentialGradedAlgebra.opposite R A).mem_grading_iff m (a : C.A) |>.mp a.property⟩
  let da : C.grading (m + 1) := ⟨C.d a, C.d_mem m a a.property⟩
  let db : B.grading (n + 1) := ⟨B.d b, B.d_mem n b b.property⟩
  let dx : M.rightModule.grading (p + 1) :=
    ⟨M.rightModule.d x, M.rightModule.d_mem p x x.property⟩
  have hr := M.rightModule.leibniz p n (x : M.rightModule.M) (b : B.A) x.property b.property
  have hl := leftActionTotal_leibniz A B M.rightModule M.leftAction.1 aa
    (MulOpposite.op (b : B.A) • (x : M.rightModule.M))
  have hf := tensorAction_tmul_formula A B M a b x
  have hfdx := tensorAction_tmul_formula A B M a b dx
  have hfda := tensorAction_tmul_formula A B M da b x
  have hfdb := tensorAction_tmul_formula A B M a db x
  have hdt := DifferentialGradedAlgebra.tensorProductDifferential_tmul C B m a b
  have hf' := by simpa [T, F, aa] using hf
  have hfdx' := by simpa [T, F, aa, dx] using hfdx
  have hfda' := by simpa [T, F] using hfda
  have hfdb' := by simpa [T, F, aa, db] using hfdb
  rw [hf', Units.smul_def, ← Int.cast_smul_eq_zsmul R, M.rightModule.d.map_smul,
    Int.cast_smul_eq_zsmul R, ← Units.smul_def, hl, hr,
    (leftActionTotal A B M.rightModule M.leftAction.1 aa).map_add, map_zsmul, hdt,
    MulOpposite.op_add, add_smul, hfdx', hfda', MulOpposite.op_smul, IsScalarTower.smul_assoc,
    hfdb']
  simp only [smul_add]
  repeat' rw [smul_smul]
  have hsq (z : ℤ) : z.negOnePow * z.negOnePow = 1 := by
    rw [← Int.negOnePow_add, Int.negOnePow_even _ (Even.add_self z)]
  have hA : (m * p).negOnePow = p.negOnePow * ((m + 1) * p).negOnePow := by
    rw [show (m + 1) * p = m * p + p by ring, Int.negOnePow_add]
    calc
      (m * p).negOnePow = (m * p).negOnePow * 1 := by simp
      _ = (m * p).negOnePow * (p.negOnePow * p.negOnePow) := by rw [hsq]
      _ = p.negOnePow * ((m * p).negOnePow * p.negOnePow) := by ac_rfl
  have hB : (m * (p + 1)).negOnePow = (m * p).negOnePow * m.negOnePow := by
    rw [show m * (p + 1) = m * p + m by ring, Int.negOnePow_add]
  rw [hA, hB]
  simp only [aa, da]
  rw [← (DifferentialGradedAlgebra.opposite R A).map_d, ← hA]
  simp_rw [Units.smul_def]
  simp_rw [← Int.cast_smul_eq_zsmul R]
  have hvalmul (u v : ℤˣ) : (u : R) * (v : R) = ((u * v : ℤˣ) : R) := by
    rw [← Int.cast_mul, Units.val_mul]
  have hAcoeff : ((m * p).negOnePow : R) =
      (p.negOnePow : R) * (((m + 1) * p).negOnePow : R) := by
    calc
      _ = ((p.negOnePow * ((m + 1) * p).negOnePow : ℤˣ) : R) :=
        congrArg (fun z : ℤˣ => (z : R)) hA
      _ = _ := (hvalmul _ _).symm
  simp only [smul_smul, Units.val_mul, Int.cast_mul]
  rw [hAcoeff, hvalmul]
  module

/-- The Leibniz rule for the combined action. -/
theorem tensorAction_leibniz (M : Bimodule A B) {p q : ℤ} (t : (tensorAlgebra A B).A)
    (ht : t ∈ (tensorAlgebra A B).grading q) (x : M.rightModule.M)
    (hx : x ∈ M.rightModule.grading p) :
    letI := moduleOfAlgHom (tensorAlgebra A B) M.rightModule.M (tensorActionAlgHom A B M)
    M.rightModule.d ((MulOpposite.op t : MulOpposite (tensorAlgebra A B).A) • x) =
      (MulOpposite.op t : MulOpposite (tensorAlgebra A B).A) • M.rightModule.d x +
        (p.negOnePow : ℤ) •
          ((MulOpposite.op ((tensorAlgebra A B).d t) :
            MulOpposite (tensorAlgebra A B).A) • x) := by
  let C := oppAlgebra A
  let T := tensorAlgebra A B
  let F := tensorActionAlgHom A B M
  let _ := moduleOfAlgHom T M.rightModule.M F
  let _ := moduleOfAlgHom_isScalarTower T M.rightModule.M F
  show M.rightModule.d ((MulOpposite.op t : MulOpposite T.A) • x) =
    (MulOpposite.op t : MulOpposite T.A) • M.rightModule.d x +
      (p.negOnePow : ℤ) • ((MulOpposite.op (T.d t) : MulOpposite T.A) • x)
  change t ∈ DifferentialGradedAlgebra.tensorProductGrading C B q at ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨i, j, a, b, ha, hb, hij, rfl⟩ := ht
    let aa : C.grading i := ⟨a, ha⟩
    let bb : B.grading j := ⟨b, hb⟩
    exact tensorAction_tmul_leibniz A B M aa bb ⟨x, hx⟩
  | zero => simp
  | add s t hs ht ihs iht =>
    show M.rightModule.d (MulOpposite.op (s + t) • x) =
      MulOpposite.op (s + t) • M.rightModule.d x +
        (p.negOnePow : ℤ) • (MulOpposite.op (T.d (s + t)) • x)
    simp only [MulOpposite.op_add, add_smul, map_add, ihs, iht]
    simp only [smul_add]
    abel
  | smul r t ht ih =>
    show M.rightModule.d (MulOpposite.op (r • t) • x) =
      MulOpposite.op (r • t) • M.rightModule.d x +
        (p.negOnePow : ℤ) • (MulOpposite.op (T.d (r • t)) • x)
    have hscalar : (MulOpposite.op (r • t) : MulOpposite T.A) =
        algebraMap R (MulOpposite T.A) r * MulOpposite.op t := by
      simp [Algebra.smul_def, ← MulOpposite.op_mul, Algebra.commutes]
      rfl
    have hscalar' : (MulOpposite.op (r • T.d t) : MulOpposite T.A) =
        algebraMap R (MulOpposite T.A) r * MulOpposite.op (T.d t) := by
      simp [Algebra.smul_def, ← MulOpposite.op_mul, Algebra.commutes]
    rw [hscalar, mul_smul, IsScalarTower.algebraMap_smul, M.rightModule.d.map_smul]
    rw [show T.d (r • t) = r • T.d t by simp, hscalar', mul_smul,
      IsScalarTower.algebraMap_smul]
    rw [ih, smul_add, smul_comm r (p.negOnePow : ℤ)]
    rw [add_left_cancel_iff]
    have hr : r • (MulOpposite.op (T.d t) • x) =
        (algebraMap R (MulOpposite T.A) r * MulOpposite.op (T.d t)) • x := by
      rw [← IsScalarTower.algebraMap_smul (A := MulOpposite T.A), ← mul_smul]
    exact congrArg (fun y : M.rightModule.M => (p.negOnePow : ℤ) • y) hr

/-- A differential graded `(A, B)`-bimodule, regarded as a right differential graded module over
the graded tensor product of the graded opposite of `A` with `B`. -/
noncomputable abbrev toTensorModule (M : Bimodule A B) :
    DifferentialGradedModule (tensorAlgebra A B) := by
  let T := tensorAlgebra A B
  let F := tensorActionAlgHom A B M
  letI : Module (MulOpposite T.A) M.rightModule.M := moduleOfAlgHom T M.rightModule.M F
  letI : IsScalarTower R (MulOpposite T.A) M.rightModule.M :=
    moduleOfAlgHom_isScalarTower T M.rightModule.M F
  refine {
    M := M.rightModule.M
    grading := M.rightModule.grading
    d := M.rightModule.d
    d_comp_d := M.rightModule.d_comp_d
    smul_mem := ?_
    d_mem := M.rightModule.d_mem
    leibniz := ?_ }
  · intro n m x t hx ht
    exact tensorAction_smul_mem A B M t ht x hx
  · intro n m x t hx ht
    exact tensorAction_leibniz A B M t ht x hx

end DifferentialGraded.Bimodule
