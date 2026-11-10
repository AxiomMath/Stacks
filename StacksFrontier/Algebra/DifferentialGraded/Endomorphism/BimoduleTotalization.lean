module

public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.Bimodule
public import StacksFrontier.Algebra.DifferentialGraded.TensorProduct

/-!
# Totalizing cochains to endomorphisms of a differential graded module

Let `C` be a differential graded algebra over a commutative ring `R` and `M` a right differential
graded `C`-module. A degree-`n` cochain of the complex underlying `M` is a family of maps
`M^p → M^{p+n}`; assembling them along the direct-sum decomposition of `M` gives an `R`-linear
endomorphism of the whole of `M`. This file performs that assembly and records how it interacts
with the operations on cochains, so that a left differential graded action of a second algebra `A`
on the complex underlying `M` can be turned into an algebra homomorphism `A ⟶ End_R(M)`.

It also records the three general constructions needed to combine such a left action with the
right `C`-action into an action of a graded tensor product: the right action as an algebra
homomorphism into the opposite endomorphism algebra, the transport of such a homomorphism along a
linear equivalence, and the module structure a homomorphism into the opposite endomorphism algebra
defines.

## Main definitions

* `DifferentialGradedModule.totalizeCochain`: the endomorphism of `M` assembled from a cochain.
* `DifferentialGraded.leftActionTotal`: the algebra-like map `A → End_R(M)` assembled from a left
  differential graded action, and `DifferentialGraded.leftActionAlgHom`, its packaging as an
  algebra homomorphism.
* `DifferentialGradedModule.rightActionAlgHom`: the right action of `C` on `M`, as an algebra
  homomorphism into the opposite of `End_R(M)`.
* `DifferentialGraded.moduleOfAlgHom`: the right module structure defined by an algebra
  homomorphism into the opposite of `End_R(X)`.
* `DifferentialGraded.liftTensorActionAlgHom`: two such homomorphisms that commute up to the
  Koszul sign extend to the graded tensor product.

## Main results

* `DifferentialGradedModule.totalizeCochain_apply`: the assembled map is the cochain component on
  each homogeneous piece.
* `DifferentialGradedModule.totalizeCochain_add`, `_smul`, `_comp`, `_id` and `_delta_apply`: the
  assembly is additive, `R`-linear, anti-multiplicative for composition of cochains, unital, and
  turns the cochain differential into the graded commutator with `M.d`.
* `DifferentialGraded.leftActionTotal_leibniz`, `_commutes`, `_mul`, `_one`: the resulting map
  satisfies the Leibniz rule, commutes with the right action when the action is right `C`-linear,
  and is multiplicative and unital, so that it is an algebra homomorphism.

## Implementation notes

The assembly is `DirectSum.toModule` applied to the cochain components, precomposed with the
decomposition of `M`; `totalizeCochain_apply` describes it on homogeneous elements, and the later
proofs go through that lemma after `DirectSum.Decomposition.inductionOn`.

## References

* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ)
-/

@[expose] public section

open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R]

namespace DifferentialGradedAlgebra

/-- The differential of a differential graded algebra kills the unit. -/
theorem d_one (C : DifferentialGradedAlgebra R) : C.d 1 = 0 := by
  have h1 : (1 : C.A) ∈ C.grading 0 := SetLike.one_mem_graded C.grading
  simpa using C.leibniz 0 0 (1 : C.A) 1 h1 h1

end DifferentialGradedAlgebra

namespace DifferentialGraded

/-- A `ℤˣ`-power of `-1` acting on a scalar may be moved onto the whole action. -/
theorem units_negOnePow_smul_assoc {S X : Type*} [Ring S] [Algebra R S] [AddCommGroup X]
    [Module R X] [Module S X] [IsScalarTower R S X] (n : ℤ) (s : S) (x : X) :
    ((-1 : ℤˣ) ^ n • s) • x = n.negOnePow • (s • x) := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R, IsScalarTower.smul_assoc, Units.smul_def,
    ← Int.cast_smul_eq_zsmul R, ← Int.negOnePow_def]

end DifferentialGraded

namespace DifferentialGradedModule

/-- The `R`-linear endomorphism of `M` assembled from a degree-`n` cochain of its underlying
complex. -/
noncomputable def totalizeCochain (C : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule C) (n : ℤ)
    (f : Cochain M.toCochainComplex M.toCochainComplex n) : M.M →ₗ[R] M.M := by
  let pieces : ∀ p : ℤ, M.grading p →ₗ[R] M.M := fun p =>
    (M.grading (p + n)).subtype.comp (f.v p (p + n) rfl).hom
  exact (DirectSum.toModule R ℤ M.M pieces).comp
    (DirectSum.decomposeLinearEquiv M.grading).toLinearMap

/-- On a homogeneous element, the assembled endomorphism is the cochain component. -/
theorem totalizeCochain_apply (C : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule C) (n p : ℤ)
    (f : Cochain M.toCochainComplex M.toCochainComplex n) (x : M.grading p) :
    totalizeCochain C M n f x = (M.grading (p + n)).subtype ((f.v p (p + n) rfl).hom x) := by
  simp [totalizeCochain, DirectSum.toModule_lof, DirectSum.decomposeLinearEquiv_apply_coe,
    DifferentialGradedModule.toCochainComplex_X]
  rfl

/-- `totalizeCochain_apply` with the target degree prescribed. -/
theorem totalizeCochain_apply_of_eq (C : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule C) (n p q : ℤ) (hpq : p + n = q)
    (f : Cochain M.toCochainComplex M.toCochainComplex n) (x : M.grading p) :
    totalizeCochain C M n f x = (M.grading q).subtype ((f.v p q hpq).hom x) := by
  cases hpq
  exact totalizeCochain_apply C M n p f x

/-- The cochain differential becomes the graded commutator with the differential of `M`. -/
theorem totalizeCochain_delta_apply (C : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule C) (n : ℤ)
    (f : Cochain M.toCochainComplex M.toCochainComplex n) (x : M.M) :
    totalizeCochain C M (n + 1) (δ n (n + 1) f) x =
      M.d (totalizeCochain C M n f x) +
        ((n + 1).negOnePow : ℤ) • totalizeCochain C M n f (M.d x) := by
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp [totalizeCochain]
  | add x y hx hy =>
    simp only [map_add, hx, hy, smul_add]
    abel
  | @homogeneous p x =>
    let x' : M.grading p := x
    have hx := totalizeCochain_apply C M n p f x'
    have hδ := δ_v (n := n) (m := n + 1) (by omega) f p (p + n + 1) (by omega) (p + n) (p + 1)
      (by omega) rfl
    have hdx : M.d (x : M.M) = (M.gradedDifferential p x' : M.M) := rfl
    have hδeval := congrArg
      (fun (g : M.toCochainComplex.X p ⟶ M.toCochainComplex.X (p + n + 1)) =>
        (M.grading (p + n + 1)).subtype (g x')) hδ
    calc
      _ = (M.grading (p + n + 1)).subtype
          (((δ n (n + 1) f).v p (p + n + 1) (by omega)).hom x') :=
        totalizeCochain_apply_of_eq C M (n + 1) p (p + n + 1) (by omega) (δ n (n + 1) f) x'
      _ = (M.grading (p + n + 1)).subtype
          (((f.v p (p + n) rfl ≫ M.toCochainComplex.d (p + n) (p + n + 1)) +
            (n + 1).negOnePow •
              (M.toCochainComplex.d p (p + 1) ≫ f.v (p + 1) (p + n + 1) (by omega))) x') := hδeval
      _ = _ := by
        rw [hx, hdx, totalizeCochain_apply_of_eq C M n (p + 1) (p + n + 1) (by omega) f
          (M.gradedDifferential p x')]
        simp only [DifferentialGradedModule.toCochainComplex_d,
          DifferentialGradedModule.toCochainComplex_X]
        rfl

/-- A right `C`-linear cochain assembles to a right `C`-linear endomorphism. -/
theorem totalizeCochain_rightLinear (C : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule C) (n : ℤ)
    (f : Cochain M.toCochainComplex M.toCochainComplex n)
    (hf : IsRightLinearCochain C M f) {q : ℤ} (b : C.grading q) (x : M.M) :
    totalizeCochain C M n f (MulOpposite.op (b : C.A) • x) =
      MulOpposite.op (b : C.A) • totalizeCochain C M n f x := by
  rcases hf with ⟨g, hg⟩
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp [totalizeCochain]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | @homogeneous p x =>
    let xb : M.grading (p + q) :=
      ⟨MulOpposite.op (b : C.A) • (x : M.M), M.smul_mem p q x b x.property b.property⟩
    rw [totalizeCochain_apply C M n (p + q) f xb, totalizeCochain_apply C M n p f x]
    exact (hg (p + q) xb).trans ((g.property.2 (b : C.A) x).trans
      (congrArg (MulOpposite.op (b : C.A) • ·) (hg p x).symm))

/-- Two endomorphisms of `M` are equal if they agree on every homogeneous element. -/
private theorem totalizeCochain_ext (C : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule C) (f g : M.M →ₗ[R] M.M)
    (h : ∀ (p : ℤ) (x : M.grading p), f x = g x) : f = g :=
  DirectSum.decompose_lhom_ext M.grading fun p => LinearMap.ext fun x => h p x

/-- The assembly is additive in the cochain. -/
theorem totalizeCochain_add (C : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule C) (n : ℤ)
    (f g : Cochain M.toCochainComplex M.toCochainComplex n) :
    totalizeCochain C M n (f + g) = totalizeCochain C M n f + totalizeCochain C M n g := by
  refine totalizeCochain_ext C M _ _ fun p x => ?_
  simp only [totalizeCochain_apply]
  rw [Cochain.add_v]
  simp only [ModuleCat.hom_add, LinearMap.add_apply]
  have hf := totalizeCochain_apply C M n p f x
  have hg := totalizeCochain_apply C M n p g x
  rw [hf, hg]
  exact (M.grading (p + n)).subtype.map_add _ _

/-- The assembly is `R`-linear in the cochain. -/
theorem totalizeCochain_smul (C : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule C) (n : ℤ) (r : R)
    (f : Cochain M.toCochainComplex M.toCochainComplex n) :
    totalizeCochain C M n (r • f) = r • totalizeCochain C M n f := by
  refine totalizeCochain_ext C M _ _ fun p x => ?_
  simp only [totalizeCochain_apply]
  rw [Cochain.smul_v]
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
  have hf := totalizeCochain_apply C M n p f x
  rw [hf]
  exact (M.grading (p + n)).subtype.map_smul r _

/-- The assembly turns composition of cochains into composition of endomorphisms, in the opposite
order. -/
theorem totalizeCochain_comp (C : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule C) (n m q : ℤ) (hnm : n + m = q)
    (f : Cochain M.toCochainComplex M.toCochainComplex n)
    (g : Cochain M.toCochainComplex M.toCochainComplex m) :
    totalizeCochain C M q (f.comp g hnm) =
      totalizeCochain C M m g ∘ₗ totalizeCochain C M n f := by
  cases hnm
  refine totalizeCochain_ext C M _ _ fun p x => ?_
  let x' : M.toCochainComplex.X p := x
  let y : M.grading (p + n) := (f.v p (p + n) rfl).hom x'
  have hf := totalizeCochain_apply C M n p f x
  have hc := Cochain.comp_v f g (rfl : n + m = n + m) p (p + n) (p + n + m) rfl (by omega)
  have hc'' : ((f.comp g rfl).v p (p + n + m) (by omega)).hom x' =
      (g.v (p + n) (p + n + m) (by omega)).hom ((f.v p (p + n) rfl).hom x') :=
    congrArg (fun h => h x') hc
  calc
    _ = (M.grading (p + n + m)).subtype
        (((f.comp g rfl).v p (p + n + m) (by omega)).hom x') :=
      totalizeCochain_apply_of_eq C M (n + m) p (p + n + m) (by omega) (f.comp g rfl) x
    _ = (M.grading (p + n + m)).subtype
        ((g.v (p + n) (p + n + m) (by omega)).hom ((f.v p (p + n) rfl).hom x')) :=
      congrArg (M.grading (p + n + m)).subtype hc''
    _ = totalizeCochain C M m g y :=
      (totalizeCochain_apply_of_eq C M m (p + n) (p + n + m) (by omega) g y).symm
    _ = totalizeCochain C M m g (totalizeCochain C M n f x) :=
      congrArg (totalizeCochain C M m g) hf.symm
    _ = _ := rfl

/-- The identity cochain assembles to the identity. -/
theorem totalizeCochain_id (C : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule C) :
    totalizeCochain C M 0 (Cochain.ofHom (𝟙 M.toCochainComplex)) = LinearMap.id := by
  refine totalizeCochain_ext C M _ _ fun p x => ?_
  calc
    totalizeCochain C M 0 (Cochain.ofHom (𝟙 M.toCochainComplex)) x =
        (M.grading p).subtype
          (((Cochain.ofHom (𝟙 M.toCochainComplex)).v p p (by omega)).hom x) :=
      totalizeCochain_apply_of_eq C M 0 p p (by omega)
        (Cochain.ofHom (𝟙 M.toCochainComplex)) x
    _ = (x : M.M) := by
      simp [Cochain.ofHom_v, HomologicalComplex.id_f,
        DifferentialGradedModule.toCochainComplex_X]
      rfl

/-- The assembly, as an `R`-linear map on cochains. -/
noncomputable def totalizeCochainLinear (C : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule C) (n : ℤ) :
    Cochain M.toCochainComplex M.toCochainComplex n →ₗ[R] (M.M →ₗ[R] M.M) where
  toFun := totalizeCochain C M n
  map_add' := totalizeCochain_add C M n
  map_smul' := totalizeCochain_smul C M n

/-- The right action of `C` on `M`, as an algebra homomorphism into the opposite of the
endomorphism algebra of `M`. -/
noncomputable def rightActionAlgHom (C : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule C) : C.A →ₐ[R] MulOpposite (Module.End R M.M) where
  toFun a := MulOpposite.op
    { toFun := fun x => MulOpposite.op a • x
      map_add' := smul_add _
      map_smul' r x := (smul_comm r (MulOpposite.op a) x).symm }
  map_zero' := MulOpposite.unop_injective <| LinearMap.ext fun _ => zero_smul _ _
  map_add' _ _ := MulOpposite.unop_injective <| LinearMap.ext fun _ => add_smul _ _ _
  map_one' := by
    apply MulOpposite.unop_injective
    ext x
    simp
  map_mul' := by
    intro a b
    apply MulOpposite.unop_injective
    ext x
    change MulOpposite.op (a * b) • x = _
    rw [MulOpposite.op_mul]
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op]
    exact (smul_smul (MulOpposite.op b) (MulOpposite.op a) x).symm
  commutes' := by
    intro r
    apply MulOpposite.unop_injective
    ext x
    change MulOpposite.op (algebraMap R C.A r) • x = _
    simpa [Algebra.smul_def] using (smul_assoc r (1 : MulOpposite C.A) x)

/-- The endomorphism underlying `rightActionAlgHom C M a` is the right action of `a`. -/
@[simp]
theorem rightActionAlgHom_apply (C : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule C) (a : C.A) (x : M.M) :
    MulOpposite.unop (rightActionAlgHom C M a) x = MulOpposite.op a • x := rfl

end DifferentialGradedModule

namespace DifferentialGraded

variable (A : DifferentialGradedAlgebra R) (B : DifferentialGradedAlgebra R)

open DifferentialGradedModule

/-- The map `A → End_R(M)` assembled from a left differential graded action of `A` on the complex
underlying a right differential graded `B`-module `M`. -/
noncomputable def leftActionTotal (M : DifferentialGradedModule B)
    (L : A.LeftAction M.toCochainComplex) : A.A →ₗ[R] M.M →ₗ[R] M.M := by
  let pieces : ∀ n : ℤ, A.grading n →ₗ[R] (M.M →ₗ[R] M.M) := fun n =>
    (totalizeCochainLinear B M n).comp (L.action n)
  exact (DirectSum.toModule R ℤ (M.M →ₗ[R] M.M) pieces).comp
    (DirectSum.decomposeLinearEquiv A.grading).toLinearMap

/-- On a homogeneous element, `leftActionTotal` is the totalization of its action. -/
theorem leftActionTotal_apply (M : DifferentialGradedModule B)
    (L : A.LeftAction M.toCochainComplex) (n : ℤ) (a : A.grading n) :
    leftActionTotal A B M L (a : A.A) = totalizeCochain B M n (L.action n a) := by
  simp [leftActionTotal, totalizeCochainLinear, DirectSum.toModule_lof,
    DirectSum.decomposeLinearEquiv_apply_coe]

/-- A homogeneous element of degree `n` sends `M^p` into `M^{p+n}`. -/
theorem leftActionTotal_apply_mem (M : DifferentialGradedModule B)
    (L : A.LeftAction M.toCochainComplex) {n p : ℤ} (a : A.grading n) (x : M.grading p) :
    leftActionTotal A B M L (a : A.A) x ∈ M.grading (p + n) := by
  rw [leftActionTotal_apply A B M L n a, totalizeCochain_apply B M n p (L.action n a) x]
  exact ((L.action n a).v p (p + n) (by omega) x).property

/-- The graded Leibniz rule for `leftActionTotal`: for `a` of degree `n`,
`d (a x) = (d a) x + (-1)^n a (d x)`. -/
theorem leftActionTotal_leibniz (M : DifferentialGradedModule B)
    (L : A.LeftAction M.toCochainComplex) {n : ℤ} (a : A.grading n) (x : M.M) :
    M.d (leftActionTotal A B M L (a : A.A) x) =
      leftActionTotal A B M L (A.d a) x +
        (n.negOnePow : ℤ) • leftActionTotal A B M L (a : A.A) (M.d x) := by
  let da : A.grading (n + 1) := ⟨A.d a, A.d_mem n a a.property⟩
  have hmap := congrArg (totalizeCochain B M (n + 1)) (L.map_d n a)
  have hmapx := congrArg (fun f : M.M →ₗ[R] M.M => f x) hmap
  have hδx := totalizeCochain_delta_apply B M n (L.action n a) x
  rw [hδx] at hmapx
  have hsZ : ((n + 1).negOnePow : ℤ) = -(n.negOnePow : ℤ) := by
    rw [Int.negOnePow_add]
    simp
  rw [leftActionTotal_apply A B M L n a, leftActionTotal_apply A B M L (n + 1) da]
  rw [hmapx, hsZ]
  simp only [neg_zsmul]
  abel

/-- If every homogeneous action is right `B`-linear, then `leftActionTotal` commutes with the
right action of homogeneous elements of `B`. -/
theorem leftActionTotal_commutes (M : DifferentialGradedModule B)
    (L : A.LeftAction M.toCochainComplex)
    (hL : ∀ (n : ℤ) (a : A.grading n), IsRightLinearCochain B M (L.action n a))
    {n : ℤ} (a : A.grading n) {q : ℤ} (b : B.grading q) (x : M.M) :
    leftActionTotal A B M L (a : A.A) (MulOpposite.op (b : B.A) • x) =
      MulOpposite.op (b : B.A) • leftActionTotal A B M L (a : A.A) x := by
  rw [leftActionTotal_apply A B M L n a]
  exact totalizeCochain_rightLinear B M n (L.action n a) (hL n a) b x

/-- On a product of homogeneous elements, `leftActionTotal` is the product of the
totalizations of their actions. -/
theorem leftActionTotal_mul (M : DifferentialGradedModule B)
    (L : A.LeftAction M.toCochainComplex) {n m : ℤ} (a : A.grading n) (b : A.grading m) :
    leftActionTotal A B M L ((a : A.A) * (b : A.A)) =
      totalizeCochain B M n (L.action n a) * totalizeCochain B M m (L.action m b) := by
  rw [Module.End.mul_eq_comp,
    ← totalizeCochain_comp B M m n (n + m) (by omega) (L.action m b) (L.action n a), ← L.map_mul]
  exact leftActionTotal_apply A B M L (n + m) ⟨_, SetLike.mul_mem_graded a.property b.property⟩

/-- `leftActionTotal` sends the unit to the identity. -/
theorem leftActionTotal_one (M : DifferentialGradedModule B)
    (L : A.LeftAction M.toCochainComplex) :
    leftActionTotal A B M L 1 = LinearMap.id := by
  rw [← totalizeCochain_id B M, ← L.map_one]
  exact leftActionTotal_apply A B M L 0 ⟨1, SetLike.one_mem_graded A.grading⟩

/-- The algebra homomorphism `A → End_R(M)` attached to a left differential graded action. -/
noncomputable def leftActionAlgHom (M : DifferentialGradedModule B)
    (L : A.LeftAction M.toCochainComplex) : A.A →ₐ[R] Module.End R M.M :=
  AlgHom.ofLinearMap (leftActionTotal A B M L) (leftActionTotal_one A B M L) (by
    intro a b
    induction a using DirectSum.Decomposition.inductionOn A.grading with
    | zero => simp
    | add a b ha hb => simp [map_add, ha, hb, add_mul]
    | @homogeneous n a =>
      induction b using DirectSum.Decomposition.inductionOn A.grading with
      | zero => simp
      | add b c hb hc => simp [map_add, hb, hc, mul_add]
      | @homogeneous m b =>
        simpa only [leftActionTotal_apply A B M L n a, leftActionTotal_apply A B M L m b] using
          leftActionTotal_mul A B M L a b)

/-- Transport an algebra homomorphism into the opposite endomorphism algebra along a linear
equivalence. -/
noncomputable def transportRightActionAlgHom {C : DifferentialGradedAlgebra R} {X Y : Type u}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] (e : X ≃ₗ[R] Y)
    (F : C.A →ₐ[R] MulOpposite (Module.End R X)) : C.A →ₐ[R] MulOpposite (Module.End R Y) :=
  (e.conjAlgEquiv R).op.toAlgHom.comp F

/-- The transported action of `a` on `y` is `e (F a (e.symm y))`. -/
theorem transportRightActionAlgHom_apply {C : DifferentialGradedAlgebra R} {X Y : Type u}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] (e : X ≃ₗ[R] Y)
    (F : C.A →ₐ[R] MulOpposite (Module.End R X)) (a : C.A) (y : Y) :
    MulOpposite.unop (transportRightActionAlgHom e F a) y =
      e (MulOpposite.unop (F a) (e.symm y)) := by
  simp [transportRightActionAlgHom, LinearEquiv.conjAlgEquiv_apply]

/-- A `ℤˣ`-power of `-1` acting on an element of the opposite endomorphism algebra acts on the
values. -/
theorem unop_units_smul_apply {X : Type u} [AddCommGroup X] [Module R X] (k : ℤ)
    (z : MulOpposite (Module.End R X)) (x : X) :
    MulOpposite.unop ((-1 : ℤˣ) ^ k • z) x = k.negOnePow • MulOpposite.unop z x := by
  simp [Units.smul_def, Int.negOnePow_def]

/-- The ring homomorphism `Cᵐᵒᵖ → End_R(X)` underlying an algebra homomorphism into the opposite
endomorphism algebra. -/
def actionRingHom (C : DifferentialGradedAlgebra R) (X : Type u) [AddCommGroup X] [Module R X]
    (F : C.A →ₐ[R] MulOpposite (Module.End R X)) : MulOpposite C.A →+* Module.End R X where
  toFun a := MulOpposite.unop (F (MulOpposite.unop a))
  map_one' := by simp
  map_mul' := by
    intro a b
    change MulOpposite.unop (F (MulOpposite.unop b * MulOpposite.unop a)) = _
    rw [map_mul]
    simp only [MulOpposite.unop_mul]
  map_zero' := by simp
  map_add' := by intro a b; simp

/-- The right `C`-module structure on `X` defined by an algebra homomorphism into the opposite
endomorphism algebra. -/
noncomputable abbrev moduleOfAlgHom (C : DifferentialGradedAlgebra R) (X : Type u)
    [AddCommGroup X] [Module R X] (F : C.A →ₐ[R] MulOpposite (Module.End R X)) :
    Module (MulOpposite C.A) X :=
  Module.compHom X (actionRingHom C X F)

/-- In the module structure `moduleOfAlgHom C X F`, `a` acts through `F`. -/
theorem moduleOfAlgHom_smul (C : DifferentialGradedAlgebra R) (X : Type u) [AddCommGroup X]
    [Module R X] (F : C.A →ₐ[R] MulOpposite (Module.End R X)) (a : MulOpposite C.A) (x : X) :
    letI := moduleOfAlgHom C X F
    a • x = MulOpposite.unop (F (MulOpposite.unop a)) x := rfl

/-- The module structure `moduleOfAlgHom C X F` is compatible with the `R`-module structure of
`X`. -/
theorem moduleOfAlgHom_isScalarTower (C : DifferentialGradedAlgebra R) (X : Type u)
    [AddCommGroup X] [Module R X] (F : C.A →ₐ[R] MulOpposite (Module.End R X)) :
    letI := moduleOfAlgHom C X F
    IsScalarTower R (MulOpposite C.A) X := by
  let _ := (moduleOfAlgHom C X F : Module (MulOpposite C.A) X)
  constructor
  intro r a x
  change (actionRingHom C X F (r • a)) x = r • ((actionRingHom C X F a) x)
  simp [actionRingHom, map_smul]

/-- Two algebra homomorphisms into the opposite endomorphism algebra of `X` that commute up to the
Koszul sign extend to the graded tensor product. -/
noncomputable def liftTensorActionAlgHom {C D : DifferentialGradedAlgebra R} (X : Type u)
    [AddCommGroup X] [Module R X] (f : C.A →ₐ[R] MulOpposite (Module.End R X))
    (g : D.A →ₐ[R] MulOpposite (Module.End R X))
    (h : ∀ ⦃i j⦄ (a : C.grading i) (b : D.grading j),
      f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a)) :
    (DifferentialGradedAlgebra.tensorProduct C D).A →ₐ[R] MulOpposite (Module.End R X) :=
  GradedTensorProduct.lift C.grading D.grading f g h

/-- In the module structure defined by `liftTensorActionAlgHom X f g h`, a pure tensor `a ⊗ b`
acts on `x` by `f a` followed by `g b`. -/
theorem liftedTensorAction_smul_tmul {C D : DifferentialGradedAlgebra R} (X : Type u)
    [AddCommGroup X] [Module R X] (f : C.A →ₐ[R] MulOpposite (Module.End R X))
    (g : D.A →ₐ[R] MulOpposite (Module.End R X))
    (h : ∀ ⦃i j⦄ (a : C.grading i) (b : D.grading j),
      f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a))
    (a : C.A) (b : D.A) (x : X) :
    let F := liftTensorActionAlgHom X f g h
    letI := moduleOfAlgHom (DifferentialGradedAlgebra.tensorProduct C D) X F
    (MulOpposite.op (GradedTensorProduct.tmul (R := R) (𝒜 := C.grading) (ℬ := D.grading) a b :
        (DifferentialGradedAlgebra.tensorProduct C D).A) :
        MulOpposite (DifferentialGradedAlgebra.tensorProduct C D).A) • x =
      MulOpposite.unop (g b) (MulOpposite.unop (f a) x) := by
  change MulOpposite.unop ((liftTensorActionAlgHom X f g h)
    (GradedTensorProduct.tmul (R := R) (𝒜 := C.grading) (ℬ := D.grading) a b)) x = _
  rw [liftTensorActionAlgHom, GradedTensorProduct.lift_tmul, MulOpposite.unop_mul]
  rfl

end DifferentialGraded
