module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedOppositeAlgebra
public import StacksCore.Tactic.StacksAttribute

/-!
# Left differential graded modules as right modules over the opposite algebra

Let `R` be a sheaf of rings on a site, let `A` be a sheaf of differential graded `R`-algebras
and let `A.op` be its opposite. Interchanging the two factors of an action and twisting by the
Koszul sign turns a left differential graded `A`-module into a right differential graded
`A.op`-module and back:

`x ⬝ a = (-1)^{n m} a x` for `a` of degree `n` and `x` of degree `m`.

This file records the three instances of that interchange which the left-module half of
Tag 0FSH uses: a left differential graded `A`-module read as a right differential graded
`A.op`-module, a right differential graded `A`-module read as a left differential graded
`A.op`-module, and a right differential graded `A.op`-module read as a left differential graded
`A`-module. Each keeps the underlying cochain complex, so acyclicity and quasi-isomorphy are
unchanged by all three.

## Main definitions

* `SheafOfModules.LeftDifferentialGradedModule.opRight` reads a left differential graded
  `A`-module as a right differential graded `A.op`-module.
* `SheafOfModules.DifferentialGradedModule.opLeft` reads a right differential graded `A`-module
  as a left differential graded `A.op`-module.
* `SheafOfModules.DifferentialGradedModule.unopLeft` reads a right differential graded
  `A.op`-module as a left differential graded `A`-module, and
  `SheafOfModules.DifferentialGradedModule.Hom.unopLeft` carries a homomorphism of right
  differential graded `A.op`-modules into the target of `opRight` to a homomorphism of left
  differential graded `A`-modules.

## Main results

* `SheafOfModules.LeftDifferentialGradedModule.opRightMul_leibniz`,
  `SheafOfModules.DifferentialGradedModule.opLeftMul_leibniz` and
  `SheafOfModules.DifferentialGradedModule.unopLeftMul_leibniz` are the signed Leibniz rules of
  the three interchanged actions: the Koszul sign is exactly what makes them hold.
* `SheafOfModules.DifferentialGradedModule.Hom.unopLeft_toHomologicalComplex`: the interchange
  leaves the underlying morphism of cochain complexes alone.

## Implementation notes

`Hom.unopLeft` goes from `Q ⟶ N.opRight` to `Q.unopLeft ⟶ N` rather than to
`Q.unopLeft ⟶ (N.opRight).unopLeft`, so that no equality of structures has to be proved: the two
actions differ by the Koszul sign applied twice and by two transports of degrees which compose
to the identity, and that cancellation is discharged inside the one `map_mul` obligation.

Each of the three actions is defined by transporting a flipped, sign-twisted bilinear map along
the commutativity of the two degrees, as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedOppositeAlgebra.lean`; the
bilinearity is then inherited and the `*_app_heq` lemmas are the only computation rules the
laws need.

## References

* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
-/

@[expose] public section

open CategoryTheory

universe t a w v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- A degreewise morphism of cochain complexes of sheaves of modules commutes with transport
along an equality of degrees. -/
theorem gradedCast_hom_f_app {M N : CochainComplex (SheafOfModules.{w} R) ℤ} (φ : M ⟶ N)
    {j k : ℤ} (h : j = k) (U : Cᵒᵖ) (x : (M.X j).val.obj U) :
    (φ.f k).val.app U (gradedCast (fun q ↦ (M.X q).val.obj U) h x) =
      gradedCast (fun q ↦ (N.X q).val.obj U) h ((φ.f j).val.app U x) := by
  cases h
  rfl

/-- A degreewise morphism of cochain complexes of sheaves of modules commutes with integer
multiples. -/
theorem hom_f_app_zsmul {M N : CochainComplex (SheafOfModules.{w} R) ℤ} (φ : M ⟶ N) (k : ℤ)
    (U : Cᵒᵖ) (ε : ℤ) (x : (M.X k).val.obj U) :
    (φ.f k).val.app U (ε • x) = ε • (φ.f k).val.app U x :=
  map_zsmul (ConcreteCategory.hom ((φ.f k).val.app U)) ε x

/-- The product of a sign with itself is one. -/
theorem negOnePow_mul_negOnePow (k : ℤ) :
    (Int.negOnePow k : ℤ) * (Int.negOnePow k : ℤ) = 1 := by
  rw [← Units.val_mul, ← Int.negOnePow_add, Units.val_eq_one]
  exact Int.negOnePow_even _ ⟨k, rfl⟩

/-- Transport along an equality of a degree with itself is the identity. -/
theorem gradedCast_self {ι : Type*} (T : ι → Type*) {i : ι} (h : i = i) (x : T i) :
    gradedCast T h x = x := rfl

/-- Shifting the first factor of a product by one multiplies the sign by the sign of the other
factor. -/
private theorem negOnePow_succ_mul (n p : ℤ) :
    (Int.negOnePow ((n + 1) * p) : ℤ) = (Int.negOnePow (n * p) : ℤ) * (Int.negOnePow p : ℤ) := by
  rw [← Units.val_mul, ← Int.negOnePow_add]
  congr 2
  ring

/-- The sign of a degree and the sign of its product with a shifted degree combine to the sign of
the unshifted product. -/
private theorem negOnePow_mul_negOnePow_mul_succ (n p : ℤ) :
    (Int.negOnePow n : ℤ) * (Int.negOnePow (n * (p + 1)) : ℤ) = (Int.negOnePow (n * p) : ℤ) := by
  rw [← Units.val_mul, ← Int.negOnePow_add, show n + n * (p + 1) = n * p + 2 * n by ring,
    Int.negOnePow_add, Int.negOnePow_two_mul, _root_.mul_one]

variable {A : DifferentialGradedAlgebra.{t, a} R}

namespace LeftDifferentialGradedModule

variable (N : LeftDifferentialGradedModule.{t, a, w} A)

/-! ### A left `A`-module as a right `A.op`-module -/

/-- The right action of `A.op` on a left differential graded `A`-module: the action of `A` with
its two factors interchanged, twisted by the Koszul sign and transported from degree `n + p` to
degree `p + n`. -/
noncomputable def opRightMul (p n : ℤ) :
    BilinearMap (N.complex.X p) (A.complex.X n) (N.complex.X (p + n)) :=
  gradedCast (fun k ↦ BilinearMap (N.complex.X p) (A.complex.X n) (N.complex.X k))
    (Int.add_comm n p) ((N.mul n p).flip.intSmul (Int.negOnePow (n * p)))

/-- The value of the interchanged right action on homogeneous local sections. -/
theorem opRightMul_app (p n : ℤ) (U : Cᵒᵖ) (x : (N.complex.X p).val.obj U)
    (α : (A.complex.X n).val.obj U) :
    (N.opRightMul p n).app U x α =
      gradedCast (fun k ↦ (N.complex.X k).val.obj U) (Int.add_comm n p)
        ((Int.negOnePow (n * p) : ℤ) • (N.mul n p).app U α x) :=
  gradedCast_bilinearMap_app (E := N.complex.X) _ _ _ _ _

/-- The value of the interchanged right action, read as a heterogeneous equality with the
untransported local section. -/
theorem opRightMul_app_heq (p n : ℤ) (U : Cᵒᵖ) (x : (N.complex.X p).val.obj U)
    (α : (A.complex.X n).val.obj U) :
    (N.opRightMul p n).app U x α ≍ (Int.negOnePow (n * p) : ℤ) • (N.mul n p).app U α x := by
  rw [N.opRightMul_app]
  exact gradedCast_heq _ _ _

/-- The interchanged right action is associative with the multiplication of `A.op`. -/
theorem opRightMul_assoc (p n r : ℤ) (U : Cᵒᵖ) (x : (N.complex.X p).val.obj U)
    (α : (A.complex.X n).val.obj U) (β : (A.complex.X r).val.obj U) :
    (N.opRightMul (p + n) r).app U ((N.opRightMul p n).app U x α) β ≍
      (N.opRightMul p (n + r)).app U x ((A.opMul n r).app U α β) := by
  refine HEq.trans (N.opRightMul_app_heq (p + n) r U _ β) ?_
  refine HEq.trans ?_ (N.opRightMul_app_heq p (n + r) U x _).symm
  have hleft : (N.mul r (p + n)).app U β ((N.opRightMul p n).app U x α) ≍
      (Int.negOnePow (n * p) : ℤ) • (N.mul r (n + p)).app U β ((N.mul n p).app U α x) := by
    refine HEq.trans (heq_dependent_apply
      (fun k (y : (N.complex.X k).val.obj U) ↦ (N.mul r k).app U β y)
      (Int.add_comm p n) (N.opRightMul_app_heq p n U x α)) ?_
    exact heq_of_eq ((N.mul r (n + p)).app_zsmul_right _ _ _ _)
  have hright : (N.mul (n + r) p).app U ((A.opMul n r).app U α β) x ≍
      (Int.negOnePow (n * r) : ℤ) • (N.mul (r + n) p).app U ((A.mul r n).app U β α) x := by
    refine HEq.trans (heq_dependent_apply
      (fun k (y : (A.complex.X k).val.obj U) ↦ (N.mul k p).app U y x)
      (Int.add_comm n r) (A.opMul_app_heq n r U α β)) ?_
    exact heq_of_eq ((N.mul (r + n) p).app_zsmul_left _ _ _ _)
  refine HEq.trans (heq_zsmul (fun q ↦ (N.complex.X q).val.obj U)
    (congrArg (fun k ↦ r + k) (Int.add_comm p n)) _ hleft) ?_
  refine HEq.trans ?_ (heq_zsmul (fun q ↦ (N.complex.X q).val.obj U)
    (congrArg (fun k ↦ k + p) (Int.add_comm n r)) _ hright).symm
  have hmid : (N.mul r (n + p)).app U β ((N.mul n p).app U α x) ≍
      (N.mul (r + n) p).app U ((A.mul r n).app U β α) x := (N.mul_assoc r n p U β α x).symm
  refine HEq.trans (heq_zsmul (fun q ↦ (N.complex.X q).val.obj U) (add_assoc r n p).symm _
    (heq_zsmul (fun q ↦ (N.complex.X q).val.obj U) (add_assoc r n p).symm _ hmid)) ?_
  refine heq_of_eq ?_
  rw [smul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul, ← Int.negOnePow_add,
    ← Int.negOnePow_add]
  congr 2
  ring_nf

/-- The unit of `A.op` acts as the identity for the interchanged right action. -/
theorem opRightMul_mul_one (p : ℤ) (U : Cᵒᵖ) (x : (N.complex.X p).val.obj U) :
    (N.opRightMul p 0).app U x (A.one.eval U) ≍ x := by
  refine HEq.trans (N.opRightMul_app_heq p 0 U x (A.one.eval U)) ?_
  rw [Int.zero_mul, Int.negOnePow_zero, Units.val_one, one_zsmul]
  exact N.one_mul p U x

/-- **The signed Leibniz rule for the interchanged right action.** -/
theorem opRightMul_leibniz (p n : ℤ) (U : Cᵒᵖ) (x : (N.complex.X p).val.obj U)
    (α : (A.complex.X n).val.obj U) :
    (N.complex.d (p + n) (p + n + 1)).val.app U ((N.opRightMul p n).app U x α) =
      gradedCast (fun q ↦ (N.complex.X q).val.obj U) (add_right_comm p 1 n)
          ((N.opRightMul (p + 1) n).app U ((N.complex.d p (p + 1)).val.app U x) α) +
        (Int.negOnePow p : ℤ) •
          gradedCast (fun q ↦ (N.complex.X q).val.obj U) (add_assoc p n 1).symm
            ((N.opRightMul p (n + 1)).app U x ((A.complex.d n (n + 1)).val.app U α)) := by
  have hsign₁ : (Int.negOnePow (n * (p + 1)) : ℤ) =
      (Int.negOnePow (n * p) : ℤ) * (Int.negOnePow n : ℤ) := by
    simpa only [mul_comm] using negOnePow_succ_mul p n
  have hsign₂ : (Int.negOnePow p : ℤ) * (Int.negOnePow ((n + 1) * p) : ℤ) =
      (Int.negOnePow (n * p) : ℤ) := by
    simpa only [mul_comm] using negOnePow_mul_negOnePow_mul_succ p n
  simp only [N.opRightMul_app, gradedCast_d_app, d_app_zsmul, N.leibniz n p U α x,
    gradedCast_smul, gradedCast_add, gradedCast_trans, smul_add, smul_smul]
  rw [hsign₁, hsign₂]
  abel

/-- **A left differential graded `A`-module read as a right differential graded
`A.op`-module.** The cochain complex is unchanged and the action is interchanged and twisted by
the Koszul sign. -/
@[stacks 0FRI "left differential graded modules as right modules over the opposite algebra"]
noncomputable def opRight : DifferentialGradedModule.{t, a, w} A.op where
  complex := N.complex
  mul := N.opRightMul
  mul_assoc := N.opRightMul_assoc
  mul_one := N.opRightMul_mul_one
  leibniz := N.opRightMul_leibniz

/-- The cochain complex underlying `N.opRight` is that of `N`. -/
@[simp] theorem opRight_complex : N.opRight.complex = N.complex := rfl

/-- The right action of `A.op` on `N.opRight` is `N.opRightMul`. -/
@[simp] theorem opRight_mul (p n : ℤ) : N.opRight.mul p n = N.opRightMul p n := rfl

end LeftDifferentialGradedModule

namespace DifferentialGradedModule

/-! ### A right `A`-module as a left `A.op`-module -/

variable (M : DifferentialGradedModule.{t, a, w} A)

/-- The left action of `A.op` on a right differential graded `A`-module: the action of `A` with
its two factors interchanged, twisted by the Koszul sign and transported from degree `p + n` to
degree `n + p`. -/
noncomputable def opLeftMul (n p : ℤ) :
    BilinearMap (A.complex.X n) (M.complex.X p) (M.complex.X (n + p)) :=
  gradedCast (fun k ↦ BilinearMap (A.complex.X n) (M.complex.X p) (M.complex.X k))
    (Int.add_comm p n) ((M.mul p n).flip.intSmul (Int.negOnePow (n * p)))

/-- The value of the interchanged left action on homogeneous local sections. -/
theorem opLeftMul_app (n p : ℤ) (U : Cᵒᵖ) (α : (A.complex.X n).val.obj U)
    (x : (M.complex.X p).val.obj U) :
    (M.opLeftMul n p).app U α x =
      gradedCast (fun k ↦ (M.complex.X k).val.obj U) (Int.add_comm p n)
        ((Int.negOnePow (n * p) : ℤ) • (M.mul p n).app U x α) :=
  gradedCast_bilinearMap_app (E := M.complex.X) _ _ _ _ _

/-- The value of the interchanged left action, read as a heterogeneous equality with the
untransported local section. -/
theorem opLeftMul_app_heq (n p : ℤ) (U : Cᵒᵖ) (α : (A.complex.X n).val.obj U)
    (x : (M.complex.X p).val.obj U) :
    (M.opLeftMul n p).app U α x ≍ (Int.negOnePow (n * p) : ℤ) • (M.mul p n).app U x α := by
  rw [M.opLeftMul_app]
  exact gradedCast_heq _ _ _

/-- The interchanged left action is associative with the multiplication of `A.op`. -/
theorem opLeftMul_assoc (n r p : ℤ) (U : Cᵒᵖ) (α : (A.complex.X n).val.obj U)
    (β : (A.complex.X r).val.obj U) (x : (M.complex.X p).val.obj U) :
    (M.opLeftMul (n + r) p).app U ((A.opMul n r).app U α β) x ≍
      (M.opLeftMul n (r + p)).app U α ((M.opLeftMul r p).app U β x) := by
  refine HEq.trans (M.opLeftMul_app_heq (n + r) p U _ x) ?_
  refine HEq.trans ?_ (M.opLeftMul_app_heq n (r + p) U α _).symm
  have hleft : (M.mul p (n + r)).app U x ((A.opMul n r).app U α β) ≍
      (Int.negOnePow (n * r) : ℤ) • (M.mul p (r + n)).app U x ((A.mul r n).app U β α) := by
    refine HEq.trans (heq_dependent_apply
      (fun k (y : (A.complex.X k).val.obj U) ↦ (M.mul p k).app U x y)
      (Int.add_comm n r) (A.opMul_app_heq n r U α β)) ?_
    exact heq_of_eq ((M.mul p (r + n)).app_zsmul_right _ _ _ _)
  have hright : (M.mul (r + p) n).app U ((M.opLeftMul r p).app U β x) α ≍
      (Int.negOnePow (r * p) : ℤ) • (M.mul (p + r) n).app U ((M.mul p r).app U x β) α := by
    refine HEq.trans (heq_dependent_apply
      (fun k (y : (M.complex.X k).val.obj U) ↦ (M.mul k n).app U y α)
      (Int.add_comm r p) (M.opLeftMul_app_heq r p U β x)) ?_
    exact heq_of_eq ((M.mul (p + r) n).app_zsmul_left _ _ _ _)
  refine HEq.trans (heq_zsmul (fun q ↦ (M.complex.X q).val.obj U)
    (congrArg (fun k ↦ p + k) (Int.add_comm n r)) _ hleft) ?_
  refine HEq.trans ?_ (heq_zsmul (fun q ↦ (M.complex.X q).val.obj U)
    (congrArg (fun k ↦ k + n) (Int.add_comm r p)) _ hright).symm
  have hmid : (M.mul p (r + n)).app U x ((A.mul r n).app U β α) ≍
      (M.mul (p + r) n).app U ((M.mul p r).app U x β) α := (M.mul_assoc p r n U x β α).symm
  refine HEq.trans (heq_zsmul (fun q ↦ (M.complex.X q).val.obj U) (add_assoc p r n).symm _
    (heq_zsmul (fun q ↦ (M.complex.X q).val.obj U) (add_assoc p r n).symm _ hmid)) ?_
  refine heq_of_eq ?_
  rw [smul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul, ← Int.negOnePow_add,
    ← Int.negOnePow_add]
  congr 2
  ring_nf

/-- The unit of `A.op` acts as the identity for the interchanged left action. -/
theorem opLeftMul_one_mul (p : ℤ) (U : Cᵒᵖ) (x : (M.complex.X p).val.obj U) :
    (M.opLeftMul 0 p).app U (A.one.eval U) x ≍ x := by
  refine HEq.trans (M.opLeftMul_app_heq 0 p U (A.one.eval U) x) ?_
  rw [Int.zero_mul, Int.negOnePow_zero, Units.val_one, one_zsmul]
  exact M.mul_one p U x

/-- **The signed Leibniz rule for the interchanged left action.** -/
theorem opLeftMul_leibniz (n p : ℤ) (U : Cᵒᵖ) (α : (A.complex.X n).val.obj U)
    (x : (M.complex.X p).val.obj U) :
    (M.complex.d (n + p) (n + p + 1)).val.app U ((M.opLeftMul n p).app U α x) =
      gradedCast (fun q ↦ (M.complex.X q).val.obj U) (add_right_comm n 1 p)
          ((M.opLeftMul (n + 1) p).app U ((A.complex.d n (n + 1)).val.app U α) x) +
        (Int.negOnePow n : ℤ) •
          gradedCast (fun q ↦ (M.complex.X q).val.obj U) (add_assoc n p 1).symm
            ((M.opLeftMul n (p + 1)).app U α ((M.complex.d p (p + 1)).val.app U x)) := by
  simp only [M.opLeftMul_app, gradedCast_d_app, d_app_zsmul, M.leibniz p n U x α,
    gradedCast_smul, gradedCast_add, gradedCast_trans, smul_add, smul_smul]
  rw [negOnePow_succ_mul, negOnePow_mul_negOnePow_mul_succ]
  abel

/-- **A right differential graded `A`-module read as a left differential graded
`A.op`-module.** The cochain complex is unchanged and the action is interchanged and twisted by
the Koszul sign. -/
@[stacks 0FRI "right differential graded modules as left modules over the opposite algebra"]
noncomputable def opLeft : LeftDifferentialGradedModule.{t, a, w} A.op where
  complex := M.complex
  mul := M.opLeftMul
  mul_assoc := M.opLeftMul_assoc
  one_mul := M.opLeftMul_one_mul
  leibniz := M.opLeftMul_leibniz

/-- The cochain complex underlying `M.opLeft` is that of `M`. -/
@[simp] theorem opLeft_complex : M.opLeft.complex = M.complex := rfl

/-- The left action of `A.op` on `M.opLeft` is `M.opLeftMul`. -/
@[simp] theorem opLeft_mul (n p : ℤ) : M.opLeft.mul n p = M.opLeftMul n p := rfl

/-! ### A right `A.op`-module as a left `A`-module -/

variable (P : DifferentialGradedModule.{t, a, w} A.op)

/-- The left action of `A` on a right differential graded `A.op`-module: the action of `A.op`
with its two factors interchanged, twisted by the Koszul sign and transported from degree
`p + n` to degree `n + p`. -/
noncomputable def unopLeftMul (n p : ℤ) :
    BilinearMap (A.complex.X n) (P.complex.X p) (P.complex.X (n + p)) :=
  gradedCast (fun k ↦ BilinearMap (A.complex.X n) (P.complex.X p) (P.complex.X k))
    (Int.add_comm p n) ((P.mul p n).flip.intSmul (Int.negOnePow (n * p)))

/-- The value of the interchanged left action on homogeneous local sections. -/
theorem unopLeftMul_app (n p : ℤ) (U : Cᵒᵖ) (α : (A.complex.X n).val.obj U)
    (x : (P.complex.X p).val.obj U) :
    (P.unopLeftMul n p).app U α x =
      gradedCast (fun k ↦ (P.complex.X k).val.obj U) (Int.add_comm p n)
        ((Int.negOnePow (n * p) : ℤ) • (P.mul p n).app U x α) :=
  gradedCast_bilinearMap_app (E := P.complex.X) _ _ _ _ _

/-- The value of the interchanged left action, read as a heterogeneous equality with the
untransported local section. -/
theorem unopLeftMul_app_heq (n p : ℤ) (U : Cᵒᵖ) (α : (A.complex.X n).val.obj U)
    (x : (P.complex.X p).val.obj U) :
    (P.unopLeftMul n p).app U α x ≍ (Int.negOnePow (n * p) : ℤ) • (P.mul p n).app U x α := by
  rw [P.unopLeftMul_app]
  exact gradedCast_heq _ _ _

/-- The interchanged left action is associative with the multiplication of `A`. -/
theorem unopLeftMul_assoc (n r p : ℤ) (U : Cᵒᵖ) (α : (A.complex.X n).val.obj U)
    (β : (A.complex.X r).val.obj U) (x : (P.complex.X p).val.obj U) :
    (P.unopLeftMul (n + r) p).app U ((A.mul n r).app U α β) x ≍
      (P.unopLeftMul n (r + p)).app U α ((P.unopLeftMul r p).app U β x) := by
  refine HEq.trans (P.unopLeftMul_app_heq (n + r) p U _ x) ?_
  refine HEq.trans ?_ (P.unopLeftMul_app_heq n (r + p) U α _).symm
  have hright : (P.mul (r + p) n).app U ((P.unopLeftMul r p).app U β x) α ≍
      (Int.negOnePow (r * p) : ℤ) • (P.mul (p + r) n).app U ((P.mul p r).app U x β) α := by
    refine HEq.trans (heq_dependent_apply
      (fun k (y : (P.complex.X k).val.obj U) ↦ (P.mul k n).app U y α)
      (Int.add_comm r p) (P.unopLeftMul_app_heq r p U β x)) ?_
    exact heq_of_eq ((P.mul (p + r) n).app_zsmul_left _ _ _ _)
  have hmid : (P.mul (p + r) n).app U ((P.mul p r).app U x β) α ≍
      (Int.negOnePow (r * n) : ℤ) • (P.mul p (n + r)).app U x ((A.mul n r).app U α β) := by
    refine HEq.trans (P.mul_assoc p r n U x β α) ?_
    refine HEq.trans (heq_dependent_apply
      (fun k (y : (A.complex.X k).val.obj U) ↦ (P.mul p k).app U x y)
      (Int.add_comm r n) (A.opMul_app_heq r n U β α)) ?_
    exact heq_of_eq ((P.mul p (n + r)).app_zsmul_right _ _ _ _)
  refine HEq.trans ?_ (heq_zsmul (fun q ↦ (P.complex.X q).val.obj U)
    (congrArg (fun k ↦ k + n) (Int.add_comm r p)) _ hright).symm
  refine HEq.trans ?_ (heq_zsmul (fun q ↦ (P.complex.X q).val.obj U)
    ((add_assoc p r n).trans (congrArg (fun k ↦ p + k) (Int.add_comm r n))) _
    (heq_zsmul (fun q ↦ (P.complex.X q).val.obj U)
      ((add_assoc p r n).trans (congrArg (fun k ↦ p + k) (Int.add_comm r n))) _ hmid)).symm
  refine heq_of_eq ?_
  rw [smul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul, ← Int.negOnePow_add,
    ← Int.negOnePow_add, show n * (r + p) + r * p + r * n = (n + r) * p + 2 * (r * n) by ring,
    Int.negOnePow_add, Int.negOnePow_two_mul, _root_.mul_one]

/-- The unit of `A` acts as the identity for the interchanged left action. -/
theorem unopLeftMul_one_mul (p : ℤ) (U : Cᵒᵖ) (x : (P.complex.X p).val.obj U) :
    (P.unopLeftMul 0 p).app U (A.one.eval U) x ≍ x := by
  refine HEq.trans (P.unopLeftMul_app_heq 0 p U (A.one.eval U) x) ?_
  rw [Int.zero_mul, Int.negOnePow_zero, Units.val_one, one_zsmul]
  exact P.mul_one p U x

/-- **The signed Leibniz rule for the interchanged left action.** -/
theorem unopLeftMul_leibniz (n p : ℤ) (U : Cᵒᵖ) (α : (A.complex.X n).val.obj U)
    (x : (P.complex.X p).val.obj U) :
    (P.complex.d (n + p) (n + p + 1)).val.app U ((P.unopLeftMul n p).app U α x) =
      gradedCast (fun q ↦ (P.complex.X q).val.obj U) (add_right_comm n 1 p)
          ((P.unopLeftMul (n + 1) p).app U ((A.complex.d n (n + 1)).val.app U α) x) +
        (Int.negOnePow n : ℤ) •
          gradedCast (fun q ↦ (P.complex.X q).val.obj U) (add_assoc n p 1).symm
            ((P.unopLeftMul n (p + 1)).app U α ((P.complex.d p (p + 1)).val.app U x)) := by
  have hleib : (P.complex.d (p + n) (p + n + 1)).val.app U ((P.mul p n).app U x α) =
      gradedCast (fun q ↦ (P.complex.X q).val.obj U) (add_right_comm p 1 n)
          ((P.mul (p + 1) n).app U ((P.complex.d p (p + 1)).val.app U x) α) +
        (Int.negOnePow p : ℤ) •
          gradedCast (fun q ↦ (P.complex.X q).val.obj U) (add_assoc p n 1).symm
            ((P.mul p (n + 1)).app U x ((A.complex.d n (n + 1)).val.app U α)) :=
    P.leibniz p n U x α
  simp only [P.unopLeftMul_app, gradedCast_d_app, d_app_zsmul, hleib,
    gradedCast_smul, gradedCast_add, gradedCast_trans, smul_add, smul_smul]
  rw [negOnePow_succ_mul, negOnePow_mul_negOnePow_mul_succ]
  abel

/-- **A right differential graded `A.op`-module read as a left differential graded
`A`-module.** The cochain complex is unchanged and the action is interchanged and twisted by the
Koszul sign. -/
@[stacks 0FRI "right differential graded modules over the opposite algebra as left modules"]
noncomputable def unopLeft : LeftDifferentialGradedModule.{t, a, w} A where
  complex := P.complex
  mul := P.unopLeftMul
  mul_assoc := P.unopLeftMul_assoc
  one_mul := P.unopLeftMul_one_mul
  leibniz := P.unopLeftMul_leibniz

/-- The cochain complex underlying `P.unopLeft` is that of `P`. -/
@[simp] theorem unopLeft_complex : P.unopLeft.complex = P.complex := rfl

/-- The left action of `A` on `P.unopLeft` is `P.unopLeftMul`. -/
@[simp] theorem unopLeft_mul (n p : ℤ) : P.unopLeft.mul n p = P.unopLeftMul n p := rfl

/-! ### Homomorphisms -/

/-- A homomorphism of right differential graded `A.op`-modules into `N.opRight` commutes with
the left action of `A` on its source and the left action of `A` on `N`: the Koszul sign appears
once on each side and the two transports of degrees cancel. -/
theorem unopLeft_map_mul {P : DifferentialGradedModule.{t, a, w} A.op}
    {N : LeftDifferentialGradedModule.{t, a, w} A} (f : P ⟶ N.opRight) (n p : ℤ) (U : Cᵒᵖ)
    (α : (A.complex.X n).val.obj U) (x : (P.complex.X p).val.obj U) :
    (f.toHomologicalComplex.f (n + p)).val.app U ((P.unopLeftMul n p).app U α x) =
      (N.mul n p).app U α ((f.toHomologicalComplex.f p).val.app U x) := by
  refine eq_of_heq (HEq.trans (heq_dependent_apply
    (fun k (y : (P.complex.X k).val.obj U) ↦ (f.toHomologicalComplex.f k).val.app U y)
    (Int.add_comm n p) (P.unopLeftMul_app_heq n p U α x)) ?_)
  refine HEq.trans (heq_of_eq (hom_f_app_zsmul f.toHomologicalComplex (p + n) U _ _)) ?_
  refine HEq.trans (heq_of_eq (congrArg (fun z ↦ (Int.negOnePow (n * p) : ℤ) • z)
    (f.map_mul p n U x α))) ?_
  refine HEq.trans (heq_zsmul (fun q ↦ (N.complex.X q).val.obj U) (Int.add_comm p n) _
    (N.opRightMul_app_heq p n U ((f.toHomologicalComplex.f p).val.app U x) α)) ?_
  refine heq_of_eq ?_
  rw [smul_smul, negOnePow_mul_negOnePow, one_smul]

/-- **A homomorphism of right differential graded `A.op`-modules into `N.opRight` read as a
homomorphism of left differential graded `A`-modules into `N`.** The underlying morphism of
cochain complexes is unchanged: the two interchanges compose to the identity, the Koszul sign
appearing twice and the two transports of degrees cancelling. -/
noncomputable def Hom.unopLeft {P : DifferentialGradedModule.{t, a, w} A.op}
    {N : LeftDifferentialGradedModule.{t, a, w} A} (f : P ⟶ N.opRight) : P.unopLeft ⟶ N where
  toHomologicalComplex := f.toHomologicalComplex
  map_mul := unopLeft_map_mul f

/-- The morphism of cochain complexes underlying `Hom.unopLeft f` is that of `f`. -/
@[simp]
theorem Hom.unopLeft_toHomologicalComplex {P : DifferentialGradedModule.{t, a, w} A.op}
    {N : LeftDifferentialGradedModule.{t, a, w} A} (f : P ⟶ N.opRight) :
    (Hom.unopLeft f).toHomologicalComplex = f.toHomologicalComplex := rfl

end DifferentialGradedModule

end SheafOfModules

end
