module

public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Topology.Instances.AddCircle.Defs
public import StacksFrontier.Algebra.DGA.Dual.DualComplex

/-!
# The right differential graded module `A^vee`

For a differential graded algebra `(A, d)` over a commutative ring `R`, the dual
`A^vee` has the same underlying complex as the dual complex of `A`, with
`(A^vee)^n = Hom_Z(A^{-n}, Q/Z)`, and the right action `(f · a)(x) = f(a x)`.

## Main definitions

* `DGAlgebra.DualPiece`: the degree-`n` piece `Hom_Z(A^{-n}, Q/Z)` of `A^vee`.
* `DGAlgebra.dualModule`: the right differential graded `A`-module `A^vee`.

## References

* [Stacks Project, Tag 09K4](https://stacks.math.columbia.edu/tag/09K4)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Stacks.DifferentialGradedDual

universe u

variable (R : Type u) [CommRing R]

namespace DGAlgebra
variable {R}

variable {A : DGAlgebra R}

/-! ### The right differential graded `A`-module `A^vee` -/

/-- The degree-`n` piece `Hom_Z(A^{-n}, Q/Z)` of `A^vee`, with the `R`-module structure
`(r . f)(x) = f(r . x)`. -/
def DualPiece (A : DGAlgebra R) (n : ℤ) : Type u := A.carrier (-n) →+ QZ

namespace DualPiece
variable {A : DGAlgebra R} {n : ℤ}

/-- The pointwise additive group structure on `DualPiece A n`. -/
instance : AddCommGroup (DualPiece A n) := inferInstanceAs (AddCommGroup (A.carrier (-n) →+ QZ))

/-- The action `(r • f)(x) = f(r • x)` of `R` on `DualPiece A n`. -/
instance : SMul R (DualPiece A n) where
  smul r f := (show A.carrier (-n) →+ QZ from f).comp ((r • (LinearMap.id : A.carrier (-n) →ₗ[R]
      A.carrier (-n))).toAddMonoidHom)

/-- `(r • f)(x) = f(r • x)`. -/
@[simp] theorem smul_apply (r : R) (f : DualPiece A n) (x : A.carrier (-n)) :
    (show A.carrier (-n) →+ QZ from r • f) x = (show A.carrier (-n) →+ QZ from f) (r • x) := rfl

/-- The `R`-module structure on `DualPiece A n` given by `(r • f)(x) = f(r • x)`. -/
instance : Module R (DualPiece A n) where
  one_smul f := by
    apply AddMonoidHom.ext; intro x; change (show A.carrier (-n) →+ QZ from f) ((1 : R) • x) = _
    rw [one_smul]
  mul_smul r s f := by
    apply AddMonoidHom.ext; intro x
    change (show A.carrier (-n) →+ QZ from f) ((r * s) • x)
        = (show A.carrier (-n) →+ QZ from f) (s • (r • x))
    rw [smul_smul, mul_comm s r]
  smul_zero r := by apply AddMonoidHom.ext; intro x; rfl
  smul_add r f g := by apply AddMonoidHom.ext; intro x; rfl
  add_smul r s f := by
    apply AddMonoidHom.ext; intro x
    change (show A.carrier (-n) →+ QZ from f) ((r + s) • x) = _
    rw [add_smul, map_add]; rfl
  zero_smul f := by
    apply AddMonoidHom.ext; intro x
    change (show A.carrier (-n) →+ QZ from f) ((0 : R) • x) = _
    rw [zero_smul, map_zero]; rfl

end DualPiece

/-- Multiplication map `A^m ->_l A^{-(n+m)} ->_l A^{-n}`, `(a, x) |-> a.x`, transported into
the appropriate degree. -/
noncomputable def mulMap (A : DGAlgebra R) (n m : ℤ) :
    A.carrier m →ₗ[R] A.carrier (-(n + m)) →ₗ[R] A.carrier (-n) :=
  (LinearMap.llcomp R (A.carrier (-(n + m))) (A.carrier (m + -(n + m))) (A.carrier (-n))
    (degCastLin R (show m + -(n + m) = -n by ring)).toLinearMap).comp (A.mul m (-(n + m)))

/-- `mulMap n m a x` is the product `a x` transported into degree `-n`. -/
@[simp] theorem mulMap_apply (A : DGAlgebra R) (n m : ℤ) (a : A.carrier m) (x : A.carrier (-(n +
    m))) :
    A.mulMap n m a x = degCastLin R (show m + -(n + m) = -n by ring) (A.mul m (-(n + m)) a x) := rfl

/-- The right action `(f . a)(x) = f(a x)` of `A` on `A^vee`, as an `R`-bilinear map. -/
noncomputable def dualSmul (A : DGAlgebra R) (n m : ℤ) :
    DualPiece A n →ₗ[R] A.carrier m →ₗ[R] DualPiece A (n + m) where
  toFun f :=
    { toFun := fun a => (show A.carrier (-n) →+ QZ from f).comp (A.mulMap n m a).toAddMonoidHom
      map_add' := by
        intro a b; apply AddMonoidHom.ext; intro x
        rw [AddMonoidHom.add_apply]
        simp only [map_add, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
          LinearMap.add_apply]
      map_smul' := by
        intro r a; apply AddMonoidHom.ext; intro x
        simp only [RingHom.id_apply, LinearMap.smul_apply, map_smul, AddMonoidHom.comp_apply,
          LinearMap.toAddMonoidHom_coe, DualPiece.smul_apply] }
  map_add' f g := by
    apply LinearMap.ext; intro a; apply AddMonoidHom.ext; intro x
    change (show A.carrier (-n) →+ QZ from f + g) _ = _
    rw [AddMonoidHom.add_apply]; rfl
  map_smul' r f := by
    apply LinearMap.ext; intro a; apply AddMonoidHom.ext; intro x
    rw [RingHom.id_apply, LinearMap.smul_apply]
    change (show A.carrier (-n) →+ QZ from r • f) ((A.mulMap n m a) x)
        = (show A.carrier (-(n + m)) →+ QZ from r • (show DualPiece A (n + m) from
            (show A.carrier (-n) →+ QZ from f).comp (A.mulMap n m a).toAddMonoidHom)) x
    rw [DualPiece.smul_apply, DualPiece.smul_apply]
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, map_smul]

/-- `(f . a)(x) = f(a x)`. -/
@[simp] theorem dualSmul_apply (A : DGAlgebra R) (n m : ℤ) (f : DualPiece A n) (a : A.carrier m)
    (x : A.carrier (-(n + m))) :
    (show A.carrier (-(n + m)) →+ QZ from A.dualSmul n m f a) x
      = (show A.carrier (-n) →+ QZ from f) (A.mulMap n m a x) := rfl

/-- The differential `d(f) = (-1)^{n+1} . (f . d_A)` of `A^vee`, as an `R`-linear map. -/
noncomputable def dualD (A : DGAlgebra R) (n : ℤ) : DualPiece A n →ₗ[R] DualPiece A (n + 1) where
  toFun f := ((-1 : ℤ) ^ (n + 1).natAbs) •
    ((show A.carrier (-n) →+ QZ from f).comp
      (((degCastLin R (show -(n + 1) + 1 = -n by ring)).toLinearMap.comp (A.d (-(n +
          1)))).toAddMonoidHom)
      : A.carrier (-(n + 1)) →+ QZ)
  map_add' f g := by
    change ((-1 : ℤ) ^ _) • (AddMonoidHom.comp (show A.carrier (-n) →+ QZ from f + g) _) = _
    rw [AddMonoidHom.add_comp, smul_add]
  map_smul' r f := by
    apply AddMonoidHom.ext; intro x
    simp only [RingHom.id_apply, AddMonoidHom.zsmul_apply, AddMonoidHom.coe_comp,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe, DualPiece.smul_apply,
      LinearEquiv.coe_coe, map_smul]

/-- `(d f)(x) = (-1)^{n+1} f(d_A x)`. -/
@[simp] theorem dualD_apply (A : DGAlgebra R) (n : ℤ) (f : DualPiece A n) (x : A.carrier (-(n +
    1))) :
    (show A.carrier (-(n + 1)) →+ QZ from A.dualD n f) x
      = ((-1 : ℤ) ^ (n + 1).natAbs) • (show A.carrier (-n) →+ QZ from f)
          (degCastLin R (show -(n + 1) + 1 = -n by ring) (A.d (-(n + 1)) x)) := rfl

/-- Extensionality for `DualPiece`. -/
theorem DualPiece.ext' {A : DGAlgebra R} {n : ℤ} {f g : DualPiece A n}
    (h : ∀ x : A.carrier (-n), (show A.carrier (-n) →+ QZ from f) x
      = (show A.carrier (-n) →+ QZ from g) x) : f = g :=
  AddMonoidHom.ext h

/-- Apply a `degCast` of a `DualPiece` to a point. -/
theorem DualPiece.degCast_apply {A : DGAlgebra R} {a b : ℤ} (h : a = b) (f : DualPiece A a)
    (x : A.carrier (-b)) :
    (show A.carrier (-b) →+ QZ from degCast (V := DualPiece A) h f) x
      = (show A.carrier (-a) →+ QZ from f) (degCast (V := fun n => A.carrier (-n)) h.symm x) := by
  subst h; rfl

/-- Congruence of `A.mul` in its second argument under `HEq`. -/
theorem mul_arg_congr {A : DGAlgebra R} (m : ℤ) (a : A.carrier m) {j j' : ℤ}
    (hj : j = j') {y : A.carrier j} {y' : A.carrier j'} (hy : HEq y y') :
    HEq (A.mul m j a y) (A.mul m j' a y') := by
  subst hj; cases hy; rfl

/-- Congruence of `A.d` under `HEq`. -/
theorem d_congr_heq (A : DGAlgebra R) {i j : ℤ} (hij : i = j) {x : A.carrier i}
    {y : A.carrier j} (hxy : HEq x y) : HEq (A.d i x) (A.d j y) := by
  subst hij; cases hxy; rfl

/-- Congruence of addition under `HEq` (same target degree). -/
theorem add_congr_heq {V : ℤ → Type u} [∀ n, AddCommGroup (V n)] {a b : ℤ} (hab : a = b)
    {x x' : V a} {y y' : V b} (hx : HEq x y) (hx' : HEq x' y') :
    HEq (x + x') (y + y') := by subst hab; cases hx; cases hx'; rfl

/-- Congruence of zsmul under `HEq`. -/
theorem zsmul_congr_heq {V : ℤ → Type u} [∀ n, AddCommGroup (V n)] {a b : ℤ} (hab : a = b)
    (c : ℤ) {x : V a} {y : V b} (hx : HEq x y) : HEq (c • x) (c • y) := by
  subst hab; cases hx; rfl

/-- The right differential graded `A`-module `A^vee`: `(A^vee)^n = Hom_Z(A^{-n}, Q/Z)`, with
the right action `(f . a)(x) = f(a x)` and the differential `d(f) = (-1)^{n+1} . (f . d_A)`. -/
noncomputable def dualModule (A : DGAlgebra R) : RightModule A where
  carrier n := DualPiece A n
  smul n m := A.dualSmul n m
  smul_one := by
    intro n f
    apply DualPiece.ext'
    intro x
    rw [DualPiece.degCast_apply, dualSmul_apply]
    simp only [mulMap_apply]
    congr 1
    apply eq_of_heq
    refine HEq.trans (degCastLin_heq R _ _) ?_
    have hom := A.one_mul (-(n + 0)) (degCast (V := fun k => A.carrier (-k)) (add_zero n).symm x)
    refine (degCast_heq (V := A.carrier) (zero_add (-(n + 0)))
      (A.mul 0 (-(n + 0)) A.one (degCast (V := fun k => A.carrier (-k)) (add_zero n).symm
          x))).symm.trans ?_
    rw [hom]
    exact degCast_heq (V := fun k => A.carrier (-k)) (add_zero n).symm x
  smul_assoc := by
    intro n m p f a b
    apply DualPiece.ext'
    intro x
    rw [DualPiece.degCast_apply, dualSmul_apply, dualSmul_apply, dualSmul_apply]
    simp only [mulMap_apply]
    congr 1
    apply eq_of_heq
    refine HEq.trans (degCastLin_heq R _ _) ?_
    refine HEq.trans (mul_arg_congr m a (j' := p + -((n + m) + p)) (by ring)
      (HEq.trans (degCastLin_heq R _ _)
        (mul_arg_congr p b (j' := -((n + m) + p)) rfl HEq.rfl))) ?_
    have hassoc := A.mul_assoc m p (-((n + m) + p)) a b
        (degCast (V := fun k => A.carrier (-k)) (add_assoc n m p).symm x)
    refine HEq.trans (heq_of_eq hassoc.symm) ?_
    refine HEq.trans (degCast_heq (V := A.carrier) _ _) ?_
    refine HEq.trans (mul_arg_congr (m + p) (A.mul m p a b) (j' := -(n + (m + p))) (by ring)
      (degCast_heq (V := fun k => A.carrier (-k)) (add_assoc n m p).symm x)) ?_
    exact (degCastLin_heq R _ _).symm
  d n := A.dualD n
  d_comp_d := by
    intro n f
    apply DualPiece.ext'
    intro x
    rw [dualD_apply]
    change _ = (0 : A.carrier (-(n + 1 + 1)) →+ QZ) x
    rw [AddMonoidHom.zero_apply]
    rw [dualD_apply, smul_smul]
    rw [family_degCastLin R A.d, degCastLin_trans, A.d_comp_d, degCastLin_zero, map_zero,
      smul_zero]
  leibniz := by
    intro n m f a
    apply DualPiece.ext'
    intro x
    show (show A.carrier (-(n + m + 1)) →+ QZ from A.dualD (n + m) (A.dualSmul n m f a)) x = _
    rw [dualD_apply, dualSmul_apply]
    simp only [mulMap_apply]
    rw [AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply]
    rw [DualPiece.degCast_apply, DualPiece.degCast_apply]
    rw [dualSmul_apply, dualD_apply, dualSmul_apply]
    simp only [mulMap_apply]
    set g : A.carrier (-n) →+ QZ := (show A.carrier (-n) →+ QZ from f) with hg
    set CL : A.carrier (-n) := degCastLin R (show m + -(n + m) = -n by ring)
      (A.mul m (-(n + m)) a (degCastLin R (show -(n + m + 1) + 1 = -(n + m) by ring)
        (A.d (-(n + m + 1)) x))) with hCL
    set C1 : A.carrier (-n) := degCastLin R (show -(n + 1) + 1 = -n by ring)
      (A.d (-(n + 1)) (degCastLin R (show m + -(n + 1 + m) = -(n + 1) by ring)
        (A.mul m (-(n + 1 + m)) a (degCast (V := fun k => A.carrier (-k))
          (show n + m + 1 = n + 1 + m by ring) x)))) with hC1
    set C2 : A.carrier (-n) := degCastLin R (show m + 1 + -(n + (m + 1)) = -n by ring)
      (A.mul (m + 1) (-(n + (m + 1))) (A.d m a) (degCast (V := fun k => A.carrier (-k))
        (show n + m + 1 = n + (m + 1) by ring) x)) with hC2
    change (-1 : ℤ) ^ (n + m + 1).natAbs • g CL
        = (-1 : ℤ) ^ (n + 1).natAbs • g C1 + (-1 : ℤ) ^ n.natAbs • g C2
    have hcore : (-1 : ℤ) ^ (n + m + 1).natAbs • CL
        = (-1 : ℤ) ^ (n + 1).natAbs • C1 + (-1 : ℤ) ^ n.natAbs • C2 := by
      have hleib := A.leibniz m (-(n + m + 1)) a x
      have eCL : HEq CL (A.mul m (-(n + m + 1) + 1) a (A.d (-(n + m + 1)) x)) := by
        rw [hCL]
        refine HEq.trans (degCastLin_heq R _ _) ?_
        exact mul_arg_congr m a (j' := -(n + m + 1) + 1) (by ring) (degCastLin_heq R _ _)
      have eC1 : HEq C1 (A.d (m + -(n + m + 1)) (A.mul m (-(n + m + 1)) a x)) := by
        rw [hC1]
        refine HEq.trans (degCastLin_heq R _ _) ?_
        refine d_congr_heq A (by ring) ?_
        refine HEq.trans (degCastLin_heq R _ _) ?_
        exact mul_arg_congr m a (j' := -(n + m + 1)) (by ring)
          (degCast_heq (V := fun k => A.carrier (-k)) _ x)
      have eC2 : HEq C2 (A.mul (m + 1) (-(n + m + 1)) (A.d m a) x) := by
        rw [hC2]
        refine HEq.trans (degCastLin_heq R _ _) ?_
        exact mul_arg_congr (m + 1) (A.d m a) (j' := -(n + m + 1)) (by ring)
          (degCast_heq (V := fun k => A.carrier (-k)) _ x)
      have hLt : C1 = C2 + (-1 : ℤ) ^ m.natAbs • CL := by
        apply eq_of_heq
        refine eC1.trans ?_
        rw [hleib]
        exact add_congr_heq (a := m + -(n + m + 1) + 1) (b := -n) (by ring)
          (HEq.trans (degCast_heq _ _) eC2.symm)
          (zsmul_congr_heq (by ring) _ (HEq.trans (degCast_heq _ _) eCL.symm))
      rw [hLt, smul_add, smul_smul]
      rw [neg_one_pow_natAbs_add (n + 1) m,
        show (n + 1) + m = n + m + 1 by ring,
        neg_one_pow_natAbs_succ n, neg_smul]
      abel
    rw [← g.map_zsmul, ← g.map_zsmul, ← g.map_zsmul, ← g.map_add, hcore]

end DGAlgebra

end Stacks.DifferentialGradedDual
