module

public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute

/-!
# Restricting an exterior tensor product to the diagonal

Let `A` be a commutative algebra over a commutative ring `k` and let `M`, `N` be
`A`-modules. The `k`-tensor product `M ⊗[k] N` is a module over `A ⊗[k] A` through
`(a ⊗ b) • (m ⊗ n) = (a • m) ⊗ (b • n)`, and `A` is an `A ⊗[k] A`-algebra through the
multiplication map `a ⊗ b ↦ a * b`. Base changing the exterior tensor product along that
multiplication map returns the ordinary tensor product over `A`:

`A ⊗[A ⊗[k] A] (M ⊗[k] N) ≅ M ⊗[A] N`.

Geometrically `Spec (A ⊗[k] A)` is `Spec A × Spec A`, the exterior tensor product is
`pr_1^*M ⊗ pr_2^*N`, and `A` is the structure sheaf of the diagonal; the displayed
isomorphism is the degree-zero case of the reduction to the diagonal.

## Main definitions

* `Stacks.Intersection.Diagonal.exteriorModule` is the `A ⊗[k] B`-module structure on
  `M ⊗[k] N` for an `A`-module `M` and a `B`-module `N`.
* `Stacks.Intersection.Diagonal.exteriorToTensor` is the canonical `A ⊗[k] A`-linear map
  `M ⊗[k] N → M ⊗[A] N`.
* `Stacks.Intersection.Diagonal.diagonalTensorEquiv` is the isomorphism
  `A ⊗[A ⊗[k] A] (M ⊗[k] N) ≅ M ⊗[A] N`.
* `Stacks.Intersection.Diagonal.exteriorMap` is the functorial action of a pair of
  `A`-linear maps on exterior tensor products.
* `Stacks.Intersection.Diagonal.diagonalTensorEquivRight` is the case `N = A` of
  `Stacks.Intersection.Diagonal.diagonalTensorEquiv`.

## Main results

* `Stacks.Intersection.Diagonal.diagonalTensorEquiv_tmul` and
  `Stacks.Intersection.Diagonal.diagonalTensorEquiv_symm_tmul` compute the isomorphism and
  its inverse on generators, which determines it.
* `Stacks.Intersection.Diagonal.diagonalTensorEquiv_naturality` is naturality in both
  modules.
* `Stacks.Intersection.Diagonal.one_tmul_tmul_smul_left` is the `A`-balancing relation the
  base change imposes on the exterior tensor product.

## Implementation notes

The `A ⊗[k] B`-module structure on `M ⊗[k] N` and the `A ⊗[k] A`-algebra structure on `A`
are not global instances: for `M = N = A` and `B = A` the first competes with the ring's own
module structure on `A ⊗[k] A`. They are local instances instead.

## References

* [Stacks Project, Tag 0B0T](https://stacks.math.columbia.edu/tag/0B0T)
-/

@[expose] public section

open TensorProduct

namespace Stacks.Intersection.Diagonal

universe u

section Exterior

variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
variable (M N : Type u) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [AddCommGroup N] [Module k N] [Module B N] [IsScalarTower k B N]

/-- The action of `A ⊗[k] B` on `M ⊗[k] N` by letting the first factor act on `M` and the
second on `N`. The two factors act by commuting endomorphisms, so the action of the tensor
product algebra is well defined. -/
public noncomputable def exteriorAction : A ⊗[k] B →ₐ[k] Module.End k (M ⊗[k] N) :=
  Algebra.TensorProduct.lift
    ((Module.End.rTensorAlgHom k M N).comp (Algebra.lsmul k k M : A →ₐ[k] Module.End k M))
    ((Module.End.lTensorAlgHom k N M).comp (Algebra.lsmul k k N : B →ₐ[k] Module.End k N))
    (by
      intro a b
      apply LinearMap.ext
      intro x
      induction x with
      | tmul m n => simp [Module.End.mul_apply, TensorProduct.liftAux_tmul]
      | add x y hx hy => simp only [map_add, hx, hy])

/-- The exterior tensor product `M ⊗[k] N` of an `A`-module and a `B`-module as a module
over `A ⊗[k] B`. -/
@[instance_reducible]
public noncomputable def exteriorModule : Module (A ⊗[k] B) (M ⊗[k] N) :=
  Module.compHom _ (exteriorAction M N).toRingHom

attribute [local instance] exteriorModule

/-- A pure tensor of scalars acts on a pure tensor factor by factor. -/
public theorem exteriorModule_smul_tmul (a : A) (b : B) (m : M) (n : N) :
    (a ⊗ₜ[k] b) • (m ⊗ₜ[k] n) = (a • m) ⊗ₜ[k] (b • n) := rfl

end Exterior

section Diagonal

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
variable (M N : Type u) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- `A` as an `A ⊗[k] A`-algebra through the multiplication map `a ⊗ b ↦ a * b`, that is,
the structure sheaf of the diagonal of `Spec A` over `Spec k`. -/
@[instance_reducible]
public noncomputable def diagonalAlgebra : Algebra (A ⊗[k] A) A :=
  (Algebra.TensorProduct.lmul' k (S := A)).toRingHom.toAlgebra

/-- The tensor product `M ⊗[A] N` as an `A ⊗[k] A`-module, through the multiplication map. -/
@[instance_reducible]
public noncomputable def diagonalModule : Module (A ⊗[k] A) (M ⊗[A] N) :=
  Module.compHom _ (Algebra.TensorProduct.lmul' k (S := A)).toRingHom

attribute [local instance] exteriorModule diagonalAlgebra diagonalModule

/-- Scalars from `A ⊗[k] A` act on `A` through the multiplication map. -/
public theorem diagonalAlgebra_smul (r : A ⊗[k] A) (a : A) :
    r • a = Algebra.TensorProduct.lmul' k r * a := rfl

omit [Module k M] [IsScalarTower k A M] [Module k N] [IsScalarTower k A N] in
/-- Scalars from `A ⊗[k] A` act on `M ⊗[A] N` through the multiplication map. -/
public theorem diagonalModule_smul (r : A ⊗[k] A) (x : M ⊗[A] N) :
    r • x = Algebra.TensorProduct.lmul' k r • x := rfl

omit [Module k M] [IsScalarTower k A M] [Module k N] [IsScalarTower k A N] in
/-- The `A ⊗[k] A`-action on `M ⊗[A] N` factors through the `A`-action. -/
public theorem diagonalIsScalarTower : IsScalarTower (A ⊗[k] A) A (M ⊗[A] N) :=
  ⟨fun r a x => by rw [diagonalModule_smul, diagonalAlgebra_smul, mul_smul, ← smul_assoc]⟩

attribute [local instance] diagonalIsScalarTower

/-- The canonical `k`-linear map from the exterior tensor product to the tensor product over
`A`, sending `m ⊗ n` to `m ⊗ n`. -/
public noncomputable def exteriorToTensorAux : M ⊗[k] N →ₗ[k] M ⊗[A] N :=
  TensorProduct.lift
    { toFun := fun m => (TensorProduct.mk A M N m).restrictScalars k
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }

/-- The comparison `M ⊗[k] N → M ⊗[A] N` sends `m ⊗ n` to `m ⊗ n`. -/
@[simp] public theorem exteriorToTensorAux_tmul (m : M) (n : N) :
    exteriorToTensorAux M N (m ⊗ₜ[k] n) = m ⊗ₜ[A] n := rfl

/-- The canonical comparison `M ⊗[k] N → M ⊗[A] N` is `A ⊗[k] A`-linear, the target carrying
the action through the multiplication map: `(a ⊗ b) • (m ⊗ n)` and `(a * b) • (m ⊗ n)` have
the same image. -/
public noncomputable def exteriorToTensor : M ⊗[k] N →ₗ[A ⊗[k] A] M ⊗[A] N where
  toFun := exteriorToTensorAux M N
  map_add' := (exteriorToTensorAux M N).map_add
  map_smul' := by
    intro r x
    induction r with
    | add r r' hr hr' => simp only [add_smul, map_add, hr, hr']
    | tmul a b =>
        induction x with
        | add x y hx hy => simp only [smul_add, map_add, hx, hy]
        | tmul m n =>
            rw [RingHom.id_apply, exteriorModule_smul_tmul, exteriorToTensorAux_tmul,
              exteriorToTensorAux_tmul, diagonalModule_smul,
              Algebra.TensorProduct.lmul'_apply_tmul]
            conv_lhs => rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_smul]
            rw [mul_comm]
            exact TensorProduct.smul_tmul' _ _ _

/-- The `A ⊗[k] A`-linear comparison sends `m ⊗ n` to `m ⊗ n`. -/
@[simp] public theorem exteriorToTensor_tmul (m : M) (n : N) :
    exteriorToTensor M N (m ⊗ₜ[k] n) = m ⊗ₜ[A] n := rfl

/-- Multiplying a scalar into the left factor of `A ⊗[A ⊗[k] A] (M ⊗[k] N)`. -/
public theorem one_tmul_smul (r : A ⊗[k] A) (z : M ⊗[k] N) :
    (1 : A) ⊗ₜ[A ⊗[k] A] (r • z) = (Algebra.TensorProduct.lmul' k r) ⊗ₜ[A ⊗[k] A] z := by
  rw [← TensorProduct.smul_tmul]
  congr 1
  rw [diagonalAlgebra_smul, mul_one]

/-- The `A`-action on the left factor of `A ⊗[A ⊗[k] A] (M ⊗[k] N)`. -/
public theorem smul_one_tmul (a : A) (z : M ⊗[k] N) :
    a • ((1 : A) ⊗ₜ[A ⊗[k] A] z) = a ⊗ₜ[A ⊗[k] A] z := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- After base change along the multiplication map a scalar of `A` crosses the exterior
tensor product: both sides are `a ⊗ (m ⊗ n)`. -/
public theorem one_tmul_tmul_smul_left (a : A) (m : M) (n : N) :
    (1 : A) ⊗ₜ[A ⊗[k] A] ((a • m) ⊗ₜ[k] n) = (1 : A) ⊗ₜ[A ⊗[k] A] (m ⊗ₜ[k] (a • n)) := by
  have hl : (a • m) ⊗ₜ[k] n = (a ⊗ₜ[k] (1 : A)) • (m ⊗ₜ[k] n) := by
    rw [exteriorModule_smul_tmul, one_smul]
  have hr : m ⊗ₜ[k] (a • n) = ((1 : A) ⊗ₜ[k] a) • (m ⊗ₜ[k] n) := by
    rw [exteriorModule_smul_tmul, one_smul]
  rw [hl, hr, one_tmul_smul, one_tmul_smul, Algebra.TensorProduct.lmul'_apply_tmul,
    Algebra.TensorProduct.lmul'_apply_tmul, mul_one, one_mul]

/-- The bilinear map underlying the base-changed comparison: a scalar `a` of `A` acts on the
canonical comparison `M ⊗[k] N → M ⊗[A] N`. -/
public noncomputable def diagonalTensorFwdAux :
    A →ₗ[A] (M ⊗[k] N) →ₗ[A ⊗[k] A] (M ⊗[A] N) where
  toFun a := a • exteriorToTensor M N
  map_add' a a' := by rw [add_smul]
  map_smul' c a := by rw [smul_eq_mul, mul_smul, RingHom.id_apply]

/-- The base change of the canonical comparison along the multiplication map. -/
public noncomputable def diagonalTensorFwd :
    A ⊗[A ⊗[k] A] (M ⊗[k] N) →ₗ[A] M ⊗[A] N :=
  TensorProduct.AlgebraTensorModule.lift (diagonalTensorFwdAux M N)

/-- The bilinear map `(m, n) ↦ 1 ⊗ (m ⊗ n)`, which is `A`-balanced because scalars from
either factor of `A ⊗[k] A` reach the left factor as the same element of `A`. -/
public noncomputable def diagonalTensorInvAux :
    M →ₗ[A] N →ₗ[A] (A ⊗[A ⊗[k] A] (M ⊗[k] N)) where
  toFun m :=
    { toFun := fun n => (1 : A) ⊗ₜ[A ⊗[k] A] (m ⊗ₜ[k] n)
      map_add' := fun n n' => by
        rw [TensorProduct.tmul_add (R := k), TensorProduct.tmul_add (R := A ⊗[k] A)]
      map_smul' := fun a n => by
        have h : m ⊗ₜ[k] (a • n) = ((1 : A) ⊗ₜ[k] a) • (m ⊗ₜ[k] n) := by
          rw [exteriorModule_smul_tmul, one_smul]
        rw [RingHom.id_apply, h, one_tmul_smul, Algebra.TensorProduct.lmul'_apply_tmul,
          one_mul, smul_one_tmul] }
  map_add' m m' := by
    ext n
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [TensorProduct.add_tmul (R := k), TensorProduct.tmul_add (R := A ⊗[k] A)]
  map_smul' a m := by
    ext n
    have h : (a • m) ⊗ₜ[k] n = (a ⊗ₜ[k] (1 : A)) • (m ⊗ₜ[k] n) := by
      rw [exteriorModule_smul_tmul, one_smul]
    simp only [RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply]
    rw [h, one_tmul_smul, Algebra.TensorProduct.lmul'_apply_tmul, mul_one, smul_one_tmul]

/-- The inverse comparison `M ⊗[A] N → A ⊗[A ⊗[k] A] (M ⊗[k] N)`. -/
public noncomputable def diagonalTensorInv :
    M ⊗[A] N →ₗ[A] A ⊗[A ⊗[k] A] (M ⊗[k] N) :=
  TensorProduct.lift (diagonalTensorInvAux M N)

/-- **Reduction to the diagonal in degree zero.** For a commutative ring `k`, a commutative
`k`-algebra `A` and `A`-modules `M`, `N`, base changing the exterior tensor product
`M ⊗[k] N` along the multiplication map `A ⊗[k] A → A` gives the tensor product over `A`:

`A ⊗[A ⊗[k] A] (M ⊗[k] N) ≅ M ⊗[A] N`.

On `Spec A × Spec A` this identifies `𝒪_Δ ⊗ pr_1^*M ⊗ pr_2^*N` with the pushforward of
`M ⊗_A N` along the diagonal; it is the affine, degree-zero case of part (1) of
[Stacks, Tag 0B0T]. -/
public noncomputable def diagonalTensorEquiv :
    A ⊗[A ⊗[k] A] (M ⊗[k] N) ≃ₗ[A] M ⊗[A] N :=
  LinearEquiv.ofLinearMap (diagonalTensorFwd M N) (diagonalTensorInv M N)
    (by
      ext m n
      simp [diagonalTensorFwd, diagonalTensorInv, diagonalTensorInvAux, diagonalTensorFwdAux,
        exteriorToTensor, exteriorToTensorAux])
    (by
      ext z
      induction z with
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | tmul m n =>
          simp [diagonalTensorFwd, diagonalTensorInv, diagonalTensorFwdAux,
            diagonalTensorInvAux, exteriorToTensor, exteriorToTensorAux])

/-- The isomorphism is the base-changed comparison map. -/
public theorem diagonalTensorEquiv_apply (x : A ⊗[A ⊗[k] A] (M ⊗[k] N)) :
    diagonalTensorEquiv M N x = diagonalTensorFwd M N x := rfl

/-- The isomorphism sends `a ⊗ (m ⊗ n)` to `(a • m) ⊗ n`. -/
@[simp] public theorem diagonalTensorEquiv_tmul (a : A) (m : M) (n : N) :
    diagonalTensorEquiv M N (a ⊗ₜ[A ⊗[k] A] (m ⊗ₜ[k] n)) = (a • m) ⊗ₜ[A] n := by
  rw [diagonalTensorEquiv_apply, diagonalTensorFwd,
    TensorProduct.AlgebraTensorModule.lift_tmul]
  simp only [diagonalTensorFwdAux, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
    exteriorToTensor_tmul, TensorProduct.smul_tmul']

/-- The inverse isomorphism sends `m ⊗ n` to `1 ⊗ (m ⊗ n)`. -/
@[simp] public theorem diagonalTensorEquiv_symm_tmul (m : M) (n : N) :
    (diagonalTensorEquiv M N).symm (m ⊗ₜ[A] n) = (1 : A) ⊗ₜ[A ⊗[k] A] (m ⊗ₜ[k] n) := by
  rw [LinearEquiv.symm_apply_eq]
  simp

end Diagonal

section Functoriality

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
variable {M N M' N' : Type u} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  [AddCommGroup M'] [Module k M'] [Module A M'] [IsScalarTower k A M']
  [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']

attribute [local instance] exteriorModule diagonalAlgebra diagonalModule diagonalIsScalarTower

/-- A pair of `A`-linear maps acts on exterior tensor products by an `A ⊗[k] A`-linear map. -/
public noncomputable def exteriorMap (f : M →ₗ[A] M') (g : N →ₗ[A] N') :
    M ⊗[k] N →ₗ[A ⊗[k] A] M' ⊗[k] N' where
  toFun := TensorProduct.map (f.restrictScalars k) (g.restrictScalars k)
  map_add' := (TensorProduct.map (f.restrictScalars k) (g.restrictScalars k)).map_add
  map_smul' := by
    intro r x
    induction r with
    | add r r' hr hr' => simp only [add_smul, map_add, hr, hr']
    | tmul a b =>
        induction x with
        | add x y hx hy => simp only [smul_add, map_add, hx, hy]
        | tmul m n =>
            rw [RingHom.id_apply, exteriorModule_smul_tmul, TensorProduct.map_tmul,
              TensorProduct.map_tmul, exteriorModule_smul_tmul]
            simp

/-- The map induced by `f` and `g` sends `m ⊗ n` to `f m ⊗ g n`. -/
@[simp] public theorem exteriorMap_tmul (f : M →ₗ[A] M') (g : N →ₗ[A] N') (m : M) (n : N) :
    exteriorMap (k := k) f g (m ⊗ₜ[k] n) = f m ⊗ₜ[k] g n := rfl

/-- **The degree-zero reduction to the diagonal is natural in both modules.** -/
public theorem diagonalTensorEquiv_naturality (f : M →ₗ[A] M') (g : N →ₗ[A] N')
    (x : A ⊗[A ⊗[k] A] (M ⊗[k] N)) :
    diagonalTensorEquiv M' N' (LinearMap.lTensor A (exteriorMap (k := k) f g) x) =
      TensorProduct.map f g (diagonalTensorEquiv M N x) := by
  induction x with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a z =>
      induction z with
      | add z z' hz hz' => simp only [TensorProduct.tmul_add, map_add, hz, hz']
      | tmul m n => simp

end Functoriality

section Right

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
variable (M : Type u) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

attribute [local instance] exteriorModule diagonalAlgebra diagonalModule diagonalIsScalarTower

/-- The case `N = A` of the degree-zero reduction to the diagonal: base changing
`M ⊗[k] A` along the multiplication map returns `M`. -/
public noncomputable def diagonalTensorEquivRight :
    A ⊗[A ⊗[k] A] (M ⊗[k] A) ≃ₗ[A] M :=
  (diagonalTensorEquiv M A).trans (TensorProduct.rid A M)

/-- The isomorphism sends `a ⊗ (m ⊗ b)` to `(a * b) • m`. -/
@[simp] public theorem diagonalTensorEquivRight_tmul (a b : A) (m : M) :
    diagonalTensorEquivRight M (a ⊗ₜ[A ⊗[k] A] (m ⊗ₜ[k] b)) = (a * b) • m := by
  simp only [diagonalTensorEquivRight, LinearEquiv.trans_apply, diagonalTensorEquiv_tmul,
    TensorProduct.rid_tmul, smul_smul]
  rw [mul_comm]

end Right

end Stacks.Intersection.Diagonal
