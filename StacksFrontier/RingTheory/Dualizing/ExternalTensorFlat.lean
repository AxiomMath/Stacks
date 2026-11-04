module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Flatness of an external tensor product over the tensor product of its base rings

Let `R` be a commutative ring, `S` and `T` two `R`-algebras, `M` an `S`-module and `N` a
`T`-module.  Then `M ⊗[R] N` carries commuting actions of `S` (on the left factor) and of `T`
(on the right factor), hence an action of `S ⊗[R] T`, and

  `Dualizing.flat_extTensor` : if `M` is flat over `S` and `N` is flat over `T`, then `M ⊗[R] N`
  is flat over `S ⊗[R] T`.

This is the one algebraic step of [stacks 0E2H] that
`StacksFrontier.RingTheory.Dualizing.RelativeComposition` records as missing: taking `S = T = A`,
it says that an external tensor product of two `A`-flat modules is flat over the diagonal
`D = A ⊗[R] A`, which is what gives `K_{B/A} ⊗ᴸ_B (B ⊗[R] B)` a Tor-amplitude bound over `D`.
That specialisation and the bound it yields are
`Dualizing.flat_restrictScalars_diagonalExtendScalars` and
`Dualizing.torAmplitudeAbove_restrictScalars_diagonalDerivedExtension` in
`StacksFrontier.RingTheory.Dualizing.RelativeCompositionTorAmplitude`.

## The `S ⊗[R] T`-action, and why it is a `def`

Mathlib supplies exactly one of the two actions as an instance: `TensorProduct.leftModule` gives
`Module S (M ⊗[R] N)`, and flipping the tensor factors flips which one is missing.  So the
right-factor action is built here (`Dualizing.extRightModule`), and
`TensorProduct.Algebra.module` — the `def` Mathlib deliberately keeps off the instance list —
assembles the two into `Dualizing.extTensorModule`.

Neither is an `instance`, and neither is installed with `attribute [local instance]`: at `T = R`
the type `Module R (M ⊗[R] N)` would be matched by `Dualizing.extRightModule` as well as by
`TensorProduct.leftModule`, and then `IsScalarTower R S (M ⊗[R] N)` is no longer found.  Every
declaration below therefore carries its instances as `letI` in its own statement, which fixes
them to the one type they are meant for.  This is the price of stating the result on the literal
`M ⊗[R] N`; see `StacksCore.RingTheory.FiniteStability` for the same trade-off made for finiteness,
whose `Module.tensorBaseChangeEquiv` is the `S`-linear half of
`Dualizing.extBaseChangeEquiv` below.

## The proof

Write `D = S ⊗[R] T`.  Flatness is transported twice:

* `Dualizing.extBaseChangeEquiv'` identifies `M ⊗[R] T` with the base change `D ⊗[S] M`, which
  is `D`-flat by `Module.Flat.baseChange` because `M` is `S`-flat; and
* `Dualizing.extCollapseEquiv` identifies `M ⊗[R] N` with `(M ⊗[R] T) ⊗[T] N`, which is `D`-flat
  because `M ⊗[R] T` is `D`-flat and `N` is `T`-flat.

Both identifications are assembled from `TensorProduct.comm` and
`TensorProduct.AlgebraTensorModule.cancelBaseChange` and then upgraded from `S`- respectively
`T`-linearity to `D`-linearity by checking the action of a pure tensor on a pure tensor.

## References

* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Dualizing

section ExternalTensor

variable (R S T M N : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module T N] [IsScalarTower R T N]

/-- The right-factor action of `T` on `M ⊗[R] N`. -/
@[instance_reducible]
noncomputable def extRightModule : Module T (M ⊗[R] N) :=
  Module.compHom (M ⊗[R] N)
    (((Module.End.lTensorAlgHom R N M).comp
      (Algebra.lsmul R R N : T →ₐ[R] Module.End R N)).toRingHom)

/-- The right-factor action of `Dualizing.extRightModule` on a homogeneous tensor. -/
theorem extRightModule_smul_tmul (t : T) (m : M) (n : N) :
    letI := extRightModule R T M N
    (t • (m ⊗ₜ[R] n) : M ⊗[R] N) = m ⊗ₜ[R] (t • n) := rfl

/-- The right-factor action of `T` on `M ⊗[R] N` extends the action of `R`. -/
theorem extRightIsScalarTower :
    letI := extRightModule R T M N
    IsScalarTower R T (M ⊗[R] N) :=
  let := extRightModule R T M N
  { smul_assoc := fun a b x => by
      induction x with
      | zero => simp
      | tmul m n =>
          rw [extRightModule_smul_tmul, extRightModule_smul_tmul, TensorProduct.smul_tmul',
            TensorProduct.smul_tmul, smul_assoc]
      | add u v hu hv => simp only [smul_add, hu, hv] }

/-- The left-factor action of `S` and the right-factor action of `T` on `M ⊗[R] N` commute. -/
theorem extRightSMulCommClass :
    letI := extRightModule R T M N
    SMulCommClass S T (M ⊗[R] N) :=
  let := extRightModule R T M N
  { smul_comm := fun s t x => by
      induction x with
      | zero => simp
      | tmul m n =>
          rw [extRightModule_smul_tmul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
            extRightModule_smul_tmul]
      | add u v hu hv => simp only [smul_add, hu, hv] }

/-- The `S ⊗[R] T`-action on `M ⊗[R] N`. -/
@[instance_reducible]
noncomputable def extTensorModule : Module (S ⊗[R] T) (M ⊗[R] N) :=
  let := extRightModule R T M N
  let := extRightIsScalarTower R T M N
  let := extRightSMulCommClass R S T M N
  TensorProduct.Algebra.module

/-- A pure tensor of `S ⊗[R] T` acts on `M ⊗[R] N` as the left factor followed by the right. -/
theorem extTensorModule_smul (s : S) (t : T) (x : M ⊗[R] N) :
    letI := extRightModule R T M N
    letI := extTensorModule R S T M N
    ((s ⊗ₜ[R] t : S ⊗[R] T) • x) = s • t • x := rfl

/-- **The `S ⊗[R] T`-action on `M ⊗[R] N` on homogeneous tensors**: `s ⊗ t` carries `m ⊗ n` to
`(s • m) ⊗ (t • n)`. -/
theorem extTensorModule_smul_tmul (s : S) (t : T) (m : M) (n : N) :
    letI := extTensorModule R S T M N
    ((s ⊗ₜ[R] t : S ⊗[R] T) • (m ⊗ₜ[R] n)) = (s • m) ⊗ₜ[R] (t • n) := by
  let := extRightModule R T M N
  let := extTensorModule R S T M N
  rw [extTensorModule_smul, extRightModule_smul_tmul, TensorProduct.smul_tmul']

/-! ### `M ⊗[R] T` as a base change of `M` -/

/-- `M ⊗[R] T` is the base change of `M` along `S → S ⊗[R] T`. -/
noncomputable def extBaseChangeEquiv :
    ((S ⊗[R] T) ⊗[S] M) ≃ₗ[S] (M ⊗[R] T) :=
  (TensorProduct.comm S (S ⊗[R] T) M).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M T)

/-- `Dualizing.extBaseChangeEquiv` sends `(s ⊗ t) ⊗ m` to `(s • m) ⊗ t`. -/
@[simp]
theorem extBaseChangeEquiv_tmul (s : S) (t : T) (m : M) :
    extBaseChangeEquiv R S T M ((s ⊗ₜ[R] t) ⊗ₜ[S] m) = (s • m) ⊗ₜ[R] t := by
  simp [extBaseChangeEquiv]

/-- An additive map out of `(U ⊗[R] V) ⊗[B] Q` commutes with `S ⊗[R] T`-scalars once it does on
a pure tensor of pure tensors. -/
private theorem map_smul_of_map_smul_tmul_tmul {B U V Q Y F : Type*} [CommSemiring B]
    [AddCommMonoid U] [AddCommMonoid V] [Module R U] [Module R V] [AddCommMonoid Q] [Module B Q]
    [Module B (U ⊗[R] V)] [AddCommMonoid Y] [Module (S ⊗[R] T) ((U ⊗[R] V) ⊗[B] Q)]
    [Module (S ⊗[R] T) Y] [FunLike F ((U ⊗[R] V) ⊗[B] Q) Y]
    [AddMonoidHomClass F ((U ⊗[R] V) ⊗[B] Q) Y] (f : F)
    (h : ∀ (s : S) (t : T) (u : U) (v : V) (q : Q),
      f ((s ⊗ₜ[R] t : S ⊗[R] T) • ((u ⊗ₜ[R] v) ⊗ₜ[B] q)) =
        (s ⊗ₜ[R] t : S ⊗[R] T) • f ((u ⊗ₜ[R] v) ⊗ₜ[B] q))
    (c : S ⊗[R] T) (x : (U ⊗[R] V) ⊗[B] Q) : f (c • x) = c • f x := by
  induction c with
  | zero => simp
  | tmul s t =>
      induction x with
      | zero => simp
      | tmul y q =>
          induction y with
          | zero => simp
          | tmul u v => exact h s t u v q
          | add a b ha hb =>
              rw [TensorProduct.add_tmul] at *
              simp only [smul_add, map_add] at *
              rw [ha, hb]
      | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | add a b ha hb => simp only [add_smul, map_add, ha, hb]

/-- `Dualizing.extBaseChangeEquiv` is linear over `S ⊗[R] T`, not only over `S`. -/
theorem extBaseChangeEquiv_smul (c : S ⊗[R] T) (x : (S ⊗[R] T) ⊗[S] M) :
    letI := extTensorModule R S T M T
    extBaseChangeEquiv R S T M (c • x) = c • extBaseChangeEquiv R S T M x := by
  let := extRightModule R T M T
  let := extTensorModule R S T M T
  refine map_smul_of_map_smul_tmul_tmul R S T (extBaseChangeEquiv R S T M) ?_ c x
  intro s t s' t' m
  rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
    extBaseChangeEquiv_tmul, extBaseChangeEquiv_tmul, extTensorModule_smul_tmul, mul_smul,
    smul_eq_mul]

/-- `Dualizing.extBaseChangeEquiv` upgraded to `S ⊗[R] T`-linearity. -/
noncomputable def extBaseChangeEquiv' :
    letI := extTensorModule R S T M T
    ((S ⊗[R] T) ⊗[S] M) ≃ₗ[S ⊗[R] T] (M ⊗[R] T) :=
  let := extTensorModule R S T M T
  { extBaseChangeEquiv R S T M with map_smul' := extBaseChangeEquiv_smul R S T M }

/-- The scalar tower `T → S ⊗[R] T → M ⊗[R] N`. -/
theorem extIsScalarTowerRight :
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := T)
    letI := extRightModule R T M N
    letI := extTensorModule R S T M N
    IsScalarTower T (S ⊗[R] T) (M ⊗[R] N) :=
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := T)
  let := extRightModule R T M N
  let := extTensorModule R S T M N
  IsScalarTower.of_algebraMap_smul fun t x => by
    rw [Algebra.TensorProduct.right_algebraMap_apply, extTensorModule_smul, one_smul]

/-! ### `M ⊗[R] N` as a base change of `M ⊗[R] T` -/

/-- Commuting the two factors of `M ⊗[R] T` is linear for the right-factor action of `T`. -/
theorem extCommRight_aux (t : T) (x : M ⊗[R] T) :
    letI := extRightModule R T M T
    TensorProduct.comm R M T (t • x) = t • TensorProduct.comm R M T x := by
  let := extRightModule R T M T
  induction x with
  | zero => simp
  | tmul m t' =>
      rw [extRightModule_smul_tmul, TensorProduct.comm_tmul, TensorProduct.comm_tmul,
        TensorProduct.smul_tmul', smul_eq_mul]
  | add u v hu hv => rw [smul_add, map_add, map_add, smul_add, hu, hv]

/-- Commuting the factors of `M ⊗[R] T`, `T`-linearly. -/
noncomputable def extCommRight :
    letI := extRightModule R T M T
    (M ⊗[R] T) ≃ₗ[T] (T ⊗[R] M) :=
  let := extRightModule R T M T
  { TensorProduct.comm R M T with map_smul' := extCommRight_aux R T M }

/-- `(M ⊗[R] T) ⊗[T] N ≅ N ⊗[R] M`, `T`-linearly. -/
noncomputable def extCollapseEquivAux :
    letI := extRightModule R T M T
    ((M ⊗[R] T) ⊗[T] N) ≃ₗ[T] (N ⊗[R] M) :=
  let := extRightModule R T M T
  (TensorProduct.comm T (M ⊗[R] T) N).trans
    ((TensorProduct.congr (LinearEquiv.refl T N) (extCommRight R T M)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R T T N M))

/-- `(M ⊗[R] T) ⊗[T] N ≅ M ⊗[R] N`, `R`-linearly. -/
noncomputable def extCollapseEquivR :
    letI := extRightModule R T M T
    letI := (extRightSMulCommClass R R T M T).symm
    ((M ⊗[R] T) ⊗[T] N) ≃ₗ[R] (M ⊗[R] N) :=
  let := extRightModule R T M T
  let := (extRightSMulCommClass R R T M T).symm
  let := extRightIsScalarTower R T M T
  ((extCollapseEquivAux R T M N).restrictScalars R).trans (TensorProduct.comm R N M)

/-- `Dualizing.extCollapseEquivR` on a homogeneous tensor. -/
@[simp]
theorem extCollapseEquivR_tmul (m : M) (t : T) (n : N) :
    letI := extRightModule R T M T
    letI := (extRightSMulCommClass R R T M T).symm
    extCollapseEquivR R T M N ((m ⊗ₜ[R] t) ⊗ₜ[T] n) = m ⊗ₜ[R] (t • n) := by
  let := extRightModule R T M T
  let := (extRightSMulCommClass R R T M T).symm
  simp [extCollapseEquivR, extCollapseEquivAux, extCommRight]

/-- `Dualizing.extCollapseEquivR` is linear over `S ⊗[R] T`, not only over `R`. -/
theorem extCollapseEquivR_smul :
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := T)
    letI := extRightModule R T M T
    letI := (extRightSMulCommClass R R T M T).symm
    letI := extTensorModule R S T M T
    letI := extIsScalarTowerRight R S T M T
    letI := extRightModule R T M N
    letI := extTensorModule R S T M N
    ∀ (c : S ⊗[R] T) (x : (M ⊗[R] T) ⊗[T] N),
      extCollapseEquivR R T M N (c • x) = c • extCollapseEquivR R T M N x := by
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := T)
  let := extRightModule R T M T
  let := (extRightSMulCommClass R R T M T).symm
  let := extTensorModule R S T M T
  let := extIsScalarTowerRight R S T M T
  let := extRightModule R T M N
  let := extTensorModule R S T M N
  intro c x
  refine map_smul_of_map_smul_tmul_tmul R S T (extCollapseEquivR R T M N) ?_ c x
  intro s t' m t n
  rw [TensorProduct.smul_tmul', extTensorModule_smul_tmul, smul_eq_mul, extCollapseEquivR_tmul,
    extCollapseEquivR_tmul, extTensorModule_smul_tmul, mul_smul]

/-- `(M ⊗[R] T) ⊗[T] N ≅ M ⊗[R] N`, linearly over `S ⊗[R] T`. -/
noncomputable def extCollapseEquiv :
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := T)
    letI := extRightModule R T M T
    letI := (extRightSMulCommClass R R T M T).symm
    letI := extTensorModule R S T M T
    letI := extIsScalarTowerRight R S T M T
    letI := extRightModule R T M N
    letI := extTensorModule R S T M N
    ((M ⊗[R] T) ⊗[T] N) ≃ₗ[S ⊗[R] T] (M ⊗[R] N) :=
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := T)
  let := extRightModule R T M T
  let := (extRightSMulCommClass R R T M T).symm
  let := extTensorModule R S T M T
  let := extIsScalarTowerRight R S T M T
  let := extRightModule R T M N
  let := extTensorModule R S T M N
  { extCollapseEquivR R T M N with map_smul' := extCollapseEquivR_smul R S T M N }

/-- **Flatness of an external tensor product over the tensor product of its base rings.**  If `M`
is a flat `S`-module and `N` is a flat `T`-module, then the external tensor product `M ⊗[R] N` is
flat over `S ⊗[R] T` for the action of `Dualizing.extTensorModule`.

At `S = T = A` this is the statement used by [stacks 0E2H]: an external tensor product of two
`A`-flat modules is flat over the diagonal `A ⊗[R] A`. -/
theorem flat_extTensor [Module.Flat S M] [Module.Flat T N] :
    letI := extTensorModule R S T M N
    Module.Flat (S ⊗[R] T) (M ⊗[R] N) := by
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := T)
  let := extRightModule R T M T
  let := (extRightSMulCommClass R R T M T).symm
  let := extTensorModule R S T M T
  let := extIsScalarTowerRight R S T M T
  let := extRightModule R T M N
  let := extTensorModule R S T M N
  have h1 : Module.Flat (S ⊗[R] T) (M ⊗[R] T) :=
    Module.Flat.of_linearEquiv (extBaseChangeEquiv' R S T M).symm
  have h2 : Module.Flat (S ⊗[R] T) ((M ⊗[R] T) ⊗[T] N) := inferInstance
  exact Module.Flat.of_linearEquiv (extCollapseEquiv R S T M N).symm

end ExternalTensor

end Dualizing

end
