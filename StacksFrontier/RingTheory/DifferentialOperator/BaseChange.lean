module

public import StacksFrontier.RingTheory.DifferentialOperator.Defs
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u

/-!
# Tensoring a differential operator with the identity of a module over a second base

Let `R → A` and `R → B` be ring maps, let `M` and `M'` be `A`-modules and let `N` be a `B`-module,
so that `A ⊗[R] B` acts on `M ⊗[R] N` and on `M' ⊗[R] N` by
`(a ⊗ b) • (m ⊗ n) = (a • m) ⊗ (b • n)`.
This file proves that if `D : M → M'` is a differential operator of order at most `k` relative to
`R → A`, then `D ⊗ id_N` is a differential operator of order at most `k` relative to
`B → A ⊗[R] B`, and is the unique `B`-linear map sending `m ⊗ n` to `D m ⊗ n`.

The `B`-linearity of `D ⊗ id_N` is the identity `b • (m ⊗ n) = m ⊗ (b • n)`, which the pinned
actions give: `b` acts through `algebraMap B (A ⊗[R] B) b = 1 ⊗ b`. The order is then read off from
the commutator identity `[D ⊗ id_N, a ⊗ b] = b • ([D, a] ⊗ id_N)`, where `[D, a]` is the commutator
`m ↦ D (a • m) - a • D m`, of order at most `k - 1`. Multiplication by `b` is `A ⊗[R] B`-linear, so
the right hand side has order at most `k - 1` by induction on `k`. Commutators depend additively on
the scalar and every element of `A ⊗[R] B` is a sum of pure tensors, so all commutators of
`D ⊗ id_N` have order at most `k - 1`, which is the order bound.

## Main results

* `Stacks.DifferentialOperator.TensorIdentity.solution`: the statement of Lemma 0G37, that `D ⊗
  id_N` is the unique `B`-linear map with `(D ⊗ id_N) (m ⊗ n) = D m ⊗ n` and is a differential
  operator of order at most `k` relative to `B → A ⊗[R] B`.

## Implementation notes

The source reduces the order bound to the commutators with the elements `a ⊗ 1`, which generate
`A ⊗[R] B` as a `B`-algebra, by Lemma 0G35. That reduction is not needed: the commutator with an
arbitrary pure tensor `a ⊗ b` is computed by the same one-line calculation as the commutator with
`a ⊗ 1`, and commutators are additive in the scalar, so the additive generation of `A ⊗[R] B` by
pure tensors already covers every element. So Lemma 0G35, and with it Lemma 09CJ on composites, is
not used here.

The generalities on the order of a differential operator that the source leaves to the reader are
proved here as private lemmas, for an arbitrary, not necessarily commutative, algebra `S` over the
base: the zero operator has every order, operators of order at most `k` are closed under sums, and
postcomposition with an `S`-linear map preserves the order. Each is an induction on `k` whose step
is one of the identities satisfied by the commutator `m ↦ D (g • m) - g • D m`; those identities
are named first, and the order-`0` case goes through them as well, order at most `0` being the
vanishing of every commutator.

Multiplication by `b : B` on `M' ⊗[R] N` is `A ⊗[R] B`-linear because it is multiplication by
`algebraMap B (A ⊗[R] B) b`, which is central; it is available as
`Algebra.lsmul B (A ⊗[R] B) (M' ⊗[R] N) b`, so no commutativity of `A` is needed anywhere.

## References

* [Stacks 0G37](https://stacks.math.columbia.edu/tag/0G37), Lemma 10.133.13, in the section
  "Finite order differential operators" (Tag 09CH).
-/

@[expose] public section

open TensorProduct

namespace Stacks.DifferentialOperator.TensorIdentity

open LinearMap (commSMul commSMul_apply commSMul_zero_left commSMul_add_left commSMul_zero_right
  commSMul_add_right commSMul_comp isDifferentialOperatorOfOrderLE_zero_iff_commSMul_eq_zero
  isDifferentialOperatorOfOrderLE_succ_iff zero_isDifferentialOperatorOfOrderLE
  isDifferentialOperatorOfOrderLE_add isDifferentialOperatorOfOrderLE_postcomp)

/-! ### Commutators with the scalars of a tensor product algebra -/

section Generation

variable {R A B M N : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [CommSemiring B]
  [Algebra R B] [Algebra B (A ⊗[R] B)]
  [AddCommMonoid M] [Module B M] [Module (A ⊗[R] B) M] [IsScalarTower B (A ⊗[R] B) M]
  [AddCommGroup N] [Module B N] [Module (A ⊗[R] B) N] [IsScalarTower B (A ⊗[R] B) N]

/-- A property of operators inherited by `0` and by sums which holds for the commutators of `D`
with the pure tensors `a ⊗ b` holds for the commutators of `D` with every element of `A ⊗[R] B`,
the pure tensors generating `A ⊗[R] B` additively. This replaces the source's reduction to the
elements `a ⊗ 1`, which generate `A ⊗[R] B` as a `B`-algebra, by Lemma 0G35. -/
private lemma forall_commSMul_of_tmul {P : (M →ₗ[B] N) → Prop} (hzero : P 0)
    (hadd : ∀ D E, P D → P E → P (D + E)) (D : M →ₗ[B] N)
    (h : ∀ (a : A) (b : B), P (commSMul D (a ⊗ₜ[R] b))) (g : A ⊗[R] B) : P (commSMul D g) := by
  induction g using TensorProduct.induction_on with
  | zero => rw [commSMul_zero_right]; exact hzero
  | tmul a b => exact h a b
  | add g₁ g₂ h₁ h₂ => rw [commSMul_add_right]; exact hadd _ _ h₁ h₂

end Generation

/-! ### Maps out of a tensor product -/

section Ext

variable {R B M N P : Type*} [CommSemiring R] [Semiring B] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [Module B (M ⊗[R] N)] [AddCommMonoid P] [Module B P]

/-- Two `B`-linear maps out of `M ⊗[R] N` that agree on the pure tensors are equal, the pure
tensors generating `M ⊗[R] N` additively. -/
private lemma tmul_ext {F G : M ⊗[R] N →ₗ[B] P}
    (h : ∀ (m : M) (n : N), F (m ⊗ₜ[R] n) = G (m ⊗ₜ[R] n)) : F = G := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => exact h m n
  | add x y hx hy => simp [hx, hy]

end Ext

/-! ### The action of `B` on a tensor product over `R` -/

section SMul

variable {R A B P N : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [CommSemiring B]
  [Algebra R B] [AddCommMonoid P] [Module R P] [Module A P]
  [AddCommMonoid N] [Module R N] [Module B N]
  [Algebra B (A ⊗[R] B)]
  [Module B (P ⊗[R] N)] [Module (A ⊗[R] B) (P ⊗[R] N)] [IsScalarTower B (A ⊗[R] B) (P ⊗[R] N)]

/-- If `A ⊗[R] B` acts on `P ⊗[R] N` by `(a ⊗ b) • (p ⊗ n) = (a • p) ⊗ (b • n)` and the structure
map `B → A ⊗[R] B` is `b ↦ 1 ⊗ b`, then `B` acts on the second factor. -/
private lemma smul_tmul_right
    (halg : ∀ b : B, algebraMap B (A ⊗[R] B) b = 1 ⊗ₜ[R] b)
    (hsmul : ∀ (a : A) (b : B) (p : P) (n : N),
      (a ⊗ₜ[R] b) • (p ⊗ₜ[R] n) = (a • p) ⊗ₜ[R] (b • n))
    (b : B) (p : P) (n : N) : b • (p ⊗ₜ[R] n) = p ⊗ₜ[R] (b • n) := by
  rw [← IsScalarTower.algebraMap_smul (A ⊗[R] B) b (p ⊗ₜ[R] n), halg b, hsmul 1 b p n, one_smul]

end SMul

/-! ### Lemma 0G37 -/

section Main

variable {R A B M M' N : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [CommSemiring B]
  [Algebra R B]
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
  [AddCommMonoid N] [Module R N] [Module B N] [IsScalarTower R B N]
  [Algebra B (A ⊗[R] B)]
  [Module B (M ⊗[R] N)] [Module (A ⊗[R] B) (M ⊗[R] N)] [IsScalarTower B (A ⊗[R] B) (M ⊗[R] N)]
  [Module B (M' ⊗[R] N)] [Module (A ⊗[R] B) (M' ⊗[R] N)]
  [IsScalarTower B (A ⊗[R] B) (M' ⊗[R] N)]

variable (halg : ∀ b : B, algebraMap B (A ⊗[R] B) b = 1 ⊗ₜ[R] b)
  (hsmul : ∀ (a : A) (b : B) (m : M) (n : N),
    (a ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n))
  (hsmul' : ∀ (a : A) (b : B) (m : M') (n : N),
    (a ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n))

omit [IsScalarTower R A M] [IsScalarTower R A M'] [IsScalarTower R B N] in
include halg hsmul hsmul' in
/-- `D ⊗ id_N` is `B`-linear, `B` acting on the factor `N` that `D ⊗ id_N` leaves alone. -/
public lemma rTensor_smul (D : M →ₗ[R] M') (b : B) (x : M ⊗[R] N) :
    D.rTensor N (b • x) = b • D.rTensor N x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    rw [smul_tmul_right halg hsmul b m n, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
      smul_tmul_right halg hsmul' b (D m) n]
  | add x y hx hy => simp [smul_add, hx, hy]

omit [IsScalarTower R A M] [IsScalarTower R A M'] [IsScalarTower R B N] in
include halg hsmul hsmul' in
/-- The operator `D ⊗ id_N : M ⊗[R] N → M' ⊗[R] N` as a `B`-linear map: the `R`-linear map
`D.rTensor N` is `B`-linear for the pinned actions. -/
public def rTensorB (D : M →ₗ[R] M') : M ⊗[R] N →ₗ[B] M' ⊗[R] N where
  __ := (D.rTensor N).toAddMonoidHom
  map_smul' := rTensor_smul halg hsmul hsmul' D

omit [IsScalarTower R A M] [IsScalarTower R A M'] [IsScalarTower R B N] in
include halg hsmul hsmul' in
/-- `D ⊗ id_N` sends `m ⊗ n` to `D m ⊗ n`. -/
public lemma rTensorB_tmul (D : M →ₗ[R] M') (m : M) (n : N) :
    rTensorB halg hsmul hsmul' D (m ⊗ₜ[R] n) = D m ⊗ₜ[R] n := rfl

omit [IsScalarTower R A M] [IsScalarTower R A M'] [IsScalarTower R B N] in
include halg hsmul hsmul' in
/-- The zero operator tensored with the identity of `N` is zero. -/
private lemma rTensorB_zero : rTensorB halg hsmul hsmul' (0 : M →ₗ[R] M') = 0 :=
  tmul_ext fun m n => by rw [rTensorB_tmul]; simp

omit [IsScalarTower R B N] in
include halg hsmul hsmul' in
/-- **The commutator identity.** `[D ⊗ id_N, a ⊗ b] = b • ([D, a] ⊗ id_N)`: the commutator of
`D ⊗ id_N` with a pure tensor `a ⊗ b` is the multiplication by `b` of the tensor product of the
commutator of `D` with `a` and the identity of `N`. Multiplication by `b` is `A ⊗[R] B`-linear, so
this identity is what drops the order by one. -/
private lemma commSMul_rTensorB (D : M →ₗ[R] M') (a : A) (b : B) :
    commSMul (rTensorB halg hsmul hsmul' D) (a ⊗ₜ[R] b)
      = (Algebra.lsmul B (A ⊗[R] B) (M' ⊗[R] N) b).restrictScalars B ∘ₗ
          rTensorB halg hsmul hsmul' (commSMul D a) := by
  refine tmul_ext fun m n => ?_
  show commSMul (rTensorB halg hsmul hsmul' D) (a ⊗ₜ[R] b) (m ⊗ₜ[R] n)
    = b • rTensorB halg hsmul hsmul' (commSMul D a) (m ⊗ₜ[R] n)
  rw [commSMul_apply, hsmul a b m n, rTensorB_tmul, rTensorB_tmul, hsmul' a b (D m) n,
    ← TensorProduct.sub_tmul, ← commSMul_apply, rTensorB_tmul,
    smul_tmul_right halg hsmul' b (commSMul D a m) n]

omit [IsScalarTower R B N] in
include halg hsmul hsmul' in
/-- The order bound of Lemma 0G37: if `D` is a differential operator of order at most `k` relative
to `R → A`, then `D ⊗ id_N` is one of order at most `k` relative to `B → A ⊗[R] B`. -/
public lemma order_rTensorB (k : ℕ) {D : M →ₗ[R] M'}
    (hD : D.IsDifferentialOperatorOfOrderLE A k) :
    (rTensorB halg hsmul hsmul' D).IsDifferentialOperatorOfOrderLE (A ⊗[R] B) k := by
  induction k generalizing D with
  | zero =>
    refine isDifferentialOperatorOfOrderLE_zero_iff_commSMul_eq_zero.mpr
      (forall_commSMul_of_tmul (P := fun E => E = 0) rfl
        (fun E F hE hF => by rw [hE, hF, add_zero]) _ fun a b => ?_)
    rw [commSMul_rTensorB, isDifferentialOperatorOfOrderLE_zero_iff_commSMul_eq_zero.mp hD a,
      rTensorB_zero, LinearMap.comp_zero]
  | succ k ih =>
    refine isDifferentialOperatorOfOrderLE_succ_iff.mpr (forall_commSMul_of_tmul
      (P := fun E => E.IsDifferentialOperatorOfOrderLE (A ⊗[R] B) k)
      (zero_isDifferentialOperatorOfOrderLE k)
      (fun E F hE hF => isDifferentialOperatorOfOrderLE_add hE hF) _ fun a b => ?_)
    rw [commSMul_rTensorB]
    exact isDifferentialOperatorOfOrderLE_postcomp _
      (ih (isDifferentialOperatorOfOrderLE_succ_iff.mp hD a))

omit [IsScalarTower R A M] [IsScalarTower R A M'] [IsScalarTower R B N] in
include halg hsmul hsmul' in
/-- A `B`-linear map carrying every pure tensor `m ⊗ n` to `D m ⊗ n` is `D ⊗ id_N`, the pure
tensors generating `M ⊗[R] N` additively. -/
public lemma eq_rTensorB {D : M →ₗ[R] M'} (D' : M ⊗[R] N →ₗ[B] M' ⊗[R] N)
    (hD' : ∀ (m : M) (n : N), D' (m ⊗ₜ[R] n) = D m ⊗ₜ[R] n) :
    D' = rTensorB halg hsmul hsmul' D :=
  tmul_ext fun m n => by rw [hD' m n, rTensorB_tmul]

-- `IsScalarTower R B N` is a hypothesis of the statement — it pins the `R`-action on `N` to the one
-- along `R → B`, and is what makes the pinned actions on the tensor products exist in any
-- instantiation — but it is unused by this proof, which reads those actions off `halg`, `hsmul`
-- and `hsmul'`; it is kept to match the source, so the two lints are silenced here.
/-- `D ⊗ id_N` is the unique `B`-linear map `M ⊗[R] N → M' ⊗[R] N` sending `m ⊗ n` to `D m ⊗ n`,
and it is a differential operator of order at most `k` relative to `B → A ⊗[R] B`. -/
@[nolint unusedArguments]
public theorem solution {k : ℕ} {D : M →ₗ[R] M'}
    (hD : D.IsDifferentialOperatorOfOrderLE A k)
    (halg : ∀ b : B, algebraMap B (A ⊗[R] B) b = 1 ⊗ₜ[R] b)
    (hsmul : ∀ (a : A) (b : B) (m : M) (n : N),
      (a ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n))
    (hsmul' : ∀ (a : A) (b : B) (m : M') (n : N),
      (a ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n)) :
    ∃! D' : M ⊗[R] N →ₗ[B] M' ⊗[R] N,
      (∀ (m : M) (n : N), D' (m ⊗ₜ[R] n) = D m ⊗ₜ[R] n) ∧
        D'.IsDifferentialOperatorOfOrderLE (A ⊗[R] B) k :=
  ⟨rTensorB halg hsmul hsmul' D, ⟨rTensorB_tmul halg hsmul hsmul' D,
    order_rTensorB halg hsmul hsmul' k hD⟩,
    fun F hF => eq_rTensorB halg hsmul hsmul' F hF.1⟩

end Main

end Stacks.DifferentialOperator.TensorIdentity

end

/-!
# Differential operators and tensoring with a module over a second base

Let `R → A` and `R → B` be ring maps, let `M` and `M'` be `A`-modules and let `N` be a `B`-module.
The tensor product `M ⊗[R] N` is a module over `A ⊗[R] B`, with `A` acting through `M` and `B`
through `N`, so that `(a ⊗ b) • (m ⊗ n) = (a • m) ⊗ (b • n)`. If `D : M → M'` is a differential
operator of order at most `k` relative to `R → A`, then `D ⊗ id_N : M ⊗[R] N → M' ⊗[R] N` is a
differential operator of order at most `k` relative to `B → A ⊗[R] B`. Being such an operator
includes being `B`-linear, which the source asserts as the first step of its proof; the order is
then read off from the commutator identity
`(D ⊗ id) ∘ (a ⊗ 1) - (a ⊗ 1) ∘ (D ⊗ id) = (D ∘ a - a ∘ D) ⊗ id`, whose right hand side has order
at most `k - 1` by induction.

A `B`-linear map on `M ⊗[R] N` is determined by its values on the pure tensors, so `D ⊗ id_N` is
the *unique* `B`-linear map with `D' (m ⊗ n) = D m ⊗ n`. That characterisation is the form in which
the geometric counterpart (Morphisms, Lemma 0G45) is stated and used: there `D'` is characterised
by `D' (s ⊗ t) = D s ⊗ t` on local sections.

## Main results

* `LinearMap.IsDifferentialOperatorOfOrderLE.rTensorB`: the operator `D ⊗ id_N` itself, as a
  `B`-linear map, with `rTensorB_tmul` for its values on pure tensors, `order_rTensorB` for the
  order bound and `eq_rTensorB` for its uniqueness.
* `LinearMap.IsDifferentialOperatorOfOrderLE.existsUnique_rTensor`: those three in the
  existence-and-uniqueness form of the source — tensoring a differential operator of order at most
  `k` relative to `R → A` with the identity of a `B`-module gives a differential operator of order
  at most `k` relative to `B → A ⊗[R] B`.

## Implementation notes

The three scalar actions the statement needs are hypotheses rather than instances, because
Mathlib deliberately provides none of them globally: `Algebra B (A ⊗[R] B)` is
`Algebra.TensorProduct.rightAlgebra`, which is not an instance since the action of `A` on
`A ⊗[R] A` would be ambiguous; the `A ⊗[R] B`-module structure on a module with commuting `A`- and
`B`-actions is `TensorProduct.Algebra.module`, not an instance for the same reason; and only the
left factor of a tensor product carries a `Module` instance (`TensorProduct.leftModule`), so the
`B`-action coming from `N` is not an instance either. Each is pinned to the canonical one:
`hsmul` and `hsmul'` fix the `A ⊗[R] B`-action on pure tensors, hence on all of `M ⊗[R] N` and
`M' ⊗[R] N` by additivity, and `halg` fixes `algebraMap B (A ⊗[R] B)`, whence
`b • x = (b • 1) • x = (1 ⊗ b) • x` recovers the `B`-action from the scalar tower. So no unpinned
structure is quantified over, and instantiating with `Algebra.TensorProduct.rightAlgebra` and
`TensorProduct.Algebra.module` discharges all of them.

Only `B`, the base ring of the operator `D ⊗ id_N`, has to be commutative; `A` is an arbitrary
`R`-algebra, as in Definition 09CI, and `M` and `N` are additive monoids, only `M'` being a group
since only the values of an operator are subtracted.

One departure from the source's form: the order is an upper bound, following Definition 09CI as
formalized. As an `R`-linear map `D ⊗ id_N` is `LinearMap.rTensor N D`, whence the name `rTensorB`;
the `B` marks the upgrade of the scalars from `R` to `B`, which is the content of the definition
and has no Mathlib form, there being no instance for the `B`-action on the right factor of
`M ⊗[R] N`.

Faithfulness. (1) No dead hypothesis: `hD` is the operator being tensored, `halg`, `hsmul` and
`hsmul'` pin the three actions the conclusion speaks about, the scalar towers pin the `R`-actions
on `M`, `M'`, `N` to the ones along `R → A` and `R → B`, and `k` occurs in both `hD` and the
conclusion. (2) The scalars and base are the source's: `D` is a differential operator relative to
`R → A` and `D'` one relative to `B → A ⊗[R] B` — `B`-linear, not `R`-linear, with `A ⊗[R] B`
acting as in the source. (3) The map the source names is a term, `rTensorB`, pinned by
`rTensorB_tmul` and `eq_rTensorB` as the unique `B`-linear map with `D' (m ⊗ₜ n) = D m ⊗ₜ n`, so
the statement is about `D ⊗ id_N` itself and not about the existence of some operator. (4) The
instantiation is not degenerate: for `R = ℚ`,
`A = M = M' = ℚ[X]`, `B = N = MvPolynomial Bool ℚ`, `D = d/dX` and `k = 1`, every hypothesis holds
with the canonical structures (`halg` and both `hsmul` are `rfl` and
`Algebra.TensorProduct.tmul_mul_tmul`), and `d/dX` is a differential operator of order at most `1`
which is not of order at most `0`, so neither the hypothesis nor the conclusion is vacuous.

## References

* [Stacks 0G37](https://stacks.math.columbia.edu/tag/0G37), Lemma 10.133.13, in the section
  "Finite order differential operators" (Tag 09CH).
-/

@[expose] public section

open TensorProduct

namespace LinearMap.IsDifferentialOperatorOfOrderLE

variable {R A B M M' N : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [CommSemiring B]
  [Algebra R B]
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
  [AddCommMonoid N] [Module R N] [Module B N] [IsScalarTower R B N]
  [Algebra B (A ⊗[R] B)]
  [Module B (M ⊗[R] N)] [Module (A ⊗[R] B) (M ⊗[R] N)] [IsScalarTower B (A ⊗[R] B) (M ⊗[R] N)]
  [Module B (M' ⊗[R] N)] [Module (A ⊗[R] B) (M' ⊗[R] N)]
  [IsScalarTower B (A ⊗[R] B) (M' ⊗[R] N)]

omit [IsScalarTower R A M] [IsScalarTower R A M'] [IsScalarTower R B N] in
/-- **The operator `D ⊗ id_N`.** The tensor product of an `R`-linear map `D : M →ₗ[R] M'` with the
identity of a `B`-module `N`, as a `B`-linear map `M ⊗[R] N → M' ⊗[R] N`. Its underlying `R`-linear
map is `LinearMap.rTensor N D`; the content of the definition is the `B`-linearity, `B` acting
through `algebraMap B (A ⊗[R] B) b = 1 ⊗ₜ b` on the factor `N` that `D ⊗ id_N` leaves alone. Here
`hsmul` and `hsmul'` say that `A ⊗[R] B` acts on the tensor products by
`(a ⊗ b) • (m ⊗ n) = (a • m) ⊗ (b • n)`, and `halg` that `B → A ⊗[R] B` is `b ↦ 1 ⊗ b`. -/
@[stacks 0G37 "the operator `D ⊗ id_N` itself; `rTensorB_tmul` is its values on pure tensors,
`order_rTensorB` the order bound and `eq_rTensorB` its uniqueness. The `B`-algebra structure on
`A ⊗[R] B` and the actions on `M ⊗[R] N`, `M' ⊗[R] N` are hypotheses because Mathlib has no such
instances; `halg`, `hsmul` and `hsmul'` pin them to the canonical ones. See the module docstring."]
public def rTensorB
    (halg : ∀ b : B, algebraMap B (A ⊗[R] B) b = 1 ⊗ₜ[R] b)
    (hsmul : ∀ (a : A) (b : B) (m : M) (n : N),
      (a ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n))
    (hsmul' : ∀ (a : A) (b : B) (m : M') (n : N),
      (a ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n))
    (D : M →ₗ[R] M') : M ⊗[R] N →ₗ[B] M' ⊗[R] N :=
  Stacks.DifferentialOperator.TensorIdentity.rTensorB halg hsmul hsmul' D

omit [IsScalarTower R A M] [IsScalarTower R A M'] [IsScalarTower R B N] in
/-- `D ⊗ id_N` sends `m ⊗ n` to `D m ⊗ n`. -/
@[stacks 0G37 "the values of `rTensorB` on pure tensors"]
public lemma rTensorB_tmul
    (halg : ∀ b : B, algebraMap B (A ⊗[R] B) b = 1 ⊗ₜ[R] b)
    (hsmul : ∀ (a : A) (b : B) (m : M) (n : N),
      (a ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n))
    (hsmul' : ∀ (a : A) (b : B) (m : M') (n : N),
      (a ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n))
    (D : M →ₗ[R] M') (m : M) (n : N) :
    rTensorB halg hsmul hsmul' D (m ⊗ₜ[R] n) = D m ⊗ₜ[R] n :=
  Stacks.DifferentialOperator.TensorIdentity.rTensorB_tmul halg hsmul hsmul' D m n

omit [IsScalarTower R B N] in
/-- If `D` is a differential operator of order at most `k` relative to `R → A`, then `D ⊗ id_N` is
one of order at most `k` relative to `B → A ⊗[R] B`. -/
@[stacks 0G37 "the order bound on `rTensorB`"]
public lemma order_rTensorB {k : ℕ} {D : M →ₗ[R] M'}
    (hD : D.IsDifferentialOperatorOfOrderLE A k)
    (halg : ∀ b : B, algebraMap B (A ⊗[R] B) b = 1 ⊗ₜ[R] b)
    (hsmul : ∀ (a : A) (b : B) (m : M) (n : N),
      (a ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n))
    (hsmul' : ∀ (a : A) (b : B) (m : M') (n : N),
      (a ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n)) :
    (rTensorB halg hsmul hsmul' D).IsDifferentialOperatorOfOrderLE (A ⊗[R] B) k :=
  Stacks.DifferentialOperator.TensorIdentity.order_rTensorB halg hsmul hsmul' k hD

omit [IsScalarTower R A M] [IsScalarTower R A M'] [IsScalarTower R B N] in
/-- `D ⊗ id_N` is the only `B`-linear map `M ⊗[R] N → M' ⊗[R] N` carrying `m ⊗ n` to `D m ⊗ n`. -/
@[stacks 0G37 "uniqueness of `rTensorB`"]
public lemma eq_rTensorB {D : M →ₗ[R] M'}
    (halg : ∀ b : B, algebraMap B (A ⊗[R] B) b = 1 ⊗ₜ[R] b)
    (hsmul : ∀ (a : A) (b : B) (m : M) (n : N),
      (a ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n))
    (hsmul' : ∀ (a : A) (b : B) (m : M') (n : N),
      (a ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n))
    (D' : M ⊗[R] N →ₗ[B] M' ⊗[R] N)
    (hD' : ∀ (m : M) (n : N), D' (m ⊗ₜ[R] n) = D m ⊗ₜ[R] n) :
    D' = rTensorB halg hsmul hsmul' D :=
  Stacks.DifferentialOperator.TensorIdentity.eq_rTensorB halg hsmul hsmul' D' hD'

/-- **Stacks 0G37.** Let `R → A` and `R → B` be ring maps, let `M` and `M'` be `A`-modules and
let `N` be a `B`-module. If `D : M → M'` is a differential operator of order at most `k` relative
to `R → A`, then `D ⊗ id_N` is a differential operator of order at most `k` relative to
`B → A ⊗[R] B`: there is a unique `B`-linear map `D' : M ⊗[R] N → M' ⊗[R] N` with
`D' (m ⊗ₜ n) = D m ⊗ₜ n` which is a differential operator of order at most `k` relative to
`B → A ⊗[R] B`. That map is `rTensorB halg hsmul hsmul' D`. -/
public theorem existsUnique_rTensor {k : ℕ} {D : M →ₗ[R] M'}
    (hD : D.IsDifferentialOperatorOfOrderLE A k)
    (halg : ∀ b : B, algebraMap B (A ⊗[R] B) b = 1 ⊗ₜ[R] b)
    (hsmul : ∀ (a : A) (b : B) (m : M) (n : N),
      (a ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n))
    (hsmul' : ∀ (a : A) (b : B) (m : M') (n : N),
      (a ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n)) :
    ∃! D' : M ⊗[R] N →ₗ[B] M' ⊗[R] N,
      (∀ (m : M) (n : N), D' (m ⊗ₜ[R] n) = D m ⊗ₜ[R] n) ∧
        D'.IsDifferentialOperatorOfOrderLE (A ⊗[R] B) k :=
    by exact Stacks.DifferentialOperator.TensorIdentity.solution hD halg hsmul hsmul'

end LinearMap.IsDifferentialOperatorOfOrderLE

end

/-!
# Base change of the modules of principal parts

Let `A → A'` and `A → B` be ring maps, let `B' = B ⊗[A] A'`, let `M` be a `B`-module and let
`M' = M ⊗[A] A'`, a `B'`-module. This file proves that the map of Remark 09CP between modules of
principal parts is a base change: `Pᵏ_{B/A}(M) ⊗[A] A' = Pᵏ_{B'/A'}(M')`.

The proof is the source's. Writing `D : M → P` for the universal differential operator of order at
most `k` relative to `A → B` (Definition 09CL), the base change `D ⊗ 1` of `D` is realised here as
the operator `Dt : M' → B' ⊗[B] P` sending `φ m` to `1 ⊗ₜ D m`, where `φ : M → M'` is the
canonical map. Two verifications make `Dt` a universal operator of order at most `k` relative to
`A' → B'`:

* `Dt` has order at most `k`. The order of an `A'`-linear operator may be tested on a set of
  generators of `B'` as an `A'`-module, because the commutator `m ↦ E (g • m) - g • E m` of an
  `A'`-linear `E` is `A'`-linear in `g`; and `B'` is generated over `A'` by the image of `B`,
  where the commutators of `Dt` are the base changes of those of `D`.
* `Dt` is universal. An operator `E : M' → N` of order at most `k` over `A' → B'` restricts to the
  operator `E ∘ φ : M → N` of order at most `k` over `A → B`, hence factors as `γ ∘ D` for a
  unique `B`-linear `γ : P → N`, and `γ.liftBaseChange B'` is the required factorisation of `E`
  through `Dt`; it is unique because `B' ⊗[B] P` is generated over `B'` by the image of `P`.

Comparing `Dt` with the given universal operator `D' : M' → P'` produces a `B'`-linear isomorphism
`B' ⊗[B] P ≃ P'` carrying `1 ⊗ₜ p` to `ψ p`, and `B' ⊗[B] P = A' ⊗[A] P` because `B' = B ⊗[A] A'`
(`Algebra.IsPushout.cancelBaseChange`).

## Main results

* `Stacks.PrincipalParts.BaseChange.solution`: the statement of Lemma 0H8Z, that the map of Remark
  09CP exhibits `Pᵏ_{B'/A'}(M ⊗[A] A')` as `Pᵏ_{B/A}(M) ⊗[A] A'`.

## Implementation notes

The base change of `P` is taken in the form `B' ⊗[B] P` rather than `A' ⊗[A] P`, since it is over
`B'` that the universal property of `D'` is applied and `B' ⊗[B] P` carries the `B'`-action for
free; the two agree by `Algebra.IsPushout.cancelBaseChange`.

A universal operator `D : M → P` generates `P` over `B`: this is used twice, once to see that a
`B`-linear map out of `P` is determined on the image of `D` and once for the uniqueness of the
factorisation through `Dt`. It is proved here
(`Stacks.PrincipalParts.BaseChange.span_range_eq_top`) by feeding the quotient of `P` by the span
of the image of `D` to the universal property, and is the same argument as in the proof of
Lemma 09CN.

The generalities on the order of a differential operator that the source leaves to the reader are
proved here as private lemmas: an operator of order at most `k` composed with a `B`-linear map has
order at most `k`, sums of such operators have order at most `k`, and the order may be tested on a
generating set of the ring of scalars.

## References

* [Stacks 0H8Z](https://stacks.math.columbia.edu/tag/0H8Z), Lemma 10.133.10, in the section
  "Finite order differential operators" (Tag 09CH), and Remark 09CP for the map.
-/

@[expose] public section

open TensorProduct



namespace Stacks.PrincipalParts.BaseChange

open LinearMap (commSMul commSMul_apply isDifferentialOperatorOfOrderLE_succ_iff
  zero_isDifferentialOperatorOfOrderLE isDifferentialOperatorOfOrderLE_add
  isDifferentialOperatorOfOrderLE_postcomp)

/-! ### Generalities on differential operators of finite order -/

section Order

variable {R S M N N₂ : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommGroup N₂] [Module R N₂] [Module S N₂] [IsScalarTower R S N₂]

/-- Order at most `0` may be tested on a generating set of `S` as an `R`-module. -/
private lemma isDifferentialOperatorOfOrderLE_zero_of_span {G : Set S}
    (hG : Submodule.span R G = ⊤) {D : M →ₗ[R] N}
    (h : ∀ g ∈ G, ∀ m : M, D (g • m) = g • D m) :
    D.IsDifferentialOperatorOfOrderLE S 0 := by
  have key : ∀ g ∈ Submodule.span R G, ∀ m : M, D (g • m) = g • D m := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => intro m; simp
    | add x y _ _ ihx ihy => intro m; rw [add_smul, map_add, ihx, ihy, add_smul]
    | smul a x _ ih => intro m; rw [smul_assoc, map_smul, ih, smul_assoc]
  exact fun g m => key g (Submodule.eq_top_iff'.mp hG g) m

/-- Order at most `k + 1` may be tested on a generating set of `S` as an `R`-module. -/
private lemma isDifferentialOperatorOfOrderLE_succ_of_span {k : ℕ} {G : Set S}
    (hG : Submodule.span R G = ⊤) {D : M →ₗ[R] N}
    (h : ∀ g ∈ G, (commSMul D g).IsDifferentialOperatorOfOrderLE S k) :
    D.IsDifferentialOperatorOfOrderLE S (k + 1) := by
  rw [isDifferentialOperatorOfOrderLE_succ_iff]
  have key : ∀ g ∈ Submodule.span R G, (commSMul D g).IsDifferentialOperatorOfOrderLE S k := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero =>
      rw [LinearMap.commSMul_zero_right]
      exact zero_isDifferentialOperatorOfOrderLE k
    | add x y _ _ ihx ihy =>
      rw [LinearMap.commSMul_add_right]
      exact isDifferentialOperatorOfOrderLE_add ihx ihy
    | smul a x _ ih =>
      have hsmul : commSMul D (a • x) =
          (Algebra.lsmul S S N (algebraMap R S a)).restrictScalars R ∘ₗ commSMul D x := by
        ext m
        simp only [commSMul_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
          Function.comp_apply, Algebra.lsmul_coe, algebraMap_smul, smul_assoc, map_smul, smul_sub]
      rw [hsmul]
      exact isDifferentialOperatorOfOrderLE_postcomp _ ih
  exact fun g => key g (Submodule.eq_top_iff'.mp hG g)

end Order

/-! ### A universal operator generates its target -/

section Span

variable {A : Type*} {B M P : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup P] [Module A P] [Module B P] [IsScalarTower A B P]

/-- A universal differential operator generates its target over `B`; this is the same argument as
in the proof of Lemma 09CN. -/
@[ega "IV 16.3.8" "Affine case"]
private lemma span_range_eq_top {k : ℕ} {D : M →ₗ[A] P}
    (hD : D.IsUniversalDifferentialOperatorOfOrderLE B k) :
    Submodule.span B (Set.range D) = ⊤ := by
  obtain ⟨T, hT⟩ : ∃ T : Submodule B P, Submodule.span B (Set.range D) = T := ⟨_, rfl⟩
  obtain ⟨α, -, huq⟩ := hD.2 (N := P ⧸ T) 0 (zero_isDifferentialOperatorOfOrderLE k)
  have hmem : ∀ m : M, D m ∈ T := fun m => hT ▸ Submodule.subset_span ⟨m, rfl⟩
  have h1 : T.mkQ = α := huq _ fun m => (Submodule.Quotient.mk_eq_zero T).mpr (hmem m)
  have h2 : (0 : P →ₗ[B] P ⧸ T) = α := huq _ fun m => rfl
  rw [hT, Submodule.eq_top_iff']
  intro p
  exact (Submodule.Quotient.mk_eq_zero T).mp (LinearMap.congr_fun (h1.trans h2.symm) p)

end Span

/-! ### The image of `B` spans `B'` over `A'` -/

/-- If `B' = B ⊗[A] A'`, then `B'` is generated as an `A'`-module by the image of `B`. -/
private lemma span_range_algebraMap_eq_top (A A' B B' : Type*) [CommRing A] [CommRing A']
    [CommRing B] [CommRing B'] [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B']
    [Algebra B B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] [Algebra.IsPushout A A' B B'] :
    Submodule.span A' (Set.range (algebraMap B B')) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  refine (Algebra.IsPushout.out (R := A) (S := A') (R' := B) (S' := B')).inductionOn x _
    (Submodule.zero_mem _) (fun b => Submodule.subset_span ⟨b, rfl⟩)
    (fun a y hy => Submodule.smul_mem _ a hy) (fun y z hy hz => Submodule.add_mem _ hy hz)

/-! ### Base change of a differential operator -/

section BaseChange

variable {A : Type*} {A' B B' M M' P N : Type u}
  [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
  [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
  [IsScalarTower A A' B'] [IsScalarTower A B B'] [Algebra.IsPushout A A' B B']
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup M'] [Module A M'] [Module A' M'] [Module B M'] [Module B' M']
  [IsScalarTower A A' M'] [IsScalarTower A B M'] [IsScalarTower A' B' M'] [IsScalarTower B B' M']
  [AddCommGroup P] [Module A P] [Module B P] [IsScalarTower A B P]
  [AddCommGroup N] [Module A N] [Module A' N] [Module B N] [Module B' N]
  [IsScalarTower A A' N] [IsScalarTower A B N] [IsScalarTower A' B' N] [IsScalarTower B B' N]

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] [Algebra.IsPushout A A' B B'] in
/-- An operator of order at most `k` relative to `A' → B'` restricts along `M → M'` to an operator
of order at most `k` relative to `A → B`. -/
@[sga "3 VIIA 1.2.2" "special case", sga "3 VIIA 1.3" "partial"]
private lemma isDifferentialOperatorOfOrderLE_comp_restrictScalars (φ : M →ₗ[B] M') (k : ℕ)
    {E : M' →ₗ[A'] N} (hE : E.IsDifferentialOperatorOfOrderLE B' k) :
    (E.restrictScalars A ∘ₗ φ.restrictScalars A).IsDifferentialOperatorOfOrderLE B k := by
  induction k generalizing E with
  | zero =>
    replace hE : ∀ (g : B') (x : M'), E (g • x) = g • E x := hE
    intro b m
    show E (φ (b • m)) = b • E (φ m)
    rw [map_smul φ b m, ← algebraMap_smul B' b (φ m), hE, algebraMap_smul]
  | succ k ih =>
    rw [isDifferentialOperatorOfOrderLE_succ_iff]
    intro b
    have key : commSMul (E.restrictScalars A ∘ₗ φ.restrictScalars A) b =
        (commSMul E (algebraMap B B' b)).restrictScalars A ∘ₗ φ.restrictScalars A := by
      ext m
      show E (φ (b • m)) - b • E (φ m) =
        E (algebraMap B B' b • φ m) - algebraMap B B' b • E (φ m)
      rw [map_smul φ b m, algebraMap_smul, algebraMap_smul]
    rw [key]
    exact ih (isDifferentialOperatorOfOrderLE_succ_iff.mp hE (algebraMap B B' b))

omit [Module A N] [IsScalarTower A A' N] [IsScalarTower A B N] in
/-- If an `A'`-linear map `E : M' → N` agrees on the image of `M` with a `B`-linear map applied to
an operator `D` of order at most `k` relative to `A → B`, then `E` has order at most `k` relative
to `A' → B'`. This is the verification that the base change of an operator is an operator. -/
@[sga "3 VIIA 1.2.2" "partial", sga "3 VIIA 1.3" "Affine case"]
private lemma isDifferentialOperatorOfOrderLE_of_comp_eq (φ : M →ₗ[B] M')
    (hφ : IsBaseChange A' (φ.restrictScalars A)) (χ : P →ₗ[B] N) (k : ℕ)
    {D : M →ₗ[A] P} {E : M' →ₗ[A'] N} (hD : D.IsDifferentialOperatorOfOrderLE B k)
    (hE : ∀ m : M, E (φ m) = χ (D m)) : E.IsDifferentialOperatorOfOrderLE B' k := by
  induction k generalizing D E with
  | zero =>
    replace hD : ∀ (b : B) (m : M), D (b • m) = b • D m := hD
    refine isDifferentialOperatorOfOrderLE_zero_of_span
      (span_range_algebraMap_eq_top A A' B B') ?_
    rintro g ⟨b, rfl⟩
    have key : (E ∘ₗ Algebra.lsmul A' A' M' (algebraMap B B' b) : M' →ₗ[A'] N) =
        Algebra.lsmul A' A' N (algebraMap B B' b) ∘ₗ E := by
      refine hφ.algHom_ext _ _ fun m => ?_
      show E (algebraMap B B' b • φ m) = algebraMap B B' b • E (φ m)
      rw [algebraMap_smul, algebraMap_smul, ← map_smul φ b m, hE, hE, hD, map_smul]
    exact fun x => LinearMap.congr_fun key x
  | succ k ih =>
    refine isDifferentialOperatorOfOrderLE_succ_of_span
      (span_range_algebraMap_eq_top A A' B B') ?_
    rintro g ⟨b, rfl⟩
    refine ih (isDifferentialOperatorOfOrderLE_succ_iff.mp hD b) fun m => ?_
    rw [commSMul_apply, commSMul_apply, algebraMap_smul, ← map_smul φ b m, hE, hE, map_sub,
      map_smul χ b (D m), algebraMap_smul]

/-- The base change of an operator of order at most `k` has order at most `k`: any `A'`-linear
`Dt : M' → B' ⊗[B] P` with `Dt (φ m) = 1 ⊗ₜ D m` is an operator of order at most `k` relative to
`A' → B'`. -/
@[sga "3 VIIA 1.2.2" "partial"]
private lemma isDifferentialOperatorOfOrderLE_of_tmul {k : ℕ} {D : M →ₗ[A] P} {φ : M →ₗ[B] M'}
    (hφ : IsBaseChange A' (φ.restrictScalars A)) (hD : D.IsDifferentialOperatorOfOrderLE B k)
    (Dt : M' →ₗ[A'] B' ⊗[B] P) (hDt : ∀ m : M, Dt (φ m) = 1 ⊗ₜ[B] D m) :
    Dt.IsDifferentialOperatorOfOrderLE B' k :=
  isDifferentialOperatorOfOrderLE_of_comp_eq φ hφ (TensorProduct.mk B B' P 1) k hD hDt

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] [Algebra.IsPushout A A' B B'] in
/-- The base change of a universal operator is universal: an operator `E` of order at most `k`
relative to `A' → B'` factors uniquely through `Dt` by a `B'`-linear map. -/
private lemma existsUnique_comp_eq {k : ℕ} {D : M →ₗ[A] P} {φ : M →ₗ[B] M'}
    (hD : D.IsUniversalDifferentialOperatorOfOrderLE B k)
    (hφ : IsBaseChange A' (φ.restrictScalars A))
    (Dt : M' →ₗ[A'] B' ⊗[B] P) (hDt : ∀ m : M, Dt (φ m) = 1 ⊗ₜ[B] D m)
    {E : M' →ₗ[A'] N} (hE : E.IsDifferentialOperatorOfOrderLE B' k) :
    ∃! α : B' ⊗[B] P →ₗ[B'] N, ∀ x : M', α (Dt x) = E x := by
  obtain ⟨γ, hγ, -⟩ := hD.2 (N := N) (E.restrictScalars A ∘ₗ φ.restrictScalars A)
    (isDifferentialOperatorOfOrderLE_comp_restrictScalars φ k hE)
  refine ⟨γ.liftBaseChange B', ?_, ?_⟩
  · have key : ((γ.liftBaseChange B').restrictScalars A' ∘ₗ Dt : M' →ₗ[A'] N) = E := by
      refine hφ.algHom_ext _ _ fun m => ?_
      show (γ.liftBaseChange B') (Dt (φ m)) = E (φ m)
      rw [hDt m, LinearMap.liftBaseChange_one_tmul]
      exact hγ m
    exact fun x => LinearMap.congr_fun key x
  · intro α hα
    have hres : (α.restrictScalars B) ∘ₗ (TensorProduct.mk B B' P 1) =
        ((γ.liftBaseChange B').restrictScalars B) ∘ₗ (TensorProduct.mk B B' P 1) := by
      refine LinearMap.ext_on (span_range_eq_top hD) ?_
      rintro x ⟨m, rfl⟩
      show α (1 ⊗ₜ[B] D m) = (γ.liftBaseChange B') (1 ⊗ₜ[B] D m)
      rw [LinearMap.liftBaseChange_one_tmul, ← hDt m, hα (φ m)]
      exact (hγ m).symm
    exact (LinearMap.liftBaseChangeEquiv B').symm.injective
      (LinearMap.ext fun p => LinearMap.congr_fun hres p)

end BaseChange

/-! ### Lemma 0H8Z -/

/-- If `D : M → P` and `D' : M' → P'` are universal differential operators of order at most `k`
relative to `A → B` and `A' → B'`, where `B'` and `M'` are the base changes of `B` and `M` along
`A → A'`, then the `B`-linear map `ψ : P → P'` with `ψ ∘ D = D' ∘ φ` exhibits `P'` as the base
change of `P` along `A → A'`. -/
public theorem solution {A : Type*} {A' B B' M M' P P' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A A' B'] [IsScalarTower A B B'] [Algebra.IsPushout A A' B B']
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [AddCommGroup M'] [Module A M'] [Module A' M'] [Module B M'] [Module B' M']
    [IsScalarTower A A' M'] [IsScalarTower A B M'] [IsScalarTower A' B' M']
    [IsScalarTower B B' M']
    [AddCommGroup P] [Module A P] [Module B P] [IsScalarTower A B P]
    [AddCommGroup P'] [Module A P'] [Module A' P'] [Module B P'] [Module B' P']
    [IsScalarTower A A' P'] [IsScalarTower A B P'] [IsScalarTower A' B' P']
    [IsScalarTower B B' P']
    {k : ℕ} {D : M →ₗ[A] P} {D' : M' →ₗ[A'] P'}
    (hD : D.IsUniversalDifferentialOperatorOfOrderLE B k)
    (φ : M →ₗ[B] M') (hφ : IsBaseChange A' (φ.restrictScalars A))
    (hD' : D'.IsUniversalDifferentialOperatorOfOrderLE B' k)
    (ψ : P →ₗ[B] P') (hψ : ∀ m : M, ψ (D m) = D' (φ m)) :
    IsBaseChange A' (ψ.restrictScalars A) := by
  -- The base change `Dt = D ⊗ 1` of `D`, an operator of order at most `k` over `A' → B'`.
  obtain ⟨Dt, hDt⟩ : ∃ Dt : M' →ₗ[A'] B' ⊗[B] P, ∀ m : M, Dt (φ m) = 1 ⊗ₜ[B] D m :=
    ⟨hφ.lift ((TensorProduct.mk B B' P 1).restrictScalars A ∘ₗ D), fun m => hφ.lift_eq _ m⟩
  have hDtord : Dt.IsDifferentialOperatorOfOrderLE B' k :=
    isDifferentialOperatorOfOrderLE_of_tmul hφ hD.1 Dt hDt
  -- The two comparison maps between `B' ⊗[B] P` and `P'`, and their composites.
  obtain ⟨η, hη, -⟩ := existsUnique_comp_eq hD hφ Dt hDt hD'.1
  obtain ⟨θ, hθ, -⟩ := hD'.2 (N := B' ⊗[B] P) Dt hDtord
  have hηθ : η ∘ₗ θ = LinearMap.id :=
    (hD'.2 (N := P') D' hD'.1).unique (fun x => by rw [LinearMap.comp_apply, hθ x, hη x])
      fun x => rfl
  have hθη : θ ∘ₗ η = LinearMap.id :=
    (existsUnique_comp_eq hD hφ Dt hDt hDtord).unique
      (fun x => by rw [LinearMap.comp_apply, hη x, hθ x]) fun x => rfl
  -- The resulting isomorphism `B' ⊗[B] P ≃ P'` carries `1 ⊗ₜ p` to `ψ p`.
  have key : (η.restrictScalars B) ∘ₗ (TensorProduct.mk B B' P 1) = ψ := by
    refine LinearMap.ext_on (span_range_eq_top hD) ?_
    rintro x ⟨m, rfl⟩
    show η (1 ⊗ₜ[B] D m) = ψ (D m)
    rw [← hDt m, hη (φ m), hψ m]
  have hψη : ∀ p : P, η (1 ⊗ₜ[B] p) = ψ p := fun p => LinearMap.congr_fun key p
  refine IsBaseChange.of_equiv
    ((Algebra.IsPushout.cancelBaseChange A A' B B' P).symm.trans
      ((LinearEquiv.ofLinearMap η θ hηθ hθη).restrictScalars A')) fun p => ?_
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one, LinearEquiv.coe_ofLinearMap]
  exact hψη p

end Stacks.PrincipalParts.BaseChange

end

/-!
# Base change of the modules of principal parts

Let `A → A'` and `A → B` be ring maps, let `B'` be the pushout `B ⊗_A A'`, and let `M` be a
`B`-module. Then `M' = M ⊗_A A'` is a `B'`-module, and the commutative square of rings together
with the canonical `B`-linear map `M → M'` induces, by Remark 09CP, a map of modules of principal
parts `Pᵏ_{B/A}(M) → Pᵏ_{B'/A'}(M')` for every `k`. This file states that this map exhibits
`Pᵏ_{B'/A'}(M')` as the base change of `Pᵏ_{B/A}(M)` along `A → A'`:
`Pᵏ_{B/A}(M) ⊗_A A' = Pᵏ_{B'/A'}(M')`.

Modules of principal parts are used here in the form of Definition 09CL: a `B`-module `P` together
with an `A`-linear `D : M → P` *is* a `Pᵏ_{B/A}(M)` when `D` is a universal differential operator
of order at most `k` relative to `A → B`, that is, when `D` has order at most `k` and every
order-`≤ k` operator out of `M` factors through `D` by a unique `B`-linear map. So the statement
reads: for universal operators `D : M → P` over `A → B` and `D' : M' → P'` over `A' → B'`, the
unique `B`-linear `ψ : P → P'` with `ψ ∘ D = D' ∘ φ` — the map of Remark 09CP — makes `P'` the base
change of `P` along `A → A'`.

At `k = 0` the operators of order at most `0` are the `B`-linear maps, so `P = M` with `D` the
identity, `P' = M'` with `D'` the identity, and `ψ = φ`, and the statement reduces to
`M ⊗_A A' = M'`, which is the hypothesis on `φ`. At `k = 1` and `M = B` the source's Example 09CM
gives `P = Ω[B⁄A] × B` with `D b = (d b, b)`, so that for `A` a field, `A' = A[t]`, `B = A[X]` and
`B' = A[t][X]` the statement reads `(Ω[B⁄A] × B) ⊗_A A' = Ω[B'⁄A'] × B'`, both sides free of rank
`2` over `B'`; the isomorphism is then the base change of `Ω[B⁄A]` of Lemma 00RV together with
`B ⊗_A A' = B'`.

## Main results

* `LinearMap.IsUniversalDifferentialOperatorOfOrderLE.isBaseChange`: the map of Remark 09CP
  between modules of principal parts of order `k` along a base change `A → A'` exhibits
  `Pᵏ_{B'/A'}(M ⊗_A A')` as `Pᵏ_{B/A}(M) ⊗_A A'`.

## Implementation notes

`B' = B ⊗_A A'` is taken in the abstract form `Algebra.IsPushout A A' B B'`, and both occurrences
of `- ⊗_A A'` in Mathlib's form `IsBaseChange A'`, as in `KaehlerDifferential.isBaseChange` and in
Lemma 0H8Y; the statement therefore applies to any rings and modules realising these tensor
products, the standard models included. `IsBaseChange.equiv` turns the conclusion into a linear
equivalence `A' ⊗[A] P ≃ₗ[A'] P'` compatible with `ψ`, which is the displayed equality of the
source.

The modules of principal parts enter through the property of Definition 09CL rather than through a
chosen construction, as in Lemma 09CN: a pair `(P, D)` with the universal property is what
`Pᵏ_{B/A}(M)` is, it is determined up to unique isomorphism, and existence is Lemma 09CK. Neither
`M'` nor `P'` is a chosen tensor product either, so the hypotheses say exactly which square of
modules is meant: `φ` is `B`-linear and makes `M'` the base change of `M`, whence the `B'`-action
on `M'` is the one of the source, since `B'` is generated as an `A`-algebra by the images of `B`
and `A'`; and `hψ` says `ψ ∘ D = D' ∘ φ`.

The map of Remark 09CP is pinned by `hψ`, not merely asserted to exist: a universal `D` forces `P`
to be generated over `B` by the image of `D`, so a `B`-linear map out of `P` is determined by its
values on that image. This is why `ψ` is asked to be `B`-linear and not just `A`-linear — over `A`
the image of `D` does not generate `P` and `hψ` would leave `ψ` undetermined. Remark 09CP itself,
which produces `ψ` and its compatibilities, is a separate statement; here it suffices to
hypothesise a map with its characteristic property, and the theorem is then the assertion that it
is an isomorphism after base change, which is the content of the lemma.

The source's proof establishes the equivalent form that the base change of a universal operator is
again universal, `D ⊗ 1 : M ⊗_A A' → P ⊗_A A'`; with Lemma 09CK and the uniqueness of universal
objects, that form and the one stated here imply each other, and the form stated here is the one
that says the map of Remark 09CP is an isomorphism.

All of `A'`, `B`, `B'`, `M`, `M'`, `P` and `P'` live in a single universe `u`, while `A` is
arbitrary. Definition 09CL asks its universal property for test modules in the universe generated
by the ring, the source and the target, so the two hypotheses `hD` and `hD'` here speak about test
modules for `(B, M, P)` and for `(B', M', P')` respectively; the argument feeds `P'` to the first
and `A' ⊗[A] P` to the second, so the two test universes must agree. Nothing mathematical is lost,
since a pair with the property in one universe has it in every universe and any instantiation is a
lift of one in a common universe; `A` is unconstrained because its universe enters neither test
universe. The conclusion `IsBaseChange` is itself universe-free, being the bijectivity of one
canonical map.

Faithfulness. (1) No dead hypothesis: `hφ` is what makes `M'` the base change of `M` (without it,
`φ = 0` and `ψ = 0` satisfy everything else while `P' ≠ 0`), `hD` and `hD'` are what make `P` and
`P'` modules of principal parts, `hψ` is what makes `ψ` the map of Remark 09CP, and
`Algebra.IsPushout A A' B B'` is essential and not implied by the rest: for `A = A' = B = M = k` a
field, `B' = k[X]` acting on `M' = k` through `X ↦ 0`, the two sides at `k = 1` have `k`-dimensions
`1` and `2`. (2) The scalars and base are the source's: `D` is `A`-linear with order measured over
`B`, `D'` is `A'`-linear with order measured over `B'`, `φ` and `ψ` are `B`-linear, and both base
changes are along `A → A'` — not along `B → B'`, which would be a different statement. (3) The
canonical map is pinned: `ψ` is the unique `B`-linear map with `ψ (D m) = D' (φ m)`, and it is of
`ψ` that the conclusion speaks; that *some* isomorphism `Pᵏ_{B/A}(M) ⊗_A A' ≅ Pᵏ_{B'/A'}(M')`
exists is weaker. (4) The instantiation is not degenerate: the whole hypothesis set is inhabited
with `A = ℤ`, `A' = B' = M' = P' = ℤ[X]`, `B = M = P = ℤ`, `k = 0`, `D = D' = id` and
`φ = ψ = Algebra.linearMap ℤ ℤ[X]` — at those types every typeclass hypothesis of the statement,
`Algebra.IsPushout ℤ ℤ[X] ℤ ℤ[X]` included, is found by inference, and `hφ` is
`IsBaseChange.linearMap ℤ ℤ[X]`, both compiled; `hψ` is `rfl`, and that the identity is universal
at `k = 0` is the witness compiled for Definition 09CL. There the conclusion is the assertion that
`ℤ[X]` is the base change of `ℤ` along `ℤ → ℤ[X]`. The `k = 1`, `M = B` case described above is an
instantiation in which `P` and `P'` are free of rank `2` and `ψ` is not the identity.

## References

* [Stacks 0H8Z](https://stacks.math.columbia.edu/tag/0H8Z), in the section "Finite order
  differential operators" (Tag 09CH). Definition 09CI is
  `LinearMap.IsDifferentialOperatorOfOrderLE`, Definition 09CL is
  `LinearMap.IsUniversalDifferentialOperatorOfOrderLE`, Lemma 09CK is
  `LinearMap.exists_universal_isDifferentialOperatorOfOrderLE`, and Remark 09CP, which produces
  the map `ψ`, has no declaration of its own.
* [Stacks 00RV](https://stacks.math.columbia.edu/tag/00RV), the case `k = 1`, `M = B` of the
  underlying base change of Kähler differentials, in Mathlib as
  `KaehlerDifferential.isBaseChange`.
-/

@[expose] public section



namespace LinearMap.IsUniversalDifferentialOperatorOfOrderLE

variable {A : Type*} {A' B B' M M' P P' : Type u}

/-- **Stacks 0H8Z.** Let `A → A'` and `A → B` be ring maps, let `B' = B ⊗_A A'`, let `M` be a
`B`-module and let `M' = M ⊗_A A'`, a `B'`-module, with `φ : M → M'` the canonical map. Let
`D : M → P` be a universal differential operator of order at most `k` relative to `A → B` and let
`D' : M' → P'` be one relative to `A' → B'`, so that `P = Pᵏ_{B/A}(M)` and `P' = Pᵏ_{B'/A'}(M')`
are modules of principal parts. Then the map `ψ : P → P'` of Remark 09CP, i.e. the unique
`B`-linear map with `ψ ∘ D = D' ∘ φ`, exhibits `P'` as the base change of `P` along `A → A'`:
`Pᵏ_{B/A}(M) ⊗_A A' = Pᵏ_{B'/A'}(M')`. -/
@[stacks 0H8Z "Modules of principal parts appear through the universal property of Definition 09CL
rather than as chosen constructions, and both base changes in Mathlib's `IsBaseChange` form. The
map of Remark 09CP is the hypothesis `hψ`, which pins it since a universal `D` generates `P` over
`B`. See the module docstring."]
public theorem isBaseChange
    [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A A' B'] [IsScalarTower A B B'] [Algebra.IsPushout A A' B B']
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [AddCommGroup M'] [Module A M'] [Module A' M'] [Module B M'] [Module B' M']
    [IsScalarTower A A' M'] [IsScalarTower A B M'] [IsScalarTower A' B' M']
    [IsScalarTower B B' M']
    [AddCommGroup P] [Module A P] [Module B P] [IsScalarTower A B P]
    [AddCommGroup P'] [Module A P'] [Module A' P'] [Module B P'] [Module B' P']
    [IsScalarTower A A' P'] [IsScalarTower A B P'] [IsScalarTower A' B' P']
    [IsScalarTower B B' P']
    {k : ℕ} {D : M →ₗ[A] P} {D' : M' →ₗ[A'] P'}
    (hD : D.IsUniversalDifferentialOperatorOfOrderLE B k)
    (φ : M →ₗ[B] M') (hφ : IsBaseChange A' (φ.restrictScalars A))
    (hD' : D'.IsUniversalDifferentialOperatorOfOrderLE B' k)
    (ψ : P →ₗ[B] P') (hψ : ∀ m : M, ψ (D m) = D' (φ m)) :
    IsBaseChange A' (ψ.restrictScalars A) :=
  Stacks.PrincipalParts.BaseChange.solution (B' := B') hD φ hφ hD' ψ hψ

end LinearMap.IsUniversalDifferentialOperatorOfOrderLE

end
