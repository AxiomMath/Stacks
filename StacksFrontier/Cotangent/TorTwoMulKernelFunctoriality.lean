module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksFrontier.Cotangent.TorTwoQuotientSelf

/-!
# The tensor-kernel model of `Tor₂^P(B, B)`, its functoriality and its alternating map

For a surjective ring map `φ : P → B` with kernel `J`, `Stacks.Cotangent.torTwoSelfIsoMulKernel`
identifies `Tor₂^P(B, B)` with `Ker(J ⊗_P J → J²)`. This file develops the structure of that
model used in Stacks Remark 09D6.

* The model is a `B`-module: `J` acts on `Ker(J ⊗_P J → J²)` by zero, so when `φ` is surjective
  the `P`-action descends to `B`. The conormal module `J/J²` is a `B`-module in the same way.
* It is functorial: a ring map `g : P → P'` with `φ' ∘ g = φ` maps `J` into `J' = ker φ'` and
  induces a `B`-linear map `Ker(J ⊗_P J → J²) → Ker(J' ⊗_{P'} J' → J'²)`, compatibly with
  identities and composition. These are the maps that the face and degeneracy maps of a
  simplicial resolution induce on `Tor₂`.
* The antisymmetrisation `∧²_B(J/J²) → Ker(J ⊗_P J → J²)`, `ā ∧ b̄ ↦ a ⊗ b - b ⊗ a`, the first
  map of the exact sequence of 09D6.

## Main definitions

* `Stacks.Cotangent.TorTwo.mulKernel`: `Ker(J ⊗_P J → J²)` for `J = ker φ`.
* `Stacks.Cotangent.TorTwo.mulKernelMap`: the map induced by a ring map over `B`.
* `Stacks.Cotangent.TorTwo.antisymm`: `(a, b) ↦ a ⊗ b - b ⊗ a`, valued in the model.
* `Stacks.Cotangent.TorTwo.cotangentLift`: descent of an additive map out of `J` to `J/J²`.
* `Stacks.Cotangent.TorTwo.exteriorTwoLift`: the map out of `∧²` induced by an alternating
  bilinear map.
* `Stacks.Cotangent.TorTwo.wedgeAntisymm`: the antisymmetrisation `∧²_B(J/J²) → Ker(J ⊗ J → J²)`.

## Implementation notes

The `B`-module structures are instances under `[Fact (Function.Surjective φ)]`: `b` acts as any
preimage of `b` does, which is well defined because `J` acts by zero. Ring maps rather than
`Algebra` instances carry the augmentations, since in a simplicial resolution several rings map
to the same `B`, and two different ring maps out of one ring (the face maps `d₀, d₁`) are
compared.

The model is the kernel of `Submodule.mulMap'`, exactly the target of
`Stacks.Cotangent.torTwoSelfIsoMulKernel`, so that identification applies verbatim.

## References

* [Stacks Project, Tag 09D6](https://stacks.math.columbia.edu/tag/09D6)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v w

namespace Stacks.Cotangent.TorTwo

/-! ### Modules over a quotient ring through a surjection -/

section DescendModule

variable {P : Type u} {B : Type v} [CommRing P] [CommRing B] (φ : P →+* B)
  {M : Type w} [AddCommGroup M] [Module P M]

/-- A `P`-module on which `ker φ` acts by zero is a `B`-module when `φ` is surjective: `b` acts
as any preimage of `b`. -/
abbrev moduleOfSurjective (hφ : Function.Surjective φ)
    (hM : ∀ r : P, φ r = 0 → ∀ m : M, r • m = 0) :
    Module B M :=
  have key : ∀ r r' : P, φ r = φ r' → ∀ m : M, r • m = r' • m := fun r r' h m => by
    have := hM (r - r') (by rw [map_sub, h, sub_self]) m
    rwa [sub_smul, sub_eq_zero] at this
  { smul := fun b m => Function.surjInv hφ b • m
    one_smul := fun m => by
      change Function.surjInv hφ 1 • m = m
      rw [key _ 1 (by rw [Function.surjInv_eq hφ, map_one]), one_smul]
    mul_smul := fun b b' m => by
      change Function.surjInv hφ (b * b') • m =
        Function.surjInv hφ b • Function.surjInv hφ b' • m
      rw [← mul_smul]
      exact key _ _ (by rw [Function.surjInv_eq hφ, map_mul, Function.surjInv_eq hφ,
        Function.surjInv_eq hφ]) m
    smul_zero := fun b => smul_zero (Function.surjInv hφ b)
    smul_add := fun b m m' => smul_add (Function.surjInv hφ b) m m'
    add_smul := fun b b' m => by
      change Function.surjInv hφ (b + b') • m =
        Function.surjInv hφ b • m + Function.surjInv hφ b' • m
      rw [← add_smul]
      exact key _ _ (by rw [Function.surjInv_eq hφ, map_add, Function.surjInv_eq hφ,
        Function.surjInv_eq hφ]) m
    zero_smul := fun m => by
      change Function.surjInv hφ 0 • m = 0
      rw [key _ 0 (by rw [Function.surjInv_eq hφ, map_zero]), zero_smul] }

/-- In `moduleOfSurjective`, `φ r` acts as `r` does. -/
theorem moduleOfSurjective_smul (hφ : Function.Surjective φ)
    (hM : ∀ r : P, φ r = 0 → ∀ m : M, r • m = 0) (r : P) (m : M) :
    (moduleOfSurjective φ hφ hM).smul (φ r) m = r • m := by
  show Function.surjInv hφ (φ r) • m = r • m
  have := hM (Function.surjInv hφ (φ r) - r)
    (by rw [map_sub, Function.surjInv_eq hφ, sub_self]) m
  rwa [sub_smul, sub_eq_zero] at this

end DescendModule

/-! ### The tensor-kernel model -/

section Model

variable {P : Type u} {B : Type v} [CommRing P] [CommRing B] (φ : P →+* B)

/-- The tensor-kernel model `Ker(J ⊗_P J → J²)` of `Tor₂^P(B, B)`, for `J = ker φ`. -/
def mulKernel : Submodule P (RingHom.ker φ ⊗[P] RingHom.ker φ) :=
  LinearMap.ker (Submodule.mulMap' (RingHom.ker φ) (RingHom.ker φ))

variable {φ}

/-- An element of `J ⊗_P J` lies in `mulKernel φ` if and only if its product in `P` vanishes. -/
theorem mem_mulKernel_iff (x : RingHom.ker φ ⊗[P] RingHom.ker φ) :
    x ∈ mulKernel φ ↔ Submodule.mulMap (RingHom.ker φ) (RingHom.ker φ) x = 0 := by
  rw [mulKernel, ker_mulMap'_eq]
  rfl

/-- Multiplication `J ⊗_P J → J`, `a ⊗ b ↦ ab`. -/
def mulIntoIdeal : RingHom.ker φ ⊗[P] RingHom.ker φ →ₗ[P] RingHom.ker φ :=
  TensorProduct.lift (LinearMap.lsmul P (RingHom.ker φ) ∘ₗ (RingHom.ker φ).subtype)

/-- `mulIntoIdeal` sends `a ⊗ b` to `ab`. -/
@[simp]
theorem mulIntoIdeal_tmul (a b : RingHom.ker φ) :
    mulIntoIdeal (a ⊗ₜ[P] b) = (a : P) • b := rfl

/-- As an element of `P`, `mulIntoIdeal x` is the image of `x` under `Submodule.mulMap`. -/
theorem coe_mulIntoIdeal (x : RingHom.ker φ ⊗[P] RingHom.ker φ) :
    (mulIntoIdeal x : P) = Submodule.mulMap (RingHom.ker φ) (RingHom.ker φ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Submodule.mulMap_tmul]
  | add x y hx hy => simp [hx, hy]

/-- An element `j` of `J` acts on `J ⊗_P J` as `x ↦ j ⊗ m(x)`, `m` the multiplication. -/
theorem smul_eq_tmul_mulIntoIdeal (j : RingHom.ker φ) (x : RingHom.ker φ ⊗[P] RingHom.ker φ) :
    (j : P) • x = j ⊗ₜ[P] mulIntoIdeal x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.smul_tmul', mulIntoIdeal_tmul,
      show (j : P) • a = (a : P) • j from Subtype.ext (mul_comm (j : P) (a : P)),
      TensorProduct.smul_tmul]
  | add x y hx hy => rw [smul_add, hx, hy, map_add, TensorProduct.tmul_add]

/-- `J` acts by zero on the tensor-kernel model. -/
theorem smul_mulKernel_eq_zero (r : P) (hr : φ r = 0) (x : mulKernel φ) : r • x = 0 := by
  apply Subtype.ext
  show r • (x : RingHom.ker φ ⊗[P] RingHom.ker φ) = 0
  have hx : mulIntoIdeal (x : RingHom.ker φ ⊗[P] RingHom.ker φ) = 0 :=
    Subtype.ext ((coe_mulIntoIdeal _).trans ((mem_mulKernel_iff _).mp x.2))
  rw [smul_eq_tmul_mulIntoIdeal (⟨r, hr⟩ : RingHom.ker φ), hx, TensorProduct.tmul_zero]

/-- `J` acts by zero on the conormal module `J/J²`. -/
theorem smul_cotangent_eq_zero (r : P) (hr : φ r = 0) (c : (RingHom.ker φ).Cotangent) :
    r • c = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ c
  rw [← map_smul, Ideal.toCotangent_eq_zero]
  show r * (a : P) ∈ RingHom.ker φ ^ 2
  rw [pow_two]
  exact Ideal.mul_mem_mul hr a.2

/-- For surjective `φ`, the tensor-kernel model is a `B`-module, `φ r` acting as `r`. -/
instance [Fact (Function.Surjective φ)] : Module B (mulKernel φ) :=
  moduleOfSurjective φ Fact.out fun r hr x => smul_mulKernel_eq_zero r hr x

/-- For surjective `φ`, the conormal module `J/J²` is a `B`-module, `φ r` acting as `r`. -/
instance [Fact (Function.Surjective φ)] : Module B (RingHom.ker φ).Cotangent :=
  moduleOfSurjective φ Fact.out fun r hr c => smul_cotangent_eq_zero r hr c

/-- On the tensor-kernel model, `φ r` acts as `r` does. -/
theorem algebraMap_smul_mulKernel [Fact (Function.Surjective φ)] (r : P) (x : mulKernel φ) :
    φ r • x = r • x :=
  moduleOfSurjective_smul φ Fact.out (fun r hr x => smul_mulKernel_eq_zero r hr x) r x

/-- On the conormal module `J/J²`, `φ r` acts as `r` does. -/
theorem algebraMap_smul_cotangent [Fact (Function.Surjective φ)] (r : P)
    (c : (RingHom.ker φ).Cotangent) : φ r • c = r • c :=
  moduleOfSurjective_smul φ Fact.out (fun r hr c => smul_cotangent_eq_zero r hr c) r c

/-- On the tensor-kernel model, `b : B` acts as the chosen preimage `Function.surjInv _ b`. -/
theorem smul_mulKernel_def [Fact (Function.Surjective φ)] (b : B) (x : mulKernel φ) :
    b • x = Function.surjInv (Fact.out : Function.Surjective φ) b • x := rfl

/-- On the conormal module `J/J²`, `b : B` acts as the chosen preimage `Function.surjInv _ b`. -/
theorem smul_cotangent_def [Fact (Function.Surjective φ)] (b : B)
    (c : (RingHom.ker φ).Cotangent) :
    b • c = Function.surjInv (Fact.out : Function.Surjective φ) b • c := rfl

end Model

/-! ### Functoriality -/

section Functoriality

variable {P : Type u} {P' : Type v} {P'' : Type w} {B : Type*}
  [CommRing P] [CommRing P'] [CommRing P''] [CommRing B]
  {φ : P →+* B} {φ' : P' →+* B} {φ'' : P'' →+* B}

/-- A ring map over `B` maps `ker φ` into `ker φ'`. -/
def kerMap (g : P →+* P') (hg : φ'.comp g = φ) : RingHom.ker φ →+ RingHom.ker φ' where
  toFun a := ⟨g a.1, by rw [RingHom.mem_ker, ← RingHom.comp_apply, hg]; exact a.2⟩
  map_zero' := Subtype.ext (map_zero g)
  map_add' a b := Subtype.ext (map_add g a.1 b.1)

/-- `kerMap g hg` is `g` on underlying elements. -/
@[simp]
theorem coe_kerMap (g : P →+* P') (hg : φ'.comp g = φ) (a : RingHom.ker φ) :
    (kerMap g hg a : P') = g a.1 := rfl

/-- `kerMap g hg` is semilinear along `g`. -/
theorem kerMap_smul (g : P →+* P') (hg : φ'.comp g = φ) (r : P) (a : RingHom.ker φ) :
    kerMap g hg (r • a) = g r • kerMap g hg a :=
  Subtype.ext (map_mul g r a.1)

/-- The map `J ⊗_P J → J' ⊗_{P'} J'` induced by a ring map over `B`. -/
def tensorMap (g : P →+* P') (hg : φ'.comp g = φ) :
    RingHom.ker φ ⊗[P] RingHom.ker φ →+ RingHom.ker φ' ⊗[P'] RingHom.ker φ' :=
  TensorProduct.liftAddHom
    { toFun := fun a => ((TensorProduct.mk P' _ _ (kerMap g hg a)).toAddMonoidHom).comp
        (kerMap g hg)
      map_zero' := by ext b; simp
      map_add' := fun a a' => by ext b; simp }
    fun r a b => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply, kerMap_smul,
        TensorProduct.smul_tmul]

/-- `tensorMap g hg` sends `a ⊗ b` to `g a ⊗ g b`. -/
@[simp]
theorem tensorMap_tmul (g : P →+* P') (hg : φ'.comp g = φ) (a b : RingHom.ker φ) :
    tensorMap g hg (a ⊗ₜ[P] b) = kerMap g hg a ⊗ₜ[P'] kerMap g hg b := rfl

/-- `tensorMap g hg` is semilinear along `g`. -/
theorem tensorMap_smul (g : P →+* P') (hg : φ'.comp g = φ) (r : P)
    (x : RingHom.ker φ ⊗[P] RingHom.ker φ) :
    tensorMap g hg (r • x) = g r • tensorMap g hg x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [TensorProduct.smul_tmul', tensorMap_tmul, tensorMap_tmul, kerMap_smul,
      TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `tensorMap g hg` commutes with multiplication: the product of its image is `g` of the
product. -/
theorem mulMap_tensorMap (g : P →+* P') (hg : φ'.comp g = φ)
    (x : RingHom.ker φ ⊗[P] RingHom.ker φ) :
    Submodule.mulMap (RingHom.ker φ') (RingHom.ker φ') (tensorMap g hg x) =
      g (Submodule.mulMap (RingHom.ker φ) (RingHom.ker φ) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Submodule.mulMap_tmul]
  | add x y hx hy => simp [hx, hy]

/-- The identity ring map induces the identity on `J ⊗_P J`. -/
theorem tensorMap_id (x : RingHom.ker φ ⊗[P] RingHom.ker φ) :
    tensorMap (RingHom.id P) (RingHom.comp_id φ) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, hx, hy]

/-- `tensorMap` sends a composite of ring maps over `B` to the composite of the induced maps. -/
theorem tensorMap_comp (g : P →+* P') (hg : φ'.comp g = φ) (g' : P' →+* P'')
    (hg' : φ''.comp g' = φ') (x : RingHom.ker φ ⊗[P] RingHom.ker φ) :
    tensorMap (g'.comp g) (by rw [← RingHom.comp_assoc, hg', hg]) x =
      tensorMap g' hg' (tensorMap g hg x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

/-- `tensorMap g hg` maps `Ker(J ⊗_P J → J²)` into `Ker(J' ⊗_{P'} J' → J'²)`. -/
theorem tensorMap_mem_mulKernel (g : P →+* P') (hg : φ'.comp g = φ) (x : mulKernel φ) :
    tensorMap g hg x ∈ mulKernel φ' := by
  rw [mem_mulKernel_iff, mulMap_tensorMap, (mem_mulKernel_iff _).mp x.2, map_zero]

/-- The additive map `Ker(J ⊗_P J → J²) → Ker(J' ⊗_{P'} J' → J'²)` induced by a ring map
over `B`. -/
def mulKernelAddMap (g : P →+* P') (hg : φ'.comp g = φ) : mulKernel φ →+ mulKernel φ' where
  toFun x := ⟨tensorMap g hg x, tensorMap_mem_mulKernel g hg x⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

variable [Fact (Function.Surjective φ)] [Fact (Function.Surjective φ')]

/-- **The map induced on the model of `Tor₂(B, B)` by a ring map `g : P → P'` over `B`.** It is
`B`-linear. -/
def mulKernelMap (g : P →+* P') (hg : φ'.comp g = φ) : mulKernel φ →ₗ[B] mulKernel φ' where
  toAddHom := (mulKernelAddMap g hg).toAddHom
  map_smul' b x := by
    apply Subtype.ext
    change tensorMap g hg ((Function.surjInv (Fact.out : Function.Surjective φ) b) • (x : _)) =
      ((b • (⟨tensorMap g hg x, tensorMap_mem_mulKernel g hg x⟩ : mulKernel φ') :
        mulKernel φ') : RingHom.ker φ' ⊗[P'] RingHom.ker φ')
    rw [tensorMap_smul]
    conv_rhs => rw [show b = φ' (g (Function.surjInv (Fact.out : Function.Surjective φ) b)) by
      rw [← RingHom.comp_apply, hg, Function.surjInv_eq (Fact.out : Function.Surjective φ)],
      algebraMap_smul_mulKernel]
    rfl

/-- On underlying elements of `J ⊗_P J`, `mulKernelMap g hg` is `tensorMap g hg`. -/
@[simp]
theorem coe_mulKernelMap (g : P →+* P') (hg : φ'.comp g = φ) (x : mulKernel φ) :
    (mulKernelMap g hg x : RingHom.ker φ' ⊗[P'] RingHom.ker φ') = tensorMap g hg x := rfl

/-- The identity ring map induces the identity on the tensor-kernel model. -/
theorem mulKernelMap_id (x : mulKernel φ) :
    mulKernelMap (RingHom.id P) (RingHom.comp_id φ) x = x :=
  Subtype.ext (tensorMap_id _)

/-- `mulKernelMap` sends a composite of ring maps over `B` to the composite of the induced
maps. -/
theorem mulKernelMap_comp [Fact (Function.Surjective φ'')] (g : P →+* P') (hg : φ'.comp g = φ)
    (g' : P' →+* P'') (hg' : φ''.comp g' = φ') (x : mulKernel φ) :
    mulKernelMap (g'.comp g) (by rw [← RingHom.comp_assoc, hg', hg]) x =
      mulKernelMap g' hg' (mulKernelMap g hg x) :=
  Subtype.ext (tensorMap_comp g hg g' hg' _)

/-- Two ring maps that agree induce the same map on the model; the proofs of compatibility
are irrelevant. -/
theorem mulKernelMap_congr {g₁ g₂ : P →+* P'} (h : g₁ = g₂) (hg₁ : φ'.comp g₁ = φ)
    (hg₂ : φ'.comp g₂ = φ) (x : mulKernel φ) :
    mulKernelMap g₁ hg₁ x = mulKernelMap g₂ hg₂ x := by
  subst h
  rfl

end Functoriality

/-! ### The antisymmetrisation -/

section Antisymm

variable {P : Type u} {B : Type v} [CommRing P] [CommRing B] {φ : P →+* B}

/-- For `a, b ∈ J`, the element `a ⊗ b - b ⊗ a` lies in `Ker(J ⊗_P J → J²)`. -/
theorem antisymm_mem (a b : RingHom.ker φ) : a ⊗ₜ[P] b - b ⊗ₜ[P] a ∈ mulKernel φ := by
  rw [mem_mulKernel_iff, map_sub, Submodule.mulMap_tmul, Submodule.mulMap_tmul, mul_comm,
    sub_self]

/-- `(a, b) ↦ a ⊗ b - b ⊗ a`, an element of `Ker(J ⊗_P J → J²)`. -/
def antisymm (a b : RingHom.ker φ) : mulKernel φ :=
  ⟨a ⊗ₜ[P] b - b ⊗ₜ[P] a, antisymm_mem a b⟩

/-- The underlying element of `antisymm a b` is `a ⊗ b - b ⊗ a`. -/
@[simp]
theorem coe_antisymm (a b : RingHom.ker φ) :
    (antisymm a b : RingHom.ker φ ⊗[P] RingHom.ker φ) = a ⊗ₜ[P] b - b ⊗ₜ[P] a := rfl

/-- `antisymm a a = 0`. -/
theorem antisymm_self (a : RingHom.ker φ) : antisymm a a = 0 :=
  Subtype.ext (sub_self _)

/-- `antisymm` is antisymmetric. -/
theorem antisymm_swap (a b : RingHom.ker φ) : antisymm b a = -antisymm a b :=
  Subtype.ext (neg_sub _ _).symm

/-- `antisymm` is additive in its first argument. -/
theorem antisymm_add_left (a a' b : RingHom.ker φ) :
    antisymm (a + a') b = antisymm a b + antisymm a' b :=
  Subtype.ext (by simp only [coe_antisymm, Submodule.coe_add, TensorProduct.add_tmul,
    TensorProduct.tmul_add]; abel)

/-- `antisymm` is additive in its second argument. -/
theorem antisymm_add_right (a b b' : RingHom.ker φ) :
    antisymm a (b + b') = antisymm a b + antisymm a b' :=
  Subtype.ext (by simp only [coe_antisymm, Submodule.coe_add, TensorProduct.add_tmul,
    TensorProduct.tmul_add]; abel)

/-- `antisymm` is `P`-linear in its first argument. -/
theorem antisymm_smul_left (r : P) (a b : RingHom.ker φ) :
    antisymm (r • a) b = r • antisymm a b :=
  Subtype.ext (by simp only [coe_antisymm, SetLike.val_smul, smul_sub,
    TensorProduct.smul_tmul', TensorProduct.tmul_smul])

/-- `antisymm` is `P`-linear in its second argument. -/
theorem antisymm_smul_right (r : P) (a b : RingHom.ker φ) :
    antisymm a (r • b) = r • antisymm a b := by
  rw [← neg_neg (antisymm a (r • b)), ← antisymm_swap, antisymm_smul_left, antisymm_swap,
    smul_neg, neg_neg]

/-- `antisymm 0 b = 0`. -/
theorem antisymm_zero_left (b : RingHom.ker φ) : antisymm 0 b = 0 :=
  Subtype.ext (by simp)

/-- `antisymm a 0 = 0`. -/
theorem antisymm_zero_right (a : RingHom.ker φ) : antisymm a 0 = 0 :=
  Subtype.ext (by simp)

/-- The map induced by a ring map `g` over `B` sends `a ⊗ b - b ⊗ a` to
`g a ⊗ g b - g b ⊗ g a`. -/
theorem mulKernelMap_antisymm {P' : Type w} [CommRing P'] {φ' : P' →+* B}
    [Fact (Function.Surjective φ)] [Fact (Function.Surjective φ')]
    (g : P →+* P') (hg : φ'.comp g = φ) (a b : RingHom.ker φ) :
    mulKernelMap g hg (antisymm a b) = antisymm (kerMap g hg a) (kerMap g hg b) :=
  Subtype.ext (by simp)

end Antisymm

/-! ### Descending through `J → J/J²` -/

section CotangentLift

variable {P : Type u} {B : Type v} [CommRing P] [CommRing B] {φ : P →+* B}
  [Fact (Function.Surjective φ)] {N : Type w} [AddCommGroup N] [Module B N]

omit [Fact (Function.Surjective φ)] in
/-- An additive map `g : J →+ N` with `g (r • a) = φ r • g a` takes equal values on elements of
`J` with the same image in `J/J²`. -/
theorem eq_of_toCotangent_eq (g : RingHom.ker φ →+ N) (hg : ∀ (r : P) (a : RingHom.ker φ),
    g (r • a) = φ r • g a) {a a' : RingHom.ker φ}
    (h : (RingHom.ker φ).toCotangent a = (RingHom.ker φ).toCotangent a') : g a = g a' := by
  have h0 : (RingHom.ker φ).toCotangent (a - a') = 0 := by rw [map_sub, h, sub_self]
  have hmem : a - a' ∈ (RingHom.ker φ • ⊤ : Submodule P (RingHom.ker φ)) :=
    (Submodule.Quotient.mk_eq_zero _).mp h0
  have hz : g (a - a') = 0 := by
    refine Submodule.smul_induction_on hmem ?_ ?_
    · intro r hr y _
      rw [hg, show φ r = 0 from hr, zero_smul]
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]
  rwa [map_sub, sub_eq_zero] at hz

/-- An additive map `g : J →+ N` into a `B`-module with `g (r • a) = φ r • g a` descends to a
`B`-linear map `J/J² → N`. -/
def cotangentLift (g : RingHom.ker φ →+ N) (hg : ∀ (r : P) (a : RingHom.ker φ),
    g (r • a) = φ r • g a) : (RingHom.ker φ).Cotangent →ₗ[B] N where
  toFun c := g (Function.surjInv (Ideal.toCotangent_surjective _) c)
  map_add' c c' := by
    rw [← map_add]
    refine eq_of_toCotangent_eq g hg ?_
    rw [map_add, Function.surjInv_eq (Ideal.toCotangent_surjective _),
      Function.surjInv_eq (Ideal.toCotangent_surjective _),
      Function.surjInv_eq (Ideal.toCotangent_surjective _)]
  map_smul' b c := by
    have hb := Function.surjInv_eq (Fact.out : Function.Surjective φ) b
    change g _ = b • g _
    conv_rhs => rw [← hb, ← hg]
    refine eq_of_toCotangent_eq g hg ?_
    rw [map_smul, Function.surjInv_eq (Ideal.toCotangent_surjective _),
      Function.surjInv_eq (Ideal.toCotangent_surjective _)]
    rfl

/-- `cotangentLift g hg` sends the class of `a` in `J/J²` to `g a`. -/
@[simp]
theorem cotangentLift_toCotangent (g : RingHom.ker φ →+ N)
    (hg : ∀ (r : P) (a : RingHom.ker φ), g (r • a) = φ r • g a) (a : RingHom.ker φ) :
    cotangentLift g hg ((RingHom.ker φ).toCotangent a) = g a :=
  eq_of_toCotangent_eq g hg (Function.surjInv_eq (Ideal.toCotangent_surjective _) _)

/-- Two `B`-linear maps out of `J/J²` agreeing on the classes of all elements of `J` agree. -/
theorem cotangent_linearMap_ext {N : Type w} [AddCommGroup N] [Module B N]
    {f g : (RingHom.ker φ).Cotangent →ₗ[B] N}
    (h : ∀ a : RingHom.ker φ, f ((RingHom.ker φ).toCotangent a) =
      g ((RingHom.ker φ).toCotangent a)) : f = g := by
  ext c
  obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ c
  exact h a

end CotangentLift

/-! ### Maps out of the second exterior power -/

section ExteriorTwo

variable {R : Type u} [CommRing R] {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- An alternating bilinear map, read as an alternating map on `Fin 2`-indexed families. -/
def alternatingOfBilin (β : M →ₗ[R] M →ₗ[R] N) (hβ : ∀ x, β x x = 0) :
    M [⋀^Fin 2]→ₗ[R] N where
  toFun v := β (v 0) (v 1)
  map_update_add' := by
    intro _ v i x y
    fin_cases i
    · simp only [Function.update, Fin.isValue, Fin.zero_eta, ↓reduceDIte, one_ne_zero, map_add,
        LinearMap.add_apply]
    · simp only [Function.update, Fin.isValue, Fin.mk_one, zero_ne_one, ↓reduceDIte, map_add]
  map_update_smul' := by
    intro _ v i c x
    fin_cases i
    · simp only [Function.update, Fin.isValue, Fin.zero_eta, ↓reduceDIte, one_ne_zero, map_smul,
        LinearMap.smul_apply]
    · simp only [Function.update, Fin.isValue, Fin.mk_one, zero_ne_one, ↓reduceDIte, map_smul]
  map_eq_zero_of_eq' := by
    intro v i j hv hij
    have h01 : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    change β (v 0) (v 1) = 0
    rw [h01, hβ]

/-- The linear map `∧²M → N` induced by an alternating bilinear map. -/
def exteriorTwoLift (β : M →ₗ[R] M →ₗ[R] N) (hβ : ∀ x, β x x = 0) : ⋀[R]^2 M →ₗ[R] N :=
  exteriorPower.alternatingMapLinearEquiv (alternatingOfBilin β hβ)

/-- `exteriorTwoLift β hβ` sends `v 0 ∧ v 1` to `β (v 0) (v 1)`. -/
theorem exteriorTwoLift_ιMulti (β : M →ₗ[R] M →ₗ[R] N) (hβ : ∀ x, β x x = 0) (v : Fin 2 → M) :
    exteriorTwoLift β hβ (exteriorPower.ιMulti R 2 v) = β (v 0) (v 1) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ v

/-- The wedge product `M × M → ∧²M`, as a bilinear map. -/
def wedgeBilin : M →ₗ[R] M →ₗ[R] ⋀[R]^2 M :=
  LinearMap.mk₂ R (fun x y => exteriorPower.ιMulti R 2 ![x, y])
    (fun x x' y => by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_add ![x, y] 0 x x'
      have e0 : Function.update ![x, y] 0 (x + x') = ![x + x', y] := by
        funext i; fin_cases i <;> simp
      have e1 : Function.update ![x, y] 0 x = ![x, y] := by funext i; fin_cases i <;> simp
      have e2 : Function.update ![x, y] 0 x' = ![x', y] := by funext i; fin_cases i <;> simp
      rw [e0, e1, e2] at h; exact h)
    (fun c x y => by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_smul ![x, y] 0 c x
      have e0 : Function.update ![x, y] 0 (c • x) = ![c • x, y] := by
        funext i; fin_cases i <;> simp
      have e1 : Function.update ![x, y] 0 x = ![x, y] := by funext i; fin_cases i <;> simp
      rw [e0, e1] at h; exact h)
    (fun x y y' => by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_add ![x, y] 1 y y'
      have e0 : Function.update ![x, y] 1 (y + y') = ![x, y + y'] := by
        funext i; fin_cases i <;> simp
      have e1 : Function.update ![x, y] 1 y = ![x, y] := by funext i; fin_cases i <;> simp
      have e2 : Function.update ![x, y] 1 y' = ![x, y'] := by funext i; fin_cases i <;> simp
      rw [e0, e1, e2] at h; exact h)
    (fun c x y => by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_smul ![x, y] 1 c y
      have e0 : Function.update ![x, y] 1 (c • y) = ![x, c • y] := by
        funext i; fin_cases i <;> simp
      have e1 : Function.update ![x, y] 1 y = ![x, y] := by funext i; fin_cases i <;> simp
      rw [e0, e1] at h; exact h)

/-- `wedgeBilin x y` is `exteriorPower.ιMulti R 2 ![x, y]`. -/
theorem wedgeBilin_apply (x y : M) : wedgeBilin x y = exteriorPower.ιMulti R 2 ![x, y] := rfl

/-- `x ∧ x = 0`. -/
theorem wedgeBilin_self (x : M) : wedgeBilin (R := R) x x = 0 :=
  (exteriorPower.ιMulti R 2).map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide)

/-- `y ∧ x = -(x ∧ y)`. -/
theorem wedgeBilin_swap (x y : M) : wedgeBilin (R := R) y x = -wedgeBilin x y := by
  have h := (exteriorPower.ιMulti R 2 (M := M)).map_swap ![x, y] (i := 0) (j := 1) (by decide)
  rw [wedgeBilin_apply, wedgeBilin_apply, ← h]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The wedge of a `Fin 2`-indexed family `v` is `v 0 ∧ v 1`. -/
theorem ιMulti_eq_wedgeBilin (v : Fin 2 → M) :
    exteriorPower.ιMulti R 2 v = wedgeBilin (v 0) (v 1) := by
  rw [wedgeBilin_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- `exteriorTwoLift β hβ` sends `x ∧ y` to `β x y`. -/
theorem exteriorTwoLift_wedgeBilin (β : M →ₗ[R] M →ₗ[R] N) (hβ : ∀ x, β x x = 0) (x y : M) :
    exteriorTwoLift β hβ (wedgeBilin x y) = β x y := by
  rw [wedgeBilin_apply, exteriorTwoLift_ιMulti]
  rfl

/-- Two linear maps out of `∧²M` agreeing on all `x ∧ y` agree. -/
theorem exteriorTwo_ext {f g : ⋀[R]^2 M →ₗ[R] N}
    (h : ∀ x y : M, f (wedgeBilin x y) = g (wedgeBilin x y)) : f = g := by
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply]
  rw [ιMulti_eq_wedgeBilin]
  exact h _ _

end ExteriorTwo

/-! ### The antisymmetrisation `∧²_B(J/J²) → Ker(J ⊗ J → J²)` -/

section WedgeAntisymm

variable {P : Type u} {B : Type v} [CommRing P] [CommRing B] {φ : P →+* B}
  [Fact (Function.Surjective φ)]

/-- For fixed `a`, the map `J/J² → Ker(J ⊗ J → J²)`, `b̄ ↦ a ⊗ b - b ⊗ a`. -/
def antisymmLeft (a : RingHom.ker φ) : (RingHom.ker φ).Cotangent →ₗ[B] mulKernel φ :=
  cotangentLift
    { toFun := fun b => antisymm a b
      map_zero' := antisymm_zero_right a
      map_add' := antisymm_add_right a }
    fun r b => by
      change antisymm a (r • b) = φ r • antisymm a b
      rw [antisymm_smul_right, algebraMap_smul_mulKernel]

/-- `antisymmLeft a` sends the class of `b` to `a ⊗ b - b ⊗ a`. -/
@[simp]
theorem antisymmLeft_apply (a b : RingHom.ker φ) :
    antisymmLeft a ((RingHom.ker φ).toCotangent b) = antisymm a b :=
  cotangentLift_toCotangent _ _ b

/-- The bilinear map `J/J² × J/J² → Ker(J ⊗ J → J²)`, `(ā, b̄) ↦ a ⊗ b - b ⊗ a`. -/
def antisymmBilin :
    (RingHom.ker φ).Cotangent →ₗ[B] (RingHom.ker φ).Cotangent →ₗ[B] mulKernel φ :=
  cotangentLift
    { toFun := fun a => antisymmLeft a
      map_zero' := cotangent_linearMap_ext fun b => by
        rw [antisymmLeft_apply, antisymm_zero_left, LinearMap.zero_apply]
      map_add' := fun a a' => cotangent_linearMap_ext fun b => by
        rw [LinearMap.add_apply, antisymmLeft_apply, antisymmLeft_apply, antisymmLeft_apply,
          antisymm_add_left] }
    fun r a => cotangent_linearMap_ext fun b => by
      change antisymmLeft (r • a) _ = (φ r • antisymmLeft a) _
      rw [LinearMap.smul_apply, antisymmLeft_apply, antisymmLeft_apply, antisymm_smul_left,
        algebraMap_smul_mulKernel]

/-- `antisymmBilin` sends the classes of `a` and `b` to `a ⊗ b - b ⊗ a`. -/
@[simp]
theorem antisymmBilin_apply (a b : RingHom.ker φ) :
    antisymmBilin ((RingHom.ker φ).toCotangent a) ((RingHom.ker φ).toCotangent b) =
      antisymm a b := by
  rw [antisymmBilin, cotangentLift_toCotangent]
  exact antisymmLeft_apply a b

/-- `antisymmBilin` is alternating. -/
theorem antisymmBilin_self (c : (RingHom.ker φ).Cotangent) : antisymmBilin c c = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ c
  rw [antisymmBilin_apply]
  exact antisymm_self a

/-- **The antisymmetrisation `∧²_B(J/J²) → Ker(J ⊗_P J → J²)`**, `ā ∧ b̄ ↦ a ⊗ b - b ⊗ a`: the
first map of the exact sequence of Stacks 09D6. -/
def wedgeAntisymm : ⋀[B]^2 (RingHom.ker φ).Cotangent →ₗ[B] mulKernel φ :=
  exteriorTwoLift antisymmBilin antisymmBilin_self

/-- `wedgeAntisymm` sends `ā ∧ b̄` to `a ⊗ b - b ⊗ a`. -/
theorem wedgeAntisymm_wedge (a b : RingHom.ker φ) :
    wedgeAntisymm (wedgeBilin ((RingHom.ker φ).toCotangent a) ((RingHom.ker φ).toCotangent b)) =
      antisymm a b := by
  rw [wedgeAntisymm, exteriorTwoLift_wedgeBilin, antisymmBilin_apply]

end WedgeAntisymm

end Stacks.Cotangent.TorTwo

end
