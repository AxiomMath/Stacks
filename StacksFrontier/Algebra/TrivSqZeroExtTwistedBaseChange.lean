module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SqZeroExt

/-!
# Base change along a twisted structure of `k[V]`

Let `k` be a commutative ring, `V` a `k`-module and `z : k →+* k[V]` a section of the projection
`k[V] = k ⊕ V ⟶ k` (a ring map `c ↦ (c, D c)` with `D` a derivation). Read `k[V]` as a
`k`-algebra through `z`. For any `k`-algebra `R`, the kernel of `R ⊗_k k[V] ⟶ R` is
`R ⊗_k V`, embedded by `x ⊗ v ↦ x ⊗ (0, v)`
(`Stacks.SqZeroTwist.exact_lTensor_inrTwist` and
`Stacks.SqZeroTwist.injective_lTensor_inrTwist`). In the proof of Stacks 0DLL, `z` is the
second component of a lift over `k[V]` of a point of the fibre over `Spec k`, and `R` the ring of
an affine étale chart of `X₀`: this computes the ideal of `X₀` in
`X_V = X₀ ×_{Spec k, z} Spec k[V]`.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

open TensorProduct

universe u

namespace Stacks.SqZeroTwist

attribute [local instance] PresheafOfModules.moduleMulOpposite
  PresheafOfModules.isCentralScalar_of_commRing

variable {k : Type u} [CommRing k] {V : Type u} [AddCommGroup V] [Module k V]
  (z : k →+* TrivSqZeroExt k V) (hz : ∀ c, (z c).fst = c)

/-- `k[V]` as a `k`-algebra through the twisted structure `z`: a type synonym of
`TrivSqZeroExt k V`, whose own `k`-module structure is the untwisted one. -/
def Twisted (_z : k →+* TrivSqZeroExt k V) : Type u := TrivSqZeroExt k V

/-- The commutative ring structure of `TrivSqZeroExt k V` on `Twisted z`. -/
instance (z : k →+* TrivSqZeroExt k V) : CommRing (Twisted z) :=
  inferInstanceAs (CommRing (TrivSqZeroExt k V))

/-- The `k`-algebra structure on `Twisted z` given by `z`. -/
instance (z : k →+* TrivSqZeroExt k V) : Algebra k (Twisted z) := z.toAlgebra

/-- An element of `k[V]` as an element of the twisted algebra. -/
def toTwisted : TrivSqZeroExt k V →+* Twisted z := RingHom.id _

/-- An element of the twisted algebra as an element of `k[V]`. -/
def fromTwisted : Twisted z →+* TrivSqZeroExt k V := RingHom.id _

/-- `fromTwisted z` is a left inverse of `toTwisted z`. -/
@[simp] theorem fromTwisted_toTwisted (t : TrivSqZeroExt k V) :
    fromTwisted z (toTwisted z t) = t := rfl
/-- `toTwisted z` is a left inverse of `fromTwisted z`. -/
@[simp] theorem toTwisted_fromTwisted (t : Twisted z) : toTwisted z (fromTwisted z t) = t := rfl

/-- `fromTwisted z` is injective. -/
theorem fromTwisted_injective : Function.Injective (fromTwisted z) := fun _ _ h => h

/-- Scalar multiplication by `c : k` on `Twisted z` is multiplication by `z c` in `k[V]`. -/
theorem fromTwisted_smul (c : k) (t : Twisted z) :
    fromTwisted z (c • t) = z c * fromTwisted z t := rfl

include hz in
/-- The inclusion `V ⟶ k[V]`, `v ↦ (0, v)`, is `k`-linear for the twisted structure. -/
def inrTwist : V →ₗ[k] Twisted z where
  toFun v := toTwisted z (TrivSqZeroExt.inr v)
  map_add' v w := by rw [TrivSqZeroExt.inr_add, map_add]
  map_smul' c v := by
    apply fromTwisted_injective z
    rw [fromTwisted_smul, fromTwisted_toTwisted, RingHom.id_apply, fromTwisted_toTwisted]
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [TrivSqZeroExt.snd_mul, hz]

/-- `inrTwist z hz v` is the element `(0, v)` of `k[V]`. -/
theorem fromTwisted_inrTwist (v : V) : fromTwisted z (inrTwist z hz v) = TrivSqZeroExt.inr v := rfl

include hz in
/-- The projection `k[V] ⟶ k`, `k`-linear for the twisted structure. -/
def fstTwist : Twisted z →ₗ[k] k where
  toFun t := TrivSqZeroExt.fst (fromTwisted z t)
  map_add' _ _ := by rw [map_add, TrivSqZeroExt.fst_add]
  map_smul' c t := by
    rw [fromTwisted_smul, TrivSqZeroExt.fst_mul, hz]
    rfl

include hz in
/-- **`k[V] = k ⊕ V` for the twisted structure**: `(c, v) ↦ z(c) + (0, v)`. -/
def prodEquivTwist : (k × V) ≃ₗ[k] Twisted z where
  toFun p := toTwisted z (z p.1 + TrivSqZeroExt.inr p.2)
  invFun t := (TrivSqZeroExt.fst (fromTwisted z t),
    TrivSqZeroExt.snd (fromTwisted z t) - (z (TrivSqZeroExt.fst (fromTwisted z t))).snd)
  map_add' p q := by
    apply fromTwisted_injective z
    simp only [fromTwisted_toTwisted, map_add, Prod.fst_add, Prod.snd_add, TrivSqZeroExt.inr_add]
    abel
  map_smul' c p := by
    apply fromTwisted_injective z
    rw [RingHom.id_apply, fromTwisted_smul, fromTwisted_toTwisted, fromTwisted_toTwisted,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul, mul_add]
    congr 1
    exact congrArg (fromTwisted z) ((inrTwist z hz).map_smul c p.2)
  left_inv p := by
    refine Prod.ext ?_ ?_ <;> simp [hz]
  right_inv t := by
    apply fromTwisted_injective z
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [hz]

/-- `prodEquivTwist z hz` sends `(0, v)` to `inrTwist z hz v`. -/
theorem prodEquivTwist_inr (v : V) :
    prodEquivTwist z hz (0, v) = inrTwist z hz v := by
  apply fromTwisted_injective z
  change z 0 + TrivSqZeroExt.inr v = TrivSqZeroExt.inr v
  rw [map_zero, zero_add]

/-- The first component of `prodEquivTwist z hz p` is `p.1`. -/
theorem fstTwist_prodEquivTwist (p : k × V) :
    fstTwist z hz (prodEquivTwist z hz p) = p.1 := by
  change TrivSqZeroExt.fst (z p.1 + TrivSqZeroExt.inr p.2) = p.1
  simp [hz]

/-- `inrTwist z hz` factors as `V ⟶ k × V ≃ k[V]` through `prodEquivTwist z hz`. -/
private theorem inrTwist_eq_comp :
    inrTwist z hz = (prodEquivTwist z hz).toLinearMap ∘ₗ LinearMap.inr k k V :=
  LinearMap.ext fun v => (prodEquivTwist_inr z hz v).symm

variable (R : Type u) [CommRing R] [Algebra k R]

/-- **The ideal of `R` in `R ⊗_k k[V]` is `R ⊗_k V`**: the sequence
`R ⊗ V ⟶ R ⊗ k[V] ⟶ R ⊗ k` is exact, `k[V]` being read through `z`. -/
theorem exact_lTensor_inrTwist :
    Function.Exact (LinearMap.lTensor R (inrTwist z hz)) (LinearMap.lTensor R (fstTwist z hz)) := by
  have hfst : fstTwist z hz = LinearMap.fst k k V ∘ₗ (prodEquivTwist z hz).symm.toLinearMap :=
    LinearMap.ext fun _ => rfl
  rw [inrTwist_eq_comp, hfst, LinearMap.lTensor_comp, LinearMap.lTensor_comp]
  exact (LinearEquiv.conj_exact_iff_exact _ _ ((prodEquivTwist z hz).lTensor R)).2
    (lTensor_exact R Function.Exact.inr_fst LinearMap.fst_surjective)

/-- The embedding `R ⊗_k V ⟶ R ⊗_k k[V]` is injective: `V ⟶ k[V]` is split. -/
theorem injective_lTensor_inrTwist :
    Function.Injective (LinearMap.lTensor R (inrTwist z hz)) := by
  rw [inrTwist_eq_comp, LinearMap.lTensor_comp, LinearMap.coe_comp]
  refine ((prodEquivTwist z hz).lTensor R).injective.comp ?_
  refine Function.LeftInverse.injective (g := LinearMap.lTensor R (LinearMap.snd k k V)) fun x => ?_
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, LinearMap.snd_comp_inr,
    LinearMap.lTensor_id, LinearMap.id_apply]

end Stacks.SqZeroTwist

end
