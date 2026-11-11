module

public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksFrontier.FieldTheory.Galois.SeparableClosureGaloisGroup

/-!
# Automorphisms over the relative perfect closure

Let `K/k` be an algebraic extension of fields and `k' = perfectClosure k K` the relative perfect
closure of `k` in `K`, the largest purely inseparable subextension. Every `k`-automorphism of `K`
fixes `k'` pointwise: if `x ^ (q ^ n) ∈ k` then `σ x ^ (q ^ n) = x ^ (q ^ n)`, and the iterated
Frobenius of a field is injective. So restricting scalars from `k'` to `k` is a bijection
`Aut(K/k') ≃ Aut(K/k)`, and it is a homeomorphism for the two Krull topologies: both directions
are continuous, by the stabilizer criterion `continuous_of_stabilizer_mem_nhds_one`.

For `K` an algebraic closure of `k`, `K` is separable over `k'` (an algebraic extension of the
perfect field `k'`), so `Aut(K/k')` is the Galois group of the Galois extension `K/k'`. This is how
statements about the Galois action on the geometric fibre `X_{k̄}` over an arbitrary field `k`
reduce to the separable case over `k'`: both the group and the geometric fibre are unchanged.

## Main definitions

* `perfectClosureAlgEquivContinuousMulEquiv`: `Aut(K/k') ≃ₜ* Aut(K/k)`, restriction of scalars.

## Main results

* `AlgEquiv.apply_eq_self_of_mem_perfectClosure`: a `k`-automorphism fixes the perfect closure.
* `isSeparable_of_isAlgClosure_perfectClosure`: `K/k'` is separable for `K` an algebraic closure.
-/

@[expose] public noncomputable section

open IntermediateField Topology

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- **A `k`-automorphism of `K` fixes the relative perfect closure of `k` in `K`.** -/
theorem AlgEquiv.apply_eq_self_of_mem_perfectClosure (σ : K ≃ₐ[k] K) {x : K}
    (hx : x ∈ _root_.perfectClosure k K) : σ x = x := by
  obtain ⟨q, hq⟩ := ExpChar.exists k
  have : ExpChar K q := expChar_of_injective_algebraMap (algebraMap k K).injective q
  obtain ⟨n, a, ha⟩ := (mem_perfectClosure_iff_pow_mem q).mp hx
  apply iterateFrobenius_inj K q n
  rw [iterateFrobenius_def, iterateFrobenius_def, ← map_pow, ← ha, AlgEquiv.commutes]

/-- **Every `k`-automorphism of `K` is `k'`-linear**, `k' = perfectClosure k K`: the inverse of
restriction of scalars `Aut(K/k') → Aut(K/k)`. -/
def AlgEquiv.toPerfectClosureAlgEquiv (σ : K ≃ₐ[k] K) : K ≃ₐ[_root_.perfectClosure k K] K :=
  { σ.toRingEquiv with
    commutes' := fun x ↦ σ.apply_eq_self_of_mem_perfectClosure k K x.2 }

@[simp]
theorem AlgEquiv.toPerfectClosureAlgEquiv_apply (σ : K ≃ₐ[k] K) (x : K) :
    σ.toPerfectClosureAlgEquiv k K x = σ x :=
  rfl

/-- **`Aut(K/k') ≃* Aut(K/k)`** for `k' = perfectClosure k K`: restriction of scalars. -/
def perfectClosureAlgEquivMulEquiv : (K ≃ₐ[perfectClosure k K] K) ≃* (K ≃ₐ[k] K) where
  toFun σ := σ.restrictScalars k
  invFun σ := σ.toPerfectClosureAlgEquiv k K
  left_inv σ := by ext; rfl
  right_inv σ := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[simp]
theorem perfectClosureAlgEquivMulEquiv_apply_apply (σ : K ≃ₐ[perfectClosure k K] K) (x : K) :
    perfectClosureAlgEquivMulEquiv k K σ x = σ x :=
  rfl

@[simp]
theorem perfectClosureAlgEquivMulEquiv_symm_apply_apply (σ : K ≃ₐ[k] K) (x : K) :
    (perfectClosureAlgEquivMulEquiv k K).symm σ x = σ x :=
  rfl

variable [Algebra.IsAlgebraic k K]

/-- **`Aut(K/k') ≃ₜ* Aut(K/k)`** for an algebraic extension `K/k` and `k' = perfectClosure k K`:
restriction of scalars, a homeomorphism for the Krull topologies. Both directions are
continuous because the stabilizer of every element of `K` is open in both groups. -/
def perfectClosureAlgEquivContinuousMulEquiv :
    (K ≃ₐ[perfectClosure k K] K) ≃ₜ* (K ≃ₐ[k] K) :=
  { perfectClosureAlgEquivMulEquiv k K with
    continuous_toFun :=
      continuous_of_stabilizer_mem_nhds_one (perfectClosureAlgEquivMulEquiv k K).toMonoidHom
        fun x ↦ stabilizer_mem_nhds_one (k := perfectClosure k K) x
    continuous_invFun :=
      continuous_of_stabilizer_mem_nhds_one (perfectClosureAlgEquivMulEquiv k K).symm.toMonoidHom
        fun x ↦ stabilizer_mem_nhds_one (k := k) x }

@[simp]
theorem perfectClosureAlgEquivContinuousMulEquiv_apply_apply
    (σ : K ≃ₐ[perfectClosure k K] K) (x : K) :
    perfectClosureAlgEquivContinuousMulEquiv k K σ x = σ x :=
  rfl

@[simp]
theorem perfectClosureAlgEquivContinuousMulEquiv_symm_apply_apply (σ : K ≃ₐ[k] K) (x : K) :
    (perfectClosureAlgEquivContinuousMulEquiv k K).symm σ x = σ x :=
  rfl

/-- **An algebraic closure of `k` is separable over the relative perfect closure of `k` in it**,
the latter being a perfect field. -/
theorem isSeparable_of_isAlgClosure_perfectClosure [IsAlgClosed K] :
    Algebra.IsSeparable (perfectClosure k K) K :=
  inferInstance

/-- An algebraic closure of `k` is an algebraic closure of the relative perfect closure. -/
theorem isAlgClosure_perfectClosure [IsAlgClosure k K] : IsAlgClosure (perfectClosure k K) K :=
  ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩

end
