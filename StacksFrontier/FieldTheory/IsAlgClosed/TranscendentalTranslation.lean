module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Translating a transcendental element by an automorphism of an algebraically closed field

Let `K/k` be an extension with `K` algebraically closed and let `μ ∈ K` be transcendental over
`k`. Then some `k`-automorphism of `K` sends `μ` to `μ + 1`. Choose a transcendence basis `t` of
`K/k` containing `μ`; translating the variable `μ` by `1` is an automorphism of the polynomial
ring `k[t] ≅ k[t]`, and `K` is an algebraic closure of `k[t]`, so the automorphism extends.

## Main results

* `IsAlgClosed.exists_algEquiv_apply_eq_add_one`: the automorphism.
-/

@[expose] public section

open MvPolynomial

namespace IsAlgClosed

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Translation of one variable by `1`, as an automorphism of a polynomial ring. -/
noncomputable def mvPolynomialTranslate {σ : Type*} [DecidableEq σ] (i₀ : σ) :
    MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k :=
  AlgEquiv.ofAlgHom (aeval fun i => X i + if i = i₀ then 1 else 0)
    (aeval fun i => X i - if i = i₀ then 1 else 0)
    (by ext i; by_cases h : i = i₀ <;> simp [h])
    (by ext i; by_cases h : i = i₀ <;> simp [h])

/-- **A transcendental element of an algebraically closed field can be translated by `1`.** If
`K` is algebraically closed and `μ ∈ K` is transcendental over `k`, some `k`-automorphism of `K`
sends `μ` to `μ + 1`. -/
theorem exists_algEquiv_apply_eq_add_one [IsAlgClosed K] {μ : K} (hμ : Transcendental k μ) :
    ∃ σ : K ≃ₐ[k] K, σ μ = μ + 1 := by
  classical
  have hs : AlgebraicIndepOn k id ({μ} : Set K) :=
    (algebraicIndependent_singleton_iff (⟨μ, rfl⟩ : ({μ} : Set K))).mpr hμ
  obtain ⟨t, hst, ht⟩ := exists_isTranscendenceBasis_superset hs
  let hx := ht.1
  let A := Algebra.adjoin k (Set.range ((↑) : t → K))
  let μ₀ : t := ⟨μ, hst rfl⟩
  let τ : A ≃ₐ[k] A := hx.aevalEquiv.symm.trans ((mvPolynomialTranslate μ₀).trans hx.aevalEquiv)
  have : Algebra.IsAlgebraic A K := ht.isAlgebraic
  have : IsAlgClosure A K := ⟨inferInstance, inferInstance⟩
  let σ := IsAlgClosure.equivOfEquiv K K τ.toRingEquiv
  have hσ : ∀ a : A, σ (algebraMap A K a) = algebraMap A K (τ a) := fun a =>
    IsAlgClosure.equivOfEquiv_algebraMap K K τ.toRingEquiv a
  have hk : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := fun c => by
    rw [IsScalarTower.algebraMap_apply k A K, hσ]
    exact congrArg (algebraMap A K) (τ.commutes c)
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) hk, ?_⟩
  have hμA : μ = algebraMap A K (hx.aevalEquiv (X μ₀)) := by
    rw [AlgebraicIndependent.algebraMap_aevalEquiv, aeval_X]
  rw [AlgEquiv.ofRingEquiv_apply, hμA, hσ]
  simp only [τ, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, mvPolynomialTranslate,
    AlgEquiv.ofAlgHom_apply, aeval_X, map_add, map_one, ite_true]

end IsAlgClosed

end
