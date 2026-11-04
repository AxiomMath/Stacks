module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# The canonical element of a perfect pairing with a finite projective module

Let `R` be a commutative ring, `M` a finitely generated projective `R`-module and
`p : M' → Hom_R(M, R)` a bijective linear map, read as a perfect pairing `M' × M → R`. Then
`M ⊗ M'` contains a unique element `c` whose contraction `M → M`, `g ↦ ∑ p(b, g) a` for
`c = ∑ a ⊗ b`, is the identity; the other contraction `M' → M'`, `f ↦ ∑ p(f, a) b`, is then the
identity too. These are the two zigzag identities exhibiting `M'` as a dual of `M` with
evaluation `p`, which is what a coevaluation of a perfect pairing of sheaves has to satisfy on
each fibre.

The element is `c = ∑ₗ eₗ ⊗ βₗ`, where `(eₗ, φₗ)` is a dual basis of `M` (it exists because `M` is
a direct summand of a finite free module) and `βₗ = p⁻¹(φₗ)`. Uniqueness comes from the
reconstruction formula `d = ∑ₗ (contraction of d)(eₗ) ⊗ βₗ`, valid for every `d ∈ M ⊗ M'`.

## Main definitions

* `Stacks.PerfectPairing.contract`: the contraction `M ⊗ M' → End(M)`.
* `Stacks.PerfectPairing.contractDual`: the contraction `M ⊗ M' → End(M')`.

## Main results

* `Stacks.PerfectPairing.exists_dualBasis`: a finite projective module has a finite dual basis.
* `Stacks.PerfectPairing.exists_canonical`: the canonical element exists, is the unique solution
  of the first zigzag identity, and satisfies the second.
-/

@[expose] public section

namespace Stacks.PerfectPairing

open TensorProduct

variable {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']

/-- A finitely generated projective module has a finite dual basis: elements `e l` and linear
forms `φ l` with `m = ∑ l, φ l m • e l` for every `m`. -/
theorem exists_dualBasis [Module.Finite R M] [Module.Projective R M] :
    ∃ (n : ℕ) (e : Fin n → M) (φ : Fin n → (M →ₗ[R] R)), ∀ m, ∑ l, φ l m • e l = m := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  refine ⟨n, fun l => π (Pi.single l 1), fun l => (LinearMap.proj l).comp s, fun m => ?_⟩
  have h : s m = ∑ l, s m l • (Pi.single l (1 : R) : Fin n → R) := by
    ext j
    simp [Pi.single_apply]
  calc ∑ l, ((LinearMap.proj l).comp s) m • π (Pi.single l 1)
      = π (∑ l, s m l • (Pi.single l (1 : R) : Fin n → R)) := by simp [map_sum]
    _ = π (s m) := by rw [← h]
    _ = m := LinearMap.congr_fun hs m

variable (p : M' →ₗ[R] M →ₗ[R] R)

/-- The contraction `M ⊗ M' → End(M)`, `a ⊗ b ↦ (g ↦ p b g • a)`. -/
def contract : M ⊗[R] M' →ₗ[R] M →ₗ[R] M :=
  TensorProduct.lift (LinearMap.mk₂ R (fun a b => (p b).smulRight a)
    (fun a a' b => by ext; simp) (fun r a b => by ext; exact smul_comm _ _ _)
    (fun a b b' => by ext; simp [add_smul]) (fun r a b => by ext; simp [mul_smul]))

/-- The contraction of `a ⊗ b` sends `g` to `p b g • a`. -/
@[simp]
theorem contract_tmul (a : M) (b : M') (g : M) : contract p (a ⊗ₜ b) g = p b g • a := rfl

/-- The contraction `M ⊗ M' → End(M')`, `a ⊗ b ↦ (f ↦ p f a • b)`. -/
def contractDual : M ⊗[R] M' →ₗ[R] M' →ₗ[R] M' :=
  TensorProduct.lift (LinearMap.mk₂ R (fun a b => (p.flip a).smulRight b)
    (fun a a' b => by ext; simp [add_smul]) (fun r a b => by ext; simp [mul_smul])
    (fun a b b' => by ext; simp) (fun r a b => by ext; exact smul_comm _ _ _))

/-- The dual contraction of `a ⊗ b` sends `f` to `p f a • b`. -/
@[simp]
theorem contractDual_tmul (a : M) (b : M') (f : M') : contractDual p (a ⊗ₜ b) f = p f a • b :=
  rfl

variable {p}

section DualBasis

variable (hp : Function.Bijective p) {n : ℕ} {e : Fin n → M} {φ : Fin n → (M →ₗ[R] R)}
  (he : ∀ m, ∑ l, φ l m • e l = m) {β : Fin n → M'} (hβ : ∀ l, p (β l) = φ l)

include hp he hβ in
/-- Every element of `M'` is recovered from its pairings with the dual basis. -/
theorem sum_pairing_smul (f : M') : ∑ l, p f (e l) • β l = f := by
  apply hp.1
  ext g
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    hβ, smul_eq_mul]
  conv_rhs => rw [← he g]
  simp [map_sum, mul_comm]

include hp he hβ in
/-- **The reconstruction formula**: every `d ∈ M ⊗ M'` is `∑ l, (contract p d (e l)) ⊗ β l`. -/
theorem eq_sum_contract (d : M ⊗[R] M') : d = ∑ l, contract p d (e l) ⊗ₜ β l := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [contract_tmul, smul_tmul, ← tmul_sum]
    rw [sum_pairing_smul hp he hβ]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp [add_tmul, Finset.sum_add_distrib]

end DualBasis

/-- **The canonical element of a perfect pairing.** For `M` finitely generated projective and
`p : M' → Hom(M, R)` bijective, there is `c ∈ M ⊗ M'` whose contraction on `M` is the identity,
it is the only element with this property, and its contraction on `M'` is the identity too. -/
theorem exists_canonical [Module.Finite R M] [Module.Projective R M]
    (hp : Function.Bijective p) :
    ∃ c : M ⊗[R] M', (∀ g, contract p c g = g) ∧
      (∀ d : M ⊗[R] M', (∀ g, contract p d g = g) → d = c) ∧
      (∀ f, contractDual p c f = f) := by
  obtain ⟨n, e, φ, he⟩ := exists_dualBasis (R := R) (M := M)
  choose β hβ using fun l => hp.2 (φ l)
  refine ⟨∑ l, e l ⊗ₜ β l, fun g => ?_, fun d hd => ?_, fun f => ?_⟩
  · simpa only [map_sum, LinearMap.sum_apply, contract_tmul, hβ] using he g
  · rw [eq_sum_contract hp he hβ d]
    simp only [hd]
  · simpa only [map_sum, LinearMap.sum_apply, contractDual_tmul] using
      sum_pairing_smul hp he hβ f

end Stacks.PerfectPairing
