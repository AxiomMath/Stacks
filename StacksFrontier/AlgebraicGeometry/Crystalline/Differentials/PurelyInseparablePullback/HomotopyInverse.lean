module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PurelyInseparablePullback.PrimeRingTheta
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PurelyInseparablePullback.DifferentialComponents

/-!
# Pulling back along a purely inseparable map: the remainder of `θ` and Tag 07N1

For the extension `B → B' = B[z]⟨ξ⟩/(ξ - (z^p - λ))`, this file computes the values of `∂_z` and
`d₁` on the basis `z^i ξ^[n]` from the divided power identity `d(ξ^[n+1]) = ξ^[n] d ξ`, shows
that the remainder `ε'(f) = (θ ⊗ 1)(d₁ f) - d₁(θ f)` lies in `Ω` (assumption (07Q6) of
Lemma 07Q7), and assembles the conclusion of Tag 07N1 for the uncompleted extension.

## Main definitions

* `Crystalline.PthRootExtension.IsDpowDifferential` — the statement `d(ξ^[n+1]) = ξ^[n] d ξ`.
* `Crystalline.PthRootExtension.DOneValues` — the two values of `d₁` on the basis.
* `Crystalline.PthRootExtension.epsilonPrimeMap` — the remainder `ε'` as a `B`-linear map.

## Main results

* `Crystalline.PthRootExtension.xiElt_one_mul_xiElt` — `ξ ξ^[n] = (n + 1) ξ^[n+1]`.
* `Crystalline.PthRootExtension.partialZValues_of_isDpowDifferential` and
  `Crystalline.PthRootExtension.dOneValues_of_isDpowDifferential` — the two tables of values.
* `Crystalline.PthRootExtension.dOne_remainder_mem` — assumption (07Q6): `ε'(f)` lies in `Ω`.
* `Crystalline.exists_homotopyInverse_pthRootExtension` — the conclusion of Tag 07N1 for the
  uncompleted extension.

## References

* [Stacks Project, Tag 07Q7](https://stacks.math.columbia.edu/tag/07Q7)
* [Stacks Project, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
-/

@[expose] public section

noncomputable section

open DividedPowers Stacks.DeRham.DifferentialDescent

open scoped TensorProduct

universe u w

namespace Crystalline

/-! ### Scalar and module identities used in the induction -/

section Auxiliary

/-- Cancelling an inverse: `x (P x⁻¹) = P` for an element `x` with inverse `u`. -/
private theorem mul_mul_inverse_cancel {R : Type*} [CommRing R] (P x u : R) (hu : u * x = 1) :
    x * (P * u) = P := by
  linear_combination P * hu

/-- The module identity behind the inductive step: if `c (c₀ + P) = 1` and
`c₀ • W = P • U - Q • V`, then `c • (-(P • U) - (Q • (-V) + P • W)) = -W`. -/
private theorem smul_bracket_eq_neg {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (c c₀ P Q : R) (U V W : M) (hW : c₀ • W = P • U - Q • V) (hc : c * (c₀ + P) = 1) :
    c • (-(P • U) - (Q • (-V) + P • W)) = -W := by
  have h1 : -(P • U) - (Q • (-V) + P • W) = (-c₀ - P) • W := by
    linear_combination (norm := module) hW
  have h2 : c * (-c₀ - P) = -1 := by linear_combination -hc
  rw [h1, smul_smul, h2, neg_smul, one_smul]

end Auxiliary

section Remainder

/-! ### The remainder of `θ` on one-forms of the purely inseparable extension -/

namespace PthRootExtension

variable {A Omega : Type u} [CommRing A] [AddCommGroup Omega]
variable (B : DividedPowerRing.{u}) (p : ℕ) (lam : (B : Type u))
variable [Algebra A (B : Type u)] [Module (B : Type u) Omega]
variable (pi : Ω[(B : Type u)⁄A] →ₗ[(B : Type u)] Omega)
variable {Omega' : Type u} [AddCommGroup Omega']
variable [Module (primeRing B p lam) Omega']
variable {pi' : Ω[(primeRing B p lam)⁄A] →ₗ[primeRing B p lam] Omega'}
variable {psi : Omega →ₛₗ[algebraMap (B : Type u) (primeRing B p lam)] Omega'}
variable {z : primeRing B p lam}
variable (dec : DzDecomposition pi' psi z)
variable (hpsi : ∀ b : (B : Type u),
  psi (pi (KaehlerDifferential.D A (B : Type u) b)) =
    pi' (KaehlerDifferential.D A (primeRing B p lam)
      (algebraMap (B : Type u) (primeRing B p lam) b)))

/-- The two values of `d₁` on the basis vectors `ξ^[n] z^i` computed in the proof of Tag 07N1
from `ξ = z^p - λ`: the differential of a power of `z` is a multiple of `dz`, so has no
base-change component, while the differential of `ξ^[n+1] z^i` contributes `-(ξ^[n] z^i ⊗ dλ)`
because `ξ = z^p - λ`. -/
public structure DOneValues : Prop where
  /-- `d₁(z^i) = 0`. -/
  pow : ∀ i : ℕ, dec.dOne (xiElt B p lam 0 i) = 0
  /-- `d₁(ξ^[n+1] z^i) = -(ξ^[n] z^i ⊗ dλ)`. -/
  xi : ∀ (n i : ℕ), dec.dOne (xiElt B p lam (n + 1) i) =
    -(xiElt B p lam n i ⊗ₜ[(B : Type u)] SourceDeRham.targetD pi lam)

/-! ### The two tables of values, computed rather than assumed

The proof of Tag 07N1 obtains the values of `∂_z` and `d₁` on the basis `z^i ξ^[n]` from the
single divided power identity `d(ξ^[n]) = ξ^[n-1] d ξ`, together with `ξ = z^p - λ` and
`ξ ξ^[n-1] = n ξ^[n]`.  That derivation is carried out here, so that
`PthRootExtension.PartialZValues` and `PthRootExtension.DOneValues` become theorems about any
`Ω'` whose differential is a divided power differential in the variable `ξ`. -/

section DpowValues

/-- **The divided power derivation property of `ξ`.**  In the source `Ω'` is the module of
divided power differentials of `B' = B[z]⟨ξ⟩/(ξ - (z^p - λ))` over `A` and `ξ` lies in its
divided power ideal, so the differential satisfies `d(ξ^[n+1]) = ξ^[n] d ξ`.  This is the first
display of the proof of Tag 07N1, and the only property of `Ω'` beyond the decomposition
(07Q1) that the computation of `∂_z` and `d₁` on the basis `z^i ξ^[n]` uses. -/
public def IsDpowDifferential : Prop :=
  ∀ n : ℕ, SourceDeRham.targetD pi' (xiElt B p lam (n + 1) 0) =
    xiElt B p lam n 0 • SourceDeRham.targetD pi' (xiElt B p lam 1 0)

variable {B p lam}

/-- `ξ^[n] z^i` is the product of `ξ^[n]` and `z^i`. -/
public theorem xiElt_eq_mul (n i : ℕ) :
    xiElt B p lam n i = xiElt B p lam n 0 * zElt B p lam ^ i := by
  rw [xiElt_zero_right]
  rfl

/-- The image of `λ` in the extension. -/
public theorem of_algebraMap_lam :
    AdjoinRoot.of (primePoly B p lam) (algebraMap (B : Type u) (XiAlg B) lam) =
      algebraMap (B : Type u) (primeRing B p lam) lam := by
  rw [IsScalarTower.algebraMap_apply (B : Type u) (XiAlg B) (primeRing B p lam),
    AdjoinRoot.algebraMap_eq]

/-- The relation `ξ = z^p - λ` of the extension, as an identity between `ξ^[1]` and `z^p`. -/
public theorem xiElt_one_zero_eq :
    xiElt B p lam 1 0 =
      zElt B p lam ^ p - algebraMap (B : Type u) (primeRing B p lam) lam := by
  rw [xiElt_one_zero, xi_eq, of_algebraMap_lam]

/-- **`ξ ξ^[n] = (n + 1) ξ^[n+1]`**, the divided power identity used in the proof of Tag 07N1
to turn `p z^{i + p - 1} ξ^[n]` into `p n z^{i - 1} ξ^[n]`. -/
public theorem xiElt_one_mul_xiElt (n : ℕ) :
    xiElt B p lam 1 0 * xiElt B p lam n 0 =
      ((n + 1 : ℕ) : primeRing B p lam) * xiElt B p lam (n + 1) 0 := by
  have hmem : xi B ∈ (xiRing B).ideal := variable_mem_polynomialIdeal B ()
  have h0 := (xiRing B).dividedPowers.mul_dpow (m := 1) (n := n) hmem
  rw [dpow_xi, dpow_xi, dpow_xi] at h0
  have hchoose : Nat.choose (1 + n) 1 = n + 1 := by
    rw [Nat.choose_one_right, Nat.add_comm]
  rw [hchoose, Nat.add_comm 1 n] at h0
  have h : xiMonomial B 1 * xiMonomial B n =
      ((n + 1 : ℕ) : XiAlg B) * xiMonomial B (n + 1) := h0
  have h' := congrArg (AdjoinRoot.of (primePoly B p lam)) h
  simp only [map_mul, map_natCast] at h'
  rw [xiElt_zero_right, xiElt_zero_right, xiElt_zero_right]
  exact h'

/-- `c • (1 ⊗ ω) = c ⊗ ω` for the `B'`-module structure on `B' ⊗_B Ω`. -/
private theorem smul_one_tmul (c : primeRing B p lam) (w : Omega) :
    (c • ((1 : primeRing B p lam) ⊗ₜ[(B : Type u)] w) :
      primeRing B p lam ⊗[(B : Type u)] Omega) = c ⊗ₜ[(B : Type u)] w := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The coefficient of `dz` in `d ξ` is `p z^{p-1}`: this is `d ξ = p z^{p-1} dz - dλ`,
read off the relation `ξ = z^p - λ`. -/
public theorem partialZ_xiElt_one_zero (dec : DzDecomposition pi' psi (zElt B p lam))
    (hpsi : ∀ b : (B : Type u),
      psi (pi (KaehlerDifferential.D A (B : Type u) b)) =
        pi' (KaehlerDifferential.D A (primeRing B p lam)
          (algebraMap (B : Type u) (primeRing B p lam) b)))
    (hp : p ≠ 0) :
    dec.partialZ (xiElt B p lam 1 0) =
      ((p : ℕ) : primeRing B p lam) * zElt B p lam ^ (p - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  rw [xiElt_one_zero_eq, dec.partialZ_sub, dec.partialZ_algebraMap hpsi,
    dec.partialZ_pow_succ, sub_zero]
  rfl

/-- The base-change component of `d ξ` is `-(1 ⊗ dλ)`: this is `d ξ = p z^{p-1} dz - dλ`,
read off the relation `ξ = z^p - λ`. -/
public theorem dOne_xiElt_one_zero (dec : DzDecomposition pi' psi (zElt B p lam))
    (hpsi : ∀ b : (B : Type u),
      psi (pi (KaehlerDifferential.D A (B : Type u) b)) =
        pi' (KaehlerDifferential.D A (primeRing B p lam)
          (algebraMap (B : Type u) (primeRing B p lam) b))) :
    dec.dOne (xiElt B p lam 1 0) =
      -((1 : primeRing B p lam) ⊗ₜ[(B : Type u)] SourceDeRham.targetD pi lam) := by
  rw [xiElt_one_zero_eq, dec.dOne_sub, dec.dOne_algebraMap hpsi, dec.dOne_pow, zero_sub]

/-- `∂_z(ξ^[n+1]) = ξ^[n] ∂_z(ξ)`, the divided power derivation property read through the
decomposition. -/
public theorem partialZ_xiElt_succ_zero (dec : DzDecomposition pi' psi (zElt B p lam))
    (hd : IsDpowDifferential B p lam (pi' := pi')) (n : ℕ) :
    dec.partialZ (xiElt B p lam (n + 1) 0) =
      xiElt B p lam n 0 * dec.partialZ (xiElt B p lam 1 0) := by
  change (dec.equiv.symm (SourceDeRham.targetD pi' (xiElt B p lam (n + 1) 0))).2 = _
  rw [hd n, map_smul, Prod.smul_snd, smul_eq_mul]
  rfl

/-- `d₁(ξ^[n+1]) = ξ^[n] d₁(ξ)`, the divided power derivation property read through the
decomposition. -/
public theorem dOne_xiElt_succ_zero (dec : DzDecomposition pi' psi (zElt B p lam))
    (hd : IsDpowDifferential B p lam (pi' := pi')) (n : ℕ) :
    dec.dOne (xiElt B p lam (n + 1) 0) =
      xiElt B p lam n 0 • dec.dOne (xiElt B p lam 1 0) := by
  change (dec.equiv.symm (SourceDeRham.targetD pi' (xiElt B p lam (n + 1) 0))).1 = _
  rw [hd n, map_smul, Prod.smul_fst]
  rfl

/-- **The three values of `∂_z` on the basis, computed.**  Assumption
`PthRootExtension.PartialZValues` is a theorem for any `Ω'` satisfying (07Q1) whose differential
is a divided power differential in `ξ`: the displayed formulas of the proof of Tag 07N1 follow
from `d(ξ^[n]) = ξ^[n-1] dξ`, `ξ = z^p - λ` and `ξ ξ^[n-1] = n ξ^[n]`. -/
public theorem partialZValues_of_isDpowDifferential
    (dec : DzDecomposition pi' psi (zElt B p lam))
    (hpsi : ∀ b : (B : Type u),
      psi (pi (KaehlerDifferential.D A (B : Type u) b)) =
        pi' (KaehlerDifferential.D A (primeRing B p lam)
          (algebraMap (B : Type u) (primeRing B p lam) b)))
    (hp : p ≠ 0) (hd : IsDpowDifferential B p lam (pi' := pi')) :
    PartialZValues B p lam (dec.partialZLinear hpsi) where
  pow i := by
    rw [dec.partialZLinear_apply hpsi, xiElt_zero_left, xiElt_zero_left]
    simp only [Algebra.smul_def, map_natCast]
    cases i with
    | zero => rw [pow_zero, dec.partialZ_one, Nat.cast_zero, zero_mul]
    | succ k => rw [dec.partialZ_pow_succ, Nat.add_sub_cancel]
  xiPow n := by
    rw [dec.partialZLinear_apply hpsi, partialZ_xiElt_succ_zero dec hd,
      partialZ_xiElt_one_zero pi dec hpsi hp, xiElt_eq_mul n (p - 1)]
    simp only [Algebra.smul_def, map_natCast]
    ring
  xiZ n i hi := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, (Nat.succ_pred_eq_of_pos hi).symm⟩
    have hz : zElt B p lam ^ (p - 1) * zElt B p lam = zElt B p lam ^ p := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp)]
    have h2 : zElt B p lam ^ p =
        xiElt B p lam 1 0 + algebraMap (B : Type u) (primeRing B p lam) lam := by
      rw [xiElt_one_zero_eq]; ring
    have h3 := xiElt_one_mul_xiElt (B := B) (p := p) (lam := lam) n
    have h4 : ((j + 1 + p * (n + 1) : ℕ) : primeRing B p lam) =
        ((j + 1 : ℕ) : primeRing B p lam) +
          ((p : ℕ) : primeRing B p lam) * ((n + 1 : ℕ) : primeRing B p lam) := by
      push_cast
      ring
    rw [dec.partialZLinear_apply hpsi, Nat.add_sub_cancel, xiElt_eq_mul (n + 1) (j + 1),
      xiElt_eq_mul (n + 1) j, xiElt_eq_mul n j, dec.partialZ_mul, dec.partialZ_pow_succ,
      partialZ_xiElt_succ_zero dec hd, partialZ_xiElt_one_zero pi dec hpsi hp]
    simp only [Algebra.smul_def, map_mul, map_natCast]
    linear_combination
      (((p : ℕ) : primeRing B p lam) * xiElt B p lam n 0 * zElt B p lam ^ j) * hz +
        (((p : ℕ) : primeRing B p lam) * xiElt B p lam n 0 * zElt B p lam ^ j) * h2 +
        (((p : ℕ) : primeRing B p lam) * zElt B p lam ^ j) * h3 -
        (xiElt B p lam (n + 1) 0 * zElt B p lam ^ j) * h4

/-- **The two values of `d₁` on the basis, computed.**  Assumption
`PthRootExtension.DOneValues` is a theorem for any `Ω'` satisfying (07Q1) whose differential is
a divided power differential in `ξ`. -/
public theorem dOneValues_of_isDpowDifferential
    (dec : DzDecomposition pi' psi (zElt B p lam))
    (hpsi : ∀ b : (B : Type u),
      psi (pi (KaehlerDifferential.D A (B : Type u) b)) =
        pi' (KaehlerDifferential.D A (primeRing B p lam)
          (algebraMap (B : Type u) (primeRing B p lam) b)))
    (hd : IsDpowDifferential B p lam (pi' := pi')) :
    DOneValues B p lam pi dec where
  pow i := by rw [xiElt_zero_left, dec.dOne_pow]
  xi n i := by
    rw [xiElt_eq_mul (n + 1) i, dec.dOne_mul, dec.dOne_pow, smul_zero, zero_add,
      dOne_xiElt_succ_zero dec hd, dOne_xiElt_one_zero pi dec hpsi, smul_neg, smul_neg,
      smul_smul, smul_one_tmul, xiElt_eq_mul n i,
      mul_comm (xiElt B p lam n 0) (zElt B p lam ^ i)]

end DpowValues

/-- `θ(z^i ξ^[n-1])`, with the convention that it is `0` for `n = 0`: the lower term of the
recursion `(i + 1 + pn) θ(z^i ξ^[n]) = p z^{i+1} ξ^[n] - p λ θ(z^i ξ^[n-1])`. -/
public def thetaBasisPred : ℕ → Fin p → primeRing B p lam
  | 0, _ => 0
  | n + 1, i => thetaBasis B p lam n i

/-- The lower term of the recursion is `0` at `n = 0`. -/
public theorem thetaBasisPred_zero (i : Fin p) : thetaBasisPred B p lam 0 i = 0 := rfl

/-- The lower term of the recursion at `n + 1` is `θ(z^i ξ^[n])`. -/
public theorem thetaBasisPred_succ (n : ℕ) (i : Fin p) :
    thetaBasisPred B p lam (n + 1) i = thetaBasis B p lam n i := rfl

variable [Nontrivial (XiAlg B)] (hp : p ≠ 0)

/-- The value of `θ` on `z^i ξ^[n]` for a basis index `i : Fin p`. -/
public theorem theta_xiElt_fin (n : ℕ) (i : Fin p) :
    theta B p lam hp (xiElt B p lam n (i : ℕ)) = thetaBasis B p lam n i :=
  theta_xiElt B p lam hp n (i : ℕ) i.isLt

/-- The remainder `ε'(f) = (θ ⊗ 1)(d₁ f) - d₁(θ f)` of assumption (07Q6), as a `B`-linear map.
It is `B`-linear even though `d₁` is not, because the two twisted Leibniz correction terms
`θ(f) ⊗ d b` cancel. -/
public def epsilonPrimeMap :
    primeRing B p lam →ₗ[(B : Type u)] (primeRing B p lam ⊗[(B : Type u)] Omega) where
  toFun f :=
    TensorProduct.map (theta B p lam hp) (LinearMap.id (R := (B : Type u)) (M := Omega))
        (dec.dOne f) -
      dec.dOne (theta B p lam hp f)
  map_add' f g := by
    have h1 : dec.dOne (f + g) = dec.dOne f + dec.dOne g := dec.dOne_add f g
    have h2 : theta B p lam hp (f + g) = theta B p lam hp f + theta B p lam hp g :=
      map_add _ f g
    rw [h1, h2, dec.dOne_add, map_add]
    abel
  map_smul' b f := by
    have h1 : dec.dOne (b • f) =
        b • dec.dOne f + f ⊗ₜ[(B : Type u)] SourceDeRham.targetD pi b :=
      dec.dOne_smul hpsi b f
    have h2 : theta B p lam hp (b • f) = b • theta B p lam hp f := map_smul _ b f
    have h3 : dec.dOne (b • theta B p lam hp f) =
        b • dec.dOne (theta B p lam hp f) +
          theta B p lam hp f ⊗ₜ[(B : Type u)] SourceDeRham.targetD pi b :=
      dec.dOne_smul hpsi b _
    rw [RingHom.id_apply, h1, h2, h3, map_add, map_smul, TensorProduct.map_tmul,
      LinearMap.id_apply, smul_sub]
    abel

/-- The remainder `ε'` has the stated underlying function. -/
public theorem epsilonPrimeMap_apply (f : primeRing B p lam) :
    epsilonPrimeMap B p lam pi dec hpsi hp f =
      TensorProduct.map (theta B p lam hp) (LinearMap.id (R := (B : Type u)) (M := Omega))
          (dec.dOne f) -
        dec.dOne (theta B p lam hp f) := rfl

/-- `(θ ⊗ 1)(d₁(ξ^[m+1] z^i)) = -(θ(z^i ξ^[m]) ⊗ dλ)`. -/
private theorem map_theta_dOne_xiElt_succ (hv : DOneValues B p lam pi dec) (m : ℕ) (i : Fin p) :
    TensorProduct.map (theta B p lam hp) (LinearMap.id (R := (B : Type u)) (M := Omega))
        (dec.dOne (xiElt B p lam (m + 1) (i : ℕ))) =
      -(thetaBasis B p lam m i ⊗ₜ[(B : Type u)] SourceDeRham.targetD pi lam) := by
  rw [hv.xi, map_neg, TensorProduct.map_tmul, LinearMap.id_apply, theta_xiElt_fin]

omit [Nontrivial (XiAlg B)] in
include hpsi in
/-- `d₁(θ(z^{p-1})) = 0`: the differential of `z^p = ξ + λ` has base-change component
`-(1 ⊗ dλ) + (1 ⊗ dλ) = 0`. -/
public theorem dOne_thetaBasis_zero_top (hv : DOneValues B p lam pi dec) (i : Fin p)
    (hi : (i : ℕ) + 1 = p) : dec.dOne (thetaBasis B p lam 0 i) = 0 := by
  rw [thetaBasis_zero_top B p lam i hi, zElt_pow_prime, dec.dOne_add, hv.xi 0 0,
    dec.dOne_smul hpsi, hv.pow 0, smul_zero, zero_add, xiElt_zero_zero, neg_add_cancel]

variable [Fact p.Prime] [Algebra (IntegersAtPrime p) (B : Type u)]

omit [Nontrivial (XiAlg B)] in
/-- The descended de Rham differential of `B` annihilates `p/k` for `k` prime to `p`: both `p`
and `k` are images of natural numbers, and `k` is invertible. -/
public theorem targetD_natCast_mul_inverse {k : ℕ} (hk : ¬ p ∣ k) :
    SourceDeRham.targetD pi
        (((p : ℕ) : (B : Type u)) * Ring.inverse ((k : ℕ) : (B : Type u))) = 0 :=
  targetD_mul_eq_zero pi (targetD_natCast pi p)
    (targetD_ringInverse pi (isUnit_natCast_of_not_dvd B p hk) (targetD_natCast pi k))

omit [Nontrivial (XiAlg B)] in
/-- The recursion defining `θ` on `z^i ξ^[n]` for `i + 1 ≠ p`, cleared of denominators:
`(i + 1 + pn) θ(z^i ξ^[n]) = p z^{i+1} ξ^[n] - p λ θ(z^i ξ^[n-1])`. -/
public theorem natCast_smul_thetaBasis (i : Fin p) (hi : (i : ℕ) + 1 ≠ p) (n : ℕ) :
    (((i : ℕ) + 1 + p * n : ℕ) : (B : Type u)) • thetaBasis B p lam n i =
      ((p : ℕ) : (B : Type u)) • xiElt B p lam n ((i : ℕ) + 1) -
        (((p : ℕ) : (B : Type u)) * lam) • thetaBasisPred B p lam n i := by
  have hip : (i : ℕ) + 1 < p := lt_of_le_of_ne i.isLt hi
  cases n with
  | zero =>
    have hidx : (i : ℕ) + 1 + p * 0 = (i : ℕ) + 1 := by omega
    rw [hidx, thetaBasis_zero_of_ne B p lam i hi, thetaBasisPred_zero, smul_zero, sub_zero,
      smul_smul,
      mul_mul_inverse_cancel _ _ _
        (Ring.inverse_mul_cancel _ (isUnit_natCast_of_lt B p (by omega) hip))]
  | succ k =>
    rw [thetaBasis_succ_of_ne B p lam k i hi, thetaBasisPred_succ, smul_smul,
      Ring.mul_inverse_cancel _ (isUnit_natCast_add_mul B p (by omega) hip), one_smul]

omit [Nontrivial (XiAlg B)] in
include hpsi in
/-- Applying `d₁` to the recursion for `θ` on `z^i ξ^[n+1]`, with `i + 1 ≠ p`.  The de Rham
differential kills the scalars `1/(i+1+p(n+1))` and `p`, and `d(p λ) = p dλ`. -/
public theorem dOne_thetaBasis_succ (hv : DOneValues B p lam pi dec) (i : Fin p)
    (hi : (i : ℕ) + 1 ≠ p) (n : ℕ) :
    dec.dOne (thetaBasis B p lam (n + 1) i) =
      Ring.inverse (((i : ℕ) + 1 + p * (n + 1) : ℕ) : (B : Type u)) •
        (-(((p : ℕ) : (B : Type u)) •
              (xiElt B p lam n ((i : ℕ) + 1) ⊗ₜ[(B : Type u)]
                SourceDeRham.targetD pi lam)) -
          ((((p : ℕ) : (B : Type u)) * lam) • dec.dOne (thetaBasis B p lam n i) +
            ((p : ℕ) : (B : Type u)) •
              (thetaBasis B p lam n i ⊗ₜ[(B : Type u)] SourceDeRham.targetD pi lam))) := by
  have hip : (i : ℕ) + 1 < p := lt_of_le_of_ne i.isLt hi
  have hunit : IsUnit ((((i : ℕ) + 1 + p * (n + 1) : ℕ)) : (B : Type u)) :=
    isUnit_natCast_add_mul B p (by omega) hip
  have hdinv : SourceDeRham.targetD pi
      (Ring.inverse ((((i : ℕ) + 1 + p * (n + 1) : ℕ)) : (B : Type u))) = 0 :=
    targetD_ringInverse pi hunit (targetD_natCast pi _)
  have hdp : SourceDeRham.targetD pi ((p : ℕ) : (B : Type u)) = 0 := targetD_natCast pi p
  have hdplam : SourceDeRham.targetD pi (((p : ℕ) : (B : Type u)) * lam) =
      ((p : ℕ) : (B : Type u)) • SourceDeRham.targetD pi lam := by
    rw [targetD_leibniz, hdp, smul_zero, add_zero]
  rw [thetaBasis_succ_of_ne B p lam n i hi, dec.dOne_smul hpsi, hdinv,
    TensorProduct.tmul_zero, add_zero, dec.dOne_sub, dec.dOne_smul hpsi,
    dec.dOne_smul hpsi, hdp, TensorProduct.tmul_zero, add_zero, hdplam,
    TensorProduct.tmul_smul, hv.xi n ((i : ℕ) + 1), smul_neg]

omit [Nontrivial (XiAlg B)] in
include hpsi in
/-- `d₁(θ(z^i ξ^[n])) = -(θ(z^i ξ^[n-1]) ⊗ dλ)` for `i + 1 ≠ p`, by induction on `n` from the
recursion defining `θ`. -/
public theorem dOne_thetaBasis_of_ne (hv : DOneValues B p lam pi dec) (i : Fin p)
    (hi : (i : ℕ) + 1 ≠ p) (n : ℕ) :
    dec.dOne (thetaBasis B p lam n i) =
      -(thetaBasisPred B p lam n i ⊗ₜ[(B : Type u)] SourceDeRham.targetD pi lam) := by
  have hip : (i : ℕ) + 1 < p := lt_of_le_of_ne i.isLt hi
  induction n with
  | zero =>
    rw [thetaBasisPred_zero, TensorProduct.zero_tmul, neg_zero,
      thetaBasis_zero_of_ne B p lam i hi, dec.dOne_smul hpsi, hv.pow ((i : ℕ) + 1), smul_zero,
      zero_add,
      targetD_natCast_mul_inverse B p pi (Nat.not_dvd_of_pos_of_lt (by omega) hip),
      TensorProduct.tmul_zero]
  | succ k ih =>
    have hcast : (((i : ℕ) + 1 + p * k : ℕ) : (B : Type u)) + ((p : ℕ) : (B : Type u)) =
        (((i : ℕ) + 1 + p * (k + 1) : ℕ) : (B : Type u)) := by
      push_cast
      ring
    have hc : Ring.inverse ((((i : ℕ) + 1 + p * (k + 1) : ℕ)) : (B : Type u)) *
        ((((i : ℕ) + 1 + p * k : ℕ) : (B : Type u)) + ((p : ℕ) : (B : Type u))) = 1 := by
      rw [hcast]
      exact Ring.inverse_mul_cancel _ (isUnit_natCast_add_mul B p (by omega) hip)
    have hW : (((i : ℕ) + 1 + p * k : ℕ) : (B : Type u)) •
          (thetaBasis B p lam k i ⊗ₜ[(B : Type u)] SourceDeRham.targetD pi lam) =
        ((p : ℕ) : (B : Type u)) •
            (xiElt B p lam k ((i : ℕ) + 1) ⊗ₜ[(B : Type u)] SourceDeRham.targetD pi lam) -
          (((p : ℕ) : (B : Type u)) * lam) •
            (thetaBasisPred B p lam k i ⊗ₜ[(B : Type u)] SourceDeRham.targetD pi lam) := by
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', TensorProduct.smul_tmul',
        ← TensorProduct.sub_tmul, natCast_smul_thetaBasis B p lam i hi k]
    rw [thetaBasisPred_succ, dOne_thetaBasis_succ B p lam pi dec hpsi hv i hi k, ih,
      smul_bracket_eq_neg _ _ _ _ _ _ _ hW hc]

/-- **Step 1 and Step 2.**  For `i + 1 ≠ p` the remainder `ε'` vanishes on every basis vector
`z^i ξ^[n]`. -/
public theorem epsilonPrimeMap_xiElt_of_ne (hv : DOneValues B p lam pi dec) (i : Fin p)
    (hi : (i : ℕ) + 1 ≠ p) (n : ℕ) :
    epsilonPrimeMap B p lam pi dec hpsi hp (xiElt B p lam n (i : ℕ)) = 0 := by
  rw [epsilonPrimeMap_apply, theta_xiElt_fin,
    dOne_thetaBasis_of_ne B p lam pi dec hpsi hv i hi n, sub_eq_zero]
  cases n with
  | zero =>
    rw [hv.pow, map_zero, thetaBasisPred_zero, TensorProduct.zero_tmul, neg_zero]
  | succ m =>
    rw [map_theta_dOne_xiElt_succ B p lam pi dec hp hv, thetaBasisPred_succ]

omit [Fact p.Prime] [Algebra (IntegersAtPrime p) (B : Type u)] in
/-- **Step 3.**  For `i + 1 = p` the remainder `ε'` vanishes on `z^{p-1} ξ^[n]` for `n ≠ 1`
and equals `-(1 ⊗ λ dλ)` for `n = 1`; in every case it lies in `1 ⊗ Ω`. -/
public theorem epsilonPrimeMap_xiElt_mem_top (hv : DOneValues B p lam pi dec) (i : Fin p)
    (hi : (i : ℕ) + 1 = p) (n : ℕ) :
    epsilonPrimeMap B p lam pi dec hpsi hp (xiElt B p lam n (i : ℕ)) ∈
      LinearMap.range (TensorProduct.mk (B : Type u) (primeRing B p lam) Omega 1) := by
  rw [epsilonPrimeMap_apply, theta_xiElt_fin]
  cases n with
  | zero =>
    rw [hv.pow, map_zero, dOne_thetaBasis_zero_top B p lam pi dec hpsi hv i hi, sub_zero]
    exact Submodule.zero_mem _
  | succ m =>
    rw [map_theta_dOne_xiElt_succ B p lam pi dec hp hv, thetaBasis_succ_top B p lam m i hi,
      hv.xi]
    cases m with
    | zero =>
      refine ⟨-(lam • SourceDeRham.targetD pi lam), ?_⟩
      rw [TensorProduct.mk_apply, TensorProduct.tmul_neg, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', thetaBasis_zero_top B p lam i hi, zElt_pow_prime,
        xiElt_zero_zero, TensorProduct.add_tmul]
      abel
    | succ k =>
      rw [thetaBasis_succ_top B p lam k i hi, sub_neg_eq_add, neg_add_cancel]
      exact Submodule.zero_mem _

/-- The remainder `ε'` lies in `1 ⊗ Ω` on every basis vector `z^i ξ^[n]`. -/
public theorem epsilonPrimeMap_xiElt_mem (hv : DOneValues B p lam pi dec) (n : ℕ) (i : Fin p) :
    epsilonPrimeMap B p lam pi dec hpsi hp (xiElt B p lam n (i : ℕ)) ∈
      LinearMap.range (TensorProduct.mk (B : Type u) (primeRing B p lam) Omega 1) := by
  by_cases hi : (i : ℕ) + 1 = p
  · exact epsilonPrimeMap_xiElt_mem_top B p lam pi dec hpsi hp hv i hi n
  · rw [epsilonPrimeMap_xiElt_of_ne B p lam pi dec hpsi hp hv i hi n]
    exact Submodule.zero_mem _

include hpsi in
/-- **Assumption (07Q6) of Lemma 07Q7 for the extension of Tag 07N1**, in the sharp form of the
footnote of the source: `(θ ⊗ 1)(d₁(f)) - d₁(θ(f))` always lies in `Ω`, being zero on every
basis vector `z^i ξ^[n]` except `z^{p-1} ξ`, where it is `-λ dλ`. -/
public theorem dOne_remainder_mem (hv : DOneValues B p lam pi dec) (f : primeRing B p lam) :
    TensorProduct.map (theta B p lam hp) (LinearMap.id (R := (B : Type u)) (M := Omega))
          (dec.dOne f) - dec.dOne (theta B p lam hp f) ∈
      LinearMap.range (TensorProduct.mk (B : Type u) (primeRing B p lam) Omega 1) := by
  have hle : (⊤ : Submodule (B : Type u) (primeRing B p lam)) ≤
      Submodule.comap (epsilonPrimeMap B p lam pi dec hpsi hp)
        (LinearMap.range (TensorProduct.mk (B : Type u) (primeRing B p lam) Omega 1)) := by
    rw [← (basisZXi B p lam hp).span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨n, i⟩, rfl⟩
    rw [basisZXi_eq_xiElt]
    exact epsilonPrimeMap_xiElt_mem B p lam pi dec hpsi hp hv n i
  have hf := hle (Submodule.mem_top (R := (B : Type u)) (x := f))
  rwa [Submodule.mem_comap, epsilonPrimeMap_apply] at hf

end PthRootExtension

end Remainder

/-- **The conclusion of Tag 07N1 for the extension `B → B[z]⟨ξ⟩/(ξ - (z^p - λ))`.**  For a pair
`(M, ∇)` over `B` with `∇` integrable, the canonical map of de Rham complexes (07PY)

`c_M^• : M ⊗_B Ω^•_B ⟶ M ⊗_B Ω^•_{B'}`

admits a map `e_M^•` in the opposite direction such that both `c_M^• ∘ e_M^•` and
`e_M^• ∘ c_M^•` are homotopic to multiplication by `p`.  This is Lemma 07Q7 at `a = p`, with
the operator `θ` and all of the computations of the proof of Tag 07N1 supplied.

Six of the seven assumptions of Lemma 07Q7 are discharged here for this extension:
`d(p) = 0` because `p` is the image of an integer (07Q0); `θ` is `B`-linear by construction
(07Q2); `∂_z ∘ θ` is multiplication by `p` (07Q3); `B → B'` is universally injective because
the basis `z^i ξ^[n]` splits it (07Q4); `p f - θ(∂_z f)` lies in `B` (07Q5); and
`(θ ⊗ 1)(d₁ f) - d₁(θ f)` lies in `Ω` (07Q6).

This is the form of the conclusion for an *arbitrary* quotient `Ω'` of the one-forms of `B'`,
so it takes the decomposition `Ω' = (B' ⊗_B Ω) ⊕ B' dz` of (07Q1) and the divided power
differential property `d(ξ^[n+1]) = ξ^[n] dξ` of `Ω'` as inputs; for an arbitrary `Ω'` they are
genuinely extra information.  Tag 07N1 is registered on the specialization to the modules of
divided power differentials, where both are theorems:
`Crystalline.exists_homotopyInverse_pthRootExtension_dividedPowerDifferentials` of
`StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootFormsDecomposition`. -/
public theorem exists_homotopyInverse_pthRootExtension
    {A Omega Omega' : Type u} {M : Type w} [CommRing A]
    (B : DividedPowerRing.{u}) (p : ℕ) (lam : (B : Type u))
    [Algebra A (B : Type u)]
    [Nontrivial (PthRootExtension.XiAlg B)] [Fact p.Prime]
    [Algebra (IntegersAtPrime p) (B : Type u)]
    [AddCommGroup Omega] [Module (B : Type u) Omega]
    [AddCommGroup Omega'] [Module (PthRootExtension.primeRing B p lam) Omega']
    [AddCommGroup M] [Module (B : Type u) M]
    (S : SourceDeRham A (B : Type u))
    (S' : SourceDeRham A (PthRootExtension.primeRing B p lam))
    (pi : Ω[(B : Type u)⁄A] →ₗ[(B : Type u)] Omega)
    (pi' : Ω[PthRootExtension.primeRing B p lam⁄A] →ₗ[PthRootExtension.primeRing B p lam]
      Omega')
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (hpi' : Function.Surjective pi') (hgen' : S'.GenerationHypothesis pi')
    (psi : Omega →ₛₗ[algebraMap (B : Type u) (PthRootExtension.primeRing B p lam)] Omega')
    (hpsi : ∀ b : (B : Type u), psi (pi (KaehlerDifferential.D A (B : Type u) b)) =
      pi' (KaehlerDifferential.D A (PthRootExtension.primeRing B p lam)
        (algebraMap (B : Type u) (PthRootExtension.primeRing B p lam) b)))
    (nabla : Connection A (B : Type u) pi M)
    (hintegrable : Connection.IsIntegrable S pi hpi hgen nabla)
    (c : ∀ q : ℕ,
      RestrictScalars A (B : Type u) (M ⊗[(B : Type u)] (⋀[(B : Type u)]^q Omega)) →ₗ[A]
        RestrictScalars A (PthRootExtension.primeRing B p lam)
          ((PthRootExtension.primeRing B p lam ⊗[(B : Type u)] M)
            ⊗[PthRootExtension.primeRing B p lam]
              (⋀[PthRootExtension.primeRing B p lam]^q Omega')))
    (hc_wedge : ∀ (q : ℕ) (m : M) (omega : Fin q → Omega),
      c q (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) q omega) =
        (1 ⊗ₜ[(B : Type u)] m) ⊗ₜ[PthRootExtension.primeRing B p lam]
          exteriorPower.ιMulti (PthRootExtension.primeRing B p lam) q (psi ∘ omega))
    (hc_comm : ∀ (q : ℕ) (x : M ⊗[(B : Type u)] (⋀[(B : Type u)]^q Omega)),
      c (q + 1)
          ((extendedConnection S pi hpi hgen nabla).toLinearMap q x) =
        (extendedConnection S' pi' hpi' hgen'
          (Connection.baseChange psi nabla hpsi)).toLinearMap q (c q x))
    (dec : DzDecomposition pi' psi (PthRootExtension.zElt B p lam))
    (hp : p ≠ 0)
    (hd : PthRootExtension.IsDpowDifferential B p lam (pi' := pi')) :
    ∃ e : ∀ q : ℕ,
      RestrictScalars A (PthRootExtension.primeRing B p lam)
          ((PthRootExtension.primeRing B p lam ⊗[(B : Type u)] M)
            ⊗[PthRootExtension.primeRing B p lam]
              (⋀[PthRootExtension.primeRing B p lam]^q Omega')) →ₗ[A]
        RestrictScalars A (B : Type u) (M ⊗[(B : Type u)] (⋀[(B : Type u)]^q Omega)),
      (∀ (q : ℕ) (x : RestrictScalars A (PthRootExtension.primeRing B p lam)
          ((PthRootExtension.primeRing B p lam ⊗[(B : Type u)] M)
            ⊗[PthRootExtension.primeRing B p lam]
              (⋀[PthRootExtension.primeRing B p lam]^q Omega'))),
          e (q + 1)
              ((extendedConnection S' pi' hpi' hgen'
                (Connection.baseChange psi nabla hpsi)).toLinearMap
                q x) =
            (extendedConnection S pi hpi hgen nabla).toLinearMap
              q (e q x)) ∧
        (∃ h : ∀ q : ℕ,
            RestrictScalars A (PthRootExtension.primeRing B p lam)
                ((PthRootExtension.primeRing B p lam ⊗[(B : Type u)] M)
                  ⊗[PthRootExtension.primeRing B p lam]
                    (⋀[PthRootExtension.primeRing B p lam]^(q + 1) Omega')) →ₗ[A]
              RestrictScalars A (PthRootExtension.primeRing B p lam)
                ((PthRootExtension.primeRing B p lam ⊗[(B : Type u)] M)
                  ⊗[PthRootExtension.primeRing B p lam]
                    (⋀[PthRootExtension.primeRing B p lam]^q Omega')),
          (∀ x : RestrictScalars A (PthRootExtension.primeRing B p lam)
              ((PthRootExtension.primeRing B p lam ⊗[(B : Type u)] M)
                ⊗[PthRootExtension.primeRing B p lam]
                  (⋀[PthRootExtension.primeRing B p lam]^0 Omega')),
              h 0 ((extendedConnection S' pi' hpi' hgen'
                (Connection.baseChange psi nabla hpsi)).toLinearMap
                0 x) =
                RestrictScalars.lsmul A (PthRootExtension.primeRing B p lam)
                    ((PthRootExtension.primeRing B p lam ⊗[(B : Type u)] M)
                      ⊗[PthRootExtension.primeRing B p lam]
                        (⋀[PthRootExtension.primeRing B p lam]^0 Omega'))
                    (algebraMap (B : Type u) (PthRootExtension.primeRing B p lam)
                      ((p : ℕ) : (B : Type u))) x -
                  c 0 (e 0 x)) ∧
            ∀ (q : ℕ)
                (x : RestrictScalars A (PthRootExtension.primeRing B p lam)
                  ((PthRootExtension.primeRing B p lam ⊗[(B : Type u)] M)
                    ⊗[PthRootExtension.primeRing B p lam]
                      (⋀[PthRootExtension.primeRing B p lam]^(q + 1) Omega'))),
              (show RestrictScalars A (PthRootExtension.primeRing B p lam)
                  ((PthRootExtension.primeRing B p lam ⊗[(B : Type u)] M)
                    ⊗[PthRootExtension.primeRing B p lam]
                      (⋀[PthRootExtension.primeRing B p lam]^(q + 1) Omega')) from
                (extendedConnection S' pi' hpi' hgen'
                  (Connection.baseChange psi nabla hpsi)).toLinearMap
                    q (h q x)) +
                  h (q + 1)
                    ((extendedConnection S' pi' hpi' hgen'
                      (Connection.baseChange psi nabla hpsi)).toLinearMap
                      (q + 1) x) =
                RestrictScalars.lsmul A (PthRootExtension.primeRing B p lam)
                    ((PthRootExtension.primeRing B p lam ⊗[(B : Type u)] M)
                      ⊗[PthRootExtension.primeRing B p lam]
                        (⋀[PthRootExtension.primeRing B p lam]^(q + 1) Omega'))
                    (algebraMap (B : Type u) (PthRootExtension.primeRing B p lam)
                      ((p : ℕ) : (B : Type u))) x -
                  c (q + 1) (e (q + 1) x)) ∧
        (∃ k : ∀ q : ℕ,
            RestrictScalars A (B : Type u)
                (M ⊗[(B : Type u)] (⋀[(B : Type u)]^(q + 1) Omega)) →ₗ[A]
              RestrictScalars A (B : Type u) (M ⊗[(B : Type u)] (⋀[(B : Type u)]^q Omega)),
          (∀ x : RestrictScalars A (B : Type u)
              (M ⊗[(B : Type u)] (⋀[(B : Type u)]^0 Omega)),
              k 0 ((extendedConnection S pi hpi hgen nabla).toLinearMap
                0 x) =
                RestrictScalars.lsmul A (B : Type u)
                  (M ⊗[(B : Type u)] (⋀[(B : Type u)]^0 Omega))
                  ((p : ℕ) : (B : Type u)) x - e 0 (c 0 x)) ∧
            ∀ (q : ℕ) (x : RestrictScalars A (B : Type u)
                (M ⊗[(B : Type u)] (⋀[(B : Type u)]^(q + 1) Omega))),
              (extendedConnection S pi hpi hgen nabla).toLinearMap
                  q (k q x) +
                k (q + 1)
                  ((extendedConnection S pi hpi hgen nabla).toLinearMap
                    (q + 1) x) =
                RestrictScalars.lsmul A (B : Type u)
                    (M ⊗[(B : Type u)] (⋀[(B : Type u)]^(q + 1) Omega))
                    ((p : ℕ) : (B : Type u)) x -
                  e (q + 1) (c (q + 1) x)) :=
  let hpz := PthRootExtension.partialZValues_of_isDpowDifferential pi dec hpsi hp hd
  exists_homotopyInverse_baseChangeDeRhamMap S S' pi pi' hpi hgen hpi' hgen' psi hpsi nabla
    hintegrable c hc_wedge hc_comm ((p : ℕ) : (B : Type u)) (PthRootExtension.zElt B p lam)
    (PthRootExtension.theta B p lam hp) dec (targetD_natCast pi p)
    (fun f ↦ PthRootExtension.partialZ_theta B p lam hp hpz f)
    (PthRootExtension.universallyInjective_toPrimeRing B p lam hp)
    (fun f ↦ ⟨PthRootExtension.epsilon B p lam hp f,
      (PthRootExtension.smul_sub_theta_partialZ B p lam hp hpz f).symm⟩)
    (PthRootExtension.dOne_remainder_mem B p lam pi dec hpsi hp
      (PthRootExtension.dOneValues_of_isDpowDifferential pi dec hpsi hd))

end Crystalline

end

end
