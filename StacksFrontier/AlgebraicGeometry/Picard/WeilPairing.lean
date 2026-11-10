module

public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Algebra.Module.Torsion.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback

/-!
# Frobenius eigenvectors on the Tate module of the Picard group, from a Weil pairing

Let `X` be a smooth projective curve over an algebraically closed field, `ℓ` a prime invertible
on `X`, and `σ` an additive endomorphism of `Pic(X)` (in the application, the action of a
Frobenius). The **Weil pairing** is a family of pairings
`eₙ : Pic(X)[ℓⁿ] × Pic(X)[ℓⁿ] → ℤ/ℓⁿ` (values in `μ_{ℓⁿ}`, identified with `ℤ/ℓⁿ` by a choice of
root of unity) which is nondegenerate and Galois equivariant:
`eₙ(σa, σb) = cₙ · eₙ(a, b)` with `cₙ` the action of `σ` on `μ_{ℓⁿ}` (`q` for the arithmetic
Frobenius of `𝔽_q`, `q⁻¹` for the geometric one).

If the `σ`-fixed `ℓ`-power torsion of `Pic(X)` is bounded, then no nonzero element of the Tate
module `T_ℓ Pic(X) = lim Pic(X)[ℓⁿ]` satisfies `σx = c x`. The existence, nondegeneracy and
equivariance of the Weil pairing, the finiteness of `Pic(X)[ℓⁿ]` (`#Pic(X)[ℓⁿ] = ℓ^{2gn}`) and the
bound on the `σ`-fixed torsion are hypotheses of
`Stacks.Picard.eq_zero_of_smul_eigen_of_weilPairing`.

## Main results

* `Stacks.Picard.natCard_le_natCard_ker_restrictPairing_mul`: `#M ≤ #S^⊥ · #S` for any pairing of a
  finite group into `ℤ/N`.
* `Stacks.Picard.natCard_ker_sub_smul_le`: `#ker(σ - c) ≤ #ker(σ - 1)` for a nondegenerate
  `σ`-equivariant pairing with factor `c`.
* `Stacks.Picard.eq_zero_of_compatible_of_smul_eigen`: no nonzero compatible system of
  `ℓⁿ`-torsion points with `σxₙ = cₙxₙ`, for an abelian group with such pairings at every level
  and bounded fixed torsion.
* `Stacks.Picard.eq_zero_of_smul_eigen_of_weilPairing`: the statement for `Pic(X)` of a smooth
  projective curve, with the inputs from the Jacobian as hypotheses.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Picard

section Finite

variable {M : Type*} [AddCommGroup M] {N : ℕ} [NeZero N]

/-- Additive maps from a finite group to `ℤ/N` are at most as many as its elements: they embed
into the characters of the group, through the standard character of `ℤ/N`. -/
theorem natCard_addMonoidHom_zmod_le (S : Type*) [AddCommGroup S] [Finite S] :
    Nat.card (S →+ ZMod N) ≤ Nat.card S := by
  classical
  have : Fintype S := Fintype.ofFinite S
  have hinj : Function.Injective
      (fun f : S →+ ZMod N => (ZMod.stdAddChar (N := N)).compAddMonoidHom f) := by
    intro f g hfg
    ext s
    exact ZMod.injective_stdAddChar (by simpa using congrArg (fun χ : AddChar S ℂ ↦ χ s) hfg)
  have : Finite (AddChar S ℂ) := Finite.of_fintype _
  calc Nat.card (S →+ ZMod N) ≤ Nat.card (AddChar S ℂ) := Nat.card_le_card_of_injective _ hinj
    _ = Fintype.card (AddChar S ℂ) := Nat.card_eq_fintype_card
    _ ≤ Fintype.card S := AddChar.card_addChar_le S ℂ
    _ = Nat.card S := Nat.card_eq_fintype_card.symm

/-- The restriction of a pairing to a subgroup in the second variable: `c ↦ e(c, -)|_S`. Its kernel
is the left annihilator of `S`. -/
def restrictPairing (e : M →+ M →+ ZMod N) (S : AddSubgroup M) : M →+ (S →+ ZMod N) where
  toFun c := (e c).comp S.subtype
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

omit [NeZero N] in
@[simp]
theorem restrictPairing_apply (e : M →+ M →+ ZMod N) (S : AddSubgroup M) (c : M) (s : S) :
    restrictPairing e S c s = e c s :=
  rfl

/-- `#M = #ker φ · #im φ` for an additive map out of a finite group. -/
theorem natCard_eq_natCard_ker_mul_natCard_range [Finite M] {P : Type*} [AddGroup P]
    (φ : M →+ P) : Nat.card M = Nat.card φ.ker * Nat.card φ.range := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv, mul_comm]

/-- `#M ≤ #S^⊥ · #S` for a pairing of a finite group into `ℤ/N`, `S^⊥` the left annihilator
of a subgroup `S`. -/
theorem natCard_le_natCard_ker_restrictPairing_mul [Finite M] (e : M →+ M →+ ZMod N)
    (S : AddSubgroup M) :
    Nat.card M ≤ Nat.card (restrictPairing e S).ker * Nat.card S := by
  rw [natCard_eq_natCard_ker_mul_natCard_range (restrictPairing e S)]
  have : Finite (S →+ ZMod N) :=
    Finite.of_injective (fun f : S →+ ZMod N => (f : S → ZMod N)) DFunLike.coe_injective
  refine Nat.mul_le_mul_left _ ?_
  calc Nat.card (restrictPairing e S).range ≤ Nat.card (S →+ ZMod N) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
    _ ≤ Nat.card S := natCard_addMonoidHom_zmod_le S

variable [Finite M] (e : M →+ M →+ ZMod N) (he₀ : ∀ a, (∀ b, e a b = 0) → a = 0)
  (σ : M →+ M) (c : ℤ) (hc : IsUnit (c : ZMod N)) (he : ∀ a b, e (σ a) (σ b) = c • e a b)

include he₀ hc he in
omit [NeZero N] [Finite M] in
/-- An endomorphism multiplying a left-nondegenerate pairing by a unit is injective. -/
theorem injective_of_pairing_smul : Function.Injective σ := by
  refine (injective_iff_map_eq_zero σ).2 fun a ha => he₀ a fun b => ?_
  exact hc.mul_right_eq_zero.1 (by rw [← zsmul_eq_mul, ← he, ha, map_zero, AddMonoidHom.zero_apply])

include he₀ hc he in
/-- `#ker(σ - c) ≤ #ker(σ - 1)` on a finite group with a left-nondegenerate pairing `e` into `ℤ/N`
such that `e(σa, σb) = c e(a, b)`, `c` a unit mod `N`. -/
theorem natCard_ker_sub_smul_le :
    Nat.card (σ - c • AddMonoidHom.id M).ker ≤ Nat.card (σ - AddMonoidHom.id M).ker := by
  set ψ := σ - c • AddMonoidHom.id M
  set φ := σ - AddMonoidHom.id M
  have hsurj : Function.Surjective σ :=
    Finite.injective_iff_surjective.1 (injective_of_pairing_smul e he₀ σ c hc he)
  have hle : (restrictPairing e ψ.range).ker ≤ φ.ker := by
    intro a ha
    rw [AddMonoidHom.mem_ker]
    refine he₀ _ fun b' => ?_
    obtain ⟨b, rfl⟩ := hsurj b'
    have hψ : e a (ψ b) = 0 := by
      simpa using congrArg (fun χ : ψ.range →+ ZMod N ↦ χ ⟨ψ b, b, rfl⟩) ha
    have hψ' : e a (ψ b) = e a (σ b) - c • e a b := by
      simp [ψ, AddMonoidHom.sub_apply, map_sub, map_zsmul]
    have : e (φ a) (σ b) = -(e a (ψ b)) := by
      simp only [φ, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_sub,
        AddMonoidHom.sub_apply, he, hψ']
      abel
    rw [this, hψ, neg_zero]
  have hcount := natCard_le_natCard_ker_restrictPairing_mul e ψ.range
  rw [natCard_eq_natCard_ker_mul_natCard_range ψ] at hcount
  exact (Nat.le_of_mul_le_mul_right hcount Nat.card_pos).trans (AddSubgroup.card_le_of_le hle)

end Finite

section TateModule

variable {A : Type*} [AddCommGroup A] (ℓ : ℕ)

/-- An additive endomorphism of `A` preserves the `m`-torsion. -/
def torsionByRestrict (σ : A →+ A) (m : ℤ) :
    Submodule.torsionBy ℤ A m →+ Submodule.torsionBy ℤ A m where
  toFun a := ⟨σ a.1, by
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul, (Submodule.mem_torsionBy_iff m a.1).1 a.2,
      map_zero]⟩
  map_zero' := Subtype.ext (map_zero σ)
  map_add' a b := Subtype.ext (map_add σ a.1 b.1)

@[simp]
theorem torsionByRestrict_apply (σ : A →+ A) (m : ℤ) (a : Submodule.torsionBy ℤ A m) :
    (torsionByRestrict σ m a : A) = σ (a : A) :=
  rfl

/-- In a compatible system `ℓ x_{n+1} = xₙ`, `xₙ = ℓᵏ x_{n+k}`. -/
theorem eq_pow_smul_of_compatible {x : ℕ → A} (hx : ∀ n, ℓ • x (n + 1) = x n) (n k : ℕ) :
    x n = ℓ ^ k • x (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih, pow_succ, mul_smul, ← Nat.add_assoc, hx]

/-- No nonzero compatible system of `ℓⁿ`-torsion points is a `σ`-eigenvector for the cyclotomic
factor, given Weil-type pairings. Let `σ` be an additive endomorphism of `A` and, for
every `n`, let `eₙ` be a left-nondegenerate pairing of the (finite) `ℓⁿ`-torsion of `A` into
`ℤ/ℓⁿ` with `eₙ(σa, σb) = cₙ eₙ(a, b)`, `cₙ` a unit mod `ℓⁿ`. If the `σ`-fixed `ℓⁿ`-torsion has
bounded size, then every compatible system `(xₙ)`, `ℓⁿ xₙ = 0`, `ℓ x_{n+1} = xₙ`, with
`σ xₙ = cₙ xₙ` vanishes. -/
theorem eq_zero_of_compatible_of_smul_eigen (hℓ : ℓ.Prime) (σ : A →+ A) (c : ℕ → ℤ)
    [∀ n, Finite (Submodule.torsionBy ℤ A ((ℓ : ℤ) ^ n))]
    (e : ∀ n, Submodule.torsionBy ℤ A ((ℓ : ℤ) ^ n) →+ Submodule.torsionBy ℤ A ((ℓ : ℤ) ^ n) →+
      ZMod (ℓ ^ n))
    (he₀ : ∀ n a, (∀ b, e n a b = 0) → a = 0)
    (hc : ∀ n, IsUnit (c n : ZMod (ℓ ^ n)))
    (he : ∀ n a b, e n (torsionByRestrict σ _ a) (torsionByRestrict σ _ b) = c n • e n a b)
    (hfix : ∃ C : ℕ, ∀ n, Nat.card (torsionByRestrict σ ((ℓ : ℤ) ^ n) -
      AddMonoidHom.id (Submodule.torsionBy ℤ A ((ℓ : ℤ) ^ n))).ker ≤ C)
    (x : ℕ → A) (hxt : ∀ n, ((ℓ : ℤ) ^ n) • x n = 0) (hx : ∀ n, ℓ • x (n + 1) = x n)
    (hσx : ∀ n, σ (x n) = c n • x n) (n : ℕ) : x n = 0 := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨C, hC⟩ := hfix
  have hord : ∀ m, addOrderOf (x m) ≤ C := by
    intro m
    let M := Submodule.torsionBy ℤ A ((ℓ : ℤ) ^ m)
    let y : M := ⟨x m, (Submodule.mem_torsionBy_iff _ _).2 (hxt m)⟩
    let ψ := torsionByRestrict σ ((ℓ : ℤ) ^ m) - c m • AddMonoidHom.id M
    have hy : y ∈ ψ.ker := by
      rw [AddMonoidHom.mem_ker]
      refine Subtype.ext ?_
      change σ (x m) - c m • x m = 0
      rw [hσx m, sub_self]
    have hcard := natCard_ker_sub_smul_le (e m) (he₀ m) (torsionByRestrict σ _) (c m) (hc m)
      (he m)
    have h₁ : addOrderOf (⟨y, hy⟩ : ψ.ker) ≤ Nat.card ψ.ker := addOrderOf_le_card
    have h₂ : addOrderOf (⟨y, hy⟩ : ψ.ker) = addOrderOf (x m) := by
      rw [← addOrderOf_injective ψ.ker.subtype Subtype.val_injective ⟨y, hy⟩]
      exact (addOrderOf_injective M.toAddSubgroup.subtype Subtype.val_injective y).symm
    exact h₂ ▸ h₁.trans (hcard.trans (hC m))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, C < ℓ ^ k := ⟨C, Nat.lt_pow_self hℓ.one_lt⟩
  rw [eq_pow_smul_of_compatible ℓ hx n k]
  have hdvd : addOrderOf (x (n + k)) ∣ ℓ ^ (n + k) :=
    addOrderOf_dvd_of_nsmul_eq_zero (by exact_mod_cast hxt (n + k))
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hℓ).1 hdvd
  have hjk : j ≤ k := by
    by_contra h
    have : ℓ ^ k < ℓ ^ j := Nat.pow_lt_pow_right hℓ.one_lt (by omega)
    have := hord (n + k)
    omega
  exact addOrderOf_dvd_iff_nsmul_eq_zero.1 (hjeq ▸ Nat.pow_dvd_pow ℓ hjk)

end TateModule

section Curve

open AlgebraicGeometry

/-- No nonzero element of the Tate module of `Pic(X)` is a `σ`-eigenvector for the cyclotomic
factor, for a smooth projective curve `X` over an algebraically closed field `k`, a prime `ℓ` and
an additive endomorphism `σ` of `Pic(X)`, given:

* (`hPic`) `Pic(X)[ℓⁿ] ≅ (ℤ/ℓⁿ)^{2g}`, so the `ℓⁿ`-torsion is finite;
* (`hWeil`) the Weil pairing: for every `n` a left-nondegenerate pairing
  `eₙ : Pic(X)[ℓⁿ] × Pic(X)[ℓⁿ] → ℤ/ℓⁿ` with `eₙ(σa, σb) = cₙ eₙ(a, b)`;
* (`hfix`) the `σ`-fixed `ℓ`-power torsion is bounded.

Then every compatible system `(xₙ)` of `ℓⁿ`-torsion classes with `σxₙ = cₙxₙ` vanishes. -/
theorem eq_zero_of_smul_eigen_of_weilPairing {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hPic : ∀ n : ℕ, Nonempty (Submodule.torsionBy ℤ (Stacks.Picard.ofScheme X) ((ℓ : ℤ) ^ n) ≃+
      (Fin (2 * genus f) → ZMod (ℓ ^ n))))
    (σ : Stacks.Picard.ofScheme X →+ Stacks.Picard.ofScheme X) (c : ℕ → ℤ)
    (hc : ∀ n, IsUnit (c n : ZMod (ℓ ^ n)))
    (hWeil : ∀ n, ∃ e : Submodule.torsionBy ℤ (Stacks.Picard.ofScheme X) ((ℓ : ℤ) ^ n) →+
        Submodule.torsionBy ℤ (Stacks.Picard.ofScheme X) ((ℓ : ℤ) ^ n) →+ ZMod (ℓ ^ n),
      (∀ a, (∀ b, e a b = 0) → a = 0) ∧
        ∀ a b, e (torsionByRestrict σ _ a) (torsionByRestrict σ _ b) = c n • e a b)
    (hfix : ∃ C : ℕ, ∀ n, Nat.card (torsionByRestrict σ ((ℓ : ℤ) ^ n) -
      AddMonoidHom.id (Submodule.torsionBy ℤ (Stacks.Picard.ofScheme X) ((ℓ : ℤ) ^ n))).ker ≤ C)
    (x : ℕ → Stacks.Picard.ofScheme X) (hxt : ∀ n, ((ℓ : ℤ) ^ n) • x n = 0)
    (hx : ∀ n, ℓ • x (n + 1) = x n) (hσx : ∀ n, σ (x n) = c n • x n) (n : ℕ) : x n = 0 := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : ∀ n, Finite (Submodule.torsionBy ℤ (Stacks.Picard.ofScheme X) ((ℓ : ℤ) ^ n)) :=
    fun n => Finite.of_equiv _ (hPic n).some.toEquiv.symm
  choose e he₀ he using hWeil
  exact eq_zero_of_compatible_of_smul_eigen ℓ hℓ σ c e he₀ hc he hfix x hxt hx hσx n

end Curve

end Stacks.Picard

end
