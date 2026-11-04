module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AlgebraTower
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BaseChangeHomotopyInverse
public import StacksFrontier.RingTheory.DividedPowers.Extend
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.Basic

/-!
# Pulling back along a purely inseparable map: the descended differential and its components

Elementary properties of the descended de Rham differential `d f = π (D f)`, and of the two
components `∂_z` and `d₁` of the differential given by a decomposition
`Ω' = (B' ⊗_B Ω) ⊕ B' dz` (a `Crystalline.DzDecomposition`), used in the proof of Tag 07N1.

## Main results

* `Crystalline.targetD_natCast` — assumption (07Q0) of Lemma 07Q7 for `a` the image of an
  integer.
* `Crystalline.targetD_ringInverse` — the de Rham differential annihilates the inverse of a unit
  it annihilates.
* `Crystalline.DzDecomposition.partialZLinear` — `∂_z` is `B`-linear.
* `Crystalline.DzDecomposition.dOne_smul` — the twisted Leibniz rule `d₁(b f) = b d₁(f) + f ⊗ db`.
* `Crystalline.DzDecomposition.partialZ_mul` and `Crystalline.DzDecomposition.dOne_mul` — the
  Leibniz rules for the two components of the differential.

## References

* [Stacks Project, Tag 07Q7](https://stacks.math.columbia.edu/tag/07Q7)
* [Stacks Project, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
-/

@[expose] public section

noncomputable section

open DividedPowers Stacks.DeRham.DifferentialDescent

open scoped TensorProduct

universe u u'

namespace Crystalline

/-! ### Elementary properties of the descended de Rham differential -/

section TargetD

variable {A B Omega : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup Omega] [Module B Omega] (pi : Ω[B⁄A] →ₗ[B] Omega)

/-- The descended de Rham differential is the composite of `π` with the universal derivation. -/
public theorem targetD_apply (f : B) :
    SourceDeRham.targetD pi f = pi (KaehlerDifferential.D A B f) := rfl

/-- The descended de Rham differential `d f = π (D f)` is additive. -/
public theorem targetD_add (f g : B) :
    SourceDeRham.targetD pi (f + g) =
      SourceDeRham.targetD pi f + SourceDeRham.targetD pi g := by
  rw [targetD_apply, targetD_apply, targetD_apply, map_add, map_add]

/-- The descended de Rham differential turns a difference into a difference. -/
public theorem targetD_sub (f g : B) :
    SourceDeRham.targetD pi (f - g) =
      SourceDeRham.targetD pi f - SourceDeRham.targetD pi g := by
  rw [targetD_apply, targetD_apply, targetD_apply, map_sub, map_sub]

/-- The Leibniz rule `d(f g) = f d g + g d f` for the descended de Rham differential. -/
public theorem targetD_leibniz (f g : B) :
    SourceDeRham.targetD pi (f * g) =
      f • SourceDeRham.targetD pi g + g • SourceDeRham.targetD pi f := by
  rw [targetD_apply, targetD_apply, targetD_apply, Derivation.leibniz, map_add, map_smul,
    map_smul]

/-- The descended de Rham differential annihilates `1`. -/
public theorem targetD_one : SourceDeRham.targetD pi (1 : B) = 0 := by
  rw [targetD_apply, Derivation.map_one_eq_zero, map_zero]

/-- The descended de Rham differential annihilates the inverse of any unit it annihilates: the
Leibniz rule for `x⁻¹ x = 1` gives `x d(x⁻¹) = 0`, and `x` is invertible. -/
public theorem targetD_ringInverse {x : B} (hx : IsUnit x)
    (hdx : SourceDeRham.targetD pi x = 0) :
    SourceDeRham.targetD pi (Ring.inverse x) = 0 := by
  have h1 : SourceDeRham.targetD pi (Ring.inverse x * x) = 0 := by
    rw [Ring.inverse_mul_cancel x hx, targetD_one]
  rw [targetD_leibniz, hdx, smul_zero, zero_add] at h1
  have h2 : Ring.inverse x • (x • SourceDeRham.targetD pi (Ring.inverse x)) = 0 := by
    rw [h1, smul_zero]
  rwa [smul_smul, Ring.inverse_mul_cancel x hx, one_smul] at h2

/-- The descended de Rham differential annihilates a product of two elements it annihilates. -/
public theorem targetD_mul_eq_zero {x y : B} (hx : SourceDeRham.targetD pi x = 0)
    (hy : SourceDeRham.targetD pi y = 0) : SourceDeRham.targetD pi (x * y) = 0 := by
  rw [targetD_leibniz, hx, hy, smul_zero, smul_zero, add_zero]

end TargetD

/-- The de Rham differential descended `π : Ω_{B/A} → Ω` annihilates the image of a
natural number, since a derivation does.  This is assumption (07Q0) of Lemma 07Q7 when `a` is
the image of an integer. -/
public theorem targetD_natCast {A B Omega : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Omega] [Module B Omega] (pi : Ω[B⁄A] →ₗ[B] Omega) (n : ℕ) :
    SourceDeRham.targetD pi (n : B) = 0 := by
  change pi (KaehlerDifferential.D A B (n : B)) = 0
  rw [Derivation.map_natCast, map_zero]

section PartialZ

variable {A B Omega : Type u} {A' B' Omega' : Type u'}
variable
  [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B']
  [AddCommGroup Omega] [Module B Omega]
  [AddCommGroup Omega'] [Module B' Omega']

variable {pi : Ω[B⁄A] →ₗ[B] Omega} {pi' : Ω[B'⁄A'] →ₗ[B'] Omega'}
  {psi : Omega →ₛₗ[algebraMap B B'] Omega'} {z : B'}

namespace DzDecomposition

omit [SMulCommClass A' B B'] in
/-- The image `ψ(ω)` of a one-form of `B` lies in the base-change summand of the decomposition
`Ω' = (B' ⊗_B Ω) ⊕ B' dz`, with coordinate `1 ⊗ ω`. -/
public theorem equiv_symm_psi (dec : DzDecomposition pi' psi z) (w : Omega) :
    dec.equiv.symm (psi w) = ((1 : B') ⊗ₜ[B] w, 0) := by
  have h := dec.equiv_tmul 1 w
  rw [one_smul] at h
  rw [← h, LinearEquiv.symm_apply_apply]

omit [Algebra A A'] [Algebra A B'] [IsScalarTower A B B'] [IsScalarTower A A' B']
  [SMulCommClass A' B B'] in
/-- `∂_z` vanishes on the image of `B`: the differential of `algebraMap B B' b` is `ψ(π(d b))`,
which lies in the base-change summand. -/
public theorem partialZ_algebraMap (dec : DzDecomposition pi' psi z)
    (hpsi : ∀ b : B, psi (pi (KaehlerDifferential.D A B b)) =
      pi' (KaehlerDifferential.D A' B' (algebraMap B B' b)))
    (b : B) : dec.partialZ (algebraMap B B' b) = 0 := by
  have h : SourceDeRham.targetD pi' (algebraMap B B' b) =
      psi (pi (KaehlerDifferential.D A B b)) := (hpsi b).symm
  change (dec.equiv.symm (SourceDeRham.targetD pi' (algebraMap B B' b))).2 = 0
  rw [h, dec.equiv_symm_psi]

omit [SMulCommClass A' B B'] in
/-- `∂_z` is additive, the descended de Rham differential and the decomposition both being so.
-/
public theorem partialZ_add (dec : DzDecomposition pi' psi z) (f g : B') :
    dec.partialZ (f + g) = dec.partialZ f + dec.partialZ g := by
  change (dec.equiv.symm (SourceDeRham.targetD pi' (f + g))).2 = _
  rw [targetD_add, map_add]
  rfl

omit [SMulCommClass A' B B'] in
/-- `∂_z` turns a difference into a difference. -/
public theorem partialZ_sub (dec : DzDecomposition pi' psi z) (f g : B') :
    dec.partialZ (f - g) = dec.partialZ f - dec.partialZ g := by
  change (dec.equiv.symm (SourceDeRham.targetD pi' (f - g))).2 = _
  rw [targetD_sub, map_sub, Prod.snd_sub]
  rfl

omit [Algebra A A'] [Algebra A B'] [IsScalarTower A B B'] [IsScalarTower A A' B']
  [SMulCommClass A' B B'] in
/-- `∂_z` is `B`-linear: by the Leibniz rule the differential of `b f` is
`b d(f) + f d(b)`, and `∂_z` kills the second term because `b` comes from `B`. -/
public theorem partialZ_smul (dec : DzDecomposition pi' psi z)
    (hpsi : ∀ b : B, psi (pi (KaehlerDifferential.D A B b)) =
      pi' (KaehlerDifferential.D A' B' (algebraMap B B' b)))
    (b : B) (f : B') : dec.partialZ (b • f) = b • dec.partialZ f := by
  change (dec.equiv.symm (SourceDeRham.targetD pi' (b • f))).2 = _
  rw [Algebra.smul_def, targetD_leibniz, map_add, map_smul, map_smul]
  change algebraMap B B' b • dec.partialZ f + f • dec.partialZ (algebraMap B B' b) = _
  rw [dec.partialZ_algebraMap hpsi, smul_zero, add_zero]
  exact IsScalarTower.algebraMap_smul B' b (dec.partialZ f)

/-- `∂_z` as a `B`-linear map `B' → B'`. -/
public def partialZLinear (dec : DzDecomposition pi' psi z)
    (hpsi : ∀ b : B, psi (pi (KaehlerDifferential.D A B b)) =
      pi' (KaehlerDifferential.D A' B' (algebraMap B B' b))) :
    B' →ₗ[B] B' where
  toFun := dec.partialZ
  map_add' := dec.partialZ_add
  map_smul' := dec.partialZ_smul hpsi

omit [Algebra A A'] [Algebra A B'] [IsScalarTower A B B'] [IsScalarTower A A' B']
  [SMulCommClass A' B B'] in
/-- The `B`-linear bundle of `∂_z` has `∂_z` as its underlying function. -/
@[simp] public theorem partialZLinear_apply (dec : DzDecomposition pi' psi z)
    (hpsi : ∀ b : B, psi (pi (KaehlerDifferential.D A B b)) =
      pi' (KaehlerDifferential.D A' B' (algebraMap B B' b)))
    (f : B') : dec.partialZLinear hpsi f = dec.partialZ f := rfl

omit [SMulCommClass A' B B'] in
/-- The base-change component of the differential, read through the splitting. -/
public theorem dOne_eq (dec : DzDecomposition pi' psi z) (f : B') :
    dec.dOne f = (dec.equiv.symm (SourceDeRham.targetD pi' f)).1 := rfl

omit [Algebra A A'] [Algebra A B'] [IsScalarTower A B B'] [IsScalarTower A A' B']
  [SMulCommClass A' B B'] in
/-- On the image of `B` the base-change component of the differential is the base change of the
differential of `B`: `d₁(b) = 1 ⊗ d b`. -/
public theorem dOne_algebraMap (dec : DzDecomposition pi' psi z)
    (hpsi : ∀ b : B, psi (pi (KaehlerDifferential.D A B b)) =
      pi' (KaehlerDifferential.D A' B' (algebraMap B B' b)))
    (b : B) :
    dec.dOne (algebraMap B B' b) = (1 : B') ⊗ₜ[B] SourceDeRham.targetD pi b := by
  have h : SourceDeRham.targetD pi' (algebraMap B B' b) =
      psi (pi (KaehlerDifferential.D A B b)) := (hpsi b).symm
  rw [dec.dOne_eq, h, dec.equiv_symm_psi, targetD_apply]

omit [SMulCommClass A' B B'] in
/-- The base-change component of the differential is additive. -/
public theorem dOne_add (dec : DzDecomposition pi' psi z) (f g : B') :
    dec.dOne (f + g) = dec.dOne f + dec.dOne g := by
  rw [dec.dOne_eq, dec.dOne_eq, dec.dOne_eq, targetD_add, map_add, Prod.fst_add]

omit [SMulCommClass A' B B'] in
/-- The base-change component of the differential turns a difference into a difference. -/
public theorem dOne_sub (dec : DzDecomposition pi' psi z) (f g : B') :
    dec.dOne (f - g) = dec.dOne f - dec.dOne g := by
  rw [dec.dOne_eq, dec.dOne_eq, dec.dOne_eq, targetD_sub, map_sub, Prod.fst_sub]

omit [Algebra A A'] [Algebra A B'] [IsScalarTower A A' B'] [SMulCommClass A' B B'] in
/-- **The twisted Leibniz rule.**  The base-change component of the differential satisfies
`d₁(b f) = b d₁(f) + f ⊗ d b` for `b ∈ B` and `f ∈ B'`.  The correction term is the reason `d₁`
is merely additive and not `B`-linear. -/
public theorem dOne_smul (dec : DzDecomposition pi' psi z)
    (hpsi : ∀ b : B, psi (pi (KaehlerDifferential.D A B b)) =
      pi' (KaehlerDifferential.D A' B' (algebraMap B B' b)))
    (b : B) (f : B') :
    dec.dOne (b • f) = b • dec.dOne f + f ⊗ₜ[B] SourceDeRham.targetD pi b := by
  rw [dec.dOne_eq, Algebra.smul_def, targetD_leibniz, map_add, Prod.fst_add, map_smul, map_smul,
    Prod.smul_fst, Prod.smul_fst, ← dec.dOne_eq, ← dec.dOne_eq, dec.dOne_algebraMap hpsi,
    IsScalarTower.algebraMap_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

omit [SMulCommClass A' B B'] in
/-- The Leibniz rule for `∂_z`: the decomposition is `B'`-linear, so the coefficient of `dz`
inherits the Leibniz rule of the differential. -/
public theorem partialZ_mul (dec : DzDecomposition pi' psi z) (f g : B') :
    dec.partialZ (f * g) = f * dec.partialZ g + g * dec.partialZ f := by
  change (dec.equiv.symm (SourceDeRham.targetD pi' (f * g))).2 = _
  rw [targetD_leibniz, map_add, Prod.snd_add, map_smul, map_smul, Prod.smul_snd, Prod.smul_snd,
    smul_eq_mul, smul_eq_mul]
  rfl

omit [SMulCommClass A' B B'] in
/-- The Leibniz rule for `d₁`: the decomposition is `B'`-linear, so the base-change component
inherits the Leibniz rule of the differential. -/
public theorem dOne_mul (dec : DzDecomposition pi' psi z) (f g : B') :
    dec.dOne (f * g) = f • dec.dOne g + g • dec.dOne f := by
  change (dec.equiv.symm (SourceDeRham.targetD pi' (f * g))).1 = _
  rw [targetD_leibniz, map_add, Prod.fst_add, map_smul, map_smul, Prod.smul_fst, Prod.smul_fst]
  rfl

omit [SMulCommClass A' B B'] in
/-- The differential of `z` is `dz`: it sits in the free summand with coefficient `1`. -/
public theorem equiv_symm_targetD_self (dec : DzDecomposition pi' psi z) :
    dec.equiv.symm (SourceDeRham.targetD pi' z) = (0, 1) := by
  have h := dec.equiv_dz 1
  rw [one_smul] at h
  rw [← h, LinearEquiv.symm_apply_apply]

omit [SMulCommClass A' B B'] in
/-- `∂_z(z) = 1`. -/
public theorem partialZ_self (dec : DzDecomposition pi' psi z) : dec.partialZ z = 1 :=
  congrArg Prod.snd dec.equiv_symm_targetD_self

omit [SMulCommClass A' B B'] in
/-- `d₁(z) = 0`. -/
public theorem dOne_self (dec : DzDecomposition pi' psi z) : dec.dOne z = 0 :=
  congrArg Prod.fst dec.equiv_symm_targetD_self

omit [SMulCommClass A' B B'] in
/-- `∂_z(1) = 0`. -/
public theorem partialZ_one (dec : DzDecomposition pi' psi z) : dec.partialZ (1 : B') = 0 := by
  change (dec.equiv.symm (SourceDeRham.targetD pi' 1)).2 = 0
  rw [targetD_one, map_zero]
  rfl

omit [SMulCommClass A' B B'] in
/-- `d₁(1) = 0`. -/
public theorem dOne_one (dec : DzDecomposition pi' psi z) : dec.dOne (1 : B') = 0 := by
  change (dec.equiv.symm (SourceDeRham.targetD pi' 1)).1 = 0
  rw [targetD_one, map_zero]
  rfl

omit [SMulCommClass A' B B'] in
/-- `∂_z(z^{i+1}) = (i + 1) z^i`, by induction from the Leibniz rule and `∂_z(z) = 1`. -/
public theorem partialZ_pow_succ (dec : DzDecomposition pi' psi z) (i : ℕ) :
    dec.partialZ (z ^ (i + 1)) = ((i + 1 : ℕ) : B') * z ^ i := by
  induction i with
  | zero => rw [pow_one, dec.partialZ_self, pow_zero, Nat.cast_one, mul_one]
  | succ k ih =>
    rw [pow_succ, dec.partialZ_mul, ih, dec.partialZ_self, mul_one]
    push_cast
    ring

omit [SMulCommClass A' B B'] in
/-- `d₁(z^i) = 0`, by induction from the Leibniz rule and `d₁(z) = 0`. -/
public theorem dOne_pow (dec : DzDecomposition pi' psi z) (i : ℕ) :
    dec.dOne (z ^ i) = 0 := by
  induction i with
  | zero => rw [pow_zero, dec.dOne_one]
  | succ k ih => rw [pow_succ, dec.dOne_mul, ih, dec.dOne_self, smul_zero, smul_zero, add_zero]

end DzDecomposition

end PartialZ

end Crystalline

end

end
