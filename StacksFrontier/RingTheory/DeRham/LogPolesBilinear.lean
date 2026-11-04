module

public import StacksFrontier.AlgebraicGeometry.IdealPowerSections.Basic
public import StacksFrontier.RingTheory.DeRham.LogPolesDifferential

/-!
# The pairing that carries the differential of the forms with log poles

Let `A → R` be a ring map and let `J ⊆ R` be an ideal cutting out a divisor `Y ⊆ X = Spec R`.
In the equation-free presentation `AlgebraicGeometry.Scheme.Hom.logPolesForms` of
[Stacks, Tag 0FMW] a log form of degree `p` is an `R`-linear map `φ : J → 𝒦^p`; where `J = (t)`
it is the form `φ(t)/t`, and its differential is the `ξ` solving `t · ξ = t · dζ − dt ∧ ζ` with
`ζ = φ(t)` (`Stacks.LogPoles.exists_logDifferential`).

That description still names an equation. This file removes the equation. The right-hand side
`t · dζ − dt ∧ ζ` is the diagonal value of

`B(a, b) = a · d(φ(b)) − db ∧ φ(a)`,

and `B` is **`R`-bilinear and symmetric on `J × J`** — so it is a map `J ⊗ J → Ω^{p+1}`, defined
with no choice of generator. Bilinearity is not formal: differentiating is not `R`-linear, and the
Leibniz defect in the second variable is

`B(a, c · b) − c · B(a, b) = dc ∧ (a · φ(b) − b · φ(a))`,

which vanishes because `a · φ(b) = φ(a b) = b · φ(a)`
(`Stacks.AlgebraicGeometry.IdealPowerSections.smul_apply_comm`). Symmetry is the same identity
differentiated. So the whole differential of `Ω^•(log Y)` reduces to dividing `B` by one copy of
`J`: the value at `b` of the differential of `φ` is the unique `ξ` with `a · ξ = B(a, b)` for all
`a`, unique because multiplication by a local equation is injective on the forms, which is
condition (2) of [Stacks, Tag 0FMV].

## Main definitions

* `Stacks.LogPoles.logPairingFun`: the pairing `B(a, b) = a · d(φ(b)) − db ∧ φ(a)`.
* `Stacks.LogPoles.logPairing`: the same, as an `R`-bilinear map `J →ₗ J →ₗ Ω^{p+1}`.

## Main results

* `Stacks.LogPoles.logPairingFun_add_left`, `_smul_left`, `_add_right`, `_smul_right`:
  **the pairing is `R`-bilinear**, the last of these being the one that uses that `φ` is defined
  on an ideal.
* `Stacks.LogPoles.logPairingFun_symm`: **the pairing is symmetric.**
* `Stacks.LogPoles.exists_smul_eq_logPairing_self`: on the diagonal at a generator the pairing is
  `t` times a form that again restricts to zero on the divisor — the differential, obtained from
  `Stacks.LogPoles.exists_logDifferential`.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW), whose complex this is
  the differential of
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV), whose condition (2)
  makes the division by `J` unique
-/

@[expose] public noncomputable section

open KaehlerDifferential Stacks.AlgebraicGeometry.IdealPowerSections

universe u

namespace Stacks.LogPoles

variable (A : Type u) {R : Type u} [CommRing A] [CommRing R] [Algebra A R] {J : Ideal R} {p : ℕ}

/-- **The pairing carrying the differential of a log form.** For an `R`-linear
`φ : J → ⋀^p Ω[R⁄A]` and `a`, `b` in `J`,

`B(a, b) = a · d(φ(b)) − db ∧ φ(a)`.

Where `J = (t)` its diagonal value `B(t, t) = t · d(φ(t)) − dt ∧ φ(t)` is `t` times the value at
`t` of the differential of the log form `φ(t)/t`. -/
def logPairingFun (φ : ↥J →ₗ[R] ↥(⋀[R]^p (Ω[R⁄A]))) (a b : ↥J) :
    ↥(⋀[R]^(p + 1) (Ω[R⁄A])) :=
  (a : R) • deRhamDifferential (A := A) p (φ b) -
    exteriorPower.wedgeLeft (KaehlerDifferential.D A R (b : R)) p (φ a)

variable {A}

/-- The pairing is additive in its first variable. -/
theorem logPairingFun_add_left (φ : ↥J →ₗ[R] ↥(⋀[R]^p (Ω[R⁄A]))) (a a' b : ↥J) :
    logPairingFun A φ (a + a') b = logPairingFun A φ a b + logPairingFun A φ a' b := by
  simp only [logPairingFun, Submodule.coe_add, add_smul, map_add]
  abel

/-- The pairing is homogeneous in its first variable. -/
theorem logPairingFun_smul_left (φ : ↥J →ₗ[R] ↥(⋀[R]^p (Ω[R⁄A]))) (c : R) (a b : ↥J) :
    logPairingFun A φ (c • a) b = c • logPairingFun A φ a b := by
  simp only [logPairingFun, Submodule.coe_smul, smul_eq_mul, map_smul, smul_sub, smul_smul]

/-- The pairing is additive in its second variable. -/
theorem logPairingFun_add_right (φ : ↥J →ₗ[R] ↥(⋀[R]^p (Ω[R⁄A]))) (a b b' : ↥J) :
    logPairingFun A φ a (b + b') = logPairingFun A φ a b + logPairingFun A φ a b' := by
  simp only [logPairingFun, Submodule.coe_add, map_add, smul_add, exteriorPower.wedgeLeft_add,
    LinearMap.add_apply]
  abel

/-- **The pairing is homogeneous in its second variable.** -/
theorem logPairingFun_smul_right (φ : ↥J →ₗ[R] ↥(⋀[R]^p (Ω[R⁄A]))) (c : R) (a b : ↥J) :
    logPairingFun A φ a (c • b) = c • logPairingFun A φ a b := by
  have hcomm : (a : R) • φ b = (b : R) • φ a := smul_apply_comm φ b.2 a.2
  have hkey : (a : R) • exteriorPower.wedgeLeft (KaehlerDifferential.D A R c) p (φ b) =
      (b : R) • exteriorPower.wedgeLeft (KaehlerDifferential.D A R c) p (φ a) := by
    simpa only [map_smul] using
      congrArg (exteriorPower.wedgeLeft (KaehlerDifferential.D A R c) p) hcomm
  simp only [logPairingFun, Submodule.coe_smul, smul_eq_mul, map_smul, deRhamDifferential_smul,
    Derivation.leibniz, exteriorPower.wedgeLeft_add, LinearMap.add_apply,
    exteriorPower.wedgeLeft_smul, LinearMap.smul_apply, smul_add, smul_sub, smul_smul,
    mul_comm (a : R) c]
  rw [hkey]
  abel

/-- **The pairing is symmetric**: `B(a, b) = B(b, a)`. -/
theorem logPairingFun_symm (φ : ↥J →ₗ[R] ↥(⋀[R]^p (Ω[R⁄A]))) (a b : ↥J) :
    logPairingFun A φ a b = logPairingFun A φ b a := by
  have hcomm : (a : R) • φ b = (b : R) • φ a := smul_apply_comm φ b.2 a.2
  have hd := congrArg (deRhamDifferential (A := A) p) hcomm
  rw [deRhamDifferential_smul, deRhamDifferential_smul] at hd
  simp only [logPairingFun]
  rw [sub_eq_sub_iff_add_eq_add]
  exact (add_comm _ _).trans (hd.trans (add_comm _ _))

/-- **The pairing, as an `R`-bilinear map** `J →ₗ[R] J →ₗ[R] ⋀^(p+1) Ω[R⁄A]`, sending `a`, `b`
to `B(a, b) = a · d(φ(b)) − db ∧ φ(a)`. -/
def logPairing (φ : ↥J →ₗ[R] ↥(⋀[R]^p (Ω[R⁄A]))) :
    ↥J →ₗ[R] ↥J →ₗ[R] ↥(⋀[R]^(p + 1) (Ω[R⁄A])) :=
  LinearMap.mk₂ R (logPairingFun A φ) (logPairingFun_add_left φ) (logPairingFun_smul_left φ)
    (logPairingFun_add_right φ) (logPairingFun_smul_right φ)

/-- The bilinear map `Stacks.LogPoles.logPairing φ` evaluates at `a`, `b` to
`Stacks.LogPoles.logPairingFun A φ a b`. -/
@[simp]
theorem logPairing_apply (φ : ↥J →ₗ[R] ↥(⋀[R]^p (Ω[R⁄A]))) (a b : ↥J) :
    logPairing φ a b = logPairingFun A φ a b := rfl

/-- **The diagonal of the pairing at a generator is `t` times the differential.** If `J = (t)`
and the log form `φ` takes its value at `t` among the forms restricting to zero on the divisor,
then `B(t, t) = t · ξ` for a form `ξ` of one degree higher that again restricts to zero. That
`ξ` is the value at `t` of the differential of `φ`, and it is unique by
`Stacks.LogPoles.existsUnique_logDifferential`. -/
theorem exists_smul_eq_logPairing_self (t : R)
    (φ : ↥(Ideal.span {t}) →ₗ[R] ↥(⋀[R]^p (Ω[R⁄A])))
    (hφ : KaehlerDifferential.mapExteriorPower A R (R ⧸ Ideal.span {t}) p
      (φ ⟨t, Ideal.mem_span_singleton_self t⟩) = 0) :
    ∃ ξ : ⋀[R]^(p + 1) (Ω[R⁄A]),
      KaehlerDifferential.mapExteriorPower A R (R ⧸ Ideal.span {t}) (p + 1) ξ = 0 ∧
        t • ξ = logPairingFun A φ ⟨t, Ideal.mem_span_singleton_self t⟩
          ⟨t, Ideal.mem_span_singleton_self t⟩ :=
  exists_logDifferential t p hφ

end Stacks.LogPoles

end
