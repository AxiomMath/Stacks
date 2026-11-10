module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRham

/-!
# Derivations of a torsion free ring are divided power derivations

Let `A → B` be a ring map and let `(J, δ)` be a divided power ideal of `B`.  The module
`Ω¹_{B/A,δ}` of divided power differentials of [Stacks, Tag 07HZ] is the quotient of the Kähler
differentials `Ω[B⁄A]` by the relations `d(δ_{n+1}(z)) = δ_n(z) dz`, so a `B`-linear functional on
it is an `A`-derivation `∂ : B → B` which satisfies those relations.

**When `B` is torsion free as a `ℤ`-module every `A`-derivation satisfies them.**  Indeed
`(n+1)! δ_{n+1}(z) = z^{n+1}` and `n! δ_n(z) = z^n` by
`DividedPowers.factorial_mul_dpow_eq_pow`, so

`(n+1)! ∂(δ_{n+1}(z)) = ∂(z^{n+1}) = (n+1) z^n ∂z = (n+1)! δ_n(z) ∂z`,

and the factorial cancels.  So no divided power compatibility has to be checked by hand: on a
torsion free ring the divided powers are themselves determined by the ambient ring
(`DividedPowers.instSubsingletonDividedPowers`), and so is their behaviour under a derivation.

## Main results

* `Crystalline.Derivation.apply_dpow_succ` — the divided power relation
  `∂(δ_{n+1}(z)) = δ_n(z) ∂z`, for every `A`-derivation `∂` of a `ℤ`-torsion free `B`.
* `Crystalline.liftDividedPowerDifferentials` — the induced `B`-linear functional
  `Ω¹_{B/A,δ} → B`, and `Crystalline.liftDividedPowerDifferentials_apply`, which says that it
  carries the universal divided power differential `d b` to `∂ b`.

## References

* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 07GM](https://stacks.math.columbia.edu/tag/07GM)
-/

@[expose] public noncomputable section

universe u v

namespace Crystalline

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] {J : Ideal B}
  (hJ : DividedPowers J) [Module.IsTorsionFree ℤ B]

/-- **Every derivation of a `ℤ`-torsion free ring is a divided power derivation.**  For an
`A`-derivation `∂` of `B` and an element `z` of a divided power ideal `(J, δ)` of `B` one has
`∂(δ_{n+1}(z)) = δ_n(z) ∂z`: multiplying by `(n+1)!` turns both sides into `(n+1) z^n ∂z`, by
`(n+1)! δ_{n+1}(z) = z^{n+1}` and `n! δ_n(z) = z^n`, and `(n+1)!` is a nonzerodivisor. -/
public theorem Derivation.apply_dpow_succ (d : Derivation A B B) {z : B} (hz : z ∈ J) (n : ℕ) :
    d (hJ.dpow (n + 1) z) = hJ.dpow n z * d z := by
  have hfac : ((n + 1).factorial : ℤ) ≠ 0 := by positivity
  apply smul_right_injective B hfac
  have h1 : ((n + 1).factorial : ℤ) • d (hJ.dpow (n + 1) z) = d (z ^ (n + 1)) := by
    rw [← map_zsmul, zsmul_eq_mul, Int.cast_natCast, hJ.factorial_mul_dpow_eq_pow hz]
  have h2 : ((n + 1).factorial : ℤ) • (hJ.dpow n z * d z) = ((n + 1 : ℕ) : B) * (z ^ n * d z) := by
    rw [zsmul_eq_mul, Int.cast_natCast, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one]
    rw [show ((n : B) + 1) * (n.factorial : B) * (hJ.dpow n z * d z) =
      ((n : B) + 1) * (((n.factorial : B) * hJ.dpow n z) * d z) by ring,
      hJ.factorial_mul_dpow_eq_pow hz]
  change ((n + 1).factorial : ℤ) • d (hJ.dpow (n + 1) z) =
    ((n + 1).factorial : ℤ) • (hJ.dpow n z * d z)
  rw [h1, h2, Derivation.leibniz_pow]
  simp only [Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul]

/-- The divided power relations of [Stacks, Tag 07HZ] are killed by the Kähler lift of any
`A`-derivation of a `ℤ`-torsion free ring, by `Crystalline.Derivation.apply_dpow_succ`. -/
public theorem dividedPowerDifferentialRelations_le_ker_liftKaehlerDifferential
    (d : Derivation A B B) :
    dividedPowerDifferentialRelations (A := A) hJ ≤
      LinearMap.ker (Derivation.liftKaehlerDifferential d) := by
  rw [dividedPowerDifferentialRelations, Submodule.span_le]
  rintro _ ⟨⟨z, n⟩, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, dividedPowerDifferentialRelation, map_sub,
    map_smul, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul, sub_eq_zero]
  exact Derivation.apply_dpow_succ hJ d z.2 n

/-- **The `B`-linear functional on `Ω¹_{B/A,δ}` attached to an `A`-derivation of a `ℤ`-torsion
free ring.**  The divided power differentials are the Kähler differentials modulo the divided
power relations, and a derivation of a torsion free ring kills those relations
automatically. -/
public def liftDividedPowerDifferentials (d : Derivation A B B) :
    dividedPowerDifferentials (A := A) hJ →ₗ[B] B :=
  (dividedPowerDifferentialRelations (A := A) hJ).liftQ
    (Derivation.liftKaehlerDifferential d)
    (dividedPowerDifferentialRelations_le_ker_liftKaehlerDifferential hJ d)

/-- The functional attached to a derivation carries the universal divided power differential
`d b` of [Stacks, Tag 07HZ] to `∂ b`. -/
@[simp]
public theorem liftDividedPowerDifferentials_apply (d : Derivation A B B) (b : B) :
    liftDividedPowerDifferentials hJ d (dividedPowerDifferential (A := A) hJ b) = d b :=
  Derivation.liftKaehlerDifferential_comp_D d b

end Crystalline

end
