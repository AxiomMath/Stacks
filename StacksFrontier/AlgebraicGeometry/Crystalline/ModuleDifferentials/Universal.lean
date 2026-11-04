module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRham

/-!
# The universal divided power derivation

Let `A` be a commutative ring and let `(B, J, δ)` be a divided power ring which is an `A`-algebra.
The module `Ω_{B/A, δ}` of divided power differentials of `B` over `A` is the quotient of the
Kähler differentials `Ω_{B/A}` by the relations `d(δ_{n+1} x) = δ_n x · dx` for `x ∈ J`. Composing
the universal derivation of `B` with that quotient map therefore gives a divided power derivation
of `B` into `Ω_{B/A, δ}`, and it is the universal one: it sends `b` to the universal divided power
differential `db`.

## Main definitions

* `Crystalline.universalDividedPowerDerivation` — the universal divided power derivation of a
  divided power ring into its module of divided power differentials.

## Implementation notes

A `Crystalline.DividedPowerDerivation` carries a derivation over `ℤ` together with the two extra
conditions, so the underlying derivation is assembled as a `ℤ`-derivation from the additive map
`Ω_{B/A} ↠ Ω_{B/A, δ} ∘ d`. The Leibniz rule is inherited from the Kähler differentials, the
vanishing on the image of `A` from the corresponding property of `d`, and the divided power
condition is the defining relation of `Ω_{B/A, δ}` itself.
## References

* [Stacks Project, Tag 07HR](https://stacks.math.columbia.edu/tag/07HR)
-/

@[expose] public section

namespace Crystalline

universe u v

/-- The universal divided power derivation of a divided power ring into its module of divided
power differentials: it sends an element to its universal divided power differential. -/
public noncomputable def universalDividedPowerDerivation
    {A : Type u} [CommRing A] {B : DividedPowerRing.{v}} [Algebra A B] :
    DividedPowerDerivation A B (algebraMap A B)
      (dividedPowerDifferentials (A := A) B.dividedPowers) := by
  let π := (dividedPowerDifferentialRelations (A := A) B.dividedPowers).mkQ
  let κ := KaehlerDifferential.D A B
  let L : B →ₗ[ℤ] dividedPowerDifferentials (A := A) B.dividedPowers :=
    (π.toAddMonoidHom.comp κ.toAddMonoidHom).toIntLinearMap
  let d : Derivation ℤ B (dividedPowerDifferentials (A := A) B.dividedPowers) :=
    Derivation.mk' L (by
      intro x y
      change π (κ (x * y)) = x • π (κ y) + y • π (κ x)
      rw [κ.leibniz]
      simp)
  refine ⟨d, ?_, ?_⟩
  · intro a
    change π (κ (algebraMap A B a)) = 0
    rw [κ.map_algebraMap]
    simp
  · intro n hn x hx
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    change dividedPowerDifferential (A := A) B.dividedPowers
        (B.dividedPowers.dpow (k + 1) x) =
      B.dividedPowers.dpow k x • dividedPowerDifferential (A := A) B.dividedPowers x
    exact dividedPowerDifferential_dpow (A := A) B.dividedPowers ⟨x, hx⟩ k

end Crystalline

end
