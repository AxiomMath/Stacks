module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Fraction
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishing

/-!
# The tame symbol against a unit of the local ring, on the total ring of fractions

Let `A` be a one-dimensional Noetherian local ring with total ring of fractions `Q`.  Stacks 0EAN
says `∂_A(u, b) = ū^{ord_A(b)}` for a unit `u ∈ A^*` and a nonzerodivisor `b`.  By
bimultiplicativity this extends to every `g ∈ Q(A)^*`:

`∂_A(u, g) = ū^{ord_A(g)}`,

with `ord_A(g) = length(A/c) - length(A/d)` for `g = c/d`.  Combined with skew-symmetry this is
the effect of changing the arguments of the tame symbol by units of `A`:

`∂_A(f λ, g μ) = ∂_A(f, g) · μ̄^{-ord_A(f)} · λ̄^{ord_A(g)}`,

which is how the key formula, Stacks 0EQV, absorbs a change of the chosen local generators.

## Main results

* `Stacks.Chow.RegularTameSymbol.extend_unit_left`: `∂_A(u, g) = ū^{ord_A(g)}`.
* `Stacks.Chow.RegularTameSymbol.extend_mul_units`: the change of both arguments by units.

## References

* [Stacks Project, Tag 0EAN](https://stacks.math.columbia.edu/tag/0EAN)
* [Stacks Project, Tag 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Chow

namespace RegularTameSymbol

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  (symb : RegularTameSymbol A)
  (Q : Type v) [CommRing Q] [Algebra A Q] [IsFractionRing A Q]

/-- **Stacks 0EAN on `Q(A)^*`.**  For a unit `u` of `A` and a unit `g` of the total ring of
fractions, `∂_A(u, g) = ū^{ord_A(g)}`. -/
theorem extend_unit_left (w : Aˣ) (g : Qˣ) :
    (symb.extend Q) (Units.map (algebraMap A Q).toMonoidHom w) g =
      Units.map (residue A).toMonoidHom w ^ Ring.ordTotalFracInt A (g : Q) g.isUnit := by
  have hwz : (w : A) ∈ nonZeroDivisors A := w.isUnit.mem_nonZeroDivisors
  set c := fractionNum (A := A) Q g
  set d := fractionDen (A := A) Q g
  have hg := regularFractionUnit_fractionNum_div_fractionDen (A := A) Q g
  have hW : Units.map (algebraMap A Q).toMonoidHom w =
      regularFractionUnit (Q := Q) ⟨(w : A), hwz⟩ *
        (regularFractionUnit (Q := Q) (1 : nonZeroDivisors A))⁻¹ := by
    rw [map_one, inv_one, mul_one]
    exact Units.ext rfl
  rw [symb.extend_eq Q ⟨(w : A), hwz⟩ 1 c d hW hg,
    symb.unit_left ⟨(w : A), hwz⟩ c w rfl, symb.unit_left ⟨(w : A), hwz⟩ d w rfl]
  have h1 : ∀ x : nonZeroDivisors A, symb 1 x = 1 := fun x => by
    rw [symb.unit_left 1 x 1 (by simp)]
    simp
  rw [h1, h1, inv_one, mul_one, mul_one]
  have hord : Ring.ordTotalFracInt A (g : Q) g.isUnit =
      ((Ring.ord A (c : A)).toNat : ℤ) - ((Ring.ord A (d : A)).toNat : ℤ) := by
    have hgv : (g : Q) = IsLocalization.mk' Q (c : A) d := by
      have hmul : g * regularFractionUnit (Q := Q) d = regularFractionUnit c := by
        rw [hg, inv_mul_cancel_right]
      rw [IsLocalization.eq_mk'_iff_mul_eq]
      exact congrArg Units.val hmul
    rw [Ring.ordTotalFracInt_congr A g.isUnit (hgv ▸ g.isUnit) hgv, Ring.ordTotalFracInt_mk']
  rw [hord, zpow_sub, zpow_natCast, zpow_natCast]

/-- **The change of the arguments of the tame symbol by units of `A`.**
`∂_A(f λ, g μ) = ∂_A(f, g) · μ̄^{-ord_A(f)} · λ̄^{ord_A(g)}` for `f, g ∈ Q(A)^*` and
`λ, μ ∈ A^*`. -/
theorem extend_mul_units (f g : Qˣ) (l m : Aˣ) :
    (symb.extend Q) (f * Units.map (algebraMap A Q).toMonoidHom l)
        (g * Units.map (algebraMap A Q).toMonoidHom m) =
      (symb.extend Q) f g *
        (Units.map (residue A).toMonoidHom m ^ Ring.ordTotalFracInt A (f : Q) f.isUnit)⁻¹ *
        Units.map (residue A).toMonoidHom l ^ Ring.ordTotalFracInt A (g : Q) g.isUnit := by
  set T := symb.extend Q
  have hll : T (Units.map (algebraMap A Q).toMonoidHom l)
      (Units.map (algebraMap A Q).toMonoidHom m) = 1 := by
    rw [symb.extend_unit_left Q l]
    have h0 : Ring.ordTotalFracInt A ((Units.map (algebraMap A Q).toMonoidHom m : Qˣ) : Q)
        (Units.isUnit _) = 0 := by
      have hm : (m : A) ∈ nonZeroDivisors A := m.isUnit.mem_nonZeroDivisors
      rw [Ring.ordTotalFracInt_congr A (Units.isUnit _) (IsLocalization.map_units Q ⟨(m : A), hm⟩)
          (rfl : ((Units.map (algebraMap A Q).toMonoidHom m : Qˣ) : Q) = algebraMap A Q m),
        Ring.ordTotalFracInt_algebraMap A (m : A) hm]
      simp
    rw [h0, zpow_zero]
  rw [T.map_mul_left, T.map_mul_right, T.map_mul_right, hll, mul_one,
    T.symm_eq_inv (Units.map (algebraMap A Q).toMonoidHom m) f, symb.extend_unit_left Q m,
    symb.extend_unit_left Q l, mul_assoc]

end RegularTameSymbol

end Stacks.Chow

end
