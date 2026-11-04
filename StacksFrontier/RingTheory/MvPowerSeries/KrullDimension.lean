module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksFrontier.RingTheory.MvPowerSeries.RegularLocal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Krull dimension of a power series ring over a Noetherian local ring

For a Noetherian local ring `R`, adjoining `n` formal variables raises the Krull dimension by
exactly `n`: `dim R[[x_1, …, x_n]] = dim R + n`.

## Main results

* `MvPowerSeries.ringKrullDim_fin_eq_add`: the dimension formula.

## Implementation notes

The lower bound is `MvPowerSeries.ringKrullDim_add_le_mvPowerSeries`, which holds over any ring.
The upper bound is Krull's height theorem in the form
`ringKrullDim_le_ringKrullDim_quotient_add_card`: the `n` variables lie in the maximal ideal of
the local ring `R[[x_1, …, x_n]]`, hence in its Jacobson radical, and the quotient by the ideal
they generate is `R`, through the constant coefficient.
-/

open IsLocalRing

@[expose] public section

namespace MvPowerSeries

/-- **The dimension of a power series ring.** Over a Noetherian local ring `R`, adjoining `n`
formal variables raises the Krull dimension by exactly `n`. -/
@[ega "0 21.9.3" "partial"]
public theorem ringKrullDim_fin_eq_add (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (n : ℕ) :
    ringKrullDim (MvPowerSeries (Fin n) R) = ringKrullDim R + n := by
  classical
  refine le_antisymm ?_ (ringKrullDim_add_le_mvPowerSeries R n)
  let s : Finset (MvPowerSeries (Fin n) R) := Finset.univ.image X
  have hs : (s : Set (MvPowerSeries (Fin n) R)) ⊆ Ring.jacobson (MvPowerSeries (Fin n) R) := by
    intro x hx
    simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [SetLike.mem_coe, IsLocalRing.ringJacobson_eq_maximalIdeal, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, isUnit_iff_constantCoeff]
    simp
  have hspan : Ideal.span (s : Set (MvPowerSeries (Fin n) R)) =
      RingHom.ker (constantCoeff : MvPowerSeries (Fin n) R →+* R) := by
    rw [← span_X_eq_ker_constantCoeff]
    simp [s]
  have hsurj : Function.Surjective (constantCoeff : MvPowerSeries (Fin n) R →+* R) :=
    fun a => ⟨C a, by simp⟩
  have hquot : ringKrullDim (MvPowerSeries (Fin n) R ⧸
      Ideal.span (s : Set (MvPowerSeries (Fin n) R))) =
      ringKrullDim R := by
    rw [hspan]
    exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj)
  have hcard : s.card ≤ n := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := X))
  calc ringKrullDim (MvPowerSeries (Fin n) R)
      ≤ ringKrullDim (MvPowerSeries (Fin n) R ⧸
          Ideal.span (s : Set (MvPowerSeries (Fin n) R))) + s.card :=
        ringKrullDim_le_ringKrullDim_quotient_add_card s hs
    _ = ringKrullDim R + s.card := by rw [hquot]
    _ ≤ ringKrullDim R + n := by gcongr

end MvPowerSeries

end
