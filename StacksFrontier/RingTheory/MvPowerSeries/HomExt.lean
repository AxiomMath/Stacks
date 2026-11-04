module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Power series homomorphisms are determined by the constants and the variables

A ring homomorphism out of a formal power series ring — in one variable, or in finitely many —
into a ring separated for the adic topology of an ideal `I` is determined by what it does to the
constants and to the variables, provided the variables land in `I`.

## Main results

* `powerSeries_hom_ext`: the one-variable statement.
* `mvPowerSeries_hom_ext`: the statement for `MvPowerSeries (Fin n)`, by induction on `n` through
  `MvPowerSeries.finSuccEquiv`.

## Implementation notes

Separatedness is `IsHausdorff I S`, and the proof shows that the difference of the two maps lies
in every power of `I`. The hypothesis that the variables land in `I` is what makes the inductive
step gain one power of `I`, so it cannot be dropped: a homomorphism out of a power series ring is
not determined by the constants and the variables alone.
-/

@[expose] public section

/-- Maps out of a power series ring into a separated ring are determined by the constants
and variable, provided the variable maps into the ideal of separation. -/
theorem powerSeries_hom_ext {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal S) [IsHausdorff I S] (f g : PowerSeries R →+* S)
    (hC : ∀ r, f (PowerSeries.C r) = g (PowerSeries.C r))
    (hX : f PowerSeries.X = g PowerSeries.X) (hfX : f PowerSeries.X ∈ I) : f = g := by
  have h : ∀ n : ℕ, ∀ a, f a - g a ∈ I ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro a
      obtain ⟨b, hb⟩ : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a) := by
        rw [PowerSeries.X_dvd_iff]; simp
      have ha : a = PowerSeries.C (PowerSeries.constantCoeff a) + PowerSeries.X * b := by
        rw [← hb]; ring
      rw [ha, map_add, map_add, map_mul, map_mul, hC, ← hX]
      have he : g (PowerSeries.C (PowerSeries.constantCoeff a)) + f PowerSeries.X * f b -
          (g (PowerSeries.C (PowerSeries.constantCoeff a)) + f PowerSeries.X * g b) =
            f PowerSeries.X * (f b - g b) := by ring
      rw [he, pow_succ']
      exact Ideal.mul_mem_mul hfX (ih b)
  ext a
  exact sub_eq_zero.mp <| IsHausdorff.haus (I := I) (M := S) inferInstance (f a - g a)
    (by simpa [SModEq.sub_mem] using h · a)

/-- Multivariate power series maps into a separated ring are determined by constants and
variables when each variable maps into the ideal of separation. -/
theorem mvPowerSeries_hom_ext {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal S) [IsHausdorff I S] (n : ℕ)
    (f g : MvPowerSeries (Fin n) R →+* S)
    (hC : ∀ r, f (MvPowerSeries.C r) = g (MvPowerSeries.C r))
    (hX : ∀ i, f (MvPowerSeries.X i) = g (MvPowerSeries.X i))
    (hfX : ∀ i, f (MvPowerSeries.X i) ∈ I) : f = g := by
  induction n with
  | zero =>
    ext a
    have ha : a = MvPowerSeries.C (MvPowerSeries.constantCoeff a) :=
      ((MvPowerSeries.isEmptyEquiv (Fin 0) R).symm_apply_apply a).symm
    rw [ha, hC]
  | succ n ih =>
    let e := MvPowerSeries.finSuccEquiv R n
    have h := powerSeries_hom_ext I (f.comp e.symm.toRingHom) (g.comp e.symm.toRingHom)
      (fun a => ?_) ?_ ?_
    · ext a
      have := DFunLike.congr_fun h (e a)
      simpa using this
    · have hinner := ih
        ((f.comp e.symm.toRingHom).comp PowerSeries.C)
        ((g.comp e.symm.toRingHom).comp PowerSeries.C)
        (fun r => ?_) (fun i => ?_) (fun i => ?_)
      · exact DFunLike.congr_fun hinner a
      · simpa [e, ← MvPowerSeries.finSuccEquiv_C] using hC r
      · simpa [e, ← MvPowerSeries.finSuccEquiv_X_succ] using hX i.succ
      · simpa [e, ← MvPowerSeries.finSuccEquiv_X_succ] using hfX i.succ
    · simpa [e, ← MvPowerSeries.finSuccEquiv_X_zero] using hX 0
    · simpa [e, ← MvPowerSeries.finSuccEquiv_X_zero] using hfX 0
