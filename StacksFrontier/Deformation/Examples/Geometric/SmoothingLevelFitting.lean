module

public import StacksFrontier.Deformation.Examples.Geometric.SmoothingFitting
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingFormalObject

/-!
# The Fitting ideal of the differentials of a level of a local smoothing

Let `B` be a flat `k⟦t⟧`-algebra, essentially of finite type, such that `t^N` lies in the `d`-th
Fitting ideal of `Ω_{B/k⟦t⟧}` for some `d ≤ 1`. Then for every `n ≥ N` the element `t^n` lies in
the first Fitting ideal of `Ω_{(B/𝔪^{n+1}B)/(k⟦t⟧/𝔪^{n+1})}`. This is the step in the proof of
[Stacks, Tag 0E7Y] which reads "since taking Fitting ideals commutes with base change and since
`n - 1 ≥ n_i` we see that `t^{n-1}` is in the Fitting ideal of this module over `B_i/t^nB_i`".

## Main results

* `Deformation.Examples.Smoothing.algebraMap_pow_X_mem_fittingIdeal_levelFiber`.

## References

* [Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
* [Stacks Project, Tag 07ZA](https://stacks.math.columbia.edu/tag/07ZA)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Deformation.Examples.Smoothing

variable (k : Type u) [Field k] (B : Type u) [CommRing B] [Algebra (PowerSeries k) B]

/-- The reduction of `B` modulo the extension of an ideal of the base is the pushout of the base
change to the quotient of the base. -/
theorem isPushout_quotient_map (I : Ideal (PowerSeries k)) :
    Algebra.IsPushout (PowerSeries k) (PowerSeries k ⧸ I) B
      (B ⧸ I.map (algebraMap (PowerSeries k) B)) := by
  refine Algebra.IsPushout.symm ⟨IsBaseChange.of_equiv
    (Ideal.quotMapEquivTensorQuot B (I := I)).symm ?_⟩
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [LinearEquiv.symm_apply_eq]
  simp [Ideal.quotMapEquivTensorQuot, LinearEquiv.eq_symm_apply, Algebra.smul_def]

/-- **Fitting ideals of a level of a local smoothing.** If `t^N` lies in the `d`-th Fitting ideal
of `Ω_{B/k⟦t⟧}` with `d ≤ 1`, then for `n ≥ N` the image of `t^n` in `B / 𝔪^{n+1} B` lies in the
first Fitting ideal of its differentials over `k⟦t⟧ / 𝔪^{n+1}`. -/
theorem algebraMap_pow_X_mem_fittingIdeal_levelFiber [Module.Finite B Ω[B⁄PowerSeries k]]
    {N d : ℕ} (hd : d ≤ 1)
    (hN : algebraMap (PowerSeries k) B (PowerSeries.X ^ N) ∈
      fittingIdeal (R := B) (M := Ω[B⁄PowerSeries k]) (d : ℤ))
    {n : ℕ} (hn : N ≤ n) :
    letI : Module.Finite (levelFiber k B n)
        Ω[levelFiber k B n⁄(PowerSeries k ⧸ truncIdeal k n)] :=
      haveI := isPushout_quotient_map k B (truncIdeal k n)
      Module.Finite.equiv (KaehlerDifferential.tensorKaehlerEquiv (PowerSeries k)
        (PowerSeries k ⧸ truncIdeal k n) B (levelFiber k B n))
    algebraMap (PowerSeries k ⧸ truncIdeal k n) (levelFiber k B n)
        (Ideal.Quotient.mk _ (PowerSeries.X ^ n)) ∈
      fittingIdeal (R := levelFiber k B n)
        (M := Ω[levelFiber k B n⁄(PowerSeries k ⧸ truncIdeal k n)]) ((1 : ℕ) : ℤ) := by
  have := isPushout_quotient_map k B (truncIdeal k n)
  let : Module.Finite (levelFiber k B n)
      Ω[levelFiber k B n⁄(PowerSeries k ⧸ truncIdeal k n)] :=
    Module.Finite.equiv (KaehlerDifferential.tensorKaehlerEquiv (PowerSeries k)
      (PowerSeries k ⧸ truncIdeal k n) B (levelFiber k B n))
  have hbc := fittingIdeal_kaehler_of_isPushout (R := PowerSeries k)
    (R' := PowerSeries k ⧸ truncIdeal k n) (C := B) (C' := levelFiber k B n) d
  have hmono : fittingIdeal (R := levelFiber k B n)
      (M := Ω[levelFiber k B n⁄(PowerSeries k ⧸ truncIdeal k n)])
      (d : ℤ) ≤ fittingIdeal (R := levelFiber k B n)
        (M := Ω[levelFiber k B n⁄(PowerSeries k ⧸ truncIdeal k n)]) ((1 : ℕ) : ℤ) :=
    Stacks.Fitting.fittingIdeal_monotone (by exact_mod_cast hd)
  refine hmono ?_
  rw [hbc]
  have hX : algebraMap (PowerSeries k ⧸ truncIdeal k n) (levelFiber k B n)
      (Ideal.Quotient.mk _ (PowerSeries.X ^ n)) =
      algebraMap B (levelFiber k B n) (algebraMap (PowerSeries k) B (PowerSeries.X ^ N)) *
        algebraMap B (levelFiber k B n)
          (algebraMap (PowerSeries k) B (PowerSeries.X ^ (n - N))) := by
    rw [← map_mul, ← map_mul, ← pow_add, Nat.add_sub_cancel' hn]
    rfl
  rw [hX]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hN)

end Deformation.Examples.Smoothing

end
