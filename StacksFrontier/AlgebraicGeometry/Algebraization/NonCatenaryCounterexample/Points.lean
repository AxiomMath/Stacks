module

public import StacksFrontier.AlgebraicGeometry.Algebraization.NonCatenaryCounterexample.Situation

/-!
# Points of `U ∩ Y` in an algebraization situation, read as primes

For an algebraization situation, a prime of `A` outside `V(𝔞)` is the image of a point of `U`,
and a point `z` of `Y = Spec(A/I)` maps to the prime `z ∩ A`. For the counterexample to Stacks
0EJA this identifies the point `P` of `U ∩ Y` and reads the dimension of the closure of a point of
`U` as the coheight of its prime.

## Main results

* `Stacks.Algebraization.exists_underlyingPrime_eq` — primes outside `V(𝔞)` come from `U`.
* `Stacks.Algebraization.Yι_base_asIdeal` — `Yι` on points is contraction along `A → A/I`.
* `Stacks.Algebraization.height_U_ι_base_eq_coheight` — `dim({y}‾)` is the coheight of the prime.
-/

@[expose] public noncomputable section

open AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})

/-- A point of `X = Spec A` lies in `U` iff its prime does not contain `𝔞`. -/
private theorem mem_U_iff_not_le (x : S.X) :
    x ∈ (S.U : Set S.X) ↔ ¬ S.a ≤ (x : PrimeSpectrum S.A).asIdeal :=
  (PrimeSpectrum.mem_zeroLocus _ _).not

/-- A prime of `A` not containing `𝔞` is the prime under a point of `U`. -/
theorem exists_underlyingPrime_eq (q : PrimeSpectrum S.A) (hq : ¬ S.a ≤ q.asIdeal) :
    ∃ y : S.U.toScheme, underlyingPrime S y = q := by
  have hmemU := (mem_U_iff_not_le S (q : S.X)).2 hq
  rwa [← Scheme.Opens.range_ι S.U] at hmemU

/-- The prime under a point of `U` does not contain `𝔞`. -/
theorem not_le_underlyingPrime (y : S.U.toScheme) : ¬ S.a ≤ (underlyingPrime S y).asIdeal :=
  (mem_U_iff_not_le S _).1 (by rw [← Scheme.Opens.range_ι S.U]; exact ⟨y, rfl⟩)

/-- The closed immersion `Y ⟶ X` sends `z` to its contraction along `A → A/I`. -/
theorem Yι_base_asIdeal (z : S.Y) :
    ((S.Yι.base z : S.X) : PrimeSpectrum S.A).asIdeal =
      (z : PrimeSpectrum (S.A ⧸ S.I)).asIdeal.comap (Ideal.Quotient.mk S.I) := rfl

/-- The dimension of the closure of a point of `U` is the coheight of its prime. -/
theorem height_U_ι_base_eq_coheight (y : S.U.toScheme) :
    Order.height (S.U.ι.base y) = Order.coheight (underlyingPrime S y) :=
  (Order.height_orderIso (specOrderIsoPrimeSpectrum (.of S.A)) (S.U.ι.base y)).symm

/-- A point of `Y` whose image lies in `U`: `I` is contained in its prime. -/
theorem I_le_of_eq_Yι_base (y : S.U.toScheme) (z : S.Y) (hyz : S.U.ι.base y = S.Yι.base z) :
    S.I ≤ (underlyingPrime S y).asIdeal := by
  have hx : underlyingPrime S y = S.Yι.base z :=
    congrArg (fun t : S.X => (t : PrimeSpectrum S.A)) hyz
  rw [hx, Yι_base_asIdeal]
  intro a ha
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact Submodule.zero_mem _

/-- A prime of `A` containing `I` is the image of a point of `Y`. -/
theorem exists_Yι_base_eq (q : PrimeSpectrum S.A) (hq : S.I ≤ q.asIdeal) :
    ∃ z : S.Y, (S.Yι.base z : PrimeSpectrum S.A) = q := by
  obtain ⟨z, hz⟩ : q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk S.I)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      PrimeSpectrum.mem_zeroLocus, Ideal.mk_ker]
    exact hq
  exact ⟨z, hz⟩

end Stacks.Algebraization

end
