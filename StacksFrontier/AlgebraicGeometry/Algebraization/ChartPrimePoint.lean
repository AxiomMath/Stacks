module

public import StacksFrontier.AlgebraicGeometry.Algebraization.ChartPrimeCompletedStalk
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.RingTheory.AdicCompletion.MapOfPowLe

/-!
# Points of `U ∩ Y` from primes, and the primes of a completed chart ring

In the situation of Stacks 0EHC, a prime `P` of `A` not containing `𝔞` is a point of
`U = Spec(A) \ V(𝔞)`, and if it contains `I` it is also a point of `Y = V(I)`, the same point of
`Spec(A)`. This file names those points and records, for `A` local with `𝔪 = 𝔞`, that the
distance `δ^Y_Z` of Stacks 0EIX is finite at every point of `Y`.

It then describes the primes `𝔮 ⊇ I B` of a completed chart ring `B = (A_f)^∧_{I A_f}`, the ring
over which the per-point step of the proof of Stacks 0EHK runs: the prime `P` of `A` under `𝔮`
avoids `f` and contains `I`, and for `f ∈ 𝔞` it is a point of `U ∩ Y` whose attached prime
`Stacks.Algebraization.completedChartPrime` of `B` is `𝔮` again. The last statement is an
instance of a uniqueness that holds for any adic completion along a finitely generated ideal:
a prime of `R^∧_J` containing `J R^∧` is determined by its contraction to `R`
(`Stacks.Algebraization.eq_adicPrimeOver`).

## Main definitions

* `Stacks.Algebraization.chartRing`, `Stacks.Algebraization.chartIdeal` — the completed chart
  ring `B = (A_f)^∧_{I A_f}` and the ideal `I B`.
* `Stacks.Algebraization.pointOfPrime`, `Stacks.Algebraization.pointOfPrimeY` — the points of
  `U` and of `Y` given by a prime of `A`.

## Main results

* `Stacks.Algebraization.underlyingPrime_pointOfPrime`,
  `Stacks.Algebraization.base_pointOfPrime_eq` — the two points lie over `P`.
* `Stacks.Algebraization.distanceToZ_ne_top` — `δ^Y_Z` is finite when `A` is local and `𝔪 = 𝔞`.
* `Stacks.Algebraization.eq_adicPrimeOver` — uniqueness of the prime of an adic completion
  above a prime containing the ideal.
* `Stacks.Algebraization.eq_completedChartPrime_pointOfPrime` — a prime `𝔮 ⊇ I B` of the
  completed chart ring is the completed chart prime of the point under it.

## References

* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EIX](https://stacks.math.columbia.edu/tag/0EIX), the distance function.
* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK), the consumer.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-! ### Uniqueness of the prime of an adic completion above a prime -/

/-- **A prime of an adic completion containing the extended ideal is determined by its
contraction.** For a finitely generated ideal `J` of `R`, a prime `𝔮` of `R^∧_J` with
`J R^∧ ⊆ 𝔮` contracting to `𝔭` is `Stacks.Algebraization.adicPrimeOver J _`, the kernel of
`R^∧ → R/𝔭`: every element of `R^∧` is congruent to an element of `R` modulo `J R^∧`, which both
primes contain. -/
theorem eq_adicPrimeOver {R : Type u} [CommRing R] {J : Ideal R} (hJ : J.FG) {p : Ideal R}
    [p.IsPrime] (hJp : J ≤ p) (q : PrimeSpectrum (AdicCompletion J R))
    (hq : J.map (algebraMap R (AdicCompletion J R)) ≤ q.asIdeal)
    (hp : q.asIdeal.comap (algebraMap R (AdicCompletion J R)) = p) :
    q = adicPrimeOver J hJp := by
  ext x
  obtain ⟨r, hr⟩ := AdicCompletion.exists_sub_mem_map_pow J hJ 1 x
  rw [pow_one] at hr
  have key : ∀ Q : Ideal (AdicCompletion J R), J.map (algebraMap R _) ≤ Q →
      (x ∈ Q ↔ algebraMap R _ r ∈ Q) := fun Q hQ =>
    ⟨fun hx => by simpa using Q.sub_mem hx (hQ hr), fun h => by simpa using Q.add_mem (hQ hr) h⟩
  rw [key _ hq, key _ (map_le_adicPrimeOver J hJp), ← Ideal.mem_comap, hp, ← Ideal.mem_comap,
    comap_adicPrimeOver J hJp]

variable (S : AlgebraizationSituation.{u})

/-! ### Points of `U` and of `Y` from primes of `A` -/

/-- **The point of `U` given by a prime of `A` not containing `𝔞`.** -/
def pointOfPrime (P : PrimeSpectrum S.A) (hP : ¬ S.a ≤ P.asIdeal) : S.U.toScheme :=
  ⟨P, show P ∉ PrimeSpectrum.zeroLocus (S.a : Set S.A) from hP⟩

/-- The prime of `A` under `Stacks.Algebraization.pointOfPrime S P hP` is `P`. -/
@[simp]
theorem underlyingPrime_pointOfPrime (P : PrimeSpectrum S.A) (hP : ¬ S.a ≤ P.asIdeal) :
    underlyingPrime S (pointOfPrime S P hP) = P :=
  rfl

/-- **The point of `Y = Spec(A/I)` given by a prime of `A` containing `I`**: the image of `P` in
`A/I`. -/
def pointOfPrimeY (P : PrimeSpectrum S.A) (hIP : S.I ≤ P.asIdeal) : S.Y :=
  ⟨P.asIdeal.map (Ideal.Quotient.mk S.I),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])⟩

/-- `Stacks.Algebraization.pointOfPrimeY` lies over `P`. -/
theorem Yι_base_pointOfPrimeY (P : PrimeSpectrum S.A) (hIP : S.I ≤ P.asIdeal) :
    S.Yι.base (pointOfPrimeY S P hIP) = P := by
  refine PrimeSpectrum.ext (R := S.A) ?_
  show (P.asIdeal.map (Ideal.Quotient.mk S.I)).comap (Ideal.Quotient.mk S.I) = P.asIdeal
  exact Ideal.comap_map_mk hIP

/-- **The two points attached to `P` are the same point of `Spec(A)`.** -/
theorem base_pointOfPrime_eq (P : PrimeSpectrum S.A) (hP : ¬ S.a ≤ P.asIdeal)
    (hIP : S.I ≤ P.asIdeal) :
    S.U.ι.base (pointOfPrime S P hP) = S.Yι.base (pointOfPrimeY S P hIP) :=
  (Yι_base_pointOfPrimeY S P hIP).symm

/-! ### Finiteness of the distance function -/

/-- **`δ^Y_Z` is finite when `A` is local with `𝔪 = 𝔞`.** Every point `z` of `Y = Spec(A/I)`
specializes to the image of the maximal ideal, which lies in `Z = V(𝔞)`; so the connected
component of `z` meets `Z` and there is a system of integral closed subschemes from `Z` to `z`
(Stacks 0EIX), whose weight bounds the distance. -/
theorem distanceToZ_ne_top [IsLocalRing S.A] (hmax : IsLocalRing.maximalIdeal S.A = S.a)
    (z : S.Y) : S.distanceToZ z ≠ ⊤ := by
  let x₀ : S.Y := pointOfPrimeY S (IsLocalRing.closedPoint S.A) (S.I_le_a.trans hmax.ge)
  have hzx : z ⤳ x₀ := by
    refine (PrimeSpectrum.le_iff_specializes (R := S.A ⧸ S.I) z x₀).mp ?_
    show z.asIdeal ≤ (IsLocalRing.maximalIdeal S.A).map (Ideal.Quotient.mk S.I)
    calc z.asIdeal = (z.asIdeal.comap (Ideal.Quotient.mk S.I)).map (Ideal.Quotient.mk S.I) :=
          (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _).symm
      _ ≤ _ := Ideal.map_mono (IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ z.isPrime.ne_top))
  have hx₀Z : x₀ ∈ (S.closedSubsetZ : Set S.Y) := by
    show ((S.a.map (Ideal.Quotient.mk S.I) : Ideal (S.A ⧸ S.I)) : Set (S.A ⧸ S.I)) ⊆
      (((IsLocalRing.maximalIdeal S.A).map (Ideal.Quotient.mk S.I) : Ideal (S.A ⧸ S.I)) :
        Set (S.A ⧸ S.I))
    rw [hmax]
  have hconn : (connectedComponent z ∩ (S.closedSubsetZ : Set S.Y)).Nonempty :=
    ⟨x₀, isPreconnected_singleton.closure.subset_connectedComponent (subset_closure rfl)
      (specializes_iff_mem_closure.mp hzx), hx₀Z⟩
  obtain ⟨s⟩ := nonempty_distanceSystem_of_connectedComponent_inter S.Y S.closedSubsetZ z hconn
  have hle : S.distanceToZ z ≤ s.weight := by
    rw [AlgebraizationSituation.distanceToZ,
      distanceFunction_eq_iInf_of_nonempty S.Y S.closedSubsetZ z hconn]
    exact iInf_le _ s
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hle

/-! ### The primes of a completed chart ring -/

variable (f : S.A)

/-- **The completed chart ring** `B = (A_f)^∧_{I A_f}` of the chart `D(f)`. -/
abbrev chartRing : Type u :=
  AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f))) (Localization.Away f)

/-- **The ideal `I B`** of the completed chart ring. -/
abbrev chartIdeal : Ideal (chartRing S f) :=
  (S.I.map (algebraMap S.A (Localization.Away f))).map
    (algebraMap (Localization.Away f) (chartRing S f))

/-- The structure map `A → B` is the composite `A → A_f → B`. -/
theorem algebraMap_chartRing_apply (a : S.A) :
    algebraMap S.A (chartRing S f) a =
      algebraMap (Localization.Away f) (chartRing S f) (algebraMap S.A (Localization.Away f) a) :=
  rfl

/-- `I B` is the extension of `I` along `A → B`. -/
theorem chartIdeal_eq_map : chartIdeal S f = S.I.map (algebraMap S.A (chartRing S f)) := by
  rw [chartIdeal, Ideal.map_map]
  rfl

variable {S f} (q : PrimeSpectrum (chartRing S f))

/-- **`f` lies outside the prime of `A` under any prime of `B`**: it is a unit of `B`. -/
theorem notMem_comap_chartRing :
    f ∉ (PrimeSpectrum.comap (algebraMap S.A (chartRing S f)) q).asIdeal := by
  intro hf
  have hu : IsUnit (algebraMap S.A (chartRing S f) f) := by
    rw [algebraMap_chartRing_apply]
    exact (IsLocalization.Away.algebraMap_isUnit f).map _
  exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hf hu)

/-- **The prime of `A` under a prime `𝔮 ⊇ I B` contains `I`.** -/
theorem le_comap_chartRing (hq : chartIdeal S f ≤ q.asIdeal) :
    S.I ≤ (PrimeSpectrum.comap (algebraMap S.A (chartRing S f)) q).asIdeal := by
  rw [chartIdeal_eq_map] at hq
  exact Ideal.map_le_iff_le_comap.mp hq

/-- **For `f ∈ 𝔞`, the prime of `A` under any prime of `B` does not contain `𝔞`**, so it is a
point of `U`. -/
theorem not_le_comap_chartRing (hf : f ∈ S.a) :
    ¬ S.a ≤ (PrimeSpectrum.comap (algebraMap S.A (chartRing S f)) q).asIdeal :=
  fun h => notMem_comap_chartRing q (h hf)

/-- The prime of the chart ring `A_f` under `𝔮` is the extension of the prime of `A` under `𝔮`:
it is the `Stacks.Algebraization.chartPrimeOfPoint` of the point under `𝔮`. -/
theorem comap_chartRing_localization_eq (hf : f ∈ S.a) :
    q.asIdeal.comap (algebraMap (Localization.Away f) (chartRing S f)) =
      chartPrimeOfPoint S (pointOfPrime S _ (not_le_comap_chartRing q hf)) f := by
  rw [chartPrimeOfPoint, underlyingPrime_pointOfPrime]
  show _ = ((q.asIdeal.comap (algebraMap (Localization.Away f) (chartRing S f))).comap
    (algebraMap S.A (Localization.Away f))).map (algebraMap S.A (Localization.Away f))
  exact (IsLocalization.map_comap (Submonoid.powers f) (Localization.Away f) _).symm

/-- **A prime `𝔮 ⊇ I B` of the completed chart ring is the completed chart prime of the point
under it.** For `f ∈ 𝔞`, the prime `P` of `A` under `𝔮` is a point `y` of `U ∩ Y`, and
`Stacks.Algebraization.completedChartPrime S y f` — the prime of `B` above `P A_f` containing
`I B` — is `𝔮`. -/
theorem eq_completedChartPrime_pointOfPrime (hf : f ∈ S.a) (hq : chartIdeal S f ≤ q.asIdeal) :
    q = completedChartPrime
      (hp := isPrime_chartPrimeOfPoint S (pointOfPrime S _ (not_le_comap_chartRing q hf)) f
        (notMem_comap_chartRing q))
      S (pointOfPrime S _ (not_le_comap_chartRing q hf)) f (le_comap_chartRing q hq) := by
  have := isPrime_chartPrimeOfPoint S (pointOfPrime S _ (not_le_comap_chartRing q hf)) f
    (notMem_comap_chartRing q)
  exact eq_adicPrimeOver (Ideal.fg_of_isNoetherianRing _) _ q hq
    (comap_chartRing_localization_eq q hf)

end Stacks.Algebraization

end
