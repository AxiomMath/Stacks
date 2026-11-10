module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapCompletion
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FinitenessLocalCohomology.DepthAdicCompletion
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FinitenessLocalCohomology.DepthDimAdicCompletion
public import StacksFrontier.RingTheory.AdicCompletion.QuotientDimensionSplit
import all StacksFrontier.AlgebraicGeometry.Algebraization.AlgebraizationLocalCohomologyIIIBootstrapCriterion

/-!
# The completion of a bootstrap situation

Part (G) of [Stacks, Tag 0EFV]: for a bootstrap situation `S` with ring `A`, ideal `I`, module `M`
and locus `T`, the `I`-adic completions `A' = A^∧`, `M' = M^∧`, the extended ideal `I' = I A'` and
the preimage `T'` of `T` form a bootstrap situation with the same bounds `s` and `d`.

Assumptions (1), (3) and (6) and the conditions on the locus are
`StacksFrontier/AlgebraicGeometry/Algebraization/BootstrapCompletion.lean`. Assumption (4) is the
argument of the source from [Stacks, Tag 0EHW]: a chain `p' ⊆ r' ⊆ q'` in `Spec A'` as in (4)
lies over a chain `p ⊆ r ⊆ q` in `Spec A` as in (4); and `depth(M'_{p'}) ≥ depth(M_p)` while
`depth(M'_{p'}) + dim((A'/p')_{q'}) = depth(M_p) + dim((A/p)_q)`, so each alternative of (4) for
`A` gives the same alternative for `A'`.

When `A` is local and `T` is its closed point, `A'` is local, `I'`-adically complete, and `T'` is
the closed point of `A'`.

## Main results

* `Stacks.Algebraization.depth_or_depth_add_dimension_adicCompletion` — assumption (4) after
  completion.
* `Stacks.Algebraization.BootstrapSituation.adicCompletion` — the completed situation.
* `Stacks.Algebraization.BootstrapSituation.isLocalRing_adicCompletion`,
  `Stacks.Algebraization.BootstrapSituation.isAdicComplete_adicCompletion` and
  `Stacks.Algebraization.BootstrapSituation.adicCompletion_T_eq` — the local case.

## References

* [Stacks Project, Tag 0EFV](https://stacks.math.columbia.edu/tag/0EFV)
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v w

namespace Stacks.Algebraization

/-- **Stacks Project, Tag 0EFV (G), assumption (4).** The chain-of-primes depth estimate of a
bootstrap situation persists after `I`-adic completion, for the completed locus. -/
@[stacks 0EFV "completion"]
public theorem depth_or_depth_add_dimension_adicCompletion (S : BootstrapSituation.{u, v, w}) :
    ∀ p r q : PrimeSpectrum (AdicCompletion S.I S.A),
      p.asIdeal ≤ r.asIdeal → r.asIdeal ≤ q.asIdeal →
      p ∉ PrimeSpectrum.zeroLocus
        ((S.I.map (algebraMap S.A (AdicCompletion S.I S.A))) : Set (AdicCompletion S.I S.A)) →
      r ∈ PrimeSpectrum.zeroLocus
        ((S.I.map (algebraMap S.A (AdicCompletion S.I S.A))) : Set (AdicCompletion S.I S.A)) →
      r ∉ adicCompletionLocus S → q ∈ adicCompletionLocus S →
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl (AdicCompletion S.I S.M))) ≥ (S.s : EInt)) ∨
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl (AdicCompletion S.I S.M))) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap (AdicCompletion S.I S.A)
              (Localization.AtPrime q.asIdeal)))) >
        ((S.d + S.s : ℤ) : EInt)) := by
  intro p' r' q' hpr hrq hp hr hrT hq
  let f := algebraMap S.A (AdicCompletion S.I S.A)
  let p := PrimeSpectrum.comap f p'
  let r := PrimeSpectrum.comap f r'
  let q := PrimeSpectrum.comap f q'
  have hp₀ : p ∉ PrimeSpectrum.zeroLocus (S.I : Set S.A) := fun h =>
    hp (Ideal.map_le_iff_le_comap.mpr ((PrimeSpectrum.mem_zeroLocus _ _).mp h))
  have hr₀ : r ∈ PrimeSpectrum.zeroLocus (S.I : Set S.A) :=
    Ideal.map_le_iff_le_comap.mp ((PrimeSpectrum.mem_zeroLocus _ _).mp hr)
  have hIq : S.I.map f ≤ q'.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr
      ((PrimeSpectrum.mem_zeroLocus _ _).mp (S.subset_adicLocus hq))
  have : p'.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  have : q'.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  have hle := Module.depth_localized_adicCompletion_le S.I (M := S.M) p.asIdeal p'.asIdeal
  have heq := congrArg krullDimToEInt
    (Module.depth_add_ringKrullDim_quotient_localization_adicCompletion S.A S.dualizing S.I S.M
      p.asIdeal q.asIdeal p'.asIdeal q'.asIdeal hIq (hpr.trans hrq))
  rw [krullDimToEInt_coe_add, krullDimToEInt_coe_add] at heq
  rcases S.depth_or_depth_add_dimension p r q (Ideal.comap_mono hpr) (Ideal.comap_mono hrq)
      hp₀ hr₀ hrT hq with h | h
  · exact Or.inl (h.trans (enatToEInt_mono hle))
  · exact Or.inr (heq ▸ h)

namespace BootstrapSituation

/-- **Stacks Project, Tag 0EFV (G).** The `I`-adic completion of a bootstrap situation: the
completed ring `A^∧`, the extended ideal `I A^∧`, the completed module `M^∧` and the preimage of
the locus, with the same bounds. -/
@[stacks 0EFV "part (G): the completed quadruple is again a situation as in Stacks 0EFU"]
public def adicCompletion (S : BootstrapSituation.{u, v, w}) : BootstrapSituation.{u, v, w} where
  A := AdicCompletion S.I S.A
  I := S.I.map (algebraMap S.A (AdicCompletion S.I S.A))
  M := AdicCompletion S.I S.M
  finite := finite_adicCompletion S
  T := adicCompletionLocus S
  subset_adicLocus := subset_adicLocus_adicCompletion S
  stableUnderSpecialization := stableUnderSpecialization_adicCompletion S
  s := S.s
  d := S.d
  dualizing := dualizing_adicCompletion S
  cohomologicalDimension_le := cohomologicalDimension_le_adicCompletion S
  depth_or_depth_add_dimension := depth_or_depth_add_dimension_adicCompletion S
  completedLocalDepth := completedLocalDepth_adicCompletion S

variable (S : BootstrapSituation.{u, v, w})

/-- The completed ring of a bootstrap situation is complete for the extended ideal. -/
public theorem isAdicComplete_adicCompletion :
    IsAdicComplete S.adicCompletion.I S.adicCompletion.A :=
  AdicCompletion.isAdicComplete_self S.I (Ideal.fg_of_isNoetherianRing S.I)

/-- If the locus of a bootstrap situation over a local ring is the closed point, then `I` lies in
the maximal ideal. -/
private theorem le_closedPoint_of_T_eq [IsLocalRing S.A] (hT : S.T = {closedPoint S.A}) :
    S.I ≤ (closedPoint S.A).asIdeal :=
  (PrimeSpectrum.mem_zeroLocus _ _).mp
    (S.subset_adicLocus (hT ▸ Set.mem_singleton (closedPoint S.A)))

/-- **Stacks Project, Tag 0EFV (G), local case.** The completion of a bootstrap situation over a
local ring whose locus is the closed point has a local ring. -/
public theorem isLocalRing_adicCompletion [IsLocalRing S.A] (hT : S.T = {closedPoint S.A}) :
    IsLocalRing S.adicCompletion.A :=
  Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal S.I
    (le_closedPoint_of_T_eq S hT)

/-- For `J` inside the maximal ideal of a Noetherian local ring `R`, a prime of the `J`-adic
completion contracts to the maximal ideal of `R` exactly when it is the extension of that maximal
ideal, which is maximal. -/
private theorem comap_eq_maximalIdeal_iff {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (J : Ideal R) (hJ : J ≤ maximalIdeal R) (P : Ideal (AdicCompletion J R))
    [P.IsPrime] :
    P.comap (algebraMap R (AdicCompletion J R)) = maximalIdeal R ↔
      P = (maximalIdeal R).map (algebraMap R (AdicCompletion J R)) := by
  let f := algebraMap R (AdicCompletion J R)
  have hmax : ((maximalIdeal R).map f).IsMaximal :=
    AdicCompletion.isMaximal_map_of_le J (maximalIdeal R) hJ (Ideal.fg_of_isNoetherianRing J)
  refine ⟨fun h => (hmax.eq_of_le (Ideal.IsPrime.ne_top ‹_›)
    (Ideal.map_le_iff_le_comap.mpr h.ge)).symm, ?_⟩
  rintro rfl
  exact ((maximalIdeal.isMaximal R).eq_of_le
    (Ideal.comap_isPrime f ((maximalIdeal R).map f)).ne_top Ideal.le_comap_map).symm

/-- **Stacks Project, Tag 0EFV (G), local case.** The completion of a bootstrap situation over a
local ring whose locus is the closed point has the closed point of the completed ring as its
locus. -/
public theorem adicCompletion_T_eq [IsLocalRing S.A] (hT : S.T = {closedPoint S.A}) :
    letI := isLocalRing_adicCompletion S hT
    S.adicCompletion.T = {closedPoint S.adicCompletion.A} := by
  let := isLocalRing_adicCompletion S hT
  have hJ := le_closedPoint_of_T_eq S hT
  let f := algebraMap S.A (AdicCompletion S.I S.A)
  have hmax : ((maximalIdeal S.A).map f).IsMaximal :=
    AdicCompletion.isMaximal_map_of_le S.I (maximalIdeal S.A) hJ
      (Ideal.fg_of_isNoetherianRing S.I)
  let : IsLocalRing (AdicCompletion S.I S.A) := isLocalRing_adicCompletion S hT
  have hm : (maximalIdeal S.adicCompletion.A : Ideal (AdicCompletion S.I S.A)) =
      (maximalIdeal S.A).map f :=
    (IsLocalRing.eq_maximalIdeal hmax).symm
  ext p
  change PrimeSpectrum.comap f p ∈ S.T ↔ p = closedPoint S.adicCompletion.A
  rw [hT, Set.mem_singleton_iff, PrimeSpectrum.ext_iff, PrimeSpectrum.ext_iff]
  change (p.asIdeal : Ideal (AdicCompletion S.I S.A)).comap f = maximalIdeal S.A ↔
    (p.asIdeal : Ideal (AdicCompletion S.I S.A)) =
      (maximalIdeal S.adicCompletion.A : Ideal (AdicCompletion S.I S.A))
  rw [hm]
  exact @comap_eq_maximalIdeal_iff S.A _ _ _ S.I hJ _ p.isPrime

end BootstrapSituation

end Stacks.Algebraization

end
