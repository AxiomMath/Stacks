module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationFiniteness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdeal

/-!
# Finiteness of the stabilized local cohomology at the maximal ideal

Let `(A, 𝔪)` be a Noetherian local ring, let `I ⊂ A` be an ideal, let `M` be a finite
`A`-module and fix integers `s` and `d`. Stacks 0DXM produces, under hypotheses (1)–(4)
recorded in `Stacks.Algebraization.LocalStabilizationHypotheses`, an ideal `J₀` with
`V(J₀) ∩ V(I) = {𝔪}` whose local cohomology in degrees `≤ s` is annihilated by a power of
`J₀ I`. Stacks 0DXN replaces the empty hypothesis (2) of that lemma by

(2') if `𝔭 ∈ V(I)` and `𝔭 ≠ 𝔪`, then `depth_{A_𝔭}(M_𝔭) + dim(A/𝔭) > s`,

and concludes that `H^i_{J₀}(M)` is a finite `A`-module for `i ≤ s`.

The source proof is "this is a special case of Stacks 0EFJ", the general-`J` statement
formalized in `StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationFiniteness`. This file
carries out that specialization at `J = 𝔪`: hypothesis (2') above is 0EFJ's hypothesis (2') at
`J = 𝔪`, which `depthAddDimGtOnZeroLocus_maximalIdeal_iff` proves, so (2') is derived here and
never assumed in 0EFJ's form.

## Main definitions

* `Stacks.Algebraization.DepthAddDimGtAtMaximalIdeal` — hypothesis (2') of Stacks 0DXN.

## Main results

* `Stacks.Algebraization.depthAddDimGtOnZeroLocus_maximalIdeal_iff` — hypothesis (2') of
  Stacks 0DXN is hypothesis (2') of Stacks 0EFJ at `J = 𝔪`, for every ideal `I`.
* `Stacks.Algebraization.finite_localCohomologyModule_stabilizingIdeal_maximalIdeal` —
  `H^i_{J₀}(M)` is a finite `A`-module for `i ≤ s`, on the annihilation clause of Stacks 0DXM.
* `Stacks.Algebraization.finite_localCohomologyModule_stabilizingIdeal_maximalIdeal_of_exists` —
  the same, with that clause proved from Stacks 0EFI.

## Implementation notes

At `J = 𝔪` the set `V(𝔪) ∩ V(I)` of Stacks 0EFJ is the single point `𝔪`, so a prime of `V(I)`
lies outside it exactly when it is not `𝔪`; and `V(𝔭) ∩ V(𝔪) ∩ V(I)` is again that single
point, where the relative dimension `dim((A/𝔭)_𝔮)` of Stacks 0EFJ is `dim(A/𝔭)`. Both
normalizations are the ones already recorded for Stacks 0DXM, by
`zeroLocus_maximalIdeal_inter` and
`ringKrullDim_localization_quotient_map_of_eq_closedPoint`. They need `𝔪 ∈ V(I)`, that is
`I ≠ A`, which is a field of `LocalStabilizationHypotheses`; the identification below assumes
nothing, because for `I = A` the locus `V(I)` is empty and both conditions are vacuous.

The hypothesis `0 ≤ s` is the one Stacks 0EFC and Stacks 0EFD assume, inherited through Stacks
0EFJ. The annihilation of `H^i_{J₀}(M)` by a power of `J₀ I` for `i ≤ s` is a clause of the
conclusion of Stacks 0DXM, which `Stacks.Algebraization.exists_stabilization_of_exists` states
on the existence statement of Stacks 0EFI; the second result below obtains that existence
statement from Stacks 0EFI itself, `Stacks.Algebraization.exists_isStabilizingData`, and
converts it through
`exists_pow_mul_le_annihilator_localCohomologyModule_stabilizingIdeal`. Hypotheses (3) and (4)
of Stacks 0DXM enter both there and through the existence of `J₀`.

Stacks 0EFI needs `0 ≤ d`, which the source of Stacks 0DXM uses silently when it reads
`depth + dim > d + s` as `depth + dim > s`; see the module documentation of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence`. It does not follow from
`LocalStabilizationHypotheses`, whose dimension condition is vacuous when no prime lies outside
`V(I)` in the relevant locus, so the second result below carries it as the integer inequality
`0 ≤ d` beside `0 ≤ s`.

## References

* [Stacks Project, Tag 0DXN](https://stacks.math.columbia.edu/tag/0DXN)
* [Stacks Project, Tag 0DXM](https://stacks.math.columbia.edu/tag/0DXM)
* [Stacks Project, Tag 0EFJ](https://stacks.math.columbia.edu/tag/0EFJ)
* [Stacks Project, Tag 0EFI](https://stacks.math.columbia.edu/tag/0EFI)

## Tags

local cohomology, depth, finiteness, algebraization, local ring
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {M : Type u} [AddCommGroup M] [Module A M]

/-- Hypothesis (2') of Stacks 0DXN: a prime `𝔭 ∈ V(I)` other than the maximal ideal satisfies
`depth_{A_𝔭}(M_𝔭) + dim(A/𝔭) > s`.

Depth is measured in `ℕ∞` and the dimension of `A/𝔭` in `WithBot ℕ∞`; both are compared with
the integer `s` inside `EInt`, as in Stacks 0EFI and Stacks 0EFJ. -/
public def DepthAddDimGtAtMaximalIdeal (I : Ideal A) (s : ℤ) : Prop :=
  ∀ p : PrimeSpectrum A, p ∈ PrimeSpectrum.zeroLocus (I : Set A) → p ≠ closedPoint A →
    enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M)) +
      krullDimToEInt (ringKrullDim (A ⧸ p.asIdeal)) > (s : EInt)

omit [IsNoetherianRing A] in
/-- **Stacks 0DXN.** Hypothesis (2') of the lemma is hypothesis (2') of Stacks 0EFJ at
`J = 𝔪`, for every ideal `I`.

This biconditional is the content of the source's proof, which reads "this is a special case of
Lemma 0EFJ": at `J = 𝔪` the set `V(𝔪) ∩ V(I)` is the single point `𝔪`, so a prime of `V(I)`
lies outside it exactly when it differs from `𝔪`, and the only specialization of it available
in `V(𝔪) ∩ V(I)` is `𝔪` itself, where `dim((A/𝔭)_𝔪)` is `dim(A/𝔭)`.

That reading of `V(𝔪) ∩ V(I)` uses `𝔪 ∈ V(I)`, the source's standing assumption that `I` is
proper. It is not needed for the equivalence itself: for `I = A` the locus `V(I)` is empty, so
both conditions quantify over nothing. -/
@[stacks 0DXN "hypothesis (2') is hypothesis (2') of Stacks 0EFJ at J = 𝔪, for every ideal I"]
public theorem depthAddDimGtOnZeroLocus_maximalIdeal_iff {I : Ideal A} (s : ℤ) :
    DepthAddDimGtOnZeroLocus (M := M) I (maximalIdeal A) s ↔
      DepthAddDimGtAtMaximalIdeal (M := M) I s := by
  rcases eq_or_ne I ⊤ with rfl | hI
  · have hempty : ∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus ((⊤ : Ideal A) : Set A) := fun p hp ↦
      p.2.ne_top (top_le_iff.mp
        (SetLike.coe_subset_coe.mp ((PrimeSpectrum.mem_zeroLocus _ _).mp hp)))
    exact ⟨fun _ p hp ↦ absurd hp (hempty p), fun _ p hp ↦ absurd hp (hempty p)⟩
  refine ⟨fun h p hp hne ↦ ?_, fun h p hp hmm q hq ↦ ?_⟩
  · have h' := h p hp (fun hmm ↦ hne (by
      rwa [zeroLocus_maximalIdeal_inter hI, Set.mem_singleton_iff] at hmm)) (closedPoint A)
      ⟨⟨closedPoint_mem_zeroLocus p.2.ne_top,
        closedPoint_mem_zeroLocus (maximalIdeal.isMaximal A).ne_top⟩,
        closedPoint_mem_zeroLocus hI⟩
    rwa [ringKrullDim_localization_quotient_map_of_eq_closedPoint rfl] at h'
  · rw [ringKrullDim_localization_quotient_map_of_eq_closedPoint
      (eq_closedPoint_of_mem_zeroLocus_maximalIdeal hq.1.2)]
    exact h p hp fun hpc ↦ hmm (by rwa [zeroLocus_maximalIdeal_inter hI, Set.mem_singleton_iff])

variable [Module.Finite A M]

section

variable (I : Ideal A) (s d : ℤ) (omega : DerivedCategory (ModuleCat.{u} A))
  (H : LocalStabilizationHypotheses (M := M) I s d omega)

/-- **Stacks 0DXN.** Under hypotheses (1), (3), (4) of Stacks 0DXM together with hypothesis
(2') in place of its empty hypothesis (2), the local cohomology of `M` supported in the ideal
`J₀` that Stacks 0DXM selects is a finite `A`-module in every degree `i ≤ s`.

This is Stacks 0EFJ at `J = 𝔪`. The annihilation of `H^i_{J₀}(M)` by a power of `J₀ I` for
`i ≤ s` is a clause of the conclusion of Stacks 0DXM and is carried as a hypothesis, as it is in
Stacks 0EFJ. -/
@[stacks 0DXN "H^i_{J₀}(M) is a finite A-module for i ≤ s, given the annihilation clause of \
Stacks 0DXM and 0 ≤ s"]
public theorem finite_localCohomologyModule_stabilizingIdeal_maximalIdeal
    (h2 : DepthAddDimGtAtMaximalIdeal (M := M) I s) (hs : 0 ≤ s)
    (hann : ∃ n : ℕ, ∀ j : ℤ, j ≤ s →
      ((stabilizingIdeal I (maximalIdeal A) s d omega H.toStabilizationHypotheses * I) ^ n
        : Ideal A) ≤ Module.annihilator A
        (localCohomologyModule A
          (stabilizingIdeal I (maximalIdeal A) s d omega H.toStabilizationHypotheses)
          (Ideal.fg_of_isNoetherianRing
            (stabilizingIdeal I (maximalIdeal A) s d omega H.toStabilizationHypotheses))
          (ModuleCat.of A M) j))
    (i : ℤ) (hi : i ≤ s) :
    Module.Finite A
      (localCohomologyModule A
        (stabilizingIdeal I (maximalIdeal A) s d omega H.toStabilizationHypotheses)
        (Ideal.fg_of_isNoetherianRing
          (stabilizingIdeal I (maximalIdeal A) s d omega H.toStabilizationHypotheses))
        (ModuleCat.of A M) i) :=
  finite_localCohomologyModule_stabilizingIdeal I (maximalIdeal A) s d omega
    H.toStabilizationHypotheses ((depthAddDimGtOnZeroLocus_maximalIdeal_iff s).2 h2)
    hs hann i hi

/-- **Stacks 0DXN.** The same finiteness, with the annihilation clause of Stacks 0DXM proved
from Stacks 0EFI.

The hypotheses are then exactly those of Stacks 0DXM with its empty hypothesis (2) replaced by
(2'), together with `0 ≤ s` and the hypothesis `0 ≤ d` that Stacks 0EFI needs and the source
of Stacks 0DXM uses silently; see the module documentation. -/
@[stacks 0DXN "H^i_{J₀}(M) is a finite A-module for i ≤ s, for 0 ≤ s and 0 ≤ d"]
public theorem finite_localCohomologyModule_stabilizingIdeal_maximalIdeal_of_exists
    (h2 : DepthAddDimGtAtMaximalIdeal (M := M) I s) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (i : ℤ) (hi : i ≤ s) :
    Module.Finite A
      (localCohomologyModule A
        (stabilizingIdeal I (maximalIdeal A) s d omega H.toStabilizationHypotheses)
        (Ideal.fg_of_isNoetherianRing
          (stabilizingIdeal I (maximalIdeal A) s d omega H.toStabilizationHypotheses))
        (ModuleCat.of A M) i) :=
  finite_localCohomologyModule_stabilizingIdeal_maximalIdeal I s d omega H h2 hs
    (exists_pow_mul_le_annihilator_localCohomologyModule_stabilizingIdeal I (maximalIdeal A) s d
      omega H.toStabilizationHypotheses
      (exists_isStabilizingData I (maximalIdeal A) s d hd omega
        H.toStabilizationHypotheses)) i hi

end

end Stacks.Algebraization

end
