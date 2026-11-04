module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdealFiniteness
public import StacksFrontier.RingTheory.Jacobson.Criteria
import all StacksFrontier.RingTheory.Jacobson.Criteria

/-!
# Stacks 0DXN for all integers `s` and `d`

Let `(A, 𝔪)` be a Noetherian local ring, let `I ⊂ A` be an ideal, let `M` be a finite
`A`-module and fix integers `s` and `d`. Stacks 0DXM produces, under hypotheses (1)–(4)
recorded in `Stacks.Algebraization.LocalStabilizationHypotheses`, an ideal `J₀` with
`V(J₀) ∩ V(I) = {𝔪}` such that `RΓ_{J₀}(M) → RΓ_J(M)` is an isomorphism in degrees `≤ s` for
every `J ⊆ J₀` with `V(J) ∩ V(I) = {𝔪}`, and these modules are annihilated by a power of
`J₀ I`. Stacks 0DXN replaces its empty hypothesis (2) by

(2') if `𝔭 ∈ V(I)` and `𝔭 ≠ 𝔪`, then `depth_{A_𝔭}(M_𝔭) + dim(A/𝔭) > s`,

and concludes that moreover `H^i_{J₀}(M)` is a finite `A`-module for `i ≤ s`. This file proves
that statement for all integers `s` and `d`, with the whole conclusion of Stacks 0DXM.

## Main results

* `Stacks.Algebraization.exists_stabilization_finite_localCohomologyModule_maximalIdeal` —
  **Stacks 0DXN**.
* `Stacks.Algebraization.LocalStabilizationHypotheses.mem_zeroLocus_of_neg` — for `d < 0` the
  hypotheses of Stacks 0DXM force every prime to contain `I`.
* `Stacks.Algebraization.LocalStabilizationHypotheses.exists_isStabilizingData` — the existence
  statement of Stacks 0EFI at `J = 𝔪`, for every `d`.

## Implementation notes

The source proof is "this is a special case of Stacks 0EFJ". The finiteness for `0 ≤ s` is
`Stacks.Algebraization.finite_localCohomologyModule_stabilizingIdeal_maximalIdeal`, the case
`J = 𝔪` of Stacks 0EFJ, whose annihilation input is here proved rather than assumed: it is the
clause of Stacks 0EFI provided by `Stacks.Algebraization.exists_isStabilizingData`. For `s < 0`
the modules `H^i_{J₀}(M)`, `i ≤ s`, vanish.

`Stacks.Algebraization.exists_isStabilizingData` needs `0 ≤ d`. For the local situation of
Stacks 0DXM the case `d < 0` reduces to `d = 0`: a prime `𝔭 ∉ V(I)` maximal with that
property satisfies `V(𝔭) ∩ V(I) = {𝔪}` (every prime strictly above it contains a fixed element
of `I ∖ 𝔭`, so it is maximal by Stacks 02IG applied to `A/𝔭`), and hypothesis (3) would give
`dim(A/𝔭) ≤ d < 0`. So no prime lies outside `V(I)` and hypotheses (3), (4) hold for any `d`.
The private lemma `isMaximal_of_lt_of_forall_mem` carrying that step is reached through
`import all StacksFrontier.RingTheory.Jacobson.Criteria`.

## References

* [Stacks Project, Tag 0DXN](https://stacks.math.columbia.edu/tag/0DXN)
* [Stacks Project, Tag 0DXM](https://stacks.math.columbia.edu/tag/0DXM)
* [Stacks Project, Tag 0EFJ](https://stacks.math.columbia.edu/tag/0EFJ)
* [Stacks Project, Tag 0EFI](https://stacks.math.columbia.edu/tag/0EFI)
* [Stacks Project, Tag 02IG](https://stacks.math.columbia.edu/tag/02IG)

## Tags

local cohomology, depth, finiteness, algebraization, local ring
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **Hypothesis (3) of Stacks 0DXM for `d < 0`.** If `d < 0`, then hypotheses (1)–(4) of
Stacks 0DXM force every prime of `A` to contain `I`, that is, `I` is nilpotent.

Otherwise choose a prime `𝔭 ∉ V(I)` maximal with that property and `x ∈ I` outside `𝔭`. Every
prime strictly containing `𝔭` contains `I`, hence `x`, so it is maximal: this is
`dim A/𝔭 ≤ 1` for the Noetherian local domain `A/𝔭`, in which the nonzero element `x` lies in
every nonzero prime (Stacks 02IG). Hence `V(𝔭) ∩ V(I) = {𝔪}`, and hypothesis (3) asks for
`dim(A/𝔭) ≤ d < 0`, which fails for the nonzero ring `A/𝔭`. -/
public theorem LocalStabilizationHypotheses.mem_zeroLocus_of_neg {I : Ideal A} {s d : ℤ}
    {omega : DerivedCategory (ModuleCat.{u} A)}
    (H : LocalStabilizationHypotheses (M := M) I s d omega) (hd : d < 0)
    (p : PrimeSpectrum A) : p ∈ PrimeSpectrum.zeroLocus (I : Set A) := by
  by_contra hp
  obtain ⟨P, ⟨hPp, hPI⟩, hPmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian A A)
      {P : Ideal A | P.IsPrime ∧ ¬ I ≤ P}
      ⟨p.asIdeal, p.2, hp⟩
  have := hPp
  obtain ⟨x, hxI, hxP⟩ := SetLike.not_le_iff_exists.mp hPI
  have hIq : ∀ q : Ideal A, q.IsPrime → P < q → I ≤ q := fun q hq hPq ↦ by
    by_contra h
    exact hPmax q ⟨hq, h⟩ hPq
  have hmax : ∀ q : Ideal A, q.IsPrime → P < q → q = maximalIdeal A := fun q hq hPq ↦
    IsLocalRing.eq_maximalIdeal
      (Stacks.Jacobson.NoetherianCriterion.isMaximal_of_lt_of_forall_mem (p := P) hxP
        (fun r hr hPr ↦ hIq r hr hPr hxI) hq hPq)
  let P' : PrimeSpectrum A := ⟨P, hPp⟩
  have hP'I : P' ∉ PrimeSpectrum.zeroLocus (I : Set A) := hPI
  have hV : PrimeSpectrum.zeroLocus (P'.asIdeal : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A) = {closedPoint A} := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hrP, hrI⟩
      exact PrimeSpectrum.ext (hmax _ r.2 (lt_of_le_of_ne hrP
        fun h ↦ hPI (h ▸ hrI)))
    · rintro rfl
      exact ⟨closedPoint_mem_zeroLocus hPp.ne_top, closedPoint_mem_zeroLocus H.ne_top⟩
  have hdim := H.dimensionBound P' hP'I hV
  obtain ⟨n, hn⟩ : ∃ n : ℕ∞, ringKrullDim (A ⧸ P) = n :=
    WithBot.ne_bot_iff_exists.mp
      (ne_of_gt (lt_of_lt_of_le (WithBot.bot_lt_coe 0) ringKrullDim_nonneg_of_nontrivial))
        |>.imp fun _ h ↦ h.symm
  change krullDimToEInt (ringKrullDim (A ⧸ P)) ≤ (d : EInt) at hdim
  rw [hn] at hdim
  induction n using ENat.recTopCoe with
  | top =>
      change (⊤ : EInt) ≤ (d : EInt) at hdim
      exact absurd hdim (by simp)
  | coe n =>
      change ((n : ℤ) : EInt) ≤ (d : EInt) at hdim
      have := WithBotTop.coe_le_coe.mp hdim
      omega

/-- The hypotheses of Stacks 0DXM for `d < 0` imply those for `d = 0`: they force `V(I)` to be
all of `Spec(A)`, so hypotheses (3) and (4), which only concern primes outside `V(I)`, hold
vacuously for every `d`. -/
public theorem LocalStabilizationHypotheses.of_neg {I : Ideal A} {s d : ℤ}
    {omega : DerivedCategory (ModuleCat.{u} A)}
    (H : LocalStabilizationHypotheses (M := M) I s d omega) (hd : d < 0) (d' : ℤ) :
    LocalStabilizationHypotheses (M := M) I s d' omega where
  ne_top := H.ne_top
  dualizing := H.dualizing
  dimensionBound p hp _ := absurd (H.mem_zeroLocus_of_neg hd p) hp
  depthOrDimensionBound p hp _ := absurd (H.mem_zeroLocus_of_neg hd p) hp

/-- **Stacks 0EFI at `J = 𝔪`, for every `d`.** Under hypotheses (1)–(4) of Stacks 0DXM a pair
with the stabilization property of Stacks 0EFI at `J = 𝔪` exists. For `0 ≤ d` this is
`exists_isStabilizingData`; for `d < 0` the hypotheses hold with `d = 0` as well, by
`LocalStabilizationHypotheses.of_neg`. -/
public theorem LocalStabilizationHypotheses.exists_isStabilizingData {I : Ideal A} {s d : ℤ}
    {omega : DerivedCategory (ModuleCat.{u} A)}
    (H : LocalStabilizationHypotheses (M := M) I s d omega) :
    ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I (maximalIdeal A) s p := by
  rcases le_or_gt 0 d with hd | hd
  · exact Stacks.Algebraization.exists_isStabilizingData I (maximalIdeal A) s d hd omega
      H.toStabilizationHypotheses
  · exact Stacks.Algebraization.exists_isStabilizingData I (maximalIdeal A) s 0 le_rfl omega
      (H.of_neg hd 0).toStabilizationHypotheses

/-- **Stacks 0DXN.** Let `(A, 𝔪)` be a Noetherian local ring, `I ⊂ A` an ideal, `M` a finite
`A`-module and `s`, `d` integers. Assume (1) `A` has a dualizing complex, (2') every prime
`𝔭 ∈ V(I)` other than `𝔪` has `depth(M_𝔭) + dim(A/𝔭) > s`, (3) every prime `𝔭 ∉ V(I)` with
`V(𝔭) ∩ V(I) = {𝔪}` has `dim(A/𝔭) ≤ d`, and (4) every prime `𝔭 ∉ V(I)` with
`V(𝔭) ∩ V(I) ≠ {𝔪}` has `depth(M_𝔭) ≥ s` or `depth(M_𝔭) + dim(A/𝔭) > d + s`. Then there is an
ideal `J₀` with `V(J₀) ∩ V(I) = {𝔪}` such that for every `J ⊆ J₀` with `V(J) ∩ V(I) = {𝔪}` the
map `RΓ_{J₀}(M) → RΓ_J(M)` is an isomorphism on cohomology in degrees `≤ s` and one power of
`J₀ I` annihilates those cohomology modules (the conclusion of Stacks 0DXM), and moreover
`H^i_{J₀}(M)` is a finite `A`-module for every `i ≤ s`.

Hypotheses (1), (3), (4) and the source's standing assumption `I ≠ A` (without which
`V(J₀) ∩ V(I) = {𝔪}` is unattainable) are `LocalStabilizationHypotheses`; (2') is
`DepthAddDimGtAtMaximalIdeal`. The integers `s` and `d` are arbitrary. For `s < 0` the
finiteness is the vanishing of local cohomology in negative degrees; for `d < 0` the hypotheses
force `I` to be nilpotent (`LocalStabilizationHypotheses.mem_zeroLocus_of_neg`). -/
@[stacks 0DXN]
public theorem exists_stabilization_finite_localCohomologyModule_maximalIdeal
    (I : Ideal A) (s d : ℤ) (omega : DerivedCategory (ModuleCat.{u} A))
    (H : LocalStabilizationHypotheses (M := M) I s d omega)
    (h2 : DepthAddDimGtAtMaximalIdeal (M := M) I s) :
    ∃ J₀ : Ideal A, ∃ n : ℕ,
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          {closedPoint A} ∧
        (∀ J : Ideal A, ∀ hJ : J ≤ J₀,
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
            {closedPoint A} →
          ∀ i : ℤ, i ≤ s →
            IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
                (localCohomologyComparison A J₀ J J₀.fg_of_isNoetherianRing
                  J.fg_of_isNoetherianRing hJ
                  ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                    (ModuleCat.of A M)))) ∧
              (J₀ * I) ^ n ≤ Module.annihilator A
                ↥((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
                  ((Dualizing.localCohomologyFunctor A J J.fg_of_isNoetherianRing).obj
                    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                      (ModuleCat.of A M))).obj)) ∧
        ∀ i : ℤ, i ≤ s →
          Module.Finite A
            (localCohomologyModule A J₀ J₀.fg_of_isNoetherianRing (ModuleCat.of A M) i) := by
  have hex := H.exists_isStabilizingData
  have hdata : IsStabilizingData (M := M) I (maximalIdeal A) s
      (stabilizingData I (maximalIdeal A) s d omega H.toStabilizationHypotheses) :=
    isStabilizingData_stabilizingData I (maximalIdeal A) s d omega
      H.toStabilizationHypotheses hex
  refine ⟨stabilizingIdeal I (maximalIdeal A) s d omega H.toStabilizationHypotheses,
    stabilizingPower I (maximalIdeal A) s d omega H.toStabilizationHypotheses,
    zeroLocus_stabilizingIdeal_maximalIdeal_inter I s d omega H, fun J hJ hV i hi ↦ ?_,
    fun i hi ↦ ?_⟩
  · have hV' : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A) ∩
          PrimeSpectrum.zeroLocus (I : Set A) := by
      rw [hV, zeroLocus_maximalIdeal_inter H.ne_top]
    exact ⟨hdata.isIso J hJ hV' i hi, hdata.pow_mul_le_annihilator J hJ hV' i hi⟩
  · rcases le_or_gt 0 s with hs | hs
    · exact finite_localCohomologyModule_stabilizingIdeal_maximalIdeal I s d omega H h2 hs
        (exists_pow_mul_le_annihilator_localCohomologyModule_stabilizingIdeal I
          (maximalIdeal A) s d omega H.toStabilizationHypotheses hex) i hi
    · have := ModuleCat.isZero_iff_subsingleton.mp
        (isZero_localCohomologyModule_of_neg A
          (stabilizingIdeal I (maximalIdeal A) s d omega H.toStabilizationHypotheses)
          (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of A M) i (by omega))
      infer_instance

end Stacks.Algebraization

end
