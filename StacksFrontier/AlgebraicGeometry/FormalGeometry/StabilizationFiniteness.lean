module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Stabilization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence
public import StacksFrontier.RingTheory.LocalCohomology.FaltingsAnnihilator
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessDepthDimension
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison

/-!
# Finiteness of the stabilized local cohomology modules

Let `I` and `J` be ideals of a Noetherian ring `A` with a dualizing complex, let `M` be a finite
`A`-module and fix integers `s` and `d`. Stacks 0EFI selects from `J` a smaller ideal `J₀` with
`V(J₀) ∩ V(I) = V(J) ∩ V(I)`. Stacks 0EFJ replaces the empty condition (2) of that lemma by

(2') `depth_{A_𝔭}(M_𝔭) + dim((A/𝔭)_𝔮) > s` for every `𝔭 ∈ V(I)` outside `V(J) ∩ V(I)` and every
`𝔮 ∈ V(𝔭) ∩ V(J) ∩ V(I)`,

and concludes that `H^i_{J₀}(M)` is a finite `A`-module for `i ≤ s`.

## Main definitions

* `Stacks.Algebraization.DepthAddDimGtOnZeroLocus` — hypothesis (2').

## Main results

* `Stacks.Algebraization.finite_localCohomologyModule_of_exists_pow_mul_le_annihilator` — the
  finiteness statement for an arbitrary ideal `J₀` with the two properties of Stacks 0EFI that
  the argument uses.
* `Stacks.Algebraization.finite_localCohomologyModule_stabilizingIdeal` — the same statement for
  the stabilizing ideal of Stacks 0EFI, on the annihilation clause of that lemma.
* `Stacks.Algebraization.exists_pow_mul_le_annihilator_localCohomologyModule_stabilizingIdeal` —
  the annihilation input is a clause of the conclusion of Stacks 0EFI.
* `Stacks.Algebraization.finite_localCohomologyModule_stabilizingIdeal_of_nonneg` — **Stacks
  0EFJ**, with that input proved rather than assumed.

## Implementation notes

The argument follows the source. Finiteness of `H^i_{J₀}(M)` for `i ≤ s` is Faltings'
finiteness criterion (Stacks 0EFD) for the closed subset `V(J₀)`, so it comes down to
`depth_{A_𝔭}(M_𝔭) + dim((A/𝔭)_𝔮) > s` for every pair `𝔭 ⊆ 𝔮` with `𝔭 ∉ V(J₀)` and `𝔮 ∈ V(J₀)`.
When `𝔭 ∈ V(I)` this is hypothesis (2'): the equality `V(J₀) ∩ V(I) = V(J) ∩ V(I)` puts `𝔭`
outside `V(J) ∩ V(I)` and `𝔮` inside `V(𝔭) ∩ V(J) ∩ V(I)`. When `𝔭 ∉ V(I)` the prime avoids
`V(J₀ I)`, so the inequality follows from Faltings' annihilator theorem (Stacks 0EFC) applied to
`V(J₀) ⊆ V(J₀ I)`, given that a power of `J₀ I` annihilates `H^i_{J₀}(M)` for `i ≤ s`.

That annihilation is the one input the source takes from the cohomological part of Stacks 0EFI.
It is exactly the clause `Stacks.Algebraization.IsStabilizingData.pow_mul_le_annihilator`
evaluated at `J' = J₀`, as
`Stacks.Algebraization.exists_pow_mul_le_annihilator_localCohomologyModule_stabilizingIdeal`
records, so it follows from the existence statement
`Stacks.Algebraization.exists_isStabilizingData` of Stacks 0EFI. It is therefore proved and not
assumed in `Stacks.Algebraization.finite_localCohomologyModule_stabilizingIdeal_of_nonneg`,
which is the form of Stacks 0EFJ this file registers; nothing else of Stacks 0EFI is used beyond
its two unconditional clauses `Stacks.Algebraization.stabilizingIdeal_le` and
`Stacks.Algebraization.zeroLocus_stabilizingIdeal_inter`.
`Stacks.Algebraization.finite_localCohomologyModule_stabilizingIdeal` keeps the annihilation as
a hypothesis, which is what the specialization to `J = 𝔪` in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdealFiniteness` consumes.

Two integer hypotheses attach to the argument and neither survives into Stacks 0EFJ's own
statement. `0 ≤ s` is the hypothesis Stacks 0EFC and Stacks 0EFD assume; it is discharged by a
case split, because in degrees `i ≤ s < 0` the modules `H^i_{J₀}(M)` vanish and finiteness is
free. `0 ≤ d` is the hypothesis of `Stacks.Algebraization.exists_isStabilizingData` and remains:
the source of Stacks 0EFI uses it silently in the step that reads `depth + dim > d + s` as
`depth + dim > s`, and it is not implied by hypotheses (1)–(4), condition (4) being a strict
lower bound on `d + s` and hence monotone downward in `d`.

Depth is measured in `ℕ∞` and relative dimension in `WithBot ℕ∞`; both are compared with the
integer bound `s` inside `EInt`, through `Stacks.Algebraization.enatToEInt` and
`Stacks.Algebraization.krullDimToEInt`, exactly as in the statement of Stacks 0EFI.

## References

* [Stacks Project, Tag 0EFJ](https://stacks.math.columbia.edu/tag/0EFJ)
* [Stacks Project, Tag 0EFI](https://stacks.math.columbia.edu/tag/0EFI)
* [Stacks Project, Tag 0EFD](https://stacks.math.columbia.edu/tag/0EFD)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)

## Tags

local cohomology, depth, finiteness, algebraization
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {M : Type u} [AddCommGroup M] [Module A M]

/-- Hypothesis (2') of Stacks 0EFJ: a prime `𝔭 ∈ V(I)` lying outside `V(J) ∩ V(I)` has
`depth_{A_𝔭}(M_𝔭) + dim((A/𝔭)_𝔮) > s` along every specialization `𝔮 ∈ V(J) ∩ V(I)`. -/
public def DepthAddDimGtOnZeroLocus (I J : Ideal A) (s : ℤ) : Prop :=
  ∀ p : PrimeSpectrum A, p ∈ PrimeSpectrum.zeroLocus (I : Set A) →
    p ∉ PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) →
    ∀ q : PrimeSpectrum A,
      q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
          PrimeSpectrum.zeroLocus (J : Set A)) ∩ PrimeSpectrum.zeroLocus (I : Set A) →
      enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M)) +
        krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
          p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) > (s : EInt)

variable [Module.Finite A M]

/-- **The finiteness argument of Stacks 0EFJ.** Let `J₀` be an ideal with
`V(J₀) ∩ V(I) = V(J) ∩ V(I)` such that one power of `J₀ I` annihilates `H^i_{J₀}(M)` in every
degree `i ≤ s`. Under hypothesis (2') the modules `H^i_{J₀}(M)` are finite for `i ≤ s`. -/
public theorem finite_localCohomologyModule_of_exists_pow_mul_le_annihilator
    (I J J₀ : Ideal A) (s : ℤ) (hs : 0 ≤ s)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hzl : PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (h2 : DepthAddDimGtOnZeroLocus (M := M) I J s)
    (hann : ∃ n : ℕ, ∀ i : ℤ, i ≤ s →
      ((J₀ * I) ^ n : Ideal A) ≤ Module.annihilator A
        (localCohomologyModule A J₀ (Ideal.fg_of_isNoetherianRing J₀) (ModuleCat.of A M) i))
    (i : ℤ) (hi : i ≤ s) :
    Module.Finite A
      (localCohomologyModule A J₀ (Ideal.fg_of_isNoetherianRing J₀) (ModuleCat.of A M) i) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, s = (m : ℤ) := ⟨s.toNat, (Int.toNat_of_nonneg hs).symm⟩
  obtain ⟨n, hn⟩ := hann
  have hsp : ∀ K : Ideal A, StableUnderSpecialization (PrimeSpectrum.zeroLocus (K : Set A)) :=
    fun K ↦ (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization
  have hTT' : PrimeSpectrum.zeroLocus (J₀ : Set A) ⊆
      PrimeSpectrum.zeroLocus ((J₀ * I : Ideal A) : Set A) :=
    PrimeSpectrum.zeroLocus_anti_mono_ideal Ideal.mul_le_left
  have hann' : ∀ i : ℤ, i ≤ (m : ℤ) → ((J₀ * I) ^ n : Ideal A) ≤ Module.annihilator A
      (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (J₀ : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i) := by
    intro i hi
    rw [(localCohomologyWithSupportInIsoLocalCohomologyModule A J₀
      (Ideal.fg_of_isNoetherianRing J₀) (ModuleCat.of A M) i).toLinearEquiv.annihilator_eq]
    exact hn i hi
  have hmem : ∀ (K : Ideal A) (p : PrimeSpectrum A),
      p ∈ PrimeSpectrum.zeroLocus (K : Set A) ↔ K ≤ p.asIdeal := fun K p ↦
    (PrimeSpectrum.mem_zeroLocus p K).trans SetLike.coe_subset_coe
  have hsub : PrimeSpectrum.zeroLocus (((J₀ * I) ^ n : Ideal A) : Set A) ⊆
      PrimeSpectrum.zeroLocus ((J₀ * I : Ideal A) : Set A) := fun p hp ↦
    (hmem _ _).2 (Ideal.IsPrime.le_of_pow_le ((hmem _ _).1 hp))
  have hdepthOut := (Stacks.LocalCohomology.exists_ideal_le_annihilator_localCohomology_iff A M
    (PrimeSpectrum.zeroLocus (J₀ : Set A))
    (PrimeSpectrum.zeroLocus ((J₀ * I : Ideal A) : Set A)) hTT' (hsp _) (hsp _)
    (m : ℤ) (Int.natCast_nonneg m) omega homega).1 ⟨(J₀ * I) ^ n, hsub, hann'⟩
  refine (Module.Finite.equiv_iff (localCohomologyWithSupportInIsoLocalCohomologyModule A J₀
    (Ideal.fg_of_isNoetherianRing J₀) (ModuleCat.of A M) i).toLinearEquiv).mp
    ((Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_iff_depth_add_dim A
      (PrimeSpectrum.zeroLocus (J₀ : Set A)) (hsp _) m M omega homega).2 ?_ i hi)
  intro p q hp hq hpq
  by_cases hpI : p ∈ PrimeSpectrum.zeroLocus (I : Set A)
  · have hqI : q ∈ PrimeSpectrum.zeroLocus (I : Set A) :=
      (hmem _ _).2 (((hmem _ _).1 hpI).trans hpq)
    exact h2 p hpI (fun h ↦ hp (hzl.symm.subset h).1) q
      ⟨⟨(hmem _ _).2 hpq, (hzl.subset ⟨hq, hqI⟩).1⟩, hqI⟩
  · refine hdepthOut p q (fun h ↦ ?_) hq hpq
    rcases (Ideal.IsPrime.mul_le p.isPrime).1 ((hmem _ _).1 h) with h | h
    · exact hp ((hmem _ _).2 h)
    · exact hpI ((hmem _ _).2 h)

section

variable (I J : Ideal A) (s d : ℤ) (omega : DerivedCategory (ModuleCat.{u} A))
  (H : StabilizationHypotheses (M := M) I J s d omega)

/-- **Stacks 0EFJ.** Under hypothesis (2') the local cohomology of `M` supported in the
stabilizing ideal `J₀` of Stacks 0EFI is a finite `A`-module in every degree `i ≤ s`.

The annihilation of `H^i_{J₀}(M)` by a power of `J₀ I` for `i ≤ s` is carried as a hypothesis
here; it is the clause `Stacks.Algebraization.IsStabilizingData.pow_mul_le_annihilator` of the
conclusion of Stacks 0EFI. For the form of Stacks 0EFJ in which it is proved rather than
assumed, see
`Stacks.Algebraization.finite_localCohomologyModule_stabilizingIdeal_of_nonneg`. -/
@[stacks 0EFJ "H^i_{J₀}(M) is a finite A-module for i ≤ s, given the annihilation clause of 0EFI"]
public theorem finite_localCohomologyModule_stabilizingIdeal
    (h2 : DepthAddDimGtOnZeroLocus (M := M) I J s) (hs : 0 ≤ s)
    (hann : ∃ n : ℕ, ∀ i : ℤ, i ≤ s →
      ((stabilizingIdeal I J s d omega H * I) ^ n : Ideal A) ≤ Module.annihilator A
        (localCohomologyModule A (stabilizingIdeal I J s d omega H)
          (Ideal.fg_of_isNoetherianRing (stabilizingIdeal I J s d omega H))
          (ModuleCat.of A M) i))
    (i : ℤ) (hi : i ≤ s) :
    Module.Finite A
      (localCohomologyModule A (stabilizingIdeal I J s d omega H)
        (Ideal.fg_of_isNoetherianRing (stabilizingIdeal I J s d omega H))
        (ModuleCat.of A M) i) :=
  finite_localCohomologyModule_of_exists_pow_mul_le_annihilator I J
    (stabilizingIdeal I J s d omega H) s hs omega H.dualizing
    (zeroLocus_stabilizingIdeal_inter I J s d omega H) h2 hann i hi

/-- The annihilation hypothesis of
`Stacks.Algebraization.finite_localCohomologyModule_stabilizingIdeal` holds as soon as some pair
has the stabilization property of Stacks 0EFI: it is that lemma's uniform annihilation clause
read at `J' = J₀`. -/
public theorem exists_pow_mul_le_annihilator_localCohomologyModule_stabilizingIdeal
    (hstab : ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I J s p) :
    ∃ n : ℕ, ∀ i : ℤ, i ≤ s →
      ((stabilizingIdeal I J s d omega H * I) ^ n : Ideal A) ≤ Module.annihilator A
        (localCohomologyModule A (stabilizingIdeal I J s d omega H)
          (Ideal.fg_of_isNoetherianRing (stabilizingIdeal I J s d omega H))
          (ModuleCat.of A M) i) :=
  ⟨stabilizingPower I J s d omega H, fun i hi ↦
    (isStabilizingData_stabilizingData I J s d omega H hstab).pow_mul_le_annihilator
      (stabilizingIdeal I J s d omega H) le_rfl
      (zeroLocus_stabilizingIdeal_inter I J s d omega H) i hi⟩

/-- **Stacks 0EFJ.** Under hypotheses (1), (3), (4) of Stacks 0EFI together with hypothesis (2')
in place of its empty hypothesis (2), the local cohomology of `M` supported in the stabilizing
ideal `J₀` of Stacks 0EFI is a finite `A`-module in every degree `i ≤ s`.

Nothing is assumed about `H^i_{J₀}(M)`: the annihilation of those modules by a power of `J₀ I`
for `i ≤ s`, which the source takes from Stacks 0EFI, is proved here from
`Stacks.Algebraization.exists_isStabilizingData`, the existence statement of that lemma. The
only hypothesis beyond those of the source is `0 ≤ d`, which Stacks 0EFI needs and which the
source uses silently when it reads `depth + dim > d + s` as `depth + dim > s`; see the module
documentation. In particular `0 ≤ s` is not assumed: in degrees `i ≤ s < 0` local cohomology
vanishes, so the statement is free there. -/
@[stacks 0EFJ "H^i_{J₀}(M) is a finite A-module for i ≤ s, for 0 ≤ d"]
public theorem finite_localCohomologyModule_stabilizingIdeal_of_nonneg
    (h2 : DepthAddDimGtOnZeroLocus (M := M) I J s) (hd : 0 ≤ d)
    (i : ℤ) (hi : i ≤ s) :
    Module.Finite A
      (localCohomologyModule A (stabilizingIdeal I J s d omega H)
        (Ideal.fg_of_isNoetherianRing (stabilizingIdeal I J s d omega H))
        (ModuleCat.of A M) i) := by
  by_cases hs : 0 ≤ s
  · exact finite_localCohomologyModule_stabilizingIdeal I J s d omega H h2 hs
      (exists_pow_mul_le_annihilator_localCohomologyModule_stabilizingIdeal I J s d omega H
        (exists_isStabilizingData I J s d hd omega H)) i hi
  · have := ModuleCat.isZero_iff_subsingleton.mp
      (Stacks.LocalCohomology.isZero_localCohomologyModule_of_neg A
        (stabilizingIdeal I J s d omega H)
        (Ideal.fg_of_isNoetherianRing (stabilizingIdeal I J s d omega H))
        (ModuleCat.of A M) i (hi.trans_lt (not_le.mp hs)))
    infer_instance

end

end Stacks.Algebraization

end
