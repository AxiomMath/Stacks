module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Stabilization

/-!
# Stabilization of local cohomology at the maximal ideal of a local ring

Let `(A, 𝔪)` be a Noetherian local ring, let `I ⊂ A` be an ideal, let `M` be a finite
`A`-module and fix integers `s` and `d`. Stacks 0DXM asserts, under a dualizing-complex
hypothesis and depth and dimension bounds on the primes outside `V(I)`, that there is an ideal
`J₀` with `V(J₀) ∩ V(I) = {𝔪}` such that every further ideal `J ⊆ J₀` with
`V(J) ∩ V(I) = {𝔪}` has `RΓ_{J₀}(M) → RΓ_J(M)` an isomorphism in degrees `≤ s`, and such that
a single power of `J₀ I` annihilates all of those cohomology modules.

The source proves this as the case `J = 𝔪` of Stacks 0EFI, whose subset `T` of Stacks 0EFG is
`Stacks.Algebraization.associatedSubset`. This file carries out that specialization: it states
hypotheses (1)–(4) of Stacks 0DXM and identifies them with the hypotheses of Stacks 0EFI at
`J = 𝔪`, and it transports the conclusion of Stacks 0EFI back along that identification.

## Main definitions

* `Stacks.Algebraization.LocalStabilizationHypotheses` — the dualizing, dimension and depth
  hypotheses (1)–(4) of Stacks 0DXM.

## Main results

* `Stacks.Algebraization.localStabilizationHypotheses_iff` — hypotheses (1)–(4) of Stacks 0DXM
  are exactly `I ≠ A` together with the hypotheses of Stacks 0EFI for `J = 𝔪`.
* `Stacks.Algebraization.zeroLocus_stabilizingIdeal_maximalIdeal_inter` — the ideal selected at
  `J = 𝔪` satisfies `V(J₀) ∩ V(I) = {𝔪}`, the first clause of the conclusion.
* `Stacks.Algebraization.exists_stabilization_of_exists` — the whole conclusion of Stacks
  0DXM, deduced from the existence statement of Stacks 0EFI at `J = 𝔪`.

## Implementation notes

`V(J₀) ∩ V(I) = {𝔪}` forces `𝔪 ∈ V(I)`, so the source statement is false for `I = A`, where
`V(I)` is empty; the hypotheses therefore carry `I ≠ ⊤`, which in a local ring is `I ⊆ 𝔪`. Two
further points of the source statement are normalized here. Its `T` of Stacks 0EFG specializes
at `J = 𝔪` to the primes `𝔭` with `V(𝔭) ∩ V(I) = {𝔪}`, which is the form conditions (3) and
(4) are phrased in, and `mem_associatedSubset_maximalIdeal_iff` records the identification. And
`dim((A/𝔭)_𝔮)` of Stacks 0EFI has only `𝔮 = 𝔪` available at `J = 𝔪`, where it is `dim(A/𝔭)`;
`ringKrullDim_localization_maximalIdeal_quotient_map` records that.

The arrow of the conclusion is `RΓ_{J₀}(M) → RΓ_J(M)` for `J ⊆ J₀`, as in Stacks 0EFI and as in
`Stacks.Algebraization.localCohomologyComparison`. The source writes 0DXM's arrow in the other
direction, which is the direction in which there is no canonical map: `J ⊆ J₀` gives
`V(J₀) ⊆ V(J)`, and sections supported in the smaller closed set are sections supported in the
larger one, not conversely.

The cohomological half of the conclusion is stated here conditionally on
`∃ p, IsStabilizingData I 𝔪 s p`, the existence statement of Stacks 0EFI, because the proof of
that statement lives downstream of this file; only the clauses that hold for the junk value of
`Stacks.Algebraization.stabilizingData` are unconditional here. The hypothesis is discharged,
and the conclusion of Stacks 0DXM proved outright, by
`Stacks.Algebraization.exists_stabilization` in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdealExistence`.

## References

* [Stacks Project, Tag 0DXM](https://stacks.math.columbia.edu/tag/0DXM)
* [Stacks Project, Tag 0EFI](https://stacks.math.columbia.edu/tag/0EFI)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing PrimeSpectrum

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.Algebraization

section Spectrum

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- In a local ring the closed point lies on the zero locus of every proper ideal. -/
public theorem closedPoint_mem_zeroLocus {J : Ideal A} (hJ : J ≠ ⊤) :
    closedPoint A ∈ PrimeSpectrum.zeroLocus (J : Set A) := by
  simp only [mem_zeroLocus, SetLike.coe_subset_coe]
  exact IsLocalRing.le_maximalIdeal hJ

/-- The zero locus of the maximal ideal of a local ring is the closed point. -/
public theorem zeroLocus_maximalIdeal :
    PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A) = {closedPoint A} := by
  ext p
  simp only [mem_zeroLocus, Set.mem_singleton_iff, SetLike.coe_subset_coe]
  exact ⟨fun h ↦ PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal p.2.ne_top) h),
    fun h ↦ h ▸ le_rfl⟩

/-- For a proper ideal `I` of a local ring, `V(𝔪) ∩ V(I)` is the closed point. -/
public theorem zeroLocus_maximalIdeal_inter {I : Ideal A} (hI : I ≠ ⊤) :
    PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A) = {closedPoint A} := by
  rw [zeroLocus_maximalIdeal]
  exact Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr (closedPoint_mem_zeroLocus hI))

/-- At `J = 𝔪` the subset `T` of Stacks 0EFG consists of the primes `𝔭` whose closed set meets
`V(I)` only in the maximal ideal. -/
public theorem mem_associatedSubset_maximalIdeal_iff {I : Ideal A} (hI : I ≠ ⊤)
    (p : PrimeSpectrum A) :
    p ∈ associatedSubset I (maximalIdeal A) ↔
      PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        {closedPoint A} := by
  have hdef : p ∈ associatedSubset I (maximalIdeal A) ↔
      PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ⊆
        PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A) ∩
          PrimeSpectrum.zeroLocus (I : Set A) := Iff.rfl
  have hmem : {closedPoint A} ⊆ PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A) :=
    Set.singleton_subset_iff.2
      ⟨closedPoint_mem_zeroLocus p.2.ne_top, closedPoint_mem_zeroLocus hI⟩
  rw [hdef, zeroLocus_maximalIdeal_inter hI]
  exact ⟨fun h ↦ Set.Subset.antisymm h hmem, fun h ↦ h.le⟩

/-- A point of the zero locus of the maximal ideal is the closed point. -/
public theorem eq_closedPoint_of_mem_zeroLocus_maximalIdeal {q : PrimeSpectrum A}
    (hq : q ∈ PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A)) :
    q = closedPoint A := by
  rwa [zeroLocus_maximalIdeal, Set.mem_singleton_iff] at hq

/-- Localizing a local ring at its maximal ideal leaves the dimension of a quotient unchanged:
`dim((A/𝔭)_𝔪) = dim(A/𝔭)`. -/
public theorem ringKrullDim_localization_maximalIdeal_quotient_map (p : Ideal A) :
    ringKrullDim ((Localization.AtPrime (maximalIdeal A)) ⧸
        p.map (algebraMap A (Localization.AtPrime (maximalIdeal A)))) =
      ringKrullDim (A ⧸ p) := by
  set L := Localization.AtPrime (maximalIdeal A)
  have e : A ≃ₐ[A] L :=
    IsLocalization.atUnits A (maximalIdeal A).primeCompl (fun x ↦ by simpa using! fun a ↦ a)
  have hcoe : ∀ x : A, e x = algebraMap A L x := fun x ↦ e.commutes x
  have hbij : Function.Bijective (algebraMap A L) := by
    have := e.bijective
    simpa [funext hcoe] using this
  exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv p (p.map (algebraMap A L))
    (RingEquiv.ofBijective (algebraMap A L) hbij) rfl)).symm

/-- The same dimension comparison, phrased at a point of `Spec(A)` known to be the closed
point, which is the form the hypotheses of Stacks 0EFI present it in. -/
public theorem ringKrullDim_localization_quotient_map_of_eq_closedPoint
    {q : PrimeSpectrum A} (hq : q = closedPoint A) (p : Ideal A) :
    ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
        p.map (algebraMap A (Localization.AtPrime q.asIdeal))) = ringKrullDim (A ⧸ p) := by
  subst hq
  exact ringKrullDim_localization_maximalIdeal_quotient_map p

end Spectrum

/-- The dualizing-complex, dimension and depth hypotheses (1)–(4) of Stacks 0DXM for a
Noetherian local ring `(A, 𝔪)`.

Primes in `V(I)` carry no condition. A prime `𝔭 ∉ V(I)` with `V(𝔭) ∩ V(I) = {𝔪}` must have
`dim(A/𝔭) ≤ d`. A prime `𝔭 ∉ V(I)` with `V(𝔭) ∩ V(I) ≠ {𝔪}` must have `depth(M_𝔭) ≥ s` or
`depth(M_𝔭) + dim(A/𝔭) > d + s`. The source's standing assumption that `I` is a proper ideal
is recorded as `ne_top`; without it `V(I)` is empty and the conclusion is unattainable. -/
public structure LocalStabilizationHypotheses
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{w} A)) : Prop where
  /-- The ideal `I` is proper, so that `𝔪 ∈ V(I)`. -/
  ne_top : I ≠ ⊤
  /-- The ring has a dualizing complex, witnessed by `omega`. -/
  dualizing : Dualizing.IsDualizingComplex omega
  /-- A prime outside `V(I)` whose closed set meets `V(I)` only in `𝔪` has `dim(A/𝔭) ≤ d`. -/
  dimensionBound : ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        {closedPoint A} →
      krullDimToEInt (ringKrullDim (A ⧸ p.asIdeal)) ≤ (d : EInt)
  /-- A prime outside `V(I)` whose closed set meets `V(I)` in more than `𝔪` has depth at least
  `s`, or depth plus the dimension of `A/𝔭` exceeding `d + s`. -/
  depthOrDimensionBound : ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ≠
        {closedPoint A} →
      ((enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) ≥ (s : EInt)) ∨
        (enatToEInt
            (Module.depth (Localization.AtPrime p.asIdeal)
              (maximalIdeal (Localization.AtPrime p.asIdeal))
              (LocalizedModule p.asIdeal.primeCompl M)) +
            krullDimToEInt (ringKrullDim (A ⧸ p.asIdeal)) > ((d + s : ℤ) : EInt)))

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **Stacks 0DXM.** Hypotheses (1)–(4) of the lemma are exactly the properness of `I` together
with the hypotheses of Stacks 0EFI for `J = 𝔪`.

This biconditional is the content of the source's proof, which reads "this is a special case of
Lemma 0EFI": at `J = 𝔪` the set `V(𝔭) ∩ V(𝔪) ∩ V(I)` of Stacks 0EFI is the single point `𝔪`,
where its relative dimension `dim((A/𝔭)_𝔮)` is `dim(A/𝔭)`. -/
@[stacks 0DXM "the hypotheses, identified with those of Stacks 0EFI at J = 𝔪"]
public theorem localStabilizationHypotheses_iff (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{w} A)) :
    LocalStabilizationHypotheses (M := M) I s d omega ↔
      (I ≠ ⊤ ∧ StabilizationHypotheses (M := M) I (maximalIdeal A) s d omega) := by
  have hcp : ∀ p : PrimeSpectrum A, I ≠ ⊤ → closedPoint A ∈
      (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
        PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A)) ∩
        PrimeSpectrum.zeroLocus (I : Set A) := fun p hI ↦
    ⟨⟨closedPoint_mem_zeroLocus p.2.ne_top,
      closedPoint_mem_zeroLocus (IsLocalRing.maximalIdeal.isMaximal A).ne_top⟩,
      closedPoint_mem_zeroLocus hI⟩
  constructor
  · intro H
    refine ⟨H.ne_top, H.dualizing, ?_, ?_⟩
    · intro p hp hT
      refine ⟨closedPoint A, hcp p H.ne_top, ?_⟩
      rw [ringKrullDim_localization_quotient_map_of_eq_closedPoint rfl]
      exact H.dimensionBound p hp ((mem_associatedSubset_maximalIdeal_iff H.ne_top p).1 hT)
    · intro p hp hT
      rcases H.depthOrDimensionBound p hp
        (fun h ↦ hT ((mem_associatedSubset_maximalIdeal_iff H.ne_top p).2 h)) with h | h
      · exact Or.inl h
      · refine Or.inr fun q hq ↦ ?_
        rwa [ringKrullDim_localization_quotient_map_of_eq_closedPoint
          (eq_closedPoint_of_mem_zeroLocus_maximalIdeal hq.1.2)]
  · rintro ⟨hI, H⟩
    refine ⟨hI, H.dualizing, ?_, ?_⟩
    · intro p hp hT
      obtain ⟨q, hq, hd⟩ :=
        H.dimensionBound p hp ((mem_associatedSubset_maximalIdeal_iff hI p).2 hT)
      rwa [ringKrullDim_localization_quotient_map_of_eq_closedPoint
        (eq_closedPoint_of_mem_zeroLocus_maximalIdeal hq.1.2)] at hd
    · intro p hp hT
      rcases H.depthOrDimensionBound p hp
        (fun h ↦ hT ((mem_associatedSubset_maximalIdeal_iff hI p).1 h)) with h | h
      · exact Or.inl h
      · refine Or.inr ?_
        have hval := h (closedPoint A) (hcp p hI)
        rwa [ringKrullDim_localization_quotient_map_of_eq_closedPoint rfl] at hval

/-- The hypotheses of Stacks 0EFI at `J = 𝔪` carried by the hypotheses of Stacks 0DXM. -/
public theorem LocalStabilizationHypotheses.toStabilizationHypotheses
    {I : Ideal A} {s d : ℤ} {omega : DerivedCategory (ModuleCat.{w} A)}
    (H : LocalStabilizationHypotheses (M := M) I s d omega) :
    StabilizationHypotheses (M := M) I (maximalIdeal A) s d omega :=
  ((localStabilizationHypotheses_iff I s d omega).1 H).2

/-- **Stacks 0DXM.** The ideal that Stacks 0EFI selects at `J = 𝔪` meets `V(I)` in the closed
point only, which is the first clause of the conclusion of the lemma. -/
@[stacks 0DXM "the ideal J₀, with V(J₀) ∩ V(I) = {𝔪}"]
public theorem zeroLocus_stabilizingIdeal_maximalIdeal_inter (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{w} A))
    (H : LocalStabilizationHypotheses (M := M) I s d omega) :
    PrimeSpectrum.zeroLocus
          ((stabilizingIdeal I (maximalIdeal A) s d omega
            H.toStabilizationHypotheses : Ideal A) : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) = {closedPoint A} := by
  rw [zeroLocus_stabilizingIdeal_inter, zeroLocus_maximalIdeal_inter H.ne_top]

/-- The whole conclusion of Stacks 0DXM, deduced from the existence statement of Stacks 0EFI at
`J = 𝔪`, which is the only input of the source proof that is not available here. -/
public theorem exists_stabilization_of_exists (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{w} A))
    (H : LocalStabilizationHypotheses (M := M) I s d omega)
    (hex : ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I (maximalIdeal A) s p) :
    ∃ J₀ : Ideal A, ∃ n : ℕ,
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          {closedPoint A} ∧
        ∀ J : Ideal A, ∀ hJ : J ≤ J₀,
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
            {closedPoint A} →
          ∀ i : ℤ, i ≤ s →
            IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
                (localCohomologyComparison A J₀ J J₀.fg_of_isNoetherianRing
                  J.fg_of_isNoetherianRing hJ
                  ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
                    (ModuleCat.of A M)))) ∧
              (J₀ * I) ^ n ≤ Module.annihilator A
                ↥((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj
                  ((Dualizing.localCohomologyFunctor A J J.fg_of_isNoetherianRing).obj
                    ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
                      (ModuleCat.of A M))).obj) := by
  have hdata : IsStabilizingData (M := M) I (maximalIdeal A) s
      (stabilizingData I (maximalIdeal A) s d omega H.toStabilizationHypotheses) :=
    isStabilizingData_stabilizingData I (maximalIdeal A) s d omega
      H.toStabilizationHypotheses hex
  refine ⟨(stabilizingData I (maximalIdeal A) s d omega H.toStabilizationHypotheses).1,
    (stabilizingData I (maximalIdeal A) s d omega H.toStabilizationHypotheses).2,
    ?_, fun J hJ hV i hi ↦ ?_⟩
  · rw [hdata.zeroLocus_inter, zeroLocus_maximalIdeal_inter H.ne_top]
  · have hV' : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A) ∩
          PrimeSpectrum.zeroLocus (I : Set A) := by
      rw [hV, zeroLocus_maximalIdeal_inter H.ne_top]
    exact ⟨hdata.isIso J hJ hV' i hi, hdata.pow_mul_le_annihilator J hJ hV' i hi⟩

end

end Stacks.Algebraization
