module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence.DepthLocus
import all StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence.DepthLocus
import all StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationDepthCollapse
import all StacksFrontier.RingTheory.LocalCohomology.FaltingsAnnihilator

/-!
# The candidate ideal of Stacks 0EFI and the case `s ≤ 0`

The subset `T` of Stacks 0EFG, the set `B` of the source and the candidate ideal
`J₀ = J ⊓ I(B)` it cuts out, the hypotheses of Stacks 0EFI at a negative `d`, the finiteness of
the range of a dimension function, Claims I and II of Stacks 0EFI, and the existence of the
stabilizing data for `s ≤ 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Topology TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.Algebraization

/-! ### The subset `T` of Stacks 0EFG -/

/-- The subset `T` of Stacks 0EFG is stable under specialization. -/
private theorem associatedSubset_stableUnderSpecialization
    {A : Type u} [CommRing A] (I J : Ideal A) :
    StableUnderSpecialization (associatedSubset I J) := by
  intro p q hpq hp
  show PrimeSpectrum.zeroLocus (q.asIdeal : Set A) ∩
    PrimeSpectrum.zeroLocus (I : Set A) ⊆ _
  exact fun r hr => hp ⟨((PrimeSpectrum.le_iff_specializes p q).mpr hpq).trans hr.1, hr.2⟩

/-- Every prime of `V(J')` lies in `T` as soon as `V(J') ∩ V(I) = V(J) ∩ V(I)`. -/
private theorem mem_associatedSubset_of_mem_zeroLocus_inter
    {A : Type u} [CommRing A] (I J J' : Ideal A)
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A))
    (p : PrimeSpectrum A) (hp : p ∈ PrimeSpectrum.zeroLocus (J' : Set A)) :
    p ∈ associatedSubset I J := by
  show PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A) ⊆
    PrimeSpectrum.zeroLocus (J : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A)
  intro q hq
  have hqJ' : q ∈ PrimeSpectrum.zeroLocus (J' : Set A) :=
    (show J' ≤ p.asIdeal from hp).trans hq.1
  exact hV.subset ⟨hqJ', hq.2⟩

/-- A prime of `V(J')` outside `V(J₀)` lies outside `V(I)` and inside `T`, for `J₀` and `J'` both
admissible shrinkings of `J`. These are the primes at which Stacks 0DWV asks for vanishing. -/
private theorem prime_mem_associatedSubset_not_mem_zeroLocus
    {A : Type u} [CommRing A] (I J J₀ J' : Ideal A)
    (hzero : PrimeSpectrum.zeroLocus (J₀ : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (p : PrimeSpectrum A) (hpJ' : J' ≤ p.asIdeal)
    (hp : ¬ J₀ ≤ p.asIdeal) :
    p ∉ PrimeSpectrum.zeroLocus (I : Set A) ∧ p ∈ associatedSubset I J := by
  have hpJ' : p ∈ PrimeSpectrum.zeroLocus (J' : Set A) := hpJ'
  exact ⟨fun hpI => hp (hzero.symm.subset (hV.subset ⟨hpJ', hpI⟩)).1,
    mem_associatedSubset_of_mem_zeroLocus_inter I J J' hV p hpJ'⟩

/-! ### The set `B` of the source and the ideal it cuts out -/

/-- The set `B` of Stacks 0EFI: the primes outside `V(I)` that lie in `T` and at which the depth
of `M` is at most `s`. -/
private def badLocus
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s : ℤ) :
    Set (PrimeSpectrum A) := {p | p ∉ PrimeSpectrum.zeroLocus (I : Set A) ∧
      p ∈ associatedSubset I J ∧
      enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M)) ≤ (s : EInt)}

/-- The ideal `J₀` of Stacks 0EFI: the ideal cutting out the closure of `B ∪ V(J)`. -/
private def stabilizingIdealCandidate
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s : ℤ) : Ideal A :=
  J ⊓ PrimeSpectrum.vanishingIdeal (badLocus (M := M) I J s)

private theorem stabilizingIdealCandidate_le
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s : ℤ) :
    stabilizingIdealCandidate (M := M) I J s ≤ J := inf_le_left

private theorem zeroLocus_stabilizingIdealCandidate
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s : ℤ) :
    PrimeSpectrum.zeroLocus (stabilizingIdealCandidate (M := M) I J s : Set A) =
      closure (badLocus (M := M) I J s) ∪ PrimeSpectrum.zeroLocus (J : Set A) := by
  rw [stabilizingIdealCandidate, PrimeSpectrum.zeroLocus_inf,
    PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  exact Set.union_comm _ _

private theorem badLocus_subset_zeroLocus_stabilizingIdealCandidate
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s : ℤ) :
    badLocus (M := M) I J s ⊆
      PrimeSpectrum.zeroLocus (stabilizingIdealCandidate (M := M) I J s : Set A) := by
  rw [zeroLocus_stabilizingIdealCandidate]
  exact Set.Subset.trans subset_closure Set.subset_union_left

/-- If the closure of `B` lies in `T`, shrinking `J` to the candidate ideal does not change the
intersection of the zero locus with `V(I)`. -/
private theorem zeroLocus_stabilizingIdealCandidate_inter_of_closure_subset
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s : ℤ)
    (hclosure : closure (badLocus (M := M) I J s) ⊆ associatedSubset I J) :
    PrimeSpectrum.zeroLocus (stabilizingIdealCandidate (M := M) I J s : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) := by
  rw [zeroLocus_stabilizingIdealCandidate]
  refine Set.Subset.antisymm ?_ fun _ hp => ⟨Or.inr hp.1, hp.2⟩
  rintro p ⟨hp | hp, hpI⟩
  · exact hclosure hp ⟨fun _ hx => hx, hpI⟩
  · exact ⟨hp, hpI⟩

/-- **Claim I of Stacks 0EFI for `s ≤ 0`.** Shrinking `J` to the candidate ideal does not change
the intersection of the zero locus with `V(I)`.

The generic points of `closure B` lie in `B` itself, because a generic point outside `B` would
have `depth(M_𝔭) < s ≤ 0` by `depth_lt_of_mem_closure_of_bounded_depth`, and depth takes no
negative value. So `closure B ⊆ T`, and a prime of `T ∩ V(I)` lies in `V(J)` by the definition
of `T`. -/
private theorem zeroLocus_stabilizingIdealCandidate_inter_of_nonpos
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s : ℤ) (hs : s ≤ 0) :
    PrimeSpectrum.zeroLocus (stabilizingIdealCandidate (M := M) I J s : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) := by
  have hclosure : closure (badLocus (M := M) I J s) ⊆ associatedSubset I J := by
    refine closure_subset_of_generic_mem _ _
      (associatedSubset_stableUnderSpecialization I J) ?_
    intro p hp
    by_cases hpB : p ∈ badLocus (M := M) I J s
    · exact hpB.2.1
    · exact absurd (depth_lt_of_mem_closure_of_bounded_depth p s
        (Subtype.val ⁻¹' badLocus (M := M) I J s) (fun q hq => hq.2.2) hp hpB)
        (not_enatToEInt_lt_intCast _ hs)
  exact zeroLocus_stabilizingIdealCandidate_inter_of_closure_subset I J s hclosure

/-! ### The hypotheses of Stacks 0EFI at a negative `d` -/

/-- **Hypothesis (3) of Stacks 0EFI at a negative `d` is an exclusion, not a bound.** A relative
dimension `dim((A/𝔭)_𝔮)` is never negative, so no prime has a specialization in
`V(𝔭) ∩ V(J) ∩ V(I)` of relative dimension at most `d < 0`; hypothesis (3) therefore says that
every prime of `T` lies in `V(I)`. -/
private theorem associatedSubset_subset_zeroLocus_of_neg
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s d : ℤ) (hd : d < 0)
    (omega : DerivedCategory (ModuleCat.{w} A))
    (H : StabilizationHypotheses (M := M) I J s d omega) :
    associatedSubset I J ⊆ PrimeSpectrum.zeroLocus (I : Set A) := by
  intro p hp
  by_contra hpI
  obtain ⟨q, hq, hdim⟩ := H.dimensionBound p hpI hp
  have h0 := (zero_le_krullDimToEInt_localization_quotient p q hq.1.1).trans hdim
  change ((0 : ℤ) : EInt) ≤ (d : EInt) at h0
  exact absurd (WithBotTop.coe_le_coe.mp h0) (by omega)

/-- **The set `B` of Stacks 0EFI is empty when `d < 0`.** Its members lie outside `V(I)` and
inside `T`, and hypothesis (3) at a negative `d` leaves no such prime. -/
private theorem badLocus_eq_empty_of_neg
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s d : ℤ) (hd : d < 0)
    (omega : DerivedCategory (ModuleCat.{w} A))
    (H : StabilizationHypotheses (M := M) I J s d omega) :
    badLocus (M := M) I J s = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun p hp => hp.1 ?_
  exact associatedSubset_subset_zeroLocus_of_neg I J s d hd omega H hp.2.1

/-- **The candidate ideal of Stacks 0EFI cuts out `V(J)` when `d < 0`.** There is nothing to add
to `V(J)`: the set `B` whose closure it absorbs is empty. -/
private theorem zeroLocus_stabilizingIdealCandidate_of_neg
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s d : ℤ) (hd : d < 0)
    (omega : DerivedCategory (ModuleCat.{w} A))
    (H : StabilizationHypotheses (M := M) I J s d omega) :
    PrimeSpectrum.zeroLocus (stabilizingIdealCandidate (M := M) I J s : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) := by
  rw [zeroLocus_stabilizingIdealCandidate, badLocus_eq_empty_of_neg I J s d hd omega H,
    closure_empty, Set.empty_union]

/-! ### The dimension function and relative dimension -/

/-- A dimension function does not increase along a specialization. -/
private theorem dimensionFunction_le_of_le
    {A : Type u} [CommRing A]
    (δ : TopologicalSpace.DimensionFunction (PrimeSpectrum A))
    {p q : PrimeSpectrum A} (hpq : p.asIdeal ≤ q.asIdeal) : δ q ≤ δ p := by
  rcases eq_or_ne p q with rfl | hne
  · exact le_rfl
  · exact (δ.strictAnti_specializes ((PrimeSpectrum.le_iff_specializes p q).mp hpq) hne).le

/-- **The relative dimension as a difference of dimension-function values.** For `𝔭 ⊆ 𝔮` and a
dimension function `δ` on `Spec A`, the dimension of `(A/𝔭)_𝔮` is `δ(𝔭) - δ(𝔮)`.

The spectrum of `(A/𝔭)_𝔮` is the interval `[𝔭, 𝔮]`, whose Krull dimension a dimension function
computes as that difference. -/
private theorem krullDimToEInt_localization_quotient_eq_dimensionFunction
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (δ : TopologicalSpace.DimensionFunction (PrimeSpectrum A))
    (p q : PrimeSpectrum A) (hpq : p.asIdeal ≤ q.asIdeal) :
    krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
        p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) =
      ((δ p - δ q : ℤ) : EInt) := by
  have hprime : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hpq
  have hheight := IsLocalization.AtPrime.ringKrullDim_eq_height
    (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal))
    (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)))
  have hδ := Stacks.LocalCohomology.ringKrullDim_localizedQuotient_eq_dimensionFunction
    δ p q hpq
  rw [ringKrullDim_localization_quotient_eq_height p q hpq, ← hheight, hδ,
    krullDimToEInt_natCast]
  have hle : δ q ≤ δ p := dimensionFunction_le_of_le δ hpq
  exact congrArg (fun z : ℤ => (z : EInt)) (by omega)

/-- **A dimension function on the spectrum of a Noetherian ring of finite dimension has finite
range.** The values of a dimension function on a chain are bounded in terms of the length of the
chain, so a bound on the Krull dimension bounds the whole range in an interval. -/
theorem finite_range_dimensionFunction_of_ringKrullDim_lt_top
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (δ : TopologicalSpace.DimensionFunction (PrimeSpectrum A))
    (hA : ringKrullDim A < ⊤) : (Set.range δ.toFun).Finite := by
  have hN : ∃ N : ℕ, ringKrullDim A ≤ ((N : ℕ) : WithBot ℕ∞) := by
    generalize hr : ringKrullDim A = r at hA ⊢
    cases r using WithBotTop.rec with
    | bot => exact ⟨0, bot_le⟩
    | top => exact absurd hA (lt_irrefl _)
    | coe n => exact ⟨n, le_rfl⟩
  obtain ⟨N, hN⟩ := hN
  obtain ⟨a, b, hab⟩ := Stacks.LocalCohomology.bdd_dimensionFunction_of_krullDim_le δ N hN
  refine (Set.finite_Icc a b).subset ?_
  rintro z ⟨r, rfl⟩
  exact ⟨(hab r).1, (hab r).2⟩

/-! ### Claim I of Stacks 0EFI -/

/-- **A dimension function on the spectrum of a Noetherian ring of finite dimension has finite
range.** -/
alias finite_range_dimensionFunction := finite_range_dimensionFunction_of_ringKrullDim_lt_top

/-- Every prime of `V(J)` lies in `T`. -/
private theorem zeroLocus_subset_associatedSubset
    {A : Type u} [CommRing A] (I J : Ideal A) :
    PrimeSpectrum.zeroLocus (J : Set A) ⊆ associatedSubset I J := by
  intro p hp q hq
  exact ⟨(show J ≤ p.asIdeal from hp).trans hq.1, hq.2⟩

/-- **Claim I of Stacks 0EFI, at a generic point.** A prime which is a generic point of the
closure of `B` inside `V(𝔭)` lies in `T`.

If `𝔭 ∈ B` there is nothing to do. If not, `depth(M_𝔭) < s` by Stacks 0DWY, so `𝔭 ∉ V(I)`
forces, through hypothesis (4), the inequality
`depth(M_𝔭) + dim((A/𝔭)_𝔮) > d + s` at some specialization `𝔮 ∈ V(J) ∩ V(I)`. On the other hand
`𝔭` lies in the closure of those `𝔟 ∈ B` whose chosen specialization `𝔮_𝔟` of hypothesis (3)
has one fixed value `δ(𝔮_𝔟) = c` — such a value exists because `δ` has finite range — and on
that set `depth(M_𝔟) + δ(𝔟) ≤ d + s + c`. Semicontinuity of `depth + δ` carries the bound to
`𝔭`, contradicting the strict inequality. -/
private theorem mem_associatedSubset_of_mem_closure_badLocus_at_prime
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (H : StabilizationHypotheses (M := M) I J s d omega)
    (δ : PrimeSpectrum A → ℤ) (hδ : (Set.range δ).Finite)
    (hdim : ∀ p q : PrimeSpectrum A, p.asIdeal ≤ q.asIdeal →
      krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
        p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) =
        ((δ p - δ q : ℤ) : EInt))
    (hclosed : ∀ c : ℤ, IsClosed {p : PrimeSpectrum A | ∃ n : ℕ,
      Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) = (n : ℕ∞) ∧ (n : ℤ) + δ p ≤ c})
    (p : PrimeSpectrum A)
    (hp : (⟨p, fun _ hx => hx⟩ : ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A))) ∈
      closure (Subtype.val ⁻¹' badLocus (M := M) I J s)) :
    p ∈ associatedSubset I J := by
  classical
  by_cases hpB : p ∈ badLocus (M := M) I J s
  · exact hpB.2.1
  have hpdepth := depth_lt_of_mem_closure_of_bounded_depth p s
    (Subtype.val ⁻¹' badLocus (M := M) I J s) (fun q hq => hq.2.2) hp hpB
  let C (c : ℤ) : Set (PrimeSpectrum A) := {b | p.asIdeal ≤ b.asIdeal ∧
    b ∈ badLocus (M := M) I J s ∧ ∃ q : PrimeSpectrum A,
      q ∈ (PrimeSpectrum.zeroLocus (b.asIdeal : Set A) ∩
        PrimeSpectrum.zeroLocus (J : Set A)) ∩ PrimeSpectrum.zeroLocus (I : Set A) ∧
      krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
        b.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) ≤ (d : EInt) ∧
      δ q = c}
  have hcover : Subtype.val ''
      (Subtype.val ⁻¹' badLocus (M := M) I J s :
        Set ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A))) ⊆ ⋃ c ∈ Set.range δ, C c := by
    rintro b ⟨b', hb', rfl⟩
    obtain ⟨q, hq, hqdim⟩ := H.dimensionBound b'.1 hb'.1 hb'.2.1
    exact Set.mem_iUnion₂.mpr ⟨δ q, ⟨q, rfl⟩, b'.2, hb', q, hq, hqdim, rfl⟩
  have hpcover : p ∈ closure (⋃ c ∈ Set.range δ, C c) := by
    refine closure_mono hcover ?_
    rwa [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image] at hp
  rw [hδ.closure_biUnion] at hpcover
  obtain ⟨c, -, hpc⟩ := Set.mem_iUnion₂.mp hpcover
  have hCbound : C c ⊆ {b : PrimeSpectrum A | ∃ n : ℕ,
      Module.depth (Localization.AtPrime b.asIdeal)
        (maximalIdeal (Localization.AtPrime b.asIdeal))
        (LocalizedModule b.asIdeal.primeCompl M) = (n : ℕ∞) ∧
        (n : ℤ) + δ b ≤ d + s + c} := by
    rintro b ⟨-, hb, q, hq, hqdim, hqc⟩
    obtain ⟨n, hn, hns⟩ := (enatToEInt_le_intCast_iff _ s).mp hb.2.2
    rw [hdim b q hq.1.1] at hqdim
    have hdle : δ b - δ q ≤ d := WithBotTop.coe_le_coe.mp hqdim
    exact ⟨n, hn, by omega⟩
  obtain ⟨n, hn, hnbound⟩ := closure_minimal hCbound (hclosed (d + s + c)) hpc
  obtain ⟨b, hpb, hb, q, hq, -, hqc⟩ := closure_nonempty_iff.mp ⟨p, hpc⟩
  have hpI : p ∉ PrimeSpectrum.zeroLocus (I : Set A) := by
    intro hpI
    exact hb.1 ((show I ≤ p.asIdeal from hpI).trans hpb)
  by_contra hpT
  rcases H.depthOrDimensionBound p hpI hpT with hdepth | hbound
  · exact (not_le_of_gt hpdepth) hdepth
  have hq' : q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
      PrimeSpectrum.zeroLocus (J : Set A)) ∩ PrimeSpectrum.zeroLocus (I : Set A) :=
    ⟨⟨hpb.trans hq.1.1, hq.1.2⟩, hq.2⟩
  have hcontr := hbound q hq'
  rw [hn, hdim p q hq'.1.1] at hcontr
  change ((d + s : ℤ) : EInt) < (((n : ℤ) + (δ p - δ q) : ℤ) : EInt) at hcontr
  have hlt : d + s < (n : ℤ) + (δ p - δ q) := WithBotTop.coe_lt_coe.mp hcontr
  omega

/-- **Claim I of Stacks 0EFI.** The closure of `B` stays inside `T`. -/
private theorem closure_badLocus_subset_associatedSubset
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (H : StabilizationHypotheses (M := M) I J s d omega) :
    closure (badLocus (M := M) I J s) ⊆ associatedSubset I J := by
  let δ := Dualizing.dualizingDimensionFunction omega H.dualizing
  refine closure_subset_of_generic_mem _ _ (associatedSubset_stableUnderSpecialization I J)
    (mem_associatedSubset_of_mem_closure_badLocus_at_prime I J s d omega H δ.toFun
      (finite_range_dimensionFunction δ
        (Dualizing.ringKrullDim_lt_top_of_isDualizingComplex H.dualizing))
      (krullDimToEInt_localization_quotient_eq_dimensionFunction δ) ?_)
  intro c
  exact isClosed_depth_add_dualizingDimension_sublevel omega H.dualizing c

/-- **Claim I of Stacks 0EFI.** Shrinking `J` to the candidate ideal does not change the
intersection of the zero locus with `V(I)`. -/
private theorem zeroLocus_stabilizingIdealCandidate_inter
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (H : StabilizationHypotheses (M := M) I J s d omega) :
    PrimeSpectrum.zeroLocus (stabilizingIdealCandidate (M := M) I J s : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) := by
  exact zeroLocus_stabilizingIdealCandidate_inter_of_closure_subset I J s
    (closure_badLocus_subset_associatedSubset I J s d omega H)

/-- The candidate ideal cuts out a subset of `T`. -/
private theorem zeroLocus_stabilizingIdealCandidate_subset_associatedSubset
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (H : StabilizationHypotheses (M := M) I J s d omega) :
    PrimeSpectrum.zeroLocus (stabilizingIdealCandidate (M := M) I J s : Set A) ⊆
      associatedSubset I J := by
  rw [zeroLocus_stabilizingIdealCandidate]
  exact Set.union_subset (closure_badLocus_subset_associatedSubset I J s d omega H)
    (zeroLocus_subset_associatedSubset I J)

/-! ### Claim II: the comparison isomorphism -/

/-- **Claim II of Stacks 0EFI.** If `V(J₀)` contains `B`, then shrinking `J₀` further to an
admissible `J'` does not change local cohomology in degrees `≤ s`.

By Stacks 0DWV it suffices that `H^i_𝔭(M_𝔭)` vanish in degrees `i` and `i - 1` at the primes of
`V(J') \ V(J₀)`. Those primes lie outside `V(I)` and inside `T`, hence outside `B`, so the depth
of `M` at them exceeds `s ≥ i`, and the vanishing is the vanishing of local cohomology below the
depth. No hypothesis of the source is used. -/
private theorem isIso_localCohomologyComparison_of_badLocus_subset
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J J₀ : Ideal A) (s : ℤ)
    (hzero : PrimeSpectrum.zeroLocus (J₀ : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (hbad : badLocus (M := M) I J s ⊆ PrimeSpectrum.zeroLocus (J₀ : Set A))
    (J' : Ideal A) (hJ' : J' ≤ J₀)
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (i : ℤ) (hi : i ≤ s) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
      (localCohomologyComparison A J₀ J' J₀.fg_of_isNoetherianRing
        J'.fg_of_isNoetherianRing hJ'
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj (ModuleCat.of A M)))) := by
  by_cases hneg : i < 0
  · exact (Stacks.LocalCohomology.isZero_localCohomologyModule_of_neg A J₀
      J₀.fg_of_isNoetherianRing (ModuleCat.of A M) i hneg).isIso
      (Stacks.LocalCohomology.isZero_localCohomologyModule_of_neg A J'
        J'.fg_of_isNoetherianRing (ModuleCat.of A M) i hneg) _
  · refine Stacks.LocalCohomology.isIso_localCohomologyModuleMapOfLE A J' J₀
      J'.fg_of_isNoetherianRing J₀.fg_of_isNoetherianRing hJ' (ModuleCat.of A M) i
      (le_of_not_gt hneg) ?_
    intro p hp hpJ' hpJ₀
    obtain ⟨hxI, hxT⟩ := prime_mem_associatedSubset_not_mem_zeroLocus
      I J J₀ J' hzero hV ⟨p, hp⟩ hpJ' hpJ₀
    have hnotbad : (⟨p, hp⟩ : PrimeSpectrum A) ∉ badLocus (M := M) I J s := fun hbadp =>
      hpJ₀ (hbad hbadp)
    have hdepth : (s : EInt) < enatToEInt
        (Module.depth (Localization.AtPrime p)
          (maximalIdeal (Localization.AtPrime p)) (LocalizedModule p.primeCompl M)) :=
      lt_of_not_ge fun h => hnotbad ⟨hxI, hxT, h⟩
    have hvan : ∀ j : ℤ, j ≤ s →
        IsZero (Stacks.LocalCohomology.localCohomologyModule (Localization.AtPrime p)
          (p.map (algebraMap A (Localization.AtPrime p)))
          ((Ideal.fg_of_isNoetherianRing p).map (algebraMap A (Localization.AtPrime p)))
          (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) j) := by
      intro j hj
      simpa only [Localization.AtPrime.map_eq_maximalIdeal] using
        isZero_localCohomologyModule_maximal_of_lt_depth.{u, v} (Localization.AtPrime p)
          (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) j
          (lt_of_le_of_lt (WithBotTop.coe_le_coe.mpr hj) hdepth)
    exact ⟨hvan i hi, hvan (i - 1) (by omega)⟩

/-! ### Claim III: the uniform annihilation -/

/-- **Claim III of Stacks 0EFI for `s ≤ 0`.** A power of `J₀` annihilates `H⁰_{J₀}(M)`.

`H⁰_{J₀}(M)` is a submodule of `M`, hence a finite module, and its cohomology is `J₀`-power
torsion; a finite power-torsion module has `V(J₀)` inside the zero locus of its annihilator. -/
private theorem exists_pow_le_annihilator_localCohomologyModule_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (J₀ : Ideal A) :
    ∃ n : ℕ, J₀ ^ n ≤ Module.annihilator A
      (Stacks.LocalCohomology.localCohomologyModule A J₀ J₀.fg_of_isNoetherianRing
        (ModuleCat.of A M) 0) := by
  have hinj : Function.Injective
      (Stacks.LocalCohomology.localCohomologyZeroToModule A J₀
        J₀.fg_of_isNoetherianRing (ModuleCat.of A M)).hom :=
    Stacks.LocalCohomology.localCohomologyZeroToModule_injective A J₀
      J₀.fg_of_isNoetherianRing (ModuleCat.of A M)
  have hfin : Module.Finite A
      (Stacks.LocalCohomology.localCohomologyModule A J₀ J₀.fg_of_isNoetherianRing
        (ModuleCat.of A M) 0) :=
    Module.Finite.of_injective _ hinj
  have htor : IsIPowerTorsion A
      (Stacks.LocalCohomology.localCohomologyModule A J₀ J₀.fg_of_isNoetherianRing
        (ModuleCat.of A M) 0) J₀ :=
    ((Dualizing.localCohomologyFunctor A J₀ J₀.fg_of_isNoetherianRing).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj (ModuleCat.of A M))).property 0
  have hsupp := support_subset_zeroLocus_of_isIPowerTorsion htor
  rw [Module.support_eq_zeroLocus] at hsupp
  exact Ideal.exists_pow_le_of_le_radical_of_fg
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp hsupp) J₀.fg_of_isNoetherianRing

/-! ### The existence statement -/

/-- **Stacks 0EFI for `s ≤ 0`.** Let `I` and `J` be ideals of a Noetherian ring `A` and let `M` be
a finite `A`-module. For every integer `s ≤ 0` there is a pair `(J₀, n)` with the stabilization
property of Stacks 0EFI: `J₀ ≤ J` and `V(J₀) ∩ V(I) = V(J) ∩ V(I)`, every further ideal `J' ≤ J₀`
with `V(J') ∩ V(I) = V(J) ∩ V(I)` has `RΓ_{J₀}(M) → RΓ_{J'}(M)` an isomorphism on cohomology in
degrees `≤ s`, and `(J₀ I) ^ n` annihilates all of those cohomology modules.

The ideal is the one the source constructs, `J₀ = J ⊓ I(B)` for `B` the set of primes outside
`V(I)` lying in `T` at which the depth of `M` is at most `s`. In this range the hypotheses
(1)–(4) of the source — a dualizing complex and bounds on depth and relative dimension — are not
needed: the semicontinuity argument of Claim I is replaced by the nonnegativity of depth, and the
annihilator criterion Stacks 0EFC of Claim III by the finiteness of `H⁰_{J₀}(M)`.

For `s ≥ 1` the hypotheses are needed; see
`Stacks.Algebraization.exists_isStabilizingData`. -/
@[stacks 0EFI "the existence of the stabilizing data, for s ≤ 0"]
public theorem exists_isStabilizingData_of_nonpos
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s : ℤ) (hs : s ≤ 0) :
    ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I J s p := by
  obtain ⟨n, hn⟩ := exists_pow_le_annihilator_localCohomologyModule_zero (M := M)
    (stabilizingIdealCandidate (M := M) I J s)
  have hzero := zeroLocus_stabilizingIdealCandidate_inter_of_nonpos (M := M) I J s hs
  have hbad := badLocus_subset_zeroLocus_stabilizingIdealCandidate (M := M) I J s
  have hiso := isIso_localCohomologyComparison_of_badLocus_subset (M := M) I J
    (stabilizingIdealCandidate (M := M) I J s) s hzero hbad
  refine ⟨(stabilizingIdealCandidate (M := M) I J s, n),
    stabilizingIdealCandidate_le I J s, hzero, hiso, ?_⟩
  intro J' hJ' hV i hi
  by_cases hneg : i < 0
  · have hz := Stacks.LocalCohomology.isZero_localCohomologyModule_of_neg A J'
      J'.fg_of_isNoetherianRing (ModuleCat.of A M) i hneg
    exact le_top.trans (Module.annihilator_eq_top_iff.mpr
      (ModuleCat.isZero_iff_subsingleton.mp hz)).ge
  · have hi0 : i = 0 := by omega
    subst hi0
    have := hiso J' hJ' hV 0 hi
    have hmono : Function.Injective
        ((inv ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map
          (localCohomologyComparison A (stabilizingIdealCandidate (M := M) I J s) J'
            (stabilizingIdealCandidate (M := M) I J s).fg_of_isNoetherianRing
            J'.fg_of_isNoetherianRing hJ'
            ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
              (ModuleCat.of A M))))).hom) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    refine le_trans (pow_le_pow_left' Ideal.mul_le_left n) ?_
    exact hn.trans (LinearMap.annihilator_le_of_injective _ hmono)

end Stacks.Algebraization

end
