module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.FiniteAlgebra
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.QuotEquivMapPow
public import StacksFrontier.RingTheory.AnalyticallyUnramified.Counterexample
public import StacksFrontier.RingTheory.AnalyticallyUnramified.Criteria
public import StacksFrontier.RingTheory.AnalyticallyUnramified.Defs
public import StacksFrontier.RingTheory.AnalyticallyUnramified.Examples
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.Flat.AdicFiltration
public import StacksFrontier.RingTheory.Flat.NormalFibres
public import StacksFrontier.RingTheory.Flat.TorCriterion
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.IntegrallyClosed.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.Nagata.Defs
public import StacksFrontier.RingTheory.Nagata.MonogenicN1
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksFrontier.RingTheory.AdicCompletion.SmulTopPow
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterion
public import StacksFrontier.RingTheory.Flat.TowerLTensor
public import StacksFrontier.RingTheory.Flat.QuotientMap
public import StacksFrontier.RingTheory.AdicCompletion.CompletionMap

@[expose] public section
open Stacks.Flatness.NilpotentFibreCriterion

/-!
# Permanence of local properties under adic completion

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

07NV, 07NW, 07NX, 07NY, 0AP1, 07NZ, 0FIZ, 0C23, 0C4G, 0AGX.

## Tag 07NV — Dimension of a completed local ring

The Krull dimension of a Noetherian local ring is unchanged by completion at its maximal ideal.

### Main definitions

No new definitions are introduced.

### Main results

* `ringKrullDim_adicCompletion_maximalIdeal`: completion at the maximal ideal preserves
  the Krull dimension of a Noetherian local ring.

### Implementation notes

The completion is represented by `AdicCompletion (IsLocalRing.maximalIdeal A) A`, Mathlib's
inverse-limit model of the adic completion.

### References

* [The Stacks Project, Tag 07NV](https://stacks.math.columbia.edu/tag/07NV)

## Tag 07NW — Depth of a completed local ring

The depth of a Noetherian local ring is unchanged by completion at its maximal ideal.

### Main definitions

No new definitions are introduced.

### Main results

* `depth_adicCompletion_maximalIdeal`: completion at the maximal ideal preserves the
  depth of a Noetherian local ring.

### Implementation notes

The completion is represented by `AdicCompletion (IsLocalRing.maximalIdeal A) A`, Mathlib's
inverse-limit model of the adic completion. Ring depth is expressed as `Module.depth` of the ring
over itself along its maximal ideal.

### References

* [The Stacks Project, Tag 07NW](https://stacks.math.columbia.edu/tag/07NW)

## Tag 07NX — Cohen–Macaulayness and completion of local rings

A Noetherian local ring is Cohen–Macaulay if and only if its completion at the maximal ideal is
Cohen–Macaulay.

### Main definitions

No new definitions are introduced.

### Main results

* `isMaximalCohenMacaulay_iff_adicCompletion_maximalIdeal`: completion at the maximal
  ideal preserves and reflects Cohen–Macaulayness of a Noetherian local ring.

### Implementation notes

The completion is represented by `AdicCompletion (IsLocalRing.maximalIdeal A) A`, Mathlib's
inverse-limit model of the adic completion. Cohen–Macaulayness of a local ring `A` is expressed as
`Module.IsMaximalCohenMacaulay A A`.

### References

* [The Stacks Project, Tag 07NX](https://stacks.math.columbia.edu/tag/07NX)

## Tag 07NY — Regularity and completion of local rings

A Noetherian local ring is regular if and only if its completion at the maximal ideal is regular.

### Main definitions

No new definitions are introduced.

### Main results

* `isRegularLocalRing_iff_adicCompletion_maximalIdeal`: completion at the maximal ideal
  preserves and reflects regularity of a Noetherian local ring.

### Implementation notes

The completion is represented by `AdicCompletion (IsLocalRing.maximalIdeal A) A`, Mathlib's
inverse-limit model of the adic completion. Regularity is expressed by `IsRegularLocalRing`.

### References

* [The Stacks Project, Tag 07NY](https://stacks.math.columbia.edu/tag/07NY)

## Tag 0AP1 — Discrete valuation rings and completion

A Noetherian local ring is a discrete valuation ring exactly when its completion at the maximal
ideal is a discrete valuation ring.

### Main definitions

No new definitions are introduced.

### Main results

* `isDiscreteValuationRing_iff_adicCompletion_maximalIdeal`: completion at the maximal
  ideal preserves and reflects the property of being a discrete valuation ring.

### Implementation notes

The completion is represented by `AdicCompletion (IsLocalRing.maximalIdeal A) A`. Since Mathlib's
predicate `IsDiscreteValuationRing` takes an `IsDomain` instance, the assertion that an arbitrary
commutative ring is a discrete valuation ring is expressed by existentially bundling that instance.

### References

* [The Stacks Project, Tag 0AP1](https://stacks.math.columbia.edu/tag/0AP1)

## Tag 07NZ — Reducedness and completion of a Noetherian local ring

For a Noetherian local ring, reducedness of the completion implies reducedness of the ring.
The converse fails in general, even for a local domain, but it holds when the ring is Nagata.

### Main definitions

No new definitions are introduced.

### Main results

* `reducedness_and_adicCompletion`: reducedness descends from completion, need not
  ascend to completion in general, and ascends precisely for reduced Nagata local rings.

### Implementation notes

Reducedness of the completion at the maximal ideal is expressed by
`IsAnalyticallyUnramified`. The counterexample is stated in its stronger source form as a
Noetherian local domain with nonreduced completion.

### References

* [Stacks Project, Tag 07NZ](https://stacks.math.columbia.edu/tag/07NZ)

## Tag 0FIZ — Normality from the completion of a local ring

Let `A` be a Noetherian local ring. If the completion of `A` at its maximal ideal is
normal, then `A` is normal.

### Main definitions

There are no new definitions.

### Main results

* `isNormalRing_of_isNormalRing_adicCompletion`: normality descends from the
  maximal-ideal-adic completion of a Noetherian local ring.

### Implementation notes

The completion `A^∧` is represented by
`AdicCompletion (IsLocalRing.maximalIdeal A) A`. Normality is the local definition
`IsNormalRing`, which applies to commutative rings that need not be domains.

### References

* [Stacks Project, Tag 0FIZ](https://stacks.math.columbia.edu/tag/0FIZ)

## Tag 0C23 — Normality of the completion of a local ring

Let `A` be a Noetherian local ring. If `A` is normal and every fibre of the canonical map
from `A` to its completion is normal, then the completion is normal.

### Main definitions

No new definitions are introduced.

### Main results

* `isNormalRing_adicCompletion_maximalIdeal`: the completion of a normal
  Noetherian local ring with normal formal fibres is normal.

### Implementation notes

The completion `A^∧` is represented by `AdicCompletion (IsLocalRing.maximalIdeal A) A`.
The assertion that the formal fibres of `A` are normal is written as normality of every
`Ideal.Fiber` of the canonical algebra map from `A` to this completion.

### References

* [Stacks Project, Tag 0C23]

## Tag 0C4G — Flatness and completion of local rings

A local homomorphism of Noetherian local rings is flat if and only if the induced homomorphism
between their completions at the maximal ideals is flat.

### Main definitions

* `adicCompletionMap` is the homomorphism on adic completions induced by a ring
  homomorphism carrying the ideal of the source into the ideal of the target.

### Main results

* `adicCompletionMap_flat_iff` characterizes flatness of a local homomorphism by
  flatness of its induced map on completions.

### Implementation notes

The induced map is defined from the compatible maps on all quotients by powers of the two ideals.
The theorem is stated for a ring homomorphism directly, so `RingHom.Flat` records flatness using
the algebra structure determined by that homomorphism.

### References

* [Stacks Project, Tag 0C4G](https://stacks.math.columbia.edu/tag/0C4G)

## Tag 0AGX — Completions along a flat local homomorphism

A flat local homomorphism that identifies the maximal ideals and residue fields induces an
isomorphism on completions.

### Main definitions

No new definitions are introduced.

### Main results

* `exists_adicCompletion_ringEquiv_of_flat` gives the isomorphism between the
  completions and records its compatibility with the original homomorphism.

### Implementation notes

The equality of residue fields in the source is expressed by bijectivity of the canonical map on
residue fields. The conclusion includes a ring equivalence commuting with the canonical maps from
the source ring, thereby specifying that it is the equivalence induced by the given homomorphism.
The proof only uses finite generation of the source maximal ideal, so that hypothesis replaces the
source's stronger Noetherian hypotheses.

### References

* [Stacks Project, Tag 0AGX](https://stacks.math.columbia.edu/tag/0AGX)

-/

/-! ### Stacks Tag 07NV -/

section

section

open IsLocalRing

/-- **Stacks 07NV.** A Noetherian local ring and its completion at the maximal ideal have the
same Krull dimension. -/
@[stacks 07NV, ega "IV 7.3.19" "partial"]
public theorem ringKrullDim_adicCompletion_maximalIdeal {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] :
    ringKrullDim A = ringKrullDim (AdicCompletion (maximalIdeal A) A) := by
  let B := AdicCompletion (maximalIdeal A) A
  have hnoeth : IsNoetherianRing B := by infer_instance
  have hgd : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  have hlo : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(maximalIdeal_comap (algebraMap A B)).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal A) (maximalIdeal B)
  have hm : maximalIdeal B = (maximalIdeal A).map (algebraMap A B) := by
    dsimp [B]
    exact AdicCompletion.maximalIdeal_eq_map
  have : Nontrivial (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Ideal.Quotient.nontrivial_iff.mpr (hm ▸ (maximalIdeal.isMaximal B).ne_top)
  have hf : (maximalIdeal B).map
      (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) = ⊥ := by
    rw [hm]
    exact (Ideal.map_eq_bot_iff_le_ker _).mpr (by simp)
  have hdim : (maximalIdeal B).height = (maximalIdeal A).height := by
    rw [hf] at h
    simpa using h
  rw [← maximalIdeal_height_eq_ringKrullDim (R := A),
    ← maximalIdeal_height_eq_ringKrullDim (R := B)]
  exact_mod_cast hdim.symm

end

end

/-! ### Stacks Tag 07NW -/

section

section

open Ideal IsLocalRing

private lemma depth_residueField_eq_zero (S : Type*) [CommRing S] [IsLocalRing S] :
    Module.depth S (maximalIdeal S) (S ⧸ maximalIdeal S) = 0 := by
  rw [Module.depth, ite_eq_right]
  · refine le_antisymm (iSup₂_le fun rs hrs ↦ ?_) zero_le
    suffices rs = [] by simp [this]
    match rs with
    | [] => rfl
    | r :: t =>
      exfalso
      have hr : r ∈ maximalIdeal S := hrs.1 r (by simp)
      have hreg : IsSMulRegular (S ⧸ maximalIdeal S) r :=
        (RingTheory.Sequence.isRegular_cons_iff _ _ _).mp hrs.2 |>.1
      have hone : (1 : S ⧸ maximalIdeal S) ≠ 0 := one_ne_zero
      apply hone
      exact hreg.right_eq_zero_of_smul (by
        show Ideal.Quotient.mk (maximalIdeal S) (r * 1) = 0
        rw [mul_one]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  · intro h
    have hbot : maximalIdeal S • (⊤ : Submodule S (S ⧸ maximalIdeal S)) = ⊥ := by
      rw [Ideal.smul_top_eq_map, Ideal.Quotient.algebraMap_eq,
        Ideal.map_quotient_self, Submodule.restrictScalars_bot]
    rw [hbot] at h
    exact bot_ne_top h

/-- **Stacks 07NW.** A Noetherian local ring and its completion at the maximal ideal have the
same depth. -/
@[stacks 07NW]
public theorem depth_adicCompletion_maximalIdeal {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] :
    Module.depth A (maximalIdeal A) A =
      Module.depth (AdicCompletion (maximalIdeal A) A)
        (maximalIdeal (AdicCompletion (maximalIdeal A) A))
        (AdicCompletion (maximalIdeal A) A) := by
  let B := AdicCompletion (maximalIdeal A) A
  have h := Module.depth_self_eq_depth_self_add_depth_quotient_map_maximalIdeal A B
  rw [← AdicCompletion.maximalIdeal_eq_map] at h
  rw [depth_residueField_eq_zero] at h
  simpa [B] using h.symm

end

end

/-! ### Stacks Tag 07NX -/

section

section

/-- **Stacks 07NX.** A Noetherian local ring is Cohen–Macaulay if and only if its completion at
the maximal ideal is Cohen–Macaulay. -/
@[stacks 07NX]
public theorem isMaximalCohenMacaulay_iff_adicCompletion_maximalIdeal {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] :
    Module.IsMaximalCohenMacaulay A A ↔
      Module.IsMaximalCohenMacaulay (AdicCompletion (IsLocalRing.maximalIdeal A) A)
        (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  unfold Module.IsMaximalCohenMacaulay
  rw [ringKrullDim_adicCompletion_maximalIdeal,
    depth_adicCompletion_maximalIdeal]

end

end

/-! ### Stacks Tag 07NY -/

section

section

/-- **Stacks 07NY.** A Noetherian local ring is regular if and only if its completion at the
maximal ideal is regular. -/
@[stacks 07NY, ega "0 17.1.5", ega "0 17.3.8.1" "local, J = maximal ideal"]
public theorem isRegularLocalRing_iff_adicCompletion_maximalIdeal {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] :
    IsRegularLocalRing A ↔
      IsRegularLocalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  rw [isRegularLocalRing_iff, isRegularLocalRing_iff,
    AdicCompletion.spanFinrank_maximalIdeal_eq,
    ← ringKrullDim_adicCompletion_maximalIdeal]

end

end

/-! ### Stacks Tag 0AP1 -/

section

section

/-- **Stacks 0AP1.** A Noetherian local ring is a discrete valuation ring if and only if its
completion at the maximal ideal is a discrete valuation ring. -/
@[stacks 0AP1]
public theorem isDiscreteValuationRing_iff_adicCompletion_maximalIdeal {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] :
    (∃ _ : IsDomain A, IsDiscreteValuationRing A) ↔
      ∃ _ : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A),
        IsDiscreteValuationRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  let B := AdicCompletion (IsLocalRing.maximalIdeal A) A
  calc
    (∃ _ : IsDomain A, IsDiscreteValuationRing A) ↔
        IsRegularLocalRing A ∧ ringKrullDim A = 1 :=
      (isDiscreteValuationRing_tfae A).out 1 3
    _ ↔ IsRegularLocalRing B ∧ ringKrullDim B = 1 := by
      apply and_congr
      · exact isRegularLocalRing_iff_adicCompletion_maximalIdeal
      · rw [ringKrullDim_adicCompletion_maximalIdeal]
    _ ↔ (∃ _ : IsDomain B, IsDiscreteValuationRing B) :=
      (isDiscreteValuationRing_tfae B).out 3 1

end

end

/-! ### Stacks Tag 07NZ -/

section

section

universe u v

private theorem quotient_isDomain_of_mem_minimalPrimes
    {R : Type*} [CommRing R] {q : Ideal R} (hq : q ∈ minimalPrimes R) :
    IsDomain (R ⧸ q) := by
  have : q.IsPrime := hq.1.1
  infer_instance

private theorem quotient_isLocalRing_of_mem_minimalPrimes
    {R : Type*} [CommRing R] [IsLocalRing R] {q : Ideal R}
    (hq : q ∈ minimalPrimes R) : IsLocalRing (R ⧸ q) := by
  have : Nontrivial (R ⧸ q) := Ideal.Quotient.nontrivial_iff.mpr hq.1.1.ne_top
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective

@[ega "IV 7.6.1" "more general"]
private theorem analyticallyUnramified_of_reduced_of_isNagataRing
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hred : IsReduced R) (hnag : IsNagataRing R) : IsAnalyticallyUnramified R := by
  apply (isAnalyticallyUnramified_iff_minimalPrimes_and_isN1 R).1.mpr
  refine ⟨hred, ?_⟩
  intro q hq _
  have : IsLocalRing (R ⧸ q) := quotient_isLocalRing_of_mem_minimalPrimes hq
  have : IsDomain (R ⧸ q) := quotient_isDomain_of_mem_minimalPrimes hq
  exact IsAnalyticallyUnramified.of_isNagataRing
    (MonogenicN1.isNagataRing_quotient hnag q)

@[ega "IV 7.6.1" "more general"]
private theorem reduced_iff_analyticallyUnramified_of_isNagataRing
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hnag : IsNagataRing A) : IsReduced A ↔ IsAnalyticallyUnramified A := by
  exact ⟨fun hred => analyticallyUnramified_of_reduced_of_isNagataRing hred hnag,
    IsAnalyticallyUnramified.isReduced⟩

private theorem reducedness_and_adicCompletion_of_counterexample
    (counterexample : ∃ (B : Type v) (_ : CommRing B) (_ : IsLocalRing B)
      (_ : IsNoetherianRing B) (_ : IsDomain B), ¬ IsAnalyticallyUnramified B)
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    (IsAnalyticallyUnramified A → IsReduced A) ∧
      (∃ (B : Type v) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsNoetherianRing B)
        (_ : IsDomain B), ¬ IsAnalyticallyUnramified B) ∧
      (IsNagataRing A → (IsReduced A ↔ IsAnalyticallyUnramified A)) := by
  exact ⟨IsAnalyticallyUnramified.isReduced, counterexample,
    fun hnag => reduced_iff_analyticallyUnramified_of_isNagataRing A hnag⟩

/-- **Stacks 07NZ.** For a Noetherian local ring `A`, a reduced completion forces `A` to be
reduced. The converse fails, even for a Noetherian local domain. If `A` is Nagata, then `A` is
reduced if and only if its completion is reduced. -/
@[stacks 07NZ, ega "IV 7.6.1" "more general"]
public theorem reducedness_and_adicCompletion (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] :
    (IsAnalyticallyUnramified A → IsReduced A) ∧
      (∃ (B : Type v) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsNoetherianRing B)
        (_ : IsDomain B), ¬ IsAnalyticallyUnramified B) ∧
      (IsNagataRing A → (IsReduced A ↔ IsAnalyticallyUnramified A)) := by
  have counterexample : ∃ (B : Type v) (_ : CommRing B) (_ : IsLocalRing B)
      (_ : IsNoetherianRing B) (_ : IsDomain B), ¬ IsAnalyticallyUnramified B := by
    have h00PB : ∃ (p : ℕ), p.Prime ∧
        ∃ (R : Type v) (_ : CommRing R) (_ : CharP R p) (_ : IsLocalRing R)
          (_ : IsNoetherianRing R) (_ : IsDomain R),
          ringKrullDim R = 1 ∧ ¬ IsAnalyticallyUnramified R :=
      exists_noetherianLocalDomain_adicCompletion_not_reduced
    obtain ⟨p, hp, B, hcomm, hchar, hlocal, hnoeth, hdomain, _, hnot⟩ :=
      h00PB
    exact ⟨B, hcomm, hlocal, hnoeth, hdomain, hnot⟩
  exact reducedness_and_adicCompletion_of_counterexample counterexample A

end

end

/-! ### Stacks Tag 0FIZ -/

section

section

universe u

/-- A Noetherian local ring is normal if its completion at the maximal ideal is normal. -/
@[stacks 0FIZ]
public theorem isNormalRing_of_isNormalRing_adicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A)) :
    IsNormalRing A := by
  let _ : Module.FaithfullyFlat A
      (AdicCompletion (IsLocalRing.maximalIdeal A) A) :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson _
      (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal])
  exact isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat hA

end

end

/-! ### Stacks Tag 0C23 -/

section

section

universe u

/-- **Stacks Tag 0C23.** The completion of a Noetherian normal local ring whose formal fibres
are normal is a normal ring. -/
@[stacks 0C23, ega "IV 7.8.3" "(v) normal ascends"]
public theorem isNormalRing_adicCompletion_maximalIdeal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsNormalRing A)
    (hformal : ∀ (p : Ideal A) [p.IsPrime],
      IsNormalRing (p.Fiber (AdicCompletion (IsLocalRing.maximalIdeal A) A))) :
    IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  exact isNormalRing_of_flat_of_isNormalRing_fiber hA hformal

end

end

/-! ### Stacks Tag 0C4G -/

section

section

@[expose] public section

universe u v



end

end

section

@[expose] public section

open TensorProduct

universe u v w

open AlgebraTensorModule

@[sga "3 VIIB 5.5.2" "partial"]
private lemma faithfullyFlat_completion (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

private theorem flat_quotientMap_iff_flat_quotient {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) :
    (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
      Ideal.le_comap_map).Flat ↔
      Module.Flat (R ⧸ I) (S ⧸ (I • (⊤ : Submodule R S))) := by
  let e₀ := TensorProduct.quotTensorEquivQuotSMul S I
  let e : ((R ⧸ I) ⊗[R] S) ≃ₗ[R ⧸ I] (S ⧸ (I • (⊤ : Submodule R S))) :=
    { e₀ with
      map_smul' := by
        rintro ⟨r⟩ x
        exact e₀.map_smul r x }
  show (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))).Flat ↔ _
  rw [RingHom.flat_algebraMap_iff]
  exact (Module.Flat.equiv_iff
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv.trans e))

/-- For a Noetherian local ring `R` with maximal ideal `𝔪`, the kernel of the evaluation of the
`𝔪`-adic completion of `R` onto `R ⧸ 𝔪 ^ n` is the `n`-th power of the maximal ideal of the
completion. -/
public lemma ker_evalₐ_eq_pow_maximalIdeal (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) n).toRingHom =
      IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ^ n := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
  ext x
  rw [RingHom.mem_ker]
  show AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) n x = 0 ↔ _
  rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval
      (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing]
  have heq : IsLocalRing.maximalIdeal R ^ n * ⊤ = IsLocalRing.maximalIdeal R ^ n := by simp
  have hinj : Function.Injective (Ideal.Quotient.factor (le_of_eq heq)) := by
    simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker] using
      Ideal.map_mk_eq_bot_of_le (le_of_eq heq.symm)
  simpa [← AdicCompletion.factor_eval_eq_evalₐ] using map_eq_zero_iff _ hinj

/-- For a Noetherian local ring `R` with maximal ideal `𝔪`, the quotient of the `𝔪`-adic
completion of `R` by the `n`-th power of its maximal ideal is isomorphic to `R ⧸ 𝔪 ^ n`. -/
public noncomputable def completionQuotientEquiv (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (n : ℕ) :
    AdicCompletion (IsLocalRing.maximalIdeal R) R ⧸
        IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ^ n ≃+*
      R ⧸ IsLocalRing.maximalIdeal R ^ n :=
  Ideal.quotEquivOfEq (ker_evalₐ_eq_pow_maximalIdeal R n).symm |>.trans
    (RingHom.quotientKerEquivOfSurjective (AdicCompletion.surjective_evalₐ _ n))


/-- `completionQuotientEquiv` sends the class of the image of `r : R` in the completion to the
class of `r`. -/
public lemma completionQuotientEquiv_mk (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (n : ℕ) (r : R) :
    completionQuotientEquiv R n
        (Ideal.Quotient.mk _ (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r)) =
      Ideal.Quotient.mk _ r := by
  show completionQuotientEquiv R n
      (Ideal.Quotient.mk _ (AdicCompletion.of (IsLocalRing.maximalIdeal R) R r)) = _
  simp only [completionQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  show AdicCompletion.evalₐ _ n (AdicCompletion.of _ R r) = _
  exact AdicCompletion.evalₐ_of _ n r

private theorem isLocalization_atMaximal (R : Type u) [CommRing R] [IsLocalRing R] :
    IsLocalization.AtPrime R (IsLocalRing.maximalIdeal R) :=
  IsLocalization.self fun _ hx ↦ IsLocalRing.notMem_maximalIdeal.mp hx

/-- **Stacks 0C4G.** A local homomorphism of Noetherian local rings is flat if and only if the
induced homomorphism between their completions at the maximal ideals is flat. -/
@[stacks 0C4G, sga "3 VIIB 1.3.4" "partial"]
public theorem adicCompletionMap_flat_iff {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B) [IsLocalHom f] :
    (adicCompletionMap f (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
      (IsLocalRing.map_maximalIdeal_le f)).Flat ↔ f.Flat := by
  let Ac := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let Bc := AdicCompletion (IsLocalRing.maximalIdeal B) B
  let fc : Ac →+* Bc := adicCompletionMap f _ _ (IsLocalRing.map_maximalIdeal_le f)
  have hcomm : fc.comp (algebraMap A Ac) = (algebraMap B Bc).comp f :=
    adicCompletionMap_comp_algebraMap f _ _ _
  let : Algebra A B := f.toAlgebra
  let : Algebra B Bc := (algebraMap B Bc).toAlgebra
  let : Algebra A Bc := ((algebraMap B Bc).comp f).toAlgebra
  have : IsScalarTower A B Bc := IsScalarTower.of_algebraMap_eq' rfl
  constructor
  · intro hfc
    have hABc : ((algebraMap B Bc).comp f).Flat := by
      exact hcomm ▸ RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance) hfc
    have : Module.Flat A Bc := RingHom.flat_algebraMap_iff.mp hABc
    have : Module.FaithfullyFlat B Bc := faithfullyFlat_completion B
    exact RingHom.flat_algebraMap_iff.mpr (flat_of_flat_of_faithfullyFlat Bc)
  · intro hf
    let g : A →+* Bc := (algebraMap B Bc).comp f
    have hg : g.Flat := RingHom.Flat.comp hf
      (RingHom.flat_algebraMap_iff.mpr
        (AdicCompletion.flat_of_isNoetherian (IsLocalRing.maximalIdeal B)))
    have : Module.Flat A Bc := RingHom.flat_algebraMap_iff.mpr hg
    let : Algebra Ac Bc := fc.toAlgebra
    let : IsLocalization.AtPrime Bc (IsLocalRing.maximalIdeal Bc) :=
      isLocalization_atMaximal Bc
    let : IsLocalizedModule (IsLocalRing.maximalIdeal Bc).primeCompl
        (LinearMap.id : Bc →ₗ[Bc] Bc) :=
      isLocalizedModule_id _ _ Bc
    have hq : (IsLocalRing.maximalIdeal Ac).map fc ≤
        IsLocalRing.maximalIdeal Bc := by
      rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hcomm,
        ← Ideal.map_map, AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.map_mono (IsLocalRing.map_maximalIdeal_le f)
    show fc.Flat
    rw [← fc.algebraMap_toAlgebra, RingHom.flat_algebraMap_iff]
    refine Module.Flat.of_flat_quotient_pow
      (IsLocalRing.maximalIdeal Ac) Bc ?_
      (IsLocalRing.maximalIdeal Bc)
      hq Bc LinearMap.id
    intro n
    let Jc : Ideal Ac := IsLocalRing.maximalIdeal Ac ^ (n + 1)
    let Ja : Ideal A := IsLocalRing.maximalIdeal A ^ (n + 1)
    have hJc : Jc = Ja.map (algebraMap A Ac) := by
      dsimp [Jc, Ja]
      rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_pow]
    have hK : Jc.map fc = Ja.map g := by
      simp only [hJc, Ideal.map_map, hcomm, g]
      rfl
    let qC : Ac ⧸ Jc →+* Bc ⧸ Jc.map fc :=
      Ideal.quotientMap (Jc.map fc) fc Ideal.le_comap_map
    let qA : A ⧸ Ja →+* Bc ⧸ Ja.map g :=
      Ideal.quotientMap (Ja.map g) g Ideal.le_comap_map
    let eA : Ac ⧸ Jc ≃+* A ⧸ Ja := completionQuotientEquiv A (n + 1)
    let eT : Bc ⧸ Jc.map fc ≃+* Bc ⧸ Ja.map g := Ideal.quotEquivOfEq hK
    have hnat : eT.toRingHom.comp qC = qA.comp eA.toRingHom := by
      apply RingHom.ext
      intro x
      obtain ⟨y, rfl⟩ := eA.symm.surjective x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hx : eA.symm (Ideal.Quotient.mk Ja a) =
          Ideal.Quotient.mk Jc (algebraMap A Ac a) := by
        apply eA.injective
        simp only [eA.apply_symm_apply]
        exact (completionQuotientEquiv_mk A (n + 1) a).symm
      rw [hx]
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe]
      exact congrArg (Ideal.Quotient.mk _) (congrArg (fun h : A →+* Bc => h a) hcomm)
    have hqA : qA.Flat := RingHom.flat_quotientMap g hg Ja
    have hqC : qC.Flat :=
      (RingHom.Flat.comp_iff_of_bijective_left eT.bijective).mp (by
        rw [hnat]
        exact RingHom.Flat.comp (RingHom.Flat.of_bijective eA.bijective) hqA)
    show Module.Flat (Ac ⧸ Jc) (Bc ⧸ Jc • (⊤ : Submodule Ac Bc))
    exact (flat_quotientMap_iff_flat_quotient Jc).mp hqC

end

end

end

/-! ### Stacks Tag 0AGX -/

section

section

open CategoryTheory IsLocalRing AdicCompletion

universe u v


/-- **Stacks 0AGX.** A flat local homomorphism which identifies the maximal ideals and induces an
isomorphism of residue fields induces an isomorphism of adic completions. -/
@[stacks 0AGX]
public theorem exists_adicCompletion_ringEquiv_of_flat
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (hfg : (maximalIdeal A).FG)
    (hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (hres : Function.Bijective (ResidueField.map (algebraMap A B))) :
    ∃ e : AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B,
      ∀ a : A,
        e (algebraMap A (AdicCompletion (maximalIdeal A) A) a) =
          algebraMap B (AdicCompletion (maximalIdeal B) B) (algebraMap A B a) := by
  have hfibB : Module.Finite A (ResidueField B) := by
    apply Module.Finite.of_surjective (Algebra.linearMap A _)
    intro y
    obtain ⟨x, hx⟩ := hres.surjective y
    obtain ⟨a, rfl⟩ := residue_surjective x
    refine ⟨a, ?_⟩
    show residue B (algebraMap A B a) = _
    simpa only [IsLocalRing.ResidueField.map_residue] using hx
  have hfib : Module.Finite A (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by
    rw [hmax]
    exact hfibB
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  let I := maximalIdeal A
  let : Module.Finite A (B ⧸ I.map (algebraMap A B)) := hfib
  obtain ⟨⟨eB⟩, hfinite⟩ :=
    AdicCompletion.nonempty_algEquiv_map_and_finite (R := A) (S := B) hfg
  have hflatquot : Module.Flat (A ⧸ I) (B ⧸ (I • (⊤ : Submodule A B))) := by
    dsimp [I]
    infer_instance
  have htor : Limits.IsZero
      (((Tor (ModuleCat.{max u v} (ULift.{v} A)) 1).obj
        (ModuleCat.of (ULift.{v} A) (ULift.{u} B))).obj
        (ModuleCat.of (ULift.{v} A) (ULift.{v} (A ⧸ I)))) := by
    let : Module.Flat (ULift.{v} A) (ULift.{u} B) := by
      rw [Module.Flat.ulift_left_iff, Module.Flat.ulift_right_iff]
      exact ‹Module.Flat A B›
    exact Tor_iso_Tor'.tor_flat_isZero (R := ULift.{v} A)
      (ModuleCat.of (ULift.{v} A) (ULift.{u} B))
      (ModuleCat.of (ULift.{v} A) (ULift.{v} (A ⧸ I))) 0
  obtain ⟨-, hflat⟩ := AdicCompletion.isNoetherianRing_and_flat_of_flat_quotient
    I hfg (by dsimp [I]; infer_instance) hflatquot htor
  let Rhat := AdicCompletion I A
  let C := AdicCompletion (I.map (algebraMap A B)) B
  let : Algebra Rhat C := (completionMap (B := B) I).toRingHom.toAlgebra
  let E : AdicCompletion I B ≃ₗ[Rhat] C :=
    { __ := adicCompletionLinearEquivMap I B
      map_smul' := by
        intro x y
        dsimp [Rhat, C]
        apply Subtype.ext
        funext n
        obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective
          (I ^ n • (⊤ : Submodule A A)) (x.val n)
        obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective
          (I ^ n • (⊤ : Submodule A B)) (y.val n)
        have hab : a • b = algebraMap A B a * b := Algebra.smul_def a b
        have hL : (x • y).val n = Submodule.Quotient.mk (algebraMap A B a * b) := by
          rw [AdicCompletion.smul_eval, ← ha, ← hb, ← hab]
          rfl
        show quotEquivMapPow I B n ((x • y).val n) =
          ((completionMap (B := B) I x) * adicCompletionLinearEquivMap I B y).val n
        rw [hL, quotEquivMapPow_mk, AdicCompletion.val_mul,
          val_completionMap I n x a ha.symm]
        show _ = _ * quotEquivMapPow I B n (y.val n)
        rw [← hb, quotEquivMapPow_mk]
        rfl }
  let : Module.Finite Rhat C := hfinite.equiv E
  let : Module.Flat Rhat C := Module.Flat.of_linearEquiv E.symm
  let : IsLocalRing Rhat := AdicCompletion.isLocalRing_of_fg hfg
  let : Module.Free Rhat C := Module.free_of_flat_of_isLocalRing
  have hfgB : (I.map (algebraMap A B)).FG := hfg.map _
  have hpC : (maximalIdeal Rhat).map (algebraMap Rhat C) =
      RingHom.ker (AdicCompletion.evalOneₐ (I.map (algebraMap A B))).toRingHom := by
    have hc : (algebraMap Rhat C).comp (algebraMap A Rhat) =
        (algebraMap B C).comp (algebraMap A B) := by
      apply RingHom.ext
      intro a
      exact completionMap_algebraMap (B := B) I a
    calc
      _ = (I.map (algebraMap A Rhat)).map (algebraMap Rhat C) := by
        rw [AdicCompletion.maximalIdeal_eq_map_of_fg hfg]
      _ = I.map ((algebraMap Rhat C).comp (algebraMap A Rhat)) :=
        Ideal.map_map (algebraMap A Rhat) (algebraMap Rhat C)
      _ = I.map ((algebraMap B C).comp (algebraMap A B)) := congrArg (I.map) hc
      _ = (I.map (algebraMap A B)).map (algebraMap B C) :=
        (Ideal.map_map (algebraMap A B) (algebraMap B C)).symm
      _ = _ := (AdicCompletion.ker_evalOneₐ_eq_map _ hfgB).symm
  have hpC_ne : (maximalIdeal Rhat).map (algebraMap Rhat C) ≠ ⊤ := by
    rw [hpC]
    have hIBne : I.map (algebraMap A B) ≠ ⊤ := by
      rw [hmax]
      exact (maximalIdeal.isMaximal B).ne_top
    let : Nontrivial (B ⧸ I.map (algebraMap A B)) :=
      Ideal.Quotient.nontrivial_iff.mpr hIBne
    exact RingHom.ker_ne_top _
  let : Field (Rhat ⧸ maximalIdeal Rhat) := Ideal.Quotient.field (maximalIdeal Rhat)
  have hquotbij : Function.Bijective
      (algebraMap (Rhat ⧸ maximalIdeal Rhat)
        (C ⧸ (maximalIdeal Rhat).map (algebraMap Rhat C))) := by
    constructor
    · let : Nontrivial (C ⧸ (maximalIdeal Rhat).map (algebraMap Rhat C)) :=
        Ideal.Quotient.nontrivial_iff.mpr hpC_ne
      exact RingHom.injective _
    · intro z
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalOneₐ (I.map (algebraMap A B)) y)
      let qeq : (B ⧸ I.map (algebraMap A B)) ≃ₐ[B] ResidueField B :=
        Ideal.quotientEquivAlgOfEq B hmax
      let hb' : ResidueField B := qeq (Ideal.Quotient.mk _ b)
      obtain ⟨x, hx⟩ := hres.surjective hb'
      obtain ⟨a, rfl⟩ := residue_surjective x
      refine ⟨Ideal.Quotient.mk _ (algebraMap A Rhat a), ?_⟩
      apply Ideal.Quotient.eq.mpr
      rw [hpC, RingHom.mem_ker, map_sub]
      show AdicCompletion.evalOneₐ _
          (completionMap (B := B) I (algebraMap A Rhat a)) - _ = 0
      rw [completionMap_algebraMap]
      show AdicCompletion.evalOneₐ _ (algebraMap B C (algebraMap A B a)) -
        AdicCompletion.evalOneₐ _ y = 0
      dsimp only [C]
      rw [show AdicCompletion.evalOneₐ _
          (algebraMap B (AdicCompletion (I.map (algebraMap A B)) B) (algebraMap A B a)) =
          Ideal.Quotient.mk _ (algebraMap A B a) from by
            exact DFunLike.congr_fun
              (AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk (I.map (algebraMap A B)))
              (algebraMap A B a), ← hb, sub_eq_zero]
      apply (Ideal.quotientEquivAlgOfEq B hmax).injective
      show residue B (algebraMap A B a) = residue B b
      have hqeq : qeq (Ideal.Quotient.mk _ b) = residue B b := rfl
      simpa only [IsLocalRing.ResidueField.map_residue, hb', hqeq] using hx
  have hfinrank : Module.finrank Rhat C = 1 := by
    rw [← IsLocalRing.finrank_quotient_map]
    exact Module.finrank_of_bijective_algebraMap hquotbij
  have hbij : Function.Bijective (algebraMap Rhat C) :=
    Module.Free.bijective_algebraMap_of_finrank_eq_one hfinrank
  let eC : Rhat ≃+* C := RingEquiv.ofBijective (algebraMap Rhat C) hbij
  refine ⟨eC.trans eB.symm.toRingEquiv, fun a ↦ ?_⟩
  apply eB.injective
  show eB (eB.symm (eC (algebraMap A Rhat a))) =
    eB (algebraMap B (AdicCompletion (maximalIdeal B) B) (algebraMap A B a))
  rw [eB.apply_symm_apply, eB.commutes]
  exact completionMap_algebraMap (B := B) I a

end

end

end

@[expose] public section

universe u v

namespace Stacks.AdicCompletion

/-- A ring map `f : A →+* B` inducing a bijection `A ⧸ I ^ n ≃ B ⧸ (I ^ n).map f` for every `n`
induces a bijection on the `I`-adic completions. -/
public theorem adicCompletionMap_bijective_of_quotientMap_bijective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A)
    (h : ∀ n : ℕ, Function.Bijective
      (Ideal.quotientMap ((I ^ n).map f) f Ideal.le_comap_map)) :
    Function.Bijective
      (adicCompletionMap f I (I.map f) le_rfl) := by
  have h' (n : ℕ) : Function.Bijective
      (Ideal.quotientMap ((I.map f) ^ n) f (by
        rw [← Ideal.map_le_iff_le_comap, ← Ideal.map_pow])) := by
    let q := (Ideal.quotEquivOfEq (Ideal.map_pow f I n)).toRingHom.comp
      (Ideal.quotientMap ((I ^ n).map f) f Ideal.le_comap_map)
    have hq : q = Ideal.quotientMap ((I.map f) ^ n) f (by
        rw [← Ideal.map_le_iff_le_comap, ← Ideal.map_pow]) := by
      ext x
      rfl
    rw [← hq]
    exact (Ideal.quotEquivOfEq (Ideal.map_pow f I n)).bijective.comp (h n)
  let e (n : ℕ) : A ⧸ I ^ n ≃+* B ⧸ (I.map f) ^ n :=
    RingEquiv.ofBijective _ (h' n)
  have e_naturality {m n : ℕ} (hmn : m ≤ n) (x : A ⧸ I ^ n) :
      Ideal.Quotient.factorPow (I.map f) hmn (e n x) =
        e m (Ideal.Quotient.factorPow I hmn x) := by
    induction x using Quotient.inductionOn with
    | _ x => rfl
  have hlevel (n : ℕ) (x : AdicCompletion I A) :
      AdicCompletion.evalₐ (I.map f) n
          (adicCompletionMap f I (I.map f) le_rfl x) =
        e n (AdicCompletion.evalₐ I n x) := by
    unfold adicCompletionMap
    rw [AdicCompletion.evalₐ_liftRingHom]
    rfl
  let inv : AdicCompletion (I.map f) B →+* AdicCompletion I A :=
    AdicCompletion.liftRingHom I
      (fun n ↦ (e n).symm.toRingHom.comp (AdicCompletion.evalₐ (I.map f) n).toRingHom)
      (fun {m n} hmn ↦ by
        apply RingHom.ext
        intro x
        apply (e m).injective
        show e m (Ideal.Quotient.factorPow I hmn
            ((e n).symm (AdicCompletion.evalₐ (I.map f) n x))) =
          e m ((e m).symm (AdicCompletion.evalₐ (I.map f) m x))
        rw [← e_naturality]
        rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
        induction x using AdicCompletion.induction_on with
        | h x =>
          simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
            Ideal.Quotient.factor_mk]
          rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
          have hx := Submodule.neg_mem _ (SModEq.sub_mem.mp (x.property hmn))
          simpa [Ideal.smul_top_eq_map, neg_sub] using hx)
  have hinv_left : inv.comp (adicCompletionMap f I (I.map f) le_rfl) = RingHom.id _ := by
    apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    simp only [RingHom.comp_apply, AdicCompletion.evalₐ_liftRingHom, inv, RingHom.id_apply]
    show (e n).symm
      (AdicCompletion.evalₐ (I.map f) n
        (adicCompletionMap f I (I.map f) le_rfl x)) = _
    rw [hlevel, RingEquiv.symm_apply_apply]
  have hinv_right :
      (adicCompletionMap f I (I.map f) le_rfl).comp inv = RingHom.id _ := by
    apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [hlevel, AdicCompletion.evalₐ_liftRingHom]
    show e n ((e n).symm (AdicCompletion.evalₐ (I.map f) n x)) = _
    rw [RingEquiv.apply_symm_apply]
  exact Function.bijective_iff_has_inverse.mpr
    ⟨inv, fun x ↦ DFunLike.congr_fun hinv_left x, fun x ↦ DFunLike.congr_fun hinv_right x⟩

end Stacks.AdicCompletion

end
