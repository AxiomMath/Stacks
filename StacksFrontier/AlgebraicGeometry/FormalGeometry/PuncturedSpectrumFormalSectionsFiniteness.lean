module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationComparisonLocal
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.Generalities.ComplementCohomologyZeroSections
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedNeighbourhoodCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumFormalSections
public import StacksFrontier.RingTheory.Serre.Defs

/-!
# The hypotheses of Stacks 0DXR at `s = 1`

Let `(A, 𝔪)` be a Noetherian local ring which has a dualizing complex and is complete with
respect to an ideal `I`, let `X = Spec(A)`, `Y = V(I)` and `U = X ∖ {𝔪}`, and let `ℱ` be a
coherent module on `U`. Stacks 0DXR assumes that every associated point `x ∈ U` of `ℱ`
satisfies `dim(closure {x}) > cd(A, I) + 1`, with the closure taken in `X`, and concludes that

`colim_V H⁰(V, ℱ) ⟶ lim_n H⁰(U, ℱ / Iⁿ ℱ)`

is an isomorphism of finite `A`-modules, the colimit being over the opens `V ⊆ U` containing
`U ∩ Y`. Its proof is one line: *apply Theorem 52.11.2 (Stacks 0DXQ) with `s = 1`; we get
finiteness too.*

This file carries out the hypothesis half of that line. Stacks 0DXQ and the main lemma
Stacks 0DXP that it rests on state their depth conditions on a finite `A`-module `M` with
`ℱ = M̃|_U`, which Stacks 0BK0 (1) supplies; 0DXR's dimension hypothesis, read on `M`, is
`Stacks.Algebraization.AssociatedPrimesClosureDimensionBound` below. From it this file derives,
at `s = 1` and `d = cd(A, I)`:

* the hypotheses of Stacks 0DXP, hence the ideal `J₀` of that lemma and the isomorphism
  `H^i_J(M) ≅ H^i(RΓ_𝔪(M)^∧)` in degrees `i ≤ 1` for every `J ⊆ J₀` with `V(J) ∩ V(I) = {𝔪}`;
* the hypotheses of Stacks 0DXQ together with its extra finiteness assumption, hence the
  finiteness of `H⁰(V, M̃)` on every such neighbourhood `V = X ∖ V(J)` of `U ∩ Y`.

Both come from the same two-case analysis, which is the whole content of the source's `s = 1`:
a prime `𝔭 ≠ 𝔪` either is an associated prime of `M`, where the depth of `M_𝔭` is zero and
0DXR's dimension bound applies, or is not, where `M_𝔭` has depth at least one. Since
`cd(A, I) ≥ 0` for a proper `I`, the bound `dim(A/𝔭) > cd(A, I) + 1` of the first case implies
the bound `dim(A/𝔭) > 1` that 0DXQ's finiteness assumption asks for; in the second case
`depth(M_𝔭) ≥ 1` and `dim(A/𝔭) ≥ 1`, the latter because a prime of a local ring with
zero-dimensional quotient is the maximal ideal.

## Main definitions

* `Stacks.Algebraization.AssociatedPrimesClosureDimensionBound` — the dimension hypothesis of
  Stacks 0DXR, read on a finite `A`-module: every associated prime `𝔭 ≠ 𝔪` of `M` satisfies
  `dim(A/𝔭) > cd(A, I) + 1`.

## Main results

* `Stacks.Algebraization.maximalIdeal_mem_associatedPrimes_localization_iff` — the maximal ideal
  of `A_𝔭` is an associated prime of `M_𝔭` exactly when `𝔭` is an associated prime of `M`.
* `Stacks.Algebraization.one_le_depth_localization_of_notMem_associatedPrimes` — a prime that is
  not associated to `M` has `depth(M_𝔭) ≥ 1`.
* `Stacks.Algebraization.one_le_ringKrullDim_quotient_of_ne_closedPoint` — in a local ring a
  prime other than the maximal ideal has `dim(A/𝔭) ≥ 1`.
* `Stacks.Algebraization.zeroLocus_inter_ne_closedPoint_of_associatedPrimesClosureDimensionBound`
  — the closure of every associated point of `ℱ` meets `V(I)` away from the closed point, by
  Stacks 0DXF.
* `Stacks.Algebraization.localAlgebraizationHypotheses_of_associatedPrimesClosureDimensionBound`
  — 0DXR's hypotheses are the hypotheses of Stacks 0DXP at `s = 1`, `d = cd(A, I)`.
* `Algebraization.exists_isLocalAlgebraizationIdeal_of_associatedPrimesClosureDimensionBound`
  — hence the ideal `J₀` of Stacks 0DXP, at 0DXR's own hypotheses.
* `Stacks.Algebraization.puncturedNeighbourhoodHypotheses_of_associatedPrimesClosureDimensionBound`
  and `Stacks.Algebraization.depthAddDimGtAtMaximalIdeal_of_associatedPrimesClosureDimensionBound`
  — 0DXR's hypotheses are the hypotheses of Stacks 0DXQ at `s = 1`, `d = cd(A, I)`, together
  with that theorem's extra finiteness assumption.
* `Stacks.Algebraization.finite_neighbourhoodCohomology_of_associatedPrimesClosureDimensionBound`
  — hence the finiteness of `H⁰(V, M̃)` on arbitrarily small neighbourhoods `V` of `U ∩ Y`, at
  0DXR's own hypotheses.
* `Stacks.Algebraization.finite_complementGlobalSections_of_associatedPrimesClosureDimensionBound`
  — the same finiteness with `H⁰(V, M̃)` written as the global sections of the restriction of `M̃`
  to the open subscheme `V = X ∖ V(J)`, which is the spelling of the left-hand side of the
  displayed map of Stacks 0DXR and of the four-term exact sequence
  `Stacks.LocalCohomology.exact_lowDegreeSequence`.
* `Stacks.Algebraization.injective_comparisonAt_of_associatedPoints_specializes_vanishing` — the
  comparison at a *single* neighbourhood is injective when the closure of every associated point
  meets the formal locus.
* `Stacks.Algebraization.isIso_sectionsNearVanishing_map_of_surjective_comparisonAt`,
  `Stacks.Algebraization.isIso_colimit_ι_of_surjective_comparisonAt` and
  `Stacks.Algebraization.isIso_comparisonMap_of_surjective_comparisonAt` — the reduction: once
  the comparison at one neighbourhood is onto, every restriction below it is an isomorphism, the
  colimit collapses onto that neighbourhood, and the displayed map of Stacks 0DXR is an
  isomorphism.

## Implementation notes

No `@[stacks]` attribute is placed here. Everything below is an input to Stacks 0DXR — the
hypothesis side of its one-line proof, plus the finiteness of the sections on a *single* small
neighbourhood — and none of it is a clause of the tag's statement, which is about the colimit
and the limit of the displayed map. The tag's own registrations stay in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumFormalSections`.

What the conclusion of Stacks 0DXR still needs, beyond this file, is one statement: the
*comparison* clause of Stacks 0DXQ at `i = 0`, that

`Stacks.Algebraization.comparisonAt A I 𝔪 ℱ V : H⁰(V, ℱ) ⟶ lim_n H⁰(U, ℱ / Iⁿ ℱ)`

is onto for some neighbourhood `V` of `U ∩ Y`. The implementation notes of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedNeighbourhoodCohomologyFiniteness` record
what that waits on. Everything after it is formal, and the last section of this file proves so:
`Stacks.Algebraization.isIso_comparisonMap_of_surjective_comparisonAt` makes the displayed map
an isomorphism, and `Stacks.Algebraization.isIso_colimit_ι_of_surjective_comparisonAt` collapses
the colimit onto `H⁰(V, ℱ)`, whose finiteness is the statement proved above. The one input those
two need besides surjectivity is the injectivity of the comparison *at each single* `V`, which
`Stacks.Algebraization.mono_comparisonMap` does not give — it concludes only that the class in
the colimit vanishes — and which
`Stacks.Algebraization.injective_comparisonAt_of_associatedPoints_specializes_vanishing` supplies
from the condition that the closure of every associated point meets the formal locus. At `𝔞 = 𝔪`
that condition follows from 0DXR's own hypothesis, by
`Stacks.Algebraization.zeroLocus_inter_ne_closedPoint_of_associatedPrimesClosureDimensionBound`.

The finiteness statement above is about `PuncturedNeighbourhood.neighbourhoodCohomology`, the
sections read through `Stacks.LocalCohomologySequence.complementCohomologyBase`, while the
colimit of `Stacks.Algebraization.sectionsNearVanishing` is taken in `Ab` and made an `A`-module
by `Stacks.Algebraization.sectionsNearVanishingColimit`. The first step of the identification of
those two models of the sections on `X ∖ V(J)` is available:
`Stacks.LocalCohomologySequence.complementCohomologyBaseZeroIsoGlobalSections` reads
`complementCohomologyBase J M 0` as the global sections of the restriction of `M̃` to the open
subscheme `X ∖ V(J)`, and
`Stacks.Algebraization.finite_complementGlobalSections_of_associatedPrimesClosureDimensionBound`
is the finiteness above in that spelling. The identification of the open is available too: for
`V` the neighbourhood cut out by `J`, which is
`Stacks.Algebraization.OpensNearVanishing.ofZeroLocusInter`, the image
`(complementZeroLocus A 𝔪).ι ''ᵁ V.openSet` is `complementZeroLocus A J`, by
`Stacks.Algebraization.OpensNearVanishing.ι_image_openSet_ofZeroLocusInter`; and `ℱ` is the
restriction of `M̃` by Stacks 0BK0 (1), available in this spelling as
`Stacks.LocalCohomology.exists_finiteModule_iso_restrict_tilde`. What is still needed to reach
`(sectionsNearVanishing A I 𝔪 ℱ).obj V` is the transport of the sections themselves along that
equality of opens.

The depth bound in the second case goes through Stacks 00LL twice: once over `A_𝔭`, where
`Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes` turns depth zero into the maximal
ideal being associated, and once through the localization of associated primes, which is
`Stacks.Algebraization.maximalIdeal_mem_associatedPrimes_localization_iff`.

## References

* [Stacks Project, Tag 0DXR](https://stacks.math.columbia.edu/tag/0DXR)
* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
* [Stacks Project, Tag 0DXP](https://stacks.math.columbia.edu/tag/0DXP)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 00LL](https://stacks.math.columbia.edu/tag/00LL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### Depth one away from the associated primes -/

section AssociatedPrimes

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

omit [Module.Finite A M] in
/-- **The associated primes of a localization.** At a prime `𝔭` the maximal ideal of `A_𝔭` is an
associated prime of `M_𝔭` exactly when `𝔭` is an associated prime of `M`: associated primes of a
localization are the associated primes contained in `𝔭`, and the one contracting to `𝔭` is the
maximal ideal. -/
public theorem maximalIdeal_mem_associatedPrimes_localization_iff (p : Ideal A) [p.IsPrime] :
    maximalIdeal (Localization.AtPrime p) ∈
        associatedPrimes (Localization.AtPrime p) (LocalizedModule p.primeCompl M) ↔
      p ∈ associatedPrimes A M := by
  rw [←
    Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
    p.primeCompl (Localization.AtPrime p) (LocalizedModule.mkLinearMap p.primeCompl M)]
  change (Ideal.comap (algebraMap A (Localization.AtPrime p))
    (maximalIdeal (Localization.AtPrime p)) ∈ associatedPrimes A M) ↔ _
  rw [show Ideal.comap (algebraMap A (Localization.AtPrime p))
    (maximalIdeal (Localization.AtPrime p)) = p from
      Localization.AtPrime.under_maximalIdeal]

/-- **Depth one away from the associated primes.** If `𝔭` is not an associated prime of the
finite module `M`, then `M_𝔭` has depth at least one over `A_𝔭`: otherwise the maximal ideal of
`A_𝔭` would be an associated prime of `M_𝔭`, hence `𝔭` an associated prime of `M`. -/
public theorem one_le_depth_localization_of_notMem_associatedPrimes (p : PrimeSpectrum A)
    (hp : p.asIdeal ∉ associatedPrimes A M) :
    (1 : ℕ∞) ≤ Module.depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl M) := by
  have _ : p.asIdeal.IsPrime := p.2
  have _ : Module.Finite (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) :=
    Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
  rw [← not_lt, Order.lt_one_iff,
    Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes,
    maximalIdeal_mem_associatedPrimes_localization_iff]
  exact hp

end AssociatedPrimes

/-! ### The dimension of a quotient by a non-maximal prime -/

section Dimension

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- **A prime other than the maximal ideal has positive-dimensional quotient.** For a prime `𝔭`
of a local ring `A` with `𝔭 ≠ 𝔪` the chain `𝔭 ⊊ 𝔪` lives in `V(𝔭)`, which is the spectrum of
`A/𝔭`, so `dim(A/𝔭) ≥ 1`. -/
public theorem one_le_ringKrullDim_quotient_of_ne_closedPoint (p : PrimeSpectrum A)
    (hp : p ≠ closedPoint A) : (1 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal) := by
  have _ : p.asIdeal.IsPrime := p.2
  have hle : p ≤ closedPoint A :=
    (PrimeSpectrum.asIdeal_le_asIdeal _ _).1 (IsLocalRing.le_maximalIdeal_of_isPrime p.asIdeal)
  rw [ringKrullDim,
    Order.krullDim_eq_of_orderIso p.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus,
    Order.one_le_krullDim_iff]
  refine ⟨⟨p, (PrimeSpectrum.mem_zeroLocus _ _).2 (SetLike.coe_subset_coe.2 le_rfl)⟩,
    ⟨closedPoint A, (PrimeSpectrum.mem_zeroLocus _ _).2 (SetLike.coe_subset_coe.2
      (IsLocalRing.le_maximalIdeal_of_isPrime p.asIdeal))⟩, ?_⟩
  exact Subtype.mk_lt_mk.2 (lt_of_le_of_ne hle hp)

end Dimension

/-! ### Arithmetic of the extended integers at `s = 1` -/

/-- A strict inequality of integers is a strict inequality of extended integers. -/
private theorem eint_coe_lt_coe {a b : ℤ} (h : a < b) : ((a : ℤ) : EInt) < ((b : ℤ) : EInt) := by
  simpa only [WithBotTop.coe, Function.comp_apply, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
    using h

/-- Depth zero contributes nothing to the sum of a depth and a dimension. -/
private theorem enatToEInt_zero_add (x : WithBot ℕ∞) :
    enatToEInt 0 + krullDimToEInt x = krullDimToEInt x := by
  induction x using WithBot.recBotCoe with
  | bot => rfl
  | coe z =>
    induction z using ENat.recTopCoe with
    | top => rfl
    | coe n => exact congrArg (fun k : ℕ => ((k : ℤ) : EInt)) (Nat.zero_add n)

/-- The image of `2 : WithBot ℕ∞` in the extended integers. -/
private theorem krullDimToEInt_two : krullDimToEInt (2 : WithBot ℕ∞) = ((2 : ℤ) : EInt) := by
  have h := krullDimToEInt_natCast 2
  simp only [Nat.cast_ofNat] at h
  exact h

/-! ### The dimension hypothesis of Stacks 0DXR, read on a finite module -/

section Bridge

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **The dimension hypothesis of Stacks 0DXR, read on a finite `A`-module.** The source assumes
`dim(closure {x}) > cd(A, I) + 1` at every associated point `x ∈ U` of the coherent module `ℱ`
on the punctured spectrum. For `ℱ = M̃|_U` the associated points of `ℱ` are the associated primes
of `M` other than `𝔪`, and the closure of the point of `𝔭` in `Spec(A)` is `V(𝔭)`, whose
dimension is `dim(A/𝔭)`. -/
public def AssociatedPrimesClosureDimensionBound (I : Ideal A) : Prop :=
  ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M → p ≠ closedPoint A →
    ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
      krullDimToEInt (ringKrullDim (A ⧸ p.asIdeal))

/-- An `I`-adically complete local ring has `I` proper: `I` lies in the maximal ideal. -/
public theorem ne_top_of_isAdicComplete (A : Type u) [CommRing A] [IsLocalRing A] (I : Ideal A)
    (hcomplete : IsAdicComplete I A) : I ≠ ⊤ := by
  intro h
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    (top_le_iff.1 (h ▸ le_maximalIdeal_of_isAdicComplete A I hcomplete))

omit [Module.Finite A M] in
/-- **Every associated prime of `M` meets `V(I)` outside the closed point.** This is the step
the source's proof of Stacks 0EG2 opens with, at `𝔞 = 𝔪`. If an associated prime `𝔭 ≠ 𝔪` had
`V(𝔭) ∩ V(I) = {𝔪}` then Stacks 0DXF would give `dim(A/𝔭) ≤ cd(A, I)`, contradicting 0DXR's
bound `dim(A/𝔭) > cd(A, I) + 1`. Geometrically: the closure of every associated point of `ℱ`
meets the formal locus `U ∩ V(I)`, which is what makes a section of `ℱ` killed by the
comparison have empty support. -/
public theorem zeroLocus_inter_ne_closedPoint_of_associatedPrimesClosureDimensionBound
    (I : Ideal A) (hdim : AssociatedPrimesClosureDimensionBound (M := M) I)
    (p : PrimeSpectrum A) (hass : p.asIdeal ∈ associatedPrimes A M) (hpne : p ≠ closedPoint A) :
    PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ≠
      {closedPoint A} := by
  intro hinter
  have _ : IsLocalRing (A ⧸ p.asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p.asIdeal) Ideal.Quotient.mk_surjective
  obtain ⟨n, hn⟩ :=
    Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim (A ⧸ p.asIdeal)
  have hcd : (n : ℤ) ≤ cohomologicalDimension A I I.fg_of_isNoetherianRing :=
    Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension' A p.asIdeal I
      I.fg_of_isNoetherianRing hinter n hn
  have hlt := hdim p hass hpne
  rw [hn, krullDimToEInt_natCast] at hlt
  exact absurd (WithBotTop.coe_lt_coe.mp hlt) (by omega)

/-- **Condition (4) of Stacks 0DXM and 0DXP at `s = 1`.** A prime outside `V(I)` either is an
associated prime of `M`, in which case `depth(M_𝔭) = 0` and 0DXR's bound
`dim(A/𝔭) > cd(A, I) + 1` is the second alternative, or is not, in which case
`depth(M_𝔭) ≥ 1 = s` is the first. The intersection hypothesis of those lemmas is not used. -/
public theorem depthOrDimensionBound_of_associatedPrimesClosureDimensionBound
    (I : Ideal A) (hI : I ≠ ⊤) (hdim : AssociatedPrimesClosureDimensionBound (M := M) I)
    (p : PrimeSpectrum A) (hp : p ∉ PrimeSpectrum.zeroLocus (I : Set A)) :
    (enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M)) ≥ ((1 : ℤ) : EInt)) ∨
      (enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) +
          krullDimToEInt (ringKrullDim (A ⧸ p.asIdeal)) >
        ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt)) := by
  have hne : p ≠ closedPoint A := fun h => hp (h ▸ closedPoint_mem_zeroLocus hI)
  by_cases hass : p.asIdeal ∈ associatedPrimes A M
  · refine Or.inr ?_
    rw [depth_localization_eq_zero_of_mem_associatedPrimes p hass, enatToEInt_zero_add]
    exact hdim p hass hne
  · refine Or.inl ?_
    have h := enatToEInt_mono (one_le_depth_localization_of_notMem_associatedPrimes p hass)
    rwa [show enatToEInt (1 : ℕ∞) = ((1 : ℤ) : EInt) from rfl] at h

/-- **The hypotheses of Stacks 0DXR give the hypotheses of Stacks 0DXP at `s = 1`.** The
cohomological-dimension bound is taken at `d = cd(A, I)`, where it is an equality; completeness
and the dualizing complex are the source's own; properness of `I` follows from completeness in a
local ring; and condition (4) is
`Stacks.Algebraization.depthOrDimensionBound_of_associatedPrimesClosureDimensionBound`. -/
public theorem localAlgebraizationHypotheses_of_associatedPrimesClosureDimensionBound
    (I : Ideal A) (hcomplete : IsAdicComplete I A)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (hdualizing : Dualizing.IsDualizingComplex omega)
    (hdim : AssociatedPrimesClosureDimensionBound (M := M) I) :
    LocalAlgebraizationHypotheses (M := M) I 1
      (cohomologicalDimension A I I.fg_of_isNoetherianRing) omega where
  ne_top := ne_top_of_isAdicComplete A I hcomplete
  adicComplete := hcomplete
  dualizing := hdualizing
  cohomologicalDimension_le := le_rfl
  depthOrDimensionBound p hp _ :=
    depthOrDimensionBound_of_associatedPrimesClosureDimensionBound I
      (ne_top_of_isAdicComplete A I hcomplete) hdim p hp

/-- **Stacks 0DXP at the hypotheses of Stacks 0DXR.** There is an ideal `J₀` with
`V(J₀) ∩ V(I) = {𝔪}` such that for every `J ⊆ J₀` with the same property the canonical map
`RΓ_J(M) ⟶ RΓ_𝔪(M)^∧` is an isomorphism on cohomology in degrees `≤ 1`. -/
public theorem exists_isLocalAlgebraizationIdeal_of_associatedPrimesClosureDimensionBound
    (I : Ideal A) (hcomplete : IsAdicComplete I A)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (hdualizing : Dualizing.IsDualizingComplex omega)
    (hdim : AssociatedPrimesClosureDimensionBound (M := M) I) :
    ∃ J₀ : Ideal A, IsLocalAlgebraizationIdeal (M := M) I
      (ne_top_of_isAdicComplete A I hcomplete) 1 J₀ :=
  exists_isLocalAlgebraizationIdeal I 1
    (cohomologicalDimension A I I.fg_of_isNoetherianRing) omega
    (localAlgebraizationHypotheses_of_associatedPrimesClosureDimensionBound I hcomplete omega
      hdualizing hdim)

/-- **The hypotheses of Stacks 0DXR give the hypotheses of Stacks 0DXQ at `s = 1`.** The fields
are those of Stacks 0DXP at the same data. -/
public theorem puncturedNeighbourhoodHypotheses_of_associatedPrimesClosureDimensionBound
    (I : Ideal A) (hcomplete : IsAdicComplete I A)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (hdualizing : Dualizing.IsDualizingComplex omega)
    (hdim : AssociatedPrimesClosureDimensionBound (M := M) I) :
    PuncturedNeighbourhood.Hypotheses (M := M) I 1
      (cohomologicalDimension A I I.fg_of_isNoetherianRing) omega where
  ne_top := ne_top_of_isAdicComplete A I hcomplete
  adicComplete := hcomplete
  dualizing := hdualizing
  cohomologicalDimension_le := le_rfl
  depthOrDimensionBound p hp _ :=
    depthOrDimensionBound_of_associatedPrimesClosureDimensionBound I
      (ne_top_of_isAdicComplete A I hcomplete) hdim p hp

/-- **The extra finiteness assumption of Stacks 0DXQ at `s = 1`, from the hypotheses of
Stacks 0DXR.** At a prime `𝔭 ∈ V(I)` other than `𝔪` the sum `depth(M_𝔭) + dim(A/𝔭)` exceeds
`1`: if `𝔭` is an associated prime of `M` the depth is zero and the dimension exceeds
`cd(A, I) + 1 ≥ 1`, because the cohomological dimension of a proper ideal is nonnegative; if it
is not, the depth is at least one and the dimension is at least one. -/
public theorem depthAddDimGtAtMaximalIdeal_of_associatedPrimesClosureDimensionBound
    (I : Ideal A) (hI : I ≠ ⊤) (hdim : AssociatedPrimesClosureDimensionBound (M := M) I) :
    DepthAddDimGtAtMaximalIdeal (M := M) I 1 := by
  have hcd : (0 : ℤ) ≤ cohomologicalDimension A I I.fg_of_isNoetherianRing :=
    nonneg_cohomologicalDimension_of_mem_zeroLocus I (closedPoint A)
      (closedPoint_mem_zeroLocus hI)
  intro p _ hpne
  by_cases hass : p.asIdeal ∈ associatedPrimes A M
  · rw [depth_localization_eq_zero_of_mem_associatedPrimes p hass, enatToEInt_zero_add]
    refine lt_of_le_of_lt ?_ (hdim p hass hpne)
    exact WithBotTop.coe_le_coe.mpr (by omega)
  · have hd1 : (1 : ℕ∞) ≤ Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) :=
      one_le_depth_localization_of_notMem_associatedPrimes p hass
    have hk1 : (1 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal) :=
      one_le_ringKrullDim_quotient_of_ne_closedPoint p hpne
    have hsum : (2 : WithBot ℕ∞) ≤
        ((Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M) : ℕ∞) : WithBot ℕ∞) +
          ringKrullDim (A ⧸ p.asIdeal) := by
      have htwo : (2 : WithBot ℕ∞) = (1 : WithBot ℕ∞) + 1 := by norm_num
      rw [htwo]
      exact add_le_add (by exact_mod_cast hd1) hk1
    have hmono := krullDimToEInt_mono hsum
    have hadd : ∀ (x : ℕ∞) (y : WithBot ℕ∞),
        krullDimToEInt ((x : WithBot ℕ∞) + y) = enatToEInt x + krullDimToEInt y := by
      intro x y
      induction y using WithBot.recBotCoe with
      | bot => induction x using ENat.recTopCoe <;> rfl
      | coe z => induction x using ENat.recTopCoe <;> induction z using ENat.recTopCoe <;> rfl
    rw [krullDimToEInt_two, hadd] at hmono
    exact lt_of_lt_of_le (eint_coe_lt_coe (by norm_num)) hmono

/-- **The finiteness clause of Stacks 0DXQ at the hypotheses of Stacks 0DXR.** There is an ideal
`J₀` with `V(J₀) ∩ V(I) = {𝔪}`, that is an open `V₀ = X ∖ V(J₀)` of the punctured spectrum
containing `U ∩ V(I)`, such that for every `J ⊆ J₀` with the same property the `A`-module of
sections `H⁰(X ∖ V(J), M̃)` is finite. This is the source's parenthesis *"we get finiteness
too"*, read on one neighbourhood. -/
public theorem finite_neighbourhoodCohomology_of_associatedPrimesClosureDimensionBound
    (I : Ideal A) (hcomplete : IsAdicComplete I A)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (hdualizing : Dualizing.IsDualizingComplex omega)
    (hdim : AssociatedPrimesClosureDimensionBound (M := M) I) :
    ∃ J₀ : Ideal A,
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          {closedPoint A} ∧
        ∀ J : Ideal A, J ≤ J₀ →
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
            {closedPoint A} →
          Module.Finite A (PuncturedNeighbourhood.neighbourhoodCohomology (M := M) J 0) := by
  obtain ⟨J₀, hJ₀, hfin⟩ :=
    PuncturedNeighbourhood.exists_ideal_finite_neighbourhoodCohomology (M := M) I 1
      (cohomologicalDimension A I I.fg_of_isNoetherianRing) omega
      (puncturedNeighbourhoodHypotheses_of_associatedPrimesClosureDimensionBound I hcomplete
        omega hdualizing hdim)
      (depthAddDimGtAtMaximalIdeal_of_associatedPrimesClosureDimensionBound I
        (ne_top_of_isAdicComplete A I hcomplete) hdim)
  exact ⟨J₀, hJ₀, fun J hJ hV => hfin J hJ hV 0 (by norm_num)⟩

/-- **The finiteness clause of Stacks 0DXQ at the hypotheses of Stacks 0DXR, read on the sections
of the open subscheme.** The same conclusion as
`Stacks.Algebraization.finite_neighbourhoodCohomology_of_associatedPrimesClosureDimensionBound`,
with `H⁰(X ∖ V(J), M̃)` written as the global sections of the restriction of `M̃` to the open
subscheme `X ∖ V(J)`. That is the spelling of the left-hand side of the displayed map of
Stacks 0DXR and of the four-term exact sequence
`Stacks.LocalCohomology.exact_lowDegreeSequence`, so this is the form in which the finiteness is
available to the comparison. The two spellings are identified by
`Stacks.LocalCohomologySequence.complementCohomologyBaseZeroIsoGlobalSections`. -/
public theorem finite_complementGlobalSections_of_associatedPrimesClosureDimensionBound
    (I : Ideal A) (hcomplete : IsAdicComplete I A)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (hdualizing : Dualizing.IsDualizingComplex omega)
    (hdim : AssociatedPrimesClosureDimensionBound (M := M) I) :
    ∃ J₀ : Ideal A,
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          {closedPoint A} ∧
        ∀ J : Ideal A, J ≤ J₀ →
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
            {closedPoint A} →
          Module.Finite A (Stacks.LocalCohomology.complementGlobalSections A J
            (Stacks.LocalCohomology.complementTilde A J (ModuleCat.of A M))) := by
  obtain ⟨J₀, hJ₀, hfin⟩ :=
    finite_neighbourhoodCohomology_of_associatedPrimesClosureDimensionBound (M := M) I hcomplete
      omega hdualizing hdim
  refine ⟨J₀, hJ₀, fun J hJ hV => ?_⟩
  have h : Module.Finite (CommRingCat.of A)
      (PuncturedNeighbourhood.neighbourhoodCohomology (M := M) J 0) := hfin J hJ hV
  exact Module.Finite.equiv
    (Stacks.LocalCohomologySequence.complementCohomologyBaseZeroIsoGlobalSections A J
      (ModuleCat.of A M)).toLinearEquiv

end Bridge

/-! ### From the comparison at one neighbourhood to the displayed map of Stacks 0DXR -/

section Reduction

variable (A : Type u) [CommRing A] (I a : Ideal A)
  (F : (complementZeroLocus A a : Scheme).Modules)

/-- The intersection of two neighbourhoods of the formal locus is a neighbourhood of it. With
reverse inclusion as the order this is the upper bound that makes the index category filtered. -/
public def OpensNearVanishing.inf (V W : OpensNearVanishing A I a) :
    OpensNearVanishing A I a where
  openSet := V.openSet ⊓ W.openSet
  contains_vanishing x hx := ⟨V.contains_vanishing x hx, W.contains_vanishing x hx⟩

/-- The comparisons at the neighbourhoods of the formal locus are compatible with restriction:
restricting a section and then comparing is comparing. This is the cocone law of
`Stacks.Algebraization.formalSectionsCocone`. -/
public theorem sectionsNearVanishing_map_comp_comparisonAt {V W : OpensNearVanishing A I a}
    (g : V ⟶ W) :
    (sectionsNearVanishing A I a F).map g ≫ comparisonAt A I a F W = comparisonAt A I a F V :=
  (formalSectionsCocone A I a F).w g

variable [IsNoetherianRing A] [F.IsCoherent]

/-- **The comparison at a single neighbourhood is injective**, provided the closure of every
associated point of `F` meets the formal locus `U ∩ V(I)`. This is the source's injectivity
paragraph read at one `V` rather than at the colimit: a section killed by the comparison has
vanishing germ along the formal locus by Krull's intersection theorem, germ vanishing
transports to the points specializing to a point of that locus, so the germs vanish at every
associated point of `F`, and a section with that property is zero.

`Stacks.Algebraization.mono_comparisonMap` is weaker in exactly this respect: it concludes only
that the *class in the colimit* of such a section vanishes, which it does unconditionally. -/
public theorem injective_comparisonAt_of_associatedPoints_specializes_vanishing
    (hAss : ∀ x : (complementZeroLocus A a : Scheme),
      x ∈ Stacks.Divisors.associatedPoints F →
      ∃ y : (complementZeroLocus A a : Scheme), x ⤳ y ∧ I ≤ y.1.asIdeal)
    (V : OpensNearVanishing A I a) :
    Function.Injective (ConcreteCategory.hom (comparisonAt A I a F V)) := by
  have _ : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  refine (injective_iff_map_eq_zero _).2 fun s hs => ?_
  refine AlgebraicGeometry.eq_zero_of_forall_germ_associatedPoints_eq_zero F V.openSet s
    fun x hx hxass => ?_
  obtain ⟨y, hxy, hyI⟩ := hAss x hxass
  have hysupp : y ∈ (idealSheafNearVanishing A I a).support :=
    mem_support_baseIdealSheaf I (complementZeroLocus A a).ι hyI
  exact germ_eq_zero_of_specializes F V.openSet
    (support_idealSheafNearVanishing_le A I a V hysupp) hx hxy s
    (germ_eq_zero_of_comparisonAt_apply_eq_zero A I a F V s hs hysupp)

variable (hinj : ∀ V : OpensNearVanishing A I a,
    Function.Injective (ConcreteCategory.hom (comparisonAt A I a F V)))
  {V : OpensNearVanishing A I a}
  (hsurj : Function.Surjective (ConcreteCategory.hom (comparisonAt A I a F V)))

include hinj hsurj

omit [IsNoetherianRing A] [F.IsCoherent] in
/-- **Restriction below a neighbourhood at which the comparison is onto is an isomorphism.** If
every comparison is injective and the comparison at `V` is onto, then for every `W` below `V`
the restriction `Γ(V, F) ⟶ Γ(W, F)` is an isomorphism: it is injective because the comparison at
`V` factors through it, and onto because a section on `W` and the section on `V` with the same
comparison have the same restriction. -/
public theorem isIso_sectionsNearVanishing_map_of_surjective_comparisonAt
    {W : OpensNearVanishing A I a} (g : V ⟶ W) :
    IsIso ((sectionsNearVanishing A I a F).map g) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun t t' h => ?_, fun u => ?_⟩
  · refine hinj V ?_
    rw [← sectionsNearVanishing_map_comp_comparisonAt A I a F g,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, h]
  · obtain ⟨t, ht⟩ := hsurj (ConcreteCategory.hom (comparisonAt A I a F W) u)
    refine ⟨t, hinj W ?_⟩
    rw [← ConcreteCategory.comp_apply, sectionsNearVanishing_map_comp_comparisonAt, ht]

omit [IsNoetherianRing A] [F.IsCoherent] in
/-- **The colimit collapses onto the neighbourhood at which the comparison is onto.** Under the
same hypotheses the colimit inclusion `Γ(V, F) ⟶ colim_W Γ(W, F)` is an isomorphism: a class in
the colimit is a section on some `W`, which restricts to `V ⊓ W`, where restriction from `V` is
already onto; and a section of `V` dying in the colimit dies on some smaller neighbourhood,
where restriction from `V` is injective. -/
public theorem isIso_colimit_ι_of_surjective_comparisonAt :
    IsIso (colimit.ι (sectionsNearVanishing A I a F) V) := by
  have hforget : PreservesFilteredColimitsOfSize.{0, u} (forget Ab.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, u} _
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero _).2 fun t ht => ?_, fun z => ?_⟩
  · obtain ⟨W, g, hg⟩ := exists_map_eq_zero_of_colimit_ι_eq_zero A I a F V t ht
    have _ := isIso_sectionsNearVanishing_map_of_surjective_comparisonAt A I a F hinj hsurj g
    exact (ConcreteCategory.bijective_of_isIso
      ((sectionsNearVanishing A I a F).map g)).1 (hg.trans (map_zero _).symm)
  · obtain ⟨W, u, rfl⟩ := Concrete.colimit_exists_rep (sectionsNearVanishing A I a F) z
    have hgV : V ⟶ OpensNearVanishing.inf A I a V W := ⟨inf_le_left⟩
    have hgW : W ⟶ OpensNearVanishing.inf A I a V W := ⟨inf_le_right⟩
    have _ := isIso_sectionsNearVanishing_map_of_surjective_comparisonAt A I a F hinj hsurj hgV
    obtain ⟨t, ht⟩ := (ConcreteCategory.bijective_of_isIso
      ((sectionsNearVanishing A I a F).map hgV)).2
      (ConcreteCategory.hom ((sectionsNearVanishing A I a F).map hgW) u)
    refine ⟨t, ?_⟩
    have e : ∀ (X : OpensNearVanishing A I a) (g : X ⟶ OpensNearVanishing.inf A I a V W)
        (x : (sectionsNearVanishing A I a F).obj X),
        ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) X) x =
          ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F)
            (OpensNearVanishing.inf A I a V W))
            (ConcreteCategory.hom ((sectionsNearVanishing A I a F).map g) x) := fun X g x => by
      rw [← ConcreteCategory.comp_apply, colimit.w]
    rw [e V hgV, e W hgW, ht]

omit [IsNoetherianRing A] [F.IsCoherent] in
/-- **The displayed map of Stacks 0DXR is an isomorphism once the comparison at one
neighbourhood is onto.** Every element of `lim_n Γ(U, F / Iⁿ F)` is then the comparison of a
section on `V`, hence of its class in the colimit; and the comparison map is injective because
the comparison at `V` is and the colimit inclusion of `V` is onto. -/
public theorem isIso_comparisonMap_of_surjective_comparisonAt :
    IsIso (comparisonMap A I a F) := by
  have hι := isIso_colimit_ι_of_surjective_comparisonAt A I a F hinj hsurj
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun z z' h => ?_, fun s => ?_⟩
  · obtain ⟨t, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (colimit.ι (sectionsNearVanishing A I a F) V)).2 z
    obtain ⟨t', rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (colimit.ι (sectionsNearVanishing A I a F) V)).2 z'
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      colimit_ι_comp_comparisonMap] at h
    exact congrArg _ (hinj V h)
  · obtain ⟨t, ht⟩ := hsurj s
    refine ⟨ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) t, ?_⟩
    rw [← ConcreteCategory.comp_apply, colimit_ι_comp_comparisonMap]
    exact ht

end Reduction

end Stacks.Algebraization

end
