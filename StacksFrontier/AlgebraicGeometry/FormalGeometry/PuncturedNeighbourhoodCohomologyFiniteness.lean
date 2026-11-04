module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationDimensionBounds
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdealFiniteness
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.IsolatedPrime
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison

/-!
# Finiteness of the cohomology of a coherent sheaf on small neighbourhoods of a punctured fibre

Let `(A, 𝔪)` be a Noetherian local ring which has a dualizing complex and is `I`-adically
complete, let `X = Spec A`, `Y = V(I)` and `U = X ∖ {𝔪}`, and let `ℱ` be a coherent sheaf on
`U`. Stacks 0DXQ assumes

1. `cd(A, I) ≤ d`, and
2. for every `x ∈ X ∖ Y` whose closure in `X` meets `U ∩ Y`,
   `depth_{𝒪_{X,x}}(ℱ_x) ≥ s` or `depth_{𝒪_{X,x}}(ℱ_x) + dim(closure of x) > d + s`,

and concludes that there is an open `V₀ ⊆ U` containing `U ∩ Y` such that for every open
`V ⊆ V₀` containing `U ∩ Y` the canonical map `H^i(V, ℱ) → lim_n H^i(U, ℱ/Iⁿℱ)` is an
isomorphism for `i < s`; and that, under the further assumption
`depth_{𝒪_{X,x}}(ℱ_x) + dim(closure of x) > s` for all `x ∈ U ∩ Y`, these cohomology groups are
finite `A`-modules.

This file proves the **finiteness clause** of that theorem, for the source's left-hand group
`H^i(V, ℱ)`. The comparison clause is not proved here but is proved elsewhere; see "Where the
comparison clause of Tag 0DXQ is" below.

## Main definitions

* `Stacks.Algebraization.PuncturedNeighbourhood.StabilizingDataExists` — the existence statement
  of Stacks 0EFI, quantified over all of its own data.
* `Stacks.Algebraization.PuncturedNeighbourhood.Hypotheses` — the standing hypotheses of
  Stacks 0DXQ, namely completeness, a dualizing complex, and its numbered assumptions (1), (2).
* `Stacks.Algebraization.PuncturedNeighbourhood.neighbourhoodCohomology` — `H^i(V, M̃)` for
  `V = X ∖ V(J)`, read as an `A`-module.

## Main results

* `Stacks.Algebraization.PuncturedNeighbourhood.Hypotheses.toLocalStabilizationHypotheses` —
  assumptions (1) and (2) of Stacks 0DXQ are hypotheses (1)–(4) of Stacks 0DXM; this is the
  step of the source proof reading "then the assumptions of Lemma 0DXP are satisfied".
* `Stacks.Algebraization.PuncturedNeighbourhood.exists_ideal_finite_neighbourhoodCohomology` —
  **Stacks 0DXQ, the finiteness clause**: an ideal `J₀` with `V(J₀) ∩ V(I) = {𝔪}` such that for
  every `J ⊆ J₀` with `V(J) ∩ V(I) = {𝔪}` the `A`-module `H^i(X ∖ V(J), M̃)` is finite for
  `i < s`.
* `Stacks.Algebraization.PuncturedNeighbourhood.finite_neighbourhoodCohomology` — the same, in
  the form carrying the existence statement `StabilizingDataExists` of Stacks 0EFI.

## Implementation notes

*Coherent sheaves on `U` and finite modules.* The theorem is stated for `M̃` with `M` a finite
`A`-module, which is the form the whole neighbouring development — Stacks 0DXM, 0DXN, 0EFI, 0EFJ,
0EFQ — states its depth and dimension hypotheses in. This is not a restriction: the first move
of the source proof is to choose a finite `A`-module `M` whose associated sheaf restricts to `ℱ`
on `U`, which is Stacks 0BK0 (1), available here as
`AlgebraicGeometry.exists_finiteModule_tilde_restrict_zeroLocusCompl`. For `𝔭 ∈ U` the stalk
`ℱ_𝔭` is then `M_𝔭`, so assumption (2) and the finiteness assumption of the source become the
conditions on the localizations `M_𝔭` used below.

*Opens of `U` containing `U ∩ Y` and ideals.* The source performs this translation itself: with
`V₀ = X ∖ V(J₀)`, the opens `V ⊆ V₀` containing `U ∩ Y` correspond one-to-one with the ideals
`J ⊆ J₀` such that `V(J) ∩ V(I) = {𝔪}`. Indeed `X ∖ V(J) ⊆ U` says `𝔪 ∈ V(J)`, that is
`J ≠ A`, and `U ∩ Y ⊆ X ∖ V(J)` says `V(J) ∩ V(I) ⊆ {𝔪}`, which together with
`𝔪 ∈ V(J) ∩ V(I)` is the displayed equality. The conclusion below is therefore quantified over
ideals, as the conclusions of Stacks 0DXM, 0DXN and 0EFQ are.

*Assumption (1) and hypothesis (3) of Stacks 0DXM.* Stacks 0DXM asks for `dim(A/𝔭) ≤ d` at the
primes `𝔭 ∉ V(I)` with `V(𝔭) ∩ V(I) = {𝔪}`, while Stacks 0DXQ asks for `cd(A, I) ≤ d`. The
implication is Stacks 0DXF, `dim(A/𝔭) ≤ cd(A, I)` at exactly those primes, available as
`Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension'`; the Krull dimension of
`A/𝔭` is a natural number because `A/𝔭` is a Noetherian local ring.

*Assumption (2) and the closure condition.* For `𝔭` a prime of `A` the closure of the
corresponding point is `V(𝔭)`, and `𝔪 ∈ V(𝔭) ∩ V(I)` always, since `I` is proper. So `V(𝔭)`
meets `U ∩ Y = (V(I) ∖ {𝔪})` exactly when `V(𝔭) ∩ V(I) ≠ {𝔪}`, which is the form assumption (2)
takes below and is literally hypothesis (4) of Stacks 0DXM.

*From local cohomology to cohomology on `V`.* The chain is: Stacks 0DXN gives finiteness of
`H^j_{J₀}(M)` for `j ≤ s`; Stacks 0DXM makes `H^j_{J₀}(M) → H^j_J(M)` an isomorphism in those
degrees; Stacks 0955 passes from the coreflection model of local cohomology to the
supported-sections model; and Stacks 0BK0 (3) together with the higher comparison of Stacks 0DWR
turns finiteness of `H^{i+1}_{V(J)}(M)` into finiteness of `H^i(X ∖ V(J), M̃)`, in every degree
`i ≥ 0` — in positive degrees by the isomorphism `H^i(V, M̃) ≅ H^{i+1}_{V(J)}(M)`, and in degree
zero by the four-term exact sequence, which presents `Γ(V, M̃)` as an extension of
`H^1_{V(J)}(M)` by a quotient of `M`. The last two steps are
`Stacks.LocalCohomologySequence.finite_complementCohomologyBase_iff_finite_localCohomology` and
`Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule`. The degree shift
is why `i < s` suffices: the degree that is consumed is `i + 1 ≤ s`.

*The stabilizing data is constructed, not assumed.* `Stacks.Algebraization.stabilizingData`
*selects* a pair with the stabilization property when one exists, so every cohomological
consequence of Stacks 0EFI — and hence of Stacks 0DXM and 0DXN — needs that existence. Stacks
0EFI proves it, as `Stacks.Algebraization.exists_isStabilizingData`, under one hypothesis that
`Stacks.Algebraization.StabilizationHypotheses` does not record, namely `0 ≤ d`. That hypothesis
is supplied here by assumption (1) of the theorem: `I` is proper, so `𝔪 ∈ V(I)` and Stacks 0DXF
gives `0 ≤ cd(A, I) ≤ d`, by
`Stacks.Algebraization.nonneg_cohomologicalDimension_of_mem_zeroLocus`. So the existence of the
stabilizing data is discharged from the theorem's own hypotheses and is not an input.

*`0 ≤ s`.* Stacks 0DXN inherits the hypothesis `0 ≤ s` from Stacks 0EFC and 0EFD. It is not
assumed below: a degree `i : ℕ` with `i < s` forces `s ≥ 1`, and the hypothesis is derived at
that point. The degree ranges over `ℕ`, which is the indexing of
`Stacks.LocalCohomologySequence.complementCohomologyBase`; in a negative degree the cohomology
of the complement vanishes, so no case of the source statement is lost.

*A hypothesis that is not consumed.* `Hypotheses.adicComplete`, the `I`-adic completeness of
`A`, is a standing assumption of Stacks 0DXQ and is recorded as a field, but the finiteness
clause does not use it: in the source it enters only through Stacks 0DXP, which belongs to the
comparison clause. It is kept so that the hypotheses below are those of the theorem.

### Where the comparison clause of Tag 0DXQ is

The comparison clause — the canonical map `H^i(V, ℱ) → lim_n H^i(U, ℱ/Iⁿℱ)` and its
invertibility for `i < s` — is not proved in this file, and this file's attribute therefore
covers the finiteness clause only. It is **proved**, elsewhere, along a route
different from the source's:

* the canonical map is
  `Stacks.Algebraization.PuncturedNeighbourhood.neighbourhoodToPuncturedLimit`, and its
  invertibility for `ℱ = M̃|_U` in every degree `i < s` is
  `Stacks.Algebraization.PuncturedNeighbourhood.comparison_and_finiteness` in
  `PuncturedNeighbourhoodWhole.lean`, with the positive degrees supplied by
  `NeighbourhoodComparisonHigher.lean`;
* for an arbitrary coherent `ℱ` on `U` the clause is
  `Stacks.Algebraization.coherentFormalAlgebraization` in
  `CoherentSheafPuncturedAlgebraization.lean`, which carries `@[stacks 0DXQ]` and which is where
  the whole theorem — both clauses, at the source's own hypotheses — is registered.

The derived-completion route the source takes, through Stacks 0BLX and the general case of
Stacks 099F, is not the route taken: those inputs are absent from this library and are
not needed. The comparison is obtained instead inside the local-cohomology model that this
file's own chain already works in — Stacks 0DXP for the ideal `J₀`, the localization triangle for
the degrees `1 ≤ i < s`, and excision to move the limit from `V` to `U`
(`Stacks.Algebraization.isIso_complementAdicQuotientToExcisedLimit`). The Čech-to-sheaf
comparison in higher degrees is also available, as
`Stacks.LocalCohomologySequence.complementCohomologyBaseIsoCechHomology` and
`Stacks.LocalCohomologySequence.complementCohomologyBaseIsoRightDerivedSections`; the
implementation notes of `StacksFrontier/RingTheory/LocalCohomology/ComplementCohomology.lean`
record it as available too.

## References

* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
* [Stacks Project, Tag 0DXF](https://stacks.math.columbia.edu/tag/0DXF)
* [Stacks Project, Tag 0DXM](https://stacks.math.columbia.edu/tag/0DXM)
* [Stacks Project, Tag 0DXN](https://stacks.math.columbia.edu/tag/0DXN)
* [Stacks Project, Tag 0DXP](https://stacks.math.columbia.edu/tag/0DXP)
* [Stacks Project, Tag 0DXI](https://stacks.math.columbia.edu/tag/0DXI)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0EFI](https://stacks.math.columbia.edu/tag/0EFI)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)

## Tags

local cohomology, depth, finiteness, algebraization, formal sections, local ring
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization.PuncturedNeighbourhood

/-- **The existence statement of Stacks 0EFI**, quantified over all of its data: for a finite
module over a Noetherian ring and ideals `I`, `J` satisfying the dualizing, dimension and depth
hypotheses of that lemma, some pair `(J₀, n)` has the stabilization property.

This library *selects* such a pair rather than constructing one, so this statement is what every
cohomological consequence of Stacks 0EFI is conditional on. It is not needed at the data of
Stacks 0DXQ, where `exists_ideal_finite_neighbourhoodCohomology` constructs the pair. -/
public def StabilizingDataExists : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B]
    (N : Type u) [AddCommGroup N] [Module B N] [Module.Finite B N]
    (I J : Ideal B) (s d : ℤ) (omega : DerivedCategory (ModuleCat.{u} B)),
      StabilizationHypotheses (M := N) I J s d omega →
        ∃ p : Ideal B × ℕ, IsStabilizingData (M := N) I J s p

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- The standing hypotheses of Stacks 0DXQ for the coherent sheaf `M̃|_U` on the punctured
spectrum of `A`: the ideal `I` is proper, `A` is `I`-adically complete and has a dualizing
complex witnessed by `omega`, the cohomological dimension `cd(A, I)` is at most `d`, and every
prime `𝔭 ∉ V(I)` whose closed set meets `V(I)` in more than the maximal ideal satisfies
`depth(M_𝔭) ≥ s` or `depth(M_𝔭) + dim(A/𝔭) > d + s`.

The last two fields are assumptions (1) and (2) of the source. Properness of `I` is the source's
standing assumption that `𝔪 ∈ V(I)`, without which `V(I)` is empty. -/
public structure Hypotheses (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A)) : Prop where
  /-- The ideal `I` is proper, so that `𝔪 ∈ V(I)`. -/
  ne_top : I ≠ ⊤
  /-- The ring is `I`-adically complete. -/
  adicComplete : IsAdicComplete I A
  /-- The ring has a dualizing complex, witnessed by `omega`. -/
  dualizing : Dualizing.IsDualizingComplex omega
  /-- Assumption (1): the cohomological dimension of `I` is at most `d`. -/
  cohomologicalDimension_le :
    Stacks.LocalCohomology.cohomologicalDimension A I (Ideal.fg_of_isNoetherianRing I) ≤ d
  /-- Assumption (2): a prime outside `V(I)` whose closed set meets `V(I)` in more than the
  maximal ideal has depth at least `s`, or depth plus the dimension of `A/𝔭` exceeding
  `d + s`. -/
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

/-- **Assumptions (1) and (2) of Stacks 0DXQ are hypotheses (1)–(4) of Stacks 0DXM.** This is the
step of the source proof reading "then the assumptions of Lemma 0DXP are satisfied": the
dimension bound that Stacks 0DXM asks for at the primes `𝔭 ∉ V(I)` with `V(𝔭) ∩ V(I) = {𝔪}`
follows from `cd(A, I) ≤ d` by Stacks 0DXF, and the depth condition is literally the same.

No `@[stacks 0DXQ]` attribute is attached: this identifies the hypotheses of the theorem with
those of a lemma it invokes, and so is an input to Stacks 0DXQ rather than a clause of it. -/
public theorem Hypotheses.toLocalStabilizationHypotheses {I : Ideal A} {s d : ℤ}
    {omega : DerivedCategory (ModuleCat.{u} A)} (H : Hypotheses (M := M) I s d omega) :
    LocalStabilizationHypotheses (M := M) I s d omega where
  ne_top := H.ne_top
  dualizing := H.dualizing
  dimensionBound := by
    intro p hp hinter
    have : IsLocalRing (A ⧸ p.asIdeal) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk p.asIdeal) Ideal.Quotient.mk_surjective
    obtain ⟨n, hn⟩ :=
      Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim (A ⧸ p.asIdeal)
    have hcd : (n : ℤ) ≤
        Stacks.LocalCohomology.cohomologicalDimension A I (Ideal.fg_of_isNoetherianRing I) :=
      Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension' A p.asIdeal I
        (Ideal.fg_of_isNoetherianRing I) hinter n hn
    rw [hn, krullDimToEInt_natCast]
    exact WithBotTop.coe_le_coe.mpr (hcd.trans H.cohomologicalDimension_le)
  depthOrDimensionBound := H.depthOrDimensionBound

/-- `H^i(V, M̃)` for `V = Spec A ∖ V(J)`, read as an `A`-module: the degree-`i` cohomology on the
complement of the zero locus of `J` of the quasi-coherent sheaf attached to `M`. -/
public noncomputable abbrev neighbourhoodCohomology (J : Ideal A) (i : ℕ) : ModuleCat.{u} A :=
  Stacks.LocalCohomologySequence.complementCohomologyBase (A := CommRingCat.of A) J
    (ModuleCat.of A M) i

/-- **Stacks 0DXQ, the finiteness clause.** Let `(A, 𝔪)` be a Noetherian local ring which has a
dualizing complex and is `I`-adically complete, let `M` be a finite `A`-module, and assume
assumptions (1) and (2) of the theorem together with
`depth(M_𝔭) + dim(A/𝔭) > s` for every prime `𝔭 ∈ V(I)` other than `𝔪` — the theorem's extra
finiteness assumption, read at the points of `U ∩ Y`. Then there is an ideal `J₀` with
`V(J₀) ∩ V(I) = {𝔪}`, that is an open `V₀ = Spec A ∖ V(J₀)` of the punctured spectrum containing
`U ∩ V(I)`, such that for every `J ⊆ J₀` with `V(J) ∩ V(I) = {𝔪}` — that is, for every open
`V = Spec A ∖ V(J)` inside `V₀` containing `U ∩ V(I)` — the `A`-module `H^i(V, M̃)` is finite in
every degree `i < s`.

Nothing beyond the hypotheses of the theorem is assumed: the stabilizing data of Stacks 0EFI is
constructed, not assumed, from assumption (1); see the module documentation. -/
@[stacks 0DXQ "finiteness of H^i(V, ℱ) for i < s, with ℱ = M̃|_U"]
public theorem exists_ideal_finite_neighbourhoodCohomology (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A)) (H : Hypotheses (M := M) I s d omega)
    (hdepth : DepthAddDimGtAtMaximalIdeal (M := M) I s) :
    ∃ J₀ : Ideal A,
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          {closedPoint A} ∧
        ∀ J : Ideal A, J ≤ J₀ →
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
            {closedPoint A} →
          ∀ i : ℕ, (i : ℤ) < s → Module.Finite A (neighbourhoodCohomology (M := M) J i) := by
  classical
  set HL := H.toLocalStabilizationHypotheses with hHL
  -- Assumption (1) forces `0 ≤ d`: the ideal `I` is proper, so `𝔪 ∈ V(I)` and Stacks 0DXF
  -- gives `0 ≤ cd(A, I) ≤ d`.
  have hd : (0 : ℤ) ≤ d :=
    (nonneg_cohomologicalDimension_of_mem_zeroLocus I (closedPoint A)
      (closedPoint_mem_zeroLocus H.ne_top)).trans H.cohomologicalDimension_le
  -- Stacks 0EFI: the stabilizing data exists at the data of this theorem, `0 ≤ d` being the
  -- only hypothesis of that lemma not recorded by `StabilizationHypotheses`.
  have hexI : ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I (maximalIdeal A) s p :=
    exists_isStabilizingData I (maximalIdeal A) s d hd omega HL.toStabilizationHypotheses
  refine ⟨stabilizingIdeal I (maximalIdeal A) s d omega HL.toStabilizationHypotheses, ?_,
    fun J hJ hV i hi ↦ ?_⟩
  · exact zeroLocus_stabilizingIdeal_maximalIdeal_inter I s d omega HL
  · have hs : (0 : ℤ) ≤ s := by omega
    have hdeg : ((i + 1 : ℕ) : ℤ) ≤ s := by push_cast; omega
    -- Stacks 0DXN: finiteness of `H^{i+1}_{J₀}(M)`.
    have hfin₀ : Module.Finite A (Stacks.LocalCohomology.localCohomologyModule A
        (stabilizingIdeal I (maximalIdeal A) s d omega HL.toStabilizationHypotheses)
        (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of A M) ((i + 1 : ℕ) : ℤ)) :=
      finite_localCohomologyModule_stabilizingIdeal_maximalIdeal_of_exists I s d omega HL
        hdepth hs hd ((i + 1 : ℕ) : ℤ) hdeg
    -- Stacks 0DXM: the comparison to `H^{i+1}_J(M)` is an isomorphism in degrees `≤ s`.
    have hV' : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A) ∩
          PrimeSpectrum.zeroLocus (I : Set A) := by
      rw [hV, zeroLocus_maximalIdeal_inter H.ne_top]
    have hdata : IsStabilizingData (M := M) I (maximalIdeal A) s
        (stabilizingData I (maximalIdeal A) s d omega HL.toStabilizationHypotheses) :=
      isStabilizingData_stabilizingData I (maximalIdeal A) s d omega
        HL.toStabilizationHypotheses hexI
    have hiso := hdata.isIso J hJ hV' ((i + 1 : ℕ) : ℤ) hdeg
    have e : Stacks.LocalCohomology.localCohomologyModule A
          (stabilizingIdeal I (maximalIdeal A) s d omega HL.toStabilizationHypotheses)
          (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of A M) ((i + 1 : ℕ) : ℤ) ≅
        Stacks.LocalCohomology.localCohomologyModule A J (Ideal.fg_of_isNoetherianRing J)
          (ModuleCat.of A M) ((i + 1 : ℕ) : ℤ) := @asIso _ _ _ _ _ hiso
    have := hfin₀
    have hfinJ : Module.Finite A (Stacks.LocalCohomology.localCohomologyModule A J
        (Ideal.fg_of_isNoetherianRing J) (ModuleCat.of A M) ((i + 1 : ℕ) : ℤ)) :=
      Module.Finite.equiv e.toLinearEquiv
    -- Stacks 0955: pass to the supported-sections model of local cohomology.
    have := hfinJ
    have hfinSupp : Module.Finite A
        (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
          (PrimeSpectrum.zeroLocus (J : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M))
          ((i + 1 : ℕ) : ℤ)) :=
      Module.Finite.equiv
        (Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule A J
          (Ideal.fg_of_isNoetherianRing J) (ModuleCat.of A M) ((i + 1 : ℕ) : ℤ)).symm.toLinearEquiv
    -- Stacks 0BK0 (3) with the comparison of Stacks 0DWR: finiteness on the open `V`.
    have : IsNoetherianRing (CommRingCat.of A) := inferInstanceAs (IsNoetherianRing A)
    have : Module.Finite (CommRingCat.of A) (ModuleCat.of A M) :=
      inferInstanceAs (Module.Finite A M)
    exact
      (Stacks.LocalCohomologySequence.finite_complementCohomologyBase_iff_finite_localCohomology
        (A := CommRingCat.of A) J (ModuleCat.of A M) i).2 hfinSupp

/-- **Stacks 0DXQ, the finiteness clause.** Let `(A, 𝔪)` be a Noetherian local ring which has a
dualizing complex and is `I`-adically complete, let `M` be a finite `A`-module, and assume
assumptions (1) and (2) of the theorem together with
`depth(M_𝔭) + dim(A/𝔭) > s` for every prime `𝔭 ∈ V(I)` other than `𝔪` — the theorem's extra
finiteness assumption, read at the points of `U ∩ Y`. Then there is an ideal `J₀` with
`V(J₀) ∩ V(I) = {𝔪}`, that is an open `V₀ = Spec A ∖ V(J₀)` of the punctured spectrum containing
`U ∩ V(I)`, such that for every `J ⊆ J₀` with `V(J) ∩ V(I) = {𝔪}` — that is, for every open
`V = Spec A ∖ V(J)` inside `V₀` containing `U ∩ V(I)` — the `A`-module `H^i(V, M̃)` is finite in
every degree `i < s`.

The hypothesis `hex` is the existence statement of Stacks 0EFI, carried as a general statement
about its own data; it is unused, the same conclusion being
`exists_ideal_finite_neighbourhoodCohomology` with nothing carried. -/
@[stacks 0DXQ "finiteness of H^i(V, ℱ) for i < s, with ℱ = M̃|_U, on the carried existence \
statement of Stacks 0EFI"]
public theorem finite_neighbourhoodCohomology (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A)) (H : Hypotheses (M := M) I s d omega)
    (hdepth : DepthAddDimGtAtMaximalIdeal (M := M) I s) (hex : StabilizingDataExists.{u}) :
    ∃ J₀ : Ideal A,
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          {closedPoint A} ∧
        ∀ J : Ideal A, J ≤ J₀ →
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
            {closedPoint A} →
          ∀ i : ℕ, (i : ℤ) < s → Module.Finite A (neighbourhoodCohomology (M := M) J i) :=
  exists_ideal_finite_neighbourhoodCohomology I s d omega H hdepth

end Stacks.Algebraization.PuncturedNeighbourhood

end
