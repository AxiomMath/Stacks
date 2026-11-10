module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementExcisionAdicLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementSectionsDegreeZeroBridge
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.NeighbourhoodComparisonHigher
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.KrullDimension

/-!
# Stacks 0DXQ for the coherent sheaf `M̃|_U`, both clauses at once

Let `(A, 𝔪)` be a Noetherian local ring which has a dualizing complex and is `I`-adically
complete, let `X = Spec A`, `Y = V(I)`, `U = X ∖ {𝔪}`, and let `M` be a finite `A`-module.
Assume the two numbered hypotheses of Stacks 0DXQ.  This file proves that there is an open
`V₀ ⊆ U` containing `U ∩ Y` such that for every open `V ⊆ V₀` containing `U ∩ Y` and every
`i < s` the canonical map

`H^i(V, M̃) ⟶ lim_n H^i(U, (M/IⁿM)~)`

is an isomorphism; and, under the theorem's further assumption, that those cohomology groups are
finite `A`-modules.

## Main definitions

* `Stacks.Algebraization.PuncturedNeighbourhood.neighbourhoodToPuncturedLimit` — the canonical
  map of the theorem, with the limit on the right taken on the punctured spectrum `U`.

## Main results

* `Stacks.Algebraization.PuncturedNeighbourhood.zeroLocus_maximalIdeal_subset_zeroLocus` and
  `Stacks.Algebraization.PuncturedNeighbourhood.zeroLocus_inter_eq_zeroLocus_maximalIdeal` — the
  two readings of `V(J) ∩ V(I) = {𝔪}` that the excision step needs.
* `Stacks.Algebraization.PuncturedNeighbourhood.le_maximalIdeal_of_zeroLocus_inter` — the third
  reading, `J ⊆ 𝔪`, which is what exhibits `V = Spec A ∖ V(J)` as an open *of* `U`.
* `Stacks.Algebraization.PuncturedNeighbourhood.isIso_complementAdicQuotientToLimit_lt` — the
  comparison on a single neighbourhood in **every** degree `i < s`, degree zero included.
* `Stacks.Algebraization.PuncturedNeighbourhood.comparison_and_finiteness` — **Stacks 0DXQ** for
  `ℱ = M̃|_U`, on one ideal `J₀`: the comparison under assumptions (1) and (2), and the
  finiteness as an implication from the source's extra depth bound, which is where the source
  asks for it.

## The route

The source's conclusion has three ingredients and each is supplied separately.

*The open `V₀`.*  Stacks 0DXP, `Stacks.Algebraization.exists_isLocalAlgebraizationIdeal`, supplies
an ideal `J₁` with `V(J₁) ∩ V(I) = {𝔪}` for which the comparison holds at every further
shrinking, and Stacks 0DXN, through
`Stacks.Algebraization.PuncturedNeighbourhood.finite_neighbourhoodCohomology`, supplies an ideal
`J₂` for the finiteness.  The theorem asserts both at a single `V₀`, so `J₀` is taken to be
`J₁ ⊓ J₂`: its zero locus is the union of the two zero loci, by
`PrimeSpectrum.zeroLocus_inf`, so intersecting with `V(I)` still leaves exactly `{𝔪}`, and an
ideal below the meet is below each of the two.

*The comparison in degrees `1 ≤ i < s`.*  This is
`Stacks.Algebraization.isIso_complementAdicQuotientToLimit_of_isLocalAlgebraizationIdeal'`.

*The comparison in degree zero.*  This is
`Stacks.Algebraization.isIso_complementAdicQuotientToLimit_zero`, which needs a
`Stacks.LocalCohomology.LocalizationTriangleData` for `J`.  That is data, not a hypothesis:
`Stacks.LocalCohomology.nonempty_localizationTriangleData` produces one from any finite
generating family of `J`, and over a Noetherian ring every ideal has one.  The bound `1 ≤ s` it
asks for is the degree hypothesis `(0 : ℤ) < s` read in that degree.

*The limit on the punctured spectrum.*  The source takes the limit on `U`, while the comparison
of Stacks 0DWR produces it on `V`.  Excision closes the gap:
`Stacks.Algebraization.complementAdicQuotientToExcisedLimit` is the canonical map with the limit
taken on the larger open, and `Stacks.Algebraization.isIso_complementAdicQuotientToExcisedLimit`
says it is invertible together with the map into the limit on `V`.  The hypothesis it needs,
`V(J) ∩ V(I) = V(𝔪)`, is `V(J) ∩ V(I) = {𝔪}` together with
`AlgebraicGeometry.zeroLocus_maximalIdeal_eq_singleton`.

## Implementation notes

`U = Spec A ∖ {𝔪}` is spelled as the complement of `V(𝔪)`, which is the same open by
`AlgebraicGeometry.zeroLocus_maximalIdeal_eq_singleton`; the cohomology on it is
`Stacks.LocalCohomologySequence.complementCohomologyBaseFunctor` at the maximal ideal, as in
`StacksFrontier/RingTheory/LocalCohomology/PuncturedSpectrumDescendingChain.lean`.

Opens of `U` containing `U ∩ Y` are quantified as ideals, as the source itself does: with
`V = X ∖ V(J)`, the conditions `V ⊆ U` and `U ∩ Y ⊆ V` together say exactly
`V(J) ∩ V(I) = {𝔪}`.

No `@[stacks 0DXQ]` attribute is attached in this file: the statements below are the theorem for
the sheaf `M̃|_U` attached to a finite module, which is one of the two moves of the source proof,
the other being the choice of such an `M` for an arbitrary coherent sheaf on `U`.  That other
move is *not* outstanding — it is `Stacks.LocalCohomology.exists_finiteModule_iso_restrict_tilde`,
Stacks 0BK0 (1), in
`StacksFrontier/AlgebraicGeometry/LocalCohomology/Generalities/QuasiCoherentExtension.lean` — and
the
tag sits where the two moves are combined, on `Stacks.Algebraization.coherentFormalAlgebraization`
in `StacksFrontier/AlgebraicGeometry/FormalGeometry/CoherentSheafPuncturedAlgebraization.lean`,
which
states the theorem at its own hypotheses for an arbitrary coherent `ℱ`.  Read the absence of the
attribute here as a pointer there, not as a gap.

## References

* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
* [Stacks Project, Tag 0DXP](https://stacks.math.columbia.edu/tag/0DXP)
* [Stacks Project, Tag 0DXN](https://stacks.math.columbia.edu/tag/0DXN)
* [Stacks Project, Tag 0DWS](https://stacks.math.columbia.edu/tag/0DWS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite
open AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization.PuncturedNeighbourhood

open Stacks.LocalCohomology Stacks.LocalCohomologySequence

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-! ### The readings of `V(J) ∩ V(I) = {𝔪}` -/

omit [IsNoetherianRing A] in
/-- **`V(J) ∩ V(I) = {𝔪}` forces `V(𝔪) ⊆ V(J)`**, that is `Spec A ∖ V(J) ⊆ U`: the closed point
lies in `V(J)` because it lies in the intersection. -/
theorem zeroLocus_maximalIdeal_subset_zeroLocus {I J : Ideal A}
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A}) :
    PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A) ⊆
      PrimeSpectrum.zeroLocus (J : Set A) := by
  rw [zeroLocus_maximalIdeal_eq_singleton, ← hV]
  exact Set.inter_subset_left

omit [IsNoetherianRing A] in
/-- **`V(J) ∩ V(I) = {𝔪}` read as `V(J) ∩ V(I) = V(𝔪)`**, which is the form the excision
statement takes its hypothesis in. -/
theorem zeroLocus_inter_eq_zeroLocus_maximalIdeal {I J : Ideal A}
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A}) :
    PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A) :=
  hV.trans (zeroLocus_maximalIdeal_eq_singleton A).symm

omit [IsNoetherianRing A] in
/-- **`V(J) ∩ V(I) = {𝔪}` forces `J ⊆ 𝔪`**, that is: the open `V = Spec A ∖ V(J)` is an open of
the punctured spectrum `U`.  The zero locus of `J` contains the closed point, so `J` is contained
in the prime that closed point is. -/
theorem le_maximalIdeal_of_zeroLocus_inter {I J : Ideal A}
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A}) :
    J ≤ maximalIdeal A :=
  Stacks.LocalCohomology.le_maximalIdeal_of_zeroLocus_nonempty A J
    ⟨closedPoint A, (hV.ge (Set.mem_singleton _)).1⟩

/-! ### The canonical map of the theorem -/

/-- **The canonical map `H^i(V, Ñ) ⟶ lim_n H^i(U, (N/IⁿN)~)`** of Stacks 0DXQ, for
`V = Spec A ∖ V(J)` an open of the punctured spectrum `U` containing `U ∩ V(I)`.  It is the
canonical map into the limit taken on `V` followed by the inverse of the excision isomorphism
identifying that limit with the limit taken on `U`. -/
def neighbourhoodToPuncturedLimit (I J : Ideal A) (N : ModuleCat.{u} A)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (i : ℕ) :
    (complementCohomologyBaseFunctor (A := CommRingCat.of A) J i).obj N ⟶
      limit (adicQuotientModuleSystem A I N ⋙
        complementCohomologyBaseFunctor (A := CommRingCat.of A) (maximalIdeal A) i) :=
  complementAdicQuotientToExcisedLimit A I J (maximalIdeal A) N
    (zeroLocus_inter_eq_zeroLocus_maximalIdeal hV)
    (zeroLocus_maximalIdeal_subset_zeroLocus hV) i

/-! ### The comparison in every degree below `s` -/

/-- **The comparison on a single neighbourhood in every degree `i < s`.**  For an ideal `J₀` with
the property of Stacks 0DXP and `J ⊆ J₀` with `V(J) ∩ V(I) = {𝔪}`, the canonical map

`H^i(Spec A ∖ V(J), M̃) ⟶ lim_n H^i(Spec A ∖ V(J), (M/IⁿM)~)`

is an isomorphism for every `i < s`.  Degree zero is
`Stacks.Algebraization.isIso_complementAdicQuotientToLimit_zero` and the positive degrees are
`Stacks.Algebraization.isIso_complementAdicQuotientToLimit_of_isLocalAlgebraizationIdeal'`. -/
theorem isIso_complementAdicQuotientToLimit_lt {I : Ideal A} [IsAdicComplete I A] {hI : I ≠ ⊤}
    {s : ℤ} {J₀ : Ideal A} (H : IsLocalAlgebraizationIdeal (M := M) I hI s J₀)
    (J : Ideal A) (hJJ₀ : J ≤ J₀)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (i : ℕ) (hi : (i : ℤ) < s) :
    IsIso (complementAdicQuotientToLimit A I J (ModuleCat.of A M) i) := by
  obtain ⟨D⟩ := nonempty_localizationTriangleData.{u, u} A J (Ideal.fg_of_isNoetherianRing J)
  match i with
  | 0 =>
      exact isIso_complementAdicQuotientToLimit_zero H J hJJ₀ (Ideal.fg_of_isNoetherianRing J) D
        hV (by push_cast at hi; omega)
  | (p + 1) =>
      exact isIso_complementAdicQuotientToLimit_of_isLocalAlgebraizationIdeal' H J hJJ₀ hV (p + 1)
        p.succ_pos (by push_cast at hi ⊢; omega)

/-! ### Stacks 0DXQ for `M̃|_U` -/

/-- **Stacks 0DXQ for the coherent sheaf `ℱ = M̃|_U`.**  Let `(A, 𝔪)` be a Noetherian local ring
which has a dualizing complex and is complete with respect to an ideal `I`, set `X = Spec A`,
`Y = V(I)`, `U = X ∖ {𝔪}`, let `M` be a finite `A`-module and let `ℱ = M̃|_U`.  Assume

1. `cd(A, I) ≤ d`, and
2. for every point of `X ∖ Y` whose closure in `X` meets `U ∩ Y`, the stalk of `ℱ` has depth at
   least `s`, or its depth plus the dimension of the closure exceeds `d + s`,

Then there is an
open `V₀ ⊆ U` containing `U ∩ Y` — namely `V₀ = X ∖ V(J₀)` — such that for every open `V ⊆ V₀`
containing `U ∩ Y` — that is, for every ideal `J ⊆ J₀` with `V(J) ∩ V(I) = {𝔪}` — and every
degree `i < s`, the canonical map

`H^i(V, ℱ) ⟶ lim_n H^i(U, ℱ/Iⁿℱ)`

is an isomorphism; and if in addition `depth(ℱ_x) + dim(closure of x) > s` for every
`x ∈ U ∩ Y`, then `H^i(V, ℱ)` is a finite `A`-module.

The second clause is an implication, exactly as in the source: the comparison is asserted under
assumptions (1) and (2) alone, and the extra depth bound is what the source adds for the
finiteness and for nothing else.  The single `J₀` serving both clauses is obtained by a case
distinction on that bound: with it, `J₀` is the meet of the ideal of Stacks 0DXP and the ideal
of the finiteness clause, whose zero loci still meet `V(I)` in `{𝔪}` only because
`V(J₁ ⊓ J₂) = V(J₁) ∪ V(J₂)`; without it, `J₀` is the ideal of Stacks 0DXP and the implication
is vacuous.

Nothing beyond the hypotheses of the theorem is assumed: the stabilizing data of Stacks 0EFI and
the bound `0 ≤ d` are constructed from assumption (1), the localization triangle data of degree
zero is constructed from a finite generating family of `J`, and the ideal `J₀` is produced by
Stacks 0DXP and Stacks 0DXN. -/
theorem comparison_and_finiteness (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A)) (H : Hypotheses (M := M) I s d omega) :
    ∃ J₀ : Ideal A,
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          {closedPoint A} ∧
        ∀ J : Ideal A, J ≤ J₀ →
          ∀ hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
            {closedPoint A},
          ∀ i : ℕ, (i : ℤ) < s →
            IsIso (neighbourhoodToPuncturedLimit I J (ModuleCat.of A M) hV i) ∧
              (DepthAddDimGtAtMaximalIdeal (M := M) I s →
                Module.Finite A (neighbourhoodCohomology (M := M) J i)) := by
  classical
  have := H.adicComplete
  obtain ⟨J₁, hJ₁⟩ := exists_isLocalAlgebraizationIdeal (M := M) I s d omega
    H.toLocalAlgebraizationHypotheses
  have hiso : ∀ J : Ideal A, J ≤ J₁ →
      ∀ hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        {closedPoint A},
      ∀ i : ℕ, (i : ℤ) < s →
        IsIso (neighbourhoodToPuncturedLimit I J (ModuleCat.of A M) hV i) := by
    intro J hJ hV i hi
    exact isIso_complementAdicQuotientToExcisedLimit A I J (maximalIdeal A) (ModuleCat.of A M)
      (zeroLocus_inter_eq_zeroLocus_maximalIdeal hV)
      (zeroLocus_maximalIdeal_subset_zeroLocus hV) i
      (isIso_complementAdicQuotientToLimit_lt hJ₁ J hJ hV i hi)
  by_cases hdepth : DepthAddDimGtAtMaximalIdeal (M := M) I s
  · obtain ⟨J₂, hJ₂inter, hJ₂fin⟩ :=
      exists_ideal_finite_neighbourhoodCohomology (M := M) I s d omega H hdepth
    refine ⟨J₁ ⊓ J₂, ?_, fun J hJ hV i hi =>
      ⟨hiso J (hJ.trans inf_le_left) hV i hi,
        fun _ => hJ₂fin J (hJ.trans inf_le_right) hV i hi⟩⟩
    rw [PrimeSpectrum.zeroLocus_inf, Set.union_inter_distrib_right, hJ₁.zeroLocus_inter,
      hJ₂inter, Set.union_self]
  · exact ⟨J₁, hJ₁.zeroLocus_inter, fun J hJ hV i hi =>
      ⟨hiso J hJ hV i hi, fun h => absurd h hdepth⟩⟩

end Stacks.Algebraization.PuncturedNeighbourhood

end
