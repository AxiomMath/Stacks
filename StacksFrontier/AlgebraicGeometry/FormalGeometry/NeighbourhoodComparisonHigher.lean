module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementAdicQuotientLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedNeighbourhoodCohomologyFiniteness
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportNatural
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportTildeNatIso

/-!
# The comparison clause of Stacks 0DXQ on a neighbourhood, in positive degrees

Let `(A, 𝔪)` be a Noetherian local ring which has a dualizing complex and is `I`-adically
complete, let `M` be a finite `A`-module and let `s`, `d` be integers satisfying the two numbered
assumptions of Stacks 0DXQ. For an ideal `J` with `V(J) ∩ V(I) = {𝔪}` put `V = Spec A ∖ V(J)`.
This file proves that for `1 ≤ p` and `p + 1 ≤ s` the canonical map

`H^p(V, M̃) ⟶ lim_n H^p(V, (M/IⁿM)~)`

is an isomorphism, for every `J` inside the ideal `J₀` that Stacks 0DXP supplies.

This is the comparison of Stacks 0DXQ in degrees `1 ≤ p < s`, read with both sides taken on the
same neighbourhood `V`. The source takes the right-hand limit over the whole punctured spectrum
`U`; the two agree because the quotients `ℱ/Iⁿℱ` vanish off the formal locus `U ∩ V(I) ⊆ V`,
which is a separate statement about the restriction map and is not used here.

## The route

Stacks 0DXP supplies `J₀`, and
`Stacks.Algebraization.isIso_homology_completedLocalCohomologyUnit_of_isLocalAlgebraizationIdeal`
turns its conclusion into invertibility of the derived `I`-adic completion unit on degree-`r`
cohomology for `r ≤ s`. `Stacks.Algebraization.isIso_localCohomologyAdicQuotientToLimit` then
makes the canonical map `H^r_J(M) ⟶ lim_n H^r_J(M/IⁿM)` invertible, and
`Stacks.Algebraization.isIso_complementAdicQuotientToLimit_of_natIso` transports that to the
cohomology on `V` along the comparison of Stacks 0DWR above degree zero, read as a natural
isomorphism of functors of the module.

## Main results

* `Stacks.Algebraization.PuncturedNeighbourhood.Hypotheses.toLocalAlgebraizationHypotheses` —
  the hypotheses of Stacks 0DXQ are the hypotheses of Stacks 0DXP; the two structures have the
  same five fields.
* `Stacks.Algebraization.isIso_complementAdicQuotientToLimit_of_isLocalAlgebraizationIdeal` —
  the comparison at one neighbourhood is an isomorphism in degrees `1 ≤ p` with `p + 1 ≤ s`.
* `Stacks.Algebraization.PuncturedNeighbourhood.exists_isIso_complementAdicQuotientToLimit` —
  the same with the ideal `J₀` produced from the hypotheses of the theorem.

## Implementation notes

The comparison of Stacks 0DWR above degree zero enters as an explicit natural isomorphism
`e` of the two functors of the module. Its two halves are
`Stacks.LocalCohomologySequence.complementDeltaBaseNatIso`, the connecting morphism of the long
exact cohomology sequence of `V(J)`, and the degreewise comparison of Stacks 0A6T between
cohomology with support in `V(J)` of `M̃` and the algebraic local cohomology of `M`. Taking it as
a parameter here keeps this file independent of which of the two spellings of the latter
comparison is used, and costs nothing: it is a statement about functors, with no reference to
`I`, to `s`, or to the module `M`.

No `@[stacks 0DXQ]` attribute is attached in this file. The statements below are the comparison
clause of the theorem read on a single neighbourhood on both sides, which is one of the two
halves of that clause, so they are inputs to the tag rather than clauses of it. The tag itself
sits on `Stacks.Algebraization.coherentFormalAlgebraization` in
`CoherentSheafPuncturedAlgebraization.lean`, which assembles this file, the degree-zero half and
the choice of a finite `M` for an arbitrary coherent sheaf into the whole theorem.

## References

* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
* [Stacks Project, Tag 0DXP](https://stacks.math.columbia.edu/tag/0DXP)
* [Stacks Project, Tag 0DXJ](https://stacks.math.columbia.edu/tag/0DXJ)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology Stacks.LocalCohomologySequence

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **The comparison at one neighbourhood is an isomorphism in degrees `1 ≤ p` with
`p + 1 ≤ s`.** For an ideal `J₀` with the property that Stacks 0DXP asserts, every ideal
`J ⊆ J₀` with `V(J) ∩ V(I) = {𝔪}` has the property that

`H^p(Spec A ∖ V(J), M̃) ⟶ lim_n H^p(Spec A ∖ V(J), (M/IⁿM)~)`

is an isomorphism in those degrees.

The degree shift is the one of the source: the local cohomology degree that is consumed is
`p + 1`, which is why the conclusion holds for `p + 1 ≤ s` and hence, for a natural number `p`,
for `p < s`. -/
theorem isIso_complementAdicQuotientToLimit_of_isLocalAlgebraizationIdeal
    {I : Ideal A} {hI : I ≠ ⊤} {s : ℤ} {J₀ : Ideal A}
    (H : IsLocalAlgebraizationIdeal (M := M) I hI s J₀)
    (J : Ideal A) (hJ : J ≤ J₀)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (p : ℕ) (hps : ((p : ℤ) + 1) ≤ s)
    (e : complementCohomologyBaseFunctor (A := CommRingCat.of A) J p ≅
      localCohomologyDegreeFunctor A J (Ideal.fg_of_isNoetherianRing J) ((p : ℤ) + 1)) :
    IsIso (complementAdicQuotientToLimit A I J (ModuleCat.of A M) p) := by
  have hunit := isIso_homology_completedLocalCohomologyUnit_of_isLocalAlgebraizationIdeal
    (M := M) H J hJ hV ((p : ℤ) + 1) hps
  have hlc : IsIso (localCohomologyAdicQuotientToLimit A I J
      (Ideal.fg_of_isNoetherianRing J) (ModuleCat.of A M) ((p : ℤ) + 1)) :=
    isIso_localCohomologyAdicQuotientToLimit A I J (ModuleCat.of A M) hV ((p : ℤ) + 1) hunit
  exact isIso_complementAdicQuotientToLimit_of_natIso A I J (Ideal.fg_of_isNoetherianRing J)
    (ModuleCat.of A M) p e hlc

namespace PuncturedNeighbourhood

/-- **The hypotheses of Stacks 0DXQ are the hypotheses of Stacks 0DXP.** The two structures
record the same five conditions: properness of `I`, `I`-adic completeness, a dualizing complex,
assumption (1) on the cohomological dimension and assumption (2) on depth and dimension. -/
theorem Hypotheses.toLocalAlgebraizationHypotheses {I : Ideal A} {s d : ℤ}
    {omega : DerivedCategory (ModuleCat.{u} A)} (H : Hypotheses (M := M) I s d omega) :
    LocalAlgebraizationHypotheses (M := M) I s d omega where
  ne_top := H.ne_top
  adicComplete := H.adicComplete
  dualizing := H.dualizing
  cohomologicalDimension_le := H.cohomologicalDimension_le
  depthOrDimensionBound := H.depthOrDimensionBound

/-- **The comparison clause of Stacks 0DXQ on a neighbourhood, in positive degrees.** Under the
hypotheses of the theorem there is an ideal `J₀` with `V(J₀) ∩ V(I) = {𝔪}` — that is, an open
`V₀ = Spec A ∖ V(J₀)` of the punctured spectrum containing `U ∩ V(I)` — such that for every
`J ⊆ J₀` with `V(J) ∩ V(I) = {𝔪}`, that is for every open `V = Spec A ∖ V(J)` inside `V₀`
containing `U ∩ V(I)`, the canonical map

`H^i(V, M̃) ⟶ lim_n H^i(V, (M/IⁿM)~)`

is an isomorphism in every degree `i` with `1 ≤ i < s`.

The right-hand side is the limit taken on `V`; the source takes it on the punctured spectrum
`U`, and the restriction from `U` to `V` is an isomorphism on each term because the quotients
are supported on `U ∩ V(I) ⊆ V`. That statement about the restriction map is separate and is not
used here. -/
theorem exists_isIso_complementAdicQuotientToLimit (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A)) (H : Hypotheses (M := M) I s d omega)
    (e : ∀ J : Ideal A, ∀ p : ℕ, 1 ≤ p →
      (complementCohomologyBaseFunctor (A := CommRingCat.of A) J p ≅
        localCohomologyDegreeFunctor A J (Ideal.fg_of_isNoetherianRing J) ((p : ℤ) + 1))) :
    ∃ J₀ : Ideal A,
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          {closedPoint A} ∧
        ∀ J : Ideal A, J ≤ J₀ →
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
            {closedPoint A} →
          ∀ i : ℕ, 1 ≤ i → (i : ℤ) < s →
          IsIso (complementAdicQuotientToLimit A I J (ModuleCat.of A M) i) := by
  obtain ⟨J₀, hJ₀⟩ := exists_isLocalAlgebraizationIdeal (M := M) I s d omega
    H.toLocalAlgebraizationHypotheses
  refine ⟨J₀, hJ₀.zeroLocus_inter, fun J hJ hV i hi1 hi ↦ ?_⟩
  exact isIso_complementAdicQuotientToLimit_of_isLocalAlgebraizationIdeal (M := M) hJ₀ J hJ hV i
    (by omega) (e J i hi1)

end PuncturedNeighbourhood

/-! ### The comparison of Stacks 0DWR above degree zero, assembled -/

/-- **The comparison of Stacks 0DWR above degree zero, as a natural isomorphism of functors of
the module, with the right-hand side in the coreflection model of local cohomology.** For
`1 ≤ p` the functors `N ↦ H^p(Spec A ∖ V(J), Ñ)` and `N ↦ H^{p+1}_J(N)` on `A`-modules are
isomorphic.

It is the composite of three natural isomorphisms: the connecting morphism of the long exact
cohomology sequence of `V(J)`, the degreewise comparison of Stacks 0A6T, and the comparison of
the two models of local cohomology of Stacks 0955. -/
def complementCohomologyBaseLocalCohomologyNatIso (J : Ideal A) (p : ℕ)
    (hp : 0 < p) :
    complementCohomologyBaseFunctor (A := CommRingCat.of A) J p ≅
      localCohomologyDegreeFunctor A J (Ideal.fg_of_isNoetherianRing J) ((p : ℤ) + 1) :=
  haveI : IsNoetherianRing (CommRingCat.of A) := inferInstanceAs (IsNoetherianRing A)
  complementDeltaBaseNatIso (A := CommRingCat.of A) J p hp ≪≫
    cohomologyWithSupportTildeNatIso (A := CommRingCat.of A) J
      (Ideal.fg_of_isNoetherianRing J) (p + 1) ≪≫
    (by
      rw [show ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) by push_cast; ring]
      exact sectionsWithSupportRightDerivedIsoLocalCohomologyNatIso A J
        (Ideal.fg_of_isNoetherianRing J) (p + 1))

/-- **The comparison at one neighbourhood is an isomorphism in degrees `1 ≤ p` with
`p + 1 ≤ s`**, with the comparison of Stacks 0DWR discharged rather than assumed. -/
theorem isIso_complementAdicQuotientToLimit_of_isLocalAlgebraizationIdeal'
    {I : Ideal A} {hI : I ≠ ⊤} {s : ℤ} {J₀ : Ideal A}
    (H : IsLocalAlgebraizationIdeal (M := M) I hI s J₀)
    (J : Ideal A) (hJ : J ≤ J₀)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (p : ℕ) (hp : 0 < p) (hps : ((p : ℤ) + 1) ≤ s) :
    IsIso (complementAdicQuotientToLimit A I J (ModuleCat.of A M) p) :=
  isIso_complementAdicQuotientToLimit_of_isLocalAlgebraizationIdeal (M := M) H J hJ hV p hps
    (complementCohomologyBaseLocalCohomologyNatIso J p hp)

namespace PuncturedNeighbourhood

/-- **The comparison clause of Stacks 0DXQ on a neighbourhood, in positive degrees, with no
hypothesis beyond those of the theorem.** Under the hypotheses of Stacks 0DXQ there is an ideal
`J₀` with `V(J₀) ∩ V(I) = {𝔪}` such that for every `J ⊆ J₀` with `V(J) ∩ V(I) = {𝔪}` the
canonical map

`H^i(Spec A ∖ V(J), M̃) ⟶ lim_n H^i(Spec A ∖ V(J), (M/IⁿM)~)`

is an isomorphism in every degree `i` with `1 ≤ i < s`. -/
theorem exists_isIso_complementAdicQuotientToLimit' (I : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A)) (H : Hypotheses (M := M) I s d omega) :
    ∃ J₀ : Ideal A,
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          {closedPoint A} ∧
        ∀ J : Ideal A, J ≤ J₀ →
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
            {closedPoint A} →
          ∀ i : ℕ, 1 ≤ i → (i : ℤ) < s →
          IsIso (complementAdicQuotientToLimit A I J (ModuleCat.of A M) i) :=
  exists_isIso_complementAdicQuotientToLimit I s d omega H
    (fun J p hp => complementCohomologyBaseLocalCohomologyNatIso J p hp)

end PuncturedNeighbourhood

end Stacks.Algebraization

end
