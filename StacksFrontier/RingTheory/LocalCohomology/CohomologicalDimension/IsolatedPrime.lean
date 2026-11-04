module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimensionBounds
public import StacksFrontier.RingTheory.LocalCohomology.TopLocalCohomology

/-!
# Cohomological dimension bounds the dimension of an isolated prime

Let `(A, 𝔪)` be a Noetherian local ring, let `I ⊆ A` be an ideal and let `𝔭 ⊆ A` be a prime
ideal whose closed subset `V(𝔭)` meets `V(I)` only in the closed point. Then
`dim(A/𝔭) ≤ cd(A, I)`.

Extending `I` along `A → A/𝔭` cannot raise the cohomological dimension (Stacks 0DXA), so it is
enough to bound `cd(A/𝔭, I(A/𝔭))` from below. The hypothesis says exactly that `I(A/𝔭)` cuts out
the closed point of `Spec(A/𝔭)`, hence has the same zero locus as the maximal ideal of `A/𝔭`.
Local cohomology with support in a finitely generated ideal depends on the ideal only through
that zero locus, because having power-torsion cohomology does (Stacks 0953); so
`cd(A/𝔭, I(A/𝔭)) = cd(A/𝔭, 𝔪/𝔭)`, and the latter is `dim(A/𝔭)` by Stacks 0DXE.

## Main definitions

* `Stacks.LocalCohomology.localCohomologyDerivedObjIsoOfZeroLocusEq` — two finitely generated
  ideals with the same zero locus have isomorphic local cohomology.

## Main results

* `Stacks.LocalCohomology.cohomologicalDimension_eq_of_zeroLocus_eq` — the cohomological
  dimension depends on the ideal only through its zero locus.
* `Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension` and
  `Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension'` — Stacks 0DXF, with
  and without the dualizing complex on the completion of `A/𝔭` as a hypothesis.

## Implementation notes

Stacks 0DXE is available both with the existence of a normalized dualizing complex on the
completion as an explicit hypothesis and without it, the hypothesis being discharged by the
local case of Stacks 0BFR. Both forms of Stacks 0DXF are therefore recorded here:
`Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension` carries the hypothesis
for `A/𝔭`, and
`Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension'` is that statement
applied to
`Stacks.LocalCohomology.exists_isNormalizedDualizingComplex_adicCompletion (A ⧸ 𝔭)`, so it has
no hypothesis the source does not have.

The properness of `I` assumed by the source is not a hypothesis: the intersection hypothesis
already puts the closed point in `V(I)`, which gives `I ⊆ 𝔪` directly.

## References

* [Stacks Project, Tag 0DXF](https://stacks.math.columbia.edu/tag/0DXF)
* [Stacks Project, Tag 0DXE](https://stacks.math.columbia.edu/tag/0DXE)
* [Stacks Project, Tag 0DXA](https://stacks.math.columbia.edu/tag/0DXA)
* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- **Local cohomology depends on the ideal only through its zero locus.** For two finitely
generated ideals cutting out the same closed subset of `Spec A`, the two coreflections of `D(A)`
onto the objects with power-torsion cohomology are coreflections onto the same subcategory, hence
agree. -/
def localCohomologyDerivedObjIsoOfZeroLocusEq (A : Type u) [CommRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (hzero : PrimeSpectrum.zeroLocus (J : Set A) = PrimeSpectrum.zeroLocus (I : Set A))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (localCohomologyDerived A J hJ).obj K ≅ (localCohomologyDerived A I hI).obj K := by
  have hProp : Dualizing.derivedPowerTorsionProperty.{u, u} A J hJ =
      Dualizing.derivedPowerTorsionProperty.{u, u} A I hI := by
    funext X
    exact propext (derivedPowerTorsionProperty_iff_of_zeroLocus_eq.{u, u} J I hJ hI hzero X)
  let E := ObjectProperty.fullSubcategoryCongr hProp
  have hIncl : E.functor ⋙ (Dualizing.derivedPowerTorsionProperty A I hI).ι ≅
      (Dualizing.derivedPowerTorsionProperty A J hJ).ι := Iso.refl _
  have hRight := (Dualizing.localCohomologyAdjunction.{u, u} A J hJ).rightAdjointUniq
    (((E.toAdjunction.comp (Dualizing.localCohomologyAdjunction.{u, u} A I hI))).ofNatIsoLeft
      hIncl)
  exact (Dualizing.derivedPowerTorsionProperty A J hJ).ι.mapIso (hRight.app K)

/-- A vanishing bound for the local cohomology of `A` supported on `V(I)` is a vanishing bound
for any other finitely generated ideal with the same zero locus. -/
theorem isLocalCohomologyBound_of_zeroLocus_eq (A : Type u) [CommRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (hzero : PrimeSpectrum.zeroLocus (J : Set A) = PrimeSpectrum.zeroLocus (I : Set A))
    (d : ℤ) (hd : IsLocalCohomologyBound A I hI d) :
    IsLocalCohomologyBound A J hJ d :=
  ⟨hd.1, fun i hi => (hd.2 i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
      (localCohomologyDerivedObjIsoOfZeroLocusEq A I J hI hJ hzero _))⟩

/-- The cohomological dimension of a finitely generated ideal depends on the ideal only through
its zero locus. This is the independence used in Stacks 0DX9 (2). -/
theorem cohomologicalDimension_eq_of_zeroLocus_eq (A : Type u) [CommRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (hzero : PrimeSpectrum.zeroLocus (I : Set A) = PrimeSpectrum.zeroLocus (J : Set A)) :
    cohomologicalDimension A I hI = cohomologicalDimension A J hJ :=
  le_antisymm
    (cohomologicalDimension_le A I hI _
      (isLocalCohomologyBound_of_zeroLocus_eq A J I hJ hI hzero _
        (isLocalCohomologyBound_cohomologicalDimension A J hJ)))
    (cohomologicalDimension_le A J hJ _
      (isLocalCohomologyBound_of_zeroLocus_eq A I J hI hJ hzero.symm _
        (isLocalCohomologyBound_cohomologicalDimension A I hI)))

section Quotient

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  (p : Ideal A) [p.IsPrime]

/-- The quotient of a local ring by a prime ideal is again a local ring, the quotient map being
surjective. -/
local instance isLocalRingQuotient : IsLocalRing (A ⧸ p) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective

/-- **Stacks Project, Tag 0DXF.** Let `(A, 𝔪)` be a Noetherian local ring, `I ⊆ A` a finitely
generated ideal and `𝔭 ⊆ A` a prime ideal with `V(𝔭) ∩ V(I) = {𝔪}`. Then
`dim(A/𝔭) ≤ cd(A, I)`.

The extension of `I` to `A/𝔭` has the same zero locus as `𝔪/𝔭`, so its cohomological dimension
is `dim(A/𝔭)` by Stacks 0DXE, and extending an ideal along a ring map cannot raise the
cohomological dimension by Stacks 0DXA. -/
@[stacks 0DXF "existence of a normalized dualizing complex on the completion of A/𝔭, the local \
case of Stacks 0BFR, is an explicit hypothesis"]
theorem ringKrullDim_quotient_le_cohomologicalDimension
    (I : Ideal A) (hI : I.FG)
    (hinter : PrimeSpectrum.zeroLocus (p : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {IsLocalRing.closedPoint A})
    (d : ℕ) (hdim : ringKrullDim (A ⧸ p) = (d : WithBot ℕ∞))
    (hBFR : ∃ ω : DerivedCategory (ModuleCat.{u} (AdicCompletion
        (IsLocalRing.maximalIdeal (A ⧸ p)) (A ⧸ p))),
      Dualizing.IsNormalizedDualizingComplex.{u, u} ω) :
    (d : ℤ) ≤ cohomologicalDimension A I hI := by
  have hclosedMem : IsLocalRing.closedPoint A ∈
      PrimeSpectrum.zeroLocus (p : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) := by
    rw [hinter]
    exact Set.mem_singleton _
  have hIle : I ≤ IsLocalRing.maximalIdeal A :=
    (PrimeSpectrum.mem_zeroLocus _ _).mp hclosedMem.2
  have : IsLocalHom (Ideal.Quotient.mk p) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hmaxmap : (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk p) =
      IsLocalRing.maximalIdeal (A ⧸ p) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hmfg : (IsLocalRing.maximalIdeal (A ⧸ p)).FG := Ideal.fg_of_isNoetherianRing _
  have hzero :
      PrimeSpectrum.zeroLocus ((I.map (Ideal.Quotient.mk p) : Ideal (A ⧸ p)) : Set (A ⧸ p)) =
        PrimeSpectrum.zeroLocus
          ((IsLocalRing.maximalIdeal (A ⧸ p) : Ideal (A ⧸ p)) : Set (A ⧸ p)) := by
    ext Q
    constructor
    · intro hQ
      have hIcomap : I ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk p) Q).asIdeal :=
        Ideal.map_le_iff_le_comap.mp ((PrimeSpectrum.mem_zeroLocus _ _).mp hQ)
      have hpcomap : p ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk p) Q).asIdeal := by
        intro x hx
        refine Ideal.ker_le_comap (Ideal.Quotient.mk p) ?_
        rwa [Ideal.mk_ker]
      have hcomapClosed : PrimeSpectrum.comap (Ideal.Quotient.mk p) Q =
          IsLocalRing.closedPoint A := by
        have hmem : PrimeSpectrum.comap (Ideal.Quotient.mk p) Q ∈
            ({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A)) := by
          rw [← hinter]
          exact ⟨(PrimeSpectrum.mem_zeroLocus _ _).mpr hpcomap,
            (PrimeSpectrum.mem_zeroLocus _ _).mpr hIcomap⟩
        simpa using hmem
      have hQclosed : Q = IsLocalRing.closedPoint (A ⧸ p) := by
        refine PrimeSpectrum.comap_injective_of_surjective (Ideal.Quotient.mk p)
          Ideal.Quotient.mk_surjective ?_
        rw [hcomapClosed, IsLocalRing.comap_closedPoint]
      exact hQclosed ▸ (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl
    · exact fun hQ => (PrimeSpectrum.mem_zeroLocus _ _).mpr
        (((Ideal.map_mono hIle).trans_eq hmaxmap).trans
          ((PrimeSpectrum.mem_zeroLocus _ _).mp hQ))
  have hcdquot : cohomologicalDimension (A ⧸ p) (I.map (Ideal.Quotient.mk p))
      (hI.map (Ideal.Quotient.mk p)) = (d : ℤ) :=
    (cohomologicalDimension_eq_of_zeroLocus_eq (A ⧸ p) _ _ (hI.map (Ideal.Quotient.mk p)) hmfg
      hzero).trans (cohomologicalDimension_maximalIdeal_eq (A ⧸ p) hmfg d hdim hBFR)
  exact hcdquot.ge.trans (cohomologicalDimension_map_le (Ideal.Quotient.mk p) I hI)

/-- **Stacks Project, Tag 0DXF.** Let `(A, 𝔪)` be a Noetherian local ring, `I ⊆ A` a finitely
generated ideal and `𝔭 ⊆ A` a prime ideal with `V(𝔭) ∩ V(I) = {𝔪}`. Then
`dim(A/𝔭) ≤ cd(A, I)`.

This is `Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension` with its
hypothesis on the completion of `A/𝔭` discharged by
`Stacks.LocalCohomology.exists_isNormalizedDualizingComplex_adicCompletion`. -/
@[stacks 0DXF]
theorem ringKrullDim_quotient_le_cohomologicalDimension'
    (I : Ideal A) (hI : I.FG)
    (hinter : PrimeSpectrum.zeroLocus (p : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {IsLocalRing.closedPoint A})
    (d : ℕ) (hdim : ringKrullDim (A ⧸ p) = (d : WithBot ℕ∞)) :
    (d : ℤ) ≤ cohomologicalDimension A I hI :=
  ringKrullDim_quotient_le_cohomologicalDimension A p I hI hinter d hdim
    (exists_isNormalizedDualizingComplex_adicCompletion (A ⧸ p))

end Quotient

end Stacks.LocalCohomology

end
