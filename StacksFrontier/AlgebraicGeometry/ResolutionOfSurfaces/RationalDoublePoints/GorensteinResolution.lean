module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpRelWellFounded
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.GoodCoordinateStalkBlowUp
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ImpliedProperties.LocalDomain

/-!
# Resolution of Gorenstein rational surface singularities by blowing up singular points

[Stacks, Tag 0BGE]: let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two which defines
a rational singularity, whose completion is normal, and which is Gorenstein. Then there is a finite
sequence of blowups in singular closed points `Xₙ → ⋯ → X₁ → X₀ = Spec(A)` with `Xₙ` regular and
every `Xᵢ` normal with finitely many singular points of the same type.

The sequence is `AlgebraicGeometry.SingularPointBlowupChain` with stage property
`AlgebraicGeometry.IsRationalDoublePointStageNoetherian`: each stage is Noetherian and normal, with
finitely many singular points, each closed, whose local rings are rings of a Situation 0BGC
("of the same type"). The assembly is
`AlgebraicGeometry.exists_chains_isRegular_of_blowUpProperties`; its two inputs are the local
information on one blowup (`AlgebraicGeometry.rationalDoublePointBlowUpProperties`) and the
termination of the process
(`AlgebraicGeometry.RationalDoublePointSituation.wellFounded_blowUpRel`).

The second theorem restates the conclusion as a sequence of normalized blowups at closed points
over the closed point (every stage being normal, the normalization does nothing).

## Main results

* `AlgebraicGeometry.exists_singularPointBlowupChain_isRegular_of_isGorensteinLocalRing`
* `AlgebraicGeometry.exists_normalizedPointBlowupChain_isRegular_of_isGorensteinLocalRing`

## References

* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The relation `≺` between completed rational double points is well founded.** -/
theorem RationalDoublePointSituation.wellFounded_blowUpRel :
    WellFounded RationalDoublePointSituation.BlowUpRel.{u} :=
  RationalDoublePointSituation.wellFounded_blowUpRel_of_propagation fun S _ he x hx =>
    S.isGoodCoordinate_stalk_blowUp he x hx

/-- **[Stacks, Tag 0BGE].** Let `A` be a local normal Nagata domain of dimension two which defines
a rational singularity, whose completion is normal, and which is Gorenstein. Then there is a finite
sequence of blowups in singular closed points `Y = Xₙ → ⋯ → X₀ = Spec(A)` with `Y` regular, every
stage `Xᵢ` being (Noetherian and) normal with finitely many singular points, each closed and with
local ring the ring of a Situation 0BGC. -/
theorem exists_singularPointBlowupChain_isRegular_of_isGorensteinLocalRing
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A] (hN : IsNagataRing A)
    (hdim : ringKrullDim A = 2) (hrat : DefinesRationalSingularity A)
    (hcompl : IsNormalRing (AdicCompletion (maximalIdeal A) A))
    (hgor : letI := hN.1; Dualizing.IsGorensteinLocalRing A) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
      SingularPointBlowupChain IsRationalDoublePointStageNoetherian (Spec (.of A)) Y f ∧
        IsRegular Y :=
  exists_chains_isRegular_of_blowUpProperties rationalDoublePointBlowUpProperties
    RationalDoublePointSituation.wellFounded_blowUpRel A hN hdim hrat hcompl hgor

/-- **[Stacks, Tag 0BGE], as a sequence of normalized blowups.** Under the hypotheses of Tag 0BGE,
`Spec(A)` is resolved by a finite sequence of normalized blowups at closed points lying over the
closed point. -/
theorem exists_normalizedPointBlowupChain_isRegular_of_isGorensteinLocalRing
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A] (hN : IsNagataRing A)
    (hdim : ringKrullDim A = 2) (hrat : DefinesRationalSingularity A)
    (hcompl : IsNormalRing (AdicCompletion (maximalIdeal A) A))
    (hgor : letI := hN.1; Dualizing.IsGorensteinLocalRing A) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
      Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
        {IsLocalRing.closedPoint A} Y f ∧ IsRegular Y := by
  obtain ⟨Y, f, hc, hreg⟩ :=
    exists_singularPointBlowupChain_isRegular_of_isGorensteinLocalRing A hN hdim hrat hcompl hgor
  obtain ⟨-, Y', f', hc', e, -⟩ := hc.factorsAsNormalizedPointBlowups
  exact ⟨Y', f', hc', IsRegular.of_iso e.symm hreg⟩

end AlgebraicGeometry

end
