module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowupStillGood
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpSituation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ResolutionStages
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.SingularLocusFinite
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteLocalAssembly
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalencePort
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.StalkBaseChangePullback
public import StacksFrontier.AlgebraicGeometry.Blowup.FiniteOverLocalDimensionOne
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.StageBlowUp

/-!
# The singular points of the blowup of a rational double point

Let `A` be the ring of a Situation [Stacks, Tag 0BGC] and let `X` be the blowup of `Spec(A)` in
its maximal ideal. Then `X` has dimension at most two, and every singular point of `X` is a closed
point.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_blowUp_maximalIdeal_le_two`: the blowup of the spectrum
  of a two-dimensional Noetherian local domain in its maximal ideal has dimension at most two.
* `AlgebraicGeometry.RationalDoublePointSituation.isClosed_singleton_of_mem_singularLocus_blowUp`:
  a singular point of the blowup is a closed point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The blowup of the spectrum of a two-dimensional Noetherian local domain in its maximal ideal
has dimension at most two. -/
theorem topologicalKrullDim_blowUp_maximalIdeal_le_two (A : Type u) [CommRing A] [IsLocalRing A]
    [IsDomain A] [IsNoetherianRing A] (hdim : ringKrullDim A = 2) :
    topologicalKrullDim (blowUp (maximalIdealSheaf A)) ≤ 2 := by
  rw [topologicalKrullDim_eq_of_isModification _ (isModification_blowUpToBase_maximalIdeal A hdim)]
  show topologicalKrullDim (PrimeSpectrum A) ≤ 2
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hdim]

/-- The support of the maximal ideal sheaf of a local ring is the closed point. -/
theorem coe_support_maximalIdealSheaf (A : Type u) [CommRing A] [IsLocalRing A] :
    ((maximalIdealSheaf A).support : Set (Spec (.of A))) = {closedPoint A} := by
  rw [← vanishingIdeal_closedPoint_eq_maximalIdealSheaf A
    (IsLocalRing.isClosed_singleton_closedPoint A)]
  simp
  rfl

namespace RationalDoublePointSituation

variable (S : RationalDoublePointSituation.{u})

/-- A singular point of the blowup of `Spec(A)` in its maximal ideal is a closed point. -/
theorem isClosed_singleton_of_mem_singularLocus_blowUp (x : blowUp (maximalIdealSheaf S.A))
    (hx : x ∈ singularLocus (blowUp (maximalIdealSheaf S.A))) :
    IsClosed ({x} : Set (blowUp (maximalIdealSheaf S.A))) := by
  have := S.isNormal_blowUp
  have : IsLocallyNoetherian (blowUp (maximalIdealSheaf S.A)) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase (maximalIdealSheaf S.A))
  exact isClosed_singleton_of_mem_singularLocus _
    (topologicalKrullDim_blowUp_maximalIdeal_le_two S.A S.dimension_two) x hx

end RationalDoublePointSituation

end AlgebraicGeometry

end
