module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ExceptionalFromChart
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.ChartMembership
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowupStepSequence
public import StacksCore.Tactic.StacksAttribute

/-!
# The vanishing ideal of a closed point in its local ring

## Main results

* `AlgebraicGeometry.stalk_vanishingIdeal_closedPoint_eq_maximalIdeal`: the ideal induced in the
  local ring at a closed point by the vanishing ideal of that point is the maximal ideal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The ideal induced in the local ring at a closed point by the vanishing ideal of that point is
the maximal ideal. -/
public theorem stalk_vanishingIdeal_closedPoint_eq_maximalIdeal {X : Scheme.{u}} {p : X}
    (hp : IsClosed ({p} : Set X)) :
    AlgebraicGeometry.IdealSheafData.stalk
        (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds X)) p =
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) := by
  rw [show (⟨{p}, hp⟩ : Closeds X) = Closeds.closure ({p} : Set X) by ext; simp]
  exact stalk_vanishingIdeal_closure_singleton_eq_maximalIdeal p

end AlgebraicGeometry

end
