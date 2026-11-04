module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import Mathlib.Topology.LocallyConstant.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreLocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Fibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.RingTheory.CohenMacaulay.OpenLocus

/-!
# Membership in the open pieces of constant relative dimension

For a flat morphism `f : X ⟶ S` locally of finite presentation with Cohen–Macaulay fibres, a
point of `X` lies in `relativeDimensionOpen f hCM d` exactly when the relative dimension of `f`
at that point is `d`.

## Main results

* `AlgebraicGeometry.mem_relativeDimensionOpen`: `x ∈ relativeDimensionOpen f hCM d` if and only
  if `relativeDimensionFunction f hCM x = d`.
-/

public section

open CategoryTheory TopologicalSpace Function

universe u

namespace AlgebraicGeometry

namespace CohenMacaulayFiber

end CohenMacaulayFiber

/-- A point lies in the canonical piece of relative dimension `d` exactly when the relative
dimension function takes the value `d` at it. -/
public theorem mem_relativeDimensionOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hCM : ∀ s : S, IsCohenMacaulay (f.fiber s)) (d : ℕ) (x : X) :
    x ∈ relativeDimensionOpen f hCM d ↔ relativeDimensionFunction f hCM x = d := by
  have key : ∀ n : ℕ, x ∈ relativeDimensionOpen f hCM n →
      relativeDimensionFunction f hCM x = n := fun n hn => by
    have h := (relativeDimensionFunction_apply f hCM x).symm.trans
      (topologicalKrullDimAt_fiber_eq_of_relativeDimension f (relativeDimensionOpen f hCM n) n
        (relativeDimensionOpen_relativeDimension f hCM n) x hn)
    exact_mod_cast h
  refine ⟨key d, fun h => ?_⟩
  have hx : x ∈ (⨆ n : ℕ, relativeDimensionOpen f hCM n) := by
    rw [iSup_relativeDimensionOpen f hCM]; trivial
  obtain ⟨n, hn⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have := key n hn
  rw [h] at this
  exact this ▸ hn

end AlgebraicGeometry

end
