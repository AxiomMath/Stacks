module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularAtGeometricPoints
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom

/-!
# Descent of regularity along a flat morphism of algebraic spaces

Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over a scheme `S` with `Y` locally
Noetherian. If `X` is regular at a point `x`, then `Y` is regular at the image of `x`.

## Main results

* `AlgebraicGeometry.Space.isRegularAt_of_isFlat`: regularity at a point descends along a flat
  morphism of algebraic spaces with locally Noetherian target.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- Regularity at a point descends along a flat morphism of algebraic spaces: if `f : X ⟶ Y` is
flat, `Y` is locally Noetherian and `X` is regular at `x`, then `Y` is regular at the image of
`x` under `f`. -/
theorem isRegularAt_of_isFlat (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsFlat B S hS f)
    (hN : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (x : points B S hS X) (hx : IsRegularAt B S hS X x) :
    IsRegularAt B S hS Y (pointsMap B S hS X f x) := by
  obtain ⟨xbar, hxbar, hreg⟩ := ((isRegularAt_tfae B S hS X hX x).out 1 3).mp hx
  let : IsLocalRing (etaleLocalRing B S hS Y (geometricPointMap f xbar)) :=
    isLocalRing_etaleLocalRing B S hS Y hY (geometricPointMap f xbar)
  let : IsNoetherianRing (etaleLocalRing B S hS Y (geometricPointMap f xbar)) :=
    isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B S hS Y hY hN
      (geometricPointMap f xbar)
  let : Algebra (etaleLocalRing B S hS Y (geometricPointMap f xbar))
      (etaleLocalRing B S hS X xbar) := (etaleLocalRingMap hX f xbar).toAlgebra
  let : IsLocalHom (algebraMap (etaleLocalRing B S hS Y (geometricPointMap f xbar))
      (etaleLocalRing B S hS X xbar)) := isLocalHom_etaleLocalRingMap B S hS hX hY f xbar
  let : Module.Flat (etaleLocalRing B S hS Y (geometricPointMap f xbar))
      (etaleLocalRing B S hS X xbar) := flat_etaleLocalRingMap B S hS hX hY f hf xbar
  let : IsRegularLocalRing (etaleLocalRing B S hS X xbar) := hreg
  have key : ∃ ybar : GeometricPoint B S hS Y, ybar.LiesOver (pointsMap B S hS X f x) ∧
      IsRegularLocalRing (etaleLocalRing B S hS Y ybar) := by
    refine ⟨geometricPointMap f xbar, ?_,
      IsRegularLocalRing.of_flat_of_isLocalHom (etaleLocalRing B S hS X xbar)⟩
    change pointsMap B S hS X f xbar.image = pointsMap B S hS X f x
    rw [hxbar]
  exact ((isRegularAt_tfae B S hS Y hY (pointsMap B S hS X f x)).out 3 1).mp key

end AlgebraicGeometry.Space

end
