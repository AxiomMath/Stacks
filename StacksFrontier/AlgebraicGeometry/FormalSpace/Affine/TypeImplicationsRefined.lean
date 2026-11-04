module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.CountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.TypeImplications
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Types
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation

/-!
# Implications between the types of affine formal algebraic space: composites

A Noetherian affine formal algebraic space is countably indexed, obtained by composing the
implications Noetherian ⇒ adic\* ⇒ adic ⇒ weakly adic ⇒ countably indexed.

## Main results

* `isCountablyIndexed_of_isNoetherian`: a Noetherian affine formal algebraic space is countably
  indexed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A Noetherian affine formal algebraic space is countably indexed. -/
theorem isCountablyIndexed_of_isNoetherian {X : FppfSheaf B S hS}
    (hX : IsNoetherian B S hS X) : IsCountablyIndexed B S hS X :=
  isCountablyIndexed_of_isWeaklyAdic B S hS (isWeaklyAdic_of_isAdic B S hS
    (isAdic_of_isAdicStar B S hS (isAdicStar_of_isNoetherian B S hS hX)))

end AlgebraicGeometry.FormalSpace

end
