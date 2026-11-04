module

public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProductRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer

/-!
# Fibre products of formal algebraic spaces

The fibre product of two formal algebraic spaces over an fppf sheaf with representable relative
products satisfies the set-theoretic condition, and it is a formal algebraic space when the base
is separated.

## Main results

* `satisfiesSetTheoreticCondition_pullback_of_isFormalAlgebraicSpace`: the fibre product of two
  formal algebraic spaces satisfies the set-theoretic condition.
* `isFormalAlgebraicSpace_pullback_of_affineStages_of_representableProducts`: the fibre product
  of two formal algebraic spaces is a formal algebraic space if the fibre product of any two
  affine formal algebraic spaces over the same base is one.
* `isFormalAlgebraicSpace_pullback_of_isSeparated'`: the fibre product of two formal algebraic
  spaces over a separated base is a formal algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The set-theoretic condition on a fibre product of formal algebraic spaces -/

/-- The fibre product of two formal algebraic spaces over an fppf sheaf with representable
relative products satisfies the set-theoretic condition. -/
theorem satisfiesSetTheoreticCondition_pullback_of_isFormalAlgebraicSpace
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZrep : HasRepresentableRelativeProducts B S hS Z)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) :
    SatisfiesSetTheoreticCondition B S hS (pullback p q) :=
  satisfiesSetTheoreticCondition_pullback' B S hS p q hZrep hX.1
    (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hX) hY.1
    (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hY)

/-- The fibre product of two formal algebraic spaces over an fppf sheaf with representable
relative products is a formal algebraic space as soon as the fibre product over that sheaf of
any two *affine* formal algebraic spaces is one. -/
theorem isFormalAlgebraicSpace_pullback_of_affineStages_of_representableProducts
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZrep : HasRepresentableRelativeProducts B S hS Z)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hstage : ∀ (X' Y' : FppfSheaf B S hS) (p' : X' ⟶ Z) (q' : Y' ⟶ Z),
      IsAffineFormalAlgebraicSpace B S hS X' → IsAffineFormalAlgebraicSpace B S hS Y' →
      IsFormalAlgebraicSpace B S hS (pullback p' q')) :
    IsFormalAlgebraicSpace B S hS (pullback p q) := by
  have hXrep := hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hX
  have hYrep := hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hY
  have hset := satisfiesSetTheoreticCondition_pullback_of_isFormalAlgebraicSpace B S hS p q
    hZrep hX hY
  refine isFormalAlgebraicSpace_pullback_of_affineStages B S hS p q hX hY hstage hset
    (fun X' a hX' ↦ satisfiesSetTheoreticCondition_pullback' B S hS a (pullback.fst p q) hXrep
      hX'.1 (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hX') hset
      (hasRepresentableRelativeProducts_pullback B S hS p q hXrep hYrep hZrep))

/-- The fibre product of two formal algebraic spaces over a separated fppf sheaf with
representable relative products is a formal algebraic space.

This is `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isSeparated`, which
no longer takes the set-theoretic condition of Stacks 0AIS as an input. -/
public alias isFormalAlgebraicSpace_pullback_of_isSeparated' :=
  isFormalAlgebraicSpace_pullback_of_isSeparated

end AlgebraicGeometry.FormalSpace

end
