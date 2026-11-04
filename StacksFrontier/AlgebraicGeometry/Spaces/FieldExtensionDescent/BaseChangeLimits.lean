module

public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize

/-!
# Base change of presheaves preserves limits

Changing the base of a slice from `U` to `V` along `f : V ⟶ U` restricts presheaves along
`CategoryTheory.Over.map f`, and that restriction is the right adjoint of the lower-shriek
extension, `CategoryTheory.OverShriek.relocalizeAdjunction`. So it preserves all limits.

For a big fppf site this says that the base change of an algebraic space along a field
extension commutes with fibre products and with finite and arbitrary products: a power of the
projective line over `k`, for instance, base changes to the corresponding power of its own base
change. That compatibility is what lets a statement proved over an extension of the ground
field about an object built from products be read as a statement about the base change of the
object built over the ground field.

## Main results

* `CategoryTheory.OverShriek.relocalizeRestrict_isRightAdjoint`: restriction along
  `CategoryTheory.Over.map f` is a right adjoint.
* `CategoryTheory.OverShriek.preservesLimitsOfSize_relocalizeRestrict` and
  `CategoryTheory.OverShriek.preservesLimits_relocalizeRestrict`: it therefore preserves limits.

## Implementation notes

Limits of presheaves of types are computed objectwise, so this could also be read off from the
construction of `CategoryTheory.OverShriek.relocalizeRestrict` as a whiskering; deducing it
from the adjunction avoids producing the objectwise comparison by hand and gives the statement
at every universe through `CategoryTheory.Limits.PreservesLimitsOfSize`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.OverShriek

universe w w' v u

variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U)

/-- Restriction of presheaves along `CategoryTheory.Over.map f` is a right adjoint: its left
adjoint is the lower-shriek extension. -/
instance relocalizeRestrict_isRightAdjoint :
    (relocalizeRestrict f).IsRightAdjoint :=
  ⟨_, ⟨relocalizeAdjunction f⟩⟩

/-- **Base change of presheaves preserves limits**, at every universe. -/
lemma preservesLimitsOfSize_relocalizeRestrict :
    PreservesLimitsOfSize.{w, w'} (relocalizeRestrict f) :=
  (relocalizeAdjunction f).rightAdjoint_preservesLimits

/-- **Base change of presheaves preserves limits.** In particular it takes a product of
presheaves over `U` to the product of their base changes over `V`. -/
instance preservesLimits_relocalizeRestrict :
    PreservesLimits (relocalizeRestrict f) :=
  preservesLimitsOfSize_relocalizeRestrict f

end CategoryTheory.OverShriek

end
