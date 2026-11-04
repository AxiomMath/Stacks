module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Properties.NormalStalkDvr
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local rings of a regular scheme at codimension-one points

On a regular scheme the local ring at a point of codimension one is a discrete valuation ring:
a regular scheme is normal by Tag 0569, and the local ring of a locally Noetherian normal scheme
at a point of codimension one is a discrete valuation ring.

Local Noetherianness is not assumed; it is part of regularity, read off the characterisations of
`AlgebraicGeometry.isRegular_tfae`. Integrality is assumed only so that the local ring is a
domain while the statement is read, which is part of what `IsDiscreteValuationRing` asks for;
normality supplies it again inside the proof.

## References

* [Stacks Project, Tag 0569](https://stacks.math.columbia.edu/tag/0569)
* [Stacks Project, Tag 02IS](https://stacks.math.columbia.edu/tag/02IS)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

/-- **The local ring of a regular integral scheme at a point of codimension one is a discrete
valuation ring.**  A regular scheme is normal, and a locally Noetherian normal scheme has
discrete valuation rings for its local rings at codimension-one points. -/
@[sga "6 X 7.17.4" "O_{S_{i+1}"]
theorem isDiscreteValuationRing_stalk_of_isRegular {X : Scheme.{u}} [IsIntegral X]
    (hX : IsRegular X) {x : X} (hx : Order.coheight x = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  have : IsLocallyNoetherian X := (((isRegular_tfae X).out 1 2 rfl rfl).mp hX).1
  have : IsNormal X := isNormal_of_isRegular X hX
  exact isDiscreteValuationRing_stalk_of_coheight_eq_one hx

end AlgebraicGeometry

end
