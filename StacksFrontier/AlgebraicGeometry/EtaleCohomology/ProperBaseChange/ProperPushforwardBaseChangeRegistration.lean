module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0A4B: cohomology commutes with base change iff higher direct images vanish on injectives

For a proper morphism `f`, cohomology commutes with base change for `f` exactly when, for every
prime `ℓ`, every injective sheaf of `ℤ/ℓℤ`-modules and every cartesian square, the higher direct
images of the pulled-back injective vanish. The statement is
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_iff_higherDirectImagesVanishOnInjectives`.
-/

add_to_stacks 0A4B "(1) cohomology commutes with base change for f iff (2) higher direct images \
of pulled-back injective Z/lZ-sheaves vanish"
  Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_iff_higherDirectImagesVanishOnInjectives
