module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChangePerfect
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0AA8 part (2): affine base change of the twisted inverse image for perfect morphisms

`Stacks.Duality.isIso_twistedInverseImageBaseChangeMap_app_of_perfect` states part (2) of
[Stacks, Tag 0AA8]: for `g : Y' ⟶ Y` a morphism of affine schemes, `f` proper and perfect, `Y`
Noetherian and `f`, `g` Tor independent, `L(g')^* a(K) ⟶ a'(Lg^*K)` is invertible for every
`K ∈ D_QCoh(𝒪_Y)`.
-/

@[expose] public section

add_to_stacks 0AA8 "(2)" Stacks.Duality.isIso_twistedInverseImageBaseChangeMap_app_of_perfect
