module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.MorphismProperty.Limits
import StacksCore.Tactic.StacksAttribute

/-!
# Mathlib registrations: More on morphisms (Stacks Chapter 37)

Stacks tags from the chapter *More on morphisms* whose statements Mathlib already proves,
recorded on the Mathlib declarations with `add_to_stacks`.

## References

* [Stacks Project, Chapter 37](https://stacks.math.columbia.edu/tag/02GX)
-/

-- Flat diagonals and weakly étale morphisms are stable under composition.
add_to_stacks 02H8 "Mathlib's definition: the ring maps on affine opens are formally unramified"
  AlgebraicGeometry.FormallyUnramified
add_to_stacks 02H8 "a formally unramified morphism has at most one dotted arrow, for any \
  nilpotent closed immersion (in particular a first order thickening)"
  AlgebraicGeometry.FormallyUnramified.hom_ext
add_to_stacks 02H8 "conversely, at most one dotted arrow for first order thickenings of affine \
  schemes implies formally unramified" AlgebraicGeometry.FormallyUnramified.of_hom_ext
add_to_stacks 02HA AlgebraicGeometry.FormallyUnramified.instIsStableUnderCompositionScheme
add_to_stacks 02HB AlgebraicGeometry.FormallyUnramified.instIsStableUnderBaseChangeScheme
add_to_stacks 02HC "formally unramified is the affine-local property of formally unramified \
  ring maps, hence local on the source and on the target"
  AlgebraicGeometry.FormallyUnramified.instHasRingHomPropertyFormallyUnramified
add_to_stacks 02HC "a property local on the source and the target is preserved by restriction \
  f|_U : U → V" AlgebraicGeometry.IsZariskiLocalAtSource.resLE
add_to_stacks 02HD "formally unramified is the affine-local property of formally unramified \
  ring maps" AlgebraicGeometry.FormallyUnramified.instHasRingHomPropertyFormallyUnramified
add_to_stacks 02HD "for X and S affine, such a property holds iff it holds for the ring map on \
  global sections" AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine

add_to_stacks 094T
  "(1), for `P = @AlgebraicGeometry.Flat` on schemes: flat diagonals compose"
  CategoryTheory.MorphismProperty.diagonal_isStableUnderComposition
add_to_stacks 094T "(2)" AlgebraicGeometry.WeaklyEtale.instCompScheme

-- Flat diagonals and weakly étale morphisms are stable under base change.
add_to_stacks 094U
  "(1), for `P = @AlgebraicGeometry.Flat` on schemes: flat diagonals base change"
  CategoryTheory.MorphismProperty.IsStableUnderBaseChange.diagonal
add_to_stacks 094U "(2)" AlgebraicGeometry.WeaklyEtale.instIsStableUnderBaseChangeScheme

add_to_stacks 0EJY "U is quasi-affine (stated for affine f; integral morphisms are affine)"
  AlgebraicGeometry.Scheme.IsQuasiAffine.of_isAffineHom
add_to_stacks 0EJY "the square U → Spec Γ(U), X → Spec Γ(X) is cartesian (stated for affine f)"
  AlgebraicGeometry.Scheme.isPullback_toSpecΓ_toSpecΓ

-- The affine schemes are the essential image of `Spec`.
add_to_stacks 0H2Q "a retraction of the unit X → Spec Γ(X, 𝒪_X) puts X in Spec's essential image"
  CategoryTheory.mem_essImage_of_unit_isSplitMono
add_to_stacks 0H2Q "Spec is reflective with unit X.toSpecΓ" AlgebraicGeometry.Spec.reflective
add_to_stacks 0H2Q "the unit is X.toSpecΓ" AlgebraicGeometry.ΓSpec.adjunction_unit_app
add_to_stacks 0H2Q "the essential image of Spec is the affine schemes"
  AlgebraicGeometry.essImage_Spec

-- Stacks 02LJ: the basic diagram `V → X_U → X` over `φ : U → S`, whose right square is the
-- base change `X_U = U ×_S X`.
add_to_stacks 02LJ "the cartesian square X_U = U ×_S X of the basic diagram"
  CategoryTheory.IsPullback.of_hasPullback

