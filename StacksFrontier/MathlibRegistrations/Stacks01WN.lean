module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute

/-! Mathlib already states Stacks tag 01WN as
    `AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom`: a morphism of schemes is finite
    if and only if it is affine and proper. -/

@[expose] public section

add_to_stacks 01WN AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom
add_to_sga "6 XII 1.6" "special case" AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom
add_to_ega "II 7.3.12" "more general" AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom
add_to_ega "III 4.4.2" "more general" AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom
add_to_ega "IV 7.9.1" "more general" AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom
