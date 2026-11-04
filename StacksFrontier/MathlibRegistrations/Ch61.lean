module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags of chapter 61 (The Pro-étale Site) covered by Mathlib

Each tag registered here is stated in Mathlib; this file only records the correspondence.
-/

add_to_stacks 0989 AlgebraicGeometry.Scheme.proetalePrecoverage
add_to_stacks 098B "étale coverings"
  AlgebraicGeometry.Scheme.etalePrecoverage_le_proetalePrecoverage
add_to_stacks 098B "Zariski coverings (the case P = weakly étale)"
  AlgebraicGeometry.Scheme.zariskiPrecoverage_le_propQCPrecoverage
add_to_stacks 098C "(1)" AlgebraicGeometry.Scheme.instHasIsosProetalePrecoverage
add_to_stacks 098C "(2)" AlgebraicGeometry.Scheme.instIsStableUnderCompositionProetalePrecoverage
add_to_stacks 098C "(3)" AlgebraicGeometry.Scheme.instIsStableUnderBaseChangeProetalePrecoverage
add_to_stacks 098D "finite affine refinement by open immersions into the members"
  AlgebraicGeometry.QuasiCompactCover.exists_hom
add_to_stacks 098D "the refinement is quasi-compact, hence a pro-étale covering"
  AlgebraicGeometry.QuasiCompactCover.instCoverOfIsAffineOfFiniteI₀
