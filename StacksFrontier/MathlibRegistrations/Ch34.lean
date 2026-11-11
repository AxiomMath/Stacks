module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.CategoryTheory.Sites.Coverage
import StacksCore.Tactic.StacksAttribute

/-!
# Mathlib registrations for the chapter on topologies

Zariski, étale and fppf coverings of a scheme, and their stability under isomorphisms,
composition and base change, are already in Mathlib; this file attaches the Stacks tags to the
Mathlib declarations.
-/

add_to_stacks 020O AlgebraicGeometry.Scheme.zariskiPrecoverage
add_to_stacks 020O AlgebraicGeometry.Scheme.OpenCover
add_to_stacks 020P AlgebraicGeometry.Scheme.zariskiPretopology
add_to_stacks 0215 AlgebraicGeometry.Scheme.etalePrecoverage
add_to_stacks 0217 AlgebraicGeometry.Scheme.etalePretopology
add_to_stacks 021M AlgebraicGeometry.Scheme.fppfPrecoverage
add_to_stacks 021O "(1) isomorphisms" AlgebraicGeometry.Scheme.Hom.singleton_mem_fppfPrecoverage
add_to_stacks 021O "(2) composition"
  AlgebraicGeometry.Scheme.instIsStableUnderCompositionFppfPrecoverage
add_to_stacks 021O "(3) base change"
  AlgebraicGeometry.Scheme.instIsStableUnderBaseChangeFppfPrecoverage

/-! ### fpqc coverings (Tag 022B)

Mathlib's own `@[stacks 022B]` sits on `AlgebraicGeometry.QuasiCompactCover`, which is only the
quasi-compactness condition of the definition (every affine open of the target is a finite union
of images of quasi-compact opens), with no flatness; an upstream attribute cannot be relabelled
from here.  The fpqc coverings themselves are the families in
`AlgebraicGeometry.Scheme.fpqcPrecoverage`: flat, jointly surjective and quasi-compact.
`AlgebraicGeometry.ofArrows_mem_fpqcPrecoverage_iff` identifies membership with the source's
condition (flat, and every affine open a finite union of images of affine opens), and carries
the tag as well. -/

add_to_stacks 022B "fpqc coverings: the families that are flat, jointly surjective and \
  quasi-compact (QuasiCompactCover, which carries Mathlib's own 022B attribution, is the \
  quasi-compactness condition alone)"
  AlgebraicGeometry.Scheme.fpqcPrecoverage

/-! ### Further tags of this chapter covered by Mathlib

Where a Mathlib declaration is more general than the tag, the note says how the tag is the
special case.

Not recorded here:
* Tag 0220: Mathlib has no notion of a smooth covering, and no declaration states that étale or
  Zariski coverings are smooth coverings.
* Tag 0221: part (1), that an isomorphism is a smooth covering, has no Mathlib declaration (there is
  no `ContainsIdentities` instance for smooth morphisms); parts (2) and (3) are instances of the
  generic stability of `Scheme.precoverage`. -/

add_to_stacks 022G "(1) the sheaf property for a family: more general, for any presieve, here \
  Presieve.ofArrows of the family"
  CategoryTheory.Presieve.IsSheafFor
add_to_stacks 022G "(1) the same, in the form of the tex: elements agreeing on the U_i ×_T U_j \
  glue uniquely"
  CategoryTheory.Presieve.isSheafFor_arrows_iff_pullbacks
add_to_stacks 022G "(2) the fpqc topology on schemes"
  AlgebraicGeometry.Scheme.fpqcTopology
add_to_stacks 022G "(2) the sheaf property for a topology: more general, here the fpqc topology"
  CategoryTheory.Presieve.IsSheaf
add_to_stacks 022G "(2) the same as the sheaf property for every fpqc covering: more general, for \
  any precoverage stable under base change, here the fpqc precoverage"
  CategoryTheory.Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange
