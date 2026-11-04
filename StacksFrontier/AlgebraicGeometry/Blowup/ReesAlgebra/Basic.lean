module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraSheaf

/-!
# The Rees algebra of an ideal sheaf, as opaque data

The Rees algebra `⊕_{n ≥ 0} Iⁿ` of a quasi-coherent ideal sheaf is constructed in
`StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraSheaf`.  This module exposes it as data chosen
from an existence statement rather than as that construction: the relative `Proj` situation of
the blowup, and the vanishing results resting on it, are stated for an arbitrary graded sheaf
with the affine-local description of `⊕ₙ Iⁿ`, and their proofs rely on the chosen datum being
opaque.

## Main definitions

* `AlgebraicGeometry.ReesAlgebraData` is `Stacks.Blowup.ReesAlgebraData`.
* `AlgebraicGeometry.reesAlgebraData` is such a datum, chosen from
  `Stacks.Blowup.exists_reesAlgebraData`, hence not reducible to the construction.

## Implementation notes

`AlgebraicGeometry.reesAlgebraData` and `Stacks.Blowup.reesAlgebraData`
(`StacksFrontier/AlgebraicGeometry/Blowup/ReesAlgebraSheaf.lean:965`) are two terms of one type —
the `ReesAlgebraData` above is an `abbrev` for `Stacks.Blowup.ReesAlgebraData`. They are not a
duplicate to collapse, and the opacity recorded above is the reason: replacing the body of
`AlgebraicGeometry.reesAlgebraData` by `Stacks.Blowup.reesAlgebraData I` and building the
library fails in three modules, each because the construction is now unfolded during
definitional unification:

  StacksFrontier/AlgebraicGeometry/Blowup/Transform/FittingKernel.lean:117
    (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000)
  StacksFrontier/AlgebraicGeometry/RelativeProjSituation/QuasiCompact.lean:226
    (deterministic) timeout at `whnf`, maximum number of heartbeats (200000)
  StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/Vanishing/RegularLocalBlowup.lean:212
    (kernel) deterministic timeout
  StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/Vanishing/RegularLocalBlowup.lean:383
    (kernel) unknown constant '_private.StacksDraft.AlgebraicGeometry...'

The last of those is the sharpest: transparency carries a `private` constant of the
construction across a module boundary and into the kernel. Raising the heartbeat limit is not
an option here — `set_option` is not permitted in this library — so identifying the two terms
means rewriting those three consumers so that they never need the datum to reduce. That is the
Tag 01OG fork; the same fork is what keeps `AlgebraicGeometry.blowUpToBase` and
`Stacks.Blowup.blowUpToBase` distinct, as recorded at
`StacksFrontier/AlgebraicGeometry/Blowup/ExceptionalDifferentials.lean`.
-/

@[expose] public section

namespace AlgebraicGeometry

universe u

/-- A graded algebra over the structure sheaf whose degree-`n` piece is affine-locally `Iⁿ`. -/
public abbrev ReesAlgebraData {X : Scheme.{u}} (I : X.IdealSheafData) :=
  Stacks.Blowup.ReesAlgebraData I

/-- The Rees algebra sheaf `⊕ₙ Iⁿ` with its affine-local characterization, chosen from
`Stacks.Blowup.exists_reesAlgebraData`; the choice keeps it opaque, which its consumers need. -/
public noncomputable def reesAlgebraData {X : Scheme.{u}} (I : X.IdealSheafData) :
    ReesAlgebraData I := Classical.choice (Stacks.Blowup.exists_reesAlgebraData I)

end AlgebraicGeometry

end
