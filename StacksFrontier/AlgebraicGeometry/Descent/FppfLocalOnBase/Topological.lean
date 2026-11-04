module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.Submersive
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Descent.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.QuasiCompactLocal

/-!
# The topological entries of the list of Tag 02WH

Tag 02WH lists the properties of morphisms of schemes which, being stable under base change,
are moreover *fpqc local on the base*, hence a fortiori *fppf local on the base*. This file
records the entries of that list whose content is topological: being universally closed, being
separated, being quasi-separated, being universally open, being universally submersive, being
a universal homeomorphism, and being proper.

## Main results

* `Stacks.Descent.universallyClosed_isLocalAtTarget_fppf`: being universally closed is fppf
  local on the base.
* `Stacks.Descent.isSeparated_isLocalAtTarget_fppf` and
  `Stacks.Descent.quasiSeparated_isLocalAtTarget_fppf`: being separated, respectively
  quasi-separated, is fppf local on the base.
* `Stacks.Descent.universallyOpen_isLocalAtTarget_fppf`: being universally open is fppf local
  on the base.
* `Stacks.Descent.universallyQuotientMap_isLocalAtTarget_fppf`: being universally submersive is
  fppf local on the base.
* `Stacks.Descent.universalHomeomorphism_isLocalAtTarget_fppf`: being a universal
  homeomorphism is fppf local on the base.
* `Stacks.Descent.isProper_isLocalAtTarget_fppf`: being proper is fppf local on the base.

## Implementation notes

Each entry of the list of Tag 02WH is stated, and carries the tag, as a single conjunction in
`StacksFrontier/AlgebraicGeometry/Descent/FppfLocalOnBase/Entries.lean`: the property is stable
under arbitrary base change, it is local on the base for the fpqc precoverage, **and** it is
local on the base for the fppf precoverage. This file supplies the "a fortiori" half of the
remark, that the property is local on the base for the fppf precoverage, obtained from the fpqc
half by `Stacks.Descent.isLocalAtTarget_fppfPrecoverage`. These instances deliberately do not
carry the tag themselves: one record per entry is what makes the tag's coverage readable, and
the conjunction that does carry it asserts this fppf locality itself, so none of the remark's
content rests on an untagged declaration.

Being universally submersive is `(topologically Topology.IsQuotientMap).universally`, and being
a universal homeomorphism is likewise a universal closure, so both inherit stability under base
change from `CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange`. That one
declaration is therefore the base change half of both entries, and each entry's conjunction in
`Entries.lean` names it.

The remaining entries of the list whose content is topological have their fppf locality recorded
elsewhere, beside the fpqc halves they come from. Quasi-compactness is
`Stacks.Descent.quasiCompact_isLocalAtTarget_fppf` in
`StacksFrontier/AlgebraicGeometry/Topologies/Fppf/QuasiCompactLocal.lean`, which carries the tag for
that entry already. Being a monomorphism, being surjective and being universally injective are
`AlgebraicGeometry.instIsLocalAtTargetFppfMonomorphisms`,
`AlgebraicGeometry.surjective_isLocalAtTarget_fppf` and
`AlgebraicGeometry.universallyInjective_isLocalAtTarget_fppf` in
`StacksFrontier/AlgebraicGeometry/Spaces/Representable/FpqcLocal.lean`.

## References

* [Stacks Project, Tag 02WH](https://stacks.math.columbia.edu/tag/02WH)
-/

@[expose] public section

open CategoryTheory MorphismProperty AlgebraicGeometry

universe u

namespace Stacks.Descent

/-! ### Universally closed morphisms -/

/-- **Stacks 02WH**, entry (3). Being universally closed is fppf local on the base. -/
public instance universallyClosed_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@UniversallyClosed : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Separated and quasi-separated morphisms -/

/-- **Stacks 02WH**, entry (4), separated case. Being separated is fppf local on the base. -/
public instance isSeparated_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@IsSeparated : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-- **Stacks 02WH**, entry (4), quasi-separated case. Being quasi-separated is fppf local on
the base. -/
public instance quasiSeparated_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@QuasiSeparated : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Universally open morphisms -/

/-- **Stacks 02WH**, entry (14). Being universally open is fppf local on the base. -/
@[sga "4 IV 8.5.5" "fppf target coverings"]
public instance universallyOpen_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@UniversallyOpen : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Universally submersive morphisms -/

/-- **Stacks 02WH**, entry (23) of the list: **universally submersive**, Descent, Lemma 0CEW.
A submersive morphism is one whose underlying map of spaces is a quotient map, so the source's
"universally submersive" is `(topologically Topology.IsQuotientMap).universally` in Lean; the
name `universallyQuotientMap` denotes exactly that notion. Being universally submersive is fppf
local on the base. -/
@[ega "IV 15.7.11.1" "partial"]
public instance universallyQuotientMap_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget
      ((topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally)
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Universal homeomorphisms -/

/-- **Stacks 02WH**, entry (24) of the list: **universal homeomorphism**, Descent, Lemma 0CEX.
The source's "universal homeomorphism" is `AlgebraicGeometry.UniversalHomeomorphism` in Lean.
Being a universal homeomorphism is fppf local on the base. -/
@[sga "1 VIII 4.6" "special case", sga "4 IV 8.5.5" "fppf target coverings"]
public instance universalHomeomorphism_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@UniversalHomeomorphism : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

/-! ### Proper morphisms -/

/-- **Stacks 02WH**, entry (20) of the list: **proper**, Descent, Lemma 02L1. The source's
"proper" is `AlgebraicGeometry.IsProper` in Lean. Being proper is fppf local on the base. -/
@[sga "4 IV 8.5.5" "properness, special case"]
public instance isProper_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@IsProper : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

end Stacks.Descent

end
