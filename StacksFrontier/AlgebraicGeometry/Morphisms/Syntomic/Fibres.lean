module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.FiberCriterion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Syntomic morphisms are detected on the fibres

A flat morphism of schemes locally of finite presentation is syntomic as soon as each of its
fibres is a local complete intersection over the residue field of its base point. The result is
`AlgebraicGeometry.syntomic_of_lci_fibers` (Stacks 01UF); this file keeps the older name as an
alias.

## Main results

* `AlgebraicGeometry.syntomic_of_isLocalCompleteIntersection_fiber`: alias of
  `AlgebraicGeometry.syntomic_of_lci_fibers`.

## References

* [Stacks Project, Tag 01UF](https://stacks.math.columbia.edu/tag/01UF)
-/

@[expose] public section

namespace AlgebraicGeometry

@[inherit_doc syntomic_of_lci_fibers, ega "IV 19.3.6" "partial"]
alias syntomic_of_isLocalCompleteIntersection_fiber := syntomic_of_lci_fibers

end AlgebraicGeometry

end
