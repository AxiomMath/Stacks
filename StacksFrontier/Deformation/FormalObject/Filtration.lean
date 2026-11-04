module

public import StacksFrontier.Deformation.FormalObject.Filtration.FilteredObject
public import StacksFrontier.Deformation.FormalObject.Filtration.ComparisonFunctors
public import StacksFrontier.Deformation.FormalObject.Filtration.Equivalence

/-!
# Formal objects for a different filtration

Formal objects computed with respect to a different filtration of the underlying complete local
algebra agree with the original ones (Stacks Project, Tag 06H6).  The development is split into
`Filtration.FilteredObject` (ideal filtrations, filtered formal objects, composite transition
maps and index comparisons), `Filtration.ComparisonFunctors` (the functors between filtered
formal objects and the fibre of formal objects over `R`) and `Filtration.Equivalence` (the
round-trip isomorphisms and `filteredFormalObjectsEquivalence`).
-/
