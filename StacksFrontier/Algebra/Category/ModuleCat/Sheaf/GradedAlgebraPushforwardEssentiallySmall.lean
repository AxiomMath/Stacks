module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforwardEssentiallySmall.Specification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforwardEssentiallySmall.SectionMultiplication
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforwardEssentiallySmall.GradedAlgebra

/-!
# Pushforward of a graded algebra, with the universes of the two ringed topoi unrelated

The development is split into
`GradedAlgebraPushforwardEssentiallySmall.Specification` (the specification
`IsPushforwardGradedAlgebra`, the direct images of the structure maps, and the transposed
description of local sections), `GradedAlgebraPushforwardEssentiallySmall.SectionMultiplication`
(the multiplication of the direct image on local sections, and its bilinearity) and
`GradedAlgebraPushforwardEssentiallySmall.GradedAlgebra` (associativity, the unit laws, and the
direct-image graded algebra `pushforwardGradedAlgebra` with its specification).
-/
