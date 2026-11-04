module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforward.TransportedAddition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforward.Specification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforward.BilinearMultiplication
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforward.Construction

/-!
# Pushforward of a graded algebra

A morphism of ringed topoi sends a graded algebra to a graded algebra on the target. The
development is split into `TransportedAddition` (the addition of a sheaf of modules transported
along a functor), `Specification` (the direct-image specification `IsPushforwardGradedAlgebra`,
the canonical maps it is built from, and local sections of a direct image as morphisms out of a
sheafified Yoneda object), `BilinearMultiplication` (the multiplication on local sections, as a
bilinear map) and `Construction` (the direct image `pushforwardGradedAlgebra` and its
specification, Stacks 0FQX).
-/
