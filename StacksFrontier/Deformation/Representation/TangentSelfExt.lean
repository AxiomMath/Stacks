module

public import StacksFrontier.Deformation.Representation.TangentSelfExt.ExtensionModules
public import StacksFrontier.Deformation.Representation.TangentSelfExt.AssociatedExtensions
public import StacksFrontier.Deformation.Representation.TangentSelfExt.TangentMap
public import StacksFrontier.Deformation.Representation.TangentSelfExt.Linearity

/-!
# The tangent space of a representation deformation category

This file collects the parts of the proof that the tangent space of the deformation category
of a finite-dimensional representation is canonically its first self-extension space over the
group algebra: `TangentSelfExt.ExtensionModules` (dual-number modules on self-extensions),
`TangentSelfExt.AssociatedExtensions` (self-extensions associated to deformations),
`TangentSelfExt.TangentMap` (the map `tangentSelfExt` and its bijectivity) and
`TangentSelfExt.Linearity` (its linearity and the equivalence of Stacks 0DVT).

## Main definitions

* `Deformation.IsAssociatedSelfExtension` records the short exact sequence obtained from a
  dual-number deformation by reduction and multiplication by `ε`.

## Main results

* `Deformation.tangentSpaceEquivSelfExt`: **Stacks 0DVT**. It identifies the tangent space,
  with its natural vector-space structure, linearly with self-extensions of the
  representation, and sends each deformation to the class of its associated short exact
  sequence.

## Implementation notes

The tangent space is Tag 06IB's value `Deformation.artinianTangentSpace` of the fibrewise
isomorphism-class functor at the canonical dual numbers. Its vector-space structure is the
natural one of Tag 06IH; the predeformation and Schlessinger conditions needed for that
structure are produced inside the construction, from the deformation-category property of
`Deformation.deformationCategoryProjection`. The representation is viewed as a module over
the group algebra using Mathlib's equivalence. An associated extension identifies its middle
term with the deformation as a group-algebra module, identifies its quotient map with special
fibre reduction, and identifies its inclusion after reduction with multiplication by `ε`.

## References

* [Stacks Project, Tag 0DVT](https://stacks.math.columbia.edu/tag/0DVT)
-/
