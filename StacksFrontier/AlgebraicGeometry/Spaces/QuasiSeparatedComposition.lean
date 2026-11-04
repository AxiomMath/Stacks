module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFpqcLocalAtTarget

/-!
# Composition of quasi-separated morphisms of algebraic spaces (Stacks 03KQ)

Let `S` be a scheme contained in a big fppf site `B`. A morphism of algebraic spaces over `S` is
quasi-separated when its relative diagonal is quasi-compact (**Stacks 03HL**, part (3)), and the
quasi-separated case of **Stacks 03KQ** says that the condition is stable under composition. That
statement is `AlgebraicGeometry.Space.isQuasiSeparated_comp`; this file registers it at
`AlgebraicGeometry.Space.quasiSeparatedProperty`, the packaging of quasi-separatedness as a
property of morphisms of the category of algebraic spaces over `S`.

## Main results

* `AlgebraicGeometry.Space.quasiSeparatedProperty_isStableUnderComposition`: the
  quasi-separated case of **Stacks 03KQ** registered at
  `AlgebraicGeometry.Space.quasiSeparatedProperty`, which is the third instance argument
  that Stacks 045B asks of a property of morphisms of algebraic spaces.

## Implementation notes

The other two cases of Stacks 03KQ, the separated case and the locally separated case, are
`AlgebraicGeometry.Space.isSeparated_comp` and `AlgebraicGeometry.Space.isLocallySeparated_comp`.

## References

* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03KQ](https://stacks.math.columbia.edu/tag/03KQ)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Quasi-separatedness of morphisms of algebraic spaces over `S`, as the property
`AlgebraicGeometry.Space.quasiSeparatedProperty`, is stable under composition.

With it that property has all three instance arguments of **Stacks 045B**, the other two being
**Stacks 03KL** (stability under base change) and **Stacks 041N** read on the fppf precoverage. -/
instance quasiSeparatedProperty_isStableUnderComposition :
    (quasiSeparatedProperty B S hS).IsStableUnderComposition where
  comp_mem {X Y _Z} f g hf hg :=
    isQuasiSeparated_comp B S hS X.property Y.property f.hom g.hom hf hg

end AlgebraicGeometry.Space

end
