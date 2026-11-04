module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationModuleDescentHypercovering
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentDerivedDescentEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentDerivedUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleBigFppfRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleBigFppfSquare
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent descent along fppf hypercoverings of algebraic spaces, as Stacks tags

The comparison squares with the big fppf site (Stacks 0DH5, 0DHC) and the descent of modules and
of `D_QCoh` along fppf hypercoverings (Stacks 0D9Z, 0DHD, 0DHE, 0DHF) of simplicial algebraic
spaces are proved in the modules of `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite`; this file
records the tags.

## References

* [Stacks Project, Tag 0D9Z](https://stacks.math.columbia.edu/tag/0D9Z)
* [Stacks Project, Tag 0DH5](https://stacks.math.columbia.edu/tag/0DH5)
* [Stacks Project, Tag 0DHC](https://stacks.math.columbia.edu/tag/0DHC)
* [Stacks Project, Tag 0DHD](https://stacks.math.columbia.edu/tag/0DHD)
* [Stacks Project, Tag 0DHE](https://stacks.math.columbia.edu/tag/0DHE)
* [Stacks Project, Tag 0DHF](https://stacks.math.columbia.edu/tag/0DHF)
-/

@[expose] public section

add_to_stacks 0DHF
  AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.isWeakSerreClass_and_derivedPullback_equivalence

add_to_stacks 0DHE
  AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.isIso_unit_and_isZero_rightDerived_of_isHypercoveringAugmentation

add_to_stacks 0DHD
  AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.descent_quasicoherent_of_isHypercoveringAugmentation

add_to_stacks 0DHC AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.bigFppfAugmentationSquareTwoIso

add_to_stacks 0DH5 AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.bigFppfAugmentationSquareIso

end
