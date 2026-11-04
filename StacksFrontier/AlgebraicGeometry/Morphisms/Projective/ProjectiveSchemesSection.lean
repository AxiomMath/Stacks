module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleFibreLimit.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.ProjectiveOverAmpleBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.ProjectiveSchemes

/-!
# Projective schemes

Over a base with an ample invertible sheaf the various notions of projective morphism agree and
are stable under base change, composition, fibre products, finite morphisms and finite disjoint
unions; and a proper morphism of finite presentation whose fibre over a point is projective is
projective over a neighbourhood of that point.

## References

* [Stacks Project, Tag 0B44](https://stacks.math.columbia.edu/tag/0B44)
-/

@[expose] public section

add_to_stacks 0B44 "the characterizations of projectivity over a base with an ample invertible
  sheaf" AlgebraicGeometry.isProjective_tfae_of_exists_isAmple
add_to_stacks 0B44 "base change" AlgebraicGeometry.ProjectiveSchemesOver.baseChange
add_to_stacks 0B44 "composition" AlgebraicGeometry.isProjective_comp_of_hasAmpleInvertibleSheaf
add_to_stacks 0B44 "fibre products" AlgebraicGeometry.isProjective_pullback_snd_comp
add_to_stacks 0B44 "finite morphisms"
  AlgebraicGeometry.isProjective_of_isFinite_of_hasAmpleInvertibleSheaf
add_to_stacks 0B44 "finite disjoint unions"
  AlgebraicGeometry.projectiveOver_isClosedUnderFiniteCoproducts
add_to_stacks 0B44 "projectivity spreads out from a fibre"
  Stacks.AmpleFibreLimit.exists_mem_isRelativelyAmple_of_isAmple_fibre
