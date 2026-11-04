module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NormalMorphism.SmoothLocalSource

/-!
# Normality is local in the smooth topology

A scheme is normal if and only if the members of a jointly surjective family of smooth
morphisms onto it are normal.  Ascent is normality of a smooth algebra over a normal ring, and
descent is normality along a faithfully flat ring map.

That statement, `AlgebraicGeometry.isNormal_isLocal_smooth`, is proved in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.NormalMorphism.SmoothLocalSource`, where it is the
step that makes normality of a morphism local on the source; this module re-exports it.

## References

* [Stacks Project, Tag 034F](https://stacks.math.columbia.edu/tag/034F)
-/
