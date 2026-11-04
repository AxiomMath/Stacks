module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBaseChangeAffineIso

/-!
# Stacks 0E5I (1)

For a cartesian square of algebraic spaces with `Y`, `Y'` affine and `f` proper, flat and of
finite presentation, the base change map `L(g')^* a(K) ⟶ a'(Lg^*K)` of Stacks 0E5D is an
isomorphism for every `K ∈ D_QCoh(𝒪_Y)`. The statement is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBaseChangeAffineIso`; this file attaches
the tag to it.

## References

* [Stacks Project, Tag 0E5I](https://stacks.math.columbia.edu/tag/0E5I)
-/

@[expose] public section

add_to_stacks 0E5I "(1)"
  AlgebraicGeometry.Space.isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_isFlat

end
