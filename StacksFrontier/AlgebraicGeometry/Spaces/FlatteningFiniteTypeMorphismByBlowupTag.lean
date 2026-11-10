module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFiniteTypeMorphismByBlowup

/-!
# Stacks 087E: flattening a morphism of finite type by blowing up

Let `S` be a scheme, let `f : X ⟶ B` be a morphism of algebraic spaces over `S` and let
`U ⊆ B` be an open subspace. Assume that `B` is quasi-compact and quasi-separated, that `U` is
quasi-compact, that `f` is of finite type and quasi-separated, and that `f⁻¹(U) ⟶ U` is flat and
locally of finite presentation. Then there is a `U`-admissible blowup `B' ⟶ B` such that the
strict transform `X'` of `X` is flat and of finite presentation over `B'`.

The statement is proved under the source's hypotheses alone in
`StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFiniteTypeMorphismByBlowup`, along the source's
proof; this file attaches the tag to it. It uses flattening by blowing up (Stacks 087C), the étale
localization of strict transforms (Stacks 0863), the embedding into an algebraic space of finite
presentation (in the form of Stacks 0871, which suffices for an affine chart) and the strict
transform of a pushforward along an affine morphism (Stacks 0866).

In that statement the base is written `A`, since `B` names the big fppf site. A `U`-admissible
blowup (Stacks 086B) is the blowup in a finitely presented closed subspace `Z` whose points avoid
those of `U`. The conclusion names `Z`, because the strict transform depends on the centre and not
only on the morphism `B' ⟶ B`, as the remark after Stacks 0862 says. Quasi-separatedness of `B` is
absolute quasi-separatedness. The hypothesis `hZ : B.Contains (⊤_ Scheme)` only states that the
ambient big site contains `Spec ℤ`, which `BigFppfSite.contains_terminal` always provides.

## References

* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
-/

@[expose] public section

open AlgebraicGeometry.Space in
add_to_stacks 087E
  exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransformSpaceToBlowUp_of_isFiniteType

end
