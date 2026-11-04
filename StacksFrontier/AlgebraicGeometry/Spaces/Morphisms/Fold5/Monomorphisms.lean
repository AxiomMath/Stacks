module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono

/-!
# Monomorphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is a *monomorphism* when it is an
injective map of sheaves on the big fppf site of `S`, that is, a monomorphism of the
category of those sheaves. Since a morphism of algebraic spaces is a natural
transformation of presheaves, this is Mathlib's `CategoryTheory.Mono`, and the two
soriteses of the source — stability under composition and under base change — are its
general categorical counterparts. The one assertion that is specific to algebraic spaces is
that a monomorphism is injective on points.

## Main results

* `AlgebraicGeometry.Space.pointsMap_injective_of_mono`: a monomorphism of algebraic spaces
  induces an injective map on their sets of points. Proved in
  `StacksFrontier.AlgebraicGeometry.Spaces.PointsMono`, which this module re-exports.

## Implementation notes

Taking `CategoryTheory.Mono` as the definition rather than introducing a predicate makes
both formulations of the source available at once: `Mono f` for a natural transformation
`f` is equivalent to injectivity of each of its components, by
`CategoryTheory.NatTrans.mono_iff_mono_app`. Downstream statements use `[Mono f]`.

Tag 06RV was formalized twice, once here and once in
`StacksFrontier.AlgebraicGeometry.Spaces.PointsMono`, under the same fully-qualified name
`AlgebraicGeometry.Space.pointsMap_injective_of_mono` and with a type equal to the byte, so
in any environment holding both modules the two were one constant: one of the two proofs was
silently discarded on import and the key had two registration sites. The copy here has been
removed in favour of `PointsMono`, which is the module the import order already selected, the
only one any consumer of the name reaches, and the one with the fifty-module reverse cone
while this module had none. The import above keeps the result available to anyone who reaches
for it here, and costs nothing: the closure of `PointsMono` was already contained in this
module's own. What remains here is the registration of the three categorical keys 042L, 042O
and 042P against their Mathlib counterparts, which `PointsMono` does not carry; no key lost a
site. Nothing stopped being proved — the statement is unchanged and is settled by a bare
application of the `PointsMono` theorem in either direction.

Injectivity on points is proved there for an arbitrary morphism of presheaves on the big
fppf site. Only the monomorphism hypothesis is used, so the algebraic-space axioms would be
dead weight.

## References

* [Stacks Project, Tag 042L](https://stacks.math.columbia.edu/tag/042L)
* [Stacks Project, Tag 042O](https://stacks.math.columbia.edu/tag/042O)
* [Stacks Project, Tag 042P](https://stacks.math.columbia.edu/tag/042P)
* [Stacks Project, Tag 06RV](https://stacks.math.columbia.edu/tag/06RV)
-/

@[expose] public section

open CategoryTheory

add_to_stacks 042L CategoryTheory.Mono
add_to_stacks 042O CategoryTheory.mono_comp
add_to_stacks 042P CategoryTheory.MorphismProperty.IsStableUnderBaseChange.monomorphisms
add_to_sga "3 IV 4.5.7" "more general"
  CategoryTheory.MorphismProperty.IsStableUnderBaseChange.monomorphisms
add_to_sga "3 VIB 10.1" "monomorphisms"
  CategoryTheory.MorphismProperty.IsStableUnderBaseChange.monomorphisms
add_to_ega "I 3.3.12" "more general"
  CategoryTheory.MorphismProperty.IsStableUnderBaseChange.monomorphisms
add_to_ega "IV 2.7.1" "(ix)" CategoryTheory.MorphismProperty.IsStableUnderBaseChange.monomorphisms

end
