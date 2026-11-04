module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Diagram

/-!
# The degree `d` finite Hilbert stack and its two abbreviations

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
and let `d` be a natural number. The construction of Stacks 05WA attaches to this datum a
category over the site whose objects are the quintuples `(U, Z, y, x, α)` with `Z ⟶ U` finite
locally free of degree `d`, and Stacks 05WC gives that category its name: the *degree `d` finite
Hilbert stack of `𝒳` over `𝒴*`, written `ℋ_d(𝒳/𝒴)`. The same definition fixes two
abbreviations, for the two specialisations of the construction in which the stack `𝒴`, or both
`𝒳` and `𝒴`, is the base `S`: `ℋ_d(𝒳)` for the first and `ℋ_d` for the second.

All three categories are already constructed in this directory, the relative one in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Basic` and the two abbreviations in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Diagram`, so this file only registers the
tag of the definition against them.

## Main definitions

The three names of Stacks 05WC are registered on the declarations that already carry the
constructions:

* `ℋ_d(𝒳/𝒴)` is `AlgebraicGeometry.Stack.finiteHilbertCategory`;
* `ℋ_d(𝒳)` is `AlgebraicGeometry.Stack.absoluteHilbertCategory`;
* `ℋ_d` is `AlgebraicGeometry.Stack.finiteCoverCategory`.

## Main results

None: Stacks 05WC is a definition, and the three objects it names are defined elsewhere in this
directory. That `ℋ_d(𝒳/𝒴)` is fibred in groupoids over the site is
`AlgebraicGeometry.Stack.isFiberedInGroupoids_finiteHilbertProjection`, the first of the three
conditions of Stacks 05WB.

## Implementation notes

The three registrations are made with `add_to_stacks` rather than by introducing new
definitions, because each of the three objects of Stacks 05WC is an existing declaration of this
library: re-defining any of them would produce a second constant denoting the same category and
would detach the tag from the declarations that the rest of the directory — the diagram of
Stacks 05WD, the faithfulness statement of Stacks 05XV and the functoriality of Stacks 05XN —
is stated about.

The two abbreviations are not literal instances of `ℋ_d(𝒳/𝒴)`. Setting `𝒴 = S` in the
construction leaves the object `y` over `U` and the identification `α` determined up to unique
isomorphism, and setting `𝒳 = 𝒴 = S` leaves only the cover; so `ℋ_d(𝒳)` and `ℋ_d` are built
directly from the data that survives the specialisation, which is what makes the four forgetful
1-morphisms of Stacks 05WD definable without a choice of a category over the site representing
`S`. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Diagram`.

## References

* [Stacks Project, Tag 05WB](https://stacks.math.columbia.edu/tag/05WB)
* [Stacks Project, Tag 05WC](https://stacks.math.columbia.edu/tag/05WC)
-/

@[expose] public section

add_to_stacks 05WC "the stack ℋ_d(𝒳/𝒴)" AlgebraicGeometry.Stack.finiteHilbertCategory

add_to_stacks 05WC "ℋ_d(𝒳), the case 𝒴 = S" AlgebraicGeometry.Stack.absoluteHilbertCategory

add_to_stacks 05WC "ℋ_d, the case 𝒳 = 𝒴 = S" AlgebraicGeometry.Stack.finiteCoverCategory

end
