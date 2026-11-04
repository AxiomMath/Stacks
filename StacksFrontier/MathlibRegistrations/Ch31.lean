module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# Mathlib declarations carrying Stacks tags of Chapter 31 (Divisors)

Records Stacks tags of Chapter 31 that Mathlib already covers, on the Mathlib declarations
stating them.

* Tag 02RJ (the order of vanishing `ord_Z(f) = ord_{𝒪_{X,ξ}}(f)` of a rational function along a
  prime divisor `Z` with generic point `ξ`, on a locally Noetherian integral scheme) is
  `AlgebraicGeometry.Scheme.ord`. Mathlib indexes it by the point `ξ` rather than by `Z`, and
  takes `f` in the whole function field, with the junk value `0` at `f = 0` and at points that
  are not of codimension `1`. At a point `ξ` with `coheight ξ = 1`,
  `AlgebraicGeometry.Scheme.ord_eq_ordHom_of_coheight_eq_one` identifies the value with
  `Ring.ordFrac` (Stacks 02MD) of the stalk `𝒪_{X,ξ}`. The passage between prime divisors and
  their generic points is the order isomorphism `irreducibleSetEquivPoints` between irreducible
  closed subsets and points (with the specialization order), under which the codimension of `Z`
  is the coheight of `ξ`.

## References

* [Stacks Project, Tag 02RJ](https://stacks.math.columbia.edu/tag/02RJ)
-/

@[expose] public section

add_to_stacks 02RJ "the definition, indexed by the generic point ξ of Z (coheight ξ = 1)"
  AlgebraicGeometry.Scheme.ord
add_to_stacks 02RJ "at a codimension-one point the value is ord of the stalk (Tag 02MD)"
  AlgebraicGeometry.Scheme.ord_eq_ordHom_of_coheight_eq_one
add_to_stacks 02RJ "prime divisors Z correspond to their generic points ξ, codim Z = coheight ξ"
  irreducibleSetEquivPoints

end
