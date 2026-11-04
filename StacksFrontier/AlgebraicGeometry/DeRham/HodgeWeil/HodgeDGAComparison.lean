module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.HodgeDGAComparison.Equiv
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.HodgeDGAComparison.Multiplicative
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.HodgeDGAComparison.Pullback

/-!
# The cohomology of the Hodge complex is Hodge cohomology

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space and let
`ℋ = ⨁_p Ω^p[-p]` be the Hodge complex, with zero differential and wedge multiplication. Since the
differential vanishes, `ℋ` splits, degree by degree, into the complexes `Ω^p[-p]`, and `Ω^p[-p]`
is the shift by `-p` of `Ω^p[0]`. In a fixed degree `n` only the summands with `p ≤ n`
contribute to `H^n(X, ℋ)`, the others living in degrees `> n`, so

`H^n(X, ℋ) = ⨁_{p + q = n} H^n(X, Ω^p[-p]) = ⨁_{p + q = n} H^q(X, Ω^p) = H^n_{Hodge}(X/S)`.

This identification is multiplicative and unital, for the cup product of Section 0FKU followed by
the multiplication of `ℋ` on the left and the cup product of Hodge cohomology on the right, and,
for a commutative square of schemes, it is compatible with pullback.

## Main definitions

* `Stacks.HodgeWeil.hodgeSummand`: the complex `Ω^p[-p]`.
* `Stacks.HodgeWeil.hodgeSummandι`, `Stacks.HodgeWeil.hodgeSummandπ`: its inclusion into `ℋ` and
  the projection of `ℋ` onto it.
* `Stacks.HodgeWeil.hodgeSummandCohomologyIso`: `H^n(X, Ω^p[-p]) ≅ H^q(X, Ω^p)` for `p + q = n`.
* `Stacks.HodgeWeil.hodgeDgaEquiv`: **the identification `H^n(X, ℋ) ≅ H^n_{Hodge}(X/S)`**.
* `Stacks.HodgeWeil.hodgeSummandWedge`: the wedge product
  `Tot(Ω^p[-p] ⊗_A Ω^q[-q]) ⟶ Ω^{p + q}[-(p + q)]`.

## Main results

* `Stacks.HodgeWeil.hodgeDgaEquiv_symm_of`: the inverse of `hodgeDgaEquiv` on a class of pure
  bidegree `(p, q)` is its image under the inclusion `Ω^p[-p] ⟶ ℋ`.
* `Stacks.HodgeWeil.mapBifunctorMap_hodgeSummandι_dgAction`: the multiplication of `ℋ`
  restricts to the wedge product of the summands.
* `Stacks.HodgeWeil.hodgeDgaEquiv_cup`: **`hodgeDgaEquiv` is multiplicative**, for the cup
  product `hodgePieceMul` of Hodge cohomology, Koszul sign `(-1)^{q p'}` included.
* `Stacks.HodgeWeil.hodgeDgaEquiv_one`: **`hodgeDgaEquiv` is unital.**
* `Stacks.HodgeWeil.cohomologyPullback_shift`: the pullback along a morphism of ringed spaces
  commutes with the shift of complexes.
* `Stacks.HodgeWeil.hodgeDgaEquiv_pullback`: **`hodgeDgaEquiv` is compatible with pullback**
  along a commutative square of schemes.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Remark 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/
