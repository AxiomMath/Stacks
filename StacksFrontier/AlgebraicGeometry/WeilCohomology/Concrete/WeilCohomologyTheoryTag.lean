module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilCohomologyTheory
import StacksCore.Tactic.StacksAttribute

/-!
# Definition 0FI2: Weil cohomology theories

Definition 0FI2 of the Stacks Project defines a *Weil cohomology theory* over `k` with
coefficients in a field `F` of characteristic zero. It consists of data (D0)–(D3) satisfying the
axioms (A), (B), (C) of Section 45.9 (Tag 0FHA), together with the equivalent conditions (1) and
(2) of Lemma 0FI0 for every smooth projective `X` over `k`. That definition is
`Stacks.WeilCohomology.WeilCohomologyTheory`, and this file registers it.

## Implementation notes

* The coefficient field is not required to have characteristic zero. This generalizes the
  definition; with `[CharZero F]` it is exactly the notion of the source.
* Of the two equivalent conditions of Lemma 0FI0 the structure records condition (2):
  `H^0(Spec Γ(X, 𝒪_X)) → H^0(X)` is an isomorphism. Condition (1) follows from it through
  Lemma 0FI0.
* Axiom (B)(b), `∫_{X × Y} = ∫_X ⊗ ∫_Y` via (B)(a), reads `∫_X ⊗ ∫_Y` as zero on the Künneth
  components of `H^{2(d+e)}(X × Y)(d + e)` other than `H^{2d}(X)(d) ⊗ H^{2e}(Y)(e)`. Each trace
  map is extended by zero outside its own degree, the convention the chapter states in
  "Ad (A6)"; it is the only reading under which the equation is defined on the whole of
  `H^{2(d+e)}(X × Y)(d + e)`.

## References

* [Stacks Project, Tag 0FI2](https://stacks.math.columbia.edu/tag/0FI2)
* [Stacks Project, Section 45.9 (Tag 0FHA)](https://stacks.math.columbia.edu/tag/0FHA)
* [Stacks Project, Tag 0FI0](https://stacks.math.columbia.edu/tag/0FI0)
-/

@[expose] public section

add_to_stacks 0FI2 "Weil cohomology theory: data (D0)-(D3) on the smooth projective (01W8, not \
  merely proper) k-schemes satisfying (A), (B), (C) of 0FHA and condition (2) of 0FI0 for every \
  X, the equivalent condition (1) following by 0FI0. Generalized to any coefficient field F, \
  with no [CharZero F]: with it, this is the source's notion. (B)(b) reads ∫_X ⊗ ∫_Y as zero \
  off the top Künneth component H^{2d}(X)(d) ⊗ H^{2e}(Y)(e) of H^{2(d+e)}(X × Y)(d + e), the \
  trace maps being extended by zero outside their degree as in 'Ad (A6)'"
  Stacks.WeilCohomology.WeilCohomologyTheory

end
