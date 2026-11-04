module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProperBaseChangeUnbounded
import StacksCore.Tactic.StacksAttribute

/-!
# Registration of [Stacks, Tag 0F7L] on unbounded derived categories

For a torsion ring `Λ`, Stacks constructs the isomorphism `g⁻¹ ∘ Rf_! ≅ Rf'_! ∘ (g')⁻¹` of
[Stacks, Tag 0F7L] also on the unbounded derived categories `D(X_étale, Λ)`, the first arrow of the
construction being the unbounded proper base change theorem ([Stacks, Tag 0F0C]). That isomorphism
is `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChangeIso`, and this file registers it.

The compatibility of the base change isomorphisms with the isomorphisms of [Stacks, Tag 0F7J] is
`Stacks.EtaleCohomology.derivedLowerShriekBaseChange_compIso`, on `D⁺_tors(X_étale, Λ)`.

## References

* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
* [Stacks Project, Tag 0F0C](https://stacks.math.columbia.edu/tag/0F0C)
-/

add_to_stacks 0F7L "the isomorphism g⁻¹ ∘ Rf_! ≅ Rf'_! ∘ (g')⁻¹ on unbounded D(X_étale, Λ), Λ a torsion ring" Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChangeIso
