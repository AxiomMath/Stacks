module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.RegularSections

/-!
# Regular sections for algebraic spaces

A global section `s` of an invertible module `𝓛` on the small étale site of an algebraic
space is *regular* when the map `𝒪_X → 𝓛`, `f ↦ fs`, is injective. That map is the morphism
corresponding to `s` under `SheafOfModules.unitHomEquiv`, and its injectivity is monicity of
that morphism: exactly `AlgebraicGeometry.IsRegularSection`, which is defined for a module
sheaf on an arbitrary ringed site. The invertibility hypothesis belongs to the applications,
not to the notion.

## Main results

* `AlgebraicGeometry.IsRegularSection` is the regular-section predicate.

## References

* [Stacks Project, Tag 0843](https://stacks.math.columbia.edu/tag/0843)
-/

@[expose] public section

add_to_stacks 0843 AlgebraicGeometry.IsRegularSection

end
