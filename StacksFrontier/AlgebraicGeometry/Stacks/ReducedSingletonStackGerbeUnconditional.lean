module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedSingletonStackGerbe

/-!
# A reduced, locally Noetherian one-point algebraic stack is a gerbe

A reduced, locally Noetherian algebraic stack `𝒵` with `|𝒵|` a singleton is a gerbe over a
reduced, locally Noetherian algebraic space `Z` with `|Z|` a singleton.

## Main results

* `exists_gerbeOver_reducedLocallyNoetherianWithUniquePoint_unconditional`: a reduced, locally
  Noetherian algebraic stack with a single point is a gerbe over a reduced, locally Noetherian
  algebraic space with a single point.

## References

* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
* [Stacks Project, Tag 06G4](https://stacks.math.columbia.edu/tag/06G4)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06PX](https://stacks.math.columbia.edu/tag/06PX)
* [Stacks Project, Tag 06PZ](https://stacks.math.columbia.edu/tag/06PZ)
* [Stacks Project, Tag 06Q3](https://stacks.math.columbia.edu/tag/06Q3)
* [Stacks Project, Tag 06Q8](https://stacks.math.columbia.edu/tag/06Q8)
* [Stacks Project, Tag 06QI](https://stacks.math.columbia.edu/tag/06QI)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
* [Stacks Project, Tag 06QK](https://stacks.math.columbia.edu/tag/06QK)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `𝒵` be a reduced, locally Noetherian algebraic stack over `S` whose space of points is a
singleton. Then there is an algebraic stack `Z` over `S` which is representable by an algebraic
space, a 1-morphism `π : 𝒵 ⟶ Z` making `𝒵` a gerbe over `Z`, and `Z` is again reduced, locally
Noetherian with a single point. -/
@[stacks 06QK "unconditional. The field cover of Stacks 06MP (1) implies (2), the flatness and \
local finite presentation of the inertia and their fppf descent, Stacks 06QJ (2) implies (1) \
cited from GerbeOfFlatInertia, the gerbe 1-morphism being surjective, flat and locally of \
finite presentation by Stacks 06QI, and the conclusion about the base by Stacks 06MP (2) \
implies (1) applied to the composite from the field spectrum"]
alias exists_gerbeOver_reducedLocallyNoetherianWithUniquePoint_unconditional :=
  exists_gerbeOver_reducedLocallyNoetherianWithUniquePoint

end AlgebraicGeometry.Stack.AlgebraicStacks

end
