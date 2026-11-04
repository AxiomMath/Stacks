module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberConnected
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The special fibre of a regular proper model is geometrically connected

In the situation of [Stacks, Tag 0C61] the model `f : X ⟶ Spec(R)` has geometrically connected
fibres, by the second conclusion of [Stacks, Tag 0AY8]:
`Stacks.Models.RegularProperModelSituation.geometricallyConnected_X_to_R`. Base change to the
residue field gives that the special fibre `X_k ⟶ Spec(k)` is geometrically connected.

## Main results

* `Stacks.Models.RegularProperModelSituation.geometricallyConnected_specialFiberToSpec`: the
  special fibre `X_k ⟶ Spec(k)` is geometrically connected.

## References

* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **The special fibre `X_k ⟶ Spec(k)` of the model is geometrically connected**, being the base
change of the geometrically connected morphism `X ⟶ Spec(R)`. -/
@[ega "III 4.3.4" "special case"]
instance geometricallyConnected_specialFiberToSpec :
    GeometricallyConnected S.specialFiberToSpec :=
  haveI := S.geometricallyConnected_X_to_R
  inferInstanceAs (GeometricallyConnected
    (pullback.snd S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))))

end Stacks.Models.RegularProperModelSituation

end
