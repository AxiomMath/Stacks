module

public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.RingTheory.RegularRing.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Regularity of the local rings of a scheme smooth over a field

Every local ring of a scheme smooth over a field is a regular local ring.

## Main results

* `AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth_over_field`: the local ring of a scheme
  smooth over a field, at any of its points, is a regular local ring.

## References

* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
* [Stacks Project, Tag 02IS](https://stacks.math.columbia.edu/tag/02IS)
* [Stacks Project, Tag 00OD](https://stacks.math.columbia.edu/tag/00OD)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Let `k` be a field and let `X` be a scheme smooth over `k`. Then for every point `x` of `X`
the local ring `𝒪_{X, x}` is a regular local ring. -/
@[sga "1 II 5.3" "special case"]
public theorem isRegularLocalRing_stalk_of_smooth_over_field
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hxU, hU⟩ := isRegular_of_smooth_over_field f x
  let : IsRegularRing Γ(X, U) := hU
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨x, hxU⟩
  exact IsRegularRing.isRegularLocalRing_of_isLocalization
    (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal (X.presheaf.stalk x)

end AlgebraicGeometry

end
