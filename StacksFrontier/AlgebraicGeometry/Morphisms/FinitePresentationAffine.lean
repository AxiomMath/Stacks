module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite presentation for a morphism of affine schemes

A morphism of affine schemes which is locally of finite presentation is of finite presentation:
an affine scheme is a quasi-compact and quasi-separated space, and a morphism between affine
schemes is affine, hence quasi-compact and quasi-separated. Over a locally Noetherian base it is
enough for the morphism to be locally of finite type.

## Main results

* `AlgebraicGeometry.finitePresentation_of_isAffine`: for a morphism of affine schemes, locally of
  finite presentation implies of finite presentation.
* `AlgebraicGeometry.finitePresentation_of_isAffine_of_locallyOfFiniteType`: the same from locally
  of finite type over a locally Noetherian base.
* `AlgebraicGeometry.finitePresentation_opens_ι_comp`: an affine open of a scheme locally of finite
  type over a locally Noetherian base is of finite presentation over that base.

## References

* [Stacks Project, Tag 01TP](https://stacks.math.columbia.edu/tag/01TP)
* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of affine schemes which is locally of finite presentation is of finite
presentation. -/
public theorem finitePresentation_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine X] [IsAffine S] [LocallyOfFinitePresentation f] : FinitePresentation f :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- A morphism of affine schemes which is locally of finite type, with locally Noetherian target,
is of finite presentation. -/
@[sga "3 VIA 2.5.4" "special case"]
public theorem finitePresentation_of_isAffine_of_locallyOfFiniteType {X S : Scheme.{u}}
    (f : X ⟶ S) [IsAffine X] [IsAffine S] [IsLocallyNoetherian S] [LocallyOfFiniteType f] :
    FinitePresentation f :=
  finitePresentation_of_isAffine f

/-- An affine open of a scheme locally of finite type over a locally Noetherian base is of finite
presentation over that base. -/
@[sga "1 IX 4.10" "affine source",
  sga "1 IX 4.7" "special case",
  sga "3 V 6.1" "special case",
  sga "3 X 3.7" "partial"]
public theorem finitePresentation_opens_ι_comp {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (U : X.Opens) (hU : IsAffineOpen U) :
    FinitePresentation (U.ι ≫ f) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsAffine U.toScheme := hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : TopologicalSpace.NoetherianSpace U.toScheme := noetherianSpace_of_isAffineOpen U hU
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry

end
