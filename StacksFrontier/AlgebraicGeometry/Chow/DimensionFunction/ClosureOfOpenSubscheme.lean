module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Scheme.ClosureOfOpenSubscheme

/-!
# Delta-dimension of the closure of a closed subscheme of an open subscheme

The delta-dimension of chapter 42 of the Stacks Project does not change when an integral scheme
over the base is replaced by a nonempty open subscheme: it is read off at the generic point, an
open immersion matches generic points, and the relative dimension of Stacks 02JW does not see an
open immersion because such a morphism induces isomorphisms on residue fields.

Consequently the closure in `X` of an integral closed subscheme of an open subscheme `U` of `X`
has the delta-dimension of the subscheme one started with, because the comparison morphism
`Stacks.IdealSheaf.closureSubschemeOpenMap` is an open immersion compatible with the structure
morphisms to the base.

## Main results

* `Stacks.Chow.schemeDeltaDimension_eq_of_isOpenImmersion`: an open immersion of integral
  schemes over the base preserves delta-dimension.
* `Stacks.Chow.schemeDeltaDimension_comp_open`: the special case of an integral open subscheme
  of an integral scheme over the base.
* `Stacks.Chow.closureIdeal_schemeDeltaDimension`: the closure of an integral closed subscheme
  of an open subscheme has the delta-dimension of that closed subscheme.

## References

* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- An open immersion of integral schemes over the base preserves delta-dimension: the
delta-dimension is read off at the generic point, which the open immersion matches, and the
relative dimension does not see an open immersion. -/
theorem schemeDeltaDimension_eq_of_isOpenImmersion (C : ChowSituation.{u}) {Y Z : Scheme.{u}}
    (m : Y ⟶ Z) [IsOpenImmersion m] [IsIntegral Y] [IsIntegral Z] (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (hm : m ≫ sZ = sY) :
    schemeDeltaDimension C sZ = schemeDeltaDimension C sY := by
  rw [schemeDeltaDimension_eq_genericPoint C sZ, schemeDeltaDimension_eq_genericPoint C sY,
    ← genericPoint_eq_of_isOpenImmersion m,
    ← relativeDimension_comp_isOpenImmersion C.dimensionFunction m sZ (genericPoint Y), hm]

/-- The delta-dimension of an integral scheme locally of finite type over the base is unchanged
on passing to an integral open subscheme. -/
theorem schemeDeltaDimension_comp_open (C : ChowSituation.{u}) {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsOpenImmersion i] [IsIntegral X] (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral Y] :
    schemeDeltaDimension C (i ≫ p) = schemeDeltaDimension C p :=
  (schemeDeltaDimension_eq_of_isOpenImmersion C i p (i ≫ p) rfl).symm

/-- The closure in `X` of an integral closed subscheme of an open subscheme `U` of `X` has the
same delta-dimension over the base as that closed subscheme. -/
theorem closureIdeal_schemeDeltaDimension {U X : Scheme.{u}} (C : ChowSituation.{u}) (j : U ⟶ X)
    [IsOpenImmersion j] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S)
    [LocallyOfFiniteType sU] (hj : j ≫ sX = sU) (I : U.IdealSheafData) [IsIntegral I.subscheme]
    {n : ℤ} (hI : schemeDeltaDimension C (I.subschemeι ≫ sU) = (n : EInt)) :
    schemeDeltaDimension C ((IdealSheaf.closureIdeal j I).subschemeι ≫ sX) = (n : EInt) := by
  have : IsIntegral (IdealSheaf.closureIdeal j I).subscheme :=
    IdealSheaf.closureIdeal_integral j I
  refine (schemeDeltaDimension_eq_of_isOpenImmersion C
    (IdealSheaf.closureSubschemeOpenMap j I) _ _ ?_).trans hI
  rw [← Category.assoc, IdealSheaf.closureSubschemeOpenMap_comp_subschemeι, Category.assoc, hj]

end Stacks.Chow

end
