module

public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity

/-!
# A bivariant class read for an equal morphism

`Stacks.Chow.BivariantClass.copy`, in `StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity`,
reads a bivariant class `c ∈ A^p(X ⟶ Y)` for `f` as a class for an equal morphism `f'` and an
equal degree `p'`. This module proves that the copy is heterogeneously equal to `c`.

## Main results

* `Stacks.Chow.BivariantClass.copy_heq` — `BivariantClass.copy … c ≍ c`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- A class read for an equal morphism and degree (`Stacks.Chow.BivariantClass.copy`) is
heterogeneously equal to the class. -/
theorem BivariantClass.copy_heq {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
    {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f f' : X ⟶ Y} [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] (hff' : f = f') (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX)
    {p p' : ℤ} (hpp' : p = p') (c : BivariantClass C G sX sY f hf p) :
    BivariantClass.copy C G sX sY hff' hf hf' hpp' c ≍ c := by
  subst hff' hpp'
  rfl

end Stacks.Chow

end
