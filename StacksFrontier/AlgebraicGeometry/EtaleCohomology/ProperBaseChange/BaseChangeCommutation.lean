module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# Cohomology commuting with base change

For a morphism of schemes `f : X ⟶ Y`, cohomology commutes with base change for `f` when, for
every cartesian square with `X' = Y' ×_Y X` and every torsion abelian sheaf `F` on `X_étale`,
the canonical map `g^{-1}Rf_*F ⟶ Rf'_*(g')^{-1}F` is an isomorphism.

## Main definitions

* `Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange` — that condition.

## Main results

* `Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.of_eq` — the condition only depends
  on the morphism, so it transports along an equality of morphisms.

## Implementation notes

The map whose invertibility is asserted is
`Stacks.EtaleCohomology.etaleAbelianSheafDerivedBaseChange`, the canonical base change map of a
commutative square on the unbounded derived categories of abelian sheaves of the small étale
sites, evaluated at the sheaf placed in degree zero. It is exactly the map `(59.91.5.3)` of the
source, so the condition below is the source's phrase "cohomology commutes with base change for
`f`" read literally, in every degree at once rather than degreewise. Torsion is the intrinsic
local condition `Stacks.Torsion.torsionSheafProperty`.

Being cartesian is `CategoryTheory.IsPullback g' f' f g`; its commutativity `sq.w` is what the
base change map consumes, so no compatibility is left implicit.  The two schemes of the square
are strict implicit arguments, so that a proof of the condition can be passed as a value without
being eta-expanded.

## References

* [Stacks Project, Tag 095S](https://stacks.math.columbia.edu/tag/095S)
* [Stacks Project, Tag 0A4A](https://stacks.math.columbia.edu/tag/0A4A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-- **Cohomology commutes with base change for `f : X ⟶ Y`**: for every cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
and every torsion abelian sheaf `F` on the small étale site of `X`, the canonical base change
map `g^{-1}Rf_*F ⟶ Rf'_*(g')^{-1}F` in the derived category of abelian sheaves on `Y'_étale` is
an isomorphism. -/
public def CohomologyCommutesWithBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g)
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}),
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F →
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' sq.w F)

/-- The condition depends only on the morphism, hence transports along an equality of
morphisms. -/
public theorem CohomologyCommutesWithBaseChange.of_eq {X Y : Scheme.{u}} {f₁ f₂ : X ⟶ Y}
    (h : f₁ = f₂) (hf : CohomologyCommutesWithBaseChange.{u, v} f₁) :
    CohomologyCommutesWithBaseChange.{u, v} f₂ := h ▸ hf

end Stacks.EtaleCohomology

end
