module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdealsCongr
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fitting ideal sheaves of relative differentials under base change

For a morphism of schemes `f : X ⟶ S` locally of finite type, the sheaf of relative differentials
`Ω_{X/S}` is quasi-coherent of finite type, so its Fitting ideal sheaves are defined and cut out
the descending chain of closed subschemes `X = Z₋₁ ⊇ Z₀ ⊇ Z₁ ⊇ ⋯`. Forming
those closed subschemes commutes with arbitrary base change.

## Main results

* `AlgebraicGeometry.fittingIdeal_relativeDifferentials_comap`: for a cartesian square with right
  edge `f` and left edge `f'`, the inverse image along the top edge of the `r`-th Fitting ideal
  sheaf of `Ω_{X/S}` is the `r`-th Fitting ideal sheaf of `Ω_{X'/S'}`.

## References

* [Stacks Project, Tag 0C3I](https://stacks.math.columbia.edu/tag/0C3I)
* [Stacks Project, Tag 0C3D](https://stacks.math.columbia.edu/tag/0C3D)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
* [Stacks Project, Tag 01V2](https://stacks.math.columbia.edu/tag/01V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- For a cartesian square of schemes with right edge `f : X ⟶ S` locally of finite type, left
edge `f' : X' ⟶ S'` and top edge `g' : X' ⟶ X`, the inverse image along `g'` of the `r`-th
Fitting ideal sheaf of `Ω_{X/S}` is the `r`-th Fitting ideal sheaf of `Ω_{X'/S'}`: the closed
subschemes cut out by the Fitting ideals of the relative differentials commute with arbitrary
base change. -/
@[stacks 0C3I, sga "7 VI 5.3" "(1)"]
public theorem fittingIdeal_relativeDifferentials_comap {X' X S' S : Scheme.{u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (h : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (r : ℤ) :
    (fittingIdeal (Scheme.Hom.relativeDifferentials f) r).comap g' =
      fittingIdeal (Scheme.Hom.relativeDifferentials f') r := by
  have : LocallyOfFiniteType f' :=
    locallyOfFiniteType_isStableUnderBaseChange.of_isPullback h inferInstance
  have : IsIso (Scheme.Hom.relativeDifferentialsMap g' f f' g h.w) :=
    Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback g' f' f g h
  have : ((Scheme.Modules.pullback g').obj (Scheme.Hom.relativeDifferentials f)).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType g'.toLRSHom.toShHom _
  exact (fittingIdeal_comap g' _ r).trans
    (fittingIdeal_congr (asIso (Scheme.Hom.relativeDifferentialsMap g' f f' g h.w)) r)

end AlgebraicGeometry

end
