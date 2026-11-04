module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.TorsionExponent
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The product square of an open immersion with a scheme over a field

Let `K` be a field, `j : U ⟶ X` a morphism of schemes over `K` and `Y` a scheme over `K`. Taking
the product with `Y` over `Spec K` gives the square
```
Y ×_K X  <--h--  Y ×_K U
   |q               |p
   ↓                ↓
   X     <--j--     U
```
whose base change map `q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕` is the subject of [Stacks, Tag 0F1H]. That lemma
says the map is an isomorphism when `K` is a field, `j` is an open immersion of schemes of
finite type over `K`, `Y` is of finite type over `K`, and `𝓕` is an abelian sheaf on `U_étale`
whose stalks are torsion of orders invertible in `K`.

This file sets the square up and checks that it is cartesian. It also names the base change map
and the torsion condition, so that the lemma can be stated in the form the source gives it.

## Main definitions

* `Stacks.EtaleCohomology.OpenImmersionProductSquare.q`, `.p`, `.h` — the three new sides of
  the square, as morphisms out of the chosen fibre products `Y ×_K X` and `Y ×_K U`.
* `Stacks.EtaleCohomology.OpenImmersionProductSquare.baseChangeMap` — the base change map
  `q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕` on bounded below derived categories of abelian sheaves on the small
  étale sites. It is `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` evaluated at `𝓕`
  placed in degree zero.
* `Stacks.EtaleCohomology.OpenImmersionProductSquare.HasTorsionStalksInvertibleIn` — the
  condition that the stalks of `𝓕` are torsion of orders invertible in `K`. Equivalently,
  every local section is annihilated, locally, by a positive integer prime to the exponential
  characteristic of `K`.

## Main results

* `Stacks.EtaleCohomology.OpenImmersionProductSquare.h_comp_q` — the square commutes.
* `Stacks.EtaleCohomology.OpenImmersionProductSquare.isPullback` — the square is cartesian. It
  is the left half of the pasting of the two product squares over `Spec K`.

## Implementation notes

*The torsion condition.* The stalks of `𝓕` at geometric points are torsion of orders invertible
in `K` exactly when each local section is, on some étale covering, killed by a positive integer
invertible in `K`. A positive integer is invertible in `K` exactly when it is prime to the
exponential characteristic of `K`. That is `Stacks.Torsion.IsPrimeToCharacteristicTorsion` at
`ringExpChar K`, and the condition is defined as that.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.OpenImmersionProductSquare

attribute [local instance] HasDerivedCategory.standard

variable {K : Type u} [Field K] {X U Y : Scheme.{u}}
  (sX : X ⟶ Spec (.of K)) (sU : U ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
  (j : U ⟶ X) (hj : j ≫ sX = sU)

/-- The projection `q : Y ×_K X ⟶ X`. -/
abbrev q : pullback sY sX ⟶ X := pullback.snd sY sX

/-- The projection `p : Y ×_K U ⟶ U`. -/
abbrev p : pullback sY sU ⟶ U := pullback.snd sY sU

/-- The morphism `h = id_Y × j : Y ×_K U ⟶ Y ×_K X`. -/
def h : pullback sY sU ⟶ pullback sY sX :=
  pullback.map sY sU sY sX (𝟙 Y) j (𝟙 _) (by simp) (by simp [hj])

/-- The first projection of `Y ×_K X` composed with `h` is the first projection of `Y ×_K U`. -/
@[reassoc (attr := simp)]
theorem h_comp_fst : h sX sU sY j hj ≫ pullback.fst sY sX = pullback.fst sY sU :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- **The square commutes**: `h ≫ q = p ≫ j`. -/
@[reassoc]
theorem h_comp_q : h sX sU sY j hj ≫ q sX sY = p sU sY ≫ j :=
  pullback.lift_snd _ _ _

/-- **The square is cartesian**: `Y ×_K U` is the fibre product of `Y ×_K X ⟶ X` and `j`. It is
the left half of the pasting of the square with the product square of `Y ×_K X`, the pasted
square being the product square of `Y ×_K U`. -/
theorem isPullback : IsPullback (h sX sU sY j hj) (p sU sY) (q sX sY) j := by
  refine IsPullback.of_right ?_ (h_comp_q sX sU sY j hj) (IsPullback.of_hasPullback sY sX)
  rw [h_comp_fst, hj]
  exact IsPullback.of_hasPullback sY sU

/-- **The base change map** `q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕` of [Stacks, Tag 0F1H], for an abelian sheaf
`𝓕` on the small étale site of `U`: the canonical derived base change comparison of the square,
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`, at `𝓕` placed in degree zero. -/
def baseChangeMap (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1}) :
    (smallEtalePullbackAb (q sX sY)).rightDerivedFunctorPlus.obj
        ((smallEtalePushforwardAb j).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj 𝓕)) ⟶
      (smallEtalePushforwardAb (h sX sU sY j hj)).rightDerivedFunctorPlus.obj
        ((smallEtalePullbackAb (p sU sY)).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj 𝓕)) :=
  (smallEtaleDerivedBaseChangeAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
    (h_comp_q sX sU sY j hj)).app ((DerivedCategory.Plus.singleFunctor _ 0).obj 𝓕)

/-- An abelian sheaf `𝓕` on the small étale site of `U` **has stalks which are torsion of orders
invertible in `K`**: every local section is, locally, annihilated by a positive integer prime to
the exponential characteristic of `K`, that is, by a positive integer invertible in `K`. -/
abbrev HasTorsionStalksInvertibleIn (K : Type u) [Field K]
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1}) : Prop :=
  Stacks.Torsion.IsPrimeToCharacteristicTorsion (smallEtaleTopology U) (ringExpChar K) 𝓕

end Stacks.EtaleCohomology.OpenImmersionProductSquare

end
