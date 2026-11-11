module

public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedClassAtInfinity.Construction
public import StacksCore.Tactic.StacksAttribute

/-!
# The localized classes of a closed cover do not depend on the first member (Stacks 0FAH)

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i_j : X_j ⟶ X` (`j = 1, 2`) be closed immersions with `X = X₁ ∪ X₂`
set theoretically, and let `E₂ ∈ D(𝒪_{X₂})` be a perfect object whose Chern classes are defined
and whose restriction to `X₁ ∩ X₂` is zero, respectively a finite locally free module of rank
`< p` in degree `0`. **Stacks 0FAH** says that the class `P'_p(E₂)`, respectively
`c'_p(E₂) ∈ A^p(X₂ ⟶ X)` of Stacks 0F9H does not depend on the choice of `X₁`: if `X₁' ⊂ X` is
another closed subscheme with `X = X₁' ∪ X₂` and with `E₂|_{X₁' ∩ X₂}` zero, respectively finite
locally free of rank `< p` in degree `0`, the classes built from `X₁` and from `X₁'` agree.

## Main results

* `Stacks.Chow.localizedPowerSumOfClosedCover_eq` — **Stacks 0FAH** for `P'_p(E₂)`.
* `Stacks.Chow.localizedChernClassOfClosedCover_eq` — **Stacks 0FAH** for `c'_p(E₂)`.

## Implementation notes

The classes are `Stacks.Chow.localizedPowerSumOfClosedCover` and
`Stacks.Chow.localizedChernClassOfClosedCover`, the constructions of Stacks 0F9H. Each has the
characterizing property `Stacks.Chow.IsClosedCoverLocalizedClass` for its own cover
(`Stacks.Chow.GysinAtInfinity.isClosedCoverLocalizedClass_closedCoverLocalizedClass`), and two
classes with that property for the covers `X = X₁ ∪ X₂` and `X = X₁' ∪ X₂` and the same class on
`X₂` agree by `Stacks.Chow.eq_of_isClosedCoverLocalizedClass`.

## References

* [Stacks Project, Tag 0FAH](https://stacks.math.columbia.edu/tag/0FAH)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Chow.GysinAtInfinity (isClosedCoverLocalizedClass_closedCoverLocalizedClass)

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X X₁ X₁' X₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) [IsClosedImmersion i₁] (i₁' : X₁' ⟶ X)
  [IsClosedImmersion i₁'] (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂]
  {E₂ : DerivedCategory X₂.Modules} (hE₂ : HasDefinedChernClasses E₂) (p : ℕ)

/-- **Stacks 0FAH, for the classes `P_p`.** Let `X` be locally of finite type over `S`, let
`i₁ : X₁ ⟶ X`, `i₁' : X₁' ⟶ X` and `i₂ : X₂ ⟶ X` be closed immersions with `X = X₁ ∪ X₂` and
`X = X₁' ∪ X₂` set theoretically, and let `E₂` be a perfect object of `D(𝒪_{X₂})` whose Chern
classes are defined and whose restrictions to `X₁ ∩ X₂` and to `X₁' ∩ X₂` are zero. Then the class
`P'_p(E₂) ∈ A^p(X₂ ⟶ X)` of Stacks 0F9H built from the cover `X = X₁ ∪ X₂` equals the one built
from the cover `X = X₁' ∪ X₂`: it does not depend on the choice of `X₁`. -/
@[stacks 0FAH "the class P'_p(E₂) ∈ A^p(X₂ ⟶ X) of Stacks 0F9H, for E₂|_{X₁ ∩ X₂} zero: the \
classes built from two covers X = X₁ ∪ X₂ and X = X₁' ∪ X₂ with E₂|_{X₁ ∩ X₂} and \
E₂|_{X₁' ∩ X₂} zero are equal"]
theorem localizedPowerSumOfClosedCover_eq
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (hcover' : Set.range i₁'.base ∪ Set.range i₂.base = Set.univ)
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X₂.toRingedSpace) E₂)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂))
    (hzero' : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁' i₂).toLRSHom.toShHom).obj E₂)) :
    localizedPowerSumOfClosedCover C sX i₁ i₂ hcover hE₂ p perfect hzero =
      localizedPowerSumOfClosedCover C sX i₁' i₂ hcover' hE₂ p perfect hzero' :=
  eq_of_isClosedCoverLocalizedClass C _ sX (i₁ ≫ sX) (i₁' ≫ sX) (i₂ ≫ sX) i₁ rfl i₁' rfl i₂
    rfl _ hcover hcover'
    (isClosedCoverLocalizedClass_closedCoverLocalizedClass C sX _ _ i₁ rfl i₂ rfl hcover _ _)
    (isClosedCoverLocalizedClass_closedCoverLocalizedClass C sX _ _ i₁' rfl i₂ rfl hcover' _ _)

/-- **Stacks 0FAH, for the Chern classes.** Let `X` be locally of finite type over `S`, let
`i₁ : X₁ ⟶ X`, `i₁' : X₁' ⟶ X` and `i₂ : X₂ ⟶ X` be closed immersions with `X = X₁ ∪ X₂` and
`X = X₁' ∪ X₂` set theoretically, and let `E₂` be a perfect object of `D(𝒪_{X₂})` whose Chern
classes are defined and whose restrictions to `X₁ ∩ X₂` and to `X₁' ∩ X₂` are each isomorphic to
a finite locally free module of rank `< p` sitting in cohomological degree `0`. Then the class
`c'_p(E₂) ∈ A^p(X₂ ⟶ X)` of Stacks 0F9H built from the cover `X = X₁ ∪ X₂` equals the one built
from the cover `X = X₁' ∪ X₂`: it does not depend on the choice of `X₁`. -/
@[stacks 0FAH "the class c'_p(E₂) ∈ A^p(X₂ ⟶ X) of Stacks 0F9H, for E₂|_{X₁ ∩ X₂} finite locally \
free of rank < p in degree 0: the classes built from two covers X = X₁ ∪ X₂ and X = X₁' ∪ X₂ \
with E₂|_{X₁ ∩ X₂} and E₂|_{X₁' ∩ X₂} finite locally free of rank < p in degree 0 are equal"]
theorem localizedChernClassOfClosedCover_eq
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (hcover' : Set.range i₁'.base ∪ Set.range i₂.base = Set.univ)
    (_perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X₂.toRingedSpace) E₂)
    (hres : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂ ≅
        (DerivedCategory.singleFunctor (pullback i₁ i₂).Modules 0).obj M))
    (hres' : ∃ M : (pullback i₁' i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (pullback.snd i₁' i₂).toLRSHom.toShHom).obj E₂ ≅
        (DerivedCategory.singleFunctor (pullback i₁' i₂).Modules 0).obj M)) :
    localizedChernClassOfClosedCover C sX i₁ i₂ hcover hE₂ p hres =
      localizedChernClassOfClosedCover C sX i₁' i₂ hcover' hE₂ p hres' :=
  eq_of_isClosedCoverLocalizedClass C _ sX (i₁ ≫ sX) (i₁' ≫ sX) (i₂ ≫ sX) i₁ rfl i₁' rfl i₂
    rfl _ hcover hcover'
    (isClosedCoverLocalizedClass_closedCoverLocalizedClass C sX _ _ i₁ rfl i₂ rfl hcover _ _)
    (isClosedCoverLocalizedClass_closedCoverLocalizedClass C sX _ _ i₁' rfl i₂ rfl hcover' _ _)

end Stacks.Chow

end
