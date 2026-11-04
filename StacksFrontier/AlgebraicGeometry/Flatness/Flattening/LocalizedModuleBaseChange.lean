module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ResidueFieldFibreInjectivity

/-!
# Base change of the standing situation of Stacks 0AT6

Stacks 0AT6 is the situation of a ring map `A → B` of finite presentation, a multiplicative
subset `S ⊆ B` and a finitely presented module `N` over a localization `Bₛ` of `B` at `S`. The
source records, immediately after stating it, that the situation can be base changed along any
ring map `A → A₁`: one takes `B₁ = B ⊗_A A₁`, lets `S₁` be the image of `S`, and puts
`N₁ = N ⊗_A A₁`, "because `S₁⁻¹B₁ = S⁻¹B ⊗_A A₁`".

This file carries that construction out, and in particular proves the parenthetical: the
localization of the base-changed algebra at the image submonoid is the base change of the
localization.

## Main definitions

* `AlgebraicGeometry.FinitelyPresentedLocalizedModuleSituation.baseChange` is the base-changed
  situation, with `B₁ = A₁ ⊗_A B`, `Bₛ₁ = A₁ ⊗_A Bₛ` and `N₁ = Bₛ₁ ⊗_{Bₛ} N`.

## Main results

* `AlgebraicGeometry.FinitelyPresentedLocalizedModuleSituation.isLocalization_baseChange` is the
  statement that `A₁ ⊗_A Bₛ` is a localization of `A₁ ⊗_A B` at the image of `S`.

## Implementation notes

The module of the base-changed situation is taken to be `Bₛ₁ ⊗_{Bₛ} N` rather than the source's
`N ⊗_A A₁`. The two are isomorphic, but only the former lives in the universe
`max u₁ u₃ u₄` that Stacks 0AT8's statement prescribes, whereas `A₁ ⊗_A N` lives in
`max u₁ u₄`; and it is the former that has `IsBaseChange` on the nose.

`Mathlib`'s `IsLocalization.tensor` is the same fact in a different representative: it gives
`IsLocalization (algebraMapSubmonoid B₁ S) (B₁ ⊗_B Bₛ)`, whose carrier sits in
`Type (max u₁ u₂ u₃)`. The representative needed here, `A₁ ⊗_A Bₛ`, sits in
`Type (max u₁ u₃)`, and the two universes are incomparable, so the instance cannot be
transported along an isomorphism of carriers. Instead `Algebra.isLocalization_iff_isPushout`
turns the statement into a pushout square, and `Algebra.IsPushout.comp_iff` deduces that square
from the two base-change squares over `A`.

A `LocalQuotientBaseChange` cannot be assembled from this construction as it stands. Its field
`towerBaseLocalized` has type `IsScalarTower A (Y.A) (Y.Bₛ)`, whose instance argument
`Algebra Y.A Y.Bₛ` is the situation's *derived* instance
`FinitelyPresentedLocalizedModuleSituation.algebraLocalized`, a `RingHom.toAlgebra` of the
composite `Y.A → Y.B → Y.Bₛ`, whose `smul` is `r • x = algebraMap r * x`. The tensor product's
own `Algebra.TensorProduct.leftAlgebra` has `smul = Algebra.TensorProduct.leftHasSMul`. The two
instances have equal `algebraMap`s, hence are equal by `Algebra.algebra_ext`, but they are not
definitionally equal, so neither `inferInstance` nor a term ascription bridges them, and
`localizedPushout` depends on the resulting `Module Y.A Y.Bₛ` structure. See the module
docstring of
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LocalQuotientSpreadout` for the route.

The right-hand algebra structure on a tensor product is not a global instance in `Mathlib` (it
would make the action of `A` on `A ⊗_R A` ambiguous), so it is enabled locally here. Several
instances that it supplies are found by `inferInstance` at variables and *not* at the
projections `X.A`, `X.B`, `X.Bₛ` of the situation — a discrimination-tree miss, cured by naming
the instance.

## References

* [Stacks Project, Tag 0AT6](https://stacks.math.columbia.edu/tag/0AT6)
* [Stacks Project, Tag 0AT8](https://stacks.math.columbia.edu/tag/0AT8)
-/

@[expose] public section

open TensorProduct

universe u₁ u₂ u₃ u₄

namespace AlgebraicGeometry

namespace FinitelyPresentedLocalizedModuleSituation

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
  (A' : Type u₁) [CommRing A'] [Algebra X.A A']

/-- The structure map of the base-changed situation, from the base-changed algebra to the
base-changed localization. -/
noncomputable def baseChangeAlgHom : (A' ⊗[X.A] X.B) →ₐ[A'] (A' ⊗[X.A] X.Bₛ) :=
  Algebra.TensorProduct.map (AlgHom.id A' A') (IsScalarTower.toAlgHom X.A X.B X.Bₛ)

/-- The base-changed localization is an algebra over the base-changed algebra. -/
@[instance_reducible]
noncomputable def algebraBaseChange : Algebra (A' ⊗[X.A] X.B) (A' ⊗[X.A] X.Bₛ) :=
  (X.baseChangeAlgHom A').toRingHom.toAlgebra

attribute [local instance] algebraBaseChange

/-- The base-changed localization is an algebra over the original algebra. -/
@[instance_reducible]
noncomputable def algebraBaseChangeOfAlgebra : Algebra X.B (A' ⊗[X.A] X.Bₛ) :=
  ((algebraMap X.Bₛ (A' ⊗[X.A] X.Bₛ)).comp (algebraMap X.B X.Bₛ)).toAlgebra

attribute [local instance] algebraBaseChangeOfAlgebra

section Towers

/-- The original algebra reaches the base-changed localization through the original
localization. -/
instance isScalarTower_baseChange_of_localization :
    IsScalarTower X.B X.Bₛ (A' ⊗[X.A] X.Bₛ) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The new base ring reaches the base-changed localization through the base-changed
algebra. -/
instance isScalarTower_baseChange_base :
    IsScalarTower A' (A' ⊗[X.A] X.B) (A' ⊗[X.A] X.Bₛ) :=
  IsScalarTower.of_algebraMap_eq' ((X.baseChangeAlgHom A').comp_algebraMap).symm

/-- The original algebra reaches the base-changed localization through the base-changed
algebra. -/
instance isScalarTower_baseChange_algebra :
    IsScalarTower X.B (A' ⊗[X.A] X.B) (A' ⊗[X.A] X.Bₛ) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ ↦ rfl)

/-- The base ring reaches the base-changed algebra through the original algebra. This is
`Algebra.TensorProduct.right_isScalarTower`, which instance search does not find at the
projections of a situation. -/
instance isScalarTower_baseChange_right : IsScalarTower X.A X.B (A' ⊗[X.A] X.B) :=
  Algebra.TensorProduct.right_isScalarTower

/-- The base ring reaches the base-changed localization through the original localization. -/
instance isScalarTower_baseChange_right_localization :
    IsScalarTower X.A X.Bₛ (A' ⊗[X.A] X.Bₛ) :=
  Algebra.TensorProduct.right_isScalarTower

/-- The base ring reaches the base-changed localization through the original algebra. -/
instance isScalarTower_baseChange_source :
    IsScalarTower X.A X.B (A' ⊗[X.A] X.Bₛ) := by
  refine IsScalarTower.of_algebraMap_eq' ?_
  rw [IsScalarTower.algebraMap_eq X.A X.Bₛ (A' ⊗[X.A] X.Bₛ),
    IsScalarTower.algebraMap_eq X.A X.B X.Bₛ, ← RingHom.comp_assoc]
  rfl

/-- The base ring reaches the base-changed localization through the base-changed algebra. -/
instance isScalarTower_baseChange_total :
    IsScalarTower X.A (A' ⊗[X.A] X.B) (A' ⊗[X.A] X.Bₛ) := by
  refine IsScalarTower.of_algebraMap_eq' ?_
  rw [IsScalarTower.algebraMap_eq X.A A' (A' ⊗[X.A] X.Bₛ),
    IsScalarTower.algebraMap_eq A' (A' ⊗[X.A] X.B) (A' ⊗[X.A] X.Bₛ),
    IsScalarTower.algebraMap_eq X.A A' (A' ⊗[X.A] X.B), RingHom.comp_assoc]

/-- The base-changed localization is the base change of the localization. Named so that it can
be fed as a term where instance search would have to see through `baseChange`. -/
theorem isPushout_baseChange_localization :
    Algebra.IsPushout X.A A' X.Bₛ (A' ⊗[X.A] X.Bₛ) := inferInstance

end Towers

/-- **The parenthetical of Stacks 0AT6.** The base change of a localization is a localization of
the base change: `A₁ ⊗_A Bₛ` is a localization of `A₁ ⊗_A B` at the image of `S`. -/
theorem isLocalization_baseChange :
    IsLocalization (X.S.map (algebraMap X.B (A' ⊗[X.A] X.B))) (A' ⊗[X.A] X.Bₛ) := by
  have hleft : Algebra.IsPushout X.A X.B A' (A' ⊗[X.A] X.B) :=
    (Algebra.IsPushout.comm _ _ _ _).mpr inferInstance
  have hbig : Algebra.IsPushout X.A X.Bₛ A' (A' ⊗[X.A] X.Bₛ) :=
    (Algebra.IsPushout.comm _ _ _ _).mpr inferInstance
  have hright : Algebra.IsPushout X.B X.Bₛ (A' ⊗[X.A] X.B) (A' ⊗[X.A] X.Bₛ) := by
    have := hleft
    exact (Algebra.IsPushout.comp_iff X.A X.B A' (A' ⊗[X.A] X.B)
      (T := X.Bₛ) (T' := A' ⊗[X.A] X.Bₛ)).mp hbig
  exact (Algebra.isLocalization_iff_isPushout X.S X.Bₛ).mpr hright.symm

/-- **The base change of the standing situation of Stacks 0AT6** along a ring map `A → A₁` out
of the base ring: the algebra becomes `A₁ ⊗_A B`, the multiplicative subset the image of `S`,
the localization `A₁ ⊗_A Bₛ` and the module `(A₁ ⊗_A Bₛ) ⊗_{Bₛ} N`.

Untagged: `@[stacks 0AT6]` is already placed, on the situation itself
(`AlgebraicGeometry.FinitelyPresentedLocalizedModuleSituation`), and the base change is a remark
following that statement rather than a separate result. -/
noncomputable def baseChange :
    FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂, max u₁ u₃, max u₁ (max u₃ u₄)} where
  A := A'
  B := A' ⊗[X.A] X.B
  Bₛ := A' ⊗[X.A] X.Bₛ
  N := (A' ⊗[X.A] X.Bₛ) ⊗[X.Bₛ] X.N
  S := X.S.map (algebraMap X.B (A' ⊗[X.A] X.B))
  algebraBBₛ := X.algebraBaseChange A'
  isLocalization := X.isLocalization_baseChange A'
  finitePresentationN :=
    FinitePresentation.of_isBaseChange _ (TensorProduct.isBaseChange X.Bₛ X.N _)


end FinitelyPresentedLocalizedModuleSituation

end AlgebraicGeometry

end
