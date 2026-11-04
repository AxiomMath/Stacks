module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LocalizedModuleBaseChange
public import StacksFrontier.RingTheory.Flat.LocalizationUniversalInjectivity
public import StacksFrontier.RingTheory.Flat.NoetherianSpreadout

/-!
# The local quotient base change of the situation of Stacks 0AT6

Stacks 0AT8 asserts that the situation of Stacks 0AT6 acquires a pure spreadout after base
change to a suitable finitely generated quotient of a local ring of the base. This file
supplies the first half of that assembly: the base change of the situation to a quotient
`A_𝔭 ⧸ I` of a local ring of the base is a `LocalQuotientBaseChange`. The pure-spreadout half
is not carried out here.

## Main definitions

* `AlgebraicGeometry.FinitelyPresentedLocalizedModuleSituation.localQuotientBaseChange` exhibits
  `X.baseChange (A_𝔭 ⧸ I)` as a `LocalQuotientBaseChange` of `X` at `𝔭` and `I`.

## Main results

* `Algebra.IsPushout.of_algebra_eq` transports `Algebra.IsPushout R S R' S'` along an *equality*
  of the algebra structure of `S'` over `S`.
* `AlgebraicGeometry.FinitelyPresentedLocalizedModuleSituation.algebraLocalized_baseChange_eq`
  identifies the situation's derived algebra structure on the base-changed localization over the
  base-changed base ring with the tensor product's own left algebra structure.

## Implementation notes

The field `towerBaseLocalized` of `LocalQuotientBaseChange` has type
`IsScalarTower X.A Y.A Y.Bₛ`, and `localizedPushout` has type
`Algebra.IsPushout X.A Y.A X.Bₛ Y.Bₛ`. Both mention the instance `Algebra Y.A Y.Bₛ`, which for
`Y = X.baseChange A₁` is the situation's *derived* instance `algebraLocalized`: the
`RingHom.toAlgebra` of the composite `Y.A → Y.B → Y.Bₛ`, whose `smul` is
`r • x = algebraMap r * x`. The tensor product's own `Algebra.TensorProduct.leftAlgebra` has
`smul = Algebra.TensorProduct.leftHasSMul`. The two have equal `algebraMap`s, hence are equal by
`Algebra.algebra_ext`, but they are **not** definitionally equal, so no term ascription bridges
them.

Two devices settle this. First, the equality of the two instances is proved outright
(`algebraLocalized_baseChange_eq`) and `Algebra.IsPushout.of_algebra_eq` transports the pushout
square along it; `subst` makes the two `IsScalarTower` side conditions have the same type, so
proof irrelevance disposes of them. Second, the three algebra structures that the structure's
instance-implicit fields carry — `Algebra X.A Y.A`, `Algebra X.A Y.Bₛ` and `Algebra X.Bₛ Y.Bₛ` —
are given *names* at the `X.baseChange A₁` projection spelling and enabled as local instances,
because instance search does not see through `baseChange` and therefore cannot find them at
`Y.A`/`Y.Bₛ`, while an anonymous value supplied to an instance-implicit field is not in scope for
the later fields of the same `where` block. With the names in place,
`IsScalarTower.of_algebraMap_eq` reduces `towerBaseLocalized` to the `algebraMap` agreement.

Those local instances must be introduced *after* every fact about `A₁ ⊗[X.A] X.Bₛ` that is used
has been named: once `algebraLocalizedBaseChangeLocalized` is a local instance, a search for
`Algebra X.Bₛ (A₁ ⊗[X.A] X.Bₛ)` resolves to it rather than to
`Algebra.TensorProduct.rightAlgebra`, and the facts stated for the latter stop matching. The
declarations below are therefore ordered so that each one only ever *references* such a fact.

## References

* [Stacks Project, Tag 0AT8](https://stacks.math.columbia.edu/tag/0AT8)
* [Stacks Project, Tag 0AT6](https://stacks.math.columbia.edu/tag/0AT6)
-/

@[expose] public section

open TensorProduct

universe u₁ u₂ u₃ u₄

/-- Transport `Algebra.IsPushout R S R' S'` along an equality of the algebra structure of `S'`
over `S`, with the scalar towers `IsScalarTower R S S'` stated for the respective structures. -/
theorem Algebra.IsPushout.of_algebra_eq {R S R' S' : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring R'] [CommSemiring S'] [Algebra R S] [Algebra R R'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S'] {i j : Algebra S S'} (hij : i = j)
    {ti : @IsScalarTower R S S' _ i.toSMul _} {tj : @IsScalarTower R S S' _ j.toSMul _}
    (h : @Algebra.IsPushout R S _ _ _ R' S' _ _ _ i _ _ _ ti) :
    @Algebra.IsPushout R S _ _ _ R' S' _ _ _ j _ _ _ tj := by
  subst hij
  exact h

namespace AlgebraicGeometry

namespace FinitelyPresentedLocalizedModuleSituation

attribute [local instance] Algebra.TensorProduct.rightAlgebra algebraBaseChange
  algebraBaseChangeOfAlgebra

variable (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
  (A' : Type u₁) [CommRing A'] [Algebra X.A A']

/-- The base ring of the base-changed situation is an algebra over the original base ring. This
is `Algebra X.A A'` itself, named at the `X.baseChange A'` spelling. -/
@[instance_reducible]
noncomputable def algebraBaseChangeBase : Algebra X.A (X.baseChange A').A :=
  inferInstanceAs (Algebra X.A A')

/-- The localization of the base-changed situation is an algebra over the original base ring.
This is `Algebra X.A (A' ⊗[X.A] X.Bₛ)` itself, named at the `X.baseChange A'` spelling. -/
@[instance_reducible]
noncomputable def algebraBaseChangeBaseLocalized : Algebra X.A (X.baseChange A').Bₛ :=
  inferInstanceAs (Algebra X.A (A' ⊗[X.A] X.Bₛ))

/-- The localization of the base-changed situation is an algebra over the original localization.
This is `Algebra.TensorProduct.rightAlgebra`, named at the `X.baseChange A'` spelling. -/
@[instance_reducible]
noncomputable def algebraLocalizedBaseChangeLocalized : Algebra X.Bₛ (X.baseChange A').Bₛ :=
  inferInstanceAs (Algebra X.Bₛ (A' ⊗[X.A] X.Bₛ))

attribute [local instance] algebraBaseChangeBase algebraBaseChangeBaseLocalized
  algebraLocalizedBaseChangeLocalized

/-- The base ring reaches the localization of the base-changed situation through the original
localization. -/
theorem isScalarTower_localized_baseChange :
    IsScalarTower X.A X.Bₛ (X.baseChange A').Bₛ :=
  X.isScalarTower_baseChange_right_localization A'

attribute [local instance] isScalarTower_localized_baseChange

/-- The structure map from the base ring of the base-changed situation to its localization sends
`a` to `a ⊗ₜ 1`. -/
theorem algebraMap_baseChange_localized (a : A') :
    algebraMap (X.baseChange A').A (X.baseChange A').Bₛ a = a ⊗ₜ[X.A] (1 : X.Bₛ) := by
  show (X.baseChangeAlgHom A') (algebraMap A' (A' ⊗[X.A] X.B) a) = _
  simp [baseChangeAlgHom, Algebra.TensorProduct.algebraMap_apply]

/-- The original base ring reaches the localization of the base-changed situation through the
base ring of the base-changed situation. -/
theorem isScalarTower_baseChange_base_localized :
    IsScalarTower X.A (X.baseChange A').A (X.baseChange A').Bₛ :=
  IsScalarTower.of_algebraMap_eq fun x =>
    (X.algebraMap_baseChange_localized A' (algebraMap X.A (X.baseChange A').A x)).symm

/-- The algebra structure that the base-changed situation derives on its localization over its
base ring is the tensor product's own left algebra structure. The two are not definitionally
equal — the former multiplies by the image of the scalar, the latter acts on the left factor —
but they have the same `algebraMap`. -/
theorem algebraLocalized_baseChange_eq :
    (FinitelyPresentedLocalizedModuleSituation.algebraLocalized (X.baseChange A')) =
      (Algebra.TensorProduct.leftAlgebra : Algebra A' (A' ⊗[X.A] X.Bₛ)) :=
  Algebra.algebra_ext _ _ fun a =>
    (X.algebraMap_baseChange_localized A' a).trans
      (Algebra.TensorProduct.algebraMap_apply (S := A') a).symm

attribute [local instance] isScalarTower_baseChange_base_localized

/-- The localization of the base-changed situation is the base change of the original
localization, for the algebra structure the base-changed situation itself derives. -/
theorem isPushout_baseChange_base_localized :
    Algebra.IsPushout X.A (X.baseChange A').A X.Bₛ (X.baseChange A').Bₛ :=
  Algebra.IsPushout.of_algebra_eq (S' := (X.baseChange A').Bₛ)
    (X.algebraLocalized_baseChange_eq A').symm (X.isPushout_baseChange_localization A')

variable (p : Ideal X.A) [p.IsPrime] (I : Ideal (Localization.AtPrime p))

/-- The base change of the situation of Stacks 0AT6 to a quotient of a local ring of the base, as
a `LocalQuotientBaseChange`.

Untagged: this is the base-change half of Stacks 0AT8, whose conclusion also asserts the
existence of a pure spreadout. -/
noncomputable def localQuotientBaseChange :
    LocalQuotientBaseChange X (X.baseChange (Localization.AtPrime p ⧸ I)) p I where
  algebraBase := X.algebraBaseChangeBase (Localization.AtPrime p ⧸ I)
  baseEquiv := RingEquiv.refl _
  baseEquiv_algebraMap _ := rfl
  algebraB := inferInstanceAs
    (Algebra X.B ((Localization.AtPrime p ⧸ I) ⊗[X.A] X.B))
  algebraAB' := inferInstanceAs
    (Algebra X.A ((Localization.AtPrime p ⧸ I) ⊗[X.A] X.B))
  towerAB := X.isScalarTower_baseChange_right (Localization.AtPrime p ⧸ I)
  towerBaseB := inferInstanceAs
    (IsScalarTower X.A (Localization.AtPrime p ⧸ I)
      ((Localization.AtPrime p ⧸ I) ⊗[X.A] X.B))
  algebraPushout := inferInstanceAs
    (Algebra.IsPushout X.A (Localization.AtPrime p ⧸ I) X.B
      ((Localization.AtPrime p ⧸ I) ⊗[X.A] X.B))
  algebraLocalized := X.algebraLocalizedBaseChangeLocalized (Localization.AtPrime p ⧸ I)
  algebraALocalized := X.algebraBaseChangeBaseLocalized (Localization.AtPrime p ⧸ I)
  towerALocalized := X.isScalarTower_localized_baseChange (Localization.AtPrime p ⧸ I)
  towerBaseLocalized := X.isScalarTower_baseChange_base_localized (Localization.AtPrime p ⧸ I)
  localizedPushout := X.isPushout_baseChange_base_localized (Localization.AtPrime p ⧸ I)
  algebraBLocalized := X.algebraBaseChangeOfAlgebra (Localization.AtPrime p ⧸ I)
  towerBLocalized := X.isScalarTower_baseChange_of_localization (Localization.AtPrime p ⧸ I)
  towerBBaseLocalized := X.isScalarTower_baseChange_algebra (Localization.AtPrime p ⧸ I)
  localization_commutes _ := rfl
  submonoid_eq_map := rfl
  moduleLocalized := inferInstanceAs
    (Module X.Bₛ (((Localization.AtPrime p ⧸ I) ⊗[X.A] X.Bₛ) ⊗[X.Bₛ] X.N))
  towerLocalizedModule := inferInstanceAs
    (IsScalarTower X.Bₛ ((Localization.AtPrime p ⧸ I) ⊗[X.A] X.Bₛ)
      (((Localization.AtPrime p ⧸ I) ⊗[X.A] X.Bₛ) ⊗[X.Bₛ] X.N))
  moduleMap := TensorProduct.mk X.Bₛ ((Localization.AtPrime p ⧸ I) ⊗[X.A] X.Bₛ) X.N 1
  moduleMap_algebra b n := by
    change (1 : (Localization.AtPrime p ⧸ I) ⊗[X.A] X.Bₛ) ⊗ₜ[X.Bₛ]
      ((algebraMap X.B X.Bₛ b) • n) = _
    rw [← TensorProduct.smul_tmul]
    rfl
  moduleBaseChange :=
    TensorProduct.isBaseChange X.Bₛ X.N ((Localization.AtPrime p ⧸ I) ⊗[X.A] X.Bₛ)

end FinitelyPresentedLocalizedModuleSituation

end AlgebraicGeometry

end
