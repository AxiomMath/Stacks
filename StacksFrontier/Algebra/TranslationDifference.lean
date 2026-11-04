module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Logic.Function.Defs

/-!
# A base-point-free difference makes two simply transitive actions compatible

Let `A₁` and `A₂` be abelian groups acting on sets `L₁` and `L₂`, each action presented by a
single map `t₁ : A₁ → L₁`, `t₂ : A₂ → L₂` — "translate a fixed base point" — and let
`resA : A₁ → A₂`, `resL : L₁ → L₂` be two maps, thought of as the restriction of the acting
group and of the acted-on set along a morphism of the index.

Suppose given, on each side, a *difference* `D₁ : L₁ → L₁ → A₁`, `D₂ : L₂ → L₂ → A₂` which
recovers the acting element from a pair of translates, and which commutes with the restriction.
Then the two presentations are compatible: a translate of the first whose restriction is a
translate of the second stays so after both are translated further by one and the same element.

## Main results

* `Stacks.eq_translate_add_of_difference`: the compatibility, from the two difference identities,
  the naturality of the difference and the surjectivity of the second presentation.
* `Stacks.eq_of_difference_translate`: a difference which is a subtraction after an additive
  injection recovers the acting element from a pair of translates at an arbitrary base point.

## Implementation notes

**The difference identity is asked for at an arbitrary translate, not only at the base point.**
The hypotheses `ht₁` and `ht₂` say `D (t η) (t (θ + η)) = θ` for *all* `η`, where the statement
"the difference recovers the acting element" would be the case `η = 0`, `D (t 0) (t θ) = θ`.
The two are not interchangeable here: the conclusion compares translates of two *different*
base points — `resL (t₁ η)` on one side and `t₂ ζ` on the other — and the case `η = 0` alone
gives no handle on a difference whose first argument is not a base point.  Granted that the
family of presentations is closed under moving the base point along the action, the general case
follows from the case `η = 0` applied to the moved presentation; that closure is not assumed
here, and the general form is asked for instead.

**No additivity of `resA` is needed**, and no injectivity of `t₂`.
-/

@[expose] public section

namespace Stacks

/-- **A restriction-natural difference makes two simply transitive actions compatible.**

`t₁` and `t₂` present two actions — of the abelian group `A₁` on `L₁` and of `A₂` on `L₂` — by
their effect on a base point, `resA` and `resL` restrict the acting group and the acted-on set,
and `D₁`, `D₂` are differences recovering the acting element from a pair of translates (`ht₁`,
`ht₂`) and commuting with the restriction (`hnat`).  Granted that the second presentation is
surjective, a translate `t₁ η` whose restriction is the translate `t₂ ζ` has the property that
translating further by `θ` on the left and by `resA θ` on the right again gives a restriction
and a translate which agree.

The hypotheses mention no structure beyond the two abelian groups: in particular `resA` is an
arbitrary map, and `t₂` is not assumed injective. -/
public theorem eq_translate_add_of_difference {A₁ A₂ L₁ L₂ : Type*} [AddCommGroup A₁]
    [AddCommGroup A₂] {resA : A₁ → A₂} {resL : L₁ → L₂} {t₁ : A₁ → L₁} {t₂ : A₂ → L₂}
    {D₁ : L₁ → L₁ → A₁} {D₂ : L₂ → L₂ → A₂}
    (ht₁ : ∀ θ η : A₁, D₁ (t₁ η) (t₁ (θ + η)) = θ)
    (ht₂ : ∀ θ η : A₂, D₂ (t₂ η) (t₂ (θ + η)) = θ)
    (hnat : ∀ x y : L₁, D₂ (resL x) (resL y) = resA (D₁ x y))
    (ht₂surj : Function.Surjective t₂) {θ η : A₁} {ζ : A₂} (h : resL (t₁ η) = t₂ ζ) :
    resL (t₁ (θ + η)) = t₂ (resA θ + ζ) := by
  obtain ⟨ξ, hξ⟩ := ht₂surj (resL (t₁ (θ + η)))
  have key : D₂ (t₂ ζ) (t₂ ξ) = resA θ := by
    rw [← h, hξ, hnat, ht₁]
  have hsub : D₂ (t₂ ζ) (t₂ ξ) = ξ - ζ := by
    have h₂ := ht₂ (ξ - ζ) ζ
    rwa [show ξ - ζ + ζ = ξ from sub_add_cancel ξ ζ] at h₂
  exact hξ.symm.trans (congrArg t₂ (sub_eq_iff_eq_add.mp (hsub.symm.trans key)))

/-- **A difference which is a subtraction after an additive injection recovers the acting element
from a pair of translates at an arbitrary base point.**

`e : A → B` is an additive injection — the identification of the acting group with the group in
which the difference is computed — `t : B → L` presents an action of `B` on `L`, and `D` is a
difference whose value at a pair of translates is, after `e`, the subtraction of the two
arguments.  Then `D` recovers `θ` from the translates by `η` and by `θ + η`, for *every* `η` and
not only for `η = 0`.

No surjectivity of `t`, no injectivity of `t`, and no additivity of `t` are used. -/
public theorem eq_of_difference_translate {A B L : Type*} [AddCommGroup A] [AddCommGroup B]
    {e : A → B} {t : B → L} {D : L → L → A} (he : ∀ x y : A, e (x + y) = e x + e y)
    (hD : ∀ σ₁ σ₂ : B, e (D (t σ₁) (t σ₂)) = σ₂ - σ₁) (hinj : Function.Injective e)
    (θ η : A) :
    D (t (e η)) (t (e (θ + η))) = θ := by
  refine hinj ?_
  rw [hD, he, add_sub_cancel_right]

end Stacks

end
