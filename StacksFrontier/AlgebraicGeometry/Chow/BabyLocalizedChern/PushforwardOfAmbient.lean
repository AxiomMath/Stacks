module

public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.ClosedCoverCap

/-!
# An operation killing `X₁` factors through the localized cap operation

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, let `X` be a
scheme locally of finite type over `S` and let `X₁, X₂ ⊆ X` be closed subschemes with
`X = X₁ ∪ X₂` set theoretically. An operation `opX` on `A_k(X)` which kills every class pushed
forward from `X₁` and which commutes with pushforward along `i₂ : X₂ ⟶ X` with an operation `op`
on `A_k(X₂)` is `i_{2,*}` composed with the cap operation the construction of Stacks 0F9H
produces from `op`. By the surjectivity half of Stacks 0F94 the two agree on every class of `X`.

This is the computation in the proof of Stacks 0F9I, on the cap operation of a single degree over
a single scheme; the bivariant statement of Stacks 0F9I is
`Stacks.Chow.pushforward_localizedPowerSumOfClosedCover` and
`Stacks.Chow.pushforward_localizedChernClassOfClosedCover`.

## Main results

* `Stacks.Chow.pushforward_closedCoverCap_eq` — `opX = i_{2,*} ∘ (c' ∩ -)`.

## References

* [Stacks Project, Tag 0F9I](https://stacks.math.columbia.edu/tag/0F9I)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F94](https://stacks.math.columbia.edu/tag/0F94)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (I J : X.IdealSheafData) (k p : ℤ)

/-- **An operation killing `X₁` factors through the localized cap operation.** Let `opX` be an
operation on `A_k(X)` which kills every class pushed forward from `X₁` and which satisfies
`opX ∘ i_{2,*} = i_{2,*} ∘ op` for an operation `op` on `A_k(X₂)` vanishing on the classes pushed
forward from `X₁ ∩ X₂`. Then `opX = i_{2,*} ∘ (c' ∩ -)`, the operation on the right being the one
the construction of Stacks 0F9H produces from `op`. -/
theorem pushforward_closedCoverCap_eq (hcover : I.support ⊔ J.support = ⊤)
    (opX : chowGroup C sX k →+ chowGroup C sX (k - p))
    (op : chowGroup C (J.subschemeι ≫ sX) k →+ chowGroup C (J.subschemeι ≫ sX) (k - p))
    (hleft : ∀ α : chowGroup C (I.subschemeι ≫ sX) k,
      opX (chowPushforwardOfIsClosedImmersion C (I.subschemeι ≫ sX) sX I.subschemeι rfl k α) = 0)
    (hright : ∀ α : chowGroup C (J.subschemeι ≫ sX) k,
      opX (chowPushforwardOfIsClosedImmersion C (J.subschemeι ≫ sX) sX J.subschemeι rfl k α) =
        chowPushforwardOfIsClosedImmersion C (J.subschemeι ≫ sX) sX J.subschemeι rfl (k - p)
          (op α))
    (hvanish : ∀ γ : chowGroup C ((I ⊔ J).subschemeι ≫ sX) k,
      op (intersectionChowPushforwardRight C sX I J k γ) = 0) :
    opX = (chowPushforwardOfIsClosedImmersion C (J.subschemeι ≫ sX) sX J.subschemeι
        rfl (k - p)).comp (closedCoverCap C sX I J k p hcover op hvanish) :=
  eq_of_pushforward_eq C sX I J k hcover opX _
    (fun α ↦ by
      rw [hleft, AddMonoidHom.comp_apply, closedCoverCap_pushforwardLeft, map_zero])
    (fun α ↦ by
      rw [hright, AddMonoidHom.comp_apply, closedCoverCap_pushforwardRight])

end Stacks.Chow

end
