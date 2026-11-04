module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.ClosedCoverExactSequence

/-!
# The cap operation of a baby localized Chern class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, let `X` be a
scheme locally of finite type over `S` and let `X₁, X₂ ⊆ X` be closed subschemes with
`X = X₁ ∪ X₂` set theoretically. **Stacks 0F9H** constructs, from an operation on the Chow groups
of `X₂`, an operation on the Chow groups of `X` characterized by

  `c' ∩ i_{2,*} α₂ = c ∩ α₂`   and   `c' ∩ i_{1,*} α₁ = 0`.

This file is that construction and its characterization, at the level of a single degree and a
single scheme. The input `c ∩ -` is an additive map `A_k(X₂) ⟶ A_{k-p}(X₂)` which kills every
class pushed forward from the scheme-theoretic intersection `X₁ ∩ X₂`; the output `c' ∩ -` is an
additive map `A_k(X) ⟶ A_{k-p}(X₂)`.

The construction is exactly the source's. By Stacks 0F94 the sequence

  `A_k(X₁ ∩ X₂) ⟶ A_k(X₁) ⊕ A_k(X₂) ⟶ A_k(X) ⟶ 0`

is exact, so every `α ∈ A_k(X)` is `i_{1,*} α₁ + i_{2,*} α₂` and the pair `(α₁, α₂)` is unique up
to the image of the first map. The rule `(α₁, α₂) ↦ c ∩ α₂` therefore descends to `A_k(X)`
precisely when it kills that image, which — the first map being the pair of pushforwards with the
second negated — is the vanishing hypothesis on `c`. In the source that vanishing is the content
of the restriction hypothesis of Stacks 0F9H: `E₂|_{X₁ ∩ X₂}` is zero, respectively finite
locally free of rank `< p` in cohomological degree `0`, so `P_p(E₂|_{X₁ ∩ X₂}) = 0`, respectively
`c_p(E₂|_{X₁ ∩ X₂}) = 0`, and the Chern classes of Section 42.46 are bivariant, hence commute with
the pushforward along `X₁ ∩ X₂ ⟶ X₂`.

The bivariant class `c' ∈ A^p(X₂ ⟶ X)` itself, with the characterization on every base change,
is `Stacks.Chow.closedCoverLocalizedClass`
(`StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.ClosedCoverClass`), and Stacks 0F9H is
registered in `StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernClass`.

## Main definitions

* `Stacks.Chow.closedCoverPairCap` — the rule `(α₁, α₂) ↦ c ∩ α₂` on `A_k(X₁) ⊕ A_k(X₂)`.
* `Stacks.Chow.closedCoverCap` — **Stacks 0F9H, the construction**: the descended operation
  `c' ∩ - : A_k(X) ⟶ A_{k-p}(X₂)`.

## Main results

* `Stacks.Chow.closedCoverPairCap_eq_zero_of_summandsToUnionChow_eq_zero` — the well-definedness,
  from the exactness of Stacks 0F94.
* `Stacks.Chow.closedCoverCap_summandsToUnionChow` — the defining formula.
* `Stacks.Chow.closedCoverCap_pushforwardRight` — **the first characterizing identity**,
  `c' ∩ i_{2,*} α₂ = c ∩ α₂`.
* `Stacks.Chow.closedCoverCap_pushforwardLeft` — **the second characterizing identity**,
  `c' ∩ i_{1,*} α₁ = 0`.
* `Stacks.Chow.eq_of_pushforward_eq` — the surjectivity half of Stacks 0F94 as a uniqueness
  principle: two additive maps out of `A_k(X)` agreeing on both families of pushforwards are
  equal. Stated for an arbitrary target abelian group, which is what Stacks 0F9I needs.
* `Stacks.Chow.eq_closedCoverCap` — **the uniqueness clause**: the two identities determine the
  operation. This is what "canonical" rests on.

## Implementation notes

The two closed subschemes are given as ideal sheaf data `I` and `J` on `X`, so that their
scheme-theoretic intersection is cut out by `I ⊔ J`; this is the form in which Stacks 0F94 is
available here (`StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.ClosedCoverExactSequence`),
and the set-theoretic covering hypothesis reads `I.support ⊔ J.support = ⊤`.

All four pushforwards are along the inclusion of a closed subscheme, so they are the
unconditional `Stacks.Chow.chowPushforwardOfIsClosedImmersion` and no instance of Stacks 02S2
enters any statement below.

The descent is through `QuotientAddGroup.quotientKerEquivOfSurjective` for the surjection of
Stacks 0F94 rather than through a choice of preimage: the result is an `AddMonoidHom` by
construction, which is what the cap operation of a bivariant class must be.

The degree shift `p` is an arbitrary integer here. Nothing below uses `p ≥ 0`, and the source's
`p` enters only through the rank bound in the hypothesis that makes `c` kill the classes pushed
forward from the intersection — a hypothesis, not a conclusion, at this level.

## References

* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F94](https://stacks.math.columbia.edu/tag/0F94)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

open Scheme.IdealSheafData (inclusion inclusion_subschemeι_assoc)

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (I J : X.IdealSheafData) (k p : ℤ)

/-! ### The pushforward from the intersection -/

/-- Pushforward `A_k(X₁ ∩ X₂) ⟶ A_k(X₂)` along the inclusion of the scheme-theoretic
intersection into the second closed subscheme. This is the map whose image the input operation of
Stacks 0F9H must kill. -/
abbrev intersectionChowPushforwardRight :
    chowGroup C ((I ⊔ J).subschemeι ≫ sX) k →+ chowGroup C (J.subschemeι ≫ sX) k :=
  chowPushforwardOfIsClosedImmersion C ((I ⊔ J).subschemeι ≫ sX) (J.subschemeι ≫ sX)
    (inclusion (le_sup_right : J ≤ I ⊔ J))
    (inclusion_subschemeι_assoc (le_sup_right : J ≤ I ⊔ J) sX) k

/-! ### The rule on the direct sum -/

/-- The rule `(α₁, α₂) ↦ c ∩ α₂` on `A_k(X₁) ⊕ A_k(X₂)`, whose descent along the surjection of
Stacks 0F94 is the cap operation of Stacks 0F9H. -/
def closedCoverPairCap
    (op : chowGroup C (J.subschemeι ≫ sX) k →+ chowGroup C (J.subschemeι ≫ sX) (k - p)) :
    chowGroup C (I.subschemeι ≫ sX) k × chowGroup C (J.subschemeι ≫ sX) k →+
      chowGroup C (J.subschemeι ≫ sX) (k - p) :=
  op.comp (AddMonoidHom.snd _ _)

/-- `closedCoverPairCap C sX I J k p op` sends a pair `(α₁, α₂)` to `op α₂`. -/
@[simp]
theorem closedCoverPairCap_apply
    (op : chowGroup C (J.subschemeι ≫ sX) k →+ chowGroup C (J.subschemeι ≫ sX) (k - p))
    (x : chowGroup C (I.subschemeι ≫ sX) k × chowGroup C (J.subschemeι ≫ sX) k) :
    closedCoverPairCap C sX I J k p op x = op x.2 :=
  rfl

/-- **Well-definedness, from the exactness half of Stacks 0F94.** If the input operation kills
every class pushed forward from the scheme-theoretic intersection, then the rule
`(α₁, α₂) ↦ c ∩ α₂` kills every pair whose two pushforwards to `X` cancel.

Such a pair is, by Stacks 0F94, the image of a class `γ` on `X₁ ∩ X₂`, so its second component is
minus the pushforward of `γ` to `X₂`. -/
theorem closedCoverPairCap_eq_zero_of_summandsToUnionChow_eq_zero
    (hcover : I.support ⊔ J.support = ⊤)
    (op : chowGroup C (J.subschemeι ≫ sX) k →+ chowGroup C (J.subschemeι ≫ sX) (k - p))
    (hvanish : ∀ γ : chowGroup C ((I ⊔ J).subschemeι ≫ sX) k,
      op (intersectionChowPushforwardRight C sX I J k γ) = 0)
    (x : chowGroup C (I.subschemeι ≫ sX) k × chowGroup C (J.subschemeι ≫ sX) k)
    (hx : summandsToUnionChow C sX I J k x = 0) :
    closedCoverPairCap C sX I J k p op x = 0 := by
  obtain ⟨γ, rfl⟩ :=
    (exact_intersectionToSummandsChow_summandsToUnionChow C sX I J k hcover x).mp hx
  have hsnd : (intersectionToSummandsChow C sX I J k γ).2 =
      -intersectionChowPushforwardRight C sX I J k γ := rfl
  rw [closedCoverPairCap_apply, hsnd, map_neg, hvanish, neg_zero]

/-! ### The construction -/

/-- **Stacks 0F9H, the construction of the cap operation.** Given an additive operation
`c ∩ - : A_k(X₂) ⟶ A_{k-p}(X₂)` killing every class pushed forward from `X₁ ∩ X₂`, the operation

  `c' ∩ - : A_k(X) ⟶ A_{k-p}(X₂)`

obtained by writing a class on `X` as `i_{1,*} α₁ + i_{2,*} α₂` and returning `c ∩ α₂`.

This is a definition with a real body: the descent is along the surjection with known kernel that
Stacks 0F94 provides, so no class is chosen from an existence statement. -/
def closedCoverCap (hcover : I.support ⊔ J.support = ⊤)
    (op : chowGroup C (J.subschemeι ≫ sX) k →+ chowGroup C (J.subschemeι ≫ sX) (k - p))
    (hvanish : ∀ γ : chowGroup C ((I ⊔ J).subschemeι ≫ sX) k,
      op (intersectionChowPushforwardRight C sX I J k γ) = 0) :
    chowGroup C sX k →+ chowGroup C (J.subschemeι ≫ sX) (k - p) :=
  (QuotientAddGroup.lift (summandsToUnionChow C sX I J k).ker
      (closedCoverPairCap C sX I J k p op)
      fun x hx ↦ closedCoverPairCap_eq_zero_of_summandsToUnionChow_eq_zero C sX I J k p hcover
        op hvanish x hx).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective (summandsToUnionChow C sX I J k)
      (surjective_summandsToUnionChow C sX I J k hcover)).symm.toAddMonoidHom

/-- **The defining formula of Stacks 0F9H.** On a class presented as `i_{1,*} α₁ + i_{2,*} α₂`,
the constructed operation returns `c ∩ α₂`. -/
theorem closedCoverCap_summandsToUnionChow (hcover : I.support ⊔ J.support = ⊤)
    (op : chowGroup C (J.subschemeι ≫ sX) k →+ chowGroup C (J.subschemeι ≫ sX) (k - p))
    (hvanish : ∀ γ : chowGroup C ((I ⊔ J).subschemeι ≫ sX) k,
      op (intersectionChowPushforwardRight C sX I J k γ) = 0)
    (x : chowGroup C (I.subschemeι ≫ sX) k × chowGroup C (J.subschemeι ≫ sX) k) :
    closedCoverCap C sX I J k p hcover op hvanish (summandsToUnionChow C sX I J k x) = op x.2 := by
  have hsymm :
      (QuotientAddGroup.quotientKerEquivOfSurjective (summandsToUnionChow C sX I J k)
          (surjective_summandsToUnionChow C sX I J k hcover)).symm
        (summandsToUnionChow C sX I J k x) =
      QuotientAddGroup.mk' (summandsToUnionChow C sX I J k).ker x := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  unfold closedCoverCap
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hsymm]
  rfl

/-- `summandsToUnionChow` sends `(a, b)` to the sum of the two pushforwards to `X`. -/
private theorem summandsToUnionChow_apply
    (x : chowGroup C (I.subschemeι ≫ sX) k × chowGroup C (J.subschemeι ≫ sX) k) :
    summandsToUnionChow C sX I J k x =
      chowPushforwardOfIsClosedImmersion C (I.subschemeι ≫ sX) sX I.subschemeι rfl k x.1 +
        chowPushforwardOfIsClosedImmersion C (J.subschemeι ≫ sX) sX J.subschemeι rfl k x.2 :=
  rfl

/-- **Stacks 0F9H, the first characterizing identity.** On a class pushed forward from the second
closed subscheme the constructed operation is the input operation: `c' ∩ i_{2,*} α₂ = c ∩ α₂`. -/
theorem closedCoverCap_pushforwardRight (hcover : I.support ⊔ J.support = ⊤)
    (op : chowGroup C (J.subschemeι ≫ sX) k →+ chowGroup C (J.subschemeι ≫ sX) (k - p))
    (hvanish : ∀ γ : chowGroup C ((I ⊔ J).subschemeι ≫ sX) k,
      op (intersectionChowPushforwardRight C sX I J k γ) = 0)
    (α : chowGroup C (J.subschemeι ≫ sX) k) :
    closedCoverCap C sX I J k p hcover op hvanish
        (chowPushforwardOfIsClosedImmersion C (J.subschemeι ≫ sX) sX J.subschemeι rfl k α) =
      op α := by
  have := closedCoverCap_summandsToUnionChow C sX I J k p hcover op hvanish (0, α)
  rwa [summandsToUnionChow_apply, map_zero, zero_add] at this

/-- **Stacks 0F9H, the second characterizing identity.** The constructed operation kills every
class pushed forward from the first closed subscheme: `c' ∩ i_{1,*} α₁ = 0`. -/
theorem closedCoverCap_pushforwardLeft (hcover : I.support ⊔ J.support = ⊤)
    (op : chowGroup C (J.subschemeι ≫ sX) k →+ chowGroup C (J.subschemeι ≫ sX) (k - p))
    (hvanish : ∀ γ : chowGroup C ((I ⊔ J).subschemeι ≫ sX) k,
      op (intersectionChowPushforwardRight C sX I J k γ) = 0)
    (α : chowGroup C (I.subschemeι ≫ sX) k) :
    closedCoverCap C sX I J k p hcover op hvanish
        (chowPushforwardOfIsClosedImmersion C (I.subschemeι ≫ sX) sX I.subschemeι rfl k α) = 0 := by
  have := closedCoverCap_summandsToUnionChow C sX I J k p hcover op hvanish (α, 0)
  rw [summandsToUnionChow_apply, map_zero, add_zero] at this
  exact this.trans (map_zero op)

/-! ### Uniqueness -/

/-- **The surjectivity half of Stacks 0F94, as a uniqueness principle.** Two additive maps out of
`A_k(X)` that agree on the classes pushed forward from `X₁` and on those pushed forward from `X₂`
are equal, because every class on `X` is a sum of two such.

Stated for an arbitrary target abelian group: this is used below with target `A_{k-p}(X₂)` for the
uniqueness clause of Stacks 0F9H, and with target `A_{k-p}(X)` for Stacks 0F9I. -/
theorem eq_of_pushforward_eq {M : Type*} [AddCommGroup M] (hcover : I.support ⊔ J.support = ⊤)
    (F G : chowGroup C sX k →+ M)
    (hleft : ∀ α : chowGroup C (I.subschemeι ≫ sX) k,
      F (chowPushforwardOfIsClosedImmersion C (I.subschemeι ≫ sX) sX I.subschemeι rfl k α) =
        G (chowPushforwardOfIsClosedImmersion C (I.subschemeι ≫ sX) sX I.subschemeι rfl k α))
    (hright : ∀ α : chowGroup C (J.subschemeι ≫ sX) k,
      F (chowPushforwardOfIsClosedImmersion C (J.subschemeι ≫ sX) sX J.subschemeι rfl k α) =
        G (chowPushforwardOfIsClosedImmersion C (J.subschemeι ≫ sX) sX J.subschemeι rfl k α)) :
    F = G := by
  refine AddMonoidHom.ext fun α ↦ ?_
  obtain ⟨⟨a, b⟩, rfl⟩ := surjective_summandsToUnionChow C sX I J k hcover α
  rw [summandsToUnionChow_apply, map_add, map_add, hleft, hright]

/-- **The uniqueness clause of Stacks 0F9H, on cap operations.** An additive operation
`A_k(X) ⟶ A_{k-p}(X₂)` satisfying the two characterizing identities is unique, and so equals the
operation constructed above: by the surjectivity half of Stacks 0F94 every class on `X` is a sum
of two pushforwards, and the two identities prescribe the value on each summand.

This is the statement that `c'` is *canonical*. -/
theorem eq_closedCoverCap (hcover : I.support ⊔ J.support = ⊤)
    (op : chowGroup C (J.subschemeι ≫ sX) k →+ chowGroup C (J.subschemeι ≫ sX) (k - p))
    (hvanish : ∀ γ : chowGroup C ((I ⊔ J).subschemeι ≫ sX) k,
      op (intersectionChowPushforwardRight C sX I J k γ) = 0)
    (F : chowGroup C sX k →+ chowGroup C (J.subschemeι ≫ sX) (k - p))
    (hFright : ∀ α : chowGroup C (J.subschemeι ≫ sX) k,
      F (chowPushforwardOfIsClosedImmersion C (J.subschemeι ≫ sX) sX J.subschemeι rfl k α) =
        op α)
    (hFleft : ∀ α : chowGroup C (I.subschemeι ≫ sX) k,
      F (chowPushforwardOfIsClosedImmersion C (I.subschemeι ≫ sX) sX I.subschemeι rfl k α) = 0) :
    F = closedCoverCap C sX I J k p hcover op hvanish :=
  eq_of_pushforward_eq C sX I J k hcover F _
    (fun α ↦ by rw [hFleft, closedCoverCap_pushforwardLeft])
    (fun α ↦ by rw [hFright, closedCoverCap_pushforwardRight])

end Stacks.Chow

end
