module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleChow
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionGysinRetraction

/-!
# Flat pullback along a line bundle is injective, with nothing assumed

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `ℒ` be an invertible `𝒪_X`-module and let
`p : L = \underline{\Spec}(\Sym^*(ℒ)) ⟶ X` be the associated line bundle. [Stacks, Tag 0B74]
says that `p^* : A_k(X) ⟶ A_{k+1}(L)` is an isomorphism; its injectivity half is the source's
zero-section argument, `o^* ∘ p^* = (p ∘ o)^* = 𝟙^* = \mathrm{id}`.

`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleChow` proves that half from the
retraction `o^* ∘ p^* = \mathrm{id}` carried as the hypothesis `h02TR` together with the Gysin
map `o^*` carried as the datum `gysin` — [Stacks, Tag 02TR] on Chow groups. Both are now
theorems: `Stacks.Chow.zeroSectionGysinChow` is the Gysin map of the zero section and
`Stacks.Chow.zeroSectionGysinChow_flatPullbackChowOfRelativeDimension` is the retraction, clause
(4) of [Stacks, Tag 0F96], proved unconditionally in
`…Chow.AffineBundle.ZeroSectionGysinRetraction`. This file supplies them and records the
injectivity with nothing assumed.

## Main definitions

* `Stacks.Chow.zeroSectionGysinChowRetraction` — the Gysin map of the zero section, in the degree
  normalization `A_{k+(1:ℕ)}(L) ⟶ A_{k+(0:ℕ)}(X)` that
  `Stacks.Chow.GysinRetractsFlatPullbackChow` is stated at.

## Main results

* `Stacks.Chow.gysinRetractsFlatPullbackChow_zeroSectionGysinChowRetraction` — **[Stacks, Tag
  02TR] on Chow groups for the zero section of a line bundle**, discharged.
* `Stacks.Chow.flatPullbackChow_totalSpaceToBase_injective` — **[Stacks, Tag 0B74], the
  injectivity half, with nothing assumed.** The full tag is
  `Stacks.Chow.flatPullbackChow_totalSpaceToBase_bijective` of
  `StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleChowBijective`.

## Implementation notes

The two degree normalizations in play are `A_{k+1}` — what the Gysin map of
`Stacks.Chow.zeroSectionGysinChow` produces — and `A_{k+((1 : ℕ) : ℤ)}`, what flat pullback at
relative dimension `1` produces. These are the same type: `((1 : ℕ) : ℤ)` is `Int.ofNat 1`, which
is `(1 : ℤ)`, so no transport is needed on the source of
`Stacks.Chow.zeroSectionGysinChowRetraction` and the composite typechecks as it stands. The target
needs one, `A_k(X) = A_{k+((0 : ℕ) : ℤ)}(X)`, because `k + 0 = k` is not an identity of terms for
a variable `k`; it is `Stacks.Chow.chowGroupCast`, which is also the transport
`Stacks.Chow.flatPullbackChow_id` states the pullback along `𝟙 X` through, so the two sides of the
retraction meet at the same cast.

The hypotheses `hp` of relative dimension one and `hfac` of [Stacks, Tag 02S1] are kept as
arguments rather than replaced by `Stacks.LineBundle.Situation.relativeDimension_totalSpaceToBase`
and the general descent. Both are `Prop`s not occurring in the type of `flatPullbackChow`, so by
proof irrelevance the statement here is about the same map as clause (4) of [Stacks, Tag 0F96] is;
keeping them is what lets a consumer which has already fixed such proofs apply this directly.

## References

* [Stacks Project, Tag 0B74](https://stacks.math.columbia.edu/tag/0B74)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

attribute [local instance] Stacks.LineBundle.Situation.flat_totalSpaceToBase

variable (C : ChowSituation.{u}) (D : Stacks.LineBundle.Situation.{u}) (sX : D.X ⟶ C.S)
  [LocallyOfFiniteType sX]

/-- **The Gysin map of the zero section of a line bundle**, in the degree normalization
`A_{k+(1 : ℕ)}(L) ⟶ A_{k+(0 : ℕ)}(X)` that `Stacks.Chow.GysinRetractsFlatPullbackChow` is stated
at. This is `Stacks.Chow.zeroSectionGysinChow` followed by the transport
`A_k(X) = A_{k+((0 : ℕ) : ℤ)}(X)`; see the implementation notes for why the source needs no
transport. -/
def zeroSectionGysinChowRetraction (k : ℤ) :
    chowGroup C (D.totalSpaceToBase ≫ sX) (k + ((1 : ℕ) : ℤ)) →+
      chowGroup C sX (k + ((0 : ℕ) : ℤ)) :=
  (chowGroupCast C sX (show k = k + ((0 : ℕ) : ℤ) from by simp)).toAddMonoidHom.comp
    (zeroSectionGysinChow C D sX k)

/-- **[Stacks, Tag 02TR] on Chow groups for the zero section of a line bundle.** The Gysin map
`o^*` of the zero section retracts the flat pullback `p^*`:

  `o^*(p^* α) = 𝟙^* α`  in  `A_{k+0}(X)`  for every  `α ∈ A_k(X)`.

This is the hypothesis `h02TR` of
`Stacks.Chow.flatPullbackChow_injective_of_gysinRetracts`, discharged: the left-hand side is
clause (4) of [Stacks, Tag 0F96],
`Stacks.Chow.zeroSectionGysinChow_flatPullbackChowOfRelativeDimension`, and the right-hand side is
`Stacks.Chow.flatPullbackChow_id`, both landing on the same transport
`A_k(X) = A_{k+((0 : ℕ) : ℤ)}(X)`. -/
theorem gysinRetractsFlatPullbackChow_zeroSectionGysinChowRetraction
    (hp : AlgebraicGeometry.RelativeDimension D.totalSpaceToBase 1) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C (D.totalSpaceToBase ≫ sX) sX
      D.totalSpaceToBase rfl 1 hp k) :
    GysinRetractsFlatPullbackChow C sX (D.totalSpaceToBase ≫ sX) sX D.totalSpaceToBase rfl hp
      (𝟙 D.X) (Category.id_comp sX) (relativeDimension_identity D.X) k hfac
      (flatPullbackFactorsThroughRationalEquivalence_id C sX k)
      (zeroSectionGysinChowRetraction C D sX k) := by
  intro α
  rw [flatPullbackChow_id]
  exact congrArg (chowGroupCast C sX (show k = k + ((0 : ℕ) : ℤ) from by simp))
    (zeroSectionGysinChow_flatPullbackChowOfRelativeDimension C D sX k α)

/-- **[Stacks, Tag 0B74], the injectivity half, with nothing assumed.** Let `(S, δ)` be as in
Situation 02QL, let `X` be locally of finite type over `S`, let `ℒ` be an invertible `𝒪_X`-module
and let `p : L = \underline{\Spec}(\Sym^*(ℒ)) ⟶ X` be the associated line bundle. Then

  `p^* : A_k(X) ⟶ A_{k+1}(L)`

is injective for every `k`.

This is `Stacks.Chow.flatPullbackChow_injective_of_gysinRetracts` with its two carried inputs —
the Gysin map of the zero section and [Stacks, Tag 02TR] on Chow groups — supplied from
`Stacks.Chow.zeroSectionGysinChowRetraction` and
`Stacks.Chow.gysinRetractsFlatPullbackChow_zeroSectionGysinChowRetraction`. -/
theorem flatPullbackChow_totalSpaceToBase_injective
    (hp : AlgebraicGeometry.RelativeDimension D.totalSpaceToBase 1) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C (D.totalSpaceToBase ≫ sX) sX
      D.totalSpaceToBase rfl 1 hp k) :
    Function.Injective
      (flatPullbackChow C (D.totalSpaceToBase ≫ sX) sX D.totalSpaceToBase rfl 1 hp k hfac) :=
  flatPullbackChow_injective_of_gysinRetracts C D sX hp k hfac
    (zeroSectionGysinChowRetraction C D sX k)
    (gysinRetractsFlatPullbackChow_zeroSectionGysinChowRetraction C D sX hp k hfac)

end Stacks.Chow

end
