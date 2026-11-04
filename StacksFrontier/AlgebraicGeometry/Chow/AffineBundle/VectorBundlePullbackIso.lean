module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat pullback along a vector bundle projection

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `ℰ` be a finite locally free sheaf of rank `r` on `X` and let
`p : E = Spec(Sym^*(ℰ)) ⟶ X` be the associated vector bundle. Stacks 02TY asserts that

  `p^* : CH_k(X) ⟶ CH_{k+r}(E)`

is an isomorphism for every `k`, that is, that `p^*` is both injective and surjective.

This file proves the rank-zero case of that assertion, in both directions at once. A rank-zero
vector bundle projection is an isomorphism of schemes, and the flat pullback of an isomorphism in
relative dimension zero is the restriction map of Stacks 02RC, which is proper pushforward along
the inverse isomorphism and hence bijective.

## Main results

* `Stacks.Chow.flatPullbackChow_bijective_of_isIso` — flat pullback on Chow groups along an
  isomorphism over the base, in relative dimension zero, is bijective.
* `Stacks.Chow.flatPullbackChow_bijective_of_isAffineSpaceBundle_zero` — **Stacks 02TY in rank
  zero**: for a bundle projection of rank zero, `p^* : CH_k(X) ⟶ CH_{k+0}(E)` is bijective.

## Implementation notes

The vector bundle `E = Spec(Sym^*(ℰ))` of a finite locally free sheaf is not available to the
Chow development of this repository: nothing under `StacksFrontier/AlgebraicGeometry/Chow/`
constructs the relative spectrum of a sheaf of algebras, and the vector bundles of
`StacksFrontier.AlgebraicGeometry.Constructions.VectorBundle` are not connected to Chow groups. The
bundle projection is therefore carried in the shape the neighbouring file uses for Stacks 02TT,
namely `Stacks.Chow.IsAffineSpaceBundle p r`: every point of `X` has an open neighbourhood over
which `p` is the projection `𝔸^r_U ⟶ U`. A rank-`r` vector bundle projection has that property,
so the statement proved here is a generalisation of the rank-zero case of Stacks 02TY and not a
weakening of it.

The degree of the flat pullback of a `k`-class in relative dimension zero is `k + 0` rather than
`k`, so the two maps being compared have different — though equal — degrees. The comparison is
made by generalising the degree to a variable and substituting, which is the technique of
`Stacks.Chow.heq_chowGroupRestrict_flatPullbackChow`; that lemma itself is not used, as importing
it would pull in the whole bivariant disjoint-decomposition development for one transport.

What blocks the ranks `r ≥ 1` is recorded in the docstring of
`Stacks.Chow.flatPullbackChow_bijective_of_isAffineSpaceBundle_zero`.

## References

* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02RC](https://stacks.math.columbia.edu/tag/02RC)
* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Flat pullback along an isomorphism -/

/-- **Flat pullback on Chow groups along an isomorphism over the base, in relative dimension
zero, is bijective.**

Such a pullback is the restriction map of Stacks 02RC, which by
`Stacks.Chow.chowGroupRestrict_of_isIso` is proper pushforward along the inverse isomorphism and
so is bijective by Stacks 0GU8. The two maps have degrees `k` and `k + 0`; they are compared by
generalising the degree of the target to a variable and substituting. -/
theorem flatPullbackChow_bijective_of_isIso (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsIso f] (hbase : f ≫ sY = sX)
    (hf : AlgebraicGeometry.RelativeDimension f 0) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sX sY f hbase 0 hf k) :
    Function.Bijective (flatPullbackChow C sX sY f hbase 0 hf k hfac) := by
  have _ : IsOpenImmersion f := IsOpenImmersion.of_isIso f
  have hinv : inv f ≫ sX = sY := by rw [IsIso.inv_comp_eq, hbase]
  have hrestrict : chowGroupRestrict C sY sX f hbase k =
      chowPushforwardOfIso C sY sX (inv f) hinv k :=
    chowGroupRestrict_of_isIso C sY sX k f hbase
  have hres : Function.Bijective (chowGroupRestrict C sY sX f hbase k) := by
    rw [hrestrict]
    exact (chowGroupEquivOfIso C sY sX (inv f) hinv k).bijective
  have degree : ∀ (n : ℤ), k = n → ∀ (x : CycleGroup C sX k) (y : CycleGroup C sX n),
      x.1 = y.1 → HEq (QuotientAddGroup.mk' (rationalEquivalences C sX k) x)
        (QuotientAddGroup.mk' (rationalEquivalences C sX n) y) := by
    intro n hn x y h
    cases hn
    exact heq_of_eq (congrArg (QuotientAddGroup.mk' (rationalEquivalences C sX k))
      (Subtype.ext h))
  have transport : ∀ (n : ℤ), k = n → ∀ G : chowGroup C sY k →+ chowGroup C sX n,
      (∀ α, HEq (chowGroupRestrict C sY sX f hbase k α) (G α)) → Function.Bijective G := by
    intro n hn G hG
    cases hn
    have hfun : (chowGroupRestrict C sY sX f hbase k : chowGroup C sY k → chowGroup C sX k) = G :=
      funext fun α ↦ eq_of_heq (hG α)
    exact hfun ▸ hres
  refine transport (k + ((0 : ℕ) : ℤ)) (by simp) _ fun α ↦ ?_
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    exact degree (k + ((0 : ℕ) : ℤ)) (by simp) (cycleGroupRestrict C sY sX f hbase k c)
      (flatPullback C sX sY f hbase 0 hf k c)
      (cycleGroupRestrict_eq_flatPullback C sY sX f hbase hf k c)

/-! ### Stacks 02TY in rank zero -/

/-- **Stacks 02TY in rank zero.** Let `X` be locally of finite type over the base of chapter 42,
let `ℰ` be a finite locally free sheaf of rank `0` on `X` and let `p : E ⟶ X` be the associated
vector bundle. Then `p^* : CH_k(X) ⟶ CH_{k+0}(E)` is bijective, which is the assertion of Stacks
02TY for `r = 0`.

The bundle projection is carried as an affine-space bundle of rank zero, `p` being Zariski-locally
on `X` the projection `𝔸^0_U ⟶ U`; a rank-zero vector bundle projection has that property. Such a
`p` is an isomorphism, so the assertion is
`Stacks.Chow.flatPullbackChow_bijective_of_isIso`. The instance of Stacks 02S1 needed to write the
map down is not an extra assumption: it is supplied by
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isIso`.

Neither half is proved here for `r ≥ 1`. The source proof forms the projective space bundle
`P = P(ℰ ⊕ 𝒪_X)` with its tautological invertible sheaf, identifies `𝒪_P(D) = 𝒪_P(1)` for the
divisor `D = Z(s)` at infinity by Stacks 01X0, writes `E` as `P ∖ D`, and then runs the
localization sequence of Stacks 02RX against the projective bundle formula of Stacks 02TX for `P`
and for `D`.

Of those inputs **Stacks 02TR is proved**, in both of its equalities and at Chow level for an
arbitrary class: `Stacks.Chow.gysinChowOfInvertible_flatPullbackChow` gives
`i^* p^* α = (p|_D)^* α` and `Stacks.Chow.firstChernClassCapChow_flatPullbackChow` gives
`c₁(ℒ) ∩ p^* α = i_*((p|_D)^* α)`
(`StacksFrontier/AlgebraicGeometry/Chow/RelativeEffectiveCartierFlatPullbackChow.lean:385, 463`,
with the cycle-level forms at
`StacksFrontier/AlgebraicGeometry/Chow/RelativeEffectiveCartierFlatPullback.lean:178, 241, 289`).

What is still missing is Stacks 02TX, which is not proved in this repository — it is available
only as the two hypotheses `Stacks.Chow.ProjectiveBundleRelationInjective` and
`Stacks.Chow.ProjectiveBundleRelationSurjective`. Its surjectivity half alone is Stacks 02TT,
which is itself proved here only in relative dimension zero, and it may not be carried as a
hypothesis, being a conjunct of the conclusion. So the `r ≥ 1` case remains out of reach, but on
account of 02TX and 02TT, not of 02TR. -/
@[stacks 02TY "the isomorphism in rank zero, the projection carried as an affine-space bundle of \
rank zero rather than as the relative spectrum of a symmetric algebra"]
theorem flatPullbackChow_bijective_of_isAffineSpaceBundle_zero (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f]
    (hbase : f ≫ sY = sX) (hf : AlgebraicGeometry.RelativeDimension f 0)
    (hbundle : IsAffineSpaceBundle f 0) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sX sY f hbase 0 hf k) :
    Function.Bijective (flatPullbackChow C sX sY f hbase 0 hf k hfac) := by
  have _ : IsIso f := isIso_of_isAffineSpaceBundle_zero f hbundle
  exact flatPullbackChow_bijective_of_isIso C sX sY f hbase hf k hfac

end Stacks.Chow

end
