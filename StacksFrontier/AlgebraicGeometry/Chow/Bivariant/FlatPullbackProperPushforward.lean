module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackGysinComparison
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardChowBaseChangeGenuine

/-!
# Flat pullback commutes with proper pushforward on Chow groups, in bivariant form

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. In a cartesian square of
schemes locally of finite type over `S` with one pair of opposite legs proper and the other flat of
relative dimension `r`, flat pullback of Chow classes commutes with proper pushforward (Stacks
02RG). Consequently, for `f : X ⟶ Y` flat of relative dimension `r`, flat pullback along the base
changes of `f` is a bivariant class of degree `-r` for `f` (Stacks 0B78), over the Gysin system
`Stacks.Chow.gysinSystemOfInvertible` of the first Chern class of an invertible module.

## Main definitions

* `Stacks.Chow.flatPullbackBivariantClassOfInvertible` — the flat-pullback rule as an element of
  `A^{-r}(X ⟶ Y)` over the Gysin system of an invertible module.

## Main results

* `Stacks.Chow.properPushforwardFlatPullbackBaseChange` — Stacks 02RG on Chow groups, in the form
  `Stacks.Chow.ProperPushforwardFlatPullbackBaseChange`, for every cartesian square over the base
  with a proper and a flat pair of legs.
* `Stacks.Chow.flatPullbackBivariantCap_proper_naturality_unconditional` — the proper-pushforward
  condition of Stacks 0B76 for the flat-pullback rule.
* `Stacks.Chow.isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible` — that class
  satisfies the characterization `Stacks.Chow.IsBivariantFlatPullback` of Stacks 0B78.

## References

* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- In a cartesian square of schemes locally of finite type over the base of chapter 42 whose
horizontal legs `u₀ : A₀ ⟶ B₀`, `u₁ : A₁ ⟶ B₁` are proper and whose vertical legs `d : A₁ ⟶ A₀`,
`v : B₁ ⟶ B₀` are flat of relative dimension `r`, flat pullback of Chow classes commutes with
proper pushforward: `v^* u₀_* α = u₁_* d^* α`. -/
theorem properPushforwardFlatPullbackBaseChange (C : ChowSituation.{u}) :
    ProperPushforwardFlatPullbackBaseChange C := by
  intro A₀ A₁ B₀ B₁ sA₀ _ sA₁ _ sB₀ _ sB₁ _ u₀ _ hu₀ u₁ _ hu₁ d _ _ hd v _ _ hv hsq r hdr hvr k
    hfacd hfacv hppu₀ hppu₁ α
  exact flatPullbackChow_properChowPushforward_unconditional C sA₀ sB₀ sA₁ sB₁ u₀ v d u₁ hsq hu₀
    hv hd r hvr k α

/-- The proper-pushforward condition of Stacks 0B76 (1) for the flat-pullback rule of Stacks 0B78:
flat pullback along the base change of a flat `f : X ⟶ Y` of relative dimension `r` commutes with
proper pushforward along a proper morphism `h : T' ⟶ T` of test schemes over `Y`. -/
theorem flatPullbackBivariantCap_proper_naturality_unconditional (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sY = sX)
    (r : ℕ) (hfr : AlgebraicGeometry.RelativeDimension f r) {T T' : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h]
    (h' : pullback f (h ≫ g) ⟶ pullback f g) [IsProper h']
    (sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
    (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g)) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sY) (g ≫ sY) h
      (by simp [Category.assoc]) k)
    (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
      (by rw [← Category.assoc, hfst]) (k - -(r : ℤ)))
    (α : chowGroup C ((h ≫ g) ≫ sY) k) :
    flatPullbackBivariantCap C sX sY f hf r hfr (flatPullbackDescends C) g k
        (properChowPushforward C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) k hfac
          α) =
      properChowPushforward C (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
        (by rw [← Category.assoc, hfst]) (k - -(r : ℤ)) hfac'
        (flatPullbackBivariantCap C sX sY f hf r hfr (flatPullbackDescends C) (h ≫ g) k α) :=
  flatPullbackBivariantCap_proper_naturality C sX sY f hf r hfr (flatPullbackDescends C)
    (properPushforwardFlatPullbackBaseChange C) g h h' sq hfst k hfac hfac' α

/-- For `f : X ⟶ Y` flat of relative dimension `r` between schemes locally of finite type over the
base, the rule which assigns to a test scheme `g : T ⟶ Y` the flat pullback
`A_k(T) ⟶ A_{k+r}(X ×_Y T)` along the base change of `f`, as a bivariant class of degree `-r` for
`f` over the Gysin system `Stacks.Chow.gysinSystemOfInvertible`. -/
@[stacks 0B78 "the flat-pullback rule IS a bivariant class of degree -r, with NOTHING ASSUMED: \
the Stacks 02S1 descent is the theorem Stacks.Chow.flatPullbackDescends, Stacks 02RG on Chow \
groups is the theorem Stacks.Chow.properPushforwardFlatPullbackBaseChange above, and Stacks 0B71 \
with the identification of Stacks 0B6Y is the theorem \
Stacks.Chow.gysinSystemOfInvertible_flatPullbackNaturalityAtZeroSchemeComparison"]
def flatPullbackBivariantClassOfInvertible (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sY = sX) (r : ℕ)
    (hfr : AlgebraicGeometry.RelativeDimension f r) :
    BivariantClass C (gysinSystemOfInvertible C) sX sY f hf (-(r : ℤ)) where
  cap := fun {_T} g _ k ↦
    flatPullbackBivariantCap C sX sY f hf r hfr (flatPullbackDescends C) g k
  cap_properPushforward := by
    intro T T' g _ h _ h' sq hfst k α
    have : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    exact flatPullbackBivariantCap_proper_naturality_unconditional C sX sY f hf r hfr g h h' sq
      hfst k _ _ α
  cap_flatPullbackChow := by
    intro T T' g _ h _ _ m hm h' sq hfst k α
    have : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    have : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    exact flatPullbackBivariantCap_flat_naturality C sX sY f hf r hfr (flatPullbackDescends C) g h
      m hm h' sq hfst k _ _ _ α
  cap_gysin := by
    intro T g _ L _ s k
    dsimp only
    intro e he hbase α
    exact flatPullbackBivariantCap_gysin_naturality_of_comparison C (gysinSystemOfInvertible C) sX
      sY f hf r hfr (flatPullbackDescends C)
      (gysinSystemOfInvertible_flatPullbackNaturalityAtZeroSchemeComparison C r) g L s k e he
      hbase _ α

/-- The class `Stacks.Chow.flatPullbackBivariantClassOfInvertible` is the flat-pullback class in
the sense of `Stacks.Chow.IsBivariantFlatPullback`: on every test scheme its cap operation is flat
pullback along the base change of `f`. -/
theorem isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sY = sX)
    (r : ℕ) (hfr : AlgebraicGeometry.RelativeDimension f r) :
    IsBivariantFlatPullback C (gysinSystemOfInvertible C) sX sY f hf r hfr
      (flatPullbackDescends C) (flatPullbackBivariantClassOfInvertible C sX sY f hf r hfr) := by
  intro _T g _ k α
  rfl

end Stacks.Chow

end
