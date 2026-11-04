module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange

/-!
# Vanishing of bivariant classes at the canonical Gysin system

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S` and let `c ∈ A^p(X ⟶ Y)`, where `A^p(X ⟶ Y)`
is `Stacks.Chow.BivariantClass C (Stacks.Chow.gysinSystemOfInvertible C) sX sY f hf p`, the
bivariant classes for the Gysin system `Stacks.Chow.gysinSystemOfInvertible`. This file proves
that the following are equivalent: `c` is zero; `c ∩ [Y'] = 0` for every integral scheme `Y'`
locally of finite type over `Y`; and for every such `Y'` there is a proper birational
`Y'' ⟶ Y'` with `c ∩ [Y''] = 0`. It also restates the proper and flat naturality of bivariant
classes with every argument explicit.

## Main results

* `Stacks.Chow.BivariantClass.proper_naturality_of_isProper` — capping commutes with proper
  pushforward along any proper morphism of test schemes.
* `Stacks.Chow.BivariantClass.flat_naturality_of_flat` — capping commutes with flat pullback
  along a flat morphism of test schemes, with the relative dimension of the base change supplied
  by Stacks 02NK.
* `Stacks.Chow.BivariantClass.eq_zero_iff_capsIntegral_canonical`,
  `Stacks.Chow.BivariantClass.capsIntegral_iff_hasBirationalModification_canonical`,
  `Stacks.Chow.BivariantClass.eq_zero_tfae_canonical` — the three conditions above are
  equivalent for `A^p(X ⟶ Y)`.

## References

* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The naturality axioms with every argument explicit -/

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)

/-- Capping with a bivariant class commutes with proper pushforward along a
proper morphism `h : T' ⟶ T` of test schemes and its base change `h'`, pushforward being taken
with the descent of Stacks 02S2,
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper`. -/
@[stacks 0B76 "the proper pushforward axiom, with the descent condition Stacks 02S2 \
discharged"]
theorem BivariantClass.proper_naturality_of_isProper (c : BivariantClass C G sX sY f hf p)
    {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h]
    (h' : pullback f (h ≫ g) ⟶ pullback f g)
    (sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
    (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g)) (k : ℤ)
    (α : chowGroup C ((h ≫ g) ≫ sY) k) :
    letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    c.cap g k (properChowPushforward C ((h ≫ g) ≫ sY) (g ≫ sY) h
        (by simp [Category.assoc]) k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C ((h ≫ g) ≫ sY)
          (g ≫ sY) h (by simp [Category.assoc]) k) α) =
      properChowPushforward C (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
        (by rw [← Category.assoc, hfst]) (k - p)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C
          (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
          (by rw [← Category.assoc, hfst]) (k - p)) (c.cap (h ≫ g) k α) :=
  c.cap_properPushforward g h h' sq hfst k α

/-- Capping with a bivariant class commutes with flat pullback of relative
dimension `r` along a morphism `h : T' ⟶ T` of test schemes and its base change `h'`, pullback
being taken with the descent of Stacks 02S1,
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`, and the relative dimension
of `h'` supplied by Stacks 02NK from the pullback square. -/
theorem BivariantClass.flat_naturality_of_flat (c : BivariantClass C G sX sY f hf p)
    {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (h : T' ⟶ T)
    [LocallyOfFiniteType h] [Flat h] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension h r)
    (h' : pullback f (h ≫ g) ⟶ pullback f g)
    (sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
    (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g)) (k : ℤ)
    (α : chowGroup C (g ≫ sY) k) :
    letI : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    HEq
      (c.cap (h ≫ g) (k + (r : ℤ))
        (flatPullbackChow C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) r hr k
          (flatPullbackFactorsThroughRationalEquivalence_general C ((h ≫ g) ≫ sY) (g ≫ sY) h
            (by simp [Category.assoc]) r hr k) α))
      (flatPullbackChow C (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
        (by rw [← Category.assoc, hfst]) r (AlgebraicGeometry.RelativeDimension.of_isPullback sq hr)
        (k - p)
        (flatPullbackFactorsThroughRationalEquivalence_general C
          (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
          (by rw [← Category.assoc, hfst]) r
          (AlgebraicGeometry.RelativeDimension.of_isPullback sq hr) (k - p))
        (c.cap g k α)) :=
  c.cap_flatPullbackChow g h r hr h' sq hfst k α

/-! ### Stacks 02UC at the canonical Gysin system -/

section Canonical

variable (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)

/-- A bivariant class for the canonical Gysin
system is zero exactly when its cap product with the fundamental class of every integral scheme
locally of finite type over `Y` vanishes. -/
@[stacks 02UC "(1) ⇔ (2) for A^p(X ⟶ Y) itself: the bivariant group read at the canonical \
Gysin system `Stacks.Chow.gysinSystemOfInvertible`, which is constructed outright, so no Gysin \
system is assumed"]
theorem BivariantClass.eq_zero_iff_capsIntegral_canonical :
    c = 0 ↔
      c.CapsIntegralFundamentalClassesToZero C (gysinSystemOfInvertible C) sX sY f hf p :=
  BivariantClass.eq_zero_iff_capsIntegralFundamentalClassesToZero C (gysinSystemOfInvertible C)
    sX sY f hf p c

/-- A bivariant class for the canonical Gysin
system kills the fundamental class of every integral scheme locally of finite type over `Y`
exactly when each such scheme admits a proper birational modification whose fundamental class it
kills. -/
@[stacks 02UC "(2) ⇔ (3) for A^p(X ⟶ Y) itself: the bivariant group read at the canonical \
Gysin system `Stacks.Chow.gysinSystemOfInvertible`, which is constructed outright, so no Gysin \
system is assumed"]
theorem BivariantClass.capsIntegral_iff_hasBirationalModification_canonical :
    c.CapsIntegralFundamentalClassesToZero C (gysinSystemOfInvertible C) sX sY f hf p ↔
      c.HasBirationalModificationCappingToZero C (gysinSystemOfInvertible C) sX sY f hf p :=
  BivariantClass.capsIntegralFundamentalClassesToZero_iff_hasBirationalModification C
    (gysinSystemOfInvertible C) sX sY f hf p c

/-- For a bivariant class `c ∈ A^p(X ⟶ Y)` for the canonical Gysin system the following are
equivalent: `c` is zero; `c ∩ [Y'] = 0` for every integral scheme `Y'` locally of finite type
over `Y`; and every such `Y'` admits a proper birational `Y'' ⟶ Y'` with `c ∩ [Y''] = 0`. -/
@[stacks 02UC "all three clauses for A^p(X ⟶ Y) itself: the bivariant group read at the \
canonical Gysin system `Stacks.Chow.gysinSystemOfInvertible`, which is constructed outright, so \
no Gysin system is assumed"]
theorem BivariantClass.eq_zero_tfae_canonical :
    [c = 0, c.CapsIntegralFundamentalClassesToZero C (gysinSystemOfInvertible C) sX sY f hf p,
      c.HasBirationalModificationCappingToZero C (gysinSystemOfInvertible C)
        sX sY f hf p].TFAE :=
  BivariantClass.eq_zero_tfae C (gysinSystemOfInvertible C) sX sY f hf p c

end Canonical

end Stacks.Chow

end
