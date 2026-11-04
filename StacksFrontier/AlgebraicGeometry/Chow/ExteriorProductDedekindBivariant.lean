module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Cycles

/-!
# Bivariant classes towards a base of delta-dimension one

Let `(S, δ)` be a locally Noetherian scheme with an open covering by spectra of Dedekind domains,
with `δ(s) = 0` for `s` closed and `δ(s) = 1` otherwise, and let `X` be locally of finite type
over `S`. This file constructs the additive map `A^p(X → S) → CH_{1 - p}(X)`, `c ↦ c ∩ [S]₁`,
where `[S]₁ ∈ CH₁(S)` is the fundamental class of the base; by Stacks 0FC5 it is an isomorphism.

## Main definitions

* `Stacks.Chow.bivariantCapBaseFundamentalClass`: the additive map
  `A^p(X → S) → CH_{1 - p}(X)`, `c ↦ c ∩ [S]₁`.

## Main results

* `Stacks.Chow.bivariantCapBaseFundamentalClass_apply`: its defining formula.
* `Stacks.Chow.cap_flatPullbackChow_baseFundamentalChowClass_eq_zero`: a bivariant class that
  caps `[S]₁` to zero caps every flat pullback of `[S]₁` to zero.

## References

* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0FC4](https://stacks.math.columbia.edu/tag/0FC4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (p : ℤ)

/-! ### The fundamental class of the base in degree one -/

/-- The fundamental class `[S]₁ ∈ CH₁(S)` of the base, at the index at which a bivariant class
for `X ⟶ S` caps it: the test scheme is `S` itself, with structure morphism `𝟙 S ≫ 𝟙 S`. -/
def baseFundamentalChowClass : chowGroup C (𝟙 C.S ≫ 𝟙 C.S) 1 :=
  fundamentalChowClass C (𝟙 C.S ≫ 𝟙 C.S) 1

/-! ### The canonical map `A^p(X → S) → CH_{1-p}(X)` -/

/-- The first projection `X ×_S S ⟶ X` of the pullback of `sX` along the identity, an
isomorphism. -/
abbrev basePullbackProjection : pullback sX (𝟙 C.S) ⟶ X := pullback.fst sX (𝟙 C.S)

/-- Proper pushforward of Chow classes along the isomorphism `X ×_S S ⟶ X`. -/
def basePullbackPushforward (k : ℤ) :
    chowGroup C (basePullbackProjection C sX ≫ sX) k →+ chowGroup C sX k :=
  properChowPushforward C (basePullbackProjection C sX ≫ sX) sX (basePullbackProjection C sX) rfl k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C
      (basePullbackProjection C sX ≫ sX) sX (basePullbackProjection C sX) rfl k)

/-- The canonical map `A^p(X → S) → CH_{1-p}(X)`, sending a bivariant class `c` of degree `p`
for the structure morphism `X ⟶ S` to `c ∩ [S]₁`, read on `X` through the isomorphism
`X ×_S S ⟶ X`. -/
@[stacks 0FC5 "the canonical map A^p(X → S) → CH_{1-p}(X), c ↦ c ∩ [S]₁; the source's \
assertion that it is bijective is not proved here"]
def bivariantCapBaseFundamentalClass :
    BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p →+ chowGroup C sX (1 - p) :=
  AddMonoidHom.mk'
    (fun c ↦
      basePullbackPushforward C sX (1 - p) (c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C)))
    (by
      intro c d
      rw [show (c + d).cap (𝟙 C.S) 1 (baseFundamentalChowClass C) =
            c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C) +
              d.cap (𝟙 C.S) 1 (baseFundamentalChowClass C) from
          BivariantClass.add_cap C G sX (𝟙 C.S) sX (Category.comp_id sX) p c d (𝟙 C.S) 1 _,
        map_add])

/-- The canonical map sends `c` to the proper pushforward along `X ×_S S ⟶ X` of the cap
product of `c` with the fundamental class of the base. -/
theorem bivariantCapBaseFundamentalClass_apply
    (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    bivariantCapBaseFundamentalClass C G sX p c =
      basePullbackPushforward C sX (1 - p) (c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C)) :=
  rfl

/-- A class capping the fundamental class of the base to zero is sent to zero by the canonical
map. -/
theorem bivariantCapBaseFundamentalClass_eq_zero_of_cap_eq_zero
    (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (hc : c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C) = 0) :
    bivariantCapBaseFundamentalClass C G sX p c = 0 := by
  rw [bivariantCapBaseFundamentalClass_apply, hc, map_zero]

/-! ### The flat step of the injectivity argument -/

/-- The zero classes of two Chow groups of the same morphism in equal degrees are
heterogeneously equal. -/
theorem heq_zero_chowGroup_of_degree_eq {T : Scheme.{u}} (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] {i j : ℤ} (h : i = j) :
    HEq (0 : chowGroup C sT i) (0 : chowGroup C sT j) := by
  subst h
  rfl

/-- A bivariant class for `X ⟶ S` which caps the fundamental class of the base to zero also caps
every flat pullback of that class to zero. -/
theorem cap_flatPullbackChow_baseFundamentalChowClass_eq_zero
    (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (hc : c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C) = 0)
    {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] [Flat q] (r : ℕ)
    (hq : AlgebraicGeometry.RelativeDimension q r) :
    letI : LocallyOfFiniteType (bivariantBaseChangeMap sX (𝟙 C.S) q) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap sX (𝟙 C.S) q)
        (P := @LocallyOfFiniteType) inferInstance
    letI : Flat (bivariantBaseChangeMap sX (𝟙 C.S) q) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap sX (𝟙 C.S) q)
        (P := @Flat) inferInstance
    ∀ (hq' : AlgebraicGeometry.RelativeDimension (bivariantBaseChangeMap sX (𝟙 C.S) q) r)
      (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((q ≫ 𝟙 C.S) ≫ 𝟙 C.S)
        (𝟙 C.S ≫ 𝟙 C.S) q (by simp) r hq 1)
      (_hfac' : FlatPullbackFactorsThroughRationalEquivalence C
        (pullback.fst sX (q ≫ 𝟙 C.S) ≫ sX) (pullback.fst sX (𝟙 C.S) ≫ sX)
        (bivariantBaseChangeMap sX (𝟙 C.S) q)
        (by rw [← Category.assoc, bivariantBaseChangeMap_fst]) r hq' (1 - p)),
      c.cap (q ≫ 𝟙 C.S) (1 + (r : ℤ))
          (flatPullbackChow C ((q ≫ 𝟙 C.S) ≫ 𝟙 C.S) (𝟙 C.S ≫ 𝟙 C.S) q
            (by simp) r hq 1 hfac (baseFundamentalChowClass C)) = 0 := by
  intro hq' hfac hfac'
  have hnat := c.flat_naturality (𝟙 C.S) q r hq (bivariantBaseChangeMap sX (𝟙 C.S) q)
    (isPullback_bivariantBaseChangeMap sX (𝟙 C.S) q)
    (bivariantBaseChangeMap_fst sX (𝟙 C.S) q) 1 hq' hfac hfac' (baseFundamentalChowClass C)
  rw [hc, map_zero] at hnat
  exact eq_of_heq (hnat.trans
    (heq_zero_chowGroup_of_degree_eq C (pullback.fst sX (q ≫ 𝟙 C.S) ≫ sX) (by ring)))

end Stacks.Chow

end
