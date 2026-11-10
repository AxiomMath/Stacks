module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindBivariant
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.BaseFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.FieldCounterexample
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyOverFieldUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceGysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.RespectsRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.EmbeddedPointCounterexample
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Cycles
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.TopDegreeRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClassCharacterized

/-!
# Bivariant classes towards a base of delta-dimension one: the identification of Stacks 0FC5

Let `(S, δ)` be a base as in the section "Exterior product over Dedekind domains" of chapter 42
of the Stacks Project: a locally Noetherian scheme with an open covering by spectra of Dedekind
domains, with `δ(s) = 0` for `s` closed and `δ(s) = 1` otherwise. Let `X` be a scheme locally of
finite type over `S`. **Stacks 0FC5** says that `c ↦ c ∩ [S]₁`, where `[S]₁ ∈ CH₁(S)` is the
fundamental class of the base in degree one, is an identification

  `A^p(X → S) = CH_{1 - p}(X)`

for every `p ∈ ℤ`. This file proves it, under one additional hypothesis on the base which the
statement needs; see the implementation notes.

**Injectivity.** By Stacks 02UC a class `c` vanishes as soon as `c ∩ [T] = 0` for every integral
`T` locally of finite type over `S`. If `T` dominates an irreducible component of `S` it is flat
over `S` of some relative dimension `r` (Stacks 0AUW) and `[T] = (T → S)^*[S]₁`. Otherwise `T`
lies over a closed point `s`; on an integral neighbourhood `V` of `s` the reduced point `s` is the
zero scheme `D` of a section of an invertible module, so `[D]₀` is the Gysin image of
`[V]₁ = (V → S)^*[S]₁`, and `[T] = (T → D)^*[D]₀`, the point `D` being the spectrum of a field.
The laws of Stacks 0B76 for flat pullback and for Gysin maps carry `c ∩ [S]₁ = 0` to
`c ∩ [T] = 0`.

**Surjectivity.** The image is a subgroup. A class in `CH_{1-p}(X)` is that of a locally finite
cycle `∑ nₓ [x]`; separating the points over generic and over closed points of the base, and the
positive and negative coefficients, it is a combination of four cycles `∑_j [y_j]`, the points
`y_j` repeated according to the coefficients. For each, `W = ∐_j closure{y_j}` is proper over
`X`, and it suffices to find `ξ ∈ A^p(W → S)` with `ξ ∩ [S]₁ = [W]_{1-p}`, for then
`g_* ∘ ξ` (Stacks 0EPK) is sent to `g_*[W]_{1-p} = ∑_j [y_j]`. Over generic points `W` is flat
over `S` and `ξ` is the flat pullback class of Stacks 0B78. Over closed points `ξ` is assembled by
Stacks 0FDZ from classes on the summands, each the composite of the Gysin class of Stacks 0B79 of
the closed point on a neighbourhood, flat pullback along that neighbourhood, and flat pullback to
the summand.

## Main definitions

* `Stacks.Chow.HasNoZeroDimensionalComponent` — the hypothesis that every closed point of the base
  is a proper specialization.
* `Stacks.Chow.bivariantCapBaseFundamentalClass` — the canonical map
  `A^p(X → S) → CH_{1 - p}(X)`, `c ↦ c ∩ [S]₁`.
* `Stacks.Chow.bivariantCapBaseFundamentalClassEquiv` — **Stacks 0FC5**, the identification as an
  isomorphism of groups.

## Main results

* `Stacks.Chow.bivariantCapBaseFundamentalClass_bijective` — **Stacks 0FC5**: over a base as in
  section 42.63 with no zero-dimensional component the canonical map is bijective.
* `Stacks.Chow.bivariantCapBaseFundamentalClass_injective`,
  `Stacks.Chow.bivariantCapBaseFundamentalClass_surjective` — its two halves.
* `Stacks.Chow.cap_fundamentalChowClass_eq_zero_of_isDedekindChowBase` — a class killing `[S]₁`
  kills the fundamental class of every integral scheme over the base.
* `Stacks.Chow.exists_bivariantClass_cap_eq_of_closedPoint` — the class `(p')^* ∘ c_s` of the
  source attached to an integral scheme over a closed point `s`, with its value on fundamental
  classes.
* `Stacks.Chow.gysinSystemOfInvertible_onChow_fundamentalChowClass_of_isIntegral` — the Gysin
  map of a section sends the fundamental class of an integral scheme to that of the zero scheme.
* `Stacks.Chow.IsDedekindChowBase.exists_isIntegral_zeroScheme_eq` — a closed point of a Dedekind
  base with a proper generalization is the zero scheme of a section of an invertible module on an
  integral neighbourhood.
* `Stacks.Chow.not_injective_bivariantCapBaseFundamentalClass_fieldChowSituation`, with
  `Stacks.Chow.isDedekindChowBase_fieldChowSituation` — the statement of the source fails for
  `S = Spec k`, which is a base as in section 42.63.

## Implementation notes

### The hypothesis on the base

The source allows the Dedekind domains of the covering to be fields: a field is a Dedekind domain
(Stacks 034W, and Mathlib's `IsDedekindDomain`). On such a component the statement is false. If
`s` is a closed point of `S` with no proper generalization, it is an open and closed point
`Spec κ(s)` of `S` with `δ(s) = 0`; for `X` that point, `[S]₁` restricts to `[Spec κ(s)]₁ = 0`,
so `c ↦ c ∩ [S]₁` kills the class `1 ∈ A^0(X → S)`, which caps `[Spec κ(s)]₀` to itself and is
not zero. The simplest instance is `S = Spec k` with `δ ≡ 0`: then `[S]₁ = 0` and the map is zero,
whereas `A^0(S → S)` contains `1` and `CH₁(S) = 0`. The hypothesis
`Stacks.Chow.HasNoZeroDimensionalComponent`, that every closed point is a proper specialization,
excludes exactly these points, and with it the source's proof goes through: the generic points of
the base then have `δ = 1`, which is what makes a flat `T` of relative dimension `r` have its
fundamental class in degree `1 + r`.

### `A^p(X → S)` and the shape of the identification

`A^p(X → S)` is `Stacks.Chow.BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p`, read at the
Gysin system `Stacks.Chow.gysinSystemOfInvertible` of invertible modules, which is constructed
outright. The cap operation at the test scheme `𝟙 S` lands on the chosen pullback `X ×_S S`, which
is carried to `X` by pushforward along the first projection, an isomorphism.

### The inverse is not built as an exterior product

The source defines the inverse by `c_α ∩ α' = α × α'`, the exterior product of Stacks 0FC4, and
checks that `c_α` is bivariant by writing it as `g_* ∘ ξ`. Surjectivity only needs the classes
`g_* ∘ ξ` themselves, and the image being a subgroup lets the multiplicities of `α` be carried by
repeating the components of `W` rather than by integral combinations of classes, as in the
proof of Stacks 0FBW in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyOverFieldUnconditional`. The Gysin
class of a closed point is taken on an integral neighbourhood of the point, where the point is the
zero scheme of a section of an invertible module, and moved to the base by flat pullback along the
neighbourhood; the infinitely many closed points a cycle may meet are handled at once by
Stacks 0FDZ on the coproduct `W`.

## References

* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0B79](https://stacks.math.columbia.edu/tag/0B79)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0AUW](https://stacks.math.columbia.edu/tag/0AUW)
* [Stacks Project, Tag 0FC4](https://stacks.math.columbia.edu/tag/0FC4)
* [Stacks Project, Tag 034W](https://stacks.math.columbia.edu/tag/034W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (p : ℤ)

/-! ### Bases of pure dimension one -/

/-- The base of a Chow situation has **no zero-dimensional component**: every closed point is a
proper specialization of another point. For a base as in Stacks section 42.63
(`Stacks.Chow.IsDedekindChowBase`) this says that every Dedekind domain of the covering has
dimension one, i.e. that the base is of pure dimension one.

This is the hypothesis under which Stacks 0FC5 holds on all of `S`, and it is the minimal one.
(Stacks 0FCB itself needs no such hypothesis: it is proved over the zero- and the one-dimensional
parts of `S` separately, in `StacksFrontier.AlgebraicGeometry.Chow.SmoothChowCohomologyDedekind`.)
As stated in the source they also admit a zero-dimensional component — a field is a Dedekind
domain (Stacks 034W, and Mathlib's `IsDedekindDomain`) — and there they fail. If `s` is a closed
point with no proper generalization, then for `X` the open and closed point `Spec κ(s)` of the base
the class `[S]₁` restricts to `[Spec κ(s)]₁ = 0`, so `c ↦ c ∩ [S]₁` kills the nonzero class
`1 ∈ A^0(X → S)`; for `S = Spec k` with `δ ≡ 0` the map is zero on
`A^0(Spec k ⟶ Spec k) ≅ CH_0(Spec k) ≅ ℤ` (Stacks 0FBW). Likewise the exterior product of
section 42.63, landing in degree `n + m - 1`, is then identically zero, so the intersection product
of section 42.64 cannot be `[X] · [X] = [X]`. -/
def HasNoZeroDimensionalComponent (C : ChowSituation.{u}) : Prop :=
  ∀ s : C.S, IsClosed ({s} : Set C.S) → ∃ t : C.S, t ⤳ s ∧ t ≠ s


/-! ### Fundamental classes under restriction, the Gysin map and the canonical map -/

section General

/-- **Stacks 02T8 on a fundamental class.** Let `T` be integral of delta-dimension `k + 1` and
let `σ` be a global section of an invertible module whose zero scheme `D` is not all of `T`.
Then the Gysin map of the Gysin system of invertible modules sends `[T]_{k+1}` to `[D]_k`: the
whole of `T` is an integral closed subscheme not contained in `D`, and its intersection with
`D` is `D`. -/
theorem gysinSystemOfInvertible_onChow_fundamentalChowClass_of_isIntegral (C : ChowSituation.{u})
    {T : Scheme.{u}} [IsIntegral T] (q : T ⟶ C.S) [LocallyOfFiniteType q] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (σ : Γ(L, ⊤)) (k : ℤ)
    (hT : relativeDimension C.dimensionFunction q (genericPoint T) = k + 1)
    (hD : ¬ Stacks.Divisors.zeroScheme T L σ ≤ ⊥) :
    (gysinSystemOfInvertible C).onChow q L σ k (fundamentalChowClass C q (k + 1)) =
      fundamentalChowClass C ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ q) k := by
  set D := Stacks.Divisors.zeroScheme T L σ with hDdef
  have _ : IsIso ((⊥ : T.IdealSheafData).comap D.subschemeι).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).2 (Scheme.IdealSheafData.comap_bot _)
  have _ : Nonempty (⊥ : T.IdealSheafData).subscheme :=
    ⟨(inv (⊥ : T.IdealSheafData).subschemeι).base (genericPoint T)⟩
  have hW : IsIntegral (⊥ : T.IdealSheafData).subscheme :=
    isIntegral_of_isOpenImmersion (⊥ : T.IdealSheafData).subschemeι
  have _ := hW
  have hDim : schemeDeltaDimension C ((⊥ : T.IdealSheafData).subschemeι ≫ q) =
      ((k + 1 : ℤ) : EInt) := by
    rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_closedImmersion,
      genericPoint_eq_of_isOpenImmersion, hT]
  have h1 : fundamentalChowClass C q (k + 1) =
      QuotientAddGroup.mk' (rationalEquivalences C q (k + 1))
        (cycleAssociatedToClosedSubscheme C q (⊥ : T.IdealSheafData).subschemeι (k + 1)) := by
    rw [fundamentalChowClass, fundamentalCycle,
      cycleAssociatedToClosedSubscheme_eq_of_iso C q (𝟙 T) (⊥ : T.IdealSheafData).subschemeι
        (asIso (⊥ : T.IdealSheafData).subschemeι).symm (by simp)]
  rw [h1, gysinSystemOfInvertible_onChow,
    gysinHomomorphismOnChowOfInvertible_mk_cycleAssociatedToClosedSubscheme C q k L σ _ ⊥ hW
      hDim hD, fundamentalChowClass, fundamentalCycle,
    cycleAssociatedToClosedSubscheme_eq_of_iso C (D.subschemeι ≫ q) (𝟙 D.subscheme)
      ((⊥ : T.IdealSheafData).comap D.subschemeι).subschemeι
      (asIso ((⊥ : T.IdealSheafData).comap D.subschemeι).subschemeι).symm (by simp)]
  rfl

/-- Transport of the zero class along an equality of degrees is zero. -/
theorem eq_mp_chowGroup_zero (C : ChowSituation.{u}) {A : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] {k l : ℤ} (hkl : k = l) :
    Eq.mp (congrArg (chowGroup C sA) hkl) (0 : chowGroup C sA k) = 0 := by
  subst hkl
  rfl

/-- On an integral scheme the fundamental class vanishes in every degree other than the relative
dimension of the generic point. -/
theorem fundamentalChowClass_eq_zero_of_ne (C : ChowSituation.{u}) {T : Scheme.{u}}
    [IsIntegral T] (q : T ⟶ C.S) [LocallyOfFiniteType q] {k : ℤ}
    (hk : relativeDimension C.dimensionFunction q (genericPoint T) ≠ k) :
    fundamentalChowClass C q k = 0 := by
  rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_ne C q genericPoints_eq_singleton hk,
    map_zero]

/-- A bivariant class which kills a Chow class on a test scheme kills every flat pullback of it:
this is the flat-pullback law of Stacks 0B76. -/
theorem BivariantClass.cap_flatPullbackChow_eq_zero {C : ChowSituation.{u}} {G : GysinSystem C}
    {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}
    (c : BivariantClass C G sX sY f hf p) {T T' : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r) (k : ℤ) (α : chowGroup C (g ≫ sY) k)
    (hα : c.cap g k α = 0) :
    c.cap (h ≫ g) (k + (r : ℤ))
      (flatPullbackChow C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) r hr k
        (flatPullbackDescends C _ _ h _ r hr k) α) = 0 := by
  have hnat := c.flat_naturality_of_flat C G sX sY f hf p g h r hr (bivariantBaseChangeMap f g h)
    (isPullback_bivariantBaseChangeMap f g h) (bivariantBaseChangeMap_fst f g h) k α
  rw [hα, map_zero] at hnat
  exact chowGroup_eq_zero_of_heq_zero C (by ring) hnat

/-- A bivariant class which kills a Chow class on a test scheme `T` kills its Gysin image on the
zero scheme of every section of an invertible module on `T`: this is the Gysin law of
Stacks 0B76, read through the identification of Stacks 0B6Y. -/
theorem BivariantClass.cap_gysin_eq_zero {C : ChowSituation.{u}} {G : GysinSystem C}
    {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (σ : Γ(L, ⊤)) (k : ℤ) (α : chowGroup C (g ≫ sY) (k + 1)) (hα : c.cap g (k + 1) α = 0) :
    c.cap ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ g) k (G.onChow (g ≫ sY) L σ k α) =
      0 := by
  have _ : AlgebraicGeometry.SheafOfModules.IsInvertible (pullback f g).sheaf.obj
      (pullback f g).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd f g)).obj L) :=
    Stacks.Divisors.pullback_isInvertible _ _
  have hgys := c.gysin_naturality g L σ k (bivariantDivisorBaseChangeIso f g L σ)
    (bivariantDivisorBaseChangeIso_hom_subschemeι f g L σ)
    (by rw [← Category.assoc (bivariantDivisorBaseChangeIso f g L σ).hom,
      bivariantDivisorBaseChangeIso_hom_subschemeι,
      ← Category.assoc (bivariantBaseChangeMap f g (Stacks.Divisors.zeroScheme T L σ).subschemeι),
      bivariantBaseChangeMap_fst])
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _) α
  rw [hα, eq_mp_chowGroup_zero C _ (by ring : k + 1 - p = k - p + 1), map_zero,
    properChowPushforward_eq_chowPushforwardOfIso] at hgys
  exact chowPushforwardOfIso_injective C _ _ _ _ _ (hgys.trans (map_zero _).symm)

/-- Being of relative dimension `r` (Stacks 02NJ) depends on a morphism only through its
value. -/
theorem _root_.AlgebraicGeometry.RelativeDimension.of_eq {X S : Scheme.{u}} {f g : X ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (h : f = g) {r : ℕ}
    (hf : AlgebraicGeometry.RelativeDimension f r) : AlgebraicGeometry.RelativeDimension g r := by
  subst h
  exact hf

end General

/-! ### The canonical map on proper pushforwards and on flat pullback classes -/

section Evaluation

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- Proper pushforward along the isomorphism `X ×_S S ⟶ X` is pushforward along an
isomorphism. -/
theorem basePullbackPushforward_eq_chowPushforwardOfIso (k : ℤ) :
    basePullbackPushforward C sX k =
      chowPushforwardOfIso C (basePullbackProjection C sX ≫ sX) sX
        (basePullbackProjection C sX) rfl k :=
  rfl

/-- The canonical map of Stacks 0FC5 commutes with proper pushforward: for `g : W ⟶ X` proper and
`ξ ∈ A^p(W → S)`, the class `g_* ∘ ξ ∈ A^p(X → S)` of Stacks 0EPK is sent to `g_*(ξ ∩ [S]₁)`. -/
theorem bivariantCapBaseFundamentalClass_bivariantProperPushforward {W : Scheme.{u}}
    (g : W ⟶ X) [IsProper g] [LocallyOfFiniteType (g ≫ sX)] (p : ℤ)
    (ξ : BivariantClass C (gysinSystemOfInvertible C) (g ≫ sX) (𝟙 C.S) (g ≫ sX)
      (Category.comp_id _) p) :
    bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p
        (bivariantProperPushforwardOfInvertible C (g ≫ sX) sX (𝟙 C.S) g sX rfl
          (Category.comp_id sX) p ξ) =
      properChowPushforward C (g ≫ sX) sX g rfl (1 - p) (properPushforwardDescends C _ _ g rfl _)
        (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) (g ≫ sX) p ξ) :=
  chowPushforwardOfIso_properChowPushforward_baseChange C sX g (properPushforwardDescends C) rfl
    (ξ.cap (𝟙 C.S) 1 (baseFundamentalChowClass C))

/-- The canonical map of Stacks 0FC5 sends a class characterized by the rule of Stacks 0B78
(`Stacks.Chow.IsBivariantFlatPullback`) for a structure morphism `W ⟶ S` flat of relative
dimension `r` to the fundamental class `[W]_{1+r}`, as soon as the base has delta-dimension at
most one: the flat pullback of `[S]₁` is `[W ×_S S]_{1+r}`, and the isomorphism `W ×_S S ⟶ W`
carries it to `[W]_{1+r}`. -/
theorem bivariantCapBaseFundamentalClass_flatPullbackBivariantClass (G : GysinSystem C)
    {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] [Flat sW] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension sW r)
    (c : BivariantClass C G sW (𝟙 C.S) sW (Category.comp_id sW) (-(r : ℤ)))
    (hc : IsBivariantFlatPullback C G sW (𝟙 C.S) sW (Category.comp_id sW) r hr
      (flatPullbackDescends C) c)
    (hdim : schemeDeltaDimension C (𝟙 C.S ≫ 𝟙 C.S) ≤ ((1 : ℤ) : EInt)) :
    bivariantCapBaseFundamentalClass C G sW (-(r : ℤ)) c =
      fundamentalChowClass C sW (1 - -(r : ℤ)) := by
  rw [bivariantCapBaseFundamentalClass_apply, basePullbackPushforward_eq_chowPushforwardOfIso,
    baseFundamentalChowClass, hc.cap_fundamentalChowClass (𝟙 C.S) 1 hdim,
    chowPushforwardOfIso_fundamentalChowClass]

end Evaluation


/-! ### Points of a base as in section 42.63 -/

/-- If the image of `η` is closed, every two specializations of `η` have the same image. -/
private theorem apply_eq_of_specializes_of_isClosed {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} (hf : Continuous f) {η a a' : A} (ha : η ⤳ a)
    (ha' : η ⤳ a') (hc : IsClosed {f η}) : f a = f a' := by
  have h : ∀ b, η ⤳ b → f b = f η := fun b hb ↦ by
    have := specializes_iff_mem_closure.mp (hb.map hf)
    rwa [hc.closure_eq, Set.mem_singleton_iff] at this
  exact (h a ha).trans (h a' ha').symm

namespace IsDedekindChowBase

variable {C : ChowSituation.{u}}

/-- Over a base as in section 42.63, a scheme mapping to the base by an open immersion has
delta-dimension at most one. -/
theorem schemeDeltaDimension_le_one (hS : IsDedekindChowBase C) {T : Scheme.{u}} (j : T ⟶ C.S)
    [IsOpenImmersion j] [LocallyOfFiniteType j] :
    schemeDeltaDimension C j ≤ ((1 : ℤ) : EInt) := by
  have h := schemeDeltaDimension_le_of_forall_relativeDimension_le C j (𝟙 T) (k := 1)
    fun w ↦ by
      rw [← Category.comp_id j, relativeDimension_comp_isOpenImmersion, relativeDimension_id]
      exact hS.dimensionFunction_le_one _
  simpa using h

/-- On a base with no zero-dimensional component the generic points of the irreducible
components are not closed, so the dimension function is one there. -/
theorem dimensionFunction_eq_one_of_mem_genericPoints (hS : IsDedekindChowBase C)
    (hS1 : HasNoZeroDimensionalComponent C) {η : C.S} (hη : η ∈ genericPoints C.S) :
    C.dimensionFunction η = 1 :=
  hS.2.2 η fun hc ↦ by
    obtain ⟨t, hts, hne⟩ := hS1 η hc
    exact hne ((TopologicalSpace.mem_genericPoints_iff_forall_specializes_eq η).1 hη t hts)

/-- **A closed point of a Dedekind base is cut out on an integral neighbourhood.** If `s` is a
closed point with a proper generalization, there is an integral open `V` containing `s` and a
global section of an invertible module on `V` whose zero scheme is the reduced point `s`. This is
`Stacks.Chow.IsDedekindChowBase.exists_zeroScheme_unit_eq` restricted to the intersection of the
neighbourhood found there with an affine open whose ring is a Dedekind domain. -/
theorem exists_isIntegral_zeroScheme_eq (hS : IsDedekindChowBase C) {t s : C.S} (hts : t ⤳ s)
    (hne : t ≠ s) :
    ∃ (V : C.S.Opens) (hsV : s ∈ V) (L : (V : Scheme.{u}).Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible (V : Scheme.{u}).sheaf.obj
        (V : Scheme.{u}).ringCatSheaf.property L) (σ : Γ(L, ⊤)),
      IsIntegral (V : Scheme.{u}) ∧
        Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ =
          integralComponentAt (⟨s, hsV⟩ : (V : Scheme.{u})) := by
  obtain ⟨U, hsU, π, hπ⟩ := hS.exists_zeroScheme_unit_eq hts hne
  obtain ⟨U₀, hsU₀, hU₀, hded⟩ := hS.1 s
  have hsV : s ∈ U ⊓ U₀ := ⟨hsU, hsU₀⟩
  have _ : Nonempty U₀ := ⟨⟨s, hsU₀⟩⟩
  have _ : IsIntegral (U₀ : Scheme.{u}) := isIntegral_of_isOpenImmersion hU₀.isoSpec.hom
  have _ : Nonempty (U ⊓ U₀ : C.S.Opens) := ⟨⟨s, hsV⟩⟩
  have hVU : U ⊓ U₀ ≤ U := inf_le_left
  refine ⟨U ⊓ U₀, hsV, _, Stacks.Divisors.pullback_isInvertible (C.S.homOfLE hVU)
    (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf),
    pullbackGlobalSections (C.S.homOfLE hVU) (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)
      π, isIntegral_of_isOpenImmersion (C.S.homOfLE (inf_le_right : U ⊓ U₀ ≤ U₀)), ?_⟩
  refine ((Stacks.Divisors.zeroScheme_pullback (C.S.homOfLE hVU)
    (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) π).trans
      (congrArg (fun J ↦ J.comap (C.S.homOfLE hVU)) hπ)).trans ?_
  rw [show (⟨s, hsU⟩ : (U : Scheme.{u})) = (C.S.homOfLE hVU).base ⟨s, hsV⟩ from
      (Scheme.homOfLE_apply' hVU s hsV).symm]
  exact comap_integralComponentAt_of_isOpenImmersion (C.S.homOfLE hVU) _

/-- An ideal sheaf equal to the integral component at a closed point `s` has support `{s}`, and
its subscheme is an integral scheme with the single point `s`. -/
private theorem support_eq_singleton_of_eq_integralComponentAt {s : C.S}
    (hclosed : IsClosed ({s} : Set C.S)) (V : C.S.Opens) (hsV : s ∈ V)
    {D : (V : Scheme.{u}).IdealSheafData}
    (hD : D = integralComponentAt (⟨s, hsV⟩ : (V : Scheme.{u}))) :
    (D.support : Set (V : Scheme.{u})) = {(⟨s, hsV⟩ : (V : Scheme.{u}))} ∧
      (∀ z : D.subscheme, D.subschemeι.base z = ⟨s, hsV⟩) ∧ IsIntegral D.subscheme ∧
      Subsingleton D.subscheme := by
  set s' : (V : Scheme.{u}) := ⟨s, hsV⟩ with hs'
  have hs'closed : IsClosed ({s'} : Set (V : Scheme.{u})) := by
    have h1 : (V.ι.base ⁻¹' {s} : Set (V : Scheme.{u})) = {s'} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h ↦ V.ι.isOpenEmbedding.injective h, fun h ↦ h ▸ rfl⟩
    rw [← h1]
    exact hclosed.preimage V.ι.continuous
  have hsupp : (D.support : Set (V : Scheme.{u})) = {s'} := by
    rw [hD, coe_support_integralComponentAt, hs'closed.closure_eq]
  have hDpt : ∀ z : D.subscheme, D.subschemeι.base z = s' := by
    intro z
    have hz : D.subschemeι.base z ∈ (D.support : Set (V : Scheme.{u})) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    rwa [hsupp, Set.mem_singleton_iff] at hz
  exact ⟨hsupp, hDpt, by rw [hD]; exact isIntegral_integralComponentAt s',
    ⟨fun a b ↦ D.subschemeι.isClosedEmbedding.injective (by rw [hDpt a, hDpt b])⟩⟩

/-- A morphism into `V` all of whose points lie over the point `s` factors through the subscheme
of an ideal sheaf equal to the integral component at `s`. -/
private theorem exists_lift_of_eq_integralComponentAt {s : C.S} (V : C.S.Opens) (hsV : s ∈ V)
    {D : (V : Scheme.{u}).IdealSheafData}
    (hD : D = integralComponentAt (⟨s, hsV⟩ : (V : Scheme.{u}))) {T : Scheme.{u}} [IsReduced T]
    (m : T ⟶ (V : Scheme.{u})) (hm : ∀ w, m.base w = ⟨s, hsV⟩) :
    ∃ h : T ⟶ D.subscheme, h ≫ D.subschemeι = m := by
  have hker : D.subschemeι.ker ≤ m.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range, hD]
    refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
    rw [← SetLike.coe_subset_coe, TopologicalSpace.Closeds.coe_closure,
      TopologicalSpace.Closeds.coe_closure]
    refine closure_mono ?_
    rintro _ ⟨w, rfl⟩
    exact hm w
  exact ⟨IsClosedImmersion.lift D.subschemeι m hker, IsClosedImmersion.lift_fac _ _ _⟩

end IsDedekindChowBase

/-! ### Injectivity of the canonical map -/

section Injective

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (p : ℤ)

/-- A class killing `[S]₁` kills `[T]_{1+r}` for every `T` flat of relative dimension `r` over
the base, as soon as the base has delta-dimension at most one: then `[T]_{1+r}` is the flat
pullback of `[S]₁`, and `Stacks.Chow.cap_flatPullbackChow_baseFundamentalChowClass_eq_zero`
applies. -/
theorem cap_fundamentalChowClass_eq_zero_of_flat
    (hdim : schemeDeltaDimension C (𝟙 C.S ≫ 𝟙 C.S) ≤ ((1 : ℤ) : EInt))
    (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (hc : c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C) = 0)
    {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] [Flat q] (r : ℕ)
    (hq : AlgebraicGeometry.RelativeDimension q r) (k : ℤ) (hk : k = 1 + r) :
    c.cap q k (fundamentalChowClass C (q ≫ 𝟙 C.S) k) = 0 := by
  subst hk
  refine BivariantClass.cap_fundamentalChowClass_eq_zero_congr C G sX (𝟙 C.S) sX
    (Category.comp_id sX) p c (Category.comp_id q).symm _ ?_
  have sq := isPullback_bivariantBaseChangeMap sX (𝟙 C.S) q
  have _ : LocallyOfFiniteType (bivariantBaseChangeMap sX (𝟙 C.S) q) :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  have _ : Flat (bivariantBaseChangeMap sX (𝟙 C.S) q) :=
    MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  have h := cap_flatPullbackChow_baseFundamentalChowClass_eq_zero C G sX p c hc q r hq
    (AlgebraicGeometry.RelativeDimension.of_isPullback sq hq)
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
  rwa [baseFundamentalChowClass, flatPullbackChow_fundamentalChowClass _ _ _ _ _ r _ 1 _ hdim]
    at h

end Injective

section InjectiveDedekind

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (p : ℤ)

/-- **The final paragraph of the proof of Stacks 0FC5, one integral scheme at a time.** Over a base
as in section 42.63, a class `c ∈ A^p(X → S)` killing `[S]₁` kills the fundamental class of an
integral scheme `T` over the base, provided the dimension function is one at the image of the
generic point of `T` whenever that image is a generic point of the base.

If the generic point of `T` lies over a generic point of the base, `T` is flat over the base of
some relative dimension `r` and `[T]_{1+r}` is the flat pullback of `[S]₁`. Otherwise `T` lies
over a closed point `s` with a proper generalization; on an integral neighbourhood `V` of `s` the
reduced point `s` is the zero scheme `D` of a section of an invertible module, `[D]₀` is the
Gysin image of `[V]₁`, the flat pullback of `[S]₁` along `V ⟶ S`, and `[T]` is the flat pullback
of `[D]₀` along `T ⟶ D`. -/
theorem cap_fundamentalChowClass_eq_zero_of_dimensionFunction_eq_one (hS : IsDedekindChowBase C)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (hc : c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C) = 0)
    {T : Scheme.{u}} (g : T ⟶ C.S) [LocallyOfFiniteType g] [IsIntegral T] (k : ℤ)
    (hδ1 : g.base (genericPoint T) ∈ genericPoints C.S →
      C.dimensionFunction (g.base (genericPoint T)) = 1) :
    c.cap g k (fundamentalChowClass C (g ≫ 𝟙 C.S) k) = 0 := by
  have hdim : schemeDeltaDimension C (𝟙 C.S ≫ 𝟙 C.S) ≤ ((1 : ℤ) : EInt) :=
    hS.schemeDeltaDimension_le_one (𝟙 C.S ≫ 𝟙 C.S)
  set η := genericPoint T with hη
  by_cases hgen : g.base η ∈ genericPoints C.S
  · -- the flat case
    have _ : Flat g := hS.flat_of_mem_genericPoints g hgen
    have hδ := hδ1 hgen
    have hge : 1 ≤ relativeDimension C.dimensionFunction g η := by
      change 1 ≤ C.dimensionFunction (g.base η) + (Cardinal.toNat (residueTrdeg g η) : ℤ)
      omega
    set r := (relativeDimension C.dimensionFunction g η - 1).toNat with hrdef
    have hr : AlgebraicGeometry.RelativeDimension g r := by
      refine relativeDimension_of_flat_of_coheight C g (𝟙 C.S) r fun w ↦ ?_
      rw [Category.comp_id, relativeDimension_id]
      have hspec : g.base η ⤳ g.base w :=
        ((genericPoint_spec T).specializes (Set.mem_univ w)).map g.continuous
      by_cases heq : g.base η = g.base w
      · rw [← heq, Order.coheight_eq_zero.mpr (isMax_of_mem_genericPoints ⟨_, hgen⟩), zero_add,
          hδ]
      · rw [hS.coheight_eq_one_of_specializes hspec heq,
          hS.2.1 _ (hS.isClosed_singleton_of_specializes hspec heq)]
        have h1 : (relativeDimension C.dimensionFunction g η - 1).toNat + 1 =
            (relativeDimension C.dimensionFunction g η - 0).toNat := by omega
        rw [add_comm]
        exact_mod_cast h1
    have hrd : relativeDimension C.dimensionFunction (g ≫ 𝟙 C.S) η = 1 + r := by
      rw [Category.comp_id]
      omega
    by_cases hk : k = 1 + r
    · exact cap_fundamentalChowClass_eq_zero_of_flat C _ sX p hdim c hc g r hr k hk
    · rw [fundamentalChowClass_eq_zero_of_ne C (g ≫ 𝟙 C.S) (by rw [hrd]; exact Ne.symm hk),
        map_zero]
  · -- the case of a closed point
    obtain ⟨hclosed, t, hts, hne⟩ := hS.exists_specializes_of_notMem_genericPoints hgen
    obtain ⟨V, hsV, L, hL, σ, hVint, hσ⟩ := hS.exists_isIntegral_zeroScheme_eq hts hne
    set s := g.base η with hs
    set s' : (V : Scheme.{u}) := ⟨s, hsV⟩ with hs'
    set D := Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ with hD
    have htV : t ∈ V := hts.mem_open V.isOpen hsV
    have hrange : ∀ w : T, g.base w = s := fun w ↦
      apply_eq_of_specializes_of_isClosed g.continuous
        ((genericPoint_spec T).specializes (Set.mem_univ w)) specializes_rfl hclosed
    obtain ⟨hsupp, hDpt, _, _⟩ :=
      IsDedekindChowBase.support_eq_singleton_of_eq_integralComponentAt hclosed V hsV hσ
    have hδs : C.dimensionFunction s = 0 := hS.2.1 _ hclosed
    -- the generic point of `V` is not closed in the base
    have hδV : relativeDimension C.dimensionFunction ((V.ι ≫ 𝟙 C.S) ≫ 𝟙 C.S)
        (genericPoint (V : Scheme.{u})) = 0 + 1 := by
      rw [Category.comp_id, relativeDimension_comp_isOpenImmersion, relativeDimension_id,
        zero_add]
      refine hS.2.2 _ fun hc ↦ hne ?_
      exact apply_eq_of_specializes_of_isClosed V.ι.continuous
        ((genericPoint_spec (V : Scheme.{u})).specializes (Set.mem_univ ⟨t, htV⟩))
        ((genericPoint_spec (V : Scheme.{u})).specializes (Set.mem_univ s')) hc
    have hDne : ¬ D ≤ ⊥ := by
      intro hle
      have h1 := Scheme.IdealSheafData.support_antitone hle
      have hall : ∀ z : (V : Scheme.{u}), z = s' := fun z ↦ by
        have h2 : z ∈ (D.support : Set (V : Scheme.{u})) :=
          h1 (by rw [Scheme.IdealSheafData.support_bot]; trivial)
        rw [hsupp] at h2
        exact h2
      exact hne (congrArg Subtype.val (hall ⟨t, htV⟩))
    -- the lift of `g` to the reduced point `D`
    have hsub : Set.range g.base ⊆ Set.range V.ι.base := by
      rintro _ ⟨w, rfl⟩
      exact ⟨s', (hrange w).symm⟩
    set g₀ : T ⟶ (V : Scheme.{u}) := IsOpenImmersion.lift V.ι g hsub with hg₀def
    have hg₀ : g₀ ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
    have hg₀pt : ∀ w, g₀.base w = s' := by
      intro w
      refine V.ι.isOpenEmbedding.injective ?_
      rw [← Scheme.Hom.comp_apply, hg₀, hrange]
      rfl
    obtain ⟨h, hhm⟩ := IsDedekindChowBase.exists_lift_of_eq_integralComponentAt V hsV hσ g₀ hg₀pt
    have hhfac : h ≫ D.subschemeι ≫ V.ι = g := by
      rw [← Category.assoc, hhm, hg₀]
    have _ : Flat h := inferInstance
    have _ : LocallyOfFiniteType (h ≫ D.subschemeι ≫ V.ι) := by rw [hhfac]; infer_instance
    have _ : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h (D.subschemeι ≫ V.ι)
    have hnn : 0 ≤ relativeDimension C.dimensionFunction g η := by
      change 0 ≤ C.dimensionFunction s + (Cardinal.toNat (residueTrdeg g η) : ℤ)
      omega
    set r := (relativeDimension C.dimensionFunction g η).toNat with hrdef
    have hr : AlgebraicGeometry.RelativeDimension h r := by
      refine relativeDimension_of_flat_of_coheight C h (D.subschemeι ≫ V.ι) r fun w ↦ ?_
      have hmax : Order.coheight (h.base w) = 0 :=
        Order.coheight_eq_zero.mpr fun b _ ↦ le_of_eq (Subsingleton.elim _ _)
      rw [hmax, zero_add, hhfac, relativeDimension_comp_closedImmersion, ← Category.comp_id V.ι,
        relativeDimension_opensι_comp, relativeDimension_id, hDpt]
      change (r : ℕ∞) = ((relativeDimension C.dimensionFunction g η -
        C.dimensionFunction s).toNat : ℕ∞)
      rw [hδs, sub_zero]
    -- `c` kills `[V]₁`
    have hB1 : c.cap (V.ι ≫ 𝟙 C.S) (0 + 1)
        (fundamentalChowClass C ((V.ι ≫ 𝟙 C.S) ≫ 𝟙 C.S) (0 + 1)) = 0 :=
      cap_fundamentalChowClass_eq_zero_of_flat C _ sX p hdim c hc (V.ι ≫ 𝟙 C.S) 0
        (relativeDimension_of_isOpenImmersion _) (0 + 1) (by simp)
    -- the Gysin step: `c` kills `[D]₀`
    have hX := BivariantClass.cap_gysin_eq_zero c (V.ι ≫ 𝟙 C.S) L σ 0 _ hB1
    rw [gysinSystemOfInvertible_onChow_fundamentalChowClass_of_isIntegral C _ L σ 0 hδV hDne] at hX
    -- the flat step along `T ⟶ D`
    have hDdim : schemeDeltaDimension C ((D.subschemeι ≫ (V.ι ≫ 𝟙 C.S)) ≫ 𝟙 C.S) ≤
        ((0 : ℤ) : EInt) := by
      refine schemeDeltaDimension_le_of_forall_relativeDimension_le C ((V.ι ≫ 𝟙 C.S) ≫ 𝟙 C.S)
        D.subschemeι fun w ↦ ?_
      rw [Category.comp_id, Category.comp_id, ← Category.comp_id V.ι,
        relativeDimension_opensι_comp, relativeDimension_id, hDpt]
      exact hδs.le
    have hB5 := BivariantClass.cap_flatPullbackChow_eq_zero c (D.subschemeι ≫ (V.ι ≫ 𝟙 C.S)) h
      r hr 0 (fundamentalChowClass C ((D.subschemeι ≫ (V.ι ≫ 𝟙 C.S)) ≫ 𝟙 C.S) 0) hX
    rw [flatPullbackChow_fundamentalChowClass _ _ _ _ _ r _ 0 _ hDdim] at hB5
    have hgh : g = h ≫ D.subschemeι ≫ V.ι ≫ 𝟙 C.S := by rw [Category.comp_id, hhfac]
    have hrd : relativeDimension C.dimensionFunction (g ≫ 𝟙 C.S) η = 0 + r := by
      rw [Category.comp_id, zero_add, hrdef, Int.toNat_of_nonneg hnn]
    by_cases hk : k = 0 + r
    · subst hk
      exact BivariantClass.cap_fundamentalChowClass_eq_zero_congr C _ sX (𝟙 C.S) sX
        (Category.comp_id sX) p c hgh _ hB5
    · rw [fundamentalChowClass_eq_zero_of_ne C (g ≫ 𝟙 C.S) (by rw [hrd]; exact Ne.symm hk),
        map_zero]

/-- **The final paragraph of the proof of Stacks 0FC5.** Over a base as in section 42.63 with no
zero-dimensional component, a bivariant class `c ∈ A^p(X → S)` killing `[S]₁` kills the
fundamental class of every integral scheme `T` locally of finite type over the base.

If the generic point of `T` lies over a generic point of the base, `T` is flat over the base of
some relative dimension `r` and `[T]_{1+r}` is the flat pullback of `[S]₁`. Otherwise `T` lies
over a closed point `s`; on an integral neighbourhood `V` of `s` the reduced point `s` is the zero
scheme `D` of a section of an invertible module, `[D]₀` is the Gysin image of `[V]₁`, which is
the flat pullback of `[S]₁` along `V ⟶ S`, and `[T]` is the flat pullback of `[D]₀` along
`T ⟶ D`. In both cases the laws of Stacks 0B76 carry the vanishing of `c ∩ [S]₁` to
`c ∩ [T]`. -/
theorem cap_fundamentalChowClass_eq_zero_of_isDedekindChowBase (hS : IsDedekindChowBase C)
    (hS1 : HasNoZeroDimensionalComponent C)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (hc : c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C) = 0)
    {T : Scheme.{u}} (g : T ⟶ C.S) [LocallyOfFiniteType g] [IsIntegral T] (k : ℤ) :
    c.cap g k (fundamentalChowClass C (g ≫ 𝟙 C.S) k) = 0 :=
  cap_fundamentalChowClass_eq_zero_of_dimensionFunction_eq_one C sX p hS c hc g k
    fun hgen ↦ hS.dimensionFunction_eq_one_of_mem_genericPoints hS1 hgen

/-- **Stacks 0FC5, injectivity.** Over a base as in section 42.63 with no zero-dimensional
component, the canonical map `A^p(X → S) → CH_{1-p}(X)`, `c ↦ c ∩ [S]₁`, is injective: by
Stacks 02UC a class is zero once it kills the fundamental class of every integral scheme over the
base, and `Stacks.Chow.cap_fundamentalChowClass_eq_zero_of_isDedekindChowBase` derives that from
`c ∩ [S]₁ = 0`. -/
theorem bivariantCapBaseFundamentalClass_injective (hS : IsDedekindChowBase C)
    (hS1 : HasNoZeroDimensionalComponent C) :
    Function.Injective (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p) := by
  intro c d h
  rw [← sub_eq_zero, BivariantClass.eq_zero_iff_capsIntegral_canonical]
  intro T g _ _ k
  refine cap_fundamentalChowClass_eq_zero_of_isDedekindChowBase C sX p hS hS1 (c - d) ?_ g k
  rw [BivariantClass.sub_cap, sub_eq_zero]
  refine chowPushforwardOfIso_injective C _ _ (basePullbackProjection C sX) rfl (1 - p) ?_
  exact h

end InjectiveDedekind

/-! ### Surjectivity of the canonical map -/

section VerticalPiece

variable {C : ChowSituation.{u}}

/-- **The vertical generators, one piece at a time.** Let `s` be a closed point of a base as in
section 42.63, with a proper generalization `t₀`, and let `V ∋ s` be an integral open on which
`s` is the zero scheme `D` of a section `σ` of an invertible module `L`. Let `U'` be an integral
scheme mapping to `V` by `m`, all of whose points lie over `s`, of delta-dimension `1 - p`. Then
there is `c ∈ A^p(U' → V)` with `c ∩ [V']₁ = [U' ×_V V']_{1-p}` for every integral open `V'` of
`V` containing `s` and `t₀`: namely `(U' ⟶ D)^* ∘ c_D` with `c_D ∈ A^1(D → V)` the Gysin class
of Stacks 0B79 and `(U' ⟶ D)^*` the flat pullback class of Stacks 0B78, the reduced point `D`
being the spectrum of a field. On `[V']₁` the Gysin class gives `[D ×_V V']₀` and the flat
pullback then gives `[U' ×_V V']_{1-p}`. -/
theorem exists_bivariantClass_cap_eq_of_closedPoint (hS : IsDedekindChowBase C) {t₀ s : C.S}
    (hclosed : IsClosed ({s} : Set C.S)) (hne : t₀ ≠ s)
    (V : C.S.Opens) (hsV : s ∈ V) [IsIntegral (V : Scheme.{u})] (L : (V : Scheme.{u}).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (V : Scheme.{u}).sheaf.obj
      (V : Scheme.{u}).ringCatSheaf.property L] (σ : Γ(L, ⊤))
    (hσ : Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ =
      integralComponentAt (⟨s, hsV⟩ : (V : Scheme.{u})))
    {U' : Scheme.{u}} [IsIntegral U'] (sU' : U' ⟶ C.S) [LocallyOfFiniteType sU']
    (m : U' ⟶ (V : Scheme.{u})) [LocallyOfFiniteType m] (hm : m ≫ (V.ι ≫ 𝟙 C.S) = sU')
    (hpt : ∀ w, sU'.base w = s) (p : ℤ)
    (hδ : relativeDimension C.dimensionFunction sU' (genericPoint U') = 1 - p) :
    ∃ c : BivariantClass C (gysinSystemOfInvertible C) sU' (V.ι ≫ 𝟙 C.S) m hm p,
      ∀ {V' : Scheme.{u}} (t : V' ⟶ (V : Scheme.{u})) [IsOpenImmersion t]
        [LocallyOfFiniteType t] [IsIntegral V'] (x x' : V') (_hx : V.ι.base (t.base x) = s)
        (_hx' : V.ι.base (t.base x') = t₀),
        c.cap t 1 (fundamentalChowClass C (t ≫ (V.ι ≫ 𝟙 C.S)) 1) =
          fundamentalChowClass C (pullback.fst m t ≫ sU') (1 - p) := by
  set s' : (V : Scheme.{u}) := ⟨s, hsV⟩ with hs'
  set D := Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ with hD
  obtain ⟨hsupp, hDpt, _, _⟩ :=
    IsDedekindChowBase.support_eq_singleton_of_eq_integralComponentAt hclosed V hsV hσ
  have hδs : C.dimensionFunction s = 0 := hS.2.1 _ hclosed
  -- the lift of `m` to the reduced point `D`
  have hmpt : ∀ w, m.base w = s' := by
    intro w
    refine V.ι.isOpenEmbedding.injective ?_
    rw [← Scheme.Hom.comp_apply, ← Category.comp_id (m ≫ V.ι), Category.assoc, hm, hpt]
    rfl
  obtain ⟨h, hhm⟩ := IsDedekindChowBase.exists_lift_of_eq_integralComponentAt V hsV hσ m hmpt
  have hh : h ≫ (D.subschemeι ≫ (V.ι ≫ 𝟙 C.S)) = sU' := by
    rw [← Category.assoc, hhm, hm]
  have _ : Flat h := inferInstance
  have _ : LocallyOfFiniteType (h ≫ D.subschemeι) := by rw [hhm]; infer_instance
  have _ : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h D.subschemeι
  have hnn : 0 ≤ 1 - p := by
    rw [← hδ]
    change 0 ≤ C.dimensionFunction (sU'.base (genericPoint U')) +
      (Cardinal.toNat (residueTrdeg sU' (genericPoint U')) : ℤ)
    rw [hpt, hδs]
    omega
  obtain ⟨r, hr1⟩ : ∃ r : ℕ, (r : ℤ) = 1 - p := ⟨(1 - p).toNat, Int.toNat_of_nonneg hnn⟩
  have hr : AlgebraicGeometry.RelativeDimension h r := by
    refine relativeDimension_of_flat_of_coheight C h (D.subschemeι ≫ (V.ι ≫ 𝟙 C.S)) r
      fun w ↦ ?_
    have hmax : Order.coheight (h.base w) = 0 :=
      Order.coheight_eq_zero.mpr fun b _ ↦ le_of_eq (Subsingleton.elim _ _)
    rw [hmax, zero_add, hh, hδ, relativeDimension_comp_closedImmersion,
      relativeDimension_comp_isOpenImmersion, relativeDimension_id, hDpt]
    change (r : ℕ∞) = ((1 - p - C.dimensionFunction s).toNat : ℕ∞)
    rw [hδs, sub_zero, ← hr1, Int.toNat_natCast]
  -- the class
  let γ := (gysinBivariantClass C (V.ι ≫ 𝟙 C.S) L σ).1
  let φ := flatPullbackBivariantClassOfInvertible C sU' (D.subschemeι ≫ (V.ι ≫ 𝟙 C.S)) h hh r hr
  let κ := bivariantCompositeOfInvertible C sU' (D.subschemeι ≫ (V.ι ≫ 𝟙 C.S)) (V.ι ≫ 𝟙 C.S) h
    D.subschemeι hh rfl (-(r : ℤ)) 1 φ γ
  obtain rfl : p = -(r : ℤ) + 1 := by omega
  refine ⟨κ.congrHom hhm hm, ?_⟩
  intro V' t _ _ _ x x' hx hx'
  have hgen1 : genericPoint V' ⤳ x := (genericPoint_spec V').specializes (Set.mem_univ _)
  have hgen2 : genericPoint V' ⤳ x' := (genericPoint_spec V').specializes (Set.mem_univ _)
  -- the Gysin step
  have _ := Stacks.Divisors.pullback_isInvertible t L
  have hδV : relativeDimension C.dimensionFunction (t ≫ (V.ι ≫ 𝟙 C.S)) (genericPoint V') =
      (1 - 1) + 1 := by
    rw [relativeDimension_comp_isOpenImmersion, relativeDimension_comp_isOpenImmersion,
      relativeDimension_id]
    refine (hS.2.2 _ fun hc ↦ ?_).trans (by ring)
    exact hne (hx'.symm.trans ((apply_eq_of_specializes_of_isClosed
      (V.ι.continuous.comp t.continuous) hgen2 hgen1 hc).trans hx))
  have hD'ne : ¬ Stacks.Divisors.zeroScheme V' ((Scheme.Modules.pullback t).obj L)
      (pullbackGlobalSections t L σ) ≤ ⊥ := by
    intro hle
    have h1 := Scheme.IdealSheafData.support_antitone hle
    have h2 : x' ∈ ((Stacks.Divisors.zeroScheme V' ((Scheme.Modules.pullback t).obj L)
        (pullbackGlobalSections t L σ)).support : Set V') :=
      h1 (by rw [Scheme.IdealSheafData.support_bot]; trivial)
    rw [Stacks.Divisors.zeroScheme_pullback, coe_support_comap, Set.mem_preimage, ← hD, hsupp] at h2
    exact hne (hx'.symm.trans (by rw [Set.mem_singleton_iff.mp h2]; rfl))
  have h4 : γ.cap t 1 (fundamentalChowClass C (t ≫ (V.ι ≫ 𝟙 C.S)) 1) =
      fundamentalChowClass C (pullback.fst (gysinTripleInclusion L σ) t ≫
        (gysinTripleInclusion L σ ≫ (V.ι ≫ 𝟙 C.S))) (1 - 1) := by
    rw [(gysinBivariantClass C (V.ι ≫ 𝟙 C.S) L σ).2 t 1, gysinBivariantCap_apply,
      chowGroupDegreeEquiv_fundamentalChowClass,
      gysinSystemOfInvertible_onChow_fundamentalChowClass_of_isIntegral C _ _ _ (1 - 1) hδV hD'ne,
      chowPushforwardOfIso_fundamentalChowClass]
  -- the flat step
  have hdimD : schemeDeltaDimension C (pullback.fst (gysinTripleInclusion L σ) t ≫
      (gysinTripleInclusion L σ ≫ (V.ι ≫ 𝟙 C.S))) ≤ ((1 - 1 : ℤ) : EInt) := by
    rw [schemeDeltaDimension_congr C (h := pullback.snd D.subschemeι t ≫ (t ≫ (V.ι ≫ 𝟙 C.S)))
      (by rw [← Category.assoc, pullback.condition, Category.assoc])]
    refine schemeDeltaDimension_le_of_forall_relativeDimension_le C _ _ fun w ↦ ?_
    rw [relativeDimension_comp_isOpenImmersion, relativeDimension_comp_isOpenImmersion,
      relativeDimension_id,
      ← Scheme.Hom.comp_apply (pullback.snd D.subschemeι t) t, ← pullback.condition,
      Scheme.Hom.comp_apply, hDpt]
    change C.dimensionFunction s ≤ 1 - 1
    rw [hδs]
    norm_num
  have h5 := IsBivariantFlatPullback.cap_fundamentalChowClass
      (hdesc := flatPullbackDescends C)
        (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C sU'
      (D.subschemeι ≫ (V.ι ≫ 𝟙 C.S)) h hh r hr)
      (pullback.fst D.subschemeι t) (1 - 1) hdimD
  -- the composite
  have h3 := isBivariantClassComposition_bivariantCompositeOfInvertible C sU'
    (D.subschemeι ≫ (V.ι ≫ 𝟙 C.S)) (V.ι ≫ 𝟙 C.S) h D.subschemeι hh rfl (-(r : ℤ)) 1 φ γ t 1
    (fundamentalChowClass C (t ≫ (V.ι ≫ 𝟙 C.S)) 1)
  rw [bivariantCompositeCap_apply, h4, h5, properChowPushforward_eq_chowPushforwardOfIso,
    chowPushforwardOfIso_fundamentalChowClass] at h3
  have h3' : κ.cap t 1 (fundamentalChowClass C (t ≫ (V.ι ≫ 𝟙 C.S)) 1) =
      fundamentalChowClass C (pullback.fst (h ≫ D.subschemeι) t ≫ sU') (1 - (-(r : ℤ) + 1)) :=
    eq_of_heq (h3.trans (fundamentalChowClass_heq C _ (by ring)))
  rw [BivariantClass.congrHom_cap, h3', chowPushforwardOfIso_fundamentalChowClass]

end VerticalPiece

section Surjective

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (p : ℤ)

/-- **The generators of `CH_{1-p}(X)` reached by the canonical map.** Let `(y_j)_{j ∈ J}` be a
family of points of `X` of delta-dimension `1 - p`, possibly with repetitions, whose closures form
a locally finite family, and let `g : W = ∐_j closure{y_j} ⟶ X` be the induced proper morphism.
If some `ξ ∈ A^p(W → S)` caps `[S]₁` to `[W]_{1-p}`, then the cycle `∑_j [y_j]` — whose
coefficient at `x` is the number of indices `j` with `y_j = x` — is in the image of the canonical
map of Stacks 0FC5, namely as the image of `g_* ∘ ξ` (Stacks 0EPK). -/
theorem exists_cycle_mem_range_of_sigma {J : Type u} (y : J → X)
    [IsProper (Sigma.desc fun j ↦ (integralComponentAt (y j)).subschemeι)]
    (hδ : ∀ j, relativeDimension C.dimensionFunction sX (y j) = 1 - p)
    (ξ : BivariantClass C (gysinSystemOfInvertible C)
      ((Sigma.desc fun j ↦ (integralComponentAt (y j)).subschemeι) ≫ sX) (𝟙 C.S)
      ((Sigma.desc fun j ↦ (integralComponentAt (y j)).subschemeι) ≫ sX) (Category.comp_id _) p)
    (hξ : bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C)
        ((Sigma.desc fun j ↦ (integralComponentAt (y j)).subschemeι) ≫ sX) p ξ =
      fundamentalChowClass C
        ((Sigma.desc fun j ↦ (integralComponentAt (y j)).subschemeι) ≫ sX) (1 - p)) :
    ∃ P : CycleGroup C sX (1 - p),
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) P ∈
          (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p).range ∧
        ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ) := by
  have _ : ∀ j, IsIntegral (integralComponentAt (y j)).subscheme := fun j ↦
    isIntegral_integralComponentAt _
  have hπ : ∀ j, (integralComponentAt (y j)).subschemeι.base
      (genericPoint (integralComponentAt (y j)).subscheme) = y j := fun j ↦
    genericPointOf_integralComponentAt _
  refine ⟨properPushforward C _ sX (Sigma.desc fun j ↦ (integralComponentAt (y j)).subschemeι)
    rfl (1 - p) (fundamentalCycle C _ (1 - p)),
      ⟨bivariantProperPushforwardOfInvertible C _ sX (𝟙 C.S)
        (Sigma.desc fun j ↦ (integralComponentAt (y j)).subschemeι) sX rfl (Category.comp_id sX)
        p ξ, ?_⟩,
    fun x ↦ properPushforward_fundamentalCycle_sigma_apply C sX _ _ y hπ (1 - p) hδ x⟩
  rw [bivariantCapBaseFundamentalClass_bivariantProperPushforward, hξ]
  rfl

/-- **The flat generators.** Over a base as in section 42.63 with no zero-dimensional component,
the cycle `∑_j [y_j]` attached to a locally finite family of points of delta-dimension `1 - p`
lying over generic points of the base is in the image of the canonical map of Stacks 0FC5.

The closures of the `y_j` are flat over the base of relative dimension `-p` (Stacks 0AUW), so the
coproduct `W` is, and the flat pullback class of Stacks 0B78 of `W ⟶ S` caps `[S]₁` to
`[W]_{1-p}`. -/
theorem exists_cycle_mem_range_of_mem_genericPoints (hS : IsDedekindChowBase C)
    (hS1 : HasNoZeroDimensionalComponent C) {J : Type u} (y : J → X)
    (hlf : LocallyFinite fun j ↦ Set.range (integralComponentAt (y j)).subschemeι)
    (hδ : ∀ j, relativeDimension C.dimensionFunction sX (y j) = 1 - p)
    (hgen : ∀ j, sX.base (y j) ∈ genericPoints C.S) :
    ∃ P : CycleGroup C sX (1 - p),
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) P ∈
          (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p).range ∧
        ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ) := by
  by_cases hJ : IsEmpty J
  · refine ⟨0, zero_mem _, fun x ↦ ?_⟩
    rw [Set.eq_empty_of_isEmpty (y ⁻¹' {x}), finsum_mem_empty]
    rfl
  obtain ⟨j₀⟩ := not_isEmpty_iff.mp hJ
  have hδ1 : ∀ j, C.dimensionFunction (sX.base (y j)) = 1 := fun j ↦
    hS.dimensionFunction_eq_one_of_mem_genericPoints hS1 (hgen j)
  have hp : p ≤ 0 := by
    have h1 := hδ j₀
    have h2 : C.dimensionFunction (sX.base (y j₀)) ≤
        relativeDimension C.dimensionFunction sX (y j₀) := by
      change _ ≤ C.dimensionFunction (sX.base (y j₀)) +
        (Cardinal.toNat (residueTrdeg sX (y j₀)) : ℤ)
      omega
    rw [hδ1] at h2
    omega
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, p = -(r : ℤ) := ⟨(-p).toNat, by omega⟩
  set Zs := fun j ↦ (integralComponentAt (y j)).subscheme with hZs
  set v : ∀ j, Zs j ⟶ X := fun j ↦ (integralComponentAt (y j)).subschemeι with hv
  have _ : IsProper (Sigma.desc v) := isProper_sigmaDesc_of_locallyFinite Zs v hlf
  have hflat : ∀ j, Flat (v j ≫ sX) := fun j ↦ by
    have _ := isIntegral_integralComponentAt (y j)
    refine hS.flat_of_mem_genericPoints _ ?_
    rw [Scheme.Hom.comp_apply, subschemeι_genericPoint_integralComponentAt]
    exact hgen j
  have hdesc : Sigma.desc v ≫ sX = Sigma.desc fun j ↦ v j ≫ sX := by
    refine Sigma.hom_ext _ _ fun j ↦ ?_
    simp
  have _ : Flat (Sigma.desc v ≫ sX) := by
    have := hflat
    rw [hdesc]
    infer_instance
  have hr : AlgebraicGeometry.RelativeDimension (Sigma.desc v ≫ sX) r := by
    refine AlgebraicGeometry.RelativeDimension.of_sigmaι_comp Zs _ fun j ↦ ?_
    have _ := hflat j
    have h := hS.relativeDimension_integralComponentAt_comp sX (y j) (hgen j)
    have e : (relativeDimension C.dimensionFunction sX (y j) -
        C.dimensionFunction (sX.base (y j))).toNat = r := by
      rw [hδ j, hδ1]
      omega
    rw [e] at h
    exact AlgebraicGeometry.RelativeDimension.of_eq (Sigma.ι_comp_desc_assoc _ _ _).symm h
  exact exists_cycle_mem_range_of_sigma C sX (-(r : ℤ)) y hδ
    (flatPullbackBivariantClassOfInvertible C (Sigma.desc v ≫ sX) (𝟙 C.S) (Sigma.desc v ≫ sX)
        (Category.comp_id _) r hr)
    (bivariantCapBaseFundamentalClass_flatPullbackBivariantClass C _ _ r hr _
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C (Sigma.desc v ≫ sX)
        (𝟙 C.S) (Sigma.desc v ≫ sX) (Category.comp_id _) r hr)
      (hS.schemeDeltaDimension_le_one (𝟙 C.S ≫ 𝟙 C.S)))

/-- **The vertical generators.** Over a base as in section 42.63, the cycle `∑_j [y_j]` attached to
a locally finite family of points of delta-dimension `1 - p` lying over closed points of the base
is in the image of the canonical map of Stacks 0FC5.

Each closure `Z_j` lies over a closed point `s_j`, and
`Stacks.Chow.exists_bivariantClass_cap_eq_of_closedPoint` gives a class on `Z_j` relative to an
integral neighbourhood `V_j` of `s_j`. These are assembled by Stacks 0FDZ
(`Stacks.Chow.bivariantPieceAssembly`) into a class `ξ ∈ A^p(W → S)` on the coproduct
`W = ∐_j Z_j`, which caps `[S]₁` to `[W]_{1-p}`: both sides restrict to the fundamental class on
every piece. -/
theorem exists_cycle_mem_range_of_notMem_genericPoints (hS : IsDedekindChowBase C)
    {J : Type u} (y : J → X)
    (hlf : LocallyFinite fun j ↦ Set.range (integralComponentAt (y j)).subschemeι)
    (hδ : ∀ j, relativeDimension C.dimensionFunction sX (y j) = 1 - p)
    (hgen : ∀ j, sX.base (y j) ∉ genericPoints C.S) :
    ∃ P : CycleGroup C sX (1 - p),
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) P ∈
          (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p).range ∧
        ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ) := by
  set Zs := fun j ↦ (integralComponentAt (y j)).subscheme with hZs
  set v : ∀ j, Zs j ⟶ X := fun j ↦ (integralComponentAt (y j)).subschemeι with hv
  have _ : ∀ j, IsIntegral (Zs j) := fun j ↦ isIntegral_integralComponentAt _
  have _ : IsProper (Sigma.desc v) := isProper_sigmaDesc_of_locallyFinite Zs v hlf
  have hπ : ∀ j, (v j).base (genericPoint (Zs j)) = y j := fun j ↦
    genericPointOf_integralComponentAt _
  set sW := Sigma.desc v ≫ sX with hsW
  -- the closed points and their neighbourhoods
  have hcl := fun j ↦ hS.exists_specializes_of_notMem_genericPoints (hgen j)
  choose hclosed t₀ hts hne using hcl
  choose V hsV L hL σ hVint hσ using fun j ↦ hS.exists_isIntegral_zeroScheme_eq (hts j) (hne j)
  -- every point of `Z_j` lies over `s_j`
  have hZpt : ∀ j (z : Zs j), sX.base ((v j).base z) = sX.base (y j) := by
    intro j z
    have hz : (v j).base z ∈ closure ({y j} : Set X) := by
      rw [← coe_support_integralComponentAt, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    exact apply_eq_of_specializes_of_isClosed sX.continuous (specializes_iff_mem_closure.mpr hz)
      specializes_rfl (hclosed j)
  set UX : J → (∐ Zs : Scheme.{u}).Opens := fun j ↦ (Sigma.ι Zs j).opensRange with hUX
  have hX : IsClopenDecomposition UX := isClopenDecomposition_opensRange_sigmaι Zs
  have hUXpt : ∀ j (w : (UX j : Scheme.{u})), sW.base ((UX j).ι.base w) = sX.base (y j) := by
    intro j w
    obtain ⟨z, hz⟩ := w.2
    change sW.base w.1 = _
    rw [← hz, hsW, ← Scheme.Hom.comp_apply, ← Category.assoc, Sigma.ι_comp_desc,
      Scheme.Hom.comp_apply, hZpt]
  have ha : ∀ j, UX j ≤ sW ⁻¹ᵁ V j := by
    intro j w hw
    have h1 := hUXpt j ⟨w, hw⟩
    change sW.base w ∈ V j
    change sW.base w = _ at h1
    rw [h1]
    exact hsV j
  -- the classes on the pieces
  have hpiece : ∀ j, ∃ c : BivariantClass C (gysinSystemOfInvertible C) ((UX j).ι ≫ sW)
      ((V j).ι ≫ 𝟙 C.S) (pieceMap sW UX V (fun j ↦ j) ha j)
      (pieceMap_comp_pieceStructureMorphism C sW (𝟙 C.S) sW (Category.comp_id sW) UX V
        (fun j ↦ j) ha j) p,
      ∀ {V' : Scheme.{u}} (t : V' ⟶ (V j : Scheme.{u})) [IsOpenImmersion t]
        [LocallyOfFiniteType t] [IsIntegral V'] (x x' : V')
        (_hx : (V j).ι.base (t.base x) = sX.base (y j)) (_hx' : (V j).ι.base (t.base x') = t₀ j),
        c.cap t 1 (fundamentalChowClass C (t ≫ ((V j).ι ≫ 𝟙 C.S)) 1) =
          fundamentalChowClass C (pullback.fst (pieceMap sW UX V (fun j ↦ j) ha j) t ≫
            ((UX j).ι ≫ sW)) (1 - p) := by
    intro j
    have _ := hL j
    have _ := hVint j
    have e := (Sigma.ι Zs j).isoOpensRange
    have _ : Nonempty (UX j : Scheme.{u}) := ⟨e.hom.base (genericPoint (Zs j))⟩
    have _ : IsIntegral (UX j : Scheme.{u}) := isIntegral_of_isOpenImmersion e.inv
    refine exists_bivariantClass_cap_eq_of_closedPoint hS (hclosed j) (hne j) (V j) (hsV j) (L j)
      (σ j) (hσ j) ((UX j).ι ≫ sW) (pieceMap sW UX V (fun j ↦ j) ha j) _ (hUXpt j) p ?_
    have hgenUX : genericPoint (UX j : Scheme.{u}) =
        (Sigma.ι Zs j).isoOpensRange.hom.base (genericPoint (Zs j)) :=
      (genericPoint_eq_of_isOpenImmersion (Sigma.ι Zs j).isoOpensRange.hom).symm
    rw [hgenUX, ← relativeDimension_comp_isOpenImmersion, ← Category.assoc,
      Scheme.Hom.isoOpensRange_hom_ι]
    exact relativeDimension_sigmaι_genericPoint C sX Zs v y hπ (1 - p) hδ j
  choose c hc using hpiece
  -- the assembled class caps `[S]₁` to `[W]_{1-p}`
  have hWdim : schemeDeltaDimension C sW ≤ ((1 - p : ℤ) : EInt) := by
    rw [← schemeDeltaDimension_congr C (Category.id_comp sW)]
    refine schemeDeltaDimension_le_of_forall_relativeDimension_le C sW (𝟙 _) fun w ↦ ?_
    obtain ⟨j, z, rfl⟩ := exists_mem_range_sigmaι Zs w
    have hZ : schemeDeltaDimension C (𝟙 (Zs j) ≫ Sigma.ι Zs j ≫ sW) ≤ ((1 - p : ℤ) : EInt) := by
      rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_closedImmersion]
      simpa [hsW] using (relativeDimension_sigmaι_genericPoint C sX Zs v y hπ (1 - p) hδ j).le
    have h1 := relativeDimension_le_of_schemeDeltaDimension_le C _ (𝟙 (Zs j)) hZ z
    rw [relativeDimension_comp_isOpenImmersion] at h1
    simpa using h1
  have hWdim' : schemeDeltaDimension C (pullback.fst sW (𝟙 C.S) ≫ sW) ≤ ((1 - p : ℤ) : EInt) :=
    (schemeDeltaDimension_comp_iso C (asIso (pullback.fst sW (𝟙 C.S))) sW).le.trans hWdim
  set ξ := bivariantPieceAssembly C (gysinSystemOfInvertible C) sW (𝟙 C.S) sW
    (Category.comp_id sW) UX V (fun j ↦ j) ha hX p
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) c with hξdef
  have hcap : ξ.cap (𝟙 C.S) 1 (baseFundamentalChowClass C) =
      fundamentalChowClass C (pullback.fst sW (𝟙 C.S) ≫ sW) (1 - p) := by
    refine (chowGroupPullbackPieceEquiv C sW sW UX V (fun j ↦ j) ha hX (𝟙 C.S) (1 - p)).injective
      (funext fun j ↦ ?_)
    rw [chowGroupPullbackPieceEquiv_apply, chowGroupPullbackPieceEquiv_apply, hξdef,
      bivariantPieceAssembly_cap, bivariantPieceAssemblyCap_restrict, baseFundamentalChowClass,
      chowGroupRestrict_fundamentalChowClass C _ _ _ _ 1
        (hS.schemeDeltaDimension_le_one (𝟙 C.S ≫ 𝟙 C.S)),
      chowGroupRestrict_fundamentalChowClass C _ _ _ _ (1 - p) hWdim']
    have _ : IsOpenImmersion (Scheme.Hom.resLE (𝟙 C.S) (V j) ((𝟙 C.S) ⁻¹ᵁ V j) le_rfl) := by
      delta Scheme.Hom.resLE; infer_instance
    have _ := hVint j
    have _ : Nonempty ((𝟙 C.S) ⁻¹ᵁ V j : Scheme.{u}) := ⟨⟨_, hsV j⟩⟩
    have _ : IsIntegral ((𝟙 C.S) ⁻¹ᵁ V j : Scheme.{u}) :=
      isIntegral_of_isOpenImmersion (Scheme.Hom.resLE (𝟙 C.S) (V j) ((𝟙 C.S) ⁻¹ᵁ V j) le_rfl)
    have hx : sX.base (y j) ∈ (𝟙 C.S) ⁻¹ᵁ V j := hsV j
    have hx' : t₀ j ∈ (𝟙 C.S) ⁻¹ᵁ V j := (hts j).mem_open (V j).isOpen (hsV j)
    refine hc j (Scheme.Hom.resLE (𝟙 C.S) (V j) ((𝟙 C.S) ⁻¹ᵁ V j) le_rfl) ⟨_, hx⟩ ⟨_, hx'⟩ ?_ ?_
    · change ((Scheme.Hom.resLE (𝟙 C.S) (V j) ((𝟙 C.S) ⁻¹ᵁ V j) le_rfl).base ⟨_, hx⟩).1 = _
      rw [Scheme.Hom.coe_resLE_apply]
      rfl
    · change ((Scheme.Hom.resLE (𝟙 C.S) (V j) ((𝟙 C.S) ⁻¹ᵁ V j) le_rfl).base ⟨_, hx'⟩).1 = _
      rw [Scheme.Hom.coe_resLE_apply]
      rfl
  refine exists_cycle_mem_range_of_sigma C sX p y hδ ξ ?_
  rw [bivariantCapBaseFundamentalClass_apply, hcap, basePullbackPushforward_eq_chowPushforwardOfIso,
    chowPushforwardOfIso_fundamentalChowClass]

/-- **From families of generators to cycles with prescribed multiplicities.** Let `Q` be a
property of points of `X` such that for every locally finite family `(y_j)` of points of
delta-dimension `1 - p` satisfying `Q`, the cycle `∑_j [y_j]` is in the image of the canonical
map of Stacks 0FC5. Then for a `(1-p)`-cycle `a` and multiplicities `M` on its support, so is
the cycle with coefficient `M(x)` at each `x` of the support satisfying `Q` and zero elsewhere:
repeat each such point `M(x)` times. -/
theorem exists_cycle_mem_range_of_multiplicity (a : CycleGroup C sX (1 - p)) (Q : X → Prop)
    (hQ : ∀ {J : Type u} (y : J → X),
      LocallyFinite (fun j ↦ Set.range (integralComponentAt (y j)).subschemeι) →
      (∀ j, relativeDimension C.dimensionFunction sX (y j) = 1 - p) → (∀ j, Q (y j)) →
      ∃ P : CycleGroup C sX (1 - p),
        QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) P ∈
            (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p).range ∧
          ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ))
    (M : ↥(Function.support (a.1 : X → ℤ)) → ℕ) :
    ∃ P : CycleGroup C sX (1 - p),
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) P ∈
          (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p).range ∧
        ∀ x, P.1 x = open Classical in
          if h : x ∈ Function.support (a.1 : X → ℤ) ∧ Q x then (M ⟨x, h.1⟩ : ℤ) else 0 := by
  classical
  let I := {i : ↥(Function.support (a.1 : X → ℤ)) // Q i}
  let y : (Σ i : I, Fin (M i.1)) → X := fun j ↦ (j.1.1 : X)
  have hlf : LocallyFinite fun j ↦ Set.range (integralComponentAt (y j)).subschemeι :=
    locallyFinite_sigma_fst (f := fun i : I ↦ Set.range (integralComponentAt (i.1 : X)).subschemeι)
      ((locallyFinite_range_subschemeι_support C sX _ a).comp_injective Subtype.val_injective)
  obtain ⟨P, hP, hPy⟩ := hQ y hlf
    (fun j ↦ (mem_cyclesOfDimension_iff_forall_point C sX _ a.1).1 a.2 _ j.1.1.2)
    (fun j ↦ j.1.2)
  refine ⟨P, hP, fun x ↦ ?_⟩
  rw [hPy]
  by_cases hx : x ∈ Function.support (a.1 : X → ℤ) ∧ Q x
  · rw [dite_eq_left hx]
    exact (finsum_mem_preimage_sigma_fst_one (fun i : I ↦ ((i.1 : _) : X))
      (fun i i' h ↦ Subtype.ext (Subtype.ext h)) ⟨⟨x, hx.1⟩, hx.2⟩).trans (by simp)
  · rw [dite_eq_right hx]
    refine (finsum_mem_congr (Set.eq_empty_of_forall_notMem fun j hj ↦ hx ?_)
      fun _ _ ↦ rfl).trans finsum_mem_empty
    have hj' : (j.1.1 : X) = x := hj
    exact hj' ▸ ⟨j.1.1.2, j.1.2⟩

/-- **Stacks 0FC5, surjectivity.** Over a base as in section 42.63 with no zero-dimensional
component, every class in `CH_{1-p}(X)` is `c ∩ [S]₁` for some `c ∈ A^p(X → S)`.

Write the class as that of a locally finite cycle `∑ nₓ [x]`. Its part supported at points over
generic points of the base and its part supported over closed points are, after separating the
positive and negative coefficients, four cycles of the form `∑_j [y_j]` with repetitions, which
are in the image by `Stacks.Chow.exists_cycle_mem_range_of_mem_genericPoints` and
`Stacks.Chow.exists_cycle_mem_range_of_notMem_genericPoints`; the image is a subgroup. -/
theorem bivariantCapBaseFundamentalClass_surjective (hS : IsDedekindChowBase C)
    (hS1 : HasNoZeroDimensionalComponent C) :
    Function.Surjective
      (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p) := by
  classical
  intro α
  induction α using QuotientAddGroup.induction_on with
  | H a =>
  have hh := fun M ↦ exists_cycle_mem_range_of_multiplicity C sX p a
    (fun x ↦ sX.base x ∈ genericPoints C.S)
    (fun y hlf hδ hQ ↦ exists_cycle_mem_range_of_mem_genericPoints C sX p hS hS1 y hlf hδ hQ) M
  have hv := fun M ↦ exists_cycle_mem_range_of_multiplicity C sX p a
    (fun x ↦ sX.base x ∉ genericPoints C.S)
    (fun y hlf hδ hQ ↦ exists_cycle_mem_range_of_notMem_genericPoints C sX p hS y hlf hδ hQ) M
  obtain ⟨P₁, hP₁, hP₁y⟩ := hh fun i ↦ (a.1 i).toNat
  obtain ⟨P₂, hP₂, hP₂y⟩ := hh fun i ↦ (-a.1 i).toNat
  obtain ⟨P₃, hP₃, hP₃y⟩ := hv fun i ↦ (a.1 i).toNat
  obtain ⟨P₄, hP₄, hP₄y⟩ := hv fun i ↦ (-a.1 i).toNat
  have hsub : a = P₁ - P₂ + (P₃ - P₄) := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    change a.1 x = P₁.1 x - P₂.1 x + (P₃.1 x - P₄.1 x)
    rw [hP₁y, hP₂y, hP₃y, hP₄y]
    by_cases hx : x ∈ Function.support (a.1 : X → ℤ)
    · by_cases hg : sX.base x ∈ genericPoints C.S
      · rw [dite_eq_left ⟨hx, hg⟩, dite_eq_left ⟨hx, hg⟩, dite_eq_right (fun h ↦ h.2 hg),
          dite_eq_right (fun h ↦ h.2 hg)]
        simp only
        omega
      · rw [dite_eq_right (fun h ↦ hg h.2), dite_eq_right (fun h ↦ hg h.2), dite_eq_left ⟨hx, hg⟩,
          dite_eq_left ⟨hx, hg⟩]
        simp only
        omega
    · rw [dite_eq_right (fun h ↦ hx h.1), dite_eq_right (fun h ↦ hx h.1),
        dite_eq_right (fun h ↦ hx h.1), dite_eq_right (fun h ↦ hx h.1)]
      simpa using hx
  have hmem : QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) a ∈
      (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p).range := by
    rw [hsub, map_add, map_sub, map_sub]
    exact add_mem (sub_mem hP₁ hP₂) (sub_mem hP₃ hP₄)
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc⟩

end Surjective

/-! ### Stacks 0FC5 -/

section Main

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (p : ℤ)

/-- **Stacks 0FC5**, corrected form. Let `(S, δ)` be a base as in section 42.63 of the Stacks
Project with no zero-dimensional component, and let `X` be locally of finite type over `S`. Then
`c ↦ c ∩ [S]₁` is a bijection `A^p(X → S) → CH_{1-p}(X)` for every `p ∈ ℤ`.

The hypothesis `hS1` is the correction. A field is a Dedekind domain, so the source's statement
also admits a component `Spec k` of `S` with `δ ≡ 0`, and there it fails: `[S]₁` restricts to
`[Spec k]₁ = 0`, so the map kills the nonzero class `1 ∈ A^0(Spec k → S)`. -/
@[stacks 0FC5 "corrected form: the base is assumed to have no zero-dimensional component \
(`Stacks.Chow.HasNoZeroDimensionalComponent`, every closed point a proper specialization); \
the source admits such components, a field being a Dedekind domain, and for `S = Spec k` the map \
`c ↦ c ∩ [S]₁` is zero while `A^0(S → S)` contains `1`. Bivariant classes are those of the Gysin \
system of invertible modules, `Stacks.Chow.gysinSystemOfInvertible`"]
theorem bivariantCapBaseFundamentalClass_bijective (hS : IsDedekindChowBase C)
    (hS1 : HasNoZeroDimensionalComponent C) :
    Function.Bijective
      (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p) :=
  ⟨bivariantCapBaseFundamentalClass_injective C sX p hS hS1,
    bivariantCapBaseFundamentalClass_surjective C sX p hS hS1⟩

/-- **Stacks 0FC5**, corrected form, as an isomorphism of groups: over a base as in section 42.63
with no zero-dimensional component, `A^p(X → S) ≃+ CH_{1-p}(X)`, `c ↦ c ∩ [S]₁`. -/
@[stacks 0FC5 "corrected form: the base is assumed to have no zero-dimensional component \
(`Stacks.Chow.HasNoZeroDimensionalComponent`); the identification A^p(X → S) = CH_{1-p}(X) as an \
isomorphism of groups, at the Gysin system of invertible modules"]
def bivariantCapBaseFundamentalClassEquiv (hS : IsDedekindChowBase C)
    (hS1 : HasNoZeroDimensionalComponent C) :
    BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p ≃+
      chowGroup C sX (1 - p) :=
  AddEquiv.ofBijective _ (bivariantCapBaseFundamentalClass_bijective C sX p hS hS1)

/-- The identification of Stacks 0FC5 is cap product with the fundamental class of the base. -/
@[simp]
theorem bivariantCapBaseFundamentalClassEquiv_apply (hS : IsDedekindChowBase C)
    (hS1 : HasNoZeroDimensionalComponent C)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    bivariantCapBaseFundamentalClassEquiv C sX p hS hS1 c =
      bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p c :=
  rfl

end Main

/-! ### The uncorrected statement fails over a field -/

section Counterexample

variable (k : Type u) [Field k]

/-- **The source's form of Stacks 0FC5 is false.** For `S = Spec k` with `δ ≡ 0`, which satisfies
`Stacks.Chow.IsDedekindChowBase`, the canonical map `A^0(S → S) → CH_1(S)` is not injective:
`[S]₁ = 0`, so the map is zero, while the flat pullback class of the identity, the unit of
`A^0(S → S)`, caps `[S]₀` to `[S]₀ ≠ 0`. This is why
`Stacks.Chow.bivariantCapBaseFundamentalClass_bijective` assumes
`Stacks.Chow.HasNoZeroDimensionalComponent`. -/
theorem not_injective_bivariantCapBaseFundamentalClass_fieldChowSituation :
    ¬ Function.Injective (bivariantCapBaseFundamentalClass (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) (𝟙 (fieldChowSituation k).S) 0) := by
  intro hinj
  set C := fieldChowSituation k with hC
  have hr : AlgebraicGeometry.RelativeDimension (𝟙 C.S) 0 :=
    relativeDimension_of_isOpenImmersion _
  set c : BivariantClass C (gysinSystemOfInvertible C) (𝟙 C.S) (𝟙 C.S) (𝟙 C.S)
      (Category.comp_id _) 0 :=
    flatPullbackBivariantClassOfInvertible C (𝟙 C.S) (𝟙 C.S) (𝟙 C.S)
      (Category.comp_id _) 0 hr with hcdef
  have hrel : ∀ q : C.S ⟶ C.S, q = 𝟙 C.S →
      relativeDimension C.dimensionFunction q (genericPoint C.S) = 0 := by
    rintro q rfl
    exact relativeDimension_id_fieldChowSituation_eq_zero k _
  have h0 : bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) (𝟙 C.S) 0 c = 0 := by
    rw [bivariantCapBaseFundamentalClass_apply, baseFundamentalChowClass,
      fundamentalChowClass_eq_zero_of_ne C (𝟙 C.S ≫ 𝟙 C.S) (k := 1)
        (by rw [hrel _ (Category.comp_id _)]; omega), map_zero, map_zero]
  have hc : c = 0 := hinj (h0.trans (map_zero _).symm)
  have hcap := IsBivariantFlatPullback.cap_fundamentalChowClass
      (hdesc := flatPullbackDescends C)
        (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C (𝟙 C.S) (𝟙 C.S)
      (𝟙 C.S) (Category.comp_id _) 0 hr) (𝟙 C.S) 0
      (schemeDeltaDimension_fieldChowSituation_base k)
  rw [← hcdef, hc] at hcap
  have hfund : fundamentalChowClass C (𝟙 C.S) 0 = 0 := by
    have h1 := congrArg (chowPushforwardOfIso C (pullback.fst (𝟙 C.S) (𝟙 C.S) ≫ 𝟙 C.S) (𝟙 C.S)
      (pullback.fst (𝟙 C.S) (𝟙 C.S)) (by simp) _) hcap
    rw [chowPushforwardOfIso_fundamentalChowClass, BivariantClass.zero_cap, map_zero] at h1
    exact chowGroup_eq_zero_of_heq_zero C (by simp)
      ((fundamentalChowClass_heq C _ (by simp)).trans (heq_of_eq h1.symm))
  have hmem : fundamentalCycle C (𝟙 C.S) 0 ∈ rationalEquivalences C (𝟙 C.S) 0 :=
    (QuotientAddGroup.eq_zero_iff _).mp hfund
  have hzero := eq_zero_of_isRationallyEquivalentToZero_fieldChowSituation k _ hmem
  have hval : (fundamentalCycle C (𝟙 C.S) 0).1 (genericPoint C.S) =
      (0 : CycleGroup C (𝟙 C.S) 0).1 (genericPoint C.S) := by rw [hzero]
  rw [fundamentalCycle_eq_single C (𝟙 C.S) genericPoints_eq_singleton
    (hrel _ rfl) (Field.toIsField _)] at hval
  simp [Function.locallyFinsuppWithin.single_apply] at hval

end Counterexample

end Stacks.Chow

end
