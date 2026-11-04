module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.BaseDegreeSheafAffine
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.BaseDegreeSheafNaturality

/-!
# `R⁰ f_* 𝒪(d) = (𝒪_S[T₀, …, Tₙ])_d` on projective space over an arbitrary base

Let `S` be a scheme, let `n` be a natural number, let `d` be an integer and let
`f : ℙⁿ_S ⟶ S` be the structure morphism of projective `n`-space over `S`. The canonical
morphism of `𝒪_S`-modules

`(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)`

of `Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.toPushforwardTwistOver` is an
isomorphism, and so is its composite with the comparison `R⁰ f_* ≅ f_*`, in every degree `d`
with `0 ≤ d` and, as soon as `n ≥ 1`, in every integer degree. No hypothesis is placed on `S`.

The names in the lists below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace.

## Main definitions

* `baseDegreeSheafIsoPushforwardTwistOver`: **`(𝒪_S[T₀, …, Tₙ])_d ≅ f_* 𝒪(d)`**, the canonical
  morphism read as an isomorphism.
* `baseDegreeSheafIsoRightDerivedPushforwardTwistOver`:
  **`(𝒪_S[T₀, …, Tₙ])_d ≅ R⁰ f_* 𝒪(d)`**, the same isomorphism followed by the comparison
  `R⁰ f_* ≅ f_*` of [Stacks, Tag 05TD] (3).

## Main results

* `isIso_pullback_map_toPushforwardTwistOver_iff`: along a flat `g : S' ⟶ S` the inverse image
  of the canonical morphism for `S` is invertible exactly when the canonical morphism for `S'`
  is.
* `isIso_toPushforwardTwistOver`: **the canonical morphism is an isomorphism** over an arbitrary
  scheme `S`, for every `n` and every `d` with `0 ≤ d` or `n ≥ 1`.
* `isIso_toPushforwardTwistOver_of_nonneg` and `isIso_toPushforwardTwistOver_of_pos`: the same,
  with the hypothesis in each of its two forms.

## The mathematics

The assertion is local on `S` and stable under flat base change, and over a spectrum it is
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.isIso_toPushforwardTwistOver_spec`.

Base change along a flat morphism `g : S' ⟶ S` compares the two canonical morphisms:
`toPushforwardTwistOver_baseChange` writes the inverse image along `g` of the morphism for `S`,
followed by the base-change morphism `g^* f_* ⟶ f'_* p^*` and the base-change isomorphism of the
twists, as the morphism for `S'` read through the base-change isomorphism of
`(𝒪_S[T₀, …, Tₙ])_d`. For `g` flat the base-change morphism is invertible — this is
[Stacks, Tag 02KH] part (1) in degree zero,
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`, whose
hypotheses on `f` hold because `ℙⁿ_S ⟶ S` is proper — and the other two factors are invertible
outright, so invertibility passes both ways between the two sides.

Two instances of this suffice. An affine scheme `W` is the spectrum of its global sections, and
an isomorphism of schemes is flat, so the morphism over `W` is invertible as soon as the morphism
over `Spec Γ(W, ⊤)` is. An open immersion is flat, so the morphism for `S` becomes invertible
after inverse image along the inclusion of each affine open `V` of `S`; inverse image along an
open immersion is restriction, and invertibility of a morphism of sheaves of modules is local on
the scheme by `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`.

The degree-`n` row of the display of [Stacks, Tag 01XW] shows that `n ≥ 1` cannot be dropped at
a negative twist: on `ℙ⁰_S = S` the degrees `q = 0` and `q = n` of the display coincide, the
twist `𝒪(d)` is `𝒪_S` in every degree, and the degree-`d` part of `𝒪_S[T₀]` is zero for `d < 0`.

## Implementation notes

The structure morphism of `ℙⁿ_S` is a projection out of a fibre product, and
`AlgebraicGeometry.isPullback_projectiveSpaceOverMap` states the cartesian square at that
spelling; the quasi-compactness and quasi-separatedness instances are found at the spelling
`projectiveSpaceOver n S ↘ S` and are transported with `inferInstanceAs`.

`HasDerivedCategory.standard` is installed at priority `2000`, as in
`StacksFrontier/AlgebraicGeometry/ProjectiveSpaceHigherDirectImage/MiddleVanishing.lean`, so that
the statement about `CategoryTheory.Functor.rightDerivedPlus` below is in the same model as the
vanishing row of the display; at the default priority the globally declared locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` is preferred instead and the two rows do
not compose.

**No `stacks` attribute is attached.** The display of [Stacks, Tag 01XW] has three rows, of
which this is one; the vanishing row is
`StacksFrontier/AlgebraicGeometry/ProjectiveSpaceHigherDirectImage/MiddleVanishing.lean`, the
degree-`n` row is `…/TopDegreeRowGeneral.lean`, and the three rows in one statement, at `n ≥ 1`,
are `…/Display.lean`.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.AffinePushforward
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

/-! ### Flat base change for the canonical morphism -/

/-- **Base change for the degree-zero comparison of [Stacks, Tag 02KH] at the twists of
projective space.** For every `g : S' ⟶ S` the base-change morphism `g^* f_* ⟶ f'_* p^*` is
invertible at `𝒪(d)` as soon as `g` is flat: the structure morphism of `ℙⁿ_S` is proper, hence
quasi-compact and quasi-separated, and `𝒪(d)` is quasi-coherent. -/
theorem isIso_baseChangeNatTrans_twistOver (n : ℕ) {S' S : Scheme.{u}} (g : S' ⟶ S) [Flat g]
    (d : ℤ) :
    IsIso ((baseChangeNatTrans (projectiveSpaceOverMap_comp n g)).app (twistOver n S d)) := by
  have : QuasiCompact (pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n))) :=
    inferInstanceAs (QuasiCompact (projectiveSpaceOver n S ↘ S))
  have : QuasiSeparated (pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n))) :=
    inferInstanceAs (QuasiSeparated (projectiveSpaceOver n S ↘ S))
  exact Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat
    (isPullback_projectiveSpaceOverMap n g) (twistOver n S d)

/-- **Invertibility of the canonical morphism `(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)` passes both ways
along a flat base change.** -/
theorem isIso_pullback_map_toPushforwardTwistOver_iff (n : ℕ) {S' S : Scheme.{u}} (g : S' ⟶ S)
    [Flat g] (d : ℤ) :
    IsIso ((Scheme.Modules.pullback g).map (toPushforwardTwistOver n S d)) ↔
      IsIso (toPushforwardTwistOver n S' d) := by
  have := isIso_baseChangeNatTrans_twistOver n g d
  rw [← isIso_comp_right_iff _ ((baseChangeNatTrans (projectiveSpaceOverMap_comp n g)).app
      (twistOver n S d) ≫ (Scheme.Modules.pushforward (projectiveSpaceOver n S' ↘ S')).map
        (twistOverPullbackIso n g d).hom), toPushforwardTwistOver_baseChange n g d,
    isIso_comp_left_iff]

/-! ### From a spectrum to an arbitrary base -/

/-- **The canonical morphism `(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)` is an isomorphism over an affine
scheme**, in every degree `d` with `0 ≤ d` and, when `n ≥ 1`, in every degree: an affine scheme
is the spectrum of its global sections. -/
theorem isIso_toPushforwardTwistOver_of_isAffine (n : ℕ) (W : Scheme.{u}) [IsAffine W] {d : ℤ}
    (hd : 0 ≤ d ∨ 0 < n) : IsIso (toPushforwardTwistOver n W d) := by
  have : IsIso (toPushforwardTwistOver n (Spec Γ(W, ⊤)) d) :=
    isIso_toPushforwardTwistOver_spec ↥(Γ(W, ⊤)) n hd
  exact (isIso_pullback_map_toPushforwardTwistOver_iff n W.isoSpec.hom d).1
    (Functor.map_isIso _ _)

/-- **The canonical morphism `(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)` is an isomorphism**, over an
arbitrary scheme `S`, for every `n` and every degree `d` with `0 ≤ d` and, when `n ≥ 1`, in
every degree.

This is the degree-zero row of the display of [Stacks, Tag 01XW] for the underived direct
image. -/
theorem isIso_toPushforwardTwistOver (n : ℕ) (S : Scheme.{u}) {d : ℤ} (hd : 0 ≤ d ∨ 0 < n) :
    IsIso (toPushforwardTwistOver n S d) := by
  classical
  have hcov : ∀ y : S, ∃ V : S.Opens, y ∈ V ∧ IsAffineOpen V := fun y => by
    obtain ⟨-, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (show y ∈ ((⊤ : S.Opens) : Set S) from trivial) (⊤ : S.Opens).isOpen
    exact ⟨V, hyV, hV⟩
  choose V hmem haff using hcov
  have hV : IsOpenCover V :=
    IsOpenCover.mk (eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hmem y⟩)
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict _ V hV fun i => ?_
  have : IsAffine (V i).toScheme := haff i
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback (V i).ι) _).2
    ((isIso_pullback_map_toPushforwardTwistOver_iff n (V i).ι d).2
      (isIso_toPushforwardTwistOver_of_isAffine n (V i).toScheme hd))

/-- **`f_* 𝒪(d) = (𝒪_S[T₀, …, Tₙ])_d` at a nonnegative twist**, over an arbitrary scheme `S`
and for every `n`. -/
theorem isIso_toPushforwardTwistOver_of_nonneg (n : ℕ) (S : Scheme.{u}) {d : ℤ} (hd : 0 ≤ d) :
    IsIso (toPushforwardTwistOver n S d) :=
  isIso_toPushforwardTwistOver n S (Or.inl hd)

/-- **`f_* 𝒪(d) = (𝒪_S[T₀, …, Tₙ])_d` in every integer degree**, over an arbitrary scheme `S`
and for every `n ≥ 1`. -/
theorem isIso_toPushforwardTwistOver_of_pos (n : ℕ) (hn : 0 < n) (S : Scheme.{u}) (d : ℤ) :
    IsIso (toPushforwardTwistOver n S d) :=
  isIso_toPushforwardTwistOver n S (Or.inr hn)

/-- **`(𝒪_S[T₀, …, Tₙ])_d ≅ f_* 𝒪(d)`**, the canonical morphism read as an isomorphism. -/
def baseDegreeSheafIsoPushforwardTwistOver (n : ℕ) (S : Scheme.{u}) {d : ℤ}
    (hd : 0 ≤ d ∨ 0 < n) :
    baseDegreeSheaf n S d ≅
      (Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).obj (twistOver n S d) :=
  @asIso _ _ _ _ (toPushforwardTwistOver n S d) (isIso_toPushforwardTwistOver n S hd)

/-! ### The right derived direct image in degree zero -/

section Derived

attribute [local instance 2000] HasDerivedCategory.standard

/-- **`(𝒪_S[T₀, …, Tₙ])_d ≅ R⁰ f_* 𝒪(d)`**, the degree-zero row of the display of
[Stacks, Tag 01XW]: the canonical morphism of `baseDegreeSheafIsoPushforwardTwistOver` followed
by the comparison `R⁰ f_* ≅ f_*` of [Stacks, Tag 05TD] (3). -/
def baseDegreeSheafIsoRightDerivedPushforwardTwistOver (n : ℕ) (S : Scheme.{u}) {d : ℤ}
    (hd : 0 ≤ d ∨ 0 < n) :
    baseDegreeSheaf n S d ≅
      ((Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).rightDerivedPlus 0).obj
        (twistOver n S d) :=
  baseDegreeSheafIsoPushforwardTwistOver n S hd ≪≫
    (Stacks.AlgebraicGeometry.HigherDirectImage.higherDirectImageZeroIso
      (projectiveSpaceOver n S ↘ S) (twistOver n S d)).symm

end Derived

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
