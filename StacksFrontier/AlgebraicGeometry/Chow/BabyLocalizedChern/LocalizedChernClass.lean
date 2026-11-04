module

public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.ClosedCoverClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectPowerSum
public import StacksCore.Tactic.StacksAttribute

/-!
# The localized Chern classes of a closed cover

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i_j : X_j ⟶ X` (`j = 1, 2`) be closed immersions with
`X = X₁ ∪ X₂` set theoretically, and let `E₂ ∈ D(𝒪_{X₂})` be a perfect object whose Chern classes
are defined (Stacks 0F9E). If `E₂|_{X₁ ∩ X₂}` is isomorphic to a finite locally free
`𝒪_{X₁ ∩ X₂}`-module of rank `< p` sitting in cohomological degree `0`, respectively zero,
**Stacks 0F9H** produces a canonical bivariant class `c'_p(E₂)`, respectively
`P'_p(E₂) ∈ A^p(X₂ ⟶ X)`, characterized by

  `c'_p(E₂) ∩ i_{2,*} α₂ = c_p(E₂) ∩ α₂`  and  `c'_p(E₂) ∩ i_{1,*} α₁ = 0`

(respectively with `P'_p`, `P_p`) for `α_i ∈ CH_k(X_i)`, and similarly after any base change
`X' ⟶ X` locally of finite type.

The proof is the source's: `c_p(E₂|_{X₁ ∩ X₂}) = 0` by rank considerations, respectively
`P_p(E₂|_{X₁ ∩ X₂}) = 0` when `E₂|_{X₁ ∩ X₂}` is zero, and the class is the localized class
`Stacks.Chow.closedCoverLocalizedClass` of `κ = c_p(E₂)`, respectively `κ = P_p(E₂)`: on a test
scheme `X' ⟶ X` every class is `i'_{1,*} α₁ + i'_{2,*} α₂` (Stacks 0F94) and the class sends it
to `κ ∩ α₂`.

## Main definitions

* `Stacks.Chow.localizedChernClassOfClosedCover` — the class `c'_p(E₂) ∈ A^p(X₂ ⟶ X)`.
* `Stacks.Chow.localizedPowerSumOfClosedCover` — the class `P'_p(E₂) ∈ A^p(X₂ ⟶ X)`.

## Main results

* `Stacks.Chow.existsUnique_localizedChernClassOfClosedCover` — **Stacks 0F9H** for `c'_p`.
* `Stacks.Chow.existsUnique_localizedPowerSumOfClosedCover` — **Stacks 0F9H** for `P'_p`.

## Implementation notes

The cover is given by two closed immersions `i_j : X_j ⟶ X` with the images covering `X`; the
scheme-theoretic intersection `X₁ ∩ X₂` is the fibre product `X₁ ×_X X₂`, and `E₂|_{X₁ ∩ X₂}` is
the derived pullback along its projection to `X₂`. The base change of `X_j` along a test scheme
`g : X' ⟶ X` is the chosen fibre product `X_j ×_X X'`, and `c_p(E₂) ∩ α₂` for
`α₂ ∈ CH_k(X'_2)` is the operation of the Chow cohomology class `c_p(E₂) ∈ A^p(X₂)` on the test
scheme `X'_2 ⟶ X₂` (`Stacks.Chow.BivariantClass.idRule`). The structure morphisms of `X_j` over
`S` are `i_j ≫ sX`. Bivariant classes are taken at the Gysin system of the first Chern class of an
invertible module, `Stacks.Chow.gysinSystemOfInvertible`, the Gysin map of chapter 42.

The hypothesis that `E₂` is perfect is not used for `c'_p`: the Chern classes of an object whose
Chern classes are defined (Stacks 0F9E (1)) make sense without it. It is used for `P'_p`, where
`P_0(E₂)` is the rank of `E₂`.

## References

* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The localized Chern classes of a closed cover -/

section LocalizedChern

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i₁ : X₁ ⟶ X) [IsClosedImmersion i₁] (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂]
  (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
  {E₂ : DerivedCategory X₂.Modules} (hE₂ : HasDefinedChernClasses E₂) (p : ℕ)

/-- **`c_p(E₂)` vanishes on `X₁ ∩ X₂`**: if `E₂|_{X₁ ∩ X₂}` is isomorphic to a finite locally
free module of rank `< p` in degree `0`, the restriction of `c_p(E₂)` to `X₁ ∩ X₂` is
`c_p(E₂|_{X₁ ∩ X₂}) = 0`. -/
theorem chowCohomologyRestriction_perfectChernClass_eq_zero (M : (pullback i₁ i₂).Modules)
    (hM : IsFiniteLocallyFreeOfRankLT M p)
    (e : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂ ≅
      (DerivedCategory.singleFunctor (pullback i₁ i₂).Modules 0).obj M) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) (i₂ ≫ sX) (pullback.snd i₁ i₂)
      (p : ℤ) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (perfectChernClass C (i₂ ≫ sX) hE₂ p) = 0 := by
  rw [← TotalChowClass.res_rfl_apply, res_perfectChernClass_derivedPullback C (i₂ ≫ sX)
    (pullback.snd i₁ i₂) hE₂ (hasDefinedChernClasses_of_derivedPullback _ _ _ hE₂ (Iso.refl _))]
  exact perfectChernClass_apply_eq_zero_of_iso_single C _ _ M hM e

/-- **The localized Chern class `c'_p(E₂) ∈ A^p(X₂ ⟶ X)` of Stacks 0F9H**, for a set-theoretic
cover `X = X₁ ∪ X₂` by closed subschemes and an object `E₂` of `D(𝒪_{X₂})` whose Chern classes
are defined and whose restriction to `X₁ ∩ X₂` is a finite locally free module of rank `< p` in
degree `0`: on a test scheme `X' ⟶ X` it sends `i'_{1,*} α₁ + i'_{2,*} α₂` to `c_p(E₂) ∩ α₂`. -/
def localizedChernClassOfClosedCover
    (hres : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂ ≅
        (DerivedCategory.singleFunctor (pullback i₁ i₂).Modules 0).obj M)) :
    BivariantClass C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl (p : ℤ) :=
  closedCoverLocalizedClass C sX (i₁ ≫ sX) (i₂ ≫ sX) i₁ rfl i₂ rfl hcover
    (perfectChernClass C (i₂ ≫ sX) hE₂ p)
    (by
      obtain ⟨M, hM, ⟨e⟩⟩ := hres
      exact chowCohomologyRestriction_perfectChernClass_eq_zero C sX i₁ i₂ hE₂ p M hM e)

include hcover in
/-- **Stacks 0F9H, for the Chern classes.** Let `X` be locally of finite type over `S`, let
`i_j : X_j ⟶ X` be closed immersions with `X = X₁ ∪ X₂` set theoretically, and let `E₂` be a
perfect object of `D(𝒪_{X₂})` whose Chern classes are defined and such that `E₂|_{X₁ ∩ X₂}` is
isomorphic to a finite locally free `𝒪_{X₁ ∩ X₂}`-module of rank `< p` sitting in cohomological
degree `0`. Then there is a unique bivariant class `c'_p(E₂) ∈ A^p(X₂ ⟶ X)` such that, on every
test scheme `g : X' ⟶ X` locally of finite type, with `i'_j : X'_j = X_j ×_X X' ⟶ X'`,

  `c'_p(E₂) ∩ i'_{2,*} α₂ = c_p(E₂) ∩ α₂`  and  `c'_p(E₂) ∩ i'_{1,*} α₁ = 0`

for all `α_j ∈ CH_k(X'_j)`; it is `Stacks.Chow.localizedChernClassOfClosedCover`. -/
@[stacks 0F9H "the class c'_p(E₂) ∈ A^p(X₂ ⟶ X), existence and uniqueness of the bivariant class \
characterized by the two identities on every base change X' ⟶ X, for E₂|_{X₁ ∩ X₂} finite \
locally free of rank < p in degree 0"]
theorem existsUnique_localizedChernClassOfClosedCover
    (_perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X₂.toRingedSpace) E₂)
    (hres : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂ ≅
        (DerivedCategory.singleFunctor (pullback i₁ i₂).Modules 0).obj M)) :
    ∃! c : BivariantClass C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl (p : ℤ),
      (∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
        (α : chowGroup C (pullback.fst i₂ g ≫ i₂ ≫ sX) k),
        c.cap g k (chowPush C (pullback.fst i₂ g ≫ i₂ ≫ sX) (g ≫ sX) (pullback.snd i₂ g)
            (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl g) k α) =
          (perfectChernClass C (i₂ ≫ sX) hE₂ p).idRule C (i₂ ≫ sX) (gysinSystemOfInvertible C)
            (pullback.fst i₂ g) k α) ∧
      (∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
        (α : chowGroup C (pullback.fst i₁ g ≫ i₁ ≫ sX) k),
        c.cap g k (chowPush C (pullback.fst i₁ g ≫ i₁ ≫ sX) (g ≫ sX) (pullback.snd i₁ g)
            (pullbackSnd_comp_structureMorphism_eq C (i₁ ≫ sX) sX i₁ rfl g) k α) = 0) :=
  ⟨localizedChernClassOfClosedCover C sX i₁ i₂ hcover hE₂ p hres,
    ⟨fun g _ k α ↦ closedCoverLocalizedClass_cap_pushforward_right C sX _ _ i₁ rfl i₂ rfl hcover _
      _ g k α,
    fun g _ k α ↦ closedCoverLocalizedClass_cap_pushforward_left C sX _ _ i₁ rfl i₂ rfl hcover _
      _ g k α⟩,
    fun c hc ↦ eq_closedCoverLocalizedClass C sX _ _ i₁ rfl i₂ rfl hcover _ _ c hc.1 hc.2⟩

/-- **The localized class `P'_p(E₂) ∈ A^p(X₂ ⟶ X)` of Stacks 0F9H**, for a set-theoretic cover
`X = X₁ ∪ X₂` by closed subschemes and a perfect object `E₂` of `D(𝒪_{X₂})` whose Chern classes
are defined and whose restriction to `X₁ ∩ X₂` is zero: on a test scheme `X' ⟶ X` it sends
`i'_{1,*} α₁ + i'_{2,*} α₂` to `P_p(E₂) ∩ α₂`. -/
def localizedPowerSumOfClosedCover
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X₂.toRingedSpace) E₂)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂)) :
    BivariantClass C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl (p : ℤ) :=
  closedCoverLocalizedClass C sX (i₁ ≫ sX) (i₂ ≫ sX) i₁ rfl i₂ rfl hcover
    (perfectPowerSumComponent C (i₂ ≫ sX) hE₂ p)
    (chowCohomologyRestriction_perfectPowerSumComponent_eq_zero C (i₂ ≫ sX) perfect hE₂
      (pullback.snd i₁ i₂) hzero p)

include hcover in
/-- **Stacks 0F9H, for the classes `P_p`.** Let `X` be locally of finite type over `S`, let
`i_j : X_j ⟶ X` be closed immersions with `X = X₁ ∪ X₂` set theoretically, and let `E₂` be a
perfect object of `D(𝒪_{X₂})` whose Chern classes are defined and whose restriction
`E₂|_{X₁ ∩ X₂}` is zero. Then there is a unique bivariant class `P'_p(E₂) ∈ A^p(X₂ ⟶ X)` such
that, on every test scheme `g : X' ⟶ X` locally of finite type, with
`i'_j : X'_j = X_j ×_X X' ⟶ X'`,

  `P'_p(E₂) ∩ i'_{2,*} α₂ = P_p(E₂) ∩ α₂`  and  `P'_p(E₂) ∩ i'_{1,*} α₁ = 0`

for all `α_j ∈ CH_k(X'_j)`; it is `Stacks.Chow.localizedPowerSumOfClosedCover`. Here `P_p(E₂)` is
the class of Definition 0F9E (2), `Stacks.Chow.perfectPowerSumComponent`: the class of Stacks 0GUD
which restricts along every envelope presentation `(f, 𝓔^•)` of `E₂` to `∑ (-1)^n P_p(𝓔^n)`
(`Stacks.Chow.existsUnique_perfectPowerSum`). -/
@[stacks 0F9H "the class P'_p(E₂) ∈ A^p(X₂ ⟶ X), existence and uniqueness of the bivariant class \
characterized by the two identities on every base change X' ⟶ X, for E₂|_{X₁ ∩ X₂} zero"]
theorem existsUnique_localizedPowerSumOfClosedCover
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X₂.toRingedSpace) E₂)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂)) :
    ∃! c : BivariantClass C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl (p : ℤ),
      (∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
        (α : chowGroup C (pullback.fst i₂ g ≫ i₂ ≫ sX) k),
        c.cap g k (chowPush C (pullback.fst i₂ g ≫ i₂ ≫ sX) (g ≫ sX) (pullback.snd i₂ g)
            (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl g) k α) =
          (perfectPowerSumComponent C (i₂ ≫ sX) hE₂ p).idRule C (i₂ ≫ sX)
            (gysinSystemOfInvertible C) (pullback.fst i₂ g) k α) ∧
      (∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
        (α : chowGroup C (pullback.fst i₁ g ≫ i₁ ≫ sX) k),
        c.cap g k (chowPush C (pullback.fst i₁ g ≫ i₁ ≫ sX) (g ≫ sX) (pullback.snd i₁ g)
            (pullbackSnd_comp_structureMorphism_eq C (i₁ ≫ sX) sX i₁ rfl g) k α) = 0) :=
  ⟨localizedPowerSumOfClosedCover C sX i₁ i₂ hcover hE₂ p perfect hzero,
    ⟨fun g _ k α ↦ closedCoverLocalizedClass_cap_pushforward_right C sX _ _ i₁ rfl i₂ rfl hcover _
      _ g k α,
    fun g _ k α ↦ closedCoverLocalizedClass_cap_pushforward_left C sX _ _ i₁ rfl i₂ rfl hcover _
      _ g k α⟩,
    fun c hc ↦ eq_closedCoverLocalizedClass C sX _ _ i₁ rfl i₂ rfl hcover _ _ c hc.1 hc.2⟩

end LocalizedChern

end Stacks.Chow

end
