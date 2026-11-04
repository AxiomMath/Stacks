module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectChernProperties
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectPowerSumChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Pushforward

/-!
# A baby case of localized Chern classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, and let `i₁ : X₁ ⟶ X`, `i₂ : X₂ ⟶ X` be closed immersions with
`X = X₁ ∪ X₂` set-theoretically. Let `E₂ ∈ D(𝒪_{X₂})` be an object whose Chern classes are
defined. If the restriction of `E₂` to `X₁ ∩ X₂ = X₁ ×_X X₂` is zero, resp. isomorphic to a
finite locally free module of rank `< p` placed in degree `0`, Stacks 0F9H constructs a bivariant
class `P'_p(E₂)`, resp. `c'_p(E₂)`, in `A^p(X₂ ⟶ X)` characterized by

  `P'_p(E₂) ∩ i_{2,*} α₂ = P_p(E₂) ∩ α₂`   and   `P'_p(E₂) ∩ i_{1,*} α₁ = 0`,

resp. the same formulas for `c'_p(E₂)` and `c_p(E₂)`, for `α_j ∈ CH_k(X_j)`, and similarly after
every base change `X' ⟶ X` locally of finite type. Each class is the extension of
`P_p(E₂) ∈ A^p(X₂)`, resp. `c_p(E₂) ∈ A^p(X₂)`, along the closed cover
(`Stacks.Chow.closedCoverExtension`); what has to be checked is that the class caps to zero on
every test scheme over `X₁ ∩ X₂`. This holds because restriction to `X₁ ∩ X₂` takes `P_p(E₂)` to
`P_p` of the zero object, which vanishes, resp. `c(E₂)` to the total Chern class of a finite
locally free module of rank `< p`, whose component of degree `p` vanishes.

Stacks 0F9I compares the classes with the classes of an object on `X`: if `E₂` is the restriction
of an object `E ∈ D(𝒪_X)` whose Chern classes are defined and whose restriction to `X₁` is zero,
resp. finite locally free of rank `< p` in degree `0`, then `i_{2,*} ∘ P'_p(E₂) = P_p(E)`, resp.
`i_{2,*} ∘ c'_p(E₂) = c_p(E)`.

## Main definitions

* `Stacks.Chow.closedCoverPowerSum` — the class `P'_p(E₂) ∈ A^p(X₂ ⟶ X)` of Stacks 0F9H.
* `Stacks.Chow.closedCoverChernClass` — the class `c'_p(E₂) ∈ A^p(X₂ ⟶ X)` of Stacks 0F9H.

## Main results

* `Stacks.Chow.TotalChowClass.vanishesOver_of_res_apply_eq_zero` — a component of a total class
  vanishes over `z : W ⟶ Y` as soon as the corresponding component of its restriction to `W` is
  zero.
* `Stacks.Chow.vanishesOver_perfectPowerSumClass_of_isZero` — `P_p(E)` vanishes over every
  `z : W ⟶ Y` along which `E` restricts to zero.
* `Stacks.Chow.vanishesOver_perfectChernClass_of_rankLT` — `c_p(E)` vanishes over every
  `z : W ⟶ Y` along which `E` restricts to a finite locally free module of rank `< p` in
  degree `0`.
* `Stacks.Chow.isClosedCoverExtension_closedCoverPowerSum`,
  `Stacks.Chow.eq_closedCoverPowerSum_of_isClosedCoverExtension`,
  `Stacks.Chow.isClosedCoverExtension_closedCoverChernClass`,
  `Stacks.Chow.eq_closedCoverChernClass_of_isClosedCoverExtension` — the characterization of
  Stacks 0F9H.
* `Stacks.Chow.properPushforwardChowCohomology_closedCoverPowerSum`,
  `Stacks.Chow.properPushforwardChowCohomology_closedCoverChernClass` — Stacks 0F9I.

## Implementation notes

The source assumes `E₂` perfect. The constructions and their properties only use that the Chern
classes of `E₂` are defined (`Stacks.Chow.HasDefinedChernClasses`), which is the input of the
classes `Stacks.Chow.perfectPowerSumComponent` and `Stacks.Chow.perfectChernClass`; perfectness is
therefore not assumed. The same applies to `E` in Stacks 0F9I, where the Chern classes of
`E₂ = E|_{X₂}` are defined because those of `E` are.

The restriction of an object to a closed subscheme is its derived pullback, and "isomorphic to a
finite locally free module of rank `< p` sitting in cohomological degree `0`" is an isomorphism
with the image under `DerivedCategory.singleFunctor _ 0` of a module satisfying
`Stacks.Chow.IsFiniteLocallyFreeOfRankLT`, as in `Stacks.Chow.LocalizedSituation`.

The structure morphism of `X₂` is an arbitrary `sX₂` with `i₂ ≫ sX = sX₂`.

## References

* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F9I](https://stacks.math.columbia.edu/tag/0F9I)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Vanishing of the classes over a closed subscheme -/

section Vanishing

variable {C : ChowSituation.{u}} {Y W : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- A component `c_p` of a total class `c ∈ ∏_p A^p(Y)` vanishes over `z : W ⟶ Y` when the
component `(z^* c)_p` of the restriction of `c` to `W` is zero. -/
theorem TotalChowClass.vanishesOver_of_res_apply_eq_zero {sW : W ⟶ C.S} [LocallyOfFiniteType sW]
    (z : W ⟶ Y) [LocallyOfFiniteType z] (hs : z ≫ sY = sW) (c : TotalChowClass C sY) (p : ℕ)
    (h : TotalChowClass.res z hs c p = 0) :
    BivariantClass.VanishesOver (c p) z := by
  subst hs
  rw [TotalChowClass.res_rfl_apply] at h
  exact (chowCohomologyRestriction_eq_zero_iff_vanishesOver C sY z (c p)).1 h

variable (C sY) in
/-- **`P_p(E)` vanishes where `E` is zero.** If the restriction of `E ∈ D(𝒪_Y)` along
`z : W ⟶ Y` is zero, then `P_p(E) ∈ A^p(Y)` caps to zero on every test scheme over `W`. -/
theorem vanishesOver_perfectPowerSumClass_of_isZero (z : W ⟶ Y) [LocallyOfFiniteType z]
    {E : DerivedCategory Y.Modules} (hE : HasDefinedChernClasses E) (p : ℕ)
    (h : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      z.toLRSHom.toShHom).obj E)) :
    BivariantClass.VanishesOver (perfectPowerSumComponent C sY hE p) z := by
  refine TotalChowClass.vanishesOver_of_res_apply_eq_zero z rfl (perfectPowerSum C sY hE p) p ?_
  rw [res_perfectPowerSum_derivedPullback C sY hE z rfl (hE.derivedPullback z),
    perfectPowerSum_of_isZero C (z ≫ sY) _ h]
  rfl

variable (C sY) in
/-- **`c_p(E)` vanishes where `E` has rank `< p`.** If the restriction of `E ∈ D(𝒪_Y)` along
`z : W ⟶ Y` is isomorphic to a finite locally free module of rank `< p` placed in degree `0`,
then `c_p(E) ∈ A^p(Y)` caps to zero on every test scheme over `W`. -/
theorem vanishesOver_perfectChernClass_of_rankLT (z : W ⟶ Y) [LocallyOfFiniteType z]
    {E : DerivedCategory Y.Modules} (hE : HasDefinedChernClasses E) (p : ℕ)
    (h : ∃ M : W.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        z.toLRSHom.toShHom).obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M)) :
    BivariantClass.VanishesOver (perfectChernClass C sY hE p) z := by
  obtain ⟨M, hM, ⟨e⟩⟩ := h
  refine TotalChowClass.vanishesOver_of_res_apply_eq_zero z rfl _ p ?_
  rw [res_perfectChernClass_derivedPullback_of_comp_eq C sY hE z rfl (hE.derivedPullback z)]
  exact perfectChernClass_apply_eq_zero_of_rankLT C (z ≫ sY) _ e hM

end Vanishing

/-! ### The classes `P'_p(E₂)` and `c'_p(E₂)` -/

section ClosedCover

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
  (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂] (hi₂ : i₂ ≫ sX = sX₂)
  {E₂ : DerivedCategory X₂.Modules} (hE₂ : HasDefinedChernClasses E₂) (p : ℕ)

/-- Let `i₁ : X₁ ⟶ X` and `i₂ : X₂ ⟶ X` be closed immersions whose images cover `X`, and let
`E₂ ∈ D(𝒪_{X₂})` have defined Chern classes and restrict to zero on `X₁ ×_X X₂`. The class
`P'_p(E₂) ∈ A^p(X₂ ⟶ X)` is the extension of `P_p(E₂) ∈ A^p(X₂)` along the closed cover
(`Stacks.Chow.closedCoverExtension`): on a test scheme `T ⟶ X`, writing a class as
`j_{1,*} α₁ + j_{2,*} α₂` along the base-changed cover, `P'_p(E₂) ∩ α = P_p(E₂) ∩ α₂`. -/
@[stacks 0F9H "the class P'_p(E₂) in A^p(X₂ ⟶ X), for E₂ restricting to zero on X₁ ∩ X₂"]
def closedCoverPowerSum (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂)) :
    BivariantClass C (gysinSystemOfInvertible C) sX₂ sX i₂ hi₂ p :=
  closedCoverExtension C sX i₁ i₂ sX₂ hi₂ (perfectPowerSumComponent C sX₂ hE₂ p) hcover
    (vanishesOver_perfectPowerSumClass_of_isZero C sX₂ (pullback.snd i₁ i₂) hE₂ p hzero)

/-- Let `i₁ : X₁ ⟶ X` and `i₂ : X₂ ⟶ X` be closed immersions whose images cover `X`, and let
`E₂ ∈ D(𝒪_{X₂})` have defined Chern classes and restrict on `X₁ ×_X X₂` to a finite locally free
module of rank `< p` in degree `0`. The class `c'_p(E₂) ∈ A^p(X₂ ⟶ X)` is the extension of
`c_p(E₂) ∈ A^p(X₂)` along the closed cover (`Stacks.Chow.closedCoverExtension`): on a test scheme
`T ⟶ X`, writing a class as `j_{1,*} α₁ + j_{2,*} α₂` along the base-changed cover,
`c'_p(E₂) ∩ α = c_p(E₂) ∩ α₂`. -/
@[stacks 0F9H "the class c'_p(E₂) in A^p(X₂ ⟶ X), for E₂ restricting on X₁ ∩ X₂ to a finite \
locally free module of rank < p in degree 0"]
def closedCoverChernClass (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (hrank : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂ ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    BivariantClass C (gysinSystemOfInvertible C) sX₂ sX i₂ hi₂ p :=
  closedCoverExtension C sX i₁ i₂ sX₂ hi₂ (perfectChernClass C sX₂ hE₂ p) hcover
    (vanishesOver_perfectChernClass_of_rankLT C sX₂ (pullback.snd i₁ i₂) hE₂ p hrank)

variable (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)

section PowerSum

variable (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂))

/-- On every test scheme `g : T ⟶ X` locally of finite type, `P'_p(E₂)` caps the classes pushed
forward from `T ×_X X₂` as `P_p(E₂)` does, and kills the classes pushed forward from `T ×_X X₁`:
`P'_p(E₂) ∩ i_{2,*} α₂ = P_p(E₂) ∩ α₂` and `P'_p(E₂) ∩ i_{1,*} α₁ = 0`. -/
@[stacks 0F9H "the two formulas P'_p(E₂) ∩ i_{2,*} α₂ = P_p(E₂) ∩ α₂ and \
P'_p(E₂) ∩ i_{1,*} α₁ = 0, after every base change"]
theorem isClosedCoverExtension_closedCoverPowerSum :
    IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂ sX₂ hi₂
      (perfectPowerSumComponent C sX₂ hE₂ p)
      (closedCoverPowerSum C sX i₁ i₂ sX₂ hi₂ hE₂ p hcover hzero) :=
  isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ sX₂ hi₂ hcover
    (vanishesOver_perfectPowerSumClass_of_isZero C sX₂ (pullback.snd i₁ i₂) hE₂ p hzero)

/-- A class of `A^p(X₂ ⟶ X)` satisfying the two formulas `c ∩ i_{2,*} α₂ = P_p(E₂) ∩ α₂` and
`c ∩ i_{1,*} α₁ = 0` after every base change is `P'_p(E₂)`. -/
@[stacks 0F9H "uniqueness: P'_p(E₂) is the only class satisfying the two formulas after every \
base change"]
theorem eq_closedCoverPowerSum_of_isClosedCoverExtension
    {c : BivariantClass C (gysinSystemOfInvertible C) sX₂ sX i₂ hi₂ p}
    (hc : IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂ sX₂ hi₂
      (perfectPowerSumComponent C sX₂ hE₂ p) c) :
    c = closedCoverPowerSum C sX i₁ i₂ sX₂ hi₂ hE₂ p hcover hzero :=
  hc.eq_closedCoverExtension hcover
    (vanishesOver_perfectPowerSumClass_of_isZero C sX₂ (pullback.snd i₁ i₂) hE₂ p hzero)

end PowerSum

section Chern

variable (hrank : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂ ≅
          (DerivedCategory.singleFunctor _ 0).obj M))

/-- On every test scheme `g : T ⟶ X` locally of finite type, `c'_p(E₂)` caps the classes pushed
forward from `T ×_X X₂` as `c_p(E₂)` does, and kills the classes pushed forward from `T ×_X X₁`:
`c'_p(E₂) ∩ i_{2,*} α₂ = c_p(E₂) ∩ α₂` and `c'_p(E₂) ∩ i_{1,*} α₁ = 0`. -/
@[stacks 0F9H "the two formulas c'_p(E₂) ∩ i_{2,*} α₂ = c_p(E₂) ∩ α₂ and \
c'_p(E₂) ∩ i_{1,*} α₁ = 0, after every base change"]
theorem isClosedCoverExtension_closedCoverChernClass :
    IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂ sX₂ hi₂
      (perfectChernClass C sX₂ hE₂ p)
      (closedCoverChernClass C sX i₁ i₂ sX₂ hi₂ hE₂ p hcover hrank) :=
  isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ sX₂ hi₂ hcover
    (vanishesOver_perfectChernClass_of_rankLT C sX₂ (pullback.snd i₁ i₂) hE₂ p hrank)

/-- A class of `A^p(X₂ ⟶ X)` satisfying the two formulas `c ∩ i_{2,*} α₂ = c_p(E₂) ∩ α₂` and
`c ∩ i_{1,*} α₁ = 0` after every base change is `c'_p(E₂)`. -/
@[stacks 0F9H "uniqueness: c'_p(E₂) is the only class satisfying the two formulas after every \
base change"]
theorem eq_closedCoverChernClass_of_isClosedCoverExtension
    {c : BivariantClass C (gysinSystemOfInvertible C) sX₂ sX i₂ hi₂ p}
    (hc : IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂ sX₂ hi₂
      (perfectChernClass C sX₂ hE₂ p) c) :
    c = closedCoverChernClass C sX i₁ i₂ sX₂ hi₂ hE₂ p hcover hrank :=
  hc.eq_closedCoverExtension hcover
    (vanishesOver_perfectChernClass_of_rankLT C sX₂ (pullback.snd i₁ i₂) hE₂ p hrank)

end Chern

end ClosedCover

/-! ### Stacks 0F9I -/

section Pushforward

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
  {E : DerivedCategory X.Modules} (hE : HasDefinedChernClasses E) (p : ℕ)

/-- If `a ∈ A^p(X₂)` is the restriction of a class `q ∈ A^p(X)` vanishing over `X₁`, then
`i_{2,*} ∘ a' = q` for the extension `a'` of `a` along the closed cover. -/
private theorem properPushforwardChowCohomology_closedCoverExtension_of_eq_restriction {p : ℤ}
    {q : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p}
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) p}
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ) (hq : BivariantClass.VanishesOver q i₁)
    (hres : a = chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) q)
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) :
    properPushforwardChowCohomology C sX (i₂ ≫ sX) i₂ rfl
      (closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl a hcover ha) = q := by
  subst hres
  exact properPushforwardChowCohomology_closedCoverExtension C sX i₁ i₂ hcover hq

/-- Let `i₁ : X₁ ⟶ X` and `i₂ : X₂ ⟶ X` be closed immersions whose images cover `X`, and let
`E ∈ D(𝒪_X)` have defined Chern classes and restrict to zero on `X₁`. Let `E₂ = E|_{X₂}` be as in
Stacks 0F9H: it restricts to zero on `X₁ ×_X X₂`, and its Chern classes are defined by
`Stacks.Chow.HasDefinedChernClasses.derivedPullback`. Then `i_{2,*} ∘ P'_p(E₂) = P_p(E)` in
`A^p(X)`, with `i_{2,*} ∘ -` the pushforward of Stacks 0EPK. -/
@[stacks 0F9I "the case of P'_p: i_{2,*} ∘ P'_p(E₂) = P_p(E) for E₂ = E|_{X₂} and E|_{X₁} zero"]
theorem properPushforwardChowCohomology_closedCoverPowerSum
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      i₁.toLRSHom.toShHom).obj E))
    (hzero₂ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj
        ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          i₂.toLRSHom.toShHom).obj E))) :
    properPushforwardChowCohomology C sX (i₂ ≫ sX) i₂ rfl
        (closedCoverPowerSum C sX i₁ i₂ (i₂ ≫ sX) rfl (hE.derivedPullback i₂) p hcover
          hzero₂) =
      perfectPowerSumComponent C sX hE p := by
  refine properPushforwardChowCohomology_closedCoverExtension_of_eq_restriction C sX i₁ i₂ hcover
    (vanishesOver_perfectPowerSumClass_of_isZero C sX i₁ hE p hzero) ?_
    (vanishesOver_perfectPowerSumClass_of_isZero C _ _ _ p hzero₂)
  unfold perfectPowerSumComponent
  rw [← TotalChowClass.res_rfl_apply,
    res_perfectPowerSum_derivedPullback C sX hE i₂ rfl (hE.derivedPullback i₂)]

/-- Let `i₁ : X₁ ⟶ X` and `i₂ : X₂ ⟶ X` be closed immersions whose images cover `X`, and let
`E ∈ D(𝒪_X)` have defined Chern classes and restrict on `X₁` to a finite locally free module of rank
`< p` in degree `0`. Let `E₂ = E|_{X₂}` be as in Stacks 0F9H: it restricts on `X₁ ×_X X₂` to a
finite locally free module of rank `< p` in degree `0`, and its Chern classes are defined by
`Stacks.Chow.HasDefinedChernClasses.derivedPullback`. Then `i_{2,*} ∘ c'_p(E₂) = c_p(E)` in
`A^p(X)`, with `i_{2,*} ∘ -` the pushforward of Stacks 0EPK. -/
@[stacks 0F9I "the case of c'_p: i_{2,*} ∘ c'_p(E₂) = c_p(E) for E₂ = E|_{X₂} and E|_{X₁} finite \
locally free of rank < p in degree 0"]
theorem properPushforwardChowCohomology_closedCoverChernClass
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (hrank : ∃ M : X₁.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        i₁.toLRSHom.toShHom).obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (hrank₂ : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.snd i₁ i₂).toLRSHom.toShHom).obj
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            i₂.toLRSHom.toShHom).obj E) ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    properPushforwardChowCohomology C sX (i₂ ≫ sX) i₂ rfl
        (closedCoverChernClass C sX i₁ i₂ (i₂ ≫ sX) rfl (hE.derivedPullback i₂) p hcover
          hrank₂) =
      perfectChernClass C sX hE p := by
  refine properPushforwardChowCohomology_closedCoverExtension_of_eq_restriction C sX i₁ i₂ hcover
    (vanishesOver_perfectChernClass_of_rankLT C sX i₁ hE p hrank) ?_
    (vanishesOver_perfectChernClass_of_rankLT C _ _ _ p hrank₂)
  rw [← TotalChowClass.res_rfl_apply,
    res_perfectChernClass_derivedPullback_of_comp_eq C sX hE i₂ rfl (hE.derivedPullback i₂)]

end Pushforward

end Stacks.Chow

end
