module

public import StacksFrontier.AlgebraicGeometry.SectionPowerCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.MayerVietorisStep

/-!
# Tag 01XR in general, from the twisted localization of Tag 09MR

Let `X` be a quasi-compact quasi-separated scheme, `ℒ` an invertible `𝒪_X`-module, `s` a global
section of `ℒ` whose nonvanishing open `X_s` is affine, and `ℱ` a quasi-coherent `𝒪_X`-module.
[Stacks, Tag 01XR] says that every cohomology class of `ℱ` in a positive degree is annihilated
by a power of `s`. This file proves it.

## Main results

* `Stacks.SheafOfModules.exists_mulPow_eq_zero_of_isAffineOpen_nonvanishingOpen`: **the
  conclusion in the `mulPow` spelling** — some `s^k` kills the class, where multiplication by
  `s^k` is `Stacks.Cohomology.TwistedLocalizationMap.mulPow`.
* `Stacks.SheafOfModules.exists_sectionPowerAction_eq_zero_of_isAffineOpen_nonvanishingOpen`:
  **[Stacks, Tag 01XR]**, in the `IsSectionPowerHom` spelling of
  `./Basic.lean`, which quantifies over the morphisms `𝒪_X ⟶ ℒ^{⊗ k}` representing `s^k`.

## The argument

`./Basic.lean` records that a positive-degree class restricts to zero on the affine open `X_s`,
and proves the tag only where the cohomology group itself vanishes. What was missing is the
step from "restricts to zero" to "is killed by a power of `s`", and that step is exactly the
injectivity half of [Stacks, Tag 09MR] read on numerators:
`Stacks.Cohomology.TwistedLocalizationMap.RestrictKernelTorsion`, which says that a class of
`H^p(X, ℱ ⊗ ℒ^{⊗ n})` dying on `X ⊓ X_s` is killed by some `s^k`. That statement is proved for
every quasi-compact open of a quasi-separated scheme as
`Stacks.Cohomology.TwistedLocalizationMap.restrictNumerators_of_isCompact`.

The class `ξ` of `H^p(X, ℱ)` is pushed into the twist of degree zero as `mulPow … 0 ξ`, which is
the image of `ξ` under multiplication by `s⁰`. Its restriction to `X ⊓ X_s` lies in
`H^p(X ⊓ X_s, ℱ ⊗ ℒ^{⊗ 0})`, and that group vanishes: `X ⊓ X_s` is `X_s`, which is affine by
hypothesis, and the twist of a quasi-coherent module is quasi-coherent, so the positive-degree
vanishing of [Stacks, Tag 01XB] applies. The numerator statement then produces a `k` with
`s^k · (s⁰ · ξ) = 0`, and
`Stacks.Cohomology.TwistedLocalizationMap.actPow_mulPow` telescopes the two multiplications into
`s^{k + 0} · ξ = 0`.

## Implementation notes

**[Stacks, Tag 09MR] is available.** The general case reduces by [Stacks, Tag 01XB] to
[Stacks, Tag 09MR], which is proved, over every quasi-compact open of a
quasi-separated scheme, as
`Stacks.Cohomology.TwistedLocalizationMap.bijective_canonicalMap_of_isCompact`. Only the
numerator half of it is used here, so the localization itself never appears in this file.

**The affineness of `X ⊓ X_s`** is `top_inf_eq` applied to the hypothesis on `X_s`;
`Stacks.Cohomology.TwistedLocalizationMap.nonvanishingPart X L s ⊤` is `⊤ ⊓ X_s` by definition
and the two opens are equal, not merely isomorphic, so the vanishing transports by rewriting.

**The two spellings of the multiplying morphism agree definitionally.**
`Stacks.Cohomology.TwistedLocalizationMap.twistHom X L s F k` is
`sectionPowerAction … L F k (sectionPowerHom … L s k)`, so the `mulPow` conclusion is the
`IsSectionPowerHom` conclusion at the canonical representative `sectionPowerHom`.

## References

* [Stacks Project, Tag 01XR](https://stacks.math.columbia.edu/tag/01XR)
* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open Stacks.Cohomology Stacks.Cohomology.TwistedGradedModule
open Stacks.Cohomology.TwistedLocalizationMap

universe u

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

variable (X : Scheme.{u}) (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property L]
  (s : L.sections) (F : X.Modules) [F.IsQuasicoherent]

/-- **The degree-zero twist of the ambient open is `X_s` itself.** `nonvanishingPart X L s ⊤` is
`⊤ ⊓ X_s` by definition. -/
theorem nonvanishingPart_top : nonvanishingPart X L s ⊤ = nonvanishingOpen L s :=
  top_inf_eq _

/-- **The cohomology of a twist of `ℱ` on `X ⊓ X_s` vanishes in positive degree** when `X_s` is
affine, the twist of a quasi-coherent module being quasi-coherent. -/
theorem isZero_hgroup_twist_nonvanishingPart_top
    (hU : IsAffineOpen (nonvanishingOpen L s)) (p : ℕ) (hp : 0 < p) (j : ℤ) :
    IsZero (Hgroup X.ringCatSheaf (nonvanishingPart X L s ⊤) p (twist X L F j)) := by
  rw [nonvanishingPart_top X L s]
  exact Stacks.Cohomology.TwistedLocalization.isZero_hgroup_twistedModule_of_isAffineOpen
    X L F (nonvanishingOpen L s) hU p hp j

/-- Restriction of any twisted class to `X ⊓ X_s` is zero when `X_s` is affine. -/
private theorem restrictTwist_eq_zero_of_isAffineOpen (hU : IsAffineOpen (nonvanishingOpen L s))
    (p : ℕ) (hp : 0 < p) (j : ℤ) (ξ : gradedPiece X L F p ⊤ j) :
    (ConcreteCategory.hom (restrictTwist X L s F p ⊤ j)) ξ = 0 := by
  have hsub : Subsingleton
      (Hgroup X.ringCatSheaf (nonvanishingPart X L s ⊤) p (twist X L F j) : Type u) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp
      (isZero_hgroup_twist_nonvanishingPart_top X L s F hU p hp j)
  exact Subsingleton.elim _ _

/-- **[Stacks, Tag 01XR] on a twist, in the graded spelling.** On a quasi-compact quasi-separated
scheme with `X_s` affine, every positive-degree cohomology class of the `n`-th twist of a
quasi-coherent module is killed by some power of `s`, multiplication by `s^k` carrying
`H^p(X, ℱ ⊗ ℒ^{⊗ n})` into `H^p(X, ℱ ⊗ ℒ^{⊗ (k + n)})`.

This is the form the vanishing arguments on a curve consume, and it is the numerator statement
of [Stacks, Tag 09MR] with its hypothesis discharged: the restriction of any class to `X ⊓ X_s`
lands in a group that vanishes, because that open is affine and the twist is quasi-coherent. -/
theorem exists_actPow_eq_zero_of_isAffineOpen_nonvanishingOpen [CompactSpace X]
    [QuasiSeparatedSpace X] (hU : IsAffineOpen (nonvanishingOpen L s)) (p : ℕ) (hp : 0 < p)
    (n : ℕ) (ξ : gradedPiece X L F p ⊤ (n : ℤ)) :
    ∃ k : ℕ, actPow X L s F p ⊤ k n ξ = 0 := by
  exact (restrictNumerators_of_isCompact X L s F ⊤
    (by rw [Opens.coe_top]; exact isCompact_univ) p).1 n ξ
    (restrictTwist_eq_zero_of_isAffineOpen X L s F hU p hp _ ξ)

/-- **[Stacks, Tag 01XR] in the `mulPow` spelling.** On a quasi-compact quasi-separated scheme,
if the nonvanishing open `X_s` of a global section `s` of an invertible module `ℒ` is affine,
then every positive-degree cohomology class of a quasi-coherent module is killed by some power
of `s`.

The class is pushed into the degree-zero twist, where it restricts to zero on the affine
`X ⊓ X_s`; the injectivity half of [Stacks, Tag 09MR], read on numerators, then produces the
power, and `actPow_mulPow` telescopes the two multiplications into one. -/
theorem exists_mulPow_eq_zero_of_isAffineOpen_nonvanishingOpen [CompactSpace X]
    [QuasiSeparatedSpace X] (hU : IsAffineOpen (nonvanishingOpen L s)) (p : ℕ) (hp : 0 < p)
    (ξ : (Hgroup X.ringCatSheaf ⊤ p F : Type u)) :
    ∃ k : ℕ, mulPow X L s F p ⊤ k ξ = 0 := by
  obtain ⟨k, hk⟩ := (restrictNumerators_of_isCompact X L s F ⊤
    (by rw [Opens.coe_top]; exact isCompact_univ) p).1 0 (mulPow X L s F p ⊤ 0 ξ)
    (restrictTwist_eq_zero_of_isAffineOpen X L s F hU p hp _ _)
  -- `k + 0` reduces to `k`, so the telescoped exponent needs no transport.
  exact ⟨k, (actPow_mulPow X L s F p ⊤ k 0 ξ).symm.trans hk⟩

/-- **[Stacks, Tag 01XR].** Let `X` be a quasi-compact quasi-separated scheme, `ℒ` an invertible
`𝒪_X`-module and `s ∈ Γ(X, ℒ)` a global section whose nonvanishing open `X_s` is affine. Then
every cohomology class of a quasi-coherent `𝒪_X`-module in a positive degree is annihilated by
some power of `s`.

This is the general case; `./Basic.lean` has the two cases in which the cohomology group itself
vanishes. The conclusion quantifies over the morphisms `𝒪_X ⟶ ℒ^{⊗ k}` representing `s^k`, as
those statements do, and is witnessed by the canonical representative
`Stacks.SheafOfModules.sectionPowerHom`. -/
@[stacks 01XR]
theorem exists_sectionPowerAction_eq_zero_of_isAffineOpen_nonvanishingOpen [CompactSpace X]
    [QuasiSeparatedSpace X] (hU : IsAffineOpen (nonvanishingOpen L s)) (p : ℕ) (hp : 0 < p)
    (ξ : (Hgroup X.ringCatSheaf ⊤ p F : Type u)) :
    ∃ (n : ℕ) (t : SheafOfModules.unit X.ringCatSheaf ⟶
        TensorPower.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L n),
      IsSectionPowerHom X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L s n t ∧
        (Hfunctor X.ringCatSheaf ⊤ p).map
          (sectionPowerAction X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L F n t) ξ = 0 := by
  obtain ⟨k, hk⟩ :=
    exists_mulPow_eq_zero_of_isAffineOpen_nonvanishingOpen X L s F hU p hp ξ
  exact ⟨k, sectionPowerHom X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L s k,
    isSectionPowerHom_sectionPowerHom X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L s k, hk⟩

end Stacks.SheafOfModules

end
