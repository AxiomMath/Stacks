module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import StacksFrontier.AlgebraicGeometry.GradedLocalization.ModuleMaps

/-!
# Degree-zero localizations at a representative fraction

`ProjectiveSpectrum.isLocalizedModule_degreeZeroMap` exhibits `M₍g₎` as the localization of
`M₍f₎` at the single fraction `g ^ deg f / f ^ deg g`. On an affine chart `D₊(f) = Spec A₍f₎`
the standard opens are cut out by arbitrary degree-zero fractions `a / f ^ n`, and the
localizing element above is the `deg f`-th power of that fraction when `g = a * f`. Since a
localization away from a positive power of an element is a localization away from the element,
this gives the localization statement at `a / f ^ n` itself.

## Main results

* `ProjectiveSpectrum.isLocalizedModule_away_of_pow`: a localization away from `r ^ n` with
  `n ≠ 0` is a localization away from `r`.
* `ProjectiveSpectrum.isLocalizationElem_eq_pow`: for `g = a * f` the localizing element of
  `D₊(g) ⊆ D₊(f)` is the `deg f`-th power of `a / f ^ n`.
* `ProjectiveSpectrum.isLocalizedModule_degreeZeroMap_of_pow`: `M₍g₎` is the localization of
  `M₍f₎` at any degree-zero fraction whose `deg f`-th power is that localizing element.

## References

* [Stacks Project, Tag 01MB](https://stacks.math.columbia.edu/tag/01MB)
-/

@[expose] public section

open DirectSum Stacks.GradedLocalization

namespace ProjectiveSpectrum

universe u v w t

/-- A localization away from a positive power of `r` is a localization away from `r`. -/
public lemma isLocalizedModule_away_of_pow {R P Q : Type*} [CommSemiring R]
    [AddCommMonoid P] [AddCommMonoid Q] [Module R P] [Module R Q]
    {r : R} {n : ℕ} (hn : n ≠ 0) (φ : P →ₗ[R] Q)
    (hloc : IsLocalizedModule.Away (r ^ n) φ) : IsLocalizedModule.Away r φ := by
  let := hloc
  refine IsLocalizedModule.Away.mk ?_ ?_ ?_
  · have h := IsLocalizedModule.Away.isUnit_algebraMap (f := φ) (r := r ^ n)
    rwa [map_pow, isUnit_pow_iff hn] at h
  · intro x
    obtain ⟨k, y, hy⟩ := IsLocalizedModule.Away.surj (f := φ) (r := r ^ n) x
    exact ⟨n * k, y, by rwa [pow_mul]⟩
  · intro x y hxy
    obtain ⟨k, hk⟩ := IsLocalizedModule.Away.exists_of_eq (f := φ) (r := r ^ n) hxy
    exact ⟨n * k, by rwa [pow_mul]⟩

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]

/-- The localizing element of `D₊(a * f) ⊆ D₊(f)` is the `deg f`-th power of `a / f ^ n`. -/
public lemma isLocalizationElem_eq_pow {f : S} {d : ℕ} (hf : f ∈ 𝒜 d)
    (n : ℕ) (a : S) (ha : a ∈ 𝒜 (n • d)) (hg : a * f ∈ 𝒜 (n * d + d)) :
    HomogeneousLocalization.Away.isLocalizationElem hf hg =
      HomogeneousLocalization.Away.mk 𝒜 hf n a ha ^ d := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  rw [HomogeneousLocalization.val_pow, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_pow,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, SubmonoidClass.mk_pow, mul_pow]
  ring

/-- `M₍g₎` is the localization of `M₍f₎` at any degree-zero fraction whose `deg f`-th power is
the canonical localizing element of `D₊(g) ⊆ D₊(f)`. -/
public lemma isLocalizedModule_degreeZeroMap_of_pow (f g : S) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (q : HomogeneousLocalization.Away 𝒜 f)
    (hq : HomogeneousLocalization.Away.isLocalizationElem hf hg = q ^ d) :
    letI φ₀ := degreeZeroRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg
    letI : Algebra (HomogeneousLocalization.Away 𝒜 f)
        (HomogeneousLocalization.Away 𝒜 g) := φ₀.toRingHom.toAlgebra
    letI := Module.compHom (R := HomogeneousLocalization.Away 𝒜 g)
      (GradedModuleDegreeZeroLocalization 𝒜 𝒨 g) φ₀.toRingHom
    IsLocalizedModule.Away q
      (moduleRestrictionMaps 𝒜 𝒨 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg).degreeZeroMap := by
  let φ₀ := degreeZeroRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg
  let : Algebra (HomogeneousLocalization.Away 𝒜 f)
      (HomogeneousLocalization.Away 𝒜 g) := φ₀.toRingHom.toAlgebra
  let := Module.compHom (R := HomogeneousLocalization.Away 𝒜 g)
    (GradedModuleDegreeZeroLocalization 𝒜 𝒨 g) φ₀.toRingHom
  refine isLocalizedModule_away_of_pow hd.ne' _ ?_
  rw [← hq]
  exact isLocalizedModule_degreeZeroMap 𝒜 𝒨 f g d e hd he hf hg hfg

end ProjectiveSpectrum
