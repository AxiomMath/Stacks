module

public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.CanonicalMap
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.AffineComparison

/-!
# The comparison map of [Stacks, Tag 09MR] in terms of its numerators

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module, `s ∈ Γ(X, ℒ)` a global section, `ℱ` an
`𝒪_X`-module, `p` a degree and `U ⊆ X` an open. The comparison map

`canonicalMap : H^p_*(U, ℒ, ℱ)₍s₎ ⟶ H^p(U ∩ X_s, ℱ)`,  `ξ / sⁿ ↦ s^{-n} ξ`

is bijective as soon as two statements about its numerators hold, and **those statements mention
neither the localization nor the graded module**: they speak only of the restriction maps

`H^p(U, ℱ ⊗ ℒ^{⊗ n}) ⟶ H^p(U ∩ X_s, ℱ ⊗ ℒ^{⊗ n})`

and of multiplication by powers of `s`.

## Main definitions

* `Stacks.Cohomology.TwistedLocalizationMap.RestrictKernelTorsion`: a class on `U` restricting
  to zero on `U ∩ X_s` is killed by a power of `s`.
* `Stacks.Cohomology.TwistedLocalizationMap.RestrictPowerSurjective`: every class on `U ∩ X_s`
  becomes, after multiplication by some `sⁿ`, the restriction of a class of the `n`-th twist on
  `U`.

## Main results

* `Stacks.SheafOfModules.bijective_degreeZeroLocalizationLiftOfDegree_of_pow`: a lift out of a
  degree-zero localization is bijective as soon as its members are surjective up to a power of
  the denominator and kill only power-torsion numerators. This weakens the two hypotheses of
  `Stacks.Cohomology.TwistedLocalizationMap.bijective_degreeZeroLocalizationLiftOfDegree`, which
  asks for surjectivity at the single denominator `f` and for an exactly trivial kernel.
* `Stacks.Cohomology.TwistedLocalizationMap.bijective_canonicalMap_of_numerators`: **the two
  numerator statements imply that the comparison map of [Stacks, Tag 09MR] is bijective.**
* `Stacks.Cohomology.TwistedLocalizationMap.restrictKernelTorsion_of_isAffineOpen` and
  `Stacks.Cohomology.TwistedLocalizationMap.restrictPowerSurjective_of_isAffineOpen`: the two
  statements over an affine open in positive degree, where both groups vanish.

## Implementation notes

A fraction vanishes exactly when a power of the denominator kills its numerator
(`Stacks.SheafOfModules.eq_zero_iff_exists_pow_smul_eq_zero`), which is why the kernel statement
is allowed to produce a power of `s` rather than an outright zero.

## References

* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology Stacks.SheafOfModules DirectSum
open Stacks.Cohomology.TwistedGradedModule
open scoped DirectSum

universe u

namespace Stacks.SheafOfModules

/-- **A compatible family which is surjective up to a power of the denominator and kills only
power-torsion numerators lifts to a bijection out of the degree-zero localization.** -/
theorem bijective_degreeZeroLocalizationLiftOfDegree_of_pow {R : Type u} {M : Type u}
    {σ : Type u} {τ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [SetLike σ R] [AddSubgroupClass σ R] (A : ℕ → σ) [GradedRing A]
    [SetLike τ M] [AddSubgroupClass τ M] (B : ℤ → τ) [DirectSum.Decomposition B]
    [SetLike.GradedSMul A B] {f : R} (hf : f ∈ A 1)
    {N : Type u} [AddCommGroup N] (e : ℕ → M →+ N)
    (he : ∀ (n k : ℕ) (x : M), x ∈ B ((n * 1 : ℕ) : ℤ) → e (n + k) (f ^ k • x) = e n x)
    (hsurj : ∀ y : N, ∃ (n : ℕ) (x : M), x ∈ B ((n * 1 : ℕ) : ℤ) ∧ e n x = y)
    (hinj : ∀ (n : ℕ) (x : M), x ∈ B ((n * 1 : ℕ) : ℤ) → e n x = 0 → ∃ k : ℕ, f ^ k • x = 0) :
    Function.Bijective (degreeZeroLocalizationLiftOfDegree A B hf e he) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz0 ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨n, x, hx, hfrac⟩ := degreeZeroLocalization_exists_fraction_of_degree A B hf z
    rw [degreeZeroLocalizationLiftOfDegree_fraction A B hf e he z n x hx hfrac] at hz0
    exact (eq_zero_iff_exists_pow_smul_eq_zero A B z n x hfrac).2 (hinj n x hx hz0)
  · obtain ⟨n, x, hxmem, hxy⟩ := hsurj y
    exact ⟨⟨LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩,
      mk_mem_degreeZeroLocalization_of_degree A B hf n x hxmem⟩,
      (degreeZeroLocalizationLiftOfDegree_fraction A B hf e he _ n x hxmem rfl).trans hxy⟩

end Stacks.SheafOfModules

namespace Stacks.Cohomology.TwistedLocalizationMap

attribute [local instance] Stacks.SheafOfModules.sectionDegreeVAdd

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

variable (s : L.sections) (F : X.Modules) (p : ℕ) (U : X.Opens)

/-- **Multiplying a homogeneous class by `s^k`** is the action of the `k`-th power section on the
cohomology of the twist, which raises the degree by `k`. -/
theorem smul_pow_of (k n : ℕ) (ξ : gradedPiece X L F p U (n : ℤ)) :
    (homogeneousSection X L s ^ k •
        (DirectSum.of _ (n : ℤ) ξ : twistedCohomologyModule X L F p U)) =
      DirectSum.of _ ((k + n : ℕ) : ℤ)
        (act X L F p U (k : ℤ) (n : ℤ)
          (Stacks.Cohomology.PowerSection.powerSectionValue X L s k) ξ) := by
  rw [← Stacks.Cohomology.PowerSection.of_powerSectionValue]
  exact of_smul_of X L F p U k (n : ℤ)
    (Stacks.Cohomology.PowerSection.powerSectionValue X L s k) ξ

/-- **The kernel of restriction to `U ∩ X_s` is `s`-power torsion.** A cohomology class of the
`n`-th twist over `U` whose restriction to `U ∩ X_s` vanishes is killed by some power of `s`.
This is the injectivity half of [Stacks, Tag 09MR] over `U`, written without the
localization. -/
def RestrictKernelTorsion : Prop :=
  ∀ (n : ℕ) (ξ : gradedPiece X L F p U (n : ℤ)),
    (ConcreteCategory.hom (restrictTwist X L s F p U (n : ℤ))) ξ = 0 →
      ∃ k : ℕ, act X L F p U (k : ℤ) (n : ℤ)
        (Stacks.Cohomology.PowerSection.powerSectionValue X L s k) ξ = 0

/-- **Every class on `U ∩ X_s` is `s^{-n}` times a class on `U`.** For every class `y` of
`H^p(U ∩ X_s, ℱ)` there are an `n` and a class `ξ` of `H^p(U, ℱ ⊗ ℒ^{⊗ n})` whose restriction to
`U ∩ X_s` is `sⁿ y`. This is the surjectivity half of [Stacks, Tag 09MR] over `U`, written
without the localization. -/
def RestrictPowerSurjective : Prop :=
  ∀ y : (Hgroup X.ringCatSheaf (nonvanishingPart X L s U) p F : Type u),
    ∃ (n : ℕ) (ξ : gradedPiece X L F p U (n : ℤ)),
      (ConcreteCategory.hom (restrictTwist X L s F p U (n : ℤ))) ξ =
        (ConcreteCategory.hom (untwistIso X L s F p U n).hom) y

/-- **The two numerator statements imply [Stacks, Tag 09MR] over `U`.** If the kernel of
restriction to `U ∩ X_s` is `s`-power torsion in every twist, and every class on `U ∩ X_s`
becomes the restriction of a twisted class after multiplication by a power of `s`, then the
comparison map `H^p_*(U, ℒ, ℱ)₍s₎ ⟶ H^p(U ∩ X_s, ℱ)` is bijective. -/
theorem bijective_canonicalMap_of_numerators
    (hker : RestrictKernelTorsion X L s F p U)
    (hsurj : RestrictPowerSurjective X L s F p U) :
    Function.Bijective (canonicalMap X L s F p U) := by
  refine Stacks.SheafOfModules.bijective_degreeZeroLocalizationLiftOfDegree_of_pow
    (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L) (grading X L F p U)
    (homogeneousSection_mem X L s) (numeratorMap X L s F p U)
    (numeratorMap_compatible X L s F p U) ?_ ?_
  · intro y
    obtain ⟨n, ξ, hξ⟩ := hsurj y
    refine ⟨n, DirectSum.of _ (n : ℤ) ξ, by rw [Nat.mul_one]; exact ⟨ξ, rfl⟩, ?_⟩
    rw [numeratorMap_of, hξ]
    exact Iso.hom_inv_id_apply (untwistIso X L s F p U n) y
  · intro n x hx h0
    rw [Nat.mul_one] at hx
    obtain ⟨ξ, rfl⟩ := hx
    rw [numeratorMap_of] at h0
    have hres : (ConcreteCategory.hom (restrictTwist X L s F p U (n : ℤ))) ξ = 0 := by
      have h1 := congrArg (ConcreteCategory.hom (untwistIso X L s F p U n).hom) h0
      rwa [Iso.inv_hom_id_apply, map_zero] at h1
    obtain ⟨k, hk⟩ := hker n ξ hres
    exact ⟨k, by rw [smul_pow_of X L s F p U k n ξ, hk, map_zero]⟩

/-! ### The affine case

Over an affine open and in positive degree both cohomology groups vanish, so both numerator
statements hold trivially. -/

section Affine

variable [F.IsQuasicoherent]

/-- **The kernel statement over an affine open in positive degree.** -/
theorem restrictKernelTorsion_of_isAffineOpen (hU : IsAffineOpen U) (hp : 0 < p) :
    RestrictKernelTorsion X L s F p U := by
  intro n ξ _
  have hsub : Subsingleton (gradedPiece X L F p U (n : ℤ)) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp
      (Stacks.Cohomology.TwistedLocalization.isZero_hgroup_twistedModule_of_isAffineOpen
        X L F U hU p hp (n : ℤ))
  exact ⟨0, by rw [Subsingleton.elim ξ 0]; exact map_zero _⟩

/-- **The surjectivity statement over an affine open in positive degree.** -/
theorem restrictPowerSurjective_of_isAffineOpen (hU : IsAffineOpen U) (hp : 0 < p) :
    RestrictPowerSurjective X L s F p U := by
  intro y
  have hsub : Subsingleton
      (Hgroup X.ringCatSheaf (nonvanishingPart X L s U) p F : Type u) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp
      (Stacks.Cohomology.TwistedLocalization.isZero_hgroup_nonvanishingOpen_of_isAffineOpen
        X L F s U hU p hp)
  refine ⟨0, 0, ?_⟩
  rw [Subsingleton.elim y 0, map_zero, map_zero]

end Affine

end Stacks.Cohomology.TwistedLocalizationMap

end
