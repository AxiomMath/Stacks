module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingSections
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The affine base case of the comparison between twisted cohomology and cohomology on `X_s`

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module, `s` a global section of `ℒ` and `ℱ` a
quasi-coherent `𝒪_X`-module. [Stacks, Tag 09MR] asserts that on a quasi-compact and
quasi-separated `X` the canonical map

`H^p_*(X, ℒ, ℱ)₍s₎ ⟶ H^p(X_s, ℱ)`,  `ξ / sⁿ ↦ s^{-n} ξ`

out of the **degree-zero** localization at the homogeneous element `s` of the graded module
`H^p_*(X, ℒ, ℱ) = ⨁_{n ∈ ℤ} H^p(X, ℱ ⊗ ℒ^{⊗ n})` over the graded ring
`Γ_*(X, ℒ) = ⨁_{n ≥ 0} Γ(X, ℒ^{⊗ n})` is an isomorphism.

The source proves it by the induction principle of [Stacks, Tag 08DR] over the quasi-compact
opens of `X`: the base case is an affine open, and the step compares two Mayer--Vietoris
sequences. This file supplies the **base case**. Over an affine open `U` and in positive degree
both sides vanish: the homogeneous components `H^p(U, ℱ ⊗ ℒ^{⊗ n})` because every twist of a
quasi-coherent module is quasi-coherent and quasi-coherent modules have no higher cohomology on
an affine open ([Stacks, Tag 01XB]), and `H^p(U ⊓ X_s, ℱ)` because the nonvanishing locus meets
an affine open in an affine open ([Stacks, Tag 01PV]), where the same vanishing applies.

## Main results

All declarations are in the namespace `Stacks.Cohomology.TwistedLocalization`.

* `subsingleton_degreeZeroLocalization_of_forall_eq_zero`: the degree-zero localization at a
  degree-one homogeneous element of a graded module whose non-negative homogeneous components all
  vanish is trivial.
* `isZero_hgroup_twistedModule_of_isAffineOpen`: the homogeneous components of
  `H^p_*(U, ℒ, ℱ)` vanish over an affine open in positive degree.
* `isZero_hgroup_nonvanishingOpen_of_isAffineOpen`: `H^p(U ⊓ X_s, ℱ)` vanishes over an affine
  open in positive degree.
* `isZero_twistedModule_and_nonvanishingOpen_of_isAffineOpen`: the two together, which is the
  base case of the induction.

## Implementation notes

Cohomology is `Stacks.Cohomology.Hgroup`, the right derived functor of sections over an open of
[Stacks, Tag 01E3], the model in which [Stacks, Tag 01XB] is stated. The twist is spelled with
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` and
`Stacks.SheafOfModules.TensorPower.tensorPower` at the indices `sectionSiteRing X` and
`sectionSiteSheaf X`, which is the spelling of [Stacks, Tag 0B5L] and of the graded section
module of [Stacks, Tag 01CV]; quasi-coherence transfers to it because that tensor product is
definitionally `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, for which
[Stacks, Tag 01CE] is an instance. The tensor powers of an invertible module are themselves
invertible, hence quasi-coherent.

The degree-zero localization is `GradedModuleDegreeZeroLocalization`: the submodule of the
localization away from `s` spanned by the fractions whose numerator and denominator have equal
degree. It is **not** the ordinary localization, and
`Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction` writes every element of it in the
shape `x / sⁿ` with `x` homogeneous of degree `n ≥ 0`.

## References

* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology Stacks.SheafOfModules

universe u v w

namespace Stacks.Cohomology.TwistedLocalization

/-! ### Degree-zero localization of a graded module with vanishing components -/

section Algebra

/-- The grading action of a naturally graded ring on an integer-graded module, as in
`GradedModuleDegreeZeroLocalization`. -/
local instance degreeVAdd : VAdd ℕ ℤ where vadd n z := (n : ℤ) + z

variable {R : Type u} {M : Type v} {σ : Type w} {τ : Type*}
  [CommRing R] [AddCommGroup M] [Module R M]
  [SetLike σ R] [AddSubgroupClass σ R] (A : ℕ → σ) [GradedRing A]
  [SetLike τ M] [AddSubgroupClass τ M] (B : ℤ → τ) [DirectSum.Decomposition B]
  [SetLike.GradedSMul A B] {f : R}

/-- **The degree-zero localization at a degree-one homogeneous element of a graded module whose
non-negative homogeneous components vanish is trivial.** -/
theorem subsingleton_degreeZeroLocalization_of_forall_eq_zero (hf : f ∈ A 1)
    (hB : ∀ n : ℕ, ∀ x ∈ B (n : ℤ), x = (0 : M)) :
    Subsingleton (GradedModuleDegreeZeroLocalization A B f) := by
  let _ := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := R) f M)
    (algebraMap (HomogeneousLocalization.Away A f) (Localization.Away f))
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨n, x, hx, hy⟩ := Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction A B hf y
  apply Submodule.coe_eq_zero.mp
  rw [hy, hB n x hx, LocalizedModule.zero_mk]

end Algebra

/-! ### Vanishing over an affine open -/

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

/-- The twist `ℱ ⊗ ℒ^{⊗ n}`, the degree-`n` homogeneous piece of the coefficients of
`H^p_*(X, ℒ, ℱ)`. -/
abbrev twistedModule (F : X.Modules) (n : ℤ) : X.Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (F)).obj
    (@TensorPower.tensorPower _ _ _ (sectionSiteRing X) (sectionSiteSheaf X) _ _ L
      (TensorPower.isEquivalence_tensorRightFunctor (sectionSiteRing X) (sectionSiteSheaf X) L) n))

/-- **Every integer tensor power of an invertible module on a scheme is quasi-coherent.** -/
theorem isQuasicoherent_tensorPower (n : ℤ) :
    (@TensorPower.tensorPower _ _ _ (sectionSiteRing X) (sectionSiteSheaf X) _ _ L
      (TensorPower.isEquivalence_tensorRightFunctor (sectionSiteRing X) (sectionSiteSheaf X) L)
      n).IsQuasicoherent :=
  have : IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      (@TensorPower.tensorPower _ _ _ (sectionSiteRing X) (sectionSiteSheaf X) _ _ L
        (TensorPower.isEquivalence_tensorRightFunctor (sectionSiteRing X) (sectionSiteSheaf X) L)
        n) :=
    TensorPower.isInvertible_tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L n
  Scheme.isQuasicoherent_of_isInvertible X _

/-- **Every twist of a quasi-coherent module by a tensor power of an invertible module is
quasi-coherent.** -/
theorem isQuasicoherent_twistedModule (F : X.Modules) [F.IsQuasicoherent] (n : ℤ) :
    (twistedModule X L F n).IsQuasicoherent :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace F
    (@TensorPower.tensorPower _ _ _ (sectionSiteRing X) (sectionSiteSheaf X) _ _ L
      (TensorPower.isEquivalence_tensorRightFunctor (sectionSiteRing X) (sectionSiteSheaf X) L) n)
    ‹_›
    (isQuasicoherent_tensorPower X L n)

/-- **The homogeneous components of `H^p_*(U, ℒ, ℱ)` vanish over an affine open in positive
degree.** -/
theorem isZero_hgroup_twistedModule_of_isAffineOpen (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (p : ℕ) (hp : 0 < p) (n : ℤ) :
    IsZero (Hgroup X.ringCatSheaf U p (twistedModule X L F n)) :=
  have := isQuasicoherent_twistedModule X L F n
  Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X (twistedModule X L F n) U hU p hp

/-- **`H^p(U ⊓ X_s, ℱ)` vanishes over an affine open in positive degree.** -/
theorem isZero_hgroup_nonvanishingOpen_of_isAffineOpen (F : X.Modules) [F.IsQuasicoherent]
    (s : L.sections) (U : X.Opens) (hU : IsAffineOpen U) (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup X.ringCatSheaf (U ⊓ nonvanishingOpen L s) p F) :=
  Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F _
    (AlgebraicGeometry.Scheme.Modules.isAffineOpen_inf_nonvanishingOpen L s U hU) p hp

/-- **The affine base case of [Stacks, Tag 09MR].** Let `X` be a scheme, `ℒ` an invertible
`𝒪_X`-module, `s` a global section of `ℒ`, `ℱ` a quasi-coherent `𝒪_X`-module, `U ⊆ X` an affine
open and `p > 0`. Then both sides of the comparison map vanish over `U`: every homogeneous
component `H^p(U, ℱ ⊗ ℒ^{⊗ n})` of the graded module `H^p_*(U, ℒ, ℱ)` is zero, and so is
`H^p(U ⊓ X_s, ℱ)`. -/
theorem isZero_twistedModule_and_nonvanishingOpen_of_isAffineOpen (F : X.Modules)
    [F.IsQuasicoherent] (s : L.sections) (U : X.Opens) (hU : IsAffineOpen U) (p : ℕ)
    (hp : 0 < p) :
    (∀ n : ℤ, IsZero (Hgroup X.ringCatSheaf U p (twistedModule X L F n))) ∧
      IsZero (Hgroup X.ringCatSheaf (U ⊓ nonvanishingOpen L s) p F) :=
  ⟨fun n => isZero_hgroup_twistedModule_of_isAffineOpen X L F U hU p hp n,
    isZero_hgroup_nonvanishingOpen_of_isAffineOpen X L F s U hU p hp⟩

end Stacks.Cohomology.TwistedLocalization

end
