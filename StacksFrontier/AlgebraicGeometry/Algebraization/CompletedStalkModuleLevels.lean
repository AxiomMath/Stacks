module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalProperties.Basic
public import StacksFrontier.RingTheory.AdicCompletion.SmulTopPow

/-!
# The level quotients of a localized module

The `n`-th infinitesimal neighbourhood `M_T ⧸ Jⁿ M_T` of a localization of `M` is the
localization of the `n`-th infinitesimal neighbourhood `M ⧸ JⁿM` of `M`. Localization is exact,
so this is not deep; what it is, is the level-by-level half of the identification of the
completion of a localization with the localization of a completion, and that identification is
what reads a statement about a completed stalk at a prime of a chart.

## Main results

* `Stacks.Algebraization.localized'_pow_smul_top_eq_map_pow_smul_top` — the localization of
  `Jⁿ · M` is `(J · R_T)ⁿ · M_T`.
* `Stacks.Algebraization.levelLocalizationMap` — the induced map of level-`n` quotients, with
  `Stacks.Algebraization.isLocalizedModule_levelLocalizationMap` saying it is a localization and
  `Stacks.Algebraization.levelLocalizationMap_mk` saying what it does on classes.
* `Stacks.Algebraization.transitionMap_levelLocalizationMap` — the maps of level quotients are
  compatible with the transition maps of the two towers.

## Implementation notes

The target of Mathlib's `Submodule.toLocalizedQuotient'` is the quotient by
`Submodule.localized'`, which is the right object but the wrong spelling: the towers whose limits
are the adic completions are indexed by the powers of the *extended* ideal. The two are
identified by `localized'_pow_smul_top_eq_map_pow_smul_top`, and
`IsLocalizedModule.of_linearEquiv` carries the localization property across.

No declaration here carries a `stacks` attribute: this is the substrate on which the local
statements of the chapter on algebraic and formal geometry are phrased, not the content of a tag.
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.Algebraization

section Level

variable {R : Type u} [CommRing R] (J : Ideal R) (T : Submonoid R)
  {M : Type v} [AddCommGroup M] [Module R M]
  (Rt : Type w) [CommRing Rt] [Algebra R Rt] [IsLocalization T Rt]
  {Mt : Type w} [AddCommGroup Mt] [Module R Mt] [Module Rt Mt] [IsScalarTower R Rt Mt]
  (f : M →ₗ[R] Mt) [IsLocalizedModule T f]

/-- The transition maps of the tower of a module are the identity on residue classes. -/
@[simp]
theorem transitionMap_mk_eq_mk {A : Type*} [CommRing A] (I : Ideal A) (N : Type*)
    [AddCommGroup N] [Module A N] {m n : ℕ} (hmn : m ≤ n) (y : N) :
    AdicCompletion.transitionMap I N hmn (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk y :=
  rfl

/-- **The localization of `Jⁿ · M` is `(J · R_T)ⁿ · M_T`.** The level-`n` stage of the tower of
`M` localizes to the level-`n` stage of the tower of `M_T`. -/
theorem localized'_pow_smul_top_eq_map_pow_smul_top (n : ℕ) :
    (J ^ n • (⊤ : Submodule R M)).localized' Rt T f =
      (J.map (algebraMap R Rt)) ^ n • (⊤ : Submodule Rt Mt) := by
  rw [Submodule.localized'_smul, Submodule.localized'_top, Ideal.localized'_eq_map,
    Ideal.map_pow]

/-- The level-`n` stages of the two towers, identified by
`localized'_pow_smul_top_eq_map_pow_smul_top`. -/
def levelQuotEquiv (n : ℕ) :
    (Mt ⧸ ((J ^ n • (⊤ : Submodule R M)).localized' Rt T f)) ≃ₗ[Rt]
      (Mt ⧸ ((J.map (algebraMap R Rt)) ^ n • (⊤ : Submodule Rt Mt))) :=
  Submodule.quotEquivOfEq _ _ (localized'_pow_smul_top_eq_map_pow_smul_top J T Rt f n)

/-- **The map of level-`n` quotients induced by a localization.** -/
def levelLocalizationMap (n : ℕ) :
    (M ⧸ (J ^ n • (⊤ : Submodule R M))) →ₗ[R]
      (Mt ⧸ ((J.map (algebraMap R Rt)) ^ n • (⊤ : Submodule Rt Mt))) :=
  ((levelQuotEquiv J T Rt f n).restrictScalars R).toLinearMap ∘ₗ
    Submodule.toLocalizedQuotient' Rt T f (J ^ n • (⊤ : Submodule R M))

/-- **What `levelLocalizationMap` does**: on the class of `m : M` it is the class of `f m`. -/
@[simp]
theorem levelLocalizationMap_mk (n : ℕ) (m : M) :
    levelLocalizationMap J T Rt f n (Submodule.Quotient.mk m) = Submodule.Quotient.mk (f m) :=
  rfl

/-- **`levelLocalizationMap` is a localization at `T`.** -/
instance isLocalizedModule_levelLocalizationMap (n : ℕ) :
    IsLocalizedModule T (levelLocalizationMap J T Rt f n) :=
  IsLocalizedModule.of_linearEquiv T
    (Submodule.toLocalizedQuotient' Rt T f (J ^ n • (⊤ : Submodule R M)))
    ((levelQuotEquiv J T Rt f n).restrictScalars R)

/-- **The maps of level quotients are compatible with the transition maps** of the two towers. -/
theorem transitionMap_levelLocalizationMap {m n : ℕ} (hmn : m ≤ n)
    (x : M ⧸ (J ^ n • (⊤ : Submodule R M))) :
    AdicCompletion.transitionMap (J.map (algebraMap R Rt)) Mt hmn
        (levelLocalizationMap J T Rt f n x) =
      levelLocalizationMap J T Rt f m (AdicCompletion.transitionMap J M hmn x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

end Level

end Stacks.Algebraization

end
