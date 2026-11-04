module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.Flat.MittagLeffler
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.RingTheory.Module.Kaplansky
public import StacksCore.Tactic.StacksAttribute

/-!
# Universal injectivity of localization at the regular elements of the closed fibre

Let `R` be a local ring, `S` an `R`-algebra and `N` an `S`-module whose closed fibre
`N / 𝔪_R N` is finite over the Noetherian closed-fibre ring `S / 𝔪_R S`. Assume `N` is
projective over `R`. Then every element of `S` acting injectively on the closed fibre acts
universally injectively on `N` over `R`, and hence the canonical map from `N` to its
localization at those elements is universally injective over `R`.

## Main results

* `Stacks.UniversalInjectivity.universallyInjective_lsmul_of_mem_nonZeroSMulDivisors_quotient`:
  multiplication by an element regular on the closed fibre is universally injective.
* `Stacks.UniversalInjectivity.universallyInjective_localizedModule_mkLinearMap`: the canonical
  localization map is universally injective.

## Implementation notes

The multiplicative subset `Σ` of the source is Mathlib's `nonZeroSMulDivisors` for the quotient
of `N` by the action of the extended maximal ideal. Multiplication by `s` is first viewed as an
`S`-linear endomorphism and then restricted to an `R`-linear one, and the localization module is
represented by `LocalizedModule`.

The criterion for universal injectivity over a local ring,
`Module.Flat.rTensor_injective_of_projective_of_injective_mapQ_maximalIdeal`, carries a
`Small.{v} R` hypothesis. It is not needed here: a projective module over a local ring is free,
so when `N` is nontrivial the scalar action of `R` on `N` is faithful and smallness follows,
while for subsingleton `N` every map out of `N ⊗[R] Q` is injective for trivial reasons.

## References

* [Stacks Project, Tag 05FR](https://stacks.math.columbia.edu/tag/05FR)
-/

@[expose] public section

namespace Stacks.UniversalInjectivity

universe u v w

/-- **Stacks Project, Tag 05FR.** An element which acts injectively on the closed fibre of a
projective module acts universally injectively on the module over the local base ring. -/
@[stacks 05FR "elementwise_universal_injectivity"]
theorem universallyInjective_lsmul_of_mem_nonZeroSMulDivisors_quotient
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [IsNoetherianRing
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))]
    [Module.Finite
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
        (⊤ : Submodule S N)))]
    [Module.Projective R N]
    {s : S}
    (hs : s ∈ nonZeroSMulDivisors S
      (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
        (⊤ : Submodule S N)))) :
    UniversallyInjective ((LinearMap.lsmul S N s).restrictScalars R) := by
  have hu : Function.Injective
      ((IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)).mapQ
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R N))
        ((LinearMap.lsmul S N s).restrictScalars R)
        (Submodule.smul_top_le_comap_smul_top _ _)) := by
    let p : Submodule R N := IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)
    let q : Submodule S N := Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
      (⊤ : Submodule S N)
    let e : (N ⧸ p) ≃ₗ[R] (N ⧸ q) :=
      Submodule.quotEquivOfEq _ _ (by
        dsimp [p, q]
        rw [Ideal.smul_restrictScalars, Submodule.restrictScalars_top]) ≪≫ₗ
        Submodule.Quotient.restrictScalarsEquiv R _
    have hcomm : ∀ x, e (Submodule.mapQ p p ((LinearMap.lsmul S N s).restrictScalars R)
        (Submodule.smul_top_le_comap_smul_top _ _) x) = s • e x := by
      intro x
      obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
    intro x y hxy
    refine e.injective (sub_eq_zero.mp (hs _ ?_))
    show s • (e x - e y) = 0
    rw [smul_sub, ← hcomm, ← hcomm, hxy, sub_self]
  rcases subsingleton_or_nontrivial N with hN | hN
  · intro Q _ _
    exact Function.injective_of_subsingleton _
  · have _ : Module.Free R N := Module.free_of_projective_of_isLocalRing
    have _ : Small.{w} R := small_of_injective (smul_left_injective' (M := R) (α := N))
    exact Module.Flat.rTensor_injective_of_projective_of_injective_mapQ_maximalIdeal _ hu

/-- **Stacks Project, Tag 05FR.** If a module is projective over a local base ring, its
canonical map to the localization at the elements acting injectively on its closed fibre is
universally injective over the base. -/
@[stacks 05FR "localization_universal_injectivity"]
theorem universallyInjective_localizedModule_mkLinearMap
    {R : Type u} {S : Type v} {N : Type (max v w)} [CommRing R] [CommRing S] [IsLocalRing R]
    [Algebra R S] [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Projective R N]
    [IsNoetherianRing
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))]
    [Module.Finite
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
        (⊤ : Submodule S N)))] :
    UniversallyInjective
      ((LocalizedModule.mkLinearMap
        (nonZeroSMulDivisors S
          (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
            (⊤ : Submodule S N)))) N).restrictScalars R) := by
  intro Q _ _
  let T := nonZeroSMulDivisors S
    (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) • (⊤ : Submodule S N)))
  show Function.Injective
    (TensorProduct.AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T N))
  refine (IsLocalizedModule.injective_iff_isRegular T _).2 fun s => ?_
  show Function.Injective (fun x : TensorProduct R N Q ↦ (s : S) • x)
  convert (universallyInjective_lsmul_of_mem_nonZeroSMulDivisors_quotient s.property) Q using 1
  ext n
  rfl

end Stacks.UniversalInjectivity
