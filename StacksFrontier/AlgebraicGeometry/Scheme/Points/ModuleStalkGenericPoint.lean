module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.RingTheory.OrderOfVanishing.GenericRank

/-!
# The stalk at the generic point of an integral scheme is the total quotient module

Let `X` be an integral scheme with generic point `η`, let `F` be a quasi-coherent `𝒪_X`-module
and let `x` be any point. The comparison `F_x ⟶ F_η` exhibits `F_η` as the localization of the
`𝒪_{X,x}`-module `F_x` at *all* the nonzerodivisors of `𝒪_{X,x}`, not merely at the complement
of a prime: the local ring at `η` is the function field, so the prime that
`Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes` produces is `⊥`,
and the complement of `⊥` in a domain is `𝒪_{X,x}⁰`.

Combined with the algebraic half,
`Stacks.OrderOfVanishing.finrank_quotient_torsion_eq_finrank_localization`, this says that the
rank of the torsion-free quotient of `F_x` is the dimension of `F_η` over the function field —
the same number at every point of `X`. That is the *generic rank*, and it is the shape of the
hypotheses `hr` and `hr'` of `AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap` of
[Stacks, Tag 0B3T], which are read at the generic point of a prime divisor.

## Main results

* `Stacks.ModuleStalkGenericPoint.under_maximalIdeal_genericPoint_eq_bot`: the prime of
  `𝒪_{X,x}` lying under the maximal ideal of the function field is `⊥`.
* `Stacks.ModuleStalkGenericPoint.isLocalizedModule_nonZeroDivisors_stalkSpecializes_genericPoint`:
  **`F_η` is the localization of `F_x` at the nonzerodivisors of `𝒪_{X,x}`.**
* `Stacks.ModuleStalkGenericPoint.finrank_quotient_torsion_stalk_eq`: **the rank of the
  torsion-free quotient of `F_x` is the dimension of `F_η` over the function field.**

## Implementation notes

**Only one module structure has to be carried by hand.** The ambient instances suffice for the
rest, which is why the statements here are shorter than those of
`StacksFrontier/AlgebraicGeometry/Scheme/Points/ModuleStalkSpecialization.lean`:
`AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf` is a global instance giving
`Module 𝒪_{X,x} F_x`, so `Stacks.ModuleStalkSpecialization.stalkModule` never needs a `letI`
here; Mathlib's `AlgebraicGeometry.stalkFunctionFieldAlgebra` is the algebra structure
`𝒪_{X,x} → 𝒪_{X,η}` through the very same `stalkSpecializes`, and agrees with the `letI` of the
specialization file by proof irrelevance in the `⤳` argument. What stays a `letI` is
`Stacks.ModuleStalkSpecialization.stalkSpecializesModule`, the `𝒪_{X,x}`-module structure on
`F_η`, which has no ambient instance and which the linear map `stalkSpecializesₗ` needs to have
a type at all.

**`⊥` is reached through Mathlib's fraction field, not through the ring half of the
specialization comparison.** `AlgebraicGeometry.Scheme.functionField` is a field and
`IsFractionRing 𝒪_{X,x} K` is already an instance, so the maximal ideal of `K` is `⊥` and its
contraction is the kernel of an injective map. The ring half,
`Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes`, is therefore not used.

**No `@[stacks]` attribute.** This is a step of the proof of Tag 0B3T, not one of its
assertions.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.ModuleStalkSpecialization

universe u

namespace Stacks.ModuleStalkGenericPoint

variable {X : Scheme.{u}}

/-- **The prime of `𝒪_{X,x}` under the maximal ideal of the function field is `⊥`.** The
function field of an integral scheme is a field, so its maximal ideal is `⊥`, and the structure
map `𝒪_{X,x} → K` is injective because it exhibits `K` as a fraction field. -/
theorem under_maximalIdeal_genericPoint_eq_bot [IsIntegral X] (x : X) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk (genericPoint X))).under
      (X.presheaf.stalk x) = ⊥ := by
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact Ideal.comap_bot_of_injective _
    (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)

/-- **The stalk of a quasi-coherent module at the generic point of an integral scheme is the
localization of the stalk at any other point at all the nonzerodivisors.** The prime of
`Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes` is `⊥` here, and
the complement of `⊥` in a domain is the set of nonzerodivisors. -/
theorem isLocalizedModule_nonZeroDivisors_stalkSpecializes_genericPoint [IsIntegral X]
    (F : X.Modules) [F.IsQuasicoherent] (x : X) :
    letI := stalkSpecializesModule F (genericPoint_specializes x)
    IsLocalizedModule (nonZeroDivisors (X.presheaf.stalk x))
      (stalkSpecializesₗ F (genericPoint_specializes x)) := by
  let := stalkSpecializesModule F (genericPoint_specializes x)
  have h := isLocalizedModule_atPrime_stalkSpecializes F (genericPoint_specializes x)
  have h2 := isLocalizedModule_atPrime_of_eq (under_maximalIdeal_genericPoint_eq_bot x) h
  have h3 : IsLocalizedModule ((⊥ : Ideal (X.presheaf.stalk x)).primeCompl)
      (stalkSpecializesₗ F (genericPoint_specializes x)) := h2
  rwa [Ideal.primeCompl_bot] at h3

/-- **The generic rank of a quasi-coherent module is read at every point.** The rank over
`𝒪_{X,x}` of the torsion-free quotient of `F_x` is the dimension over the function field of the
stalk at the generic point, so it does not depend on `x`. -/
theorem finrank_quotient_torsion_stalk_eq [IsIntegral X] (F : X.Modules)
    [F.IsQuasicoherent] (x : X) :
    Module.finrank (X.presheaf.stalk x)
        (F.presheaf.stalk x ⧸
          Submodule.torsion (X.presheaf.stalk x) (F.presheaf.stalk x))
      = Module.finrank (X.presheaf.stalk (genericPoint X))
          (F.presheaf.stalk (genericPoint X)) := by
  let := stalkSpecializesModule F (genericPoint_specializes x)
  have : IsScalarTower (X.presheaf.stalk x) (X.presheaf.stalk (genericPoint X))
      (F.presheaf.stalk (genericPoint X)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have := isLocalizedModule_nonZeroDivisors_stalkSpecializes_genericPoint F x
  exact Stacks.OrderOfVanishing.finrank_quotient_torsion_eq_finrank_localization
    (stalkSpecializesₗ F (genericPoint_specializes x))

end Stacks.ModuleStalkGenericPoint

end
