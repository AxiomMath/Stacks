module

public import StacksFrontier.AlgebraicGeometry.Divisors.QuasicoherentIdealSheafData.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Modules.IdealSheafDataSubmodule

/-!
# A quasi-coherent sheaf of ideals on an affine scheme is the tilde of its global sections

Let `X` be an affine scheme and `J ⊆ 𝒪_X` a quasi-coherent sheaf of ideals, presented as a
submodule of the structure sheaf viewed as a sheaf of modules. Then `J` is the sheaf of ideals
`I~` associated with its ideal of global sections `I = J(X)`. In particular two quasi-coherent
sheaves of ideals on an affine scheme with the same global sections are equal.

## Main results

* `Stacks.Divisors.idealSheafDataOfSubmodule_eq_ofIdealTop`: the ideal sheaf datum of `J` is the
  one of its ideal of global sections.
* `Stacks.Divisors.eq_unitSubmodule_ofIdealTop`: `J` is the submodule of `𝒪_X` attached to the
  ideal `J(X)`, that is `J = J(X)~`.
* `Stacks.Divisors.submodule_eq_of_obj_top_eq`: two quasi-coherent sheaves of ideals on an
  affine scheme with equal global sections are equal.

## Implementation notes

On an affine scheme, Mathlib's `AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine`
identifies ideal sheaf data with ideals of the global sections, so the ideal sheaf datum
`Stacks.Divisors.idealSheafDataOfSubmodule J` is determined by `J(X)`. A submodule of a sheaf of
modules on a scheme is determined by its sections over the affine opens
(`AlgebraicGeometry.Scheme.Modules.submodule_eq_of_obj_affineOpens_eq`), and those are the ideals
of the datum.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} [IsAffine X]

/-- On an affine scheme the ideal sheaf datum of a quasi-coherent sheaf of ideals `J` is the one
attached to its ideal of global sections. -/
theorem idealSheafDataOfSubmodule_eq_ofIdealTop
    (J : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    [(J.toSheafOfModules : X.Modules).IsQuasicoherent] :
    idealSheafDataOfSubmodule J =
      Scheme.IdealSheafData.ofIdealTop (show Ideal Γ(X, ⊤) from J.obj (op ⊤)) :=
  Scheme.IdealSheafData.equivOfIsAffine.injective
    (Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply _).symm

/-- **A quasi-coherent sheaf of ideals on an affine scheme is the tilde of its global
sections.** On an affine scheme `X`, a quasi-coherent sheaf of ideals `J ⊆ 𝒪_X` is the sheaf of
ideals `J(X)~` attached to its ideal of global sections. -/
theorem eq_unitSubmodule_ofIdealTop
    (J : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    [(J.toSheafOfModules : X.Modules).IsQuasicoherent] :
    J = (Scheme.IdealSheafData.ofIdealTop
      (show Ideal Γ(X, ⊤) from J.obj (op ⊤))).unitSubmodule := by
  refine Scheme.Modules.submodule_eq_of_obj_affineOpens_eq _ _ fun U ↦ ?_
  rw [Scheme.IdealSheafData.unitSubmodule_obj_affine, ← idealSheafDataOfSubmodule_eq_ofIdealTop]
  rfl

/-- **Two quasi-coherent sheaves of ideals on an affine scheme with the same global sections
are equal.** -/
theorem submodule_eq_of_obj_top_eq
    (J₁ J₂ : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    [(J₁.toSheafOfModules : X.Modules).IsQuasicoherent]
    [(J₂.toSheafOfModules : X.Modules).IsQuasicoherent]
    (h : J₁.obj (op ⊤) = J₂.obj (op ⊤)) : J₁ = J₂ := by
  have key : idealSheafDataOfSubmodule J₁ = idealSheafDataOfSubmodule J₂ := by
    rw [idealSheafDataOfSubmodule_eq_ofIdealTop, idealSheafDataOfSubmodule_eq_ofIdealTop, h]
  exact Scheme.Modules.submodule_eq_of_obj_affineOpens_eq J₁ J₂ fun U ↦
    congrArg (fun I : X.IdealSheafData ↦ I.ideal U) key

end Stacks.Divisors

end
