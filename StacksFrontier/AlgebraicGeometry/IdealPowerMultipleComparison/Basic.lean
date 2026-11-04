module

public import StacksFrontier.AlgebraicGeometry.IdealPowerHomColimit.Basic
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.IdealSmul
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CanonicalSectionsMap
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple

/-!
# The two models of `I ^ n • F` agree, and away from `V(I)` they are everything

Let `X` be a scheme, `I` a quasi-coherent sheaf of ideals given by its affine-local ideal data,
`n : ℕ`, and `F` a quasi-coherent sheaf of modules on `X`. There are two subsheaves `I ^ n • F`
of `F` in this repository:

* `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple`, the *least* subsheaf of `F`
  dominating the affine-local products `I(U) ^ n • Γ(F, U)`, which needs no hypothesis on `F`
  and is the object the filtration of [Stacks, Tag 01YB] and [Stacks, Tag 01PQ] is stated over;
* `Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul`, the subsheaf cut out by the compatible
  affine-local family `U ↦ I(U) ^ n • Γ(F, U)`, which needs `F` quasi-coherent but *computes*
  its sections over an affine open.

This file proves they agree for quasi-coherent `F`, a comparison the implementation note of
`Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul` records as true but unproved. Two
consequences follow at once for the first model, which had neither: its sections over an affine
open are exactly `I(U) ^ n • Γ(F, U)`, and it is quasi-coherent.

The last section is the step the proofs of [Stacks, Tag 01PQ] and [Stacks, Tag 01YB] use to pass
to `F' = I ^ m • F` without changing anything over the open complement `U = X \ V(I)`: over
every open contained in `U` the inclusion `I ^ n • F ⟶ F` is bijective on sections.

## Main results

* `ideal_eq_top_of_le_idealComplement`: on an affine open disjoint from the support of `I`, the
  ideal `I` is the unit ideal.
* `idealPowerMultiple_eq_idealPowSmul`: the two models agree.
* `obj_idealPowerMultiple`: the sections of `idealPowerMultiple I n F` over an affine open `U`
  are `I(U) ^ n • Γ(F, U)`.
* `isQuasicoherent_idealPowerMultiple`: `idealPowerMultiple I n F` is quasi-coherent.
* `obj_idealPowerMultiple_eq_top`: over an open contained in the complement of the support of
  `I`, `idealPowerMultiple I n F` has all the sections of `F`.
* `bijective_idealPowerMultiple_ι_app`: equivalently, the inclusion `I ^ n • F ⟶ F` is bijective
  on the sections over any such open.

## Implementation notes

The inclusion `idealPowerMultiple ≤ idealPowSmul` is the universal property
`idealPowerMultiple_le_iff` together with the computation `obj_idealPowSmul` of the affine
sections of the second model. The reverse inclusion is where the sheaf condition is used: a
section lying locally in the affine-local family lies, on each affine open of a cover, in
`idealPowerMultiple` by `le_idealPowerMultiple_obj`, and affine opens form a basis, so the sieve
of that section is a covering sieve and `SheafOfModules.Submodule.isSheaf` applies. No
quasi-coherence is needed for that direction; it is carried only because `idealPowSmul` is not
defined without it.

The statement over an open contained in the complement is **pointwise on sections** rather than
an isomorphism of restricted sheaves, which avoids transporting a module sheaf along the open
immersion `U ⟶ X` — a step that is not definitional, because the module structure of a
restricted sheaf acts through a component of `Scheme.Opens.ι.appIso`.

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.GabberColimit
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealPowerHomColimit
open Stacks.AlgebraicGeometry.IdealPowerSmul
open Stacks.LocalCohomology

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerComparison

variable {X : Scheme.{u}}

/-! ### Away from the support the ideal is the unit ideal -/

/-- **On an affine open disjoint from the support of `I`, the ideal `I` is the unit ideal.**
Every point of such an affine open `W` lies outside `V(I.ideal W)`, so the basic opens of the
elements of `I.ideal W` cover `W`; on an affine open that says exactly that `I.ideal W` is the
unit ideal. -/
theorem ideal_eq_top_of_le_idealComplement (I : X.IdealSheafData) {V : X.Opens}
    (hV : V ≤ idealComplement I) (W : X.affineOpens) (hWV : W.1 ≤ V) :
    I.ideal W = ⊤ := by
  rw [← Ideal.span_eq (I.ideal W), ← W.2.self_le_iSup_basicOpen_iff]
  intro x hx
  have hns : x ∉ I.supportSet := hV (hWV hx)
  have hz : x ∉ X.zeroLocus (U := W.1) (I.ideal W) := fun hzero ↦
    hns ((I.mem_supportSet_iff_of_mem (show x ∈ (W : X.Opens) from hx)).2 hzero)
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe, not_forall] at hz
  obtain ⟨g, hgI, hgb⟩ := hz
  exact Opens.mem_iSup.mpr ⟨⟨g, hgI⟩, not_not.mp hgb⟩

/-! ### The two models of `I ^ n • F` -/

/-- The least subsheaf dominating the affine-local products is contained in the subsheaf cut out
by them: the latter is one of the subsheaves the former is an infimum over, because its sections
over an affine open are exactly the affine-local product. -/
theorem idealPowerMultiple_le_idealPowSmul (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] : idealPowerMultiple I n F ≤ idealPowSmul I n F := by
  rw [idealPowerMultiple_le_iff]
  intro U
  rw [obj_idealPowSmul I n F U]

/-- The subsheaf cut out by the affine-local products is contained in the least subsheaf
dominating them. This is the direction that uses the sheaf condition: a section lying locally in
the family lies in `idealPowerMultiple` over each affine open of a cover, and affine opens form
a basis. -/
theorem idealPowSmul_le_idealPowerMultiple (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] : idealPowSmul I n F ≤ idealPowerMultiple I n F := by
  intro V s hs
  refine (idealPowerMultiple I n F).isSheaf s fun x hx ↦ ?_
  obtain ⟨-, ⟨W, hWaff, rfl⟩, hxW, hWle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.unop.isOpen
  refine ⟨W, homOfLE (show W ≤ V.unop from hWle), ?_, hxW⟩
  exact le_idealPowerMultiple_obj I n F ⟨W, hWaff⟩ (hs ⟨W, hWaff⟩ hWle)

/-- **The two models of `I ^ n • F` agree for quasi-coherent `F`.** -/
theorem idealPowerMultiple_eq_idealPowSmul (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] : idealPowerMultiple I n F = idealPowSmul I n F :=
  le_antisymm (idealPowerMultiple_le_idealPowSmul I n F)
    (idealPowSmul_le_idealPowerMultiple I n F)

/-- **The sections of `I ^ n • F` over an affine open `U` are `I(U) ^ n • Γ(F, U)`.** Stated for
`idealPowerMultiple`, whose definition as an infimum does not determine them. -/
theorem obj_idealPowerMultiple (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] (U : X.affineOpens) :
    (idealPowerMultiple I n F).toSubmodule.obj (op U.1) =
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) := by
  rw [idealPowerMultiple_eq_idealPowSmul I n F, obj_idealPowSmul I n F U]

/-- `I ^ n • F` is quasi-coherent, for the infimum model. -/
theorem isQuasicoherent_idealPowerMultiple (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] : (idealPowerMultiple I n F).toSheafOfModules.IsQuasicoherent := by
  rw [idealPowerMultiple_eq_idealPowSmul I n F]
  exact isQuasicoherent_idealPowSmul I n F

/-! ### Over the complement of the support nothing is cut away -/

/-- **Over an open contained in the complement of `V(I)`, `I ^ n • F` has all the sections of
`F`.** This is the step by which the proofs of [Stacks, Tag 01PQ] and [Stacks, Tag 01YB] replace
`F` by `I ^ m • F` without changing the sections over `U = X \ V(I)`. -/
theorem obj_idealPowerMultiple_eq_top (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] {V : X.Opens} (hV : V ≤ idealComplement I) :
    (idealPowerMultiple I n F).toSubmodule.obj (op V) = ⊤ := by
  rw [idealPowerMultiple_eq_idealPowSmul I n F]
  exact localSections_idealPowFamily_eq_top I n F
    fun W hWV ↦ ideal_eq_top_of_le_idealComplement I hV W hWV

/-- A section of `F` over an open contained in the complement of `V(I)` is a section of
`I ^ n • F`. -/
theorem mem_idealPowerMultiple (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] {V : X.Opens} (hV : V ≤ idealComplement I)
    (s : F.val.obj (op V)) :
    s ∈ (idealPowerMultiple I n F).toSubmodule.obj (op V) := by
  rw [obj_idealPowerMultiple_eq_top I n F hV]
  exact Submodule.mem_top

/-- **Over an open contained in the complement of `V(I)`, the inclusion `I ^ n • F ⟶ F` is
bijective on sections.** The pointwise form of `obj_idealPowerMultiple_eq_top`; it needs no
transport of a module sheaf along the open immersion `U ⟶ X`. -/
theorem bijective_idealPowerMultiple_ι_app (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] {V : X.Opens} (hV : V ≤ idealComplement I) :
    Function.Bijective ((idealPowerMultiple I n F).ι.val.app (op V)).hom := by
  constructor
  · intro a b hab
    exact Subtype.ext hab
  · intro s
    exact ⟨⟨s, mem_idealPowerMultiple I n F hV s⟩, rfl⟩

end Stacks.AlgebraicGeometry.IdealPowerComparison

end
