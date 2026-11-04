module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness

/-!
# The module of a quasi-coherent ideal sheaf, and finite generation on affine opens

Let `X` be a scheme and `I` a quasi-coherent ideal sheaf on `X`, presented by its affine-local
ideal data. Forgetting that `I` is an ideal gives a subsheaf `I · 𝒪_X` of the structure sheaf,
which this file identifies with the kernel of `𝒪_X ⟶ (V(I))_* 𝒪_{V(I)}`. The identification
makes `I · 𝒪_X` quasi-coherent, and hence makes the finite-type condition on it affine-local:
when `I · 𝒪_X` is of finite type, the ideal `I(U)` is finitely generated for every affine open
`U`, which is the hypothesis the algebraization theorems of Stacks chapter 52 are stated with.

## Main definitions

* `Stacks.Algebraization.idealModule` — the subsheaf `I · 𝒪_X` of the structure sheaf, as a
  sheaf of modules.

## Main results

* `Stacks.Algebraization.idealPowerMultiple_unit_eq_kernel` — `I · 𝒪_X` is the kernel of the
  unit map to the pushforward of the structure sheaf of the closed subscheme cut out by `I`.
* `Stacks.Algebraization.isQuasicoherent_idealModule` — `I · 𝒪_X` is quasi-coherent.
* `Stacks.Algebraization.affineIdealFG` — if `I · 𝒪_X` is of finite type then `I(U)` is
  finitely generated for every affine open `U`.

## Implementation notes

`I · 𝒪_X` is taken to be `idealPowerMultiple I 1 𝒪_X`, the first step of the ideal-power
filtration of the structure sheaf, rather than the kernel, so that it is the same object the
ideal-power filtration is built from. The two agree, and `idealPowerMultiple_unit_eq_kernel` is
that agreement; it is proved affine-locally, where the sections of the kernel are `I(U)` by
`kernelSubmodule_obj_affine` and the sections of `I · 𝒪_X` are `I(U) • Γ(X, U) = I(U)`.

## References

* [Stacks Project, Tag 0EI8](https://stacks.math.columbia.edu/tag/0EI8)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-- The subsheaf `I · 𝒪_X` of the structure sheaf attached to a quasi-coherent ideal sheaf `I`,
viewed as a sheaf of modules. -/
public noncomputable abbrev idealModule {X : Scheme.{u}} (I : X.IdealSheafData) : X.Modules :=
  (idealPowerMultiple I 1 (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules

/-- On an affine open `U`, the submodule `I(U) • Γ(X, U)` of `Γ(X, U)` is the ideal `I(U)`. -/
private lemma ideal_smul_top_eq {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    I.ideal U • (⊤ : Submodule Γ(X, U) Γ(X, U)) = (I.ideal U : Submodule Γ(X, U) Γ(X, U)) := by
  rw [Ideal.smul_top_eq_map]
  simp only [Algebra.algebraMap_self, Ideal.map_id, Submodule.restrictScalars_self]

/-- The subsheaf `I · 𝒪_X` is the kernel of the unit map `𝒪_X ⟶ (V(I))_* 𝒪_{V(I)}`. -/
public lemma idealPowerMultiple_unit_eq_kernel {X : Scheme.{u}} (I : X.IdealSheafData) :
    idealPowerMultiple I 1 (SheafOfModules.unit X.ringCatSheaf) =
      kernelSubmodule
        (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom) := by
  set O := SheafOfModules.unit X.ringCatSheaf
  set P := idealPowerMultiple I 1 O
  set Q := kernelSubmodule
    (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom) with hQ
  refine le_antisymm ((idealPowerMultiple_le_iff I 1 O Q).2 fun U => ?_)
    (submodule_le_of_affine Q P fun U => ?_)
  · rw [hQ, kernelSubmodule_obj_affine, pow_one]
    exact (ideal_smul_top_eq I U).le
  · rw [hQ, kernelSubmodule_obj_affine, ← ideal_smul_top_eq I U, ← pow_one (I.ideal U)]
    exact (idealPowerMultiple_le_iff I 1 O P).mp le_rfl U

/-- The subsheaf `I · 𝒪_X` of the structure sheaf is quasi-coherent. -/
public instance isQuasicoherent_idealModule {X : Scheme.{u}} (I : X.IdealSheafData) :
    (idealModule I).IsQuasicoherent := by
  have h := idealKernel_isQuasicoherent I
  rwa [← idealPowerMultiple_unit_eq_kernel I] at h

/-- On an affine open `U`, the sections of `I · 𝒪_X` are the ideal `I(U)`. -/
public lemma idealModule_obj_affine {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) :
    (idealPowerMultiple I 1 (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op U.1) =
      I.ideal U := by
  rw [idealPowerMultiple_unit_eq_kernel I]
  exact kernelSubmodule_obj_affine I U

/-- If the subsheaf `I · 𝒪_X` is of finite type, then the ideal `I(U)` is finitely generated for
every affine open `U`.

The sections of a quasi-coherent module of finite type over an affine open form a finite module
over the ring of functions, and over an affine open the sections of `I · 𝒪_X` are `I(U)`. -/
public lemma affineIdealFG {X : Scheme.{u}} (I : X.IdealSheafData)
    [(idealModule I).IsFiniteType] (U : X.affineOpens) :
    (I.ideal U).FG := by
  have hfinite : Module.Finite Γ(X, U) Γ(idealModule I, U.1) :=
    moduleFinite_sections_on_affine (idealModule I) U.1 U.2
  have hsub := idealModule_obj_affine I U
  let e : Γ(idealModule I, U.1) →ₗ[Γ(X, U)] I.ideal U :=
    { toFun := fun x => ⟨x.val, by rw [← hsub]; exact x.property⟩
      map_add' := fun x y => Subtype.ext rfl
      map_smul' := fun r x => Subtype.ext rfl }
  exact Module.Finite.iff_fg.mp (Module.Finite.of_surjective e fun y =>
    ⟨⟨y.val, by rw [hsub]; exact y.property⟩, Subtype.ext rfl⟩)

end Stacks.Algebraization

end

end
