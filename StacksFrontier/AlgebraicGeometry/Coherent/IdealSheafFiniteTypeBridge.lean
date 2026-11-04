module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.IdealPowerBridge
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic

/-!
# Finite sections on affine opens, and the finite type of a sheaf of ideals

Two notions of "finite type" for a sheaf of ideals on a scheme `X` are in use:

* `AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`, finite generation of the ideal
  `I.ideal V` for every affine open `V`;
* `SheafOfModules.IsFiniteType` of `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPow I n`,
  the sheaf-of-modules condition, which is the one
  `Stacks.AlgebraicGeometry.IsIdealAffineCovering` and [Stacks, Tag 0F89] are stated with.

Passing from the first to the second needs finite type of a quasi-coherent module to be checked
on an affine open cover, from the sections alone. This file supplies that.

The missing ingredient is the converse of
`Stacks.AlgebraicGeometry.ClosedImmersionCoherence.finite_specModule`: that lemma reads off
finiteness of `specModule F hV` from finite type of `F`, while here finiteness of the sections
`Γ(F, V)` is the hypothesis and finiteness of `specModule F hV` is the goal.  The two modules
are identified by `AlgebraicGeometry.fromSpecSectionsLinearEquiv` transported along the
comparison of `F.restrict hV.fromSpec` with `specRestrict F hV`; the latter is the restriction
functor applied to `hV.isoSpec.inv ≫ V.ι`, which *is* `hV.fromSpec`.

## Main definitions

* `Stacks.AlgebraicGeometry.FiniteTypeBridge.specModuleLinearEquiv`: the sections `Γ(F, V)` over
  an affine open `V` are the module `specModule F hV` of [Stacks, Tag 01XZ] (4), `Γ(X, V)`-
  linearly.

## Main results

* `Stacks.AlgebraicGeometry.FiniteTypeBridge.finite_specModule_of_finite_sections`: the converse
  of `finite_specModule`, finiteness of `specModule F hV` from finiteness of `Γ(F, V)`.
* `Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_of_finite_sections_affineOpens`:
  **finite type of a quasi-coherent module is detected by its sections on an affine open
  cover.**
* `Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_idealPow`: **the bridge.** If every
  `I.ideal V` is finitely generated then `idealPow I n` is of finite type as an `𝒪_X`-module.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0F89](https://stacks.math.columbia.edu/tag/0F89)
-/

@[expose] public section

open CategoryTheory Limits Opposite SheafOfModules TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe u

namespace Stacks.AlgebraicGeometry.FiniteTypeBridge

variable {X : Scheme.{u}}

/-! ### The sections over an affine open as the module of condition (4) -/

/-- Restricting `F` along `IsAffineOpen.fromSpec` is restricting to `V` and then reading the
result on `Spec Γ(X, V)`: the two are the restriction functor applied to the two spellings
`hV.fromSpec` and `hV.isoSpec.inv ≫ V.ι` of one morphism. -/
noncomputable def fromSpecRestrictIso (F : X.Modules) {V : X.Opens} (hV : IsAffineOpen V) :
    F.restrict hV.fromSpec ≅ specRestrict F hV :=
  (Scheme.Modules.restrictFunctorComp hV.isoSpec.inv V.ι).app F

/-- **The sections of `F` over an affine open `V` are the module `specModule F hV`** of
[Stacks, Tag 01XZ] (4), `Γ(X, V)`-linearly. -/
noncomputable def specModuleLinearEquiv (F : X.Modules) {V : X.Opens} (hV : IsAffineOpen V) :
    Γ(F, V) ≃ₗ[Γ(X, V)] specModule F hV :=
  (fromSpecSectionsLinearEquiv F hV).symm.trans
    (moduleSpecΓFunctor.mapIso (fromSpecRestrictIso F hV)).toLinearEquiv

/-- **The converse of
`Stacks.AlgebraicGeometry.ClosedImmersionCoherence.finite_specModule`**: if the sections of `F`
over an affine open `V` are a finite `Γ(X, V)`-module then so is `specModule F hV`.  No
hypothesis on `F` is needed: the two modules are isomorphic. -/
theorem finite_specModule_of_finite_sections (F : X.Modules) {V : X.Opens}
    (hV : IsAffineOpen V) (h : Module.Finite Γ(X, V) Γ(F, V)) :
    Module.Finite Γ(X, V) (specModule F hV) :=
  Module.Finite.equiv (specModuleLinearEquiv F hV)

/-! ### Finite type from the sections on an affine open cover -/

/-- **Finite type of a quasi-coherent module is detected by its sections on an affine open
cover.**  Combined with `AlgebraicGeometry.moduleFinite_sections_on_affine`, which is the
converse, this says that for a quasi-coherent module finite type is exactly finiteness of the
sections over the affine opens. -/
theorem isFiniteType_of_finite_sections_affineOpens (F : X.Modules) [F.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hcov : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, Module.Finite Γ(X, U i) Γ(F, U i)) : F.IsFiniteType :=
  isFiniteType_of_cover_isFiniteTildeOn F U hcov hU fun i =>
    isFiniteTildeOn_of_finite_specModule F (U i) (hU i)
      (finite_specModule_of_finite_sections F (hU i) (h i))

/-- The affine opens of `X` cover `X` and their sections detect finite type: the special case of
`isFiniteType_of_finite_sections_affineOpens` for the cover by *all* affine opens. -/
theorem isFiniteType_of_finite_sections (F : X.Modules) [F.IsQuasicoherent]
    (h : ∀ V : X.affineOpens, Module.Finite Γ(X, V.1) Γ(F, V.1)) : F.IsFiniteType :=
  isFiniteType_of_finite_sections_affineOpens F (fun V : X.affineOpens => (V : X.Opens))
    (IsOpenCover.mk (iSup_affineOpens_eq_top X)) (fun V => V.2) h

/-! ### The finite type of a power of a sheaf of ideals -/

/-- The sections of `Iⁿ` over an affine open `V` are the finite `Γ(X, V)`-module `I(V)ⁿ`, as
soon as `I(V)` is finitely generated. -/
theorem finite_sections_idealPow (I : X.IdealSheafData) (n : ℕ) (V : X.affineOpens)
    (h : (I.ideal V).FG) : Module.Finite Γ(X, V.1) Γ(idealPow I n, V.1) := by
  have he : (idealPowerMultiple I n (structureModule X)).toSubmodule.obj (op V.1)
      = (I.ideal V ^ n : Ideal Γ(X, V.1)) := obj_idealPow_affineOpen I n V
  have hfin : Module.Finite Γ(X, V.1) (I.ideal V ^ n : Ideal Γ(X, V.1)) :=
    Module.Finite.iff_fg.mpr h.pow
  exact Module.Finite.equiv (M := (I.ideal V ^ n : Ideal Γ(X, V.1)))
    (N := Γ(idealPow I n, V.1)) (LinearEquiv.ofEq _ _ he.symm)

/-- **The bridge between the two finite type conditions on a sheaf of ideals.**  If the ideal
`I.ideal V` is finitely generated for every affine open `V` — that is, if `I` is of finite type
in the sense of `AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType` — then the sheaf of
modules `Iⁿ` is of finite type.  At `n = 1` this is the hypothesis
`Stacks.AlgebraicGeometry.IsIdealAffineCovering.isFiniteType` of [Stacks, Tag 0F89]. -/
theorem isFiniteType_idealPow (I : X.IdealSheafData) (n : ℕ)
    (hI : ∀ V : X.affineOpens, (I.ideal V).FG) : (idealPow I n).IsFiniteType := by
  have : (structureModule X).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  exact isFiniteType_of_finite_sections _ fun V => finite_sections_idealPow I n V (hI V)

end Stacks.AlgebraicGeometry.FiniteTypeBridge

end
