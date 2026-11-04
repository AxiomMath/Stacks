module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The ideal-power multiple of a sheaf of modules on a scheme

Let `X` be a scheme, let `I` be a quasi-coherent sheaf of ideals on `X` presented by its
affine-local ideal data, and let `M` be a sheaf of modules on `X`. This file constructs the
subsheaf `I ^ n • M` of `M` and proves the structural facts about it that do not involve
cohomology: it decreases as `n` grows, and the resulting inclusions `I ^ m • M ⟶ I ^ n • M`
for `n ≤ m` are compatible both with the inclusions into `M` and with each other.

The subsheaf is defined as the least subsheaf of `M` which, on every affine open `U`, contains
the submodule `I(U) ^ n • M(U)`. Taking an infimum rather than an affine-local image keeps the
construction available when `M` is not quasi-coherent, which is what an inverse limit of such
subsheaves requires.

## Main definitions

* `SheafOfModules.Submodule.homOfLE` is the inclusion between two submodules of a sheaf of
  modules comparable under `≤`.
* `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple` is the subsheaf `I ^ n • M` of `M`.
* `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultipleMap` is the inclusion
  `I ^ m • M ⟶ I ^ n • M` for `n ≤ m`.

## Main results

* `SheafOfModules.Submodule.homOfLE_ι` and `SheafOfModules.Submodule.homOfLE_comp`: the
  inclusions between submodules are compatible with the inclusion into the ambient sheaf and
  with composition.
* `Stacks.AlgebraicGeometry.IdealPower.le_idealPowerMultiple_obj`: the defining affine-local
  lower bound holds for `I ^ n • M` itself.
* `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_le_iff`: the affine-local universal
  property characterising `I ^ n • M`.
* `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_antitone`: `I ^ m • M ≤ I ^ n • M`
  for `n ≤ m`.
* `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultipleMap_comp_ι` and
  `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultipleMap_comp`: the inclusions of the
  filtration compose to the inclusion into `M`, and compose with each other.

## Implementation notes

`SheafOfModules.Submodule.homOfLE` fills a gap in Mathlib: `PresheafOfModules.Submodule` has
`homOfLE` together with `homOfLE_ι`, but the sheaf-level `SheafOfModules.Submodule` has only
`ι`, with no morphism between two comparable submodules. The sheaf-level morphism is the
presheaf-level one with no further condition to check, since a morphism of sheaves of modules
is by definition a morphism of the underlying presheaves. The order on
`SheafOfModules.Submodule` is `PartialOrder.lift toSubmodule`, so `N₁ ≤ N₂` is definitionally
the presheaf-level inequality and no coercion is needed.

`AlgebraicGeometry.Scheme.Modules` is a `def`, not an `abbrev`, so instance search does not see
through it to `SheafOfModules X.ringCatSheaf`; Mathlib therefore re-exports `Category`,
`Abelian` and `HasLimits` for it by `inferInstanceAs` but not the complete lattice of
submodules. `AlgebraicGeometry.Scheme.Modules.instCompleteLatticeSubmodule` supplies that
missing re-export, which is what makes the `sInf` below elaborate. This is a transport of an
existing Mathlib instance, not a new order.

The ideal data `I : X.IdealSheafData` is indexed by affine opens, which is why the defining
condition quantifies over `X.affineOpens` rather than over all opens. No quasi-coherence of
`M` is assumed anywhere in this file, and no Noetherian or finiteness hypothesis is used:
antitonicity is `Ideal.pow_le_pow_right` applied section by section.

## References

* [Stacks Project, Tag 02OA](https://stacks.math.columbia.edu/tag/02OA) uses this filtration;
  the statements proved here are the part of its setup that is independent of cohomology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe v v₁ u₁ u

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{v} R}

/-- The inclusion of one submodule of a sheaf of modules into a larger one.

This is the presheaf-level `PresheafOfModules.Submodule.homOfLE`; a morphism of sheaves of
modules is a morphism of the underlying presheaves, so there is nothing further to check. -/
public noncomputable def homOfLE {N₁ N₂ : M.Submodule} (hle : N₁ ≤ N₂) :
    N₁.toSheafOfModules ⟶ N₂.toSheafOfModules :=
  ⟨PresheafOfModules.Submodule.homOfLE hle⟩

@[simp]
public lemma homOfLE_val {N₁ N₂ : M.Submodule} (hle : N₁ ≤ N₂) :
    (homOfLE hle).val = PresheafOfModules.Submodule.homOfLE hle := rfl

/-- The inclusion `N₁ ⟶ N₂` followed by the inclusion of `N₂` into `M` is the inclusion of
`N₁` into `M`. -/
@[simp]
public lemma homOfLE_ι {N₁ N₂ : M.Submodule} (hle : N₁ ≤ N₂) :
    homOfLE hle ≫ N₂.ι = N₁.ι :=
  Hom.ext (PresheafOfModules.Submodule.homOfLE_ι hle)

/-- The inclusions between submodules of a sheaf of modules compose. -/
public lemma homOfLE_comp {N₁ N₂ N₃ : M.Submodule} (h₁ : N₁ ≤ N₂) (h₂ : N₂ ≤ N₃) :
    homOfLE h₁ ≫ homOfLE h₂ = homOfLE (h₁.trans h₂) := rfl

end SheafOfModules.Submodule

namespace AlgebraicGeometry.Scheme.Modules

/-- The complete lattice of submodules of a sheaf of modules on a scheme.

`Scheme.Modules` is a `def`, so instance search does not unfold it to `SheafOfModules`; this
transports Mathlib's `SheafOfModules.Submodule.instCompleteLattice` across that definition. -/
public noncomputable instance instCompleteLatticeSubmodule {X : Scheme.{u}} {M : X.Modules} :
    CompleteLattice M.Submodule :=
  SheafOfModules.Submodule.instCompleteLattice

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.AlgebraicGeometry.IdealPower

variable {X : Scheme.{u}}

/-- The subsheaf `I ^ n • M` of a sheaf of modules `M` on a scheme `X`.

It is the least subsheaf of `M` which, on every affine open `U`, contains the submodule
`I(U) ^ n • M(U)`. Defining it as an infimum rather than as an affine-local image keeps the
construction available when `M` is not quasi-coherent. -/
public noncomputable def idealPowerMultiple (I : X.IdealSheafData) (n : ℕ) (M : X.Modules) :
    M.Submodule :=
  sInf { N | ∀ U : X.affineOpens,
    I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U)) ≤ N.toSubmodule.obj (op U.1) }

/-- The subsheaf `I ^ n • M` satisfies its own defining affine-local lower bound. -/
public lemma le_idealPowerMultiple_obj (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    (U : X.affineOpens) :
    I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U)) ≤
      (idealPowerMultiple I n M).toSubmodule.obj (op U.1) := by
  show _ ≤ (sInf ((fun P : M.Submodule => P.toSubmodule) ''
    {P : M.Submodule | ∀ V : X.affineOpens,
      I.ideal V ^ n • (⊤ : Submodule Γ(X, V) Γ(M, V)) ≤
        P.toSubmodule.obj (op V.1)})).obj (op U.1)
  rw [PresheafOfModules.Submodule.sInf_obj]
  refine le_iInf₂ fun P hP ↦ ?_
  obtain ⟨Q, hQ, rfl⟩ := hP
  exact hQ U

/-- The affine-local universal property characterising the subsheaf `I ^ n • M`: a submodule of
`M` contains `I ^ n • M` exactly when it contains `I(U) ^ n • M(U)` on every affine open `U`. -/
public lemma idealPowerMultiple_le_iff (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    (N : M.Submodule) :
    idealPowerMultiple I n M ≤ N ↔
      ∀ U : X.affineOpens,
        I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U)) ≤
          N.toSubmodule.obj (op U.1) :=
  ⟨fun h U ↦ (le_idealPowerMultiple_obj I n M U).trans (h (op U.1)), fun h ↦ sInf_le h⟩

/-- The ideal-power filtration is decreasing: `I ^ m • M ≤ I ^ n • M` for `n ≤ m`. -/
public lemma idealPowerMultiple_antitone (I : X.IdealSheafData) (M : X.Modules) {n m : ℕ}
    (h : n ≤ m) : idealPowerMultiple I m M ≤ idealPowerMultiple I n M := by
  rw [idealPowerMultiple_le_iff]
  intro U
  exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right h)).trans
    (le_idealPowerMultiple_obj I n M U)

/-- The inclusion `I ^ m • M ⟶ I ^ n • M` of sheaves of modules, for `n ≤ m`. -/
public noncomputable def idealPowerMultipleMap (I : X.IdealSheafData) (M : X.Modules) {n m : ℕ}
    (h : n ≤ m) :
    (idealPowerMultiple I m M).toSheafOfModules ⟶ (idealPowerMultiple I n M).toSheafOfModules :=
  SheafOfModules.Submodule.homOfLE (idealPowerMultiple_antitone I M h)

/-- The inclusion `I ^ m • M ⟶ I ^ n • M` followed by the inclusion of `I ^ n • M` into `M` is
the inclusion of `I ^ m • M` into `M`. -/
@[simp]
public lemma idealPowerMultipleMap_comp_ι (I : X.IdealSheafData) (M : X.Modules) {n m : ℕ}
    (h : n ≤ m) :
    idealPowerMultipleMap I M h ≫ (idealPowerMultiple I n M).ι =
      (idealPowerMultiple I m M).ι :=
  SheafOfModules.Submodule.homOfLE_ι _

/-- The inclusions of the ideal-power filtration compose. -/
public lemma idealPowerMultipleMap_comp (I : X.IdealSheafData) (M : X.Modules) {n m k : ℕ}
    (h : n ≤ m) (h' : m ≤ k) :
    idealPowerMultipleMap I M h' ≫ idealPowerMultipleMap I M h =
      idealPowerMultipleMap I M (h.trans h') :=
  SheafOfModules.Submodule.homOfLE_comp _ _

end Stacks.AlgebraicGeometry.IdealPower

end
