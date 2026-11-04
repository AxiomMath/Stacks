module

public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.SchemeTheoretic
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization

/-!
# The scheme-theoretic support, read in a local ring

Let `F` be a quasi-coherent module of finite type on a scheme `X`. Its scheme-theoretic support
`AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport` is the ideal sheaf whose value on an
affine open is the annihilator of the sections there. This file computes the ideal it induces in
a local ring: it is the annihilator of the stalk.

## Main results

* `AlgebraicGeometry.Scheme.Modules.stalk_schemeTheoreticSupport`: the stalk at `x` of the
  scheme-theoretic support is `Ann_{𝒪_{X,x}} F_x`.
* `AlgebraicGeometry.Scheme.Modules.mem_support_schemeTheoreticSupport_iff`: a point lies in the
  support of the scheme-theoretic support exactly when the stalk there is nonzero.

## Implementation notes

The ideal a sheaf of ideals induces in a local ring is `AlgebraicGeometry.IdealSheafData.stalk`,
the extension of its sections along the germ map, and
`AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ` says that a single affine open neighbourhood
computes it. Over such an open both the local ring and the stalk of `F` are localizations — of
the sections of the structure sheaf at the prime of the point
(`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`) and of the sections of `F` at the same
prime (`Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ`) — so the computation is the
localization of annihilators of finite modules,
`AlgebraicGeometry.Scheme.Modules.map_annihilator_of_isLocalizedModule`. Finiteness of the
sections is where the finite type hypothesis on `F` enters.

The `𝒪_{X,x}`-module structure on `F_x` is not found by instance search, so it is introduced in
the statement with `letI`, as in
`StacksFrontier/AlgebraicGeometry/Scheme/Points/ModuleStalkSpecialization.lean`.

## References

* [Stacks Project, Tag 05JU](https://stacks.math.columbia.edu/tag/05JU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.ModuleStalkSpecialization

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]

/-- **The scheme-theoretic support of `F`, read in the local ring at `x`, is the annihilator of
the stalk `F_x`.** -/
theorem stalk_schemeTheoreticSupport (x : X) :
    letI := stalkModule F x
    IdealSheafData.stalk (schemeTheoreticSupport F) x =
      Module.annihilator (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  let := stalkModule F x
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have : Module.Finite Γ(X, U) Γ(F, U) := moduleFinite_sections_on_affine F U hU
  let := sectionsStalkModule F hxU
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    isScalarTower_sectionsStalk F hxU
  have : IsLocalizedModule.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal (germₗ F hxU) :=
    isLocalizedModule_germₗ F hU hxU
  rw [IdealSheafData.stalk_eq_map_germ (schemeTheoreticSupport F) x ⟨U, hU⟩ hxU,
    schemeTheoreticSupport_ideal F ⟨U, hU⟩]
  exact map_annihilator_of_isLocalizedModule
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (germₗ F hxU)

end AlgebraicGeometry.Scheme.Modules

end
