module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.AffineCore
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.Restrict

/-!
# Systems of affine schemes over an affine base

A directed system of affine schemes `T_j` over an affine scheme `B`, with an affine vertex, is
isomorphic, over `B ≅ Spec Γ(B)`, to the system of spectra of the rings of global sections, so
the colimit property `IsColim` for the one system is equivalent to that for the other.
This file transports the affine case of Stacks 09RE along that isomorphism.

## Main definitions

* `Stacks.LimitHomDescent.SchemeSystem.ringSystem`: the directed system of `Γ(B)`-algebras
  `Γ(T_j)` with the cocone `Γ(T)`.

## Main results

* `Stacks.LimitHomDescent.SchemeSystem.isColim_iff_ringSystem`: `S.IsColim X Y` holds if and only
  if it holds for the system of spectra of the rings of sections and the pullbacks of `X`, `Y`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.DerivedPullback (schemeFactorIso schemeFactorHom)

attribute [local instance 10000] HasDerivedCategory.standard

universe v u

namespace Stacks.LimitHomDescent.SchemeSystem

open _root_.Stacks.LimitHomDescent.Affine

variable {B : Scheme.{u}} {J : Type v} [Preorder J] (S : SchemeSystem.{v, u} B J)

/-- **The rings of global sections of the stages**, as a directed system of `Γ(B)`-algebras. -/
def ringSystem : Affine.RingSystem.{v, u} Γ(B, ⊤) J where
  A j := Γ(S.stage j, ⊤)
  φ j := (S.toBase j).appTop
  β h := (S.transition h).appTop
  φ_β h := by rw [← Scheme.Hom.comp_appTop, S.transition_toBase]
  β_β h h' := by rw [← Scheme.Hom.comp_appTop, S.transition_comp]
  β_refl i := by rw [S.transition_refl, Scheme.Hom.id_appTop]
  lim := Γ(S.limit, ⊤)
  φlim := S.limitToBase.appTop
  γ j := (S.proj j).appTop
  φ_γ j := by rw [← Scheme.Hom.comp_appTop, S.proj_toBase]
  β_γ h := by rw [← Scheme.Hom.comp_appTop, S.proj_transition]

variable [IsAffine B] [∀ j, IsAffine (S.stage j)] [IsAffine S.limit]

/-- The comparison of `S` with the system of spectra of its rings of sections, over `B`. -/
def toRingSystemHom : Hom (S.ringSystem.toSchemeSystem.comp B.isoSpec.inv) S where
  app j := (S.stage j).isoSpec.inv
  app_toBase j := (Scheme.isoSpec_inv_naturality (S.toBase j)).symm
  app_transition h := (Scheme.isoSpec_inv_naturality (S.transition h)).symm
  limitApp := S.limit.isoSpec.inv
  limitApp_toBase := (Scheme.isoSpec_inv_naturality S.limitToBase).symm
  limitApp_proj j := (Scheme.isoSpec_inv_naturality (S.proj j)).symm

/-- Each component of `toRingSystemHom` is an isomorphism. -/
instance (j : J) : IsIso (S.toRingSystemHom.app j) :=
  inferInstanceAs (IsIso (S.stage j).isoSpec.inv)

/-- The component of `toRingSystemHom` at the limit is an isomorphism. -/
instance : IsIso S.toRingSystemHom.limitApp := inferInstanceAs (IsIso S.limit.isoSpec.inv)

/-- `S.IsColim X Y` holds if and only if the system of spectra of the rings of sections of `S`
satisfies `IsColim` for the pullbacks of `X` and `Y` along `B.isoSpec.inv`. -/
theorem isColim_iff_ringSystem [IsDirected J (· ≤ ·)] (X Y : DMod B) :
    S.IsColim X Y ↔ S.ringSystem.toSchemeSystem.IsColim ((pb B.isoSpec.inv).obj X)
      ((pb B.isoSpec.inv).obj Y) :=
  (Hom.isColim_iff_of_isIso S S.toRingSystemHom X Y).trans (isColim_comp_iff _ X Y)

end Stacks.LimitHomDescent.SchemeSystem

end
