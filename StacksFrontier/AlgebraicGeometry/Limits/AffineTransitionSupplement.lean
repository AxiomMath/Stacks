module

public import StacksFrontier.AlgebraicGeometry.Limits.AffineTransition

/-!
# Limit cones of affine schemes detected on global sections

A cone of affine schemes over a diagram of affine schemes is a limit cone as soon as its rings of
global sections form a colimit cocone.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]

/-- **A cone of affine schemes over a diagram of affine schemes is a limit cone as soon as its
rings of global sections form a colimit cocone**: on affine schemes `Spec` and `Γ` are inverse
equivalences, and `Spec` preserves limits. -/
noncomputable def isLimitOfIsColimitΓ (c : Cone D) [IsAffine c.pt]
    (hc : IsColimit (Scheme.Γ.mapCocone c.op)) : IsLimit c := by
  let e : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := Functor.whiskerLeft D ΓSpec.adjunction.unit
  haveI (i : I) : IsIso (e.app i) := IsAffine.affine
  haveI : IsIso e := NatIso.isIso_of_isIso_app e
  have h0 : IsLimit (coneOfCoconeLeftOp (F := D ⋙ Scheme.Γ.rightOp) (Scheme.Γ.mapCocone c.op)) :=
    isLimitConeOfCoconeLeftOp _ hc
  have h1 := isLimitOfPreserves Scheme.Spec h0
  refine (IsLimit.postcomposeInvEquiv (asIso e) _).symm h1 |>.ofIsoLimit ?_
  refine Cone.ext (asIso (ΓSpec.adjunction.unit.app c.pt)).symm fun i => ?_
  have hnat := ΓSpec.adjunction.unit.naturality (c.π.app i)
  simp only [Iso.symm_hom, asIso_inv]
  rw [IsIso.eq_inv_comp]
  simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Functor.mapCone_π_app,
    coneOfCoconeLeftOp_π_app, NatIso.isIso_inv_app]
  rw [← Category.assoc, IsIso.comp_inv_eq]
  simpa [e] using hnat.symm

end AlgebraicGeometry.Scheme

end
