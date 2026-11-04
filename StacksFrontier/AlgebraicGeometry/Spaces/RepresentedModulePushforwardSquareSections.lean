module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange

/-!
# The square of direct images of a represented morphism, on sections

The inverse of `AlgebraicGeometry.Space.representedModulePushforwardSquareIso` on sections over a
chart: the chart comparison of the direct images, followed by the restriction along the
identification of the two base changes.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section RepresentedSq

attribute [local irreducible] AlgebraicGeometry.Space.smallBaseChange
  AlgebraicGeometry.Space.representedSmallEtaleEquivalence
  AlgebraicGeometry.Space.structurePresheaf AlgebraicGeometry.Space.structureSheaf
  AlgebraicGeometry.Space.structureSheaf'

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- The inverse of the square of direct images, on sections. -/
theorem representedModulePushforwardSquareIso_inv_app_val_app
    (Q : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T'))
    (V : SmallEtale B S hS (yoneda.obj T))
    (z : ((modulePushforward B S hS (representedSpaceMap B S hS g)).obj
      ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj Q)).val.obj (op V)) :
    ((representedModulePushforwardSquareIso B S hS g hg).inv.app Q).val.app (op V) z =
      Q.val.map ((representedSmallEtaleBaseChangeIso B S hS g hg).inv.app V).op
        (((modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).hom.app
          ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj Q)).val.app
            (op V) z) := by
  simp only [representedModulePushforwardSquareIso, SheafOfModules.pushforwardCongr₂]
  rfl

end RepresentedSq

end AlgebraicGeometry.Space

end
