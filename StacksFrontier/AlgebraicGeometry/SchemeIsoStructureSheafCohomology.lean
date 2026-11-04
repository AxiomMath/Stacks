module

public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximationLocal
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.GlobalSheafCohomology
public import StacksFrontier.AlgebraicGeometry.Modules.SchemeIsoRingCatSheafHom

/-!
# Sheaf cohomology of the structure sheaf along an isomorphism of schemes

For an isomorphism of schemes `v : Y ≅ Y'`, the structure sheaf of `Y'`, read as a sheaf of
modules over itself, is the pushforward along `v` of the structure sheaf of `Y`. Consequently
vanishing of the degree-`n` sheaf cohomology of the one gives vanishing for the other.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.Cohomology.SchemeIso

attribute [local instance] HasDerivedCategory.standard

variable {Y Y' : AlgebraicGeometry.Scheme.{u}}

/-- For `v : Y ≅ Y'` an isomorphism of schemes, the structure sheaf of `Y'` as a module over
itself is the pushforward along `v` of the structure sheaf of `Y`. -/
def unitPushforwardIso (v : Y ≅ Y') :
    SheafOfModules.unit Y'.ringCatSheaf ≅
      (AlgebraicGeometry.Scheme.Modules.pushforward v.hom).obj
        (SheafOfModules.unit Y.ringCatSheaf) :=
  @asIso _ _ _ _ _
    (Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit v.hom.toRingCatSheafHom)

/-- **Vanishing of the sheaf cohomology of the structure sheaf transports along an isomorphism
of schemes**: if every degree-`n` class of the abelian sheaf underlying `𝒪_Y` is zero, then so
is every degree-`n` class of the one underlying `𝒪_{Y'}`. -/
theorem eq_zero_sheafH_of_iso (v : Y ≅ Y') (n : ℕ)
    (h : ∀ x : Sheaf.H.{u} ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
      (SheafOfModules.unit Y.ringCatSheaf)) n, x = 0)
    (x : Sheaf.H.{u} ((SheafOfModules.toSheaf Y'.ringCatSheaf).obj
      (SheafOfModules.unit Y'.ringCatSheaf)) n) : x = 0 := by
  have h0 : Sheaf.H.map.{u}
      ((SheafOfModules.toSheaf Y'.ringCatSheaf).map (unitPushforwardIso v).hom) n x = 0 :=
    Stacks.Cohomology.ClosedImmersion.eq_zero_sheafH_pushforward v.hom _ n h _
  have he : (SheafOfModules.toSheaf Y'.ringCatSheaf).map (unitPushforwardIso v).hom ≫
      (SheafOfModules.toSheaf Y'.ringCatSheaf).map (unitPushforwardIso v).inv = 𝟙 _ :=
    ((SheafOfModules.toSheaf Y'.ringCatSheaf).mapIso (unitPushforwardIso v)).hom_inv_id
  calc x
      = Sheaf.H.map.{u} (𝟙 _) n x := (Sheaf.H.map_id_apply x).symm
    _ = Sheaf.H.map.{u} ((SheafOfModules.toSheaf Y'.ringCatSheaf).map
          (unitPushforwardIso v).hom ≫ (SheafOfModules.toSheaf Y'.ringCatSheaf).map
            (unitPushforwardIso v).inv) n x := by rw [he]
    _ = Sheaf.H.map.{u} ((SheafOfModules.toSheaf Y'.ringCatSheaf).map
          (unitPushforwardIso v).inv) n (Sheaf.H.map.{u}
            ((SheafOfModules.toSheaf Y'.ringCatSheaf).map (unitPushforwardIso v).hom) n x) :=
        Sheaf.H.map_comp_apply _ _ _
    _ = 0 := by rw [h0, map_zero]

end Stacks.Cohomology.SchemeIso
