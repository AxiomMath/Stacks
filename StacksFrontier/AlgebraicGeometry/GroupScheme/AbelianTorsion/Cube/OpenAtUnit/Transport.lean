module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CubeRelation

/-!
# Transporting trivializations between the two spellings of pullback

Triviality of `a^* ρ^* N` (in the `Scheme.Modules.pullback` spelling) from triviality of `g^* N`
(in the `RingedSpaceModuleAdjunction.modulePullback` spelling) along `a ≫ ρ = b ≫ g`, and back.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.CubeOpenAtUnit

/-- If `g^* N` is trivial and `a ≫ ρ = b ≫ g`, then `a^* ρ^* N` is trivial. -/
theorem nonempty_pullback_pullback_iso_unit {Q X Y Z' : Scheme.{u}} (ρ : X ⟶ Q) (N : Q.Modules)
    (a : Y ⟶ X) (b : Y ⟶ Z') (g : Z' ⟶ Q) (h : a ≫ ρ = b ≫ g)
    (hg : Nonempty ((modulePullback g.toLRSHom.toShHom).obj N ≅
      SheafOfModules.unit (structureSheafRing Z'.toRingedSpace))) :
    Nonempty ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback ρ).obj N) ≅
      SheafOfModules.unit Y.ringCatSheaf) := by
  obtain ⟨t⟩ := hg
  have e1 : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback ρ).obj N) ≅
      (Scheme.Modules.pullback (b ≫ g)).obj N :=
    (Scheme.Modules.pullbackComp a ρ).app N ≪≫ eqToIso (by rw [h])
  have e2 : (Scheme.Modules.pullback (b ≫ g)).obj N ≅
      (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback g).obj N) :=
    ((Scheme.Modules.pullbackComp b g).app N).symm
  have e3 : (Scheme.Modules.pullback g).obj N ≅ SheafOfModules.unit Z'.ringCatSheaf :=
    (Stacks.ProjectiveBundleQuotients.pullbackIso g).app N ≪≫ t
  have e4 : (Scheme.Modules.pullback b).obj (SheafOfModules.unit Z'.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
    (Stacks.ProjectiveBundleQuotients.pullbackIso b).app _ ≪≫
      modulePullbackObjUnitIso b.toLRSHom.toShHom
  exact ⟨e1 ≪≫ e2 ≪≫ (Scheme.Modules.pullback b).mapIso e3 ≪≫ e4⟩

/-- If `a^* ρ^* N` is trivial (in the `modulePullback` spelling for `a`), so is `(a ≫ ρ)^* N`. -/
theorem nonempty_modulePullback_comp_iso_unit {Q X Y : Scheme.{u}} (ρ : X ⟶ Q) (N : Q.Modules)
    (a : Y ⟶ X)
    (h : Nonempty ((modulePullback a.toLRSHom.toShHom).obj ((Scheme.Modules.pullback ρ).obj N) ≅
      SheafOfModules.unit (structureSheafRing Y.toRingedSpace))) :
    Nonempty ((modulePullback (a ≫ ρ).toLRSHom.toShHom).obj N ≅
      SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) := by
  obtain ⟨t⟩ := h
  exact ⟨(modulePullbackComp a.toLRSHom.toShHom ρ.toLRSHom.toShHom).app N ≪≫
    (modulePullback a.toLRSHom.toShHom).mapIso
      ((Stacks.ProjectiveBundleQuotients.pullbackIso ρ).app N).symm ≪≫ t⟩

end Stacks.CubeOpenAtUnit

end
