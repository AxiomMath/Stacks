module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleBaseChangePasting

/-!
# The base change map and the units of the direct image adjunctions

Let `h ≫ f' = e ≫ g` be a commutative square of schemes, with `g : T ⟶ S` and `h : Y ⟶ X'`. The
underived base change map `β : f'⁻¹ g_* ⟶ h_* e⁻¹` is the mate of the comparison
`g_* e_* ≅ f'_* h_*`. At `g⁻¹ A` for a sheaf `A` on `S`, it carries `f'⁻¹` of the unit
`A ⟶ g_* g⁻¹ A` to the unit `f'⁻¹ A ⟶ h_* h⁻¹ f'⁻¹ A`, up to the comparison
`e⁻¹ g⁻¹ ≅ h⁻¹ f'⁻¹` (`Stacks.EtaleCohomology.Purity.baseChange_unit_eq`, for any four
adjunctions). Hence when `β` is invertible at `g⁻¹ A`, `f'⁻¹` of the unit of `g` at `A` is
invertible exactly when the unit of `h` at `f'⁻¹ A` is
(`Stacks.EtaleCohomology.Purity.isIso_smallEtalePullbackAb_map_unit_iff`).

## Main results

* `Stacks.EtaleCohomology.Purity.baseChange_unit_eq`: the mate of `σ` carries the unit of `g`
  to the unit of `h`, up to the comparison of left adjoints.
* `Stacks.EtaleCohomology.Purity.isIso_smallEtalePullbackAb_map_unit_iff`: when `β` is
  invertible at `g⁻¹ A`, `f'⁻¹` of the unit of `g` is invertible iff the unit of `h` is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.Purity

section Abstract

variable {CS CX CT CY : Type*} [Category* CS] [Category* CX] [Category* CT] [Category* CY]
  {Lg : CS ⥤ CT} {Rg : CT ⥤ CS} (adjg : Lg ⊣ Rg) {Lf : CS ⥤ CX} {Rf : CX ⥤ CS} (adjf : Lf ⊣ Rf)
  {Le : CT ⥤ CY} {Re : CY ⥤ CT} (adje : Le ⊣ Re) {Lh : CX ⥤ CY} {Rh : CY ⥤ CX}
  (adjh : Lh ⊣ Rh) (σ : Re ⋙ Rg ≅ Rh ⋙ Rf)

/-- **The mate of `σ` carries the unit of `g` to the unit of `h`.** For adjunctions
`Lg ⊣ Rg`, `Lf ⊣ Rf`, `Le ⊣ Re`, `Lh ⊣ Rh` and an isomorphism `σ : Re ⋙ Rg ≅ Rh ⋙ Rf`, the mate
`Lf Rg ⟶ Rh Le` of `σ`, at `Lg A`, after `Lf` of the unit of `g` at `A`, is the unit of `h` at
`Lf A` followed by `Rh` of the comparison `Lh Lf A ≅ Le Lg A` of left adjoints of the two
composites. -/
theorem baseChange_unit_eq (A : CS) :
    Lf.map (adjg.unit.app A) ≫ (Lf.map (Rg.map (adje.unit.app (Lg.obj A))) ≫
        Lf.map (σ.hom.app (Le.obj (Lg.obj A))) ≫ adjf.counit.app (Rh.obj (Le.obj (Lg.obj A)))) =
      adjh.unit.app (Lf.obj A) ≫
        Rh.map (((adjg.comp adje).leftAdjointUniq
          ((adjf.comp adjh).ofNatIsoRight σ.symm)).inv.app A) := by
  set κ := (adjg.comp adje).leftAdjointUniq ((adjf.comp adjh).ofNatIsoRight σ.symm)
  have h1 := Adjunction.unit_leftAdjointUniq_hom_app (adjg.comp adje)
    ((adjf.comp adjh).ofNatIsoRight σ.symm) A
  have hu : ((adjf.comp adjh).ofNatIsoRight σ.symm).unit.app A =
      (adjf.comp adjh).unit.app A ≫ σ.inv.app ((Lf ⋙ Lh).obj A) := by simp
  rw [hu, Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h1
  have h2 : adjg.unit.app A ≫ Rg.map (adje.unit.app (Lg.obj A)) =
      ((adjf.unit.app A ≫ Rf.map (adjh.unit.app (Lf.obj A))) ≫
        σ.inv.app ((Lf ⋙ Lh).obj A)) ≫ (Re ⋙ Rg).map (κ.inv.app A) := by
    rw [← h1, Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
    simp
  have hY : adjg.unit.app A ≫ Rg.map (adje.unit.app (Lg.obj A)) ≫
      σ.hom.app (Le.obj (Lg.obj A)) =
      adjf.unit.app A ≫ Rf.map (adjh.unit.app (Lf.obj A) ≫ Rh.map (κ.inv.app A)) := by
    rw [reassoc_of% h2, show Rg.map (Re.map (κ.inv.app A)) ≫ σ.hom.app (Le.obj (Lg.obj A)) =
        σ.hom.app _ ≫ Rf.map (Rh.map (κ.inv.app A)) from σ.hom.naturality _]
    simp
  rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Category.assoc, hY]
  simp

end Abstract

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- **Units across a base change square.** If the underived base change map of the square
`h ≫ f' = e ≫ g` is invertible at `g⁻¹ A`, then `f'⁻¹` of the unit `A ⟶ g_* g⁻¹ A` is invertible
exactly when the unit `f'⁻¹ A ⟶ h_* h⁻¹ f'⁻¹ A` is. -/
theorem isIso_smallEtalePullbackAb_map_unit_iff (A : Sheaf (smallEtaleTopology S) Ab.{u + 1})
    (hβ : IsIso ((smallEtaleBaseChangeAb f' g h e w).app ((smallEtalePullbackAb g).obj A))) :
    IsIso ((smallEtalePullbackAb f').map ((smallEtaleAdjunctionAb g).unit.app A)) ↔
      IsIso ((smallEtaleAdjunctionAb h).unit.app ((smallEtalePullbackAb f').obj A)) := by
  have key := baseChange_unit_eq (smallEtaleAdjunctionAb g) (smallEtaleAdjunctionAb f')
    (smallEtaleAdjunctionAb e) (smallEtaleAdjunctionAb h)
    (smallEtaleSquarePushforwardIso f' g h e w) A
  rw [← smallEtaleBaseChangeAb_app_eq] at key
  rw [← isIso_comp_right_iff _ ((smallEtaleBaseChangeAb f' g h e w).app _), key,
    isIso_comp_right_iff]

end Stacks.EtaleCohomology.Purity

end
