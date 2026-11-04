module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.AssemblyStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.StructureSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The direct image of the structure sheaf along a projection of a product over a field

Let `fX : X ⟶ Spec k` be proper and geometrically integral, and let `fY : Y ⟶ Spec k` be any
morphism. For the projection `π₂ : X ×_k Y ⟶ Y`, `𝒪_Y ⟶ π₂_* 𝒪` is an isomorphism: by
degree-zero flat base change ([Stacks, Tag 02KH]), since `H⁰(X, 𝒪_X) = k`
([Stacks, Tag 0BUG]).

## Main results

* `Stacks.KunnethLowDegree.flat_of_spec_field`: a morphism to the spectrum of a field is flat.
* `Stacks.KunnethLowDegree.isIso_unitToPushforwardObjUnit_snd`: `𝒪_Y ⟶ π₂_* 𝒪` is an
  isomorphism.
* `Stacks.KunnethLowDegree.pushforwardSndUnitIso`: `π₂_* 𝒪 ≅ 𝒪_Y`.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.KunnethLowDegree

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k))
  (fY : Y ⟶ Spec (.of k))

/-- Morphisms to the spectrum of a field are flat. -/
@[ega "IV 11.9.9" "Parenthetical clause"]
theorem flat_of_spec_field {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) : Flat f :=
  flat_of_isField_stalk _ fun _ => isField_stalk_Spec_field k _

/-- **`𝒪_Y ⟶ π₂_* 𝒪` is an isomorphism** for the projection `π₂ : X ×_k Y ⟶ Y`, `X` proper and
geometrically integral over `k`. -/
@[ega "III 4.3.4" "special case"]
theorem isIso_unitToPushforwardObjUnit_snd [IsProper fX] [GeometricallyIntegral fX] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit (pullback.snd fX fY).toRingCatSheafHom) := by
  have := flat_of_spec_field fY
  have : IsIso fX.appTop :=
    have := isIso_globalSections_of_geometricallyIntegral k fX
    IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv fX.appTop
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace fX
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated fX
  have := Stacks.Groupoids.isIso_structureSheafHom_pullback_snd_of_isIso_appTop fX fY
  rw [← Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit,
    Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff]
  intro U
  have : IsIso ((forget₂ CommRingCat RingCat).map ((pullback.snd fX fY).app U)) :=
    NatIso.isIso_app_of_isIso ((sheafToPresheaf _ _).map
      (RingedSpaceModuleAdjunction.structureSheafHom (pullback.snd fX fY).toLRSHom.toShHom)) (op U)
  have : IsIso ((pullback.snd fX fY).app U) :=
    isIso_of_reflects_iso _ (forget₂ CommRingCat RingCat)
  exact ConcreteCategory.bijective_of_isIso _

/-- **`π₂_* 𝒪 ≅ 𝒪_Y`** for the projection `π₂ : X ×_k Y ⟶ Y`, `X` proper and geometrically
integral over `k`. -/
def pushforwardSndUnitIso [IsProper fX] [GeometricallyIntegral fX] :
    (Scheme.Modules.pushforward (pullback.snd fX fY)).obj
        (SheafOfModules.unit (pullback fX fY).ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  have := isIso_unitToPushforwardObjUnit_snd fX fY
  (asIso (SheafOfModules.unitToPushforwardObjUnit (pullback.snd fX fY).toRingCatSheafHom)).symm

end Stacks.KunnethLowDegree

end
