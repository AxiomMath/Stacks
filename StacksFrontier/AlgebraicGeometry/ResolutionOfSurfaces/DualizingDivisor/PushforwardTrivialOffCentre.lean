module

public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.PushforwardRestrictOpen

/-!
# The direct image of a module trivial over the locus where a morphism is an isomorphism

Let `b : X ⟶ Y` be a morphism of schemes and `U ⊆ Y` an open over which `b` is an isomorphism
(`b ∣_ U` is an isomorphism). If an `𝒪_X`-module `L` is trivial over `b⁻¹(U)`, then its direct
image `b_* L` is trivial over `U`: `(b_* L)|_U = (b ∣_ U)_* (L|_{b⁻¹ U}) ≅ (b ∣_ U)_* 𝒪 ≅ 𝒪_U`.

## Main results

* `AlgebraicGeometry.DualizingDivisor.nonempty_pullback_pushforward_iso_unit`: the statement above.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.DualizingDivisor

/-- **The direct image of a module trivial over `b⁻¹(U)` is trivial over `U`**, when `b` is an
isomorphism over `U`. -/
theorem nonempty_pullback_pushforward_iso_unit {X Y : Scheme.{u}} (b : X ⟶ Y) (U : Y.Opens)
    [IsIso (b ∣_ U)] (L : X.Modules)
    (eU : (Scheme.Modules.pullback (b ⁻¹ᵁ U).ι).obj L ≅
      (Scheme.Modules.pullback (b ⁻¹ᵁ U).ι).obj (SheafOfModules.unit X.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pushforward b).obj L) ≅
      (Scheme.Modules.pullback U.ι).obj (SheafOfModules.unit Y.ringCatSheaf)) := by
  have : IsIso (b.resLE U (b ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  have ρ := Scheme.Modules.restrictFunctorIsoPullback (X := (b ⁻¹ᵁ U).toScheme) (b ⁻¹ᵁ U).ι
  have ρU := Scheme.Modules.restrictFunctorIsoPullback (X := U.toScheme) U.ι
  exact ⟨(ρU.app _).symm ≪≫
    (Stacks.Perfect.PushforwardRestrict.pushforwardRestrictIso b U).app L ≪≫
    (Scheme.Modules.pushforward (b.resLE U (b ⁻¹ᵁ U) le_rfl)).mapIso
      (ρ.app L ≪≫ eU ≪≫ (ρ.app _).symm ≪≫
        Scheme.Modules.restrictUnitIso _) ≪≫
    pushforwardUnitIso _ ≪≫ (Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
      ρU.app _⟩

end AlgebraicGeometry.DualizingDivisor
