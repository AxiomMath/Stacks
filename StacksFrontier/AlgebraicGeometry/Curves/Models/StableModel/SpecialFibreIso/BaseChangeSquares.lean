module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.FibreMaps
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModel
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.Basic

/-!
# Fibre maps as base changes, and transport along isomorphisms of the source

Let `c : X ⟶ Y` be a morphism of schemes over `S` and `g : B ⟶ S`. The induced morphism of fibre
products `X ×_S B ⟶ Y ×_S B` is the base change of `c` along the projection `Y ×_S B ⟶ Y`: the
square is cartesian by pasting with the cartesian square of `Y ×_S B`. This identifies the fibre
maps of a morphism of models with base changes of the morphism.

Base change produces the source only up to isomorphism, so this file also records that the two
properties of `𝒪 ⟶ f_*𝒪` and of `Rⁿf_*𝒪` used later do not see a precomposition with an
isomorphism, and that the fibres of a morphism have dimension at most that of its source.

## Main results

* `Stacks.Models.SpecialFibreIso.isPullback_pullbackMap`: the morphism of fibre products induced
  by `c` is a base change of `c`.
* `Stacks.Models.SpecialFibreIso.epi_unitToPushforwardUnit_iso_comp`: surjectivity of
  `𝒪 ⟶ f_*𝒪` survives precomposition with an isomorphism.
* `Stacks.Models.SpecialFibreIso.isZero_rightDerived_unit_iso_comp`: so does the vanishing of
  `Rⁿf_*𝒪`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models.SpecialFibreIso

/-- **The morphism of fibre products induced by `c` is a base change of `c`.** For `c : X ⟶ Y`
over `S` (`c ≫ pY = p`) and `g : B ⟶ S`, the square formed by `X ×_S B ⟶ Y ×_S B`, the two first
projections and `c` is cartesian: pasted with the cartesian square of `Y ×_S B` it gives the
cartesian square of `X ×_S B`. -/
theorem isPullback_pullbackMap {X Y B S : Scheme.{u}} (p : X ⟶ S) (pY : Y ⟶ S) (c : X ⟶ Y)
    (hc : c ≫ pY = p) (g : B ⟶ S) (w₁ : p ≫ 𝟙 S = c ≫ pY) (w₂ : g ≫ 𝟙 S = 𝟙 B ≫ g) :
    IsPullback (pullback.fst p g) (pullback.map p g pY g c (𝟙 B) (𝟙 S) w₁ w₂) c
      (pullback.fst pY g) := by
  refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback pY g)
  have h : pullback.map p g pY g c (𝟙 B) (𝟙 S) w₁ w₂ ≫ pullback.snd pY g = pullback.snd p g :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  rw [h, hc]
  exact IsPullback.of_hasPullback p g

/-- `𝒪 ⟶ e_*𝒪` is an isomorphism for an isomorphism of schemes `e`. -/
theorem isIso_unitToPushforwardUnit_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] :
    IsIso (Scheme.Modules.unitToPushforwardUnit e) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  show IsIso (((forget₂ CommRingCat RingCat) ⋙ forget₂ RingCat Ab).map (e.app U))
  infer_instance

/-- **Surjectivity of `𝒪 ⟶ f_*𝒪` survives precomposition with an isomorphism.** The comparison
for `e ≫ f` is that for `f` followed by `f_*` of the comparison for `e`, an isomorphism, and the
identification `(e ≫ f)_* = f_* ∘ e_*`. -/
theorem epi_unitToPushforwardUnit_iso_comp {X' X Y : Scheme.{u}} (e : X' ⟶ X) [IsIso e]
    (f : X ⟶ Y) (hf : Epi (Scheme.Modules.unitToPushforwardUnit f)) :
    Epi (Scheme.Modules.unitToPushforwardUnit (e ≫ f)) := by
  have := isIso_unitToPushforwardUnit_of_isIso e
  rw [← Scheme.Modules.unitToPushforwardUnit_comp]
  infer_instance

/-- **The vanishing of `Rⁿf_*𝒪` survives precomposition with an isomorphism.** For `e` an
isomorphism (in particular affine), `Rⁿ(e ≫ f)_*𝒪 ≅ Rⁿf_*(e_*𝒪)` ([Stacks, Tag 089W]) and
`e_*𝒪 ≅ 𝒪`. -/
theorem isZero_rightDerived_unit_iso_comp {X' X Y : Scheme.{u}} (e : X' ⟶ X) [IsIso e]
    (f : X ⟶ Y) (n : ℕ)
    (hf : IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    IsZero (((Scheme.Modules.pushforward (e ≫ f)).rightDerived n).obj
      (SheafOfModules.unit X'.ringCatSheaf)) := by
  have := isIso_unitToPushforwardUnit_of_isIso e
  refine IsZero.of_iso ?_
    (Stacks.AlgebraicGeometry.ProperSupportCoherent.rightDerivedPushforwardCompIso e f
      (SheafOfModules.unit X'.ringCatSheaf) n)
  exact hf.of_iso (((Scheme.Modules.pushforward f).rightDerived n).mapIso
    (asIso (Scheme.Modules.unitToPushforwardUnit e)).symm)

end Stacks.Models.SpecialFibreIso

end
