module

public import StacksFrontier.Deformation.RingedSpaceThickening.ThickeningExtension

/-!
# Functoriality of the algebra structure `thickeningBase`

For morphisms `i : X ⟶ X'` and `h : X' ⟶ T` with `i ≫ h = k`, `thickeningBase h k hk` is the map
`k⁻¹𝒪_T ⟶ i⁻¹𝒪_{X'}` transposed from `h^♯`. This file shows it is functorial in `h`: the
identity goes to the identity (`thickeningBase_id`) and composites to composites
(`thickeningBase_comp_thickeningBase`). These are what compare the extensions underlying two
solutions of (08U7) related by a morphism of solutions.

## References

* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X X' T : RingedSpace.{u, u}} {i : X ⟶ X'} (h : X' ⟶ T)

/-- `thickeningBaseTranspose` for the composite itself: `h^♯` followed by the unit of `i`. -/
theorem thickeningBaseTranspose_rfl :
    thickeningBaseTranspose h (i ≫ h) rfl =
      (ObjectProperty.homMk h.hom.c : T.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} h.hom.base).obj X'.sheaf) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} h.hom.base).map (inverseImageUnit i) :=
  congrArg (_ ≫ ·) (Category.comp_id _)

/-- `thickeningBase` along the identity is the identity. -/
theorem thickeningBase_id : thickeningBase (𝟙 X') i (Category.comp_id i) = 𝟙 _ := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.hom.base).homEquiv
    _ _).injective
  refine (Equiv.apply_symm_apply _ _).trans ?_
  refine Eq.trans ?_ ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    i.hom.base).homEquiv_id _).symm
  rfl

/-- `thickeningBase` only depends on the morphism. -/
theorem thickeningBase_congr {h h' : X' ⟶ T} (e : h = h') (k : X ⟶ T) (hk : i ≫ h = k)
    (hk' : i ≫ h' = k) : thickeningBase h k hk = thickeningBase h' k hk' := by
  subst e
  rfl

/-- **`thickeningBase` is functorial**: along `h₁ : X₀ ⟶ X₁` and `h₂ : X₁ ⟶ X₂` under `X`, the
structure maps `k₂⁻¹𝒪_{X₂} ⟶ k₁⁻¹𝒪_{X₁} ⟶ i₀⁻¹𝒪_{X₀}` compose to the one along `h₁ ≫ h₂`. -/
theorem thickeningBase_comp_thickeningBase {X₀ X₁ X₂ : RingedSpace.{u, u}} {i₀ : X ⟶ X₀}
    (h₁ : X₀ ⟶ X₁) (h₂ : X₁ ⟶ X₂) (k₁ : X ⟶ X₁) (k₂ : X ⟶ X₂) (hk₁ : i₀ ≫ h₁ = k₁)
    (hk₂ : k₁ ≫ h₂ = k₂) :
    thickeningBase h₂ k₂ hk₂ ≫ thickeningBase h₁ k₁ hk₁ =
      thickeningBase (h₁ ≫ h₂) k₂ (by rw [← hk₂, ← hk₁, Category.assoc]) := by
  subst hk₁ hk₂
  let a₂ := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} ((i₀ ≫ h₁) ≫ h₂).hom.base
  let a₁ := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (i₀ ≫ h₁).hom.base
  apply (a₂.homEquiv _ _).injective
  refine (a₂.homEquiv_naturality_right _ _).trans ?_
  refine Eq.trans ?_ (Equiv.apply_symm_apply _ _).symm
  have h1 : a₂.homEquiv _ _ (thickeningBase h₂ ((i₀ ≫ h₁) ≫ h₂) rfl) =
      thickeningBaseTranspose h₂ ((i₀ ≫ h₁) ≫ h₂) rfl := Equiv.apply_symm_apply _ _
  have h2 : a₁.homEquiv _ _ (thickeningBase h₁ (i₀ ≫ h₁) rfl) =
      thickeningBaseTranspose h₁ (i₀ ≫ h₁) rfl := Equiv.apply_symm_apply _ _
  have h3 : inverseImageUnit (i₀ ≫ h₁) ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
      (i₀ ≫ h₁).hom.base).map (thickeningBase h₁ (i₀ ≫ h₁) rfl) =
      thickeningBaseTranspose h₁ (i₀ ≫ h₁) rfl :=
    (a₁.homEquiv_unit _ _ _).symm.trans h2
  rw [thickeningBaseTranspose_rfl] at h3
  refine (congrArg (· ≫ _) (h1.trans (thickeningBaseTranspose_rfl _))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  have h4 := congrArg (TopCat.Sheaf.pushforward CommRingCat.{u} h₂.hom.base).map h3
  rw [Functor.map_comp] at h4
  refine (congrArg (_ ≫ ·) h4).trans ?_
  change _ = ((ObjectProperty.homMk h₂.hom.c : X₂.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} h₂.hom.base).obj X₁.sheaf) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} h₂.hom.base).map
        (ObjectProperty.homMk h₁.hom.c : X₁.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} h₁.hom.base).obj X₀.sheaf)) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} h₂.hom.base).map
        ((TopCat.Sheaf.pushforward CommRingCat.{u} h₁.hom.base).map (inverseImageUnit i₀)) ≫ 𝟙 _
  rfl

end AlgebraicGeometry.RingedSpaceThickening

end
