module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackComparison

/-!
# The obstruction class of a failure of base change

Let `fV : X_V ⟶ V` be a morphism of schemes, `g₀ : T₀ ⟶ V` a base for a sheaf `F₀` with
`Y₀ = X_V ×_V T₀`, and `r` a degree. When the base change map
`fV⁻¹ R^r g₀_* F₀ ⟶ R^r h₀_* e₀⁻¹ F₀` is injective but not surjective, some stalk at a geometric
point `x` of `X_V` contains a class `ξ` outside its image. The proof of [Stacks, Tag 0F07] follows
such a class along changes of the base `T₀`: for `π : W ⟶ T₀` and the cartesian square
`Y' = X_V ×_V W`, the property `P(W)` asks that the image of `ξ` under the pullback map
`R^r h₀_* e₀⁻¹ F₀ ⟶ R^r h'_* e'⁻¹ π⁻¹ F₀` stay outside the image of the base change map over `W`.

## Main definitions

* `Stacks.EtaleCohomology.obstructionStalk` — the stalk in which the obstruction class lives.
* `Stacks.EtaleCohomology.ObstructionSurvives` — the property `P(W)` of the proof of
  [Stacks, Tag 0F07].

## Main results

* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_eq_id` — the base change map of a
  square whose inverse-image legs are identities is invertible.
* `Stacks.EtaleCohomology.exists_obstructionSurvives_self` — a non-invertible injective base
  change map supplies an obstruction class for which `P(T₀)` holds.
* `Stacks.EtaleCohomology.not_isIso_of_obstructionSurvives` — `P(W)` forces the base change map
  over `W` to fail.

## References

* [Stacks Project, Tag 0F07](https://stacks.math.columbia.edu/tag/0F07)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **The base change map of a square whose inverse-image legs are identities is invertible.**
This is the derived identity law `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_id_app`
read in degree `r`. -/
public theorem isIso_higherBaseChangeMapAb_app_of_eq_id {X B : Scheme.{u}} (g : X ⟶ B)
    (b : B ⟶ B) (x : X ⟶ X) (hb : b = 𝟙 B) (hx : x = 𝟙 X) (w : g ≫ b = x ≫ g) (r : ℕ)
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb b g g x w r).app F) := by
  rw [isIso_higherBaseChangeMapAb_app_iff, smallEtaleDerivedBaseChangeAb_id_app g b x hb hx w]
  infer_instance

/-- The stalk at a geometric point `x` of `X_V` of `𝟙⁻¹ R^r h₀_* e₀⁻¹ F₀`: the group in which the
obstruction class of [Stacks, Tag 0F07] is chosen. -/
public abbrev obstructionStalk {X_V T₀ Y₀ : Scheme.{u}} (h₀ : Y₀ ⟶ X_V) (e₀ : Y₀ ⟶ T₀)
    (F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1}) (r : ℕ) (x : GeometricPoint X_V) :
    Ab.{u + 1} :=
  (smallEtaleStalkAb x.hom).obj ((smallEtalePullbackAb (𝟙 X_V)).obj
    (((smallEtalePushforwardAb h₀).rightDerived r).obj ((smallEtalePullbackAb e₀).obj F₀)))

/-- **The property the dévissage of [Stacks, Tag 0F06] is applied to**, the property `P(T')` of
the proof of [Stacks, Tag 0F07]. Fix a base change `fV : X_V ⟶ V`, a base `g₀ : T₀ ⟶ V` for the
sheaf with `Y₀ = X_V ×_V T₀` (projections `h₀`, `e₀`), an abelian sheaf `F₀` on `T₀`, a degree
`r`, a geometric point `x` of `X_V` and a class `ξ` in the stalk at `x` of `R^r h₀_* e₀⁻¹F₀`.
A scheme `W` with `π : W ⟶ T₀` has the property when, for a cartesian square
`Y' = X_V ×_V W` over `Y₀ ⟶ T₀`, the image `ξ'` of `ξ` under the pullback map
`R^r h₀_* e₀⁻¹F₀ ⟶ R^r h'_* e'⁻¹π⁻¹F₀` is not in the image of the stalk at `x` of the base change
map `fV⁻¹ R^r g'_* π⁻¹F₀ ⟶ R^r h'_* e'⁻¹π⁻¹F₀`.

The pullback map is the base change map of the square `h' ≫ 𝟙 = y ≫ h₀`, followed by the
identification `y⁻¹e₀⁻¹ ≅ e'⁻¹π⁻¹` of the two inverse images along `y ≫ e₀ = e' ≫ π`. -/
public def ObstructionSurvives {V X_V T₀ Y₀ : Scheme.{u}} (fV : X_V ⟶ V) (g₀ : T₀ ⟶ V)
    (h₀ : Y₀ ⟶ X_V) (e₀ : Y₀ ⟶ T₀) (F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1}) (r : ℕ)
    (x : GeometricPoint X_V) (ξ : obstructionStalk h₀ e₀ F₀ r x) (W : Scheme.{u})
    (π : W ⟶ T₀) : Prop :=
  ∃ (Y' : Scheme.{u}) (h' : Y' ⟶ X_V) (e' : Y' ⟶ W) (g' : W ⟶ V) (_hg : g' = π ≫ g₀)
    (sq' : IsPullback h' e' fV g') (y : Y' ⟶ Y₀) (hy : y ≫ e₀ = e' ≫ π)
    (hyh : h' ≫ 𝟙 X_V = y ≫ h₀),
    ∀ η, (smallEtaleStalkAb x.hom).map
        ((higherBaseChangeMapAb fV g' h' e' sq'.w r).app ((smallEtalePullbackAb π).obj F₀)) η ≠
      (smallEtaleStalkAb x.hom).map
        ((higherBaseChangeMapAb (𝟙 X_V) h₀ h' y hyh r).app ((smallEtalePullbackAb e₀).obj F₀) ≫
          ((smallEtalePushforwardAb h').rightDerived r).map
            ((smallEtalePullbackAbComp' y e₀ (y ≫ e₀) rfl).hom.app F₀ ≫
              (smallEtalePullbackAbComp' e' π (y ≫ e₀) hy).inv.app F₀)) ξ

/-- **The property holds at the base itself for a suitable obstruction class.** If the base
change map in degree `r` of `F₀` is not an isomorphism while that of `𝟙⁻¹F₀` is a monomorphism,
there are a geometric point `x` of `X_V` and a class `ξ` with
`ObstructionSurvives … x ξ T₀ (𝟙 T₀)`: a non-surjective stalk of the base change map supplies
`ξ'`, and the pullback map along the identity is invertible. -/
public theorem exists_obstructionSurvives_self {V X_V T₀ Y₀ : Scheme.{u}} (fV : X_V ⟶ V)
    (g₀ : T₀ ⟶ V) (h₀ : Y₀ ⟶ X_V) (e₀ : Y₀ ⟶ T₀) (sq₀ : IsPullback h₀ e₀ fV g₀)
    (F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1}) (r : ℕ)
    (hmono : Mono ((higherBaseChangeMapAb fV g₀ h₀ e₀ sq₀.w r).app
      ((smallEtalePullbackAb (𝟙 T₀)).obj F₀)))
    (hni : ¬ IsIso ((higherBaseChangeMapAb fV g₀ h₀ e₀ sq₀.w r).app F₀)) :
    ∃ (x : GeometricPoint X_V) (ξ : obstructionStalk h₀ e₀ F₀ r x),
      ObstructionSurvives fV g₀ h₀ e₀ F₀ r x ξ T₀ (𝟙 T₀) := by
  set β := (higherBaseChangeMapAb fV g₀ h₀ e₀ sq₀.w r).app
    ((smallEtalePullbackAb (𝟙 T₀)).obj F₀)
  have hβ : ¬ IsIso β := by
    intro hiso
    apply hni
    let ι := (smallEtalePullbackAbIdOf (𝟙 T₀) rfl).app F₀
    have : (higherBaseChangeMapAb fV g₀ h₀ e₀ sq₀.w r).app F₀ =
        inv ((((smallEtalePushforwardAb g₀).rightDerived r) ⋙ smallEtalePullbackAb fV).map
          ι.hom) ≫ β ≫ ((smallEtalePullbackAb e₀ ⋙
            (smallEtalePushforwardAb h₀).rightDerived r).map ι.hom) := by
      rw [IsIso.eq_inv_comp]
      exact (higherBaseChangeMapAb fV g₀ h₀ e₀ sq₀.w r).naturality ι.hom
    rw [this]
    infer_instance
  obtain ⟨x, hx⟩ := not_forall.1 (mt (isIso_iff_forall_isIso_smallEtaleStalkAb β).2 hβ)
  have hepi : ¬ Epi ((smallEtaleStalkAb x.hom).map β) := fun _ ↦ hx (isIso_of_mono_of_epi _)
  rw [AddCommGrpCat.epi_iff_surjective] at hepi
  simp only [Function.Surjective, not_forall, not_exists] at hepi
  obtain ⟨ζ, hζ⟩ := hepi
  set c := (higherBaseChangeMapAb (𝟙 X_V) h₀ h₀ (𝟙 Y₀) (by simp) r).app
      ((smallEtalePullbackAb e₀).obj F₀) ≫
    ((smallEtalePushforwardAb h₀).rightDerived r).map
      ((smallEtalePullbackAbComp' (𝟙 Y₀) e₀ (𝟙 Y₀ ≫ e₀) rfl).hom.app F₀ ≫
        (smallEtalePullbackAbComp' e₀ (𝟙 T₀) (𝟙 Y₀ ≫ e₀) (by simp)).inv.app F₀) with hc
  have : IsIso c := by
    have := isIso_higherBaseChangeMapAb_app_of_eq_id h₀ (𝟙 X_V) (𝟙 Y₀) rfl rfl (by simp) r
      ((smallEtalePullbackAb e₀).obj F₀)
    rw [hc]
    infer_instance
  refine ⟨x, inv ((smallEtaleStalkAb x.hom).map c) ζ, Y₀, h₀, e₀, g₀,
    (Category.id_comp g₀).symm, sq₀, 𝟙 Y₀, by simp, by simp, fun η hη ↦ hζ η ?_⟩
  rw [hη, ← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]

/-- **The property forces a failure of base change.** If `ObstructionSurvives … W π` holds then,
for the cartesian square it provides, the base change map of `π⁻¹F₀` in degree `r` is not an
isomorphism: its stalk at `x` misses `ξ'`. -/
public theorem not_isIso_of_obstructionSurvives {V X_V T₀ Y₀ : Scheme.{u}} {fV : X_V ⟶ V}
    {g₀ : T₀ ⟶ V} {h₀ : Y₀ ⟶ X_V} {e₀ : Y₀ ⟶ T₀} {F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1}}
    {r : ℕ} {x : GeometricPoint X_V} {ξ : obstructionStalk h₀ e₀ F₀ r x} {W : Scheme.{u}}
    {π : W ⟶ T₀} (hP : ObstructionSurvives fV g₀ h₀ e₀ F₀ r x ξ W π) :
    ∃ (Y' : Scheme.{u}) (h' : Y' ⟶ X_V) (e' : Y' ⟶ W) (g' : W ⟶ V) (_hg : g' = π ≫ g₀)
      (sq' : IsPullback h' e' fV g'),
      ¬ IsIso ((higherBaseChangeMapAb fV g' h' e' sq'.w r).app
        ((smallEtalePullbackAb π).obj F₀)) := by
  obtain ⟨Y', h', e', g', hg, sq', y, hy, hyh, hne⟩ := hP
  refine ⟨Y', h', e', g', hg, sq', fun hiso ↦ ?_⟩
  obtain ⟨η, hη⟩ := (AddCommGrpCat.epi_iff_surjective _).1
    (inferInstance : Epi ((smallEtaleStalkAb x.hom).map
      ((higherBaseChangeMapAb fV g' h' e' sq'.w r).app ((smallEtalePullbackAb π).obj F₀)))) _
  exact hne η hη

end Stacks.EtaleCohomology

end
