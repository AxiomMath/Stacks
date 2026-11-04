module

public import StacksFrontier.AlgebraicGeometry.Cohomology.KunnethLowDegree.Bound
public import StacksFrontier.AlgebraicGeometry.Cohomology.KunnethLowDegree.FaceRetraction
public import StacksFrontier.AlgebraicGeometry.Cohomology.KunnethLowDegree.LinearAlgebra
public import StacksFrontier.AlgebraicGeometry.Cohomology.KunnethLowDegree.PointPushforward

/-!
# The degree-one Künneth injectivity into the two faces

Let `X` and `Y` be proper and geometrically integral over an algebraically closed field `k`, with
rational points `x₀` and `y₀`, and let `W = X ×_k Y` with faces `i₁ : X ≅ X × {y₀} ⟶ W` and
`i₂ : Y ≅ {x₀} × Y ⟶ W`. Then

`H¹(W, 𝒪_W) ⟶ H¹(W, i₁_* i₁^* 𝒪_W) × H¹(W, i₂_* i₂^* 𝒪_W)`,

the map induced by the two units `𝒪_W ⟶ iⱼ_* iⱼ^* 𝒪_W`, is injective. This is the cohomological
input of the proof of [Stacks, Tag 0BF3], which the source obtains from the Künneth formula
[Stacks, Tag 0BED].

## Proof

`H¹(X, 𝒪_X)` maps to `H¹(W, 𝒪_W)` through the edge morphism of the Leray sequence of the
projection `π₁ : W ⟶ X` (`Stacks.KunnethLowDegree.leray₁`); by naturality its composite with the
first face map is the edge morphism after `H¹` of `𝒪_X ⟶ π₁_* i₁_* i₁^* 𝒪_W`, injective because
that map has a retraction (`i₁ ≫ π₁ = 𝟙`) and the edge morphism is injective, while its composite
with the second face map factors through `H¹(X, π₁_* i₂_* i₂^* 𝒪_W) = 0`, the sheaf being
pushed forward from the point `x₀`. Symmetrically for `Y`. With the bound
`h¹(W) ≤ h¹(X) + h¹(Y)` (`Stacks.KunnethLowDegree.finrank_H1_pullback_le`) the linear algebra of
`Stacks.KunnethLowDegree.injective_prod_of_finrank_le` concludes.

## Main results

* `Stacks.KunnethLowDegree.injective_H1_faces`.

## References

* [Stacks Project, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)
* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.KunnethLowDegree

variable {k : Type u} [Field k]

/-- `kOf (π ≫ p)` is `kOf p` followed by `π.appTop`. -/
theorem kOf_comp {T S : Scheme.{u}} (π : T ⟶ S) (p : S ⟶ Spec (.of k)) :
    kOf (π ≫ p) = π.appTop.hom.comp (kOf p) := rfl

/-- A `Γ(S, 𝒪_S)`-linear map `H¹(S, F) ⟶ H¹(T, G)` (scalars restricted along `π`), read as a
`k`-linear map of cohomology over `k`. -/
def cohomologyOverFieldLinearMap {T S : Scheme.{u}} (π : T ⟶ S) (p : S ⟶ Spec (.of k))
    (F : S.Modules) (G : T.Modules)
    (f : ((moduleGlobalSections S).rightDerived 1).obj F ⟶
      (ModuleCat.restrictScalars π.appTop.hom).obj
        (((moduleGlobalSections T).rightDerived 1).obj G)) :
    cohomologyOverField k p F 1 →ₗ[k] cohomologyOverField k (π ≫ p) G 1 where
  toFun := f.hom
  map_add' := f.hom.map_add
  map_smul' c x := by
    have := f.hom.map_smul (kOf p c)
      (show ((moduleGlobalSections S).rightDerived 1).obj F from x)
    change f.hom (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ ⊤ (by simp)).hom c •
        (show ((moduleGlobalSections S).rightDerived 1).obj F from x)) =
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (π ≫ p).appLE ⊤ ⊤ (by simp)).hom c •
        (show ((moduleGlobalSections T).rightDerived 1).obj G from f.hom x))
    rw [kOf_eq p, kOf_eq (π ≫ p)]
    exact this

/-- Cohomology over `k` along two equal structure morphisms. -/
def cohomologyOverFieldEquivOfEq {T : Scheme.{u}} {p q : T ⟶ Spec (.of k)} (h : p = q)
    (F : T.Modules) (n : ℕ) :
    cohomologyOverField k p F n ≃ₗ[k] cohomologyOverField k q F n where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' c x := by subst h; rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The face map after the edge morphism.** For a flat `π : W ⟶ S` and a morphism
`i : Z ⟶ W`, the class of `c ∈ H¹(S, 𝒪_S)` pushed to `H¹(W, 𝒪_W)` through `𝒪_S ⟶ π_* 𝒪_W` and
the edge morphism, then restricted along the unit `𝒪_W ⟶ i_* i^* 𝒪_W`, is the edge morphism of
the class of `c` under `faceSection π i`. -/
theorem H1_unit_leray₁ {W S Z : Scheme.{u}} (π : W ⟶ S) [Flat π] (i : Z ⟶ W)
    (c : ((moduleGlobalSections S).rightDerived 1).obj (SheafOfModules.unit S.ringCatSheaf)) :
    (((moduleGlobalSections W).rightDerived 1).map
        ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (SheafOfModules.unit W.ringCatSheaf))).hom
      ((leray₁ π (SheafOfModules.unit W.ringCatSheaf)).hom
        ((((moduleGlobalSections S).rightDerived 1).map
          (SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom)).hom c)) =
    (leray₁ π _).hom ((((moduleGlobalSections S).rightDerived 1).map (faceSection π i)).hom c) := by
  have hn := congrArg (fun g => g.hom ((((moduleGlobalSections S).rightDerived 1).map
      (SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom)).hom c))
    (leray₁_naturality π ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (SheafOfModules.unit W.ringCatSheaf)))
  have hc : (((moduleGlobalSections S).rightDerived 1).map (faceSection π i)) =
      ((moduleGlobalSections S).rightDerived 1).map
          (SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom) ≫
        ((moduleGlobalSections S).rightDerived 1).map ((Scheme.Modules.pushforward π).map
          ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
            (SheafOfModules.unit W.ringCatSheaf))) :=
    ((moduleGlobalSections S).rightDerived 1).map_comp _ _
  rw [hc]
  exact hn.symm

/-- If a face `i` is a section of `π`, the face map after the edge morphism is injective. -/
private theorem H1_unit_leray₁_injective {W S : Scheme.{u}} (π : W ⟶ S) [Flat π] (i : S ⟶ W)
    (h : i ≫ π = 𝟙 S)
    {a b : ((moduleGlobalSections S).rightDerived 1).obj (SheafOfModules.unit S.ringCatSheaf)}
    (hab : (((moduleGlobalSections W).rightDerived 1).map
        ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (SheafOfModules.unit W.ringCatSheaf))).hom
      ((leray₁ π (SheafOfModules.unit W.ringCatSheaf)).hom
        ((((moduleGlobalSections S).rightDerived 1).map
          (SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom)).hom a)) =
    (((moduleGlobalSections W).rightDerived 1).map
        ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (SheafOfModules.unit W.ringCatSheaf))).hom
      ((leray₁ π (SheafOfModules.unit W.ringCatSheaf)).hom
        ((((moduleGlobalSections S).rightDerived 1).map
          (SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom)).hom b))) :
    a = b := by
  have hm := (ModuleCat.mono_iff_injective _).mp (mono_leray₁ π
    ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj
      (SheafOfModules.unit W.ringCatSheaf))))
  rw [H1_unit_leray₁, H1_unit_leray₁] at hab
  exact injective_H_faceSection i π h 1 (hm hab)

/-- The face map after the edge morphism vanishes if the pushed-forward `H¹` vanishes. -/
private theorem H1_unit_leray₁_eq_zero {W S Z : Scheme.{u}} (π : W ⟶ S) [Flat π] (i : Z ⟶ W)
    (hz : IsZero (((moduleGlobalSections S).rightDerived 1).obj
      ((Scheme.Modules.pushforward π).obj ((Scheme.Modules.pushforward i).obj
        ((Scheme.Modules.pullback i).obj (SheafOfModules.unit W.ringCatSheaf))))))
    (c : ((moduleGlobalSections S).rightDerived 1).obj (SheafOfModules.unit S.ringCatSheaf)) :
    (((moduleGlobalSections W).rightDerived 1).map
        ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (SheafOfModules.unit W.ringCatSheaf))).hom
      ((leray₁ π (SheafOfModules.unit W.ringCatSheaf)).hom
        ((((moduleGlobalSections S).rightDerived 1).map
          (SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom)).hom c)) = 0 := by
  rw [H1_unit_leray₁, (ModuleCat.isZero_iff_subsingleton.mp hz).elim
    ((((moduleGlobalSections S).rightDerived 1).map (faceSection π i)).hom c) 0, map_zero]
  rfl

/-- **The degree-one Künneth injectivity.** Let `X` and `Y` be proper and geometrically integral
over an algebraically closed field `k`, with rational points `x₀` and `y₀`, and let
`W = X ×_k Y` with faces `i₁ = (𝟙, y₀) : X ⟶ W` and `i₂ = (x₀, 𝟙) : Y ⟶ W`. Then a class of
`H¹(W, 𝒪_W)` which vanishes after both units `𝒪_W ⟶ iⱼ_* iⱼ^* 𝒪_W` is zero. -/
theorem injective_H1_faces (k : Type u) [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [IsProper fX] [IsProper fY] [GeometricallyIntegral fX] [GeometricallyIntegral fY]
    (x₀ : Spec (.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _) (y₀ : Spec (.of k) ⟶ Y)
    (hy₀ : y₀ ≫ fY = 𝟙 _) :
    let W := pullback fX fY
    let i₁ : X ⟶ W := pullback.lift (𝟙 X) (fX ≫ y₀) (by simp [hy₀])
    let i₂ : Y ⟶ W := pullback.lift (fY ≫ x₀) (𝟙 Y) (by simp [hx₀])
    let η₁ := (Scheme.Modules.pullbackPushforwardAdjunction i₁).unit.app
      (SheafOfModules.unit W.ringCatSheaf)
    let η₂ := (Scheme.Modules.pullbackPushforwardAdjunction i₂).unit.app
      (SheafOfModules.unit W.ringCatSheaf)
    Function.Injective (fun c : ((moduleGlobalSections W).rightDerived 1).obj
        (SheafOfModules.unit W.ringCatSheaf) =>
      ((((moduleGlobalSections W).rightDerived 1).map η₁).hom c,
       (((moduleGlobalSections W).rightDerived 1).map η₂).hom c)) := by
  intro W i₁ i₂ η₁ η₂
  have := flat_of_spec_field fX
  have := flat_of_spec_field fY
  let π₁ := pullback.fst fX fY
  let π₂ := pullback.snd fX fY
  have h₁ : i₁ ≫ π₁ = 𝟙 X := pullback.lift_fst _ _ _
  have h₂ : i₂ ≫ π₂ = 𝟙 Y := pullback.lift_snd _ _ _
  have h₂₁ : i₂ ≫ π₁ = fY ≫ x₀ := pullback.lift_fst _ _ _
  have h₁₂ : i₁ ≫ π₂ = fX ≫ y₀ := pullback.lift_snd _ _ _
  let OW := SheafOfModules.unit W.ringCatSheaf
  let u₁ := SheafOfModules.unitToPushforwardObjUnit π₁.toRingCatSheafHom
  let u₂ := SheafOfModules.unitToPushforwardObjUnit π₂.toRingCatSheafHom
  let s₁ : cohomologyOverField k fX (SheafOfModules.unit X.ringCatSheaf) 1 →ₗ[k]
      cohomologyOverField k (π₂ ≫ fY) OW 1 :=
    (cohomologyOverFieldEquivOfEq pullback.condition OW 1).toLinearMap ∘ₗ
      cohomologyOverFieldLinearMap π₁ fX _ OW
        (((moduleGlobalSections X).rightDerived 1).map u₁ ≫ leray₁ π₁ OW)
  let s₂ : cohomologyOverField k fY (SheafOfModules.unit Y.ringCatSheaf) 1 →ₗ[k]
      cohomologyOverField k (π₂ ≫ fY) OW 1 :=
    cohomologyOverFieldLinearMap π₂ fY _ OW
      (((moduleGlobalSections Y).rightDerived 1).map u₂ ≫ leray₁ π₂ OW)
  let Φ₁ : cohomologyOverField k (π₂ ≫ fY) OW 1 →+
      ((moduleGlobalSections W).rightDerived 1).obj
        ((Scheme.Modules.pushforward i₁).obj ((Scheme.Modules.pullback i₁).obj OW)) :=
    (((moduleGlobalSections W).rightDerived 1).map η₁).hom.toAddMonoidHom
  let Φ₂ : cohomologyOverField k (π₂ ≫ fY) OW 1 →+
      ((moduleGlobalSections W).rightDerived 1).obj
        ((Scheme.Modules.pushforward i₂).obj ((Scheme.Modules.pullback i₂).obj OW)) :=
    (((moduleGlobalSections W).rightDerived 1).map η₂).hom.toAddMonoidHom
  obtain ⟨hfin, hdim⟩ := finrank_H1_pullback_le fX fY
  have := forall_finiteDimensional_cohomologyOverField_unit k fX 1
  have := forall_finiteDimensional_cohomologyOverField_unit k fY 1
  have hm₁ := (ModuleCat.mono_iff_injective _).mp (mono_leray₁ π₁
    ((Scheme.Modules.pushforward i₁).obj ((Scheme.Modules.pullback i₁).obj OW)))
  have hm₂ := (ModuleCat.mono_iff_injective _).mp (mono_leray₁ π₂
    ((Scheme.Modules.pushforward i₂).obj ((Scheme.Modules.pullback i₂).obj OW)))
  refine injective_prod_of_finrank_le s₁ s₂ Φ₁ Φ₂ ?_ ?_ ?_ ?_ hdim
  · exact fun a b hab => H1_unit_leray₁_injective π₁ i₁ h₁ hab
  · exact fun a b hab => H1_unit_leray₁_injective π₂ i₂ h₂ hab
  · exact fun b => H1_unit_leray₁_eq_zero π₂ i₁
      (isZero_H_pushforward_pushforward_of_comp_eq y₀ i₁ π₂ fX h₁₂
        ((Scheme.Modules.pullback i₁).obj OW) 1 one_pos) b
  · exact fun a => H1_unit_leray₁_eq_zero π₁ i₂
      (isZero_H_pushforward_pushforward_of_comp_eq x₀ i₂ π₁ fY h₂₁
        ((Scheme.Modules.pullback i₂).obj OW) 1 one_pos) a

end Stacks.KunnethLowDegree

end
