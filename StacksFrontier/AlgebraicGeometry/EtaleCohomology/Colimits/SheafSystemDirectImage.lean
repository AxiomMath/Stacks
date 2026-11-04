module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafSystemInverseImage

/-!
# Direct images of systems of étale sheaves with arbitrary coefficients

Let `g_i : X_i ⟶ S_i` be a morphism of inverse systems of schemes over a preordered set, with
limit `g : X ⟶ S` for limit cones `f_i : X ⟶ X_i` and `h_i : S ⟶ S_i`, and let `(ℱ_i, φ_{i'i})` be
a system of sheaves on `(X_i)` with coefficients in a category `A` ([Stacks, Tag 0EZL]). The
direct images `g_{i, *}ℱ_i` form a system of sheaves on `(S_i)`: its transition maps are the base
change maps `h_{i'i}⁻¹g_{i, *} ⟶ g_{i', *}f_{i'i}⁻¹` of the transition squares followed by
`g_{i', *}φ_{i'i}`. For `ι_i : f_i⁻¹ℱ_i ⟶ ℱ` compatible with the transition maps, the base change
maps of the projection squares followed by `g_*ι_i` are compatible with the maps of the diagram
`h_i⁻¹g_{i, *}ℱ_i`; this is the cocone `g_*ℱ = colim h_i⁻¹g_{i, *}ℱ_i` of the degree zero case of
[Stacks, Tag 0EYM].

## Main definitions

* `Stacks.EtaleCohomology.LimitDirectImage.baseChangeTransitionMap`: the transition maps of the
  system of direct images.
* `Stacks.EtaleCohomology.LimitDirectImage.pushforwardSystem`: the system `i ↦ g_{i, *}ℱ_i`.
* `Stacks.EtaleCohomology.LimitDirectImage.baseChangeProjectionMap`: the maps
  `h_i⁻¹g_{i, *}ℱ_i ⟶ g_*ℱ`.

## Main results

* `Stacks.EtaleCohomology.LimitDirectImage.baseChangeTransitionMap_comp`: the cocycle condition.
* `Stacks.EtaleCohomology.LimitDirectImage.isSheafPullbackCocone_baseChangeProjectionMap`: the
  cocone identity.

## Implementation notes

Both identities are the pasting law for base change maps
(`Stacks.EtaleCohomology.smallEtaleSheafBaseChange_paste_app_named`) applied to two squares,
together with the naturality of the base change maps and the cocycle condition of the system.

The same maps are constructed by adjoint transposition, rather than from base change maps, as
`Stacks.EtaleCohomology.LimitDirectImage.transitionMap` and
`Stacks.EtaleCohomology.LimitDirectImage.projectionMap` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/LimitDirectImageSystem.lean`; the
`baseChange` names here record the base change map description, which is the form the colimit
arguments of this directory use.

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w w' v u

namespace Stacks.EtaleCohomology.LimitDirectImage

open LimitHigherDirectImage

variable (A : Type w) [Category.{w'} A]
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (smallEtalePushforward f A).IsRightAdjoint]

local notation "App" => smallEtaleSheafPullbackCompApp

variable {I : Type v} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS)

/-- A functor preserves an equality between two composites of two morphisms. -/
private theorem map_comp_congr {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {X Y Z W : C} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ W} {g' : W ⟶ Z} (h : f ≫ g = f' ≫ g') :
    G.map f ≫ G.map g = G.map f' ≫ G.map g' := by
  rw [← G.map_comp, h, G.map_comp]

/-- **The transition maps of the system of direct images**,
`h_{i'i}⁻¹g_{i, *}ℱ_i ⟶ g_{i', *}ℱ_{i'}`: the base change map of the transition square
`g_{i'} ≫ h_{i'i} = f_{i'i} ≫ g_i`, followed by `g_{i', *}` of the transition map
`φ_{i'i} : f_{i'i}⁻¹ℱ_i ⟶ ℱ_{i'}` of the system. -/
def baseChangeTransitionMap (F : EtaleSheafSystem DX A) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtaleSheafPullback A (DS.map a)).obj ((smallEtalePushforward (γ.app j) A).obj (F.obj j)) ⟶
      (smallEtalePushforward (γ.app i) A).obj (F.obj i) :=
  (smallEtaleSheafBaseChange A (DS.map a) (γ.app j) (γ.app i) (DX.map a)
      (transition_comm γ a)).app (F.obj j) ≫
    (smallEtalePushforward (γ.app i) A).map (F.sheafMap a)

/-- **The cocycle condition for the transition maps of the system of direct images.** -/
theorem baseChangeTransitionMap_comp (F : EtaleSheafSystem DX A) {i j k : Iᵒᵖ} (a : i ⟶ j)
    (b : j ⟶ k) :
    (App A (DS.map a) (DS.map b) (DS.map (a ≫ b)) (DS.map_comp a b)
          ((smallEtalePushforward (γ.app k) A).obj (F.obj k))).inv ≫
        (smallEtaleSheafPullback A (DS.map a)).map (baseChangeTransitionMap A γ F b) ≫
          baseChangeTransitionMap A γ F a =
      baseChangeTransitionMap A γ F (a ≫ b) := by
  have hτ := map_comp_congr (smallEtalePushforward (γ.app i) A) (F.sheafMap_comp a b)
  have hP := smallEtaleSheafBaseChange_paste_app_named A (γ.app k) (γ.app j) (γ.app i)
    (DS.map b) (DS.map a) (DX.map b) (DX.map a) (transition_comm γ b) (transition_comm γ a)
    (DS.map (a ≫ b)) (DS.map_comp a b) (DX.map (a ≫ b)) (DX.map_comp a b)
    (transition_comm γ (a ≫ b)) (F.obj k)
  simp only [baseChangeTransitionMap, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (smallEtaleSheafBaseChange_naturality A (DS.map a) (γ.app j) (γ.app i)
    (DX.map a) (transition_comm γ a) (F.sheafMap b)), hτ, reassoc_of% hP]

/-- **The direct images of a system of sheaves form a system of sheaves.** The sheaves
`g_{i, *}ℱ_i` on the `S_i`, with the transition maps
`Stacks.EtaleCohomology.LimitDirectImage.baseChangeTransitionMap`, satisfy the cocycle condition of
[Stacks, Tag 0EZL]. -/
abbrev pushforwardSystem (F : EtaleSheafSystem DX A) : EtaleSheafSystem DS A where
  obj i := (smallEtalePushforward (γ.app i) A).obj (F.obj i)
  map a := baseChangeTransitionMap A γ F a
  map_comp a b := by
    rw [systemPullbackComp_eq_smallEtaleSheafPullbackComp']
    exact baseChangeTransitionMap_comp A γ F a b

/-- The transition maps of `pushforwardSystem` are the maps `baseChangeTransitionMap`. -/
theorem pushforwardSystem_sheafMap (F : EtaleSheafSystem DX A) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (pushforwardSystem A γ F).sheafMap a = baseChangeTransitionMap A γ F a :=
  rfl

variable (cX : Cone DX) {cS : Cone DS} (hcS : IsLimit cS)

/-- The maps of the diagram of inverse images of the system of direct images, unfolded. -/
theorem pushforwardSystem_sheafPullbackDiagramMap (F : EtaleSheafSystem DX A) {i j : Iᵒᵖ}
    (a : i ⟶ j) :
    (pushforwardSystem A γ F).sheafPullbackDiagramMap cS (i := i) (j := j) a =
      (App A (X := cS.pt) (cS.π.app i) (DS.map a) (cS.π.app j) (cS.w a).symm
          ((smallEtalePushforward (γ.app j) A).obj (F.obj j))).inv ≫
        (smallEtaleSheafPullback A (X := cS.pt) (cS.π.app i)).map
          ((smallEtaleSheafBaseChange A (DS.map a) (γ.app j) (γ.app i) (DX.map a)
              (transition_comm γ a)).app (F.obj j)) ≫
          (smallEtaleSheafPullback A (X := cS.pt) (cS.π.app i)).map
            ((smallEtalePushforward (γ.app i) A).map (F.sheafMap a)) :=
  congrArg (_ ≫ ·) (Functor.map_comp _ _ _)

/-- **The maps `h_i⁻¹g_{i, *}ℱ_i ⟶ g_*ℱ`** of the degree zero case of [Stacks, Tag 0EYM]: the base
change map of the projection square `g ≫ h_i = f_i ≫ g_i`, followed by `g_*ι_i` for a family
`ι_i : f_i⁻¹ℱ_i ⟶ ℱ`. -/
def baseChangeProjectionMap (F : EtaleSheafSystem DX A) {𝓕 : Sheaf (smallEtaleTopology cX.pt) A}
    (ι : ∀ i : Iᵒᵖ, (smallEtaleSheafPullback A (X := cX.pt) (cX.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (i : Iᵒᵖ) :
    (smallEtaleSheafPullback A (X := cS.pt) (cS.π.app i)).obj
        ((smallEtalePushforward (γ.app i) A).obj (F.obj i)) ⟶
      (smallEtalePushforward (limitMorphism γ cX cS hcS) A).obj 𝓕 :=
  (smallEtaleSheafBaseChange A (X' := cS.pt) (Y := cX.pt) (cS.π.app i) (γ.app i)
      (limitMorphism γ cX cS hcS) (cX.π.app i)
      (limitMorphism_comp_π γ cX cS hcS i)).app (F.obj i) ≫
    (smallEtalePushforward (limitMorphism γ cX cS hcS) A).map (ι i)

/-- **The cocone identity**: the maps `h_i⁻¹g_{i, *}ℱ_i ⟶ g_*ℱ` are compatible with the maps of the
diagram of inverse images of the system of direct images, as soon as the family
`ι_i : f_i⁻¹ℱ_i ⟶ ℱ` is compatible with the maps of the diagram of inverse images of `ℱ_i`. -/
theorem isSheafPullbackCocone_baseChangeProjectionMap (F : EtaleSheafSystem DX A)
    {𝓕 : Sheaf (smallEtaleTopology cX.pt) A}
    (ι : ∀ i : Iᵒᵖ, (smallEtaleSheafPullback A (X := cX.pt) (cX.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : F.IsSheafPullbackCocone cX ι) :
    (pushforwardSystem A γ F).IsSheafPullbackCocone cS
      (baseChangeProjectionMap A γ cX hcS F ι) := by
  intro i j a
  have hτ := map_comp_congr (smallEtalePushforward (limitMorphism γ cX cS hcS) A)
    (f := (smallEtaleSheafPullback A (X := cX.pt) (cX.π.app i)).map (F.sheafMap a)) (g := ι i)
    (f' := (App A (X := cX.pt) (cX.π.app i) (DX.map a) (cX.π.app j) (cX.w a).symm (F.obj j)).hom)
    (g' := ι j) (by
      rw [← hι a, EtaleSheafSystem.sheafPullbackDiagramMap, Category.assoc, Iso.hom_inv_id_assoc])
  have hP := smallEtaleSheafBaseChange_paste_app_named A (X₂ := cX.pt) (S₂ := cS.pt) (γ.app j)
    (γ.app i) (limitMorphism γ cX cS hcS) (DS.map a) (cS.π.app i) (DX.map a) (cX.π.app i)
    (transition_comm γ a) (limitMorphism_comp_π γ cX cS hcS i) (cS.π.app j) (cS.w a).symm
    (cX.π.app j) (cX.w a).symm (limitMorphism_comp_π γ cX cS hcS j) (F.obj j)
  rw [pushforwardSystem_sheafPullbackDiagramMap]
  simp only [baseChangeProjectionMap, Category.assoc]
  rw [reassoc_of% (smallEtaleSheafBaseChange_naturality A (X' := cS.pt) (Y := cX.pt) (cS.π.app i)
    (γ.app i)
    (limitMorphism γ cX cS hcS) (cX.π.app i) (limitMorphism_comp_π γ cX cS hcS i)
    (F.sheafMap a)), hτ, reassoc_of% hP]

end Stacks.EtaleCohomology.LimitDirectImage

end
