module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleHigherBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackComparison

/-!
# The cocycle condition and the cocone identity for higher direct images along a limit

Let `(X_i, f_{i'i})` and `(S_i, h_{i'i})` be inverse systems of schemes, let `g_i : X_i ⟶ S_i` be
a morphism of the first system into the second, let `f_i : X ⟶ X_i` be the projections of a cone
over the first system, let `h_i : S ⟶ S_i` be those of a limit cone over the second, and let
`g : X ⟶ S` be the limit morphism. Let `(ℱ_i, φ_{i'i})` be a system of abelian sheaves on
`(X_i, f_{i'i})` and let `ℱ` on the small étale site of `X` carry maps `ι_i : f_i^{-1}ℱ_i ⟶ ℱ`.

Consider the maps of [Stacks, Tag 0EYM],

* `ψ_{i'i} : h_{i'i}^{-1} R^p g_{i, *} ℱ_i ⟶ R^p g_{i', *} ℱ_{i'}` (`transitionMap`),
* `ψ_i : h_i^{-1} R^p g_{i, *} ℱ_i ⟶ R^p g_* ℱ` (`projectionMap`).

This file proves two compatibilities of them:

* the cocycle condition `ψ_{i''i} = ψ_{i''i'} ∘ h_{i''i'}^{-1}ψ_{i'i}`, which makes the sheaves
  `R^p g_{i, *} ℱ_i` with the maps `ψ_{i'i}` a system of sheaves on `(S_i, h_{i'i})` in the sense
  of [Stacks, Tag 0EZL];
* the cocone identity `ψ_{i'} ∘ h_{i'}^{-1}ψ_{i'i} = ψ_i`, for a family `ι_i` that is itself
  compatible with the `φ_{i'i}` — which it is when `ℱ = colim f_i^{-1}ℱ_i`.

## Main definitions

* `Stacks.EtaleCohomology.LimitHigherDirectImage.higherDirectImageSystem` — the sheaves
  `R^p g_{i, *} ℱ_i` on the `S_i` with the maps `ψ_{i'i}`, as a system of sheaves on
  `(S_i, h_{i'i})`.

## Main results

* `Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap_comp` — **the cocycle condition**
  for the maps `ψ_{i'i}`.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.projectionMap_cocone` — **the cocone identity**
  for the maps `ψ_i`.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.pushforwardStageTransition_comp` and
  `Stacks.EtaleCohomology.LimitHigherDirectImage.pushforwardStageLeg_cocone` — both at the
  system of direct images `ℱ_i = f_{i, *}ℱ` with the counits as the maps `ι_i`, which is the
  diagram of [Stacks, Tag 0DV2]. The compatibility of the counits is not a hypothesis there: it
  is `Stacks.EtaleCohomology.coneDirectImageCounit_cocone`.
* `Stacks.EtaleCohomology.higherBaseChangeMapAb_paste_app_named` — the pasting law for the base
  change map on higher direct images, with the two composite inverse-image legs of the rectangle
  given as named morphisms together with equations identifying them.

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0DV2](https://stacks.math.columbia.edu/tag/0DV2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **The pasting law for the base change map on higher direct images, with the two composite
legs named.** The rectangle's inverse-image legs are given as morphisms `u` and `v` together
with equations identifying them with the composites, so that the two comparisons of inverse
images are `Stacks.EtaleCohomology.smallEtalePullbackAbComp'`. -/
public theorem higherBaseChangeMapAb_paste_app_named {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}}
    (g₀ : X₀ ⟶ S₀) (g₁ : X₁ ⟶ S₁) (g₂ : X₂ ⟶ S₂) (u₁ : S₁ ⟶ S₀) (u₂ : S₂ ⟶ S₁) (v₁ : X₁ ⟶ X₀)
    (v₂ : X₂ ⟶ X₁) (u : S₂ ⟶ S₀) (hu : u = u₂ ≫ u₁) (v : X₂ ⟶ X₀) (hv : v = v₂ ≫ v₁)
    (w : g₂ ≫ u = v ≫ g₀) (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁) (q : ℕ)
    (F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) :
    (higherBaseChangeMapAb u g₀ g₂ v w q).app F =
      (smallEtalePullbackAbComp' u₂ u₁ u hu).inv.app
          (((smallEtalePushforwardAb g₀).rightDerived q).obj F) ≫
        (smallEtalePullbackAb u₂).map ((higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ q).app F) ≫
          (higherBaseChangeMapAb u₂ g₁ g₂ v₂ w₂ q).app ((smallEtalePullbackAb v₁).obj F) ≫
            ((smallEtalePushforwardAb g₂).rightDerived q).map
              ((smallEtalePullbackAbComp' v₂ v₁ v hv).hom.app F) := by
  subst hu hv
  simpa [smallEtalePullbackAbComp'] using
    higherBaseChangeMapAb_paste_app g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ q F

namespace LimitHigherDirectImage

/-- In a category, `c' ≫ An ≫ Ba = ψ` whenever `c' = c`, `An = A ≫ n`, `Ba = B' ≫ r`,
`ψ = bc ≫ m` and `bc = c ≫ A ≫ B ≫ T`, the square `n ≫ B' = B ≫ s` commutes and
`T ≫ m = s ≫ r`. -/
private theorem paste_cocycle_algebra {E : Type*} [Category* E] {o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ : E}
    {c c' : o₁ ⟶ o₂} {A : o₂ ⟶ o₃} {n : o₃ ⟶ o₄} {B' : o₄ ⟶ o₅} {r : o₅ ⟶ o₆} {B : o₃ ⟶ o₇}
    {s : o₇ ⟶ o₅} {T : o₇ ⟶ o₈} {m : o₈ ⟶ o₆} {An : o₂ ⟶ o₄} {Ba : o₄ ⟶ o₆} {bc : o₁ ⟶ o₈}
    {ψ : o₁ ⟶ o₆} (hc : c' = c) (hAn : An = A ≫ n) (hbc : bc = c ≫ A ≫ B ≫ T)
    (hψ : ψ = bc ≫ m) (hBa : Ba = B' ≫ r) (hnat : n ≫ B' = B ≫ s) (htail : T ≫ m = s ≫ r) :
    c' ≫ An ≫ Ba = ψ := by
  rw [hc, hAn, hBa, hψ, hbc]
  simp only [Category.assoc]
  rw [reassoc_of% hnat, ← htail]

/-- A functor sends a commuting square of morphisms to a commuting square. -/
private theorem functor_map_comp_eq {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A B B' Z : C} {f : A ⟶ B} {g : B ⟶ Z} {f' : A ⟶ B'} {g' : B' ⟶ Z} (h : f ≫ g = f' ≫ g') :
    G.map f ≫ G.map g = G.map f' ≫ G.map g' := by
  rw [← G.map_comp, ← G.map_comp, h]

variable {I : Type v} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS) (p : ℕ)

/-! ### The cocycle condition -/

/-- The comparison `systemPullbackComp DS a b` of the inverse images along a composite
transition, at `R^p g_{k, *} ℱ_k`, is the comparison `smallEtalePullbackAbComp'` along
`DS.map_comp a b`. -/
private theorem transitionHead (F : EtaleSheafSystem DX Ab.{u + 1}) {i j k : Iᵒᵖ} (a : i ⟶ j)
    (b : j ⟶ k) :
    (systemPullbackComp DS Ab.{u + 1} a b).inv.app
        (((smallEtalePushforwardAb (γ.app k)).rightDerived p).obj (F.obj k)) =
      (smallEtalePullbackAbComp' (DS.map a) (DS.map b) (DS.map (a ≫ b))
            (DS.map_comp a b)).inv.app
        (((smallEtalePushforwardAb (γ.app k)).rightDerived p).obj (F.obj k)) :=
  congrArg (fun z => z.inv.app
      (((smallEtalePushforwardAb (γ.app k)).rightDerived p).obj (F.obj k)))
    (systemPullbackComp_eq DS a b)

/-- The cocycle condition of a system of sheaves, with the comparison of inverse images written
as `smallEtalePullbackAbComp'` and moved to the other side. -/
private theorem transitionSheafTail {D : Iᵒᵖ ⥤ Scheme.{u}} (F : EtaleSheafSystem D Ab.{u + 1})
    {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (smallEtalePullbackAbComp' (D.map a) (D.map b) (D.map (a ≫ b))
          (D.map_comp a b)).hom.app (F.obj k) ≫ F.map (a ≫ b) =
      (systemPullback D Ab.{u + 1} a).map (F.map b) ≫ F.map a := by
  rw [← systemPullbackComp_eq, ← F.map_comp a b, ← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp]

/-- The transition map is the base change map of the transition square followed by the `p`-th
right derived direct image of the transition map of the system of sheaves. -/
private theorem transitionMap_factor (F : EtaleSheafSystem DX Ab.{u + 1}) {i j : Iᵒᵖ}
    (a : i ⟶ j) :
    transitionMap γ p F a =
      (higherBaseChangeMapAb (DS.map a) (γ.app j) (γ.app i) (DX.map a)
            (transition_comm γ a) p).app (F.obj j) ≫
        ((smallEtalePushforwardAb (γ.app i)).rightDerived p).map (F.map a) := rfl

/-- The inverse image along the first transition of the transition map, split into its two
factors. -/
private theorem transitionMap_pullback_factor (F : EtaleSheafSystem DX Ab.{u + 1})
    {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (systemPullback DS Ab.{u + 1} a).map (transitionMap γ p F b) =
      (smallEtalePullbackAb (DS.map a)).map
          ((higherBaseChangeMapAb (DS.map b) (γ.app k) (γ.app j) (DX.map b)
            (transition_comm γ b) p).app (F.obj k)) ≫
        (smallEtalePullbackAb (DS.map a)).map
          (((smallEtalePushforwardAb (γ.app j)).rightDerived p).map (F.map b)) :=
  (smallEtalePullbackAb (DS.map a)).map_comp _ _

/-- The naturality of the base change map of a transition square at the transition map of the
system of sheaves. -/
private theorem transitionMap_nat (F : EtaleSheafSystem DX Ab.{u + 1}) {i j k : Iᵒᵖ}
    (a : i ⟶ j) (b : j ⟶ k) :
    (smallEtalePullbackAb (DS.map a)).map
          (((smallEtalePushforwardAb (γ.app j)).rightDerived p).map (F.map b)) ≫
        (higherBaseChangeMapAb (DS.map a) (γ.app j) (γ.app i) (DX.map a)
            (transition_comm γ a) p).app (F.obj j) =
      (higherBaseChangeMapAb (DS.map a) (γ.app j) (γ.app i) (DX.map a)
            (transition_comm γ a) p).app ((smallEtalePullbackAb (DX.map b)).obj (F.obj k)) ≫
        ((smallEtalePushforwardAb (γ.app i)).rightDerived p).map
          ((smallEtalePullbackAb (DX.map a)).map (F.map b)) :=
  (higherBaseChangeMapAb (DS.map a) (γ.app j) (γ.app i) (DX.map a)
    (transition_comm γ a) p).naturality (F.map b)

/-- The pasting law at the two transition squares of `i'' ≥ i' ≥ i`. -/
private theorem transitionMap_paste (F : EtaleSheafSystem DX Ab.{u + 1}) {i j k : Iᵒᵖ}
    (a : i ⟶ j) (b : j ⟶ k) :
    (higherBaseChangeMapAb (DS.map (a ≫ b)) (γ.app k) (γ.app i) (DX.map (a ≫ b))
          (transition_comm γ (a ≫ b)) p).app (F.obj k) =
      (smallEtalePullbackAbComp' (DS.map a) (DS.map b) (DS.map (a ≫ b))
            (DS.map_comp a b)).inv.app
          (((smallEtalePushforwardAb (γ.app k)).rightDerived p).obj (F.obj k)) ≫
        (smallEtalePullbackAb (DS.map a)).map
            ((higherBaseChangeMapAb (DS.map b) (γ.app k) (γ.app j) (DX.map b)
              (transition_comm γ b) p).app (F.obj k)) ≫
          (higherBaseChangeMapAb (DS.map a) (γ.app j) (γ.app i) (DX.map a)
              (transition_comm γ a) p).app ((smallEtalePullbackAb (DX.map b)).obj (F.obj k)) ≫
            ((smallEtalePushforwardAb (γ.app i)).rightDerived p).map
              ((smallEtalePullbackAbComp' (DX.map a) (DX.map b) (DX.map (a ≫ b))
                (DX.map_comp a b)).hom.app (F.obj k)) :=
  higherBaseChangeMapAb_paste_app_named (γ.app k) (γ.app j) (γ.app i) (DS.map b) (DS.map a)
    (DX.map b) (DX.map a) (DS.map (a ≫ b)) (DS.map_comp a b) (DX.map (a ≫ b))
    (DX.map_comp a b) (transition_comm γ (a ≫ b)) (transition_comm γ b) (transition_comm γ a)
    p (F.obj k)

/-- **The cocycle condition for the transition maps of Stacks 0EYM.** For `i'' ≥ i' ≥ i` the map
`ψ_{i''i}` is the composite of `ψ_{i''i'}` with the inverse image along `h_{i''i'}` of
`ψ_{i'i}`, read through the comparison of the inverse images along `h_{i''i} = h_{i''i'} ≫
h_{i'i}`. -/
theorem transitionMap_comp (F : EtaleSheafSystem DX Ab.{u + 1}) {i j k : Iᵒᵖ} (a : i ⟶ j)
    (b : j ⟶ k) :
    (systemPullbackComp DS Ab.{u + 1} a b).inv.app
          (((smallEtalePushforwardAb (γ.app k)).rightDerived p).obj (F.obj k)) ≫
        (systemPullback DS Ab.{u + 1} a).map (transitionMap γ p F b) ≫ transitionMap γ p F a =
      transitionMap γ p F (a ≫ b) :=
  paste_cocycle_algebra (transitionHead γ p F a b) (transitionMap_pullback_factor γ p F a b)
    (transitionMap_paste γ p F a b) (transitionMap_factor γ p F (a ≫ b))
    (transitionMap_factor γ p F a) (transitionMap_nat γ p F a b)
    (functor_map_comp_eq _ (transitionSheafTail F a b))

/-- **The higher direct images of a system of sheaves form a system of sheaves on the limit
system of bases.** The sheaves `R^p g_{i, *} ℱ_i` on the `S_i`, with the transition maps
`ψ_{i'i}` of Stacks 0EYM, satisfy the cocycle condition of Stacks 0EZL. -/
def higherDirectImageSystem (F : EtaleSheafSystem DX Ab.{u + 1}) :
    EtaleSheafSystem DS Ab.{u + 1} where
  obj i := ((smallEtalePushforwardAb (γ.app i)).rightDerived p).obj (F.obj i)
  map a := transitionMap γ p F a
  map_comp a b := transitionMap_comp γ p F a b

/-! ### The cocone identity -/

variable (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS)
  (𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})

/-- The comparison `conePullbackComp cS a` of the inverse images along the factorisation
`h_i = h_{i'} ≫ h_{i'i}` of a projection, at `R^p g_{j, *} ℱ_j`, is the comparison
`smallEtalePullbackAbComp'` along `(cS.w a).symm`. -/
private theorem projectionHead (F : EtaleSheafSystem DX Ab.{u + 1}) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (conePullbackComp cS a).inv.app
        (((smallEtalePushforwardAb (γ.app j)).rightDerived p).obj (F.obj j)) =
      (smallEtalePullbackAbComp' (cS.π.app i) (DS.map a) (cS.π.app j) (cS.w a).symm).inv.app
        (((smallEtalePushforwardAb (γ.app j)).rightDerived p).obj (F.obj j)) :=
  congrArg (fun z => z.inv.app
      (((smallEtalePushforwardAb (γ.app j)).rightDerived p).obj (F.obj j)))
    (conePullbackComp_eq cS a)

/-- The compatibility of the maps presenting `ℱ`, with the comparison of inverse images written
as `smallEtalePullbackAbComp'`. -/
private theorem projectionSheafTail {D : Iᵒᵖ ⥤ Scheme.{u}} (c : Cone D)
    (G : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}) (F : EtaleSheafSystem D Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ G) {i j : Iᵒᵖ}
    (a : i ⟶ j)
    (hι : (conePullbackComp c a).hom.app (F.obj j) ≫ ι j =
      (smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ ι i) :
    (smallEtalePullbackAbComp' (c.π.app i) (D.map a) (c.π.app j)
          (c.w a).symm).hom.app (F.obj j) ≫ ι j =
      (smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ ι i := by
  rwa [← conePullbackComp_eq]

/-- The cocone map is the base change map of the projection square followed by the `p`-th right
derived direct image along `g` of the map presenting `ℱ`. -/
private theorem projectionMap_factor (F : EtaleSheafSystem DX Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕) (i : Iᵒᵖ) :
    projectionMap γ cX cS hcS p 𝓕 F ι i =
      (higherBaseChangeMapAb (cS.π.app i) (γ.app i) (limitMorphism γ cX cS hcS) (cX.π.app i)
            (limitMorphism_comp_π γ cX cS hcS i) p).app (F.obj i) ≫
        ((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived p).map (ι i) := rfl

/-- The inverse image along the projection `h_{i'}` of the transition map, split into its two
factors. -/
private theorem projectionMap_pullback_factor (F : EtaleSheafSystem DX Ab.{u + 1})
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtalePullbackAb (cS.π.app i)).map (transitionMap γ p F a) =
      (smallEtalePullbackAb (cS.π.app i)).map
          ((higherBaseChangeMapAb (DS.map a) (γ.app j) (γ.app i) (DX.map a)
            (transition_comm γ a) p).app (F.obj j)) ≫
        (smallEtalePullbackAb (cS.π.app i)).map
          (((smallEtalePushforwardAb (γ.app i)).rightDerived p).map (F.map a)) :=
  (smallEtalePullbackAb (cS.π.app i)).map_comp _ _

/-- The naturality of the base change map of the projection square at the transition map of the
system of sheaves. -/
private theorem projectionMap_nat (F : EtaleSheafSystem DX Ab.{u + 1}) {i j : Iᵒᵖ}
    (a : i ⟶ j) :
    (smallEtalePullbackAb (cS.π.app i)).map
          (((smallEtalePushforwardAb (γ.app i)).rightDerived p).map (F.map a)) ≫
        (higherBaseChangeMapAb (cS.π.app i) (γ.app i) (limitMorphism γ cX cS hcS)
            (cX.π.app i) (limitMorphism_comp_π γ cX cS hcS i) p).app (F.obj i) =
      (higherBaseChangeMapAb (cS.π.app i) (γ.app i) (limitMorphism γ cX cS hcS)
            (cX.π.app i) (limitMorphism_comp_π γ cX cS hcS i) p).app
          ((smallEtalePullbackAb (DX.map a)).obj (F.obj j)) ≫
        ((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived p).map
          ((smallEtalePullbackAb (cX.π.app i)).map (F.map a)) :=
  (higherBaseChangeMapAb (cS.π.app i) (γ.app i) (limitMorphism γ cX cS hcS)
    (cX.π.app i) (limitMorphism_comp_π γ cX cS hcS i) p).naturality (F.map a)

/-- The pasting law at the projection square of `i'` pasted with the transition square of
`i' ≥ i`. -/
private theorem projectionMap_paste (F : EtaleSheafSystem DX Ab.{u + 1}) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (higherBaseChangeMapAb (cS.π.app j) (γ.app j) (limitMorphism γ cX cS hcS) (cX.π.app j)
          (limitMorphism_comp_π γ cX cS hcS j) p).app (F.obj j) =
      (smallEtalePullbackAbComp' (cS.π.app i) (DS.map a) (cS.π.app j) (cS.w a).symm).inv.app
          (((smallEtalePushforwardAb (γ.app j)).rightDerived p).obj (F.obj j)) ≫
        (smallEtalePullbackAb (cS.π.app i)).map
            ((higherBaseChangeMapAb (DS.map a) (γ.app j) (γ.app i) (DX.map a)
              (transition_comm γ a) p).app (F.obj j)) ≫
          (higherBaseChangeMapAb (cS.π.app i) (γ.app i) (limitMorphism γ cX cS hcS)
                (cX.π.app i) (limitMorphism_comp_π γ cX cS hcS i) p).app
              ((smallEtalePullbackAb (DX.map a)).obj (F.obj j)) ≫
            ((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived p).map
              ((smallEtalePullbackAbComp' (cX.π.app i) (DX.map a) (cX.π.app j)
                (cX.w a).symm).hom.app (F.obj j)) :=
  higherBaseChangeMapAb_paste_app_named (γ.app j) (γ.app i) (limitMorphism γ cX cS hcS)
    (DS.map a) (cS.π.app i) (DX.map a) (cX.π.app i) (cS.π.app j) (cS.w a).symm (cX.π.app j)
    (cX.w a).symm (limitMorphism_comp_π γ cX cS hcS j) (transition_comm γ a)
    (limitMorphism_comp_π γ cX cS hcS i) p (F.obj j)

/-- **The cocone identity for the maps of Stacks 0EYM.** For `i' ≥ i` the map `ψ_i` is the
composite of `ψ_{i'}` with the inverse image along `h_{i'}` of `ψ_{i'i}`, read through the
comparison of the inverse images along `h_i = h_{i'} ≫ h_{i'i}`.

The family `ι_i : f_i^{-1}ℱ_i ⟶ ℱ` is assumed compatible with the transition maps of the system
of sheaves, as it is when `ℱ = colim f_i^{-1}ℱ_i`. -/
theorem projectionMap_cocone (F : EtaleSheafSystem DX Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕) {i j : Iᵒᵖ}
    (a : i ⟶ j)
    (hι : (conePullbackComp cX a).hom.app (F.obj j) ≫ ι j =
      (smallEtalePullbackAb (cX.π.app i)).map (F.map a) ≫ ι i) :
    (conePullbackComp cS a).inv.app
          (((smallEtalePushforwardAb (γ.app j)).rightDerived p).obj (F.obj j)) ≫
        (smallEtalePullbackAb (cS.π.app i)).map (transitionMap γ p F a) ≫
          projectionMap γ cX cS hcS p 𝓕 F ι i =
      projectionMap γ cX cS hcS p 𝓕 F ι j :=
  paste_cocycle_algebra (projectionHead γ p cS F a)
    (projectionMap_pullback_factor γ p cS F a) (projectionMap_paste γ p cX cS hcS F a)
    (projectionMap_factor γ p cX cS hcS 𝓕 F ι j) (projectionMap_factor γ p cX cS hcS 𝓕 F ι i)
    (projectionMap_nat γ p cX cS hcS F a)
    (functor_map_comp_eq _ (projectionSheafTail cX 𝓕 F ι a hι))

/-! ### The diagram of Stacks 0DV2 -/

/-- **The cocycle condition at the system of direct images.** The transition maps of the diagram
of Stacks 0DV2 compose correctly along `i'' ≥ i' ≥ i`. -/
theorem pushforwardStageTransition_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (systemPullbackComp DS Ab.{u + 1} a b).inv.app
          (((smallEtalePushforwardAb (γ.app k)).rightDerived p).obj
            ((directImageSystem DX Ab.{u + 1} cX 𝓕).obj k)) ≫
        (systemPullback DS Ab.{u + 1} a).map (pushforwardStageTransition cX 𝓕 γ p b) ≫
          pushforwardStageTransition cX 𝓕 γ p a =
      pushforwardStageTransition cX 𝓕 γ p (a ≫ b) :=
  transitionMap_comp γ p (directImageSystem DX Ab.{u + 1} cX 𝓕) a b

/-- **The cocone identity at the system of direct images.** The cocone maps of the diagram of
Stacks 0DV2 are compatible with its transition maps. The compatibility of the maps presenting
`𝓕` is not a hypothesis: the maps are the counits of the adjunctions along the projections, and
`Stacks.EtaleCohomology.coneDirectImageCounit_cocone` is their compatibility. -/
theorem pushforwardStageLeg_cocone {i j : Iᵒᵖ} (a : i ⟶ j) :
    (conePullbackComp cS a).inv.app
          (((smallEtalePushforwardAb (γ.app j)).rightDerived p).obj
            ((directImageSystem DX Ab.{u + 1} cX 𝓕).obj j)) ≫
        (smallEtalePullbackAb (cS.π.app i)).map (pushforwardStageTransition cX 𝓕 γ p a) ≫
          pushforwardStageLeg cX 𝓕 γ cS hcS p i =
      pushforwardStageLeg cX 𝓕 γ cS hcS p j := by
  refine projectionMap_cocone γ p cX cS hcS 𝓕 (directImageSystem DX Ab.{u + 1} cX 𝓕)
    (coneDirectImageCounit cX 𝓕) a ?_
  rw [← coneDirectImageCounit_cocone cX 𝓕 a, ← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp]

end LimitHigherDirectImage

end Stacks.EtaleCohomology

end
