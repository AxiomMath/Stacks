module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitBaseChangeInverseImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageCocycle

/-!
# The cube of base change maps of an inverse system of squares

A commutative cube of schemes has two horizontal faces, a "top" square
`(f₁, g₁, h₁, e₁)` and a "bottom" square `(f₀, g₀, h₀, e₀)`, joined by four vertical morphisms.
Its base change maps on higher direct images are related by pasting: the rectangle made of the
`g`-face and the top square and the rectangle made of the bottom square and the `h`-face are
the same rectangle, so by the pasting law
`Stacks.EtaleCohomology.higherBaseChangeMapAb_paste_app_named` their base change maps agree
(`Stacks.EtaleCohomology.higherBaseChangeMapAb_cube`).

For an inverse system of cartesian squares `X_i ← Y_i, S_i ← T_i` with limit square
`X ← Y, S ← T`, as in [Stacks, Tag 0EZT], this is applied twice. With the transition squares as
vertical faces it says that the base change maps of the levels commute with the transition maps
`ψ_{i'i}` of [Stacks, Tag 0EYM] for `g` and for `h`; with the projection squares as vertical faces
it says that the base change map of the limit square commutes with the cocone maps `ψ_i`.
The system of sheaves for `h` is the inverse image `e_i^{-1}ℱ_i`,
`Stacks.EtaleCohomology.LimitBaseChange.inverseImageSystem`.

## Main results

* `Stacks.EtaleCohomology.higherBaseChangeMapAb_cube` — the cube of base change maps.
* `Stacks.EtaleCohomology.LimitBaseChange.transitionMap_comp_higherBaseChangeMapAb` — the base
  change maps of the levels commute with the transition maps.
* `Stacks.EtaleCohomology.LimitBaseChange.projectionMap_comp_higherBaseChangeMapAb` — the base
  change map of the limit square commutes with the cocone maps.
* `Stacks.EtaleCohomology.LimitBaseChange.stageMap_transition` — the comparisons of the levels,
  pulled back to the limit, commute with the diagram maps of the two colimit diagrams.

## Implementation notes

Every identity between composites of base change maps is obtained by instantiating a lemma on
variables in an abstract category (`cube_algebra`, `transition_algebra`, ...) with equations each
of which is a single lemma application; rearranging such composites with `rw` makes the kernel
unfold the right derived functors.

## References

* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

/-- The rearrangement behind `higherBaseChangeMapAb_cube`, in an abstract category. -/
theorem cube_algebra {C : Type*} [Category* C] {P P' Q R₁ R₁' R R' T : C}
    {α : P ≅ Q} {β : P' ≅ Q} {γ : R ≅ T} {A : P ⟶ R₁} {B : R₁ ⟶ R} {A' : P' ⟶ R₁'}
    {B' : R₁' ⟶ R'} {δ : R' ⟶ T} {K : P ⟶ P'} {E : R' ⟶ R} {BC : Q ⟶ T}
    (h₁ : BC = α.inv ≫ A ≫ B ≫ γ.hom) (h₂ : BC = β.inv ≫ A' ≫ B' ≫ δ)
    (hK : K = α.hom ≫ β.inv) (hE : E = δ ≫ γ.inv) :
    A ≫ B = K ≫ A' ≫ B' ≫ E := by
  have h : A ≫ B ≫ γ.hom = α.hom ≫ β.inv ≫ A' ≫ B' ≫ δ := by
    rw [← h₂, h₁, Iso.hom_inv_id_assoc]
  rw [hK, hE, ← cancel_mono γ.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact h

/-- **The cube of base change maps.** For a commutative cube of schemes with top square
`(f₁, g₁, h₁, e₁)`, bottom square `(f₀, g₀, h₀, e₀)` and vertical morphisms `x, s, t, y`, the base
change map of the `g`-face followed by that of the top square is, up to the comparisons of the
inverse images along the `f`-face and the `e`-face, the base change map of the bottom square
followed by that of the `h`-face: both are the base change map of the rectangle along
`U = f₁ ≫ s = x ≫ f₀` and `V = e₁ ≫ t = y ≫ e₀`, by the pasting law. -/
theorem higherBaseChangeMapAb_cube {X₀ S₀ T₀ Y₀ X₁ S₁ T₁ Y₁ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (g₀ : T₀ ⟶ S₀) (h₀ : Y₀ ⟶ X₀) (e₀ : Y₀ ⟶ T₀) (w₀ : h₀ ≫ f₀ = e₀ ≫ g₀)
    (f₁ : X₁ ⟶ S₁) (g₁ : T₁ ⟶ S₁) (h₁ : Y₁ ⟶ X₁) (e₁ : Y₁ ⟶ T₁) (w₁ : h₁ ≫ f₁ = e₁ ≫ g₁)
    (x : X₁ ⟶ X₀) (s : S₁ ⟶ S₀) (t : T₁ ⟶ T₀) (y : Y₁ ⟶ Y₀)
    (wg : g₁ ≫ s = t ≫ g₀) (wh : h₁ ≫ x = y ≫ h₀)
    (U : X₁ ⟶ S₀) (hU₁ : U = f₁ ≫ s) (hU₂ : U = x ≫ f₀)
    (V : Y₁ ⟶ T₀) (hV₁ : V = e₁ ≫ t) (hV₂ : V = y ≫ e₀) (q : ℕ)
    (F : Sheaf (smallEtaleTopology T₀) Ab.{u + 1}) :
    (smallEtalePullbackAb f₁).map ((higherBaseChangeMapAb s g₀ g₁ t wg q).app F) ≫
        (higherBaseChangeMapAb f₁ g₁ h₁ e₁ w₁ q).app ((smallEtalePullbackAb t).obj F) =
      ((smallEtalePullbackAbSquareIso f₁ x s f₀ U hU₁ hU₂).app
          (((smallEtalePushforwardAb g₀).rightDerived q).obj F)).hom ≫
        (smallEtalePullbackAb x).map ((higherBaseChangeMapAb f₀ g₀ h₀ e₀ w₀ q).app F) ≫
        (higherBaseChangeMapAb x h₀ h₁ y wh q).app ((smallEtalePullbackAb e₀).obj F) ≫
        ((smallEtalePushforwardAb h₁).rightDerived q).map
          (((smallEtalePullbackAbSquareIso y e₁ e₀ t V hV₂ hV₁).app F).hom) := by
  have wUV : h₁ ≫ U = V ≫ g₀ := by
    rw [hU₂, ← Category.assoc, wh, Category.assoc, w₀, ← Category.assoc, ← hV₂]
  exact cube_algebra
    (α := (smallEtalePullbackAbComp' f₁ s U hU₁).app
      (((smallEtalePushforwardAb g₀).rightDerived q).obj F))
    (β := (smallEtalePullbackAbComp' x f₀ U hU₂).app
      (((smallEtalePushforwardAb g₀).rightDerived q).obj F))
    (γ := ((smallEtalePushforwardAb h₁).rightDerived q).mapIso
      ((smallEtalePullbackAbComp' e₁ t V hV₁).app F))
    (higherBaseChangeMapAb_paste_app_named g₀ g₁ h₁ s f₁ t e₁ U hU₁ V hV₁ wUV wg w₁ q F)
    (higherBaseChangeMapAb_paste_app_named g₀ h₀ h₁ f₀ x e₀ y U hU₂ V hV₂ wUV w₀ wh q F)
    rfl (((smallEtalePushforwardAb h₁).rightDerived q).map_comp _ _)

namespace LimitBaseChange

open LimitHigherDirectImage

/-- The rearrangement behind `transitionMap_comp_higherBaseChangeMapAb` and
`projectionMap_comp_higherBaseChangeMapAb`, in an abstract category. -/
theorem cubeLeg_algebra {C : Type*} [Category* C] {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ : C}
    {ψ : o₀ ⟶ o₂} {x₁ : o₀ ⟶ o₁} {x₂ : o₁ ⟶ o₂} {b : o₂ ⟶ o₃} {b' : o₁ ⟶ o₄} {r : o₄ ⟶ o₃}
    {K : o₀ ⟶ o₅} {M : o₅ ⟶ o₆} {B : o₆ ⟶ o₇} {κ : o₇ ⟶ o₄} {G : o₇ ⟶ o₃} {ψ' : o₆ ⟶ o₃}
    (hA : ψ = x₁ ≫ x₂) (hN : x₂ ≫ b = b' ≫ r) (hC : x₁ ≫ b' = K ≫ M ≫ B ≫ κ)
    (hT : κ ≫ r = G) (hψ : ψ' = B ≫ G) :
    ψ ≫ b = K ≫ M ≫ ψ' := by
  rw [hA, hψ, ← hT, Category.assoc, hN, ← Category.assoc, hC]
  simp only [Category.assoc]

variable {I : Type v} [Preorder I] {DX DS DT DY : Iᵒᵖ ⥤ Scheme.{u}}
  (f : DX ⟶ DS) (g : DT ⟶ DS) (h : DY ⟶ DX) (e : DY ⟶ DT)
  (w : ∀ i : Iᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i) (q : ℕ)

/-- The inverse image along `f_{i'}` of the transition map `ψ_{i'i}` for `g`, split into its two
factors. -/
private theorem map_transitionMap_eq (F : EtaleSheafSystem DT Ab.{u + 1}) {i j : Iᵒᵖ}
    (a : i ⟶ j) :
    (smallEtalePullbackAb (f.app i)).map (transitionMap g q F a) =
      (smallEtalePullbackAb (f.app i)).map
          ((higherBaseChangeMapAb (DS.map a) (g.app j) (g.app i) (DT.map a)
            (transition_comm g a) q).app (F.obj j)) ≫
        (smallEtalePullbackAb (f.app i)).map
          (((smallEtalePushforwardAb (g.app i)).rightDerived q).map (F.map a)) :=
  (smallEtalePullbackAb (f.app i)).map_comp _ _

/-- The naturality of the base change map of the `i'`-th square at the transition map of the
system. -/
private theorem higherBaseChangeMapAb_naturality_systemMap (F : EtaleSheafSystem DT Ab.{u + 1})
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtalePullbackAb (f.app i)).map
          (((smallEtalePushforwardAb (g.app i)).rightDerived q).map (F.map a)) ≫
        (higherBaseChangeMapAb (f.app i) (g.app i) (h.app i) (e.app i) (w i) q).app (F.obj i) =
      (higherBaseChangeMapAb (f.app i) (g.app i) (h.app i) (e.app i) (w i) q).app
          ((smallEtalePullbackAb (DT.map a)).obj (F.obj j)) ≫
        ((smallEtalePushforwardAb (h.app i)).rightDerived q).map
          ((smallEtalePullbackAb (e.app i)).map (F.map a)) :=
  (higherBaseChangeMapAb (f.app i) (g.app i) (h.app i) (e.app i) (w i) q).naturality (F.map a)

/-- The image under `R^q h_{i', *}` of the transition map of the inverse image of the system,
split into the comparison and the inverse image of the transition map. -/
private theorem map_inverseImageSystem_map (F : EtaleSheafSystem DT Ab.{u + 1}) {i j : Iᵒᵖ}
    (a : i ⟶ j) :
    ((smallEtalePushforwardAb (h.app i)).rightDerived q).map
        (((smallEtalePullbackAbSquareIso (DY.map a) (e.app i) (e.app j) (DT.map a)
          (DY.map a ≫ e.app j) rfl (e.naturality a)).app (F.obj j)).hom) ≫
        ((smallEtalePushforwardAb (h.app i)).rightDerived q).map
          ((smallEtalePullbackAb (e.app i)).map (F.map a)) =
      ((smallEtalePushforwardAb (h.app i)).rightDerived q).map
        ((inverseImageSystem e F).map a) :=
  (((smallEtalePushforwardAb (h.app i)).rightDerived q).map_comp _ _).symm.trans
    (congrArg ((smallEtalePushforwardAb (h.app i)).rightDerived q).map
      (inverseImageSystem_map_eq e F a).symm)

/-- The transition map `ψ_{i'i}` for `h` with the system `e_i^{-1}ℱ_i`, split into its two
factors. -/
private theorem transitionMap_inverseImageSystem_eq (F : EtaleSheafSystem DT Ab.{u + 1})
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    transitionMap h q (inverseImageSystem e F) a =
      (higherBaseChangeMapAb (DX.map a) (h.app j) (h.app i) (DY.map a) (transition_comm h a)
          q).app ((smallEtalePullbackAb (e.app j)).obj (F.obj j)) ≫
        ((smallEtalePushforwardAb (h.app i)).rightDerived q).map
          ((inverseImageSystem e F).map a) :=
  rfl

/-- **The base change maps of the levels commute with the transition maps** `ψ_{i'i}` of
[Stacks, Tag 0EYM], for `g` with the system `ℱ_i` and for `h` with the system `e_i^{-1}ℱ_i`, up to
the comparison of the inverse images along `f_{i'} ≫ h_{i'i} = f_{i'i} ≫ f_i`: the cube with the
transition squares as vertical faces. -/
theorem transitionMap_comp_higherBaseChangeMapAb (F : EtaleSheafSystem DT Ab.{u + 1})
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtalePullbackAb (f.app i)).map (transitionMap g q F a) ≫
        (higherBaseChangeMapAb (f.app i) (g.app i) (h.app i) (e.app i) (w i) q).app (F.obj i) =
      ((smallEtalePullbackAbSquareIso (f.app i) (DX.map a) (DS.map a) (f.app j)
          (f.app i ≫ DS.map a) rfl (f.naturality a).symm).app
          (((smallEtalePushforwardAb (g.app j)).rightDerived q).obj (F.obj j))).hom ≫
        (smallEtalePullbackAb (DX.map a)).map
          ((higherBaseChangeMapAb (f.app j) (g.app j) (h.app j) (e.app j) (w j) q).app (F.obj j)) ≫
        transitionMap h q (inverseImageSystem e F) a :=
  cubeLeg_algebra (map_transitionMap_eq f g q F a)
    (higherBaseChangeMapAb_naturality_systemMap f g h e w q F a)
    (higherBaseChangeMapAb_cube (f.app j) (g.app j) (h.app j) (e.app j) (w j) (f.app i)
      (g.app i) (h.app i) (e.app i) (w i) (DX.map a) (DS.map a) (DT.map a) (DY.map a)
      (transition_comm g a) (transition_comm h a) _ rfl (f.naturality a).symm _ (e.naturality a)
      rfl q (F.obj j))
    (map_inverseImageSystem_map h e q F a) (transitionMap_inverseImageSystem_eq h e q F a)

variable {cX : Cone DX} {cS : Cone DS} {cT : Cone DT} {cY : Cone DY} (hcS : IsLimit cS)
  (hcX : IsLimit cX) (fL : cX.pt ⟶ cS.pt) (eL : cY.pt ⟶ cT.pt)
  (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i)
  (heL : ∀ i : Iᵒᵖ, eL ≫ cT.π.app i = cY.π.app i ≫ e.app i)

/-- The inverse image along `f` of the cocone map `ψ_i` for `g`, split into its two factors. -/
private theorem map_projectionMap_eq (𝓕 : Sheaf (smallEtaleTopology cT.pt) Ab.{u + 1})
    (F : EtaleSheafSystem DT Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cT.π.app i)).obj (F.obj i) ⟶ 𝓕) (i : Iᵒᵖ) :
    (smallEtalePullbackAb fL).map (projectionMap g cT cS hcS q 𝓕 F ι i) =
      (smallEtalePullbackAb fL).map
          ((higherBaseChangeMapAb (cS.π.app i) (g.app i) (limitMorphism g cT cS hcS) (cT.π.app i)
            (limitMorphism_comp_π g cT cS hcS i) q).app (F.obj i)) ≫
        (smallEtalePullbackAb fL).map
          (((smallEtalePushforwardAb (limitMorphism g cT cS hcS)).rightDerived q).map (ι i)) :=
  (smallEtalePullbackAb fL).map_comp _ _

/-- The naturality of the base change map of the limit square at a leg of the presentation. -/
private theorem higherBaseChangeMapAb_naturality_leg
    (wL : limitMorphism h cY cX hcX ≫ fL = eL ≫ limitMorphism g cT cS hcS)
    (𝓕 : Sheaf (smallEtaleTopology cT.pt) Ab.{u + 1}) (F : EtaleSheafSystem DT Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cT.π.app i)).obj (F.obj i) ⟶ 𝓕) (i : Iᵒᵖ) :
    (smallEtalePullbackAb fL).map
          (((smallEtalePushforwardAb (limitMorphism g cT cS hcS)).rightDerived q).map (ι i)) ≫
        (higherBaseChangeMapAb fL (limitMorphism g cT cS hcS) (limitMorphism h cY cX hcX) eL wL
          q).app 𝓕 =
      (higherBaseChangeMapAb fL (limitMorphism g cT cS hcS) (limitMorphism h cY cX hcX) eL wL
          q).app ((smallEtalePullbackAb (cT.π.app i)).obj (F.obj i)) ≫
        ((smallEtalePushforwardAb (limitMorphism h cY cX hcX)).rightDerived q).map
          ((smallEtalePullbackAb eL).map (ι i)) :=
  (higherBaseChangeMapAb fL (limitMorphism g cT cS hcS) (limitMorphism h cY cX hcX) eL wL
    q).naturality (ι i)

/-- The image under `R^q h_*` of a leg of the inverse image of the presentation, split into the
comparison and the inverse image of the leg. -/
private theorem map_inverseImageSystemLeg (𝓕 : Sheaf (smallEtaleTopology cT.pt) Ab.{u + 1})
    (F : EtaleSheafSystem DT Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cT.π.app i)).obj (F.obj i) ⟶ 𝓕) (i : Iᵒᵖ) :
    ((smallEtalePushforwardAb (limitMorphism h cY cX hcX)).rightDerived q).map
        (((smallEtalePullbackAbSquareIso (X' := cY.pt) (cY.π.app i) eL (e.app i) (cT.π.app i)
          (cY.π.app i ≫ e.app i) rfl (heL i).symm).app (F.obj i)).hom) ≫
        ((smallEtalePushforwardAb (limitMorphism h cY cX hcX)).rightDerived q).map
          ((smallEtalePullbackAb eL).map (ι i)) =
      ((smallEtalePushforwardAb (limitMorphism h cY cX hcX)).rightDerived q).map
        (inverseImageSystemLeg e eL heL 𝓕 F ι i) :=
  (((smallEtalePushforwardAb (limitMorphism h cY cX hcX)).rightDerived q).map_comp _ _).symm.trans
    (congrArg ((smallEtalePushforwardAb (limitMorphism h cY cX hcX)).rightDerived q).map
      (inverseImageSystemLeg_eq e eL heL 𝓕 F ι i).symm)

/-- The cocone map `ψ_i` for `h` with the inverse image of the presentation, split into its two
factors. -/
private theorem projectionMap_inverseImageSystem_eq
    (𝓕 : Sheaf (smallEtaleTopology cT.pt) Ab.{u + 1}) (F : EtaleSheafSystem DT Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cT.π.app i)).obj (F.obj i) ⟶ 𝓕) (i : Iᵒᵖ) :
    projectionMap h cY cX hcX q ((smallEtalePullbackAb eL).obj 𝓕) (inverseImageSystem e F)
        (inverseImageSystemLeg e eL heL 𝓕 F ι) i =
      (higherBaseChangeMapAb (cX.π.app i) (h.app i) (limitMorphism h cY cX hcX) (cY.π.app i)
          (limitMorphism_comp_π h cY cX hcX i) q).app
          ((smallEtalePullbackAb (e.app i)).obj (F.obj i)) ≫
        ((smallEtalePushforwardAb (limitMorphism h cY cX hcX)).rightDerived q).map
          (inverseImageSystemLeg e eL heL 𝓕 F ι i) :=
  rfl

/-- **The base change map of the limit square commutes with the cocone maps** `ψ_i` of
[Stacks, Tag 0EYM], for `g` with the system `ℱ_i` and for `h` with the system `e_i^{-1}ℱ_i`, up to
the comparison of the inverse images along `f ≫ s_i = r_i ≫ f_i`: the cube with the projection
squares as vertical faces. -/
theorem projectionMap_comp_higherBaseChangeMapAb
    (wL : limitMorphism h cY cX hcX ≫ fL = eL ≫ limitMorphism g cT cS hcS)
    (𝓕 : Sheaf (smallEtaleTopology cT.pt) Ab.{u + 1}) (F : EtaleSheafSystem DT Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cT.π.app i)).obj (F.obj i) ⟶ 𝓕) (i : Iᵒᵖ) :
    (smallEtalePullbackAb fL).map (projectionMap g cT cS hcS q 𝓕 F ι i) ≫
        (higherBaseChangeMapAb fL (limitMorphism g cT cS hcS) (limitMorphism h cY cX hcX) eL wL
          q).app 𝓕 =
      ((smallEtalePullbackAbSquareIso (X' := cX.pt) fL (cX.π.app i) (cS.π.app i) (f.app i)
          (fL ≫ cS.π.app i) rfl (hfL i)).app
          (((smallEtalePushforwardAb (g.app i)).rightDerived q).obj (F.obj i))).hom ≫
        (smallEtalePullbackAb (cX.π.app i)).map
          ((higherBaseChangeMapAb (f.app i) (g.app i) (h.app i) (e.app i) (w i) q).app (F.obj i)) ≫
        projectionMap h cY cX hcX q ((smallEtalePullbackAb eL).obj 𝓕) (inverseImageSystem e F)
          (inverseImageSystemLeg e eL heL 𝓕 F ι) i :=
  cubeLeg_algebra (map_projectionMap_eq g q hcS fL 𝓕 F ι i)
    (higherBaseChangeMapAb_naturality_leg g h q hcS hcX fL eL wL 𝓕 F ι i)
    (higherBaseChangeMapAb_cube (X₁ := cX.pt) (S₁ := cS.pt) (T₁ := cT.pt) (Y₁ := cY.pt)
      (f.app i) (g.app i) (h.app i) (e.app i) (w i) fL (limitMorphism g cT cS hcS)
      (limitMorphism h cY cX hcX) eL wL (cX.π.app i) (cS.π.app i) (cT.π.app i) (cY.π.app i)
      (limitMorphism_comp_π g cT cS hcS i) (limitMorphism_comp_π h cY cX hcX i) _ rfl (hfL i) _
      (heL i).symm rfl q (F.obj i))
    (map_inverseImageSystemLeg h e q hcX eL heL 𝓕 F ι i)
    (projectionMap_inverseImageSystem_eq h e q hcX eL heL 𝓕 F ι i)

end LimitBaseChange

end Stacks.EtaleCohomology

end
