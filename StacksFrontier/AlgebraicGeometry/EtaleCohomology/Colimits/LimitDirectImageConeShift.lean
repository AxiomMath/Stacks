module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitDirectImageSystem

/-!
# Shifting the maps of Stacks 0EYM in degree zero to an earlier level

Let `(X_i, f_{i'i})` be an inverse system of schemes with a cone `f_i : X ⟶ X_i`, and let
`x_i : G_i ⟶ f_{i, *}Y` be maps out of sheaves `G_i` with transposed transition maps
`t_{i'i} : G_i ⟶ f_{i'i, *}G_{i'}`, compatible with them. Pushing such a map at a later level `i'`
forward along a transition `f_{i'i}` and composing with the comparison
`f_{i'i, *}f_{i', *} ≅ f_{i, *}` gives a map `f_{i'i, *}G_{i'} ⟶ f_{i, *}Y` *at the earlier level*
`i`. This file records how these shifted maps behave:

* `Stacks.EtaleCohomology.LimitDirectImage.shiftTransition_comp_shiftLeg` — for `i'' ≥ i' ≥ i` the
  shifted maps from `i'` and from `i''` are compatible with the shifted transition maps, so that at
  the level `i` they form a cocone over the system `i' ↦ f_{i'i, *}G_{i'}` indexed by the `i' ≥ i`;
* `Stacks.EtaleCohomology.LimitDirectImage.shiftLeg_cancel` — an identity at `i'` between shifted
  maps persists, read through the comparisons, at any earlier level;
* `Stacks.EtaleCohomology.LimitDirectImage.shiftTransition_transitionSquareIso` — for a morphism
  `g_i : X_i ⟶ S_i` of inverse systems, `g_{i, *}` of a shifted transition map of `(F_i)` is the
  shifted transition map of the direct images `(g_{i, *}F_i)` with the transposed transition maps
  `Stacks.EtaleCohomology.LimitDirectImage.directTransition` of
  `Stacks.EtaleCohomology.LimitDirectImage.transitionSystem`, read through the square
  identifications;
* `Stacks.EtaleCohomology.LimitDirectImage.projectionTranspose_compat` and
  `Stacks.EtaleCohomology.LimitDirectImage.shiftLeg_projectionSquareIso` — the same for the maps
  `g_{i, *}x_i` followed by the identification of the projection square.

All four are the associativity pentagon of the comparisons of direct images, together with the
pasting laws `Stacks.EtaleCohomology.LimitDirectImage.transitionSquareIso_paste_app` and
`Stacks.EtaleCohomology.LimitDirectImage.projectionSquareIso_paste_app`. They are the formal half
of the degree-zero case of [Stacks, Tag 0EYM]: the source computes `g_* 𝓕` over an étale
`S_i`-scheme as a colimit over the levels `i' ≥ i`, and these identities are what make the maps of
that colimit, and the maps a candidate factorisation has to match, into cocones over the same
system.

The composite transition is carried as a morphism `ab` of the index category with an equation
`ab = b ≫ a`, so that the statements apply at the transitions to a fixed base level of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.GeIndex` without a transport.

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe w' w v u

namespace Stacks.EtaleCohomology.LimitDirectImage

section Shift

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} (A : Type w) [Category.{w'} A]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint] (c : Cone D)

omit [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint] in
/-- **The associativity pentagon at the projections of a cone**: the comparison
`f_{j, *} ≅ f_{kj, *} f_{k, *} ≅ f_{kj, *} f_{lk, *} f_{l, *}` agrees with the comparison through
the composite transition. -/
theorem coneProjectionComp_pentagon {l k j : Iᵒᵖ} (b : l ⟶ k) (a : k ⟶ j)
    (Y : Sheaf (smallEtaleTopology c.pt) A) :
    (systemPushforward D A a).map ((coneProjectionComp A c b).hom.app Y) ≫
        (coneProjectionComp A c a).hom.app Y =
      (smallEtalePushforwardComp' (D.map b) (D.map a) (D.map (b ≫ a)) (D.map_comp b a)
          A).hom.app ((smallEtalePushforward (c.π.app l) A).obj Y) ≫
        (coneProjectionComp A c (b ≫ a)).hom.app Y :=
  smallEtalePushforwardComp'_assoc_app (c.π.app l) (D.map b) (D.map a) (c.π.app k) (c.w b).symm
    (D.map (b ≫ a)) (D.map_comp b a) (c.π.app j) (c.w a).symm (c.w (b ≫ a)).symm A Y

/-- **The shifted transition map** `f_{kj, *}G_k ⟶ f_{lj, *}G_l` of a family of sheaves with
transposed transition maps `t_b : G_k ⟶ f_{lk, *}G_l`, for `l ⟶ k ⟶ j`: the direct image of the
transposed transition map, read through the comparison of the direct images along the composite
transition. For a system of sheaves `t` is
`Stacks.EtaleCohomology.EtaleSheafSystem.mapTranspose`. -/
def shiftTransition {G : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) A}
    (t : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), G j ⟶ (systemPushforward D A a).obj (G i)) {l k j : Iᵒᵖ}
    (b : l ⟶ k) (a : k ⟶ j) (ab : l ⟶ j) (hab : ab = b ≫ a) :
    (systemPushforward D A a).obj (G k) ⟶ (systemPushforward D A ab).obj (G l) :=
  (systemPushforward D A a).map (t b) ≫
    (smallEtalePushforwardComp' (D.map b) (D.map a) (D.map ab) (by rw [hab, D.map_comp])
      A).hom.app (G l)

variable {A c}

/-- **The shifted map** `f_{kj, *}G_k ⟶ f_{j, *}Y` of a family `x_k : G_k ⟶ f_{k, *}Y`: its direct
image along the transition, followed by the comparison `f_{kj, *}f_{k, *} ≅ f_{j, *}`. -/
def shiftLeg {G : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) A}
    {Y : Sheaf (smallEtaleTopology c.pt) A}
    (x : ∀ i : Iᵒᵖ, G i ⟶ (smallEtalePushforward (c.π.app i) A).obj Y) {k j : Iᵒᵖ}
    (a : k ⟶ j) :
    (systemPushforward D A a).obj (G k) ⟶ (smallEtalePushforward (c.π.app j) A).obj Y :=
  (systemPushforward D A a).map (x k) ≫ (coneProjectionComp A c a).hom.app Y

omit [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint] in
/-- **The shifted maps of a compatible family form a cocone over the shifted transition maps.**
If `x_k = f_{lk, *}x_l ∘ φ^t_{lk}` read through the comparisons, for all `l ⟶ k`, then for
`l ⟶ k ⟶ j` the shifted map from `l` composed with the shifted transition map is the shifted map
from `k`. -/
theorem shiftTransition_comp_shiftLeg {G : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) A}
    (t : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), G j ⟶ (systemPushforward D A a).obj (G i))
    {Y : Sheaf (smallEtaleTopology c.pt) A}
    (x : ∀ i : Iᵒᵖ, G i ⟶ (smallEtalePushforward (c.π.app i) A).obj Y)
    (hx : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      x j = t a ≫ (systemPushforward D A a).map (x i) ≫ (coneProjectionComp A c a).hom.app Y)
    {l k j : Iᵒᵖ} (b : l ⟶ k) (a : k ⟶ j) (ab : l ⟶ j) (hab : ab = b ≫ a) :
    shiftTransition A t b a ab hab ≫ shiftLeg (c := c) x ab = shiftLeg (c := c) x a := by
  subst hab
  have hnat := (smallEtalePushforwardComp' (D.map b) (D.map a) (D.map (b ≫ a))
    (by rw [D.map_comp]) A).hom.naturality (x l)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  have hP := coneProjectionComp_pentagon A c b a Y
  simp only [shiftTransition, shiftLeg, Category.assoc]
  rw [hx b]
  simp only [Functor.map_comp, Category.assoc]
  rw [hP, reassoc_of% hnat]

omit [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint] in
/-- **An identity between shifted maps persists at an earlier level.** If two maps
`x : Z ⟶ f_{l, *}Y` and `y : Z ⟶ f_{l, *}Y'` satisfy `x' ≫ ρ = y'` after shifting along
`b : l ⟶ k`, then after shifting along the composite `l ⟶ j` they satisfy the same identity with
`ρ` replaced by its direct image along `a : k ⟶ j`, read through the comparisons. -/
theorem shiftLeg_cancel {l k j : Iᵒᵖ} (b : l ⟶ k) (a : k ⟶ j) (ab : l ⟶ j) (hab : ab = b ≫ a)
    {Y Y' : Sheaf (smallEtaleTopology c.pt) A} {Z : Sheaf (smallEtaleTopology (D.obj l)) A}
    (x : Z ⟶ (smallEtalePushforward (c.π.app l) A).obj Y)
    (y : Z ⟶ (smallEtalePushforward (c.π.app l) A).obj Y')
    (ρ : (smallEtalePushforward (c.π.app k) A).obj Y ⟶ (smallEtalePushforward (c.π.app k) A).obj Y')
    (h : (systemPushforward D A b).map x ≫ (coneProjectionComp A c b).hom.app Y ≫ ρ =
      (systemPushforward D A b).map y ≫ (coneProjectionComp A c b).hom.app Y') :
    (systemPushforward D A ab).map x ≫ (coneProjectionComp A c ab).hom.app Y ≫
        (coneProjectionComp A c a).inv.app Y ≫ (systemPushforward D A a).map ρ ≫
          (coneProjectionComp A c a).hom.app Y' =
      (systemPushforward D A ab).map y ≫ (coneProjectionComp A c ab).hom.app Y' := by
  subst hab
  have e : ∀ Z : Sheaf (smallEtaleTopology c.pt) A,
      (coneProjectionComp A c (b ≫ a)).hom.app Z =
        (smallEtalePushforwardComp' (D.map b) (D.map a) (D.map (b ≫ a)) (D.map_comp b a)
            A).inv.app ((smallEtalePushforward (c.π.app l) A).obj Z) ≫
          (systemPushforward D A a).map ((coneProjectionComp A c b).hom.app Z) ≫
            (coneProjectionComp A c a).hom.app Z := fun Z => by
    rw [← cancel_epi ((smallEtalePushforwardComp' (D.map b) (D.map a) (D.map (b ≫ a))
      (D.map_comp b a) A).hom.app ((smallEtalePushforward (c.π.app l) A).obj Z)),
      Iso.hom_inv_id_app_assoc]
    exact (coneProjectionComp_pentagon A c b a Z).symm
  have hn := fun {Z W : Sheaf (smallEtaleTopology (D.obj l)) A} (f : Z ⟶ W) =>
    (smallEtalePushforwardComp' (D.map b) (D.map a) (D.map (b ≫ a)) (D.map_comp b a)
      A).inv.naturality f
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [e Y, e Y']
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% hn x, reassoc_of% hn y]
  simp only [← Functor.map_comp_assoc]
  rw [h]

end Shift

section Interchange

variable {I : Type v} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS)
  (A : Type w) [Category.{w'} A]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward DX A a).IsRightAdjoint]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward DS A a).IsRightAdjoint]

/-- **The transition maps of the direct images, transposed**: `g_{i, *}` of the transposed
transition map of the system followed by the square identification of the transition. This is the
transpose of `Stacks.EtaleCohomology.LimitDirectImage.transitionMap`
(`Stacks.EtaleCohomology.LimitDirectImage.transitionMap_transpose`), written out so that it is a
map between the direct images themselves. -/
def directTransition (F : EtaleSheafSystem DX A) {i j : Iᵒᵖ} (a : i ⟶ j) :
    directImage γ A F j ⟶ (systemPushforward DS A a).obj (directImage γ A F i) :=
  (smallEtalePushforward (γ.app j) A).map (F.mapTranspose a) ≫
    (transitionSquareIso γ A a).hom.app (F.obj i)

/-- `Stacks.EtaleCohomology.LimitDirectImage.directTransition` is the transpose of the transition
map of `Stacks.EtaleCohomology.LimitDirectImage.transitionSystem`. -/
theorem directTransition_eq (F : EtaleSheafSystem DX A) {i j : Iᵒᵖ} (a : i ⟶ j) :
    directTransition γ A F a = (systemAdjunction DS A a).homEquiv _ _ (transitionMap γ A F a) :=
  (transitionMap_transpose γ A F a).symm

omit [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward DS A a).IsRightAdjoint] in
/-- **The direct image of a shifted transition map is the shifted transition map of the direct
images**, read through the square identifications of the transitions. -/
theorem shiftTransition_transitionSquareIso (F : EtaleSheafSystem DX A) {l k j : Iᵒᵖ}
    (b : l ⟶ k) (a : k ⟶ j) (ab : l ⟶ j) (hab : ab = b ≫ a) :
    (smallEtalePushforward (γ.app j) A).map (shiftTransition A F.mapTranspose b a ab hab) ≫
        (transitionSquareIso γ A ab).hom.app (F.obj l) =
      (transitionSquareIso γ A a).hom.app (F.obj k) ≫
        shiftTransition A (directTransition γ A F) b a ab hab := by
  subst hab
  have hnat := (transitionSquareIso γ A a).hom.naturality (F.mapTranspose b)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  have hp := transitionSquareIso_paste_app γ A b a (F.obj l)
  simp only [shiftTransition, directTransition, Functor.map_comp, Category.assoc]
  rw [hp, reassoc_of% hnat]

variable (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS)
  [∀ i : Iᵒᵖ, (smallEtalePushforward (cX.π.app i) A).IsRightAdjoint]
  [∀ i : Iᵒᵖ, (smallEtalePushforward (cS.π.app i) A).IsRightAdjoint]
  {𝓕 : Sheaf (smallEtaleTopology cX.pt) A} (F : EtaleSheafSystem DX A)
  (x : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforward (cX.π.app i) A).obj 𝓕)

/-- **The cocone maps of Stacks 0EYM in degree zero, transposed**:
`g_{i, *}x_i : g_{i, *}F_i ⟶ g_{i, *}f_{i, *}𝓕` followed by the identification
`g_{i, *}f_{i, *} ≅ h_{i, *}g_*` of the projection square. For `x_i` the transpose of a
presentation map `ι_i` this is the transpose of
`Stacks.EtaleCohomology.LimitDirectImage.projectionMap`. -/
def projectionTranspose (i : Iᵒᵖ) :
    directImage γ A F i ⟶ (smallEtalePushforward (cS.π.app i) A).obj
      ((smallEtalePushforward (LimitHigherDirectImage.limitMorphism γ cX cS hcS) A).obj 𝓕) :=
  (smallEtalePushforward (γ.app i) A).map (x i) ≫
    (projectionSquareIso γ A cX cS hcS i).hom.app 𝓕

omit [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward DS A a).IsRightAdjoint]
  [∀ i : Iᵒᵖ, (smallEtalePushforward (cX.π.app i) A).IsRightAdjoint]
  [∀ i : Iᵒᵖ, (smallEtalePushforward (cS.π.app i) A).IsRightAdjoint] in
/-- **The transposed cocone maps are compatible with the transition maps of the direct images**,
whenever the `x_i` are compatible with those of the system. -/
theorem projectionTranspose_compat
    (hx : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      x j = F.mapTranspose a ≫ (systemPushforward DX A a).map (x i) ≫
        (coneProjectionComp A cX a).hom.app 𝓕)
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    projectionTranspose γ A cX cS hcS F x j =
      directTransition γ A F a ≫
        (systemPushforward DS A a).map (projectionTranspose γ A cX cS hcS F x i) ≫
          (coneProjectionComp A cS a).hom.app
            ((smallEtalePushforward (LimitHigherDirectImage.limitMorphism γ cX cS hcS) A).obj
              𝓕) := by
  have hnat := (transitionSquareIso γ A a).hom.naturality (x i)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  simp only [projectionTranspose, directTransition, Functor.map_comp, Category.assoc]
  rw [hx a]
  simp only [Functor.map_comp, Category.assoc]
  rw [projectionSquareIso_paste_app γ A cX cS hcS a 𝓕, reassoc_of% hnat]

omit [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward DS A a).IsRightAdjoint]
  [∀ i : Iᵒᵖ, (smallEtalePushforward (cX.π.app i) A).IsRightAdjoint]
  [∀ i : Iᵒᵖ, (smallEtalePushforward (cS.π.app i) A).IsRightAdjoint] in
/-- **The direct image of a shifted map, against the shifted transposed cocone map.** For
`a : k ⟶ j`, `g_{j, *}` of the shifted map `f_{kj, *}F_k ⟶ f_{j, *}𝓕` followed by the
identification of the projection square at `j` is the square identification of the transition
followed by the shifted map of the transposed cocone maps. -/
theorem shiftLeg_projectionSquareIso {k j : Iᵒᵖ} (a : k ⟶ j) :
    (smallEtalePushforward (γ.app j) A).map (shiftLeg (c := cX) x a) ≫
        (projectionSquareIso γ A cX cS hcS j).hom.app 𝓕 =
      (transitionSquareIso γ A a).hom.app (F.obj k) ≫
        shiftLeg (c := cS) (projectionTranspose γ A cX cS hcS F x) a := by
  have hnat := (transitionSquareIso γ A a).hom.naturality (x k)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  simp only [shiftLeg, projectionTranspose, Functor.map_comp, Category.assoc]
  rw [projectionSquareIso_paste_app γ A cX cS hcS a 𝓕, reassoc_of% hnat]

end Interchange

end Stacks.EtaleCohomology.LimitDirectImage

end
