module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitBaseChangeSetCube

/-!
# The inverse image of a presented system of sheaves of sets

Let `e : (Y_i) ⟶ (T_i)` be a morphism of inverse systems of schemes, `e : Y ⟶ T` the limit morphism
between the vertices of a cone over `(Y_i)` and a limit cone over `(T_i)`, and let `(F_i)` be a
system of sheaves of sets on the `T_i` with `𝓕 = colim p_i^{-1}F_i` on `T`. The proof of [Stacks,
Tag 0EZT] uses that `e^{-1}𝓕 = colim q_i^{-1}e_i^{-1}F_i`. This file constructs the system
`(e_i^{-1}F_i)` on the `Y_i` (`Stacks.EtaleCohomology.LimitSetBaseChange.inverseImageSystem`) and
proves that `e^{-1}𝓕` presents its colimit, in adjoint form
(`Stacks.EtaleCohomology.LimitSetBaseChange.isDirPresentation_inverseImageSystem`). Everything is
read through the adjunctions, so only direct images and the units of the adjunctions
`e_i^{-1} ⊣ e_{i, *}` and `e^{-1} ⊣ e_*` occur.

## Main definitions

* `Stacks.EtaleCohomology.LimitSetBaseChange.inverseImageSystem` — the system `(e_i^{-1}F_i)`.
* `Stacks.EtaleCohomology.LimitSetBaseChange.inverseImageLeg` — its legs to `q_{i, *}e^{-1}𝓕`.

## Main results

* `Stacks.EtaleCohomology.LimitSetBaseChange.isDirPresentation_inverseImageSystem` —
  `e^{-1}𝓕 = colim q_i^{-1}e_i^{-1}F_i`.

## References

* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology.LimitDirectImage Stacks.EtaleCohomology.SetLinearization

universe v u

namespace Stacks.EtaleCohomology.LimitSetBaseChange

/-- The adjunction `f^{-1} ⊣ f_*` on sheaves of sets of the small étale sites, with the direct
image spelled `Stacks.EtaleCohomology.smallEtalePushforward`. -/
abbrev setAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleInverseImage.{u, 0} f ⊣ smallEtalePushforward f (Type (u + 1)) :=
  smallEtaleInverseImageAdjunction.{u, 0} f

/-- **Inverting a pasting square**, in an arbitrary category: if `X ≫ P = Q ≫ R ≫ C` with
`P`, `Q`, `R` invertible, then `R⁻¹ ≫ Q⁻¹ ≫ X = C ≫ P⁻¹`. -/
theorem paste_inv {𝒜 : Type*} [Category* 𝒜] {O₀ O₁ O₂ O₃ O₅ : 𝒜}
    {X : O₀ ⟶ O₁} {P : O₁ ⟶ O₅} {P' : O₅ ⟶ O₁} {Q : O₀ ⟶ O₂} {Q' : O₂ ⟶ O₀}
    {R : O₂ ⟶ O₃} {R' : O₃ ⟶ O₂} {C : O₃ ⟶ O₅}
    (h : X ≫ P = Q ≫ R ≫ C) (hP : P ≫ P' = 𝟙 _) (hQ : Q' ≫ Q = 𝟙 _) (hR : R' ≫ R = 𝟙 _) :
    R' ≫ Q' ≫ X = C ≫ P' := by
  calc R' ≫ Q' ≫ X = R' ≫ Q' ≫ X ≫ P ≫ P' := by rw [hP, Category.comp_id]
    _ = R' ≫ (Q' ≫ Q) ≫ R ≫ C ≫ P' := by rw [← Category.assoc X, h]; simp only [Category.assoc]
    _ = C ≫ P' := by rw [hQ, Category.id_comp, ← Category.assoc, hR, Category.id_comp]

/-- In an arbitrary category, if `m = mb ≫ tma ≫ cTF` and the four given squares commute, then
`m ≫ tabη ≫ sabinv = (mb ≫ tbη ≫ sbinv) ≫ ekTinv ≫ ekCY`. -/
theorem transpose_algebra {𝒜 : Type*} [Category* 𝒜]
    {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ : 𝒜}
    {m : O₀ ⟶ O₇} {mb : O₀ ⟶ O₁} {tma : O₁ ⟶ O₆} {cTF : O₆ ⟶ O₇} {tabη : O₇ ⟶ O₈}
    {sabinv : O₈ ⟶ O₅} {tbη : O₁ ⟶ O₂} {sbinv : O₂ ⟶ O₃} {ekTinv : O₃ ⟶ O₄} {ekCY : O₄ ⟶ O₅}
    {tbEinv : O₂ ⟶ O₉} {sbinv' : O₉ ⟶ O₄} {tbtaη : O₆ ⟶ O₁₀} {tbsainv : O₁₀ ⟶ O₉}
    {cTG : O₁₀ ⟶ O₈}
    (hL : m = mb ≫ tma ≫ cTF) (n₁ : sbinv ≫ ekTinv = tbEinv ≫ sbinv')
    (e₂ : tbη ≫ tbEinv = tma ≫ tbtaη ≫ tbsainv)
    (p : tbsainv ≫ sbinv' ≫ ekCY = cTG ≫ sabinv) (n₃ : tbtaη ≫ cTG = cTF ≫ tabη) :
    m ≫ tabη ≫ sabinv = (mb ≫ tbη ≫ sbinv) ≫ ekTinv ≫ ekCY := by
  rw [hL]
  simp only [Category.assoc]
  rw [reassoc_of% n₁, reassoc_of% e₂, p, reassoc_of% n₃]

/-- In an arbitrary category, if `sj = hj ≫ psj`, `hj = (mb ≫ tη ≫ sinv) ≫ ekT ≫ ekCY`, the
given squares commute and `sq` is a right inverse of `sinv'`, then `sj = mb ≫ tσ ≫ cT`. -/
theorem compat_algebra {𝒜 : Type*} [Category* 𝒜]
    {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ : 𝒜}
    {sj : O₀ ⟶ O₆} {hj : O₀ ⟶ O₅} {psj : O₅ ⟶ O₆} {mb : O₀ ⟶ O₁} {tη : O₁ ⟶ O₂}
    {sinv : O₂ ⟶ O₃} {ekT : O₃ ⟶ O₄} {ekCY : O₄ ⟶ O₅} {tE : O₂ ⟶ O₇} {sinv' : O₇ ⟶ O₄}
    {sq : O₄ ⟶ O₇} {tPS : O₇ ⟶ O₈} {cT : O₈ ⟶ O₆} {tσ : O₁ ⟶ O₈} {tH : O₁ ⟶ O₇}
    (hs : sj = hj ≫ psj) (hh : hj = (mb ≫ tη ≫ sinv) ≫ ekT ≫ ekCY)
    (n₁ : sinv ≫ ekT = tE ≫ sinv') (e₂ : tη ≫ tE = tH)
    (p : ekCY ≫ psj = sq ≫ tPS ≫ cT) (hinv : sinv' ≫ sq = 𝟙 _) (hσ : tH ≫ tPS = tσ) :
    sj = mb ≫ tσ ≫ cT := by
  rw [hs, hh]
  simp only [Category.assoc]
  rw [p, reassoc_of% n₁, reassoc_of% hinv, reassoc_of% e₂, reassoc_of% hσ]

/-- In an arbitrary category, if `m = x ≫ pη ≫ psN`, `psN ≫ eψ = pψ ≫ psK`, `pη ≫ pψ = pH` and
`r = m ≫ eψ`, then `r = x ≫ pH ≫ psK`. -/
theorem leg_algebra {𝒜 : Type*} [Category* 𝒜] {O₀ O₁ O₂ O₃ O₄ O₅ : 𝒜}
    {m : O₀ ⟶ O₂} {x : O₀ ⟶ O₁} {pη : O₁ ⟶ O₃} {psN : O₃ ⟶ O₂} {eψ : O₂ ⟶ O₄}
    {pψ : O₃ ⟶ O₅} {psK : O₅ ⟶ O₄} {pH : O₁ ⟶ O₅} {r : O₀ ⟶ O₄}
    (hm : m = x ≫ pη ≫ psN) (hn : psN ≫ eψ = pψ ≫ psK) (hH : pη ≫ pψ = pH)
    (hr : r = m ≫ eψ) : r = x ≫ pH ≫ psK := by
  rw [hr, hm]
  simp only [Category.assoc]
  rw [hn, ← Category.assoc pη, hH]

/-- If the transpose of `ℓ` is `u ≫ v ≫ w`, then `Φ` of the unit followed by `R ℓ` is
`Φ u ≫ Φ v ≫ Φ w`. -/
private theorem map_unit_comp_map_eq {𝒞 𝒟 ℰ : Type*} [Category* 𝒞] [Category* 𝒟] [Category* ℰ]
    {L : 𝒞 ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} (adj : L ⊣ R) (Φ : 𝒞 ⥤ ℰ) {X : 𝒞} {Y : 𝒟} {ℓ : L.obj X ⟶ Y}
    {A B : 𝒞} {u : X ⟶ A} {v : A ⟶ B} {w : B ⟶ R.obj Y} (h : adj.homEquiv _ _ ℓ = u ≫ v ≫ w) :
    Φ.map (adj.unit.app X) ≫ Φ.map (R.map ℓ) = Φ.map u ≫ Φ.map v ≫ Φ.map w := by
  rw [← Φ.map_comp, ← Φ.map_comp, ← Φ.map_comp, ← h, Adjunction.homEquiv_unit]

/-! ### The inverse image system -/

section System

variable {I : Type v} [Preorder I] {DY DT : Iᵒᵖ ⥤ Scheme.{u}} (e : DY ⟶ DT)
  (F : EtaleSheafSystem DT (Type (u + 1)))

/-- The sheaf `e_i^{-1}F_i` of the inverse image system. -/
abbrev inverseImageObj (i : Iᵒᵖ) : Sheaf (smallEtaleTopology (DY.obj i)) (Type (u + 1)) :=
  (smallEtaleInverseImage.{u, 0} (e.app i)).obj (F.obj i)

/-- The transposed transition map of the inverse image system: the transpose under
`e_j^{-1} ⊣ e_{j, *}` of the transposed transition map of `F`, followed by the direct image of the
unit and the identification of the transition square. -/
def inverseImageTransition {i j : Iᵒᵖ} (a : i ⟶ j) :
    inverseImageObj e F j ⟶
      (systemPushforward DY (Type (u + 1)) a).obj (inverseImageObj e F i) :=
  ((setAdj (e.app j)).homEquiv _ _).symm
    (F.mapTranspose a ≫ (systemPushforward DT (Type (u + 1)) a).map
        ((setAdj (e.app i)).unit.app (F.obj i)) ≫
      (transitionSquareIso e (Type (u + 1)) a).inv.app (inverseImageObj e F i))

/-- The transpose under `e_j^{-1} ⊣ e_{j, *}` of the transition map
`Stacks.EtaleCohomology.LimitSetBaseChange.inverseImageTransition` is the transposed transition
map of `F`, followed by the direct image of the unit and the identification of the transition
square. -/
theorem homEquiv_inverseImageTransition {i j : Iᵒᵖ} (a : i ⟶ j) :
    (setAdj (e.app j)).homEquiv _ _ (inverseImageTransition e F a) =
      F.mapTranspose a ≫ (systemPushforward DT (Type (u + 1)) a).map
          ((setAdj (e.app i)).unit.app (F.obj i)) ≫
        (transitionSquareIso e (Type (u + 1)) a).inv.app (inverseImageObj e F i) :=
  Equiv.apply_symm_apply _ _

/-- The cocycle law of `Stacks.EtaleCohomology.LimitSetBaseChange.inverseImageTransition`. -/
theorem inverseImageTransition_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    inverseImageTransition e F (a ≫ b) = inverseImageTransition e F b ≫
      (systemPushforward DY (Type (u + 1)) b).map (inverseImageTransition e F a) ≫
        (smallEtalePushforwardComp' (DY.map a) (DY.map b) (DY.map (a ≫ b)) (DY.map_comp a b)
          (Type (u + 1))).hom.app (inverseImageObj e F i) := by
  apply ((setAdj (e.app k)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Functor.map_comp,
    homEquiv_inverseImageTransition, homEquiv_inverseImageTransition]
  have n₁ := (transitionSquareIso e (Type (u + 1)) b).inv.naturality
    (inverseImageTransition e F a)
  dsimp only [Functor.comp_map] at n₁
  have e₂ := map_unit_comp_map_eq (setAdj (e.app j)) (systemPushforward DT (Type (u + 1)) b)
    (homEquiv_inverseImageTransition e F a)
  have p := paste_inv (R' := (systemPushforward DT (Type (u + 1)) b).map
      ((transitionSquareIso e (Type (u + 1)) a).inv.app (inverseImageObj e F i)))
    (transitionSquareIso_paste_app e (Type (u + 1)) a b (inverseImageObj e F i))
    (Iso.hom_inv_id_app _ _)
    (Iso.inv_hom_id_app (transitionSquareIso e (Type (u + 1)) b)
      ((systemPushforward DY (Type (u + 1)) a).obj (inverseImageObj e F i)))
    (by rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id])
  have n₃ := (smallEtalePushforwardComp' (DT.map a) (DT.map b) (DT.map (a ≫ b)) (DT.map_comp a b)
    (Type (u + 1))).hom.naturality ((setAdj (e.app i)).unit.app (F.obj i))
  dsimp only [Functor.comp_map] at n₃
  exact transpose_algebra (F.mapTranspose_comp a b) n₁.symm e₂ p n₃

/-- **The inverse image system** `(e_i^{-1}F_i)` on the `Y_i`. -/
abbrev inverseImageSystem : EtaleSheafSystem DY (Type (u + 1)) :=
  EtaleSheafSystem.ofMapTranspose (inverseImageObj e F) (fun a => inverseImageTransition e F a)
    (fun a b => inverseImageTransition_comp e F a b)

/-- The transposed transition maps of the inverse image system are
`Stacks.EtaleCohomology.LimitSetBaseChange.inverseImageTransition`. -/
theorem inverseImageSystem_mapTranspose {i j : Iᵒᵖ} (a : i ⟶ j) :
    (inverseImageSystem e F).mapTranspose a = inverseImageTransition e F a :=
  EtaleSheafSystem.mapTranspose_ofMapTranspose _ _ _ a

end System

/-! ### The presentation of the inverse image -/

section Presentation

variable {I : Type v} [Preorder I] {DY DT : Iᵒᵖ ⥤ Scheme.{u}} (e : DY ⟶ DT)
  (F : EtaleSheafSystem DT (Type (u + 1))) (cY : Cone DY) (cT : Cone DT) (hcT : IsLimit cT)
  {𝓕 : Sheaf (smallEtaleTopology cT.pt) (Type (u + 1))}
  (x : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforward (cT.π.app i) (Type (u + 1))).obj 𝓕)

/-- The inverse image `e^{-1}𝓕` along the limit morphism. -/
abbrev inverseImageSheaf (𝓕 : Sheaf (smallEtaleTopology cT.pt) (Type (u + 1))) :
    Sheaf (smallEtaleTopology cY.pt) (Type (u + 1)) :=
  (smallEtaleInverseImage.{u, 0} (LimitHigherDirectImage.limitMorphism e cY cT hcT)).obj 𝓕

/-- **The legs** `e_i^{-1}F_i ⟶ q_{i, *}e^{-1}𝓕` of the inverse image system: the transposes of
`x_i` followed by the direct image of the unit `𝓕 ⟶ e_*e^{-1}𝓕` and the identification
`p_{i, *}e_* ≅ e_{i, *}q_{i, *}` of the projection square. -/
def inverseImageLeg (i : Iᵒᵖ) :
    inverseImageObj e F i ⟶
      (smallEtalePushforward (cY.π.app i) (Type (u + 1))).obj (inverseImageSheaf e cY cT hcT 𝓕) :=
  ((setAdj (e.app i)).homEquiv _ _).symm
    (x i ≫ (smallEtalePushforward (cT.π.app i) (Type (u + 1))).map
        ((setAdj (LimitHigherDirectImage.limitMorphism e cY cT hcT)).unit.app 𝓕) ≫
      (projectionSquareIso e (Type (u + 1)) cY cT hcT i).inv.app (inverseImageSheaf e cY cT hcT 𝓕))

/-- The transpose under `e_i^{-1} ⊣ e_{i, *}` of the leg
`Stacks.EtaleCohomology.LimitSetBaseChange.inverseImageLeg` is `x_i` followed by the direct image
of the unit `𝓕 ⟶ e_*e^{-1}𝓕` and the identification of the projection square. -/
theorem homEquiv_inverseImageLeg (i : Iᵒᵖ) :
    (setAdj (e.app i)).homEquiv _ _ (inverseImageLeg e F cY cT hcT x i) =
      x i ≫ (smallEtalePushforward (cT.π.app i) (Type (u + 1))).map
          ((setAdj (LimitHigherDirectImage.limitMorphism e cY cT hcT)).unit.app 𝓕) ≫
        (projectionSquareIso e (Type (u + 1)) cY cT hcT i).inv.app
          (inverseImageSheaf e cY cT hcT 𝓕) :=
  Equiv.apply_symm_apply _ _

/-- The transpose of a leg followed by the direct image of a map out of `e^{-1}𝓕`. -/
theorem homEquiv_inverseImageLeg_comp {𝒦 : Sheaf (smallEtaleTopology cY.pt) (Type (u + 1))}
    (ψ : inverseImageSheaf e cY cT hcT 𝓕 ⟶ 𝒦) (i : Iᵒᵖ) :
    (setAdj (e.app i)).homEquiv _ _
        (inverseImageLeg e F cY cT hcT x i ≫
          (smallEtalePushforward (cY.π.app i) (Type (u + 1))).map ψ) =
      x i ≫ (smallEtalePushforward (cT.π.app i) (Type (u + 1))).map
          ((setAdj (LimitHigherDirectImage.limitMorphism e cY cT hcT)).homEquiv _ _ ψ) ≫
        (projectionSquareIso e (Type (u + 1)) cY cT hcT i).inv.app 𝒦 := by
  have hn := (projectionSquareIso e (Type (u + 1)) cY cT hcT i).inv.naturality ψ
  dsimp only [Functor.comp_map] at hn
  refine leg_algebra (homEquiv_inverseImageLeg e F cY cT hcT x i) hn.symm ?_
    (Adjunction.homEquiv_naturality_right _ _ _)
  exact (Functor.map_comp _ _ _).symm.trans (congrArg _ (Adjunction.homEquiv_unit _ _ _ ψ).symm)

/-- **The legs of the inverse image system are compatible with its transition maps.** -/
theorem isDirCompatible_inverseImageLeg (hx : IsDirCompatible (Type (u + 1)) cT F 𝓕 x) :
    IsDirCompatible (Type (u + 1)) cY (inverseImageSystem e F) (inverseImageSheaf e cY cT hcT 𝓕)
      (inverseImageLeg e F cY cT hcT x) := by
  intro i j a
  rw [inverseImageSystem_mapTranspose]
  apply ((setAdj (e.app j)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Functor.map_comp, homEquiv_inverseImageTransition,
    homEquiv_inverseImageLeg]
  have n₁ := (transitionSquareIso e (Type (u + 1)) a).inv.naturality
    (inverseImageLeg e F cY cT hcT x i)
  dsimp only [Functor.comp_map] at n₁
  have e₂ := map_unit_comp_map_eq (setAdj (e.app i)) (systemPushforward DT (Type (u + 1)) a)
    (homEquiv_inverseImageLeg e F cY cT hcT x i)
  have p := paste_inv (R' := (systemPushforward DT (Type (u + 1)) a).map
      ((projectionSquareIso e (Type (u + 1)) cY cT hcT i).inv.app
        (inverseImageSheaf e cY cT hcT 𝓕)))
    (projectionSquareIso_paste_app e (Type (u + 1)) cY cT hcT a (inverseImageSheaf e cY cT hcT 𝓕))
    (Iso.hom_inv_id_app _ _)
    (Iso.inv_hom_id_app (transitionSquareIso e (Type (u + 1)) a)
      ((smallEtalePushforward (cY.π.app i) (Type (u + 1))).obj (inverseImageSheaf e cY cT hcT 𝓕)))
    (by rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id])
  have n₃ := (coneProjectionComp (Type (u + 1)) cT a).hom.naturality
    ((setAdj (LimitHigherDirectImage.limitMorphism e cY cT hcT)).unit.app 𝓕)
  dsimp only [Functor.comp_map] at n₃
  exact transpose_algebra (hx a) n₁.symm e₂ p n₃

/-- **`e^{-1}𝓕 = colim q_i^{-1}e_i^{-1}F_i`**, in adjoint form: if `𝓕` presents the colimit of
the system `(F_i)`, then `e^{-1}𝓕` presents the colimit of the inverse image system. -/
theorem isDirPresentation_inverseImageSystem
    (h : IsDirPresentation (Type (u + 1)) cT F 𝓕 x) :
    IsDirPresentation (Type (u + 1)) cY (inverseImageSystem e F) (inverseImageSheaf e cY cT hcT 𝓕)
      (inverseImageLeg e F cY cT hcT x) := by
  refine ⟨isDirCompatible_inverseImageLeg e F cY cT hcT x h.1, fun 𝒦 τ hτ => ?_⟩
  let σ : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforward (cT.π.app i) (Type (u + 1))).obj
      ((smallEtalePushforward (LimitHigherDirectImage.limitMorphism e cY cT hcT)
        (Type (u + 1))).obj 𝒦) := fun i =>
    (setAdj (e.app i)).homEquiv _ _ (τ i) ≫
      (projectionSquareIso e (Type (u + 1)) cY cT hcT i).hom.app 𝒦
  have hσ : IsDirCompatible (Type (u + 1)) cT F _ σ := by
    intro i j a
    have hτa := hτ a
    rw [inverseImageSystem_mapTranspose] at hτa
    have hh : (setAdj (e.app j)).homEquiv _ _ (τ j) =
        (F.mapTranspose a ≫ (systemPushforward DT (Type (u + 1)) a).map
            ((setAdj (e.app i)).unit.app (F.obj i)) ≫
          (transitionSquareIso e (Type (u + 1)) a).inv.app (inverseImageObj e F i)) ≫
        (smallEtalePushforward (e.app j) (Type (u + 1))).map
            ((systemPushforward DY (Type (u + 1)) a).map (τ i)) ≫
          (smallEtalePushforward (e.app j) (Type (u + 1))).map
            ((coneProjectionComp (Type (u + 1)) cY a).hom.app 𝒦) := by
      rw [hτa, Adjunction.homEquiv_naturality_right, Functor.map_comp,
        homEquiv_inverseImageTransition]
    have n₁ := (transitionSquareIso e (Type (u + 1)) a).inv.naturality (τ i)
    dsimp only [Functor.comp_map] at n₁
    exact compat_algebra rfl hh n₁.symm ((Functor.map_comp _ _ _).symm.trans
      (congrArg (systemPushforward DT (Type (u + 1)) a).map
        (Adjunction.homEquiv_unit (setAdj (e.app i)) _ _ (τ i)).symm))
      (projectionSquareIso_paste_app e (Type (u + 1)) cY cT hcT a 𝒦)
      (Iso.inv_hom_id_app (transitionSquareIso e (Type (u + 1)) a)
        ((smallEtalePushforward (cY.π.app i) (Type (u + 1))).obj 𝒦))
      (Functor.map_comp _ _ _).symm
  obtain ⟨χ', hχ', hu⟩ := h.2 _ σ hσ
  have key := homEquiv_inverseImageLeg_comp e F cY cT hcT x (𝒦 := 𝒦)
  refine ⟨((setAdj (LimitHigherDirectImage.limitMorphism e cY cT hcT)).homEquiv _ _).symm χ',
    fun i => ?_, fun ψ hψ => ?_⟩
  · apply ((setAdj (e.app i)).homEquiv _ _).injective
    rw [key, Equiv.apply_symm_apply, ← Category.assoc, hχ' i, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  · apply ((setAdj (LimitHigherDirectImage.limitMorphism e cY cT hcT)).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    refine hu _ fun i => ?_
    have hk := key ψ i
    rw [hψ i] at hk
    simp only [σ, hk, Category.assoc, Iso.inv_hom_id_app]
    exact (Category.comp_id _).symm

end Presentation

end Stacks.EtaleCohomology.LimitSetBaseChange

end
