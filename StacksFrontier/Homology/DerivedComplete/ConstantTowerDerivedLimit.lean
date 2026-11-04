module

public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers
import all StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers

/-!
# The derived limit of a constant tower, and maps into derived limits of pro-constant towers

In a pretriangulated category with countable products, the constant tower with value `Y` and
identity transition maps has `Y` itself as a derived limit, the Milnor difference map `1 - shift`
of `∏ Y` being a split epimorphism with kernel the diagonal. Comparing defining triangles, a map
from `Y` to a derived limit of a tower pro-isomorphic to the constant tower `Y`, compatible with
the projections, is an isomorphism.

## Main results

* `NoetherianAdicCompletion.isDerivedLimitWithProjections_const`: a constant tower is its own
  derived limit.
* `NoetherianAdicCompletion.isIso_of_comp_eq_of_hasEventualInverses_const`: a map from `Y` to a
  derived limit of a tower pro-isomorphic to the constant tower `Y`, compatible with the
  projections, is an isomorphism.
* `NoetherianAdicCompletion.hasEventualInverses_of_coneTower`: a tower of cones of eventually
  vanishing endomorphisms of a fixed object is pro-isomorphic to the constant tower.

## Implementation notes

The comparison of defining triangles uses the private lemmas `productMap_delta` and
`isIso_hom₁_of_hasEventualInverses` of
`StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers`, hence the `import all`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u v

namespace NoetherianAdicCompletion

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasProductsOfShape ℕ D]

/-- The projections of the product of a constant tower, with target the constant value. -/
private abbrev constTowerπ (Y : D) (n : ℕ) :
    Rlim.Hom.systemProduct ((Functor.const ℕᵒᵖ).obj Y) ⟶ Y :=
  Pi.π (fun n : ℕ ↦ ((Functor.const ℕᵒᵖ).obj Y).obj (op n)) n

/-- The diagonal of the product of a constant tower. -/
private abbrev constTowerDiag (Y : D) :
    Y ⟶ Rlim.Hom.systemProduct ((Functor.const ℕᵒᵖ).obj Y) :=
  Pi.lift fun _ : ℕ ↦ 𝟙 Y

/-- The section `(yₙ) ↦ (-(y₀ + ⋯ + y_{n-1}))ₙ` of the Milnor difference map of a constant
tower. -/
private noncomputable def constTowerSection (Y : D) :
    Rlim.Hom.systemProduct ((Functor.const ℕᵒᵖ).obj Y) ⟶
      Rlim.Hom.systemProduct ((Functor.const ℕᵒᵖ).obj Y) :=
  Pi.lift fun n : ℕ ↦ -∑ k ∈ Finset.range n, constTowerπ Y k

omit [HasZeroObject D] [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
private theorem constTowerSection_π (Y : D) (n : ℕ) :
    constTowerSection Y ≫ constTowerπ Y n = -∑ k ∈ Finset.range n, constTowerπ Y k :=
  Pi.lift_π _ _

omit [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
private theorem constTowerDiag_π (Y : D) (n : ℕ) :
    constTowerDiag Y ≫ constTowerπ Y n = 𝟙 Y :=
  Pi.lift_π _ _

omit [HasZeroObject D] [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
private theorem constTowerDelta_π (Y : D) (n : ℕ) :
    Rlim.Hom.systemDelta ((Functor.const ℕᵒᵖ).obj Y) ≫ constTowerπ Y n =
      constTowerπ Y n - constTowerπ Y (n + 1) := by
  simp [Rlim.Hom.systemDelta, constTowerπ]

omit [HasZeroObject D] [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
private theorem constTowerSection_comp_delta (Y : D) :
    constTowerSection Y ≫ Rlim.Hom.systemDelta ((Functor.const ℕᵒᵖ).obj Y) = 𝟙 _ := by
  apply Pi.hom_ext
  intro n
  show _ ≫ constTowerπ Y n = 𝟙 _ ≫ constTowerπ Y n
  rw [Category.assoc, constTowerDelta_π, Preadditive.comp_sub, constTowerSection_π,
    constTowerSection_π, Finset.sum_range_succ, Category.id_comp]
  abel

omit [HasZeroObject D] [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
private theorem diag_comp_constTowerDelta (Y : D) :
    constTowerDiag Y ≫ Rlim.Hom.systemDelta ((Functor.const ℕᵒᵖ).obj Y) = 0 := by
  apply Pi.hom_ext
  intro n
  show _ ≫ constTowerπ Y n = 0 ≫ constTowerπ Y n
  rw [Category.assoc, constTowerDelta_π, Preadditive.comp_sub, constTowerDiag_π,
    constTowerDiag_π, sub_self, zero_comp]

omit [HasZeroObject D] [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
private theorem constTowerDelta_comp_section (Y : D) :
    constTowerπ Y 0 ≫ constTowerDiag Y +
      Rlim.Hom.systemDelta ((Functor.const ℕᵒᵖ).obj Y) ≫ constTowerSection Y = 𝟙 _ := by
  apply Pi.hom_ext
  intro n
  show _ ≫ constTowerπ Y n = 𝟙 _ ≫ constTowerπ Y n
  rw [Preadditive.add_comp, Category.assoc, Category.assoc, constTowerDiag_π, constTowerSection_π,
    Category.comp_id, Category.id_comp, Preadditive.comp_neg, Preadditive.comp_sum]
  simp only [constTowerDelta_π]
  rw [Finset.sum_range_sub' (fun k ↦ constTowerπ Y k) n]
  abel

/-- The Milnor triangle of the constant tower: the diagonal, the difference map `1 - shift` and
the zero connecting map form a distinguished triangle. -/
private theorem constTower_triangle_distinguished (Y : D) :
    Triangle.mk (constTowerDiag Y) (Rlim.Hom.systemDelta ((Functor.const ℕᵒᵖ).obj Y))
      (0 : _ ⟶ Y⟦(1 : ℤ)⟧) ∈ distTriang D := by
  let P := Rlim.Hom.systemProduct ((Functor.const ℕᵒᵖ).obj Y)
  let d := Rlim.Hom.systemDelta ((Functor.const ℕᵒᵖ).obj Y)
  have h₁ : constTowerπ Y 0 ≫ constTowerDiag Y + d ≫ constTowerSection Y = 𝟙 P :=
    constTowerDelta_comp_section Y
  have h₂ : constTowerDiag Y ≫ d = 0 := diag_comp_constTowerDelta Y
  have h₃ : constTowerSection Y ≫ d = 𝟙 P := constTowerSection_comp_delta Y
  have h₄ : constTowerSection Y ≫ constTowerπ Y 0 = 0 := by
    rw [constTowerSection_π, Finset.range_zero, Finset.sum_empty, neg_zero]
  let e : P ≅ Y ⊞ P :=
    { hom := biprod.lift (constTowerπ Y 0) d
      inv := biprod.desc (constTowerDiag Y) (constTowerSection Y)
      hom_inv_id := by rw [biprod.lift_desc, h₁]
      inv_hom_id := by
        apply biprod.hom_ext' <;> apply biprod.hom_ext
        · simp
        · simpa using h₂
        · simpa using h₄
        · simpa using h₃ }
  refine isomorphic_distinguished _ (binaryBiproductTriangle_distinguished Y P) _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_
  · apply biprod.hom_ext
    · show (constTowerDiag Y ≫ biprod.lift (constTowerπ Y 0) d) ≫ biprod.fst =
        (𝟙 Y ≫ biprod.inl) ≫ biprod.fst
      rw [Category.assoc, biprod.lift_fst, constTowerDiag_π, Category.id_comp, biprod.inl_fst]
    · show (constTowerDiag Y ≫ biprod.lift (constTowerπ Y 0) d) ≫ biprod.snd =
        (𝟙 Y ≫ biprod.inl) ≫ biprod.snd
      rw [Category.assoc, biprod.lift_snd, h₂, Category.id_comp, biprod.inl_snd]
  · show d ≫ 𝟙 P = biprod.lift (constTowerπ Y 0) d ≫ biprod.snd
    rw [biprod.lift_snd, Category.comp_id]
  · show (0 : P ⟶ Y⟦(1 : ℤ)⟧) ≫ (𝟙 Y)⟦(1 : ℤ)⟧' = 𝟙 P ≫ 0
    rw [zero_comp, comp_zero]

/-- **The derived limit of a constant tower.** The constant tower with value `Y` and identity
transition maps has `Y` itself as a derived limit, with the identity maps as projections: the
Milnor difference map `1 - shift` of `∏ Y` is a split epimorphism with kernel the diagonal. -/
public theorem isDerivedLimitWithProjections_const (Y : D) :
    IsDerivedLimitWithProjections ((Functor.const ℕᵒᵖ).obj Y) Y (fun _ ↦ 𝟙 Y) :=
  ⟨0, constTower_triangle_distinguished Y⟩

/-- **Maps into a derived limit of a pro-constant tower.** Let `φ` be a map from the constant
tower with value `Y` to a tower `G` which has eventual inverses, and let `L` be a derived limit of
`G` with projections `π`. Every `θ : Y ⟶ L` whose composites with the projections are the
components of `φ` is an isomorphism.

Maps into a derived limit are in general not determined by their composites with the
projections. Here the defining triangles of `Y`, as the derived limit of the constant tower, and
of `L` are compared through a morphism whose connecting square commutes because the connecting
map of the constant tower vanishes. -/
public theorem isIso_of_comp_eq_of_hasEventualInverses_const {Y : D} {G : ℕᵒᵖ ⥤ D}
    (φ : (Functor.const ℕᵒᵖ).obj Y ⟶ G) (hφ : HasEventualInverses φ)
    {L : D} {π : ∀ n : ℕ, L ⟶ G.obj ⟨n⟩} (hL : IsDerivedLimitWithProjections G L π)
    (θ : Y ⟶ L) (hθ : ∀ n : ℕ, θ ≫ π n = φ.app ⟨n⟩) : IsIso θ := by
  obtain ⟨δ, hδ⟩ := hL
  let tY : Rlim.Hom.DerivedLimitTriangle ((Functor.const ℕᵒᵖ).obj Y) Y :=
    ⟨constTowerDiag Y, 0, constTower_triangle_distinguished Y⟩
  let tL : Rlim.Hom.DerivedLimitTriangle G L := ⟨Pi.lift π, δ, hδ⟩
  let p := Limits.Pi.map fun n : ℕ ↦ φ.app (op n)
  have hd : p ≫ δ = 0 := by
    have h₂ : Rlim.Hom.systemDelta G ≫ δ = 0 := comp_distTriang_mor_zero₂₃ _ hδ
    calc p ≫ δ
        = (constTowerSection Y ≫ Rlim.Hom.systemDelta ((Functor.const ℕᵒᵖ).obj Y)) ≫
            p ≫ δ := by
          rw [constTowerSection_comp_delta, Category.id_comp]
      _ = constTowerSection Y ≫ p ≫
            Rlim.Hom.systemDelta G ≫ δ := by
          rw [Category.assoc, reassoc_of% (productMap_delta φ)]
      _ = 0 := by rw [h₂, comp_zero, comp_zero]
  let f : tY.triangle ⟶ tL.triangle :=
    Triangle.homMk _ _ θ p p
      (by
        apply Pi.hom_ext
        intro n
        simp only [tY, tL, p, Rlim.Hom.DerivedLimitTriangle.triangle, Triangle.mk_mor₁,
          Category.assoc, Pi.map_π, Pi.lift_π_assoc, Pi.lift_π, hθ]
        simp)
      (productMap_delta φ)
      (by simp [tY, tL, hd])
  exact isIso_hom₁_of_hasEventualInverses φ hφ tY tL f rfl rfl

omit [HasProductsOfShape ℕ D] in
/-- **Towers of cones of eventually vanishing endomorphisms are pro-constant.** Let `C` be a
tower and `u : X ⟶ Cₙ` compatible maps from a fixed object, each the second map of a
distinguished triangle `X ⟶ X ⟶ Cₙ ⟶ X⟦1⟧` with first map `eₙ`, such that the transition maps
of `C` are compatible with the third maps up to endomorphisms `h m n` of `X`. If for every `n`
some `eₘ` with `m ≥ n` vanishes, and then some `h m' m` with `m' ≥ m` vanishes, then `u` has
eventual inverses.

This is the case of the towers of cones of the powers `gⁿ⁺¹` of a scalar acting nilpotently on
`X`, whose transition maps are induced by the maps of triangles `(gᵐ⁻ⁿ, 1)`. -/
public theorem hasEventualInverses_of_coneTower {X : D} {C : ℕᵒᵖ ⥤ D}
    (u : (Functor.const ℕᵒᵖ).obj X ⟶ C) (e : ℕ → (X ⟶ X))
    (w : ∀ n : ℕ, C.obj ⟨n⟩ ⟶ X⟦(1 : ℤ)⟧)
    (hT : ∀ n : ℕ, Triangle.mk (e n) (u.app ⟨n⟩) (w n) ∈ distTriang D)
    (h : ∀ m n : ℕ, n ≤ m → (X ⟶ X))
    (hw : ∀ (m n : ℕ) (hnm : n ≤ m),
      C.map (homOfLE hnm).op ≫ w n = w m ≫ (h m n hnm)⟦(1 : ℤ)⟧')
    (hvan : ∀ n : ℕ, ∃ (m : ℕ) (_hnm : n ≤ m), e m = 0 ∧
      ∃ (m' : ℕ) (hmm' : m ≤ m'), h m' m hmm' = 0) :
    HasEventualInverses u := by
  intro n
  obtain ⟨m, hnm, hem, m', hmm', hh⟩ := hvan n
  obtain ⟨s, hs⟩ : ∃ s : C.obj ⟨m⟩ ⟶ X, 𝟙 X = u.app ⟨m⟩ ≫ s :=
    Triangle.yoneda_exact₂ _ (hT m) (𝟙 X) (by simp [hem])
  have hu (a b : ℕ) (hab : b ≤ a) : u.app ⟨a⟩ ≫ C.map (homOfLE hab).op = u.app ⟨b⟩ := by
    simpa using (u.naturality (homOfLE hab).op).symm
  obtain ⟨k, hk⟩ : ∃ k : X⟦(1 : ℤ)⟧ ⟶ C.obj ⟨n⟩,
      C.map (homOfLE hnm).op - s ≫ u.app ⟨n⟩ = w m ≫ k :=
    Triangle.yoneda_exact₃ _ (hT m) (C.map (homOfLE hnm).op - s ≫ u.app ⟨n⟩ : C.obj ⟨m⟩ ⟶ _)
    (by
      simp only [Triangle.mk_mor₂, Preadditive.comp_sub, hu, ← Category.assoc, ← hs]
      exact sub_eq_zero.mpr (Category.id_comp (u.app ⟨n⟩)).symm)
  refine ⟨m', hnm.trans hmm', C.map (homOfLE hmm').op ≫ s, ?_, ?_⟩
  · rw [← Category.assoc, hu, ← hs]
    rfl
  · have h₁ : C.map (homOfLE hmm').op ≫ (C.map (homOfLE hnm).op - s ≫ u.app ⟨n⟩) = 0 := by
      rw [hk, ← Category.assoc, hw, hh, Functor.map_zero, comp_zero, zero_comp]
    rw [Preadditive.comp_sub, sub_eq_zero, ← Functor.map_comp] at h₁
    rw [Category.assoc, ← h₁]
    rfl

end NoetherianAdicCompletion

end
