module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionExteriorProduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CorrespondenceMonoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExteriorProductIntersection
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveCycleClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorAssociativity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The tensor product of the correspondences of two cycles

Let `k` be a field and `X`, `Y` smooth projective schemes over `k`, of arbitrary (not necessarily
constant) dimension. A cycle `α ∈ CH^i(X)` is a correspondence `a_α ∈ Corr^i(Spec k, X)`
(Stacks 0FG0 (3); `Stacks.WeilCohomology.pointCorrHom`). This file proves that the tensor product
of correspondences (Stacks 0FG7) carries `a_α` and `a_β` to the correspondence of the exterior
product `α × β ∈ CH^{i+j}(X × Y)` (Stacks 0FBV; `Stacks.Chow.codimensionExteriorProduct`):

  `ρ⁻¹ ≫ (a_α ⊗ a_β) = a_{α × β}`, `ρ : Spec k ⊗ Spec k ≅ Spec k`.

This is the identity of correspondences behind axiom (C)(c) of Stacks 0FH1.

The proof reduces, by biadditivity, to classes `a ∈ CH_{d-i}(X_d)` and `b ∈ CH_{e-j}(Y_e)`
supported on single parts. Then both sides are concentrated in the block `(0, d + e)`, and there
the tensor product `pr₁₃^* a · pr₂₄^* b` on `(P × P) × (X_d × Y_e)`, `P ≅ Spec k`, moved to
`X_d × Y_e` along the second projection, is `p₁^* a · p₂^* b = a × b` (Remark 0FHD,
`Stacks.Chow.selfIntersectionProduct_flatPullbackChow_fst_snd`).

## Main results

* `Stacks.WeilCohomology.chowPushforwardOfIso_tensorInt_point`: the tensor product of two
  correspondences from a point `P ≅ Spec k` is the exterior product.
* `Stacks.WeilCohomology.corrEquivOfIso_tensor_corrFromPointEquiv`: the identity on the
  correspondences of Section 0FFZ.
* `Stacks.WeilCohomology.tensorHom_pointCorrHom`: `ρ⁻¹ ≫ (a_α ⊗ a_β) = a_{α × β}`.

## References

* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
* [Stacks Project, Tag 0FH1](https://stacks.math.columbia.edu/tag/0FH1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Stacks.Chow

universe u

namespace Stacks.WeilCohomology

open CorrespondenceCategory ChowMotiveCat SmoothProjectiveScheme

variable {k : Type u} [Field k]

local notation "𝐎" => (GradedCompositionData.Obj.mk :
  CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme _) →
    CorrespondenceCategory _)

/-! ### Transport from a point isomorphic to the base -/

section PointTransport

variable (C : ChowSituation.{u}) {Z P : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sP : P ⟶ C.S) [IsIso sP] [LocallyOfFiniteType sP]

/-- Stacks 0FG0 (3) for a point `P` isomorphic to the base, on a pure tensor: the class moved
along the projection `P ×_S Z ≅ Z`. -/
theorem correspondenceFromPointEquivOfIso_tmul (m r : ℤ) (q : ℚ) (z : chowGroup C sZ (m - r)) :
    correspondenceFromPointEquivOfIso C sZ sP m r (q ⊗ₜ[ℤ] z) =
      q ⊗ₜ[ℤ] chowPushforwardOfIso C sZ (prodBase sP sZ) (inv (Limits.pullback.snd sP sZ))
        (by rw [IsIso.inv_comp_eq]; exact Limits.pullback.condition) (m - r) z := by
  have hc : prodHom (𝟙 C.S) sZ sP sZ sP (𝟙 Z) (Category.comp_id _) (Category.id_comp _) ≫
      Limits.pullback.snd (𝟙 C.S) sZ = Limits.pullback.snd sP sZ := by
    simp [prodHom]
  have h : correspondenceFromPointEquivOfIso C sZ sP m r (q ⊗ₜ[ℤ] z) =
      q ⊗ₜ[ℤ] chowPushforwardOfIso C (prodBase (𝟙 C.S) sZ) (prodBase sP sZ)
        (inv (prodHom (𝟙 C.S) sZ sP sZ sP (𝟙 Z) (Category.comp_id _) (Category.id_comp _)))
        (by rw [IsIso.inv_comp_eq, prodHom_comp_prodBase]) (m - r)
        (chowPushforwardOfIso C sZ (prodBase (𝟙 C.S) sZ)
          (inv (Limits.pullback.snd (𝟙 C.S) sZ))
          (by rw [IsIso.inv_comp_eq]; exact Limits.pullback.condition) (m - r) z) :=
    rfl
  rw [h, chowPushforwardOfIso_comp_apply]
  exact congrArg _ (chowPushforwardOfIso_congr_apply C _ _ _ _ (IsIso.inv_eq_of_hom_inv_id
    (by rw [← hc, Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id])).symm
    _ _ _ z)

/-- Proper pushforward along `u` followed by transport along `w` is transport along `q⁻¹` of
proper pushforward along `u'` of the transport along `ν`, when `u ≫ w ≫ q = ν ≫ u'`. -/
theorem chowPushforwardOfIso_properChowPushforward_eq_inv {A A' B B' B'' : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sA' : A' ⟶ C.S) [LocallyOfFiniteType sA']
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sB' : B' ⟶ C.S) [LocallyOfFiniteType sB']
    (sB'' : B'' ⟶ C.S) [LocallyOfFiniteType sB''] (u : A ⟶ B) [IsProper u] (hu : u ≫ sB = sA)
    (u' : A' ⟶ B') [IsProper u'] (hu' : u' ≫ sB' = sA') (ν : A ⟶ A') [IsIso ν]
    (hν : ν ≫ sA' = sA) (w : B ⟶ B'') [IsIso w] (hw : w ≫ sB'' = sB) (q : B'' ⟶ B') [IsIso q]
    (hq : q ≫ sB' = sB'') (hcomm : u ≫ w ≫ q = ν ≫ u') (m : ℤ) (y : chowGroup C sA m)
    (z : chowGroup C sA' m) (hz : chowPushforwardOfIso C sA sA' ν hν m y = z) :
    chowPushforwardOfIso C sB sB'' w hw m
        (properChowPushforward C sA sB u hu m (properPushforwardDescends _ _ _ _ _ _) y) =
      chowPushforwardOfIso C sB' sB'' (inv q) (by rw [IsIso.inv_comp_eq, hq]) m
        (properChowPushforward C sA' sB' u' hu' m (properPushforwardDescends _ _ _ _ _ _) z) := by
  subst hz
  rw [← chowPushforwardOfIso_properChowPushforward_eq C sA sA' sB sB' u hu u' hu' ν hν (w ≫ q)
    (by rw [Category.assoc, hq, hw]) hcomm m _ _ y, chowPushforwardOfIso_comp_apply]
  exact chowPushforwardOfIso_congr_apply C _ _ _ _ (by simp) _ _ _ _

end PointTransport

section IsoPullback

variable (k) {W V : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW]
  (sV : V ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sV]

/-- Pushforward along the inverse of an isomorphism `π` over `k` is flat pullback along `π`. -/
theorem chowPushforwardOfIso_inv_heq_flatPullbackChow (π : W ⟶ V) [IsIso π] (hπ : π ≫ sV = sW)
    (m : ℤ) (a : chowGroup (fieldChowSituation k) sV m) :
    chowPushforwardOfIso (fieldChowSituation k) sV sW (inv π) (by rw [IsIso.inv_comp_eq, hπ]) m
        a ≍
      flatPullbackChow (fieldChowSituation k) sW sV π hπ 0 (relativeDimension_of_isIso π) m
        (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) a := by
  have h₁ := chowPushforwardOfIso_flatPullbackChow k sW sV sV π hπ π (𝟙 V) hπ
    (Category.id_comp _) (Category.comp_id _) (relativeDimension_of_isIso π)
    (relativeDimension_identity V) m a
  have h₂ := flatPullbackChow_id_heq k sV rfl (relativeDimension_identity V) m a
  refine (chowPushforwardOfIso_heq_congr _ _ _ _ _ (add_zero m).symm _ _
    (h₂.symm.trans (heq_of_eq h₁.symm))).trans (heq_of_eq ?_)
  exact chowPushforwardOfIso_inv_comp _ _ _ π hπ _ _

end IsoPullback

/-! ### The tensor product of two correspondences from a point -/

section PointTensor

local notation "μ" =>
  selfIntersectionProduct (fieldChowSituation k)
      (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
    (fieldGysinSystem k)

local notation "pb[" sA ", " sB ", " v ", " hv ", " r ", " hr ", " n "]" =>
  flatPullbackChow (fieldChowSituation k) sA sB v hv r hr n
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)

variable (k) {P A B : Scheme.{u}} (sP : P ⟶ (fieldChowSituation k).S)
  (sA : A ⟶ (fieldChowSituation k).S) (sB : B ⟶ (fieldChowSituation k).S) [Smooth sP]
  [IsSeparated sP] [IsIso sP] [Smooth sA] [IsSeparated sA] [Smooth sB] [IsSeparated sB]

/-- Flat pullback along `f` of the transport of `a` from `A` to `P × A` is flat pullback along
`f ≫ pr₂` of `a`. -/
private theorem flatPullbackChow_inv_snd_heq {Q C T : Scheme.{u}}
    (sQ : Q ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sQ] [IsIso sQ]
    (sC : C ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sC] (sT : T ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType sT] (f : T ⟶ Limits.pullback sQ sC) [LocallyOfFiniteType f] [Flat f]
    (hf : f ≫ prodBase sQ sC = sT) {r : ℕ} (hr : RelativeDimension f r)
    (hr' : RelativeDimension (f ≫ Limits.pullback.snd sQ sC) r)
    (hpb : (f ≫ Limits.pullback.snd sQ sC) ≫ sC = sT) (n : ℤ)
    (a : chowGroup (fieldChowSituation k) sC n) :
    pb[sT, prodBase sQ sC, f, hf, r, hr, n]
        (chowPushforwardOfIso _ sC (prodBase sQ sC) (inv (Limits.pullback.snd sQ sC))
          (by rw [IsIso.inv_comp_eq]; exact Limits.pullback.condition) _ a) ≍
      pb[sT, sC, f ≫ Limits.pullback.snd sQ sC, hpb, r, hr', n] a := by
  refine (flatPullbackChow_heq_of_heq _ _ _ _ _ _ (by simp) _
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (chowPushforwardOfIso_inv_heq_flatPullbackChow k (prodBase sQ sC) sC
      (Limits.pullback.snd sQ sC) Limits.pullback.condition.symm _ a)).trans ?_
  refine (flatPullbackChow_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) a).trans ?_
  exact flatPullbackChow_heq_congr _ _ _ _ _ _ _ rfl rfl _ _ rfl _ _ _ _ HEq.rfl

omit [IsSeparated sP] [IsSeparated sA] [IsSeparated sB] in
/-- **The tensor product of two correspondences from a point is the exterior product.** For
`P ≅ Spec k`, `a ∈ CH_{d-i}(A)` and `b ∈ CH_{e-j}(B)` read as correspondences `P ⟶ A` and
`P ⟶ B` along `P × A ≅ A` and `P × B ≅ B`, the tensor product
`pr₁₃^* a · pr₂₄^* b` on `(P × P) × (A × B)`, moved to `A × B` along the second projection, is
`a × b`. -/
theorem chowPushforwardOfIso_tensorInt_point {d e : ℕ} (hP : RelativeDimension sP 0)
    (hA : RelativeDimension sA d) (hB : RelativeDimension sB e) (i j : ℤ)
    (a : chowGroup (fieldChowSituation k) sA ((d : ℤ) - i))
    (b : chowGroup (fieldChowSituation k) sB ((e : ℤ) - j)) :
    chowPushforwardOfIso (fieldChowSituation k) (tensorBase sP sP sA sB) (prodBase sA sB)
        (Limits.pullback.snd (prodBase sP sP) (prodBase sA sB)) Limits.pullback.condition.symm
        (((d + e : ℕ) : ℤ) - (i + j))
        (tensorInt k sP sP sA sB (canonicalDiagonalClassFamily k) hP hP hA hB i j
          (chowPushforwardOfIso _ sA (prodBase sP sA) (inv (Limits.pullback.snd sP sA))
            (by rw [IsIso.inv_comp_eq]; exact Limits.pullback.condition) _ a)
          (chowPushforwardOfIso _ sB (prodBase sP sB) (inv (Limits.pullback.snd sP sB))
            (by rw [IsIso.inv_comp_eq]; exact Limits.pullback.condition) _ b)) ≍
      chowExteriorProduct (fieldChowSituation k)
        (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k) sA sB ((d : ℤ) - i)
        ((e : ℤ) - j) (a ⊗ₜ[ℤ] b) := by
  have hpb₁ : (tensorPr₁₃ sP sP sA sB ≫ Limits.pullback.snd sP sA) ≫ sA =
      tensorBase sP sP sA sB := by
    rw [Category.assoc, ← Limits.pullback.condition]
    exact tensorPr₁₃_comp_prodBase sP sP sA sB
  have hpb₂ : (tensorPr₂₄ sP sP sA sB ≫ Limits.pullback.snd sP sB) ≫ sB =
      tensorBase sP sP sA sB := by
    rw [Category.assoc, ← Limits.pullback.condition]
    exact tensorPr₂₄_comp_prodBase sP sP sA sB
  have hr₁ : RelativeDimension (tensorPr₁₃ sP sP sA sB ≫ Limits.pullback.snd sP sA) e :=
    RelativeDimension.comp_of_flat _ _ (relativeDimension_tensorPr₁₃ k sP sP sA sB hP hB)
      (relativeDimension_of_isIso _)
  have hr₂ : RelativeDimension (tensorPr₂₄ sP sP sA sB ≫ Limits.pullback.snd sP sB) d :=
    RelativeDimension.comp_of_flat _ _ (relativeDimension_tensorPr₂₄ k sP sP sA sB hP hA)
      (relativeDimension_of_isIso _)
  have h₁ := flatPullbackChow_inv_snd_heq k sP sA _ (tensorPr₁₃ sP sP sA sB)
    (tensorPr₁₃_comp_prodBase sP sP sA sB) (relativeDimension_tensorPr₁₃ k sP sP sA sB hP hB)
    hr₁ hpb₁ ((d : ℤ) - i) a
  have h₂ := flatPullbackChow_inv_snd_heq k sP sB _ (tensorPr₂₄ sP sP sA sB)
    (tensorPr₂₄_comp_prodBase sP sP sA sB) (relativeDimension_tensorPr₂₄ k sP sP sA sB hP hA)
    hr₂ hpb₂ ((e : ℤ) - j) b
  have hT := tensorInt_heq k sP sP sA sB (Δ := canonicalDiagonalClassFamily k) hP hP hA hB i j
    (chowPushforwardOfIso _ sA (prodBase sP sA) (inv (Limits.pullback.snd sP sA))
      (by rw [IsIso.inv_comp_eq]; exact Limits.pullback.condition) _ a)
    (chowPushforwardOfIso _ sB (prodBase sP sB) (inv (Limits.pullback.snd sP sB))
      (by rw [IsIso.inv_comp_eq]; exact Limits.pullback.condition) _ b)
  have hμ := hT.trans (selfIntersectionProduct_heq_of_heq (tensorBase sP sP sA sB) _ _
    (by push_cast; ring) (by push_cast; ring) h₁ h₂)
  have h₆ := chowPushforwardOfIso_selfIntersectionProduct_heq k (tensorBase sP sP sA sB)
    (prodBase sA sB) sA sB (Limits.pullback.snd (prodBase sP sP) (prodBase sA sB))
    Limits.pullback.condition.symm _ _ (Limits.pullback.fst sA sB) (Limits.pullback.snd sA sB)
    hpb₁ hpb₂ rfl Limits.pullback.condition.symm (tensorPr₁₃_snd sP sP sA sB).symm
    (tensorPr₂₄_snd sP sP sA sB).symm hr₁ hr₂ (relativeDimension_fst k sA sB hB)
    (relativeDimension_snd k sA sB hA) (relativeDimension_tensorBase k sP sP sA sB hP hP hA hB)
    (relativeDimension_prodBase k sA sB hA hB) rfl ((d : ℤ) - i) ((e : ℤ) - j) a b
  have h₇ := selfIntersectionProduct_flatPullbackChow_fst_snd sA sB hA hB ((d : ℤ) - i)
    ((e : ℤ) - j) a b
  exact (chowPushforwardOfIso_heq_congr _ _ _ _ _ (by push_cast; ring) _ _ hμ).trans
    (h₆.trans h₇)

end PointTensor

section Additivity

variable {Q Q' R P P' P'' C D A B : Type*} [AddCommMonoid Q] [AddCommMonoid Q'] [AddCommMonoid R]
  [AddCommMonoid P] [AddCommMonoid P'] [AddCommMonoid P''] [AddCommMonoid C] [AddCommMonoid D]
  [AddCommMonoid A] [AddCommMonoid B] [Module ℚ P] [Module ℚ P'] [Module ℚ P''] [Module ℚ C]
  [Module ℚ D] [Module ℚ A] [Module ℚ B]

/-- A composite `E (T (C₁ (c₁ a)) (C₂ (c₂ b)))` of additive and linear maps is additive in `a`. -/
theorem linearEquiv_bilinear_addMonoidHom_add_left (c₁ : Q →+ P) (c₂ : Q' →+ P')
    (C₁ : P ≃ₗ[ℚ] C) (C₂ : P' ≃ₗ[ℚ] D) (T : C →ₗ[ℚ] D →ₗ[ℚ] A) (E : A ≃ₗ[ℚ] B) (a a' : Q)
    (b : Q') :
    E (T (C₁ (c₁ (a + a'))) (C₂ (c₂ b))) =
      E (T (C₁ (c₁ a)) (C₂ (c₂ b))) + E (T (C₁ (c₁ a')) (C₂ (c₂ b))) := by
  simp only [map_add, LinearMap.add_apply]

/-- A composite `E (T (C₁ (c₁ a)) (C₂ (c₂ b)))` of additive and linear maps is additive in `b`. -/
theorem linearEquiv_bilinear_addMonoidHom_add_right (c₁ : Q →+ P) (c₂ : Q' →+ P')
    (C₁ : P ≃ₗ[ℚ] C) (C₂ : P' ≃ₗ[ℚ] D) (T : C →ₗ[ℚ] D →ₗ[ℚ] A) (E : A ≃ₗ[ℚ] B) (a : Q)
    (b b' : Q') :
    E (T (C₁ (c₁ a)) (C₂ (c₂ (b + b')))) =
      E (T (C₁ (c₁ a)) (C₂ (c₂ b))) + E (T (C₁ (c₁ a)) (C₂ (c₂ b'))) := by
  simp only [map_add]

variable [Module ℤ Q] [Module ℤ Q'] [Module ℤ R]

/-- A composite `C₃ (c₃ (c a b))` of additive and linear maps is additive in `a`. -/
theorem linearEquiv_addMonoidHom_bilinear_add_left (c : Q →ₗ[ℤ] Q' →ₗ[ℤ] R) (c₃ : R →+ P'')
    (C₃ : P'' ≃ₗ[ℚ] B) (a a' : Q) (b : Q') :
    C₃ (c₃ (c (a + a') b)) = C₃ (c₃ (c a b)) + C₃ (c₃ (c a' b)) := by
  simp only [map_add, LinearMap.add_apply]

/-- A composite `C₃ (c₃ (c a b))` of additive and linear maps is additive in `b`. -/
theorem linearEquiv_addMonoidHom_bilinear_add_right (c : Q →ₗ[ℤ] Q' →ₗ[ℤ] R) (c₃ : R →+ P'')
    (C₃ : P'' ≃ₗ[ℚ] B) (a : Q) (b b' : Q') :
    C₃ (c₃ (c a (b + b'))) = C₃ (c₃ (c a b)) + C₃ (c₃ (c a b')) := by
  simp only [map_add]

end Additivity

section Core

variable (k) {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sX] [IsSeparated sX] [IsProper sX] [Smooth sY]
  [IsSeparated sY] [IsProper sY]

/-! ### Classes supported on one part -/

omit [IsSeparated sX] [IsProper sX] in
/-- A class of `CH^i(X)` supported on the part `X_d` goes to `1 ⊗ α_d` in the summand
`CH_{d-i}(X_d) ⊗ ℚ` of `CH^i(X) ⊗ ℚ`. -/
theorem codimensionToCodimChow_single [CompactSpace X] (i : ℤ) (d : ℕ)
    (a : chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i)) :
    codimensionToCodimChow k sX i (Pi.single d a) =
      DirectSum.lof ℚ ℕ (fun d : ℕ ↦
        TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i))) d
        ((1 : ℚ) ⊗ₜ[ℤ] a) := by
  change ∑ d' ∈ nonemptyDimParts k sX, _ = _
  by_cases hd : d ∈ nonemptyDimParts k sX
  · rw [Finset.sum_eq_single d (fun d' _ hd' ↦ by
      rw [Pi.single_eq_of_ne hd', TensorProduct.tmul_zero, map_zero]) (fun h ↦ absurd hd h),
      Pi.single_eq_same]
  · have : IsEmpty (dimPart sX d).toScheme :=
      ⟨fun y ↦ hd ((mem_nonemptyDimParts k sX).2 ⟨_, y.2⟩)⟩
    have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i)
    rw [Subsingleton.elim a 0, Pi.single_zero, TensorProduct.tmul_zero, map_zero]
    exact Finset.sum_eq_zero fun d' _ ↦ by rw [Pi.zero_apply, TensorProduct.tmul_zero, map_zero]

omit [IsSeparated sX] [IsSeparated sY] in
/-- The exterior product of two classes supported on single parts `X_d` and `Y_e` is supported on
the part `(X ×_k Y)_{d+e}`. -/
theorem codimensionExteriorProduct_single (i j : ℤ) (d e : ℕ)
    (a : chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i))
    (b : chowGroup (fieldChowSituation k) (partBase sY e) ((e : ℤ) - j)) :
    codimensionExteriorProduct k sX sY i j (Pi.single d a) (Pi.single e b) =
      Pi.single (d + e) (codimensionExteriorTerm k sX sY i j (d + e) ⟨d, by omega⟩
        (Pi.single d a) (Pi.single e b)) := by
  funext n
  rw [codimensionExteriorProduct_apply]
  by_cases hn : n = d + e
  · subst hn
    rw [Pi.single_eq_same, Finset.sum_eq_single ⟨d, by omega⟩ (fun d' _ hd' ↦ ?_)
      (fun h ↦ absurd (Finset.mem_univ _) h)]
    have hd'' : (d' : ℕ) ≠ d := fun h ↦ hd' (Fin.ext h)
    simp only [codimensionExteriorTerm, LinearMap.mk₂_apply, Pi.single_eq_of_ne hd'',
      TensorProduct.zero_tmul, map_zero]
  · rw [Pi.single_eq_of_ne hn]
    refine Finset.sum_eq_zero fun d' _ ↦ ?_
    by_cases hd : (d' : ℕ) = d
    · have he : n - (d' : ℕ) ≠ e := by omega
      simp only [codimensionExteriorTerm, LinearMap.mk₂_apply, Pi.single_eq_of_ne he,
        TensorProduct.tmul_zero, map_zero]
    · simp only [codimensionExteriorTerm, LinearMap.mk₂_apply, Pi.single_eq_of_ne hd,
        TensorProduct.zero_tmul, map_zero]

omit [IsSeparated sX] [IsProper sX] [IsSeparated sY] [IsProper sY] in
/-- Pushforwards along two morphisms into parts `(X ×_k Y)_N` and `(X ×_k Y)_M`, `N = M`, which
agree in `X ×_k Y`. -/
theorem properChowPushforward_dimPart_heq {W : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType sW] {N M : ℕ} (h : N = M)
    (f : W ⟶ (dimPart (prodBase sX sY) N).toScheme) (g : W ⟶ (dimPart (prodBase sX sY) M).toScheme)
    [IsProper f] [IsProper g] (hf : f ≫ partBase (prodBase sX sY) N = sW)
    (hg : g ≫ partBase (prodBase sX sY) M = sW)
    (hfg : f ≫ (dimPart (prodBase sX sY) N).ι = g ≫ (dimPart (prodBase sX sY) M).ι)
    {m m' : ℤ} (hm : m = m') (z : chowGroup (fieldChowSituation k) sW m)
    (z' : chowGroup (fieldChowSituation k) sW m') (hz : z ≍ z') :
    properChowPushforward (fieldChowSituation k) sW _ f hf m
        (properPushforwardDescends _ _ _ _ _ _) z ≍
      properChowPushforward (fieldChowSituation k) sW _ g hg m'
        (properPushforwardDescends _ _ _ _ _ _) z' := by
  subst h hm
  obtain rfl : f = g := (cancel_mono _).1 hfg
  cases hz
  rfl

omit [IsSeparated sX] [IsSeparated sY] in
/-- The term of the exterior product of two classes supported on single parts `X_d` and `Y_e`
which survives: `a × b` placed on `X_d × Y_e ⊆ (X ×_k Y)_{d+e}`. -/
theorem codimensionExteriorTerm_single_heq (i j : ℤ) (d e : ℕ)
    (a : chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i))
    (b : chowGroup (fieldChowSituation k) (partBase sY e) ((e : ℤ) - j)) (n : ℕ)
    (d' : Fin (n + 1)) (hd : (d' : ℕ) = d) (he : n - (d' : ℕ) = e) :
    codimensionExteriorTerm k sX sY i j n d' (Pi.single d a) (Pi.single e b) ≍
      properChowPushforward (fieldChowSituation k) (prodBase (partBase sX d) (partBase sY e))
        (partBase (prodBase sX sY) (d + e)) (partProdHom k sX sY d e)
        (partProdHom_comp_partBase k sX sY d e) (((d + e : ℕ) : ℤ) - (i + j))
        (properPushforwardDescends _ _ _ _ _ _)
        (chowGroupDegreeEquiv _ _ (by push_cast; ring)
          (chowExteriorProduct (fieldChowSituation k)
            (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
            (partBase sX d) (partBase sY e) ((d : ℤ) - i) ((e : ℤ) - j) (a ⊗ₜ[ℤ] b))) := by
  obtain ⟨d', hlt⟩ := d'
  dsimp only at hd he
  subst hd he
  simp only [codimensionExteriorTerm, LinearMap.mk₂_apply, Pi.single_eq_same]
  exact properChowPushforward_dimPart_heq k sX sY _ (by omega) _ _ _ _
    (by rw [partProdIncl_ι, partProdHom_ι])
    (by push_cast [Nat.cast_sub (Nat.lt_succ_iff.1 hlt)]; ring) _ _
    ((chowGroupDegreeEquiv_heq _ _ _ _).trans (chowGroupDegreeEquiv_heq _ _ _ _).symm)

/-- The integral form of `correspondenceEquivOfIso_tensorBlockInclusion_point`. -/
theorem chowPushforwardOfIso_tensorBlockHom_point (d e : ℕ) (i j : ℤ)
    (a : chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i))
    (b : chowGroup (fieldChowSituation k) (partBase sY e) ((e : ℤ) - j)) :
    chowPushforwardOfIso (fieldChowSituation k)
        (prodBase (partBase (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S))
          (0 + 0)) (partBase (prodBase sX sY) (d + e)))
        (prodBase (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase (prodBase sX sY) (d + e)))
        (prodHom (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase (prodBase sX sY) (d + e))
          (partBase (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S)) (0 + 0))
          (partBase (prodBase sX sY) (d + e))
          (partMap (𝟙 (fieldChowSituation k).S)
            (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S))
            (Limits.pullback.fst (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S)) rfl
            (0 + 0))
          (partMap (prodBase sX sY) (prodBase sX sY) (𝟙 _) (Category.id_comp _) (d + e))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _))
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (((d + e : ℕ) : ℤ) - (i + j))
        (properChowPushforward (fieldChowSituation k) _ _
          (tensorBlockHom k (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S) sX sY
            0 0 d e) (tensorBlockHom_comp_prodBase _ _ _ _ _ _ _ _ _) _
          (properPushforwardDescends _ _ _ _ _ _)
          (tensorInt k (partBase (𝟙 (fieldChowSituation k).S) 0)
            (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase sX d) (partBase sY e)
            (canonicalDiagonalClassFamily k) (relativeDimension_partBase _ 0)
            (relativeDimension_partBase _ 0) (relativeDimension_partBase sX d)
            (relativeDimension_partBase sY e) i j
            (chowPushforwardOfIso _ (partBase sX d)
              (prodBase (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase sX d))
              (inv (Limits.pullback.snd (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase sX d)))
              (by rw [IsIso.inv_comp_eq]; exact Limits.pullback.condition) _ a)
            (chowPushforwardOfIso _ (partBase sY e)
              (prodBase (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase sY e))
              (inv (Limits.pullback.snd (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase sY e)))
              (by rw [IsIso.inv_comp_eq]; exact Limits.pullback.condition) _ b))) =
      chowPushforwardOfIso (fieldChowSituation k) (partBase (prodBase sX sY) (d + e))
        (prodBase (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase (prodBase sX sY) (d + e)))
        (inv (Limits.pullback.snd (partBase (𝟙 (fieldChowSituation k).S) 0)
          (partBase (prodBase sX sY) (d + e))))
        (by rw [IsIso.inv_comp_eq]; exact Limits.pullback.condition) (((d + e : ℕ) : ℤ) - (i + j))
        (properChowPushforward (fieldChowSituation k)
          (prodBase (partBase sX d) (partBase sY e)) (partBase (prodBase sX sY) (d + e))
          (partProdHom k sX sY d e) (partProdHom_comp_partBase k sX sY d e)
          (((d + e : ℕ) : ℤ) - (i + j)) (properPushforwardDescends _ _ _ _ _ _)
          (chowGroupDegreeEquiv _ _ (by push_cast; ring)
            (chowExteriorProduct (fieldChowSituation k)
              (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
              (partBase sX d) (partBase sY e) ((d : ℤ) - i) ((e : ℤ) - j) (a ⊗ₜ[ℤ] b)))) := by
  have hJ := chowPushforwardOfIso_tensorInt_point k (partBase (𝟙 (fieldChowSituation k).S) 0)
    (partBase sX d) (partBase sY e) (relativeDimension_partBase _ 0)
    (relativeDimension_partBase sX d) (relativeDimension_partBase sY e) i j a b
  have key : tensorBlockHom k (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S) sX sY
        0 0 d e ≫
      prodHom (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase (prodBase sX sY) (d + e))
        (partBase (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S)) (0 + 0))
        (partBase (prodBase sX sY) (d + e))
        (partMap (𝟙 (fieldChowSituation k).S)
          (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S))
          (Limits.pullback.fst (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S)) rfl
          (0 + 0))
        (partMap (prodBase sX sY) (prodBase sX sY) (𝟙 _) (Category.id_comp _) (d + e))
        (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _) ≫
      Limits.pullback.snd (partBase (𝟙 (fieldChowSituation k).S) 0)
        (partBase (prodBase sX sY) (d + e)) =
      Limits.pullback.snd
        (prodBase (partBase (𝟙 (fieldChowSituation k).S) 0)
          (partBase (𝟙 (fieldChowSituation k).S) 0))
        (prodBase (partBase sX d) (partBase sY e)) ≫ partProdHom k sX sY d e := by
    simp only [tensorBlockHom, prodHom, Limits.pullback.lift_snd, partMap_id, Category.comp_id]
  have : IsIso (Limits.pullback.fst (partBase (𝟙 (fieldChowSituation k).S) 0)
      (partBase (𝟙 (fieldChowSituation k).S) 0)) := Limits.pullback_fst_iso_of_right_iso _ _
  have : IsIso (prodBase (partBase (𝟙 (fieldChowSituation k).S) 0)
      (partBase (𝟙 (fieldChowSituation k).S) 0)) := IsIso.comp_isIso
  have : IsIso (Limits.pullback.snd (prodBase (partBase (𝟙 (fieldChowSituation k).S) 0)
      (partBase (𝟙 (fieldChowSituation k).S) 0)) (prodBase (partBase sX d) (partBase sY e))) :=
    Limits.pullback_snd_iso_of_left_iso _ _
  exact chowPushforwardOfIso_properChowPushforward_eq_inv (fieldChowSituation k) _ _ _ _ _ _
    _ _ _ _ Limits.pullback.condition.symm _ _ _ Limits.pullback.condition.symm key _ _ _
    (eq_of_heq (hJ.trans (chowGroupDegreeEquiv_heq _ _ _ _).symm))

/-- The block `(0, d + e)` of the tensor product of two correspondences from the point, on pure
tensors. -/
theorem correspondenceEquivOfIso_tensorBlockInclusion_point_tmul (d e : ℕ) (i j : ℤ)
    (a : chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i))
    (b : chowGroup (fieldChowSituation k) (partBase sY e) ((e : ℤ) - j)) :
    correspondenceEquivOfIso (fieldChowSituation k) (partBase (𝟙 (fieldChowSituation k).S) 0)
        (partBase (prodBase sX sY) (d + e))
        (partBase (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S)) (0 + 0))
        (partBase (prodBase sX sY) (d + e))
        (partMap (𝟙 (fieldChowSituation k).S)
          (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S))
          (Limits.pullback.fst (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S)) rfl
          (0 + 0))
        (partMap (prodBase sX sY) (prodBase sX sY) (𝟙 _) (Category.id_comp _) (d + e))
        (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _) ((d + e : ℕ) : ℤ)
        (i + j)
        (tensorBlockInclusion k (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S) sX sY
          0 0 d e (i + j)
          (tensorBlock k (partBase (𝟙 (fieldChowSituation k).S) 0)
            (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase sX d) (partBase sY e)
            (canonicalDiagonalClassFamily k) (relativeDimension_partBase _ 0)
            (relativeDimension_partBase _ 0) (relativeDimension_partBase sX d)
            (relativeDimension_partBase sY e) i j
            (correspondenceFromPointEquivOfIso _ (partBase sX d)
              (partBase (𝟙 (fieldChowSituation k).S) 0) d i ((1 : ℚ) ⊗ₜ[ℤ] a))
            (correspondenceFromPointEquivOfIso _ (partBase sY e)
              (partBase (𝟙 (fieldChowSituation k).S) 0) e j ((1 : ℚ) ⊗ₜ[ℤ] b)))) =
      (1 : ℚ) ⊗ₜ[ℤ] chowPushforwardOfIso (fieldChowSituation k)
        (prodBase (partBase (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S))
          (0 + 0)) (partBase (prodBase sX sY) (d + e)))
        (prodBase (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase (prodBase sX sY) (d + e)))
        (prodHom (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase (prodBase sX sY) (d + e))
          (partBase (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S)) (0 + 0))
          (partBase (prodBase sX sY) (d + e))
          (partMap (𝟙 (fieldChowSituation k).S)
            (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S))
            (Limits.pullback.fst (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S)) rfl
            (0 + 0))
          (partMap (prodBase sX sY) (prodBase sX sY) (𝟙 _) (Category.id_comp _) (d + e))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _))
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (((d + e : ℕ) : ℤ) - (i + j))
        (properChowPushforward (fieldChowSituation k) _ _
          (tensorBlockHom k (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S) sX sY
            0 0 d e) (tensorBlockHom_comp_prodBase _ _ _ _ _ _ _ _ _) _
          (properPushforwardDescends _ _ _ _ _ _)
          (tensorInt k (partBase (𝟙 (fieldChowSituation k).S) 0)
            (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase sX d) (partBase sY e)
            (canonicalDiagonalClassFamily k) (relativeDimension_partBase _ 0)
            (relativeDimension_partBase _ 0) (relativeDimension_partBase sX d)
            (relativeDimension_partBase sY e) i j
            (chowPushforwardOfIso _ (partBase sX d)
              (prodBase (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase sX d))
              (inv (Limits.pullback.snd (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase sX d)))
              (by rw [IsIso.inv_comp_eq]; exact Limits.pullback.condition) _ a)
            (chowPushforwardOfIso _ (partBase sY e)
              (prodBase (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase sY e))
              (inv (Limits.pullback.snd (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase sY e)))
              (by rw [IsIso.inv_comp_eq]; exact Limits.pullback.condition) _ b))) := by
  simp only [correspondenceFromPointEquivOfIso_tmul, tensorBlock_tmul, tensorBlockInclusion_tmul,
    correspondenceEquivOfIso_tmul, mul_one]

/-- **The block `(0, d + e)` of the tensor product of two correspondences from the point.** For
`a ∈ CH_{d-i}(X_d)` and `b ∈ CH_{e-j}(Y_e)`, read as correspondences from (the part of
dimension `0` of) `Spec k`, the block of `a ⊗ b` in
`Corr^{i+j}((Spec k × Spec k)_0, (X × Y)_{d+e})`, transported along `Spec k × Spec k ≅ Spec k`,
is the correspondence from the point of the exterior product `a × b`, placed on
`X_d × Y_e ⊆ (X × Y)_{d+e}`. -/
theorem correspondenceEquivOfIso_tensorBlockInclusion_point (d e : ℕ) (i j : ℤ)
    (a : chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i))
    (b : chowGroup (fieldChowSituation k) (partBase sY e) ((e : ℤ) - j)) :
    correspondenceEquivOfIso (fieldChowSituation k) (partBase (𝟙 (fieldChowSituation k).S) 0)
        (partBase (prodBase sX sY) (d + e))
        (partBase (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S)) (0 + 0))
        (partBase (prodBase sX sY) (d + e))
        (partMap (𝟙 (fieldChowSituation k).S)
          (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S))
          (Limits.pullback.fst (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S)) rfl
          (0 + 0))
        (partMap (prodBase sX sY) (prodBase sX sY) (𝟙 _) (Category.id_comp _) (d + e))
        (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _) ((d + e : ℕ) : ℤ)
        (i + j)
        (tensorBlockInclusion k (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S) sX sY
          0 0 d e (i + j)
          (tensorBlock k (partBase (𝟙 (fieldChowSituation k).S) 0)
            (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase sX d) (partBase sY e)
            (canonicalDiagonalClassFamily k) (relativeDimension_partBase _ 0)
            (relativeDimension_partBase _ 0) (relativeDimension_partBase sX d)
            (relativeDimension_partBase sY e) i j
            (correspondenceFromPointEquivOfIso _ (partBase sX d)
              (partBase (𝟙 (fieldChowSituation k).S) 0) d i ((1 : ℚ) ⊗ₜ[ℤ] a))
            (correspondenceFromPointEquivOfIso _ (partBase sY e)
              (partBase (𝟙 (fieldChowSituation k).S) 0) e j ((1 : ℚ) ⊗ₜ[ℤ] b)))) =
      correspondenceFromPointEquivOfIso _ (partBase (prodBase sX sY) (d + e))
        (partBase (𝟙 (fieldChowSituation k).S) 0) ((d + e : ℕ) : ℤ) (i + j)
        ((1 : ℚ) ⊗ₜ[ℤ] properChowPushforward (fieldChowSituation k)
          (prodBase (partBase sX d) (partBase sY e)) (partBase (prodBase sX sY) (d + e))
          (partProdHom k sX sY d e) (partProdHom_comp_partBase k sX sY d e)
          (((d + e : ℕ) : ℤ) - (i + j)) (properPushforwardDescends _ _ _ _ _ _)
          (chowGroupDegreeEquiv _ _ (by push_cast; ring)
            (chowExteriorProduct (fieldChowSituation k)
              (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
              (partBase sX d) (partBase sY e) ((d : ℤ) - i) ((e : ℤ) - j) (a ⊗ₜ[ℤ] b)))) :=
  (correspondenceEquivOfIso_tensorBlockInclusion_point_tmul k sX sY d e i j a b).trans
    ((congrArg (TensorProduct.tmul ℤ (1 : ℚ))
      (chowPushforwardOfIso_tensorBlockHom_point k sX sY d e i j a b)).trans
      (correspondenceFromPointEquivOfIso_tmul _ _ _ _ _ _ _).symm)

omit [IsSeparated sX] [IsSeparated sY] in
/-- The correspondence from the point of the exterior product of two classes supported on single
parts `X_d` and `Y_e`: its only block is `(0, d + e)`. -/
theorem corrFromPointEquiv_codimensionExteriorProduct_single
    [CompactSpace (Limits.pullback sX sY : Scheme.{u})] (i j : ℤ) (d e : ℕ)
    (a : chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i))
    (b : chowGroup (fieldChowSituation k) (partBase sY e) ((e : ℤ) - j)) :
    corrFromPointEquiv k (prodBase sX sY) (i + j)
        (codimensionToCodimChow k (prodBase sX sY) (i + j)
          (codimensionExteriorProduct k sX sY i j (Pi.single d a) (Pi.single e b))) =
      DirectSum.lof ℚ ℕ _ 0 (DirectSum.lof ℚ ℕ _ (d + e)
        (correspondenceFromPointEquivOfIso _ (partBase (prodBase sX sY) (d + e))
          (partBase (𝟙 (fieldChowSituation k).S) 0) ((d + e : ℕ) : ℤ) (i + j)
          ((1 : ℚ) ⊗ₜ[ℤ] properChowPushforward (fieldChowSituation k)
            (prodBase (partBase sX d) (partBase sY e)) (partBase (prodBase sX sY) (d + e))
            (partProdHom k sX sY d e) (partProdHom_comp_partBase k sX sY d e)
            (((d + e : ℕ) : ℤ) - (i + j)) (properPushforwardDescends _ _ _ _ _ _)
            (chowGroupDegreeEquiv _ _ (by push_cast; ring)
              (chowExteriorProduct (fieldChowSituation k)
                (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
                (partBase sX d) (partBase sY e) ((d : ℤ) - i) ((e : ℤ) - j) (a ⊗ₜ[ℤ] b)))))) := by
  rw [codimensionExteriorProduct_single, codimensionToCodimChow_single,
    eq_of_heq (codimensionExteriorTerm_single_heq k sX sY i j d e a b (d + e) ⟨d, by omega⟩ rfl
      (Nat.add_sub_cancel_left d e)), corrFromPointEquiv_lof]

/-- The tensor product of the correspondences from the point of two classes supported on single
parts `X_d` and `Y_e`, transported along `Spec k × Spec k ≅ Spec k`: its only block is
`(0, d + e)`. -/
theorem corrEquivOfIso_tensor_corrFromPointEquiv_single_lof [CompactSpace X] [CompactSpace Y]
    (i j : ℤ) (d e : ℕ)
    (a : chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i))
    (b : chowGroup (fieldChowSituation k) (partBase sY e) ((e : ℤ) - j)) :
    corrEquivOfIso k (𝟙 (fieldChowSituation k).S)
        (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S))
        (prodBase sX sY) (prodBase sX sY)
        (Limits.pullback.fst (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S))
        (𝟙 _) rfl (Category.id_comp _) (i + j)
        (tensor k (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S) sX sY
          (canonicalDiagonalClassFamily k) i j
          (corrFromPointEquiv k sX i (codimensionToCodimChow k sX i (Pi.single d a)))
          (corrFromPointEquiv k sY j (codimensionToCodimChow k sY j (Pi.single e b)))) =
      DirectSum.lof ℚ ℕ _ (0 + 0) (DirectSum.lof ℚ ℕ _ (d + e)
        (correspondenceEquivOfIso (fieldChowSituation k) (partBase (𝟙 (fieldChowSituation k).S)
          (0 + 0)) (partBase (prodBase sX sY) (d + e))
          (partBase (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S)) (0 + 0))
          (partBase (prodBase sX sY) (d + e))
          (partMap (𝟙 (fieldChowSituation k).S)
            (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S))
            (Limits.pullback.fst (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S)) rfl
            (0 + 0))
          (partMap (prodBase sX sY) (prodBase sX sY) (𝟙 _) (Category.id_comp _) (d + e))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _) ((d + e : ℕ) : ℤ)
          (i + j)
          (tensorBlockInclusion k (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S) sX sY
            0 0 d e (i + j)
            (tensorBlock k (partBase (𝟙 (fieldChowSituation k).S) 0)
              (partBase (𝟙 (fieldChowSituation k).S) 0) (partBase sX d) (partBase sY e)
              (canonicalDiagonalClassFamily k) (relativeDimension_partBase _ 0)
              (relativeDimension_partBase _ 0) (relativeDimension_partBase sX d)
              (relativeDimension_partBase sY e) i j
              (correspondenceFromPointEquivOfIso _ (partBase sX d)
                (partBase (𝟙 (fieldChowSituation k).S) 0) d i ((1 : ℚ) ⊗ₜ[ℤ] a))
              (correspondenceFromPointEquivOfIso _ (partBase sY e)
                (partBase (𝟙 (fieldChowSituation k).S) 0) e j ((1 : ℚ) ⊗ₜ[ℤ] b)))))) := by
  simp only [codimensionToCodimChow_single, corrFromPointEquiv_lof, tensor_lof_lof,
    corrEquivOfIso_lof_lof]

/-- `corrEquivOfIso_tensor_corrFromPointEquiv` for classes supported on single parts. -/
theorem corrEquivOfIso_tensor_corrFromPointEquiv_single [CompactSpace X] [CompactSpace Y]
    [CompactSpace (Limits.pullback sX sY : Scheme.{u})] (i j : ℤ) (d e : ℕ)
    (a : chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i))
    (b : chowGroup (fieldChowSituation k) (partBase sY e) ((e : ℤ) - j)) :
    corrEquivOfIso k (𝟙 (fieldChowSituation k).S)
        (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S))
        (prodBase sX sY) (prodBase sX sY)
        (Limits.pullback.fst (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S))
        (𝟙 _) rfl (Category.id_comp _) (i + j)
        (tensor k (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S) sX sY
          (canonicalDiagonalClassFamily k) i j
          (corrFromPointEquiv k sX i (codimensionToCodimChow k sX i (Pi.single d a)))
          (corrFromPointEquiv k sY j (codimensionToCodimChow k sY j (Pi.single e b)))) =
      corrFromPointEquiv k (prodBase sX sY) (i + j)
        (codimensionToCodimChow k (prodBase sX sY) (i + j)
          (codimensionExteriorProduct k sX sY i j (Pi.single d a) (Pi.single e b))) :=
  (corrEquivOfIso_tensor_corrFromPointEquiv_single_lof k sX sY i j d e a b).trans
    ((congrArg (DirectSum.lof ℚ ℕ _ 0) (congrArg (DirectSum.lof ℚ ℕ _ (d + e))
      (correspondenceEquivOfIso_tensorBlockInclusion_point k sX sY d e i j a b))).trans
      (corrFromPointEquiv_codimensionExteriorProduct_single k sX sY i j d e a b).symm)

omit [IsSeparated sX] [IsSeparated sY] [IsProper sX] [IsProper sY] in
/-- Two biadditive maps on `CH^i(X) × CH^j(Y)`, `X` and `Y` quasi-compact, agree once they agree
on pairs of classes supported on single parts. -/
theorem biadditive_eq_of_pi_single [CompactSpace X] [CompactSpace Y] (i j : ℤ) {M : Type*}
    [AddCommGroup M] {F G : codimensionChowGroup k sX i → codimensionChowGroup k sY j → M}
    (h : ∀ (d e : ℕ) (a : chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i))
      (b : chowGroup (fieldChowSituation k) (partBase sY e) ((e : ℤ) - j)),
      F (Pi.single d a) (Pi.single e b) = G (Pi.single d a) (Pi.single e b))
    (hF₁ : ∀ α α' β, F (α + α') β = F α β + F α' β) (hF₂ : ∀ α β β', F α (β + β') = F α β + F α β')
    (hG₁ : ∀ α α' β, G (α + α') β = G α β + G α' β) (hG₂ : ∀ α β β', G α (β + β') = G α β + G α β')
    (α : codimensionChowGroup k sX i) (β : codimensionChowGroup k sY j) : F α β = G α β := by
  have hl : ∀ (H : codimensionChowGroup k sX i → codimensionChowGroup k sY j → M)
      (hH₁ : ∀ α α' β, H (α + α') β = H α β + H α' β)
      (hH₂ : ∀ α β β', H α (β + β') = H α β + H α β'),
      H α β = ∑ d ∈ nonemptyDimParts k sX, ∑ e ∈ nonemptyDimParts k sY,
        H (Pi.single d (α d)) (Pi.single e (β e)) := by
    intro H hH₁ hH₂
    have h₁ : ∀ a b, H a b = ∑ d ∈ nonemptyDimParts k sX, H (Pi.single d (a d)) b := by
      intro a b
      conv_lhs => rw [← sum_pi_single_codimensionChowGroup sX i a]
      exact map_sum (AddMonoidHom.mk' (fun a ↦ H a b) fun a a' ↦ hH₁ a a' b) _ _
    have h₂ : ∀ a b, H a b = ∑ e ∈ nonemptyDimParts k sY, H a (Pi.single e (b e)) := by
      intro a b
      conv_lhs => rw [← sum_pi_single_codimensionChowGroup sY j b]
      exact map_sum (AddMonoidHom.mk' (fun b ↦ H a b) fun b b' ↦ hH₂ a b b') _ _
    rw [h₁]
    exact Finset.sum_congr rfl fun d _ ↦ h₂ _ _
  rw [hl F hF₁ hF₂, hl G hG₁ hG₂]
  exact Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ h d e _ _

/-- **The tensor product of the correspondences of two cycles is the correspondence of their
exterior product**, on the correspondences of Section 0FFZ: for `α ∈ CH^i(X)` and `β ∈ CH^j(Y)`,
the tensor product `a_α ⊗ a_β ∈ Corr^{i+j}(Spec k × Spec k, X × Y)`, transported along
`Spec k × Spec k ≅ Spec k`, is `a_{α × β}`. -/
theorem corrEquivOfIso_tensor_corrFromPointEquiv [CompactSpace X] [CompactSpace Y]
    [CompactSpace (Limits.pullback sX sY : Scheme.{u})] (i j : ℤ)
    (α : codimensionChowGroup k sX i) (β : codimensionChowGroup k sY j) :
    corrEquivOfIso k (𝟙 (fieldChowSituation k).S)
        (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S))
        (prodBase sX sY) (prodBase sX sY)
        (Limits.pullback.fst (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S))
        (𝟙 _) rfl (Category.id_comp _) (i + j)
        (tensor k (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S) sX sY
          (canonicalDiagonalClassFamily k) i j
          (corrFromPointEquiv k sX i (codimensionToCodimChow k sX i α))
          (corrFromPointEquiv k sY j (codimensionToCodimChow k sY j β))) =
      corrFromPointEquiv k (prodBase sX sY) (i + j)
        (codimensionToCodimChow k (prodBase sX sY) (i + j)
          (codimensionExteriorProduct k sX sY i j α β)) := by
  refine biadditive_eq_of_pi_single k sX sY i j
    (F := fun α β ↦ corrEquivOfIso k (𝟙 (fieldChowSituation k).S)
        (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S))
        (prodBase sX sY) (prodBase sX sY)
        (Limits.pullback.fst (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S))
        (𝟙 _) rfl (Category.id_comp _) (i + j)
        (tensor k (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S) sX sY
          (canonicalDiagonalClassFamily k) i j
          (corrFromPointEquiv k sX i (codimensionToCodimChow k sX i α))
          (corrFromPointEquiv k sY j (codimensionToCodimChow k sY j β))))
    (G := fun α β ↦ corrFromPointEquiv k (prodBase sX sY) (i + j)
        (codimensionToCodimChow k (prodBase sX sY) (i + j)
          (codimensionExteriorProduct k sX sY i j α β))) ?_ ?_ ?_ ?_ ?_ α β
  · exact fun d e a b ↦ corrEquivOfIso_tensor_corrFromPointEquiv_single k sX sY i j d e a b
  · exact fun α α' β ↦ linearEquiv_bilinear_addMonoidHom_add_left _ _ _ _ _ _ α α' β
  · exact fun α β β' ↦ linearEquiv_bilinear_addMonoidHom_add_right _ _ _ _ _ _ α β β'
  · exact fun α α' β ↦ linearEquiv_addMonoidHom_bilinear_add_left _ _ _ α α' β
  · exact fun α β β' ↦ linearEquiv_addMonoidHom_bilinear_add_right _ _ _ α β β'

end Core

/-- Composing with the graph correspondence `[Γ_u]` of an isomorphism `u : Q ⟶ P` is transport
along `u`, read on the correspondences of the underlying schemes (Stacks 0FFZ, with the
proper-intersection formula of the canonical diagonal classes). -/
theorem comp_graphCorr_heq_corrEquivOfIso {P Q Y : (SmoothProjectiveScheme k).FullSubcategory}
    (u : Q ⟶ P) [IsIso u.hom.left] {s : ℤ} (h : SmoothProjectiveCorr Q Y s) :
    comp k P.obj.hom Q.obj.hom Y.obj.hom (canonicalDiagonalClassFamily k) 0 s
        (graphCorr k P.obj.hom Q.obj.hom u.hom.left (Over.w u.hom)) h ≍
      corrEquivOfIso k P.obj.hom Q.obj.hom Y.obj.hom Y.obj.hom u.hom.left (𝟙 _) (Over.w u.hom)
        (Category.id_comp _) s h :=
  (heq_of_eq (comp_graphCorr_left k P.obj.hom Q.obj.hom Y.obj.hom
    (canonicalDiagonalClassFamily_properIntersectionFormula k)
    (canonicalDiagonalClassFamily_isoInvariant k) u.hom.left (Over.w u.hom) s h)).trans
    (corrCongr_heq k _ _ _ _)

/-- `comp_graphCorr_heq_corrEquivOfIso`, for the composition of the category of
correspondences. -/
theorem canonicalComp_graphCorrespondenceSP_heq {P Q Y : (SmoothProjectiveScheme k).FullSubcategory}
    (u : Q ⟶ P) [IsIso u.hom.left] {s : ℤ} (h : SmoothProjectiveCorr Q Y s) :
    (canonicalCorrespondenceCompositionData k).comp (graphCorrespondenceSP u) h ≍
      corrEquivOfIso k P.obj.hom Q.obj.hom Y.obj.hom Y.obj.hom u.hom.left (𝟙 _) (Over.w u.hom)
        (Category.id_comp _) s h := by
  rw [comp_eq_comp, graphCorrespondenceSP_eq]
  exact comp_graphCorr_heq_corrEquivOfIso u h

/-- Composing with the graph `[Γ_u]` of an isomorphism `u : Q ⟶ P` is transport along `u`. -/
theorem graphHom_comp_of {P Q Y : (SmoothProjectiveScheme k).FullSubcategory} (u : Q ⟶ P)
    [IsIso u.hom.left] {s : ℤ} (h : SmoothProjectiveCorr Q Y s) :
    (graphHom u : 𝐎 P ⟶ 𝐎 Q) ≫ (DirectSum.of (fun i ↦ SmoothProjectiveCorr Q Y i) s h :
        𝐎 Q ⟶ 𝐎 Y) =
      DirectSum.of (fun i ↦ SmoothProjectiveCorr P Y i) s
        (corrEquivOfIso k P.obj.hom Q.obj.hom Y.obj.hom Y.obj.hom u.hom.left (𝟙 _) (Over.w u.hom)
          (Category.id_comp _) s h) := by
  rw [graphHom, GradedCompositionData.of_comp_of (canonicalCorrespondenceCompositionData k)
    (X := 𝐎 P) (Y := 𝐎 Q) (Z := 𝐎 Y) (graphCorrespondenceSP u) h]
  dsimp only
  exact of_eq_of_heq (zero_add s) (canonicalComp_graphCorrespondenceSP_heq u h)

/-- The correspondence of Stacks 0FG0 (3) attached to a class is the correspondence of
Section 0FFZ given by `Stacks.WeilCohomology.corrFromPointEquiv`. -/
theorem pointCorrEquiv_eq_corrFromPointEquiv (X : (SmoothProjectiveScheme k).FullSubcategory)
    (r : ℤ) (x : CodimChow k X.obj.hom r) :
    @Eq (SmoothProjectiveCorr (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) X r)
      (pointCorrEquiv X r x) (corrFromPointEquiv k X.obj.hom r x) :=
  rfl

/-- **The tensor product of the correspondences of two cycles** (Stacks 0FH1, proof of (C)(c)):
for `α ∈ CH^i(X)` and `β ∈ CH^j(Y)`, with `X` and `Y` smooth projective over `k` of any
dimensions, `ρ⁻¹ ≫ (a_α ⊗ a_β) = a_{α × β}` in the category of correspondences, where
`ρ : Spec k ⊗ Spec k ≅ Spec k` is the right unit constraint and `α × β ∈ CH^{i+j}(X × Y)` is the
exterior product. -/
theorem tensorHom_pointCorrHom (X Y : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) (β : codimensionChowGroup k Y.obj.hom j) :
    (CorrespondenceCategory.rightUnitorIso
        (𝐎 (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)))).inv ≫
        CorrespondenceCategory.tensorHom (pointCorrHom X i α) (pointCorrHom Y j β) =
      pointCorrHom (X ⊗ Y) (i + j) (codimensionExteriorProduct k X.obj.hom Y.obj.hom i j α β) := by
  have : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  have : CompactSpace Y.obj.left := QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
  have : CompactSpace (X ⊗ Y).obj.left :=
    QuasiCompact.compactSpace_of_compactSpace (X ⊗ Y).obj.hom
  rw [graphIso_inv, pointCorrHom_apply, pointCorrHom_apply, pointCorrHom_apply, homOf, homOf,
    homOf, DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.lof_eq_of, tensorHom_of_of,
    graphHom_comp_of]
  refine congrArg _ ?_
  dsimp only [CorrespondenceCategory.tensorUnit]
  have h := corrEquivOfIso_tensor_corrFromPointEquiv k X.obj.hom Y.obj.hom i j α β
  have hc := (tensorCorr_heq (pointCorrEquiv X i (codimensionToCodimChow k X.obj.hom i α))
    (pointCorrEquiv Y j (codimensionToCodimChow k Y.obj.hom j β))).trans
    (tensor_heq k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
    (𝟙 (fieldChowSituation k).S) (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
    (𝟙 (fieldChowSituation k).S) X.obj.hom X.obj.hom Y.obj.hom
    Y.obj.hom rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl
    (canonicalDiagonalClassFamily k) i j _ _
    (heq_of_eq (pointCorrEquiv_eq_corrFromPointEquiv X i _)) _ _
    (heq_of_eq (pointCorrEquiv_eq_corrFromPointEquiv Y j _)))
  refine eq_of_heq (HEq.trans ?_ ((heq_of_eq h).trans
    (heq_of_eq (pointCorrEquiv_eq_corrFromPointEquiv (X ⊗ Y) (i + j) _).symm)))
  have hE := corrEquivOfIso_heq k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
    (𝟙 (fieldChowSituation k).S)
    (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗
      𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
    (prodBase (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S))
    (X ⊗ Y).obj.hom (prodBase X.obj.hom Y.obj.hom) (X ⊗ Y).obj.hom (prodBase X.obj.hom Y.obj.hom)
    rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl
    (ρ_ (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))).hom.hom.left (𝟙 _) (Over.w _)
    (Category.id_comp _)
    (Limits.pullback.fst (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S)) (𝟙 _) rfl
    (Category.id_comp _) HEq.rfl HEq.rfl (i + j) _ _ hc
  refine hE.trans ?_
  -- `hE` and `h` state the same correspondence; the instance arguments synthesized for the two
  -- spellings are compared through the congruence lemmas rather than by unfolding.
  refine corrEquivOfIso_heq k _ _ _ _ _ _ _ _ rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl
    _ _ _ _ _ _ _ _ HEq.rfl HEq.rfl (i + j) _ _ ?_
  refine tensor_heq k _ _ _ _ _ _ _ _ rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl _ i j _ _
    ?_ _ _ ?_
  · exact HEq.rfl
  · exact HEq.rfl

end Stacks.WeilCohomology

end
