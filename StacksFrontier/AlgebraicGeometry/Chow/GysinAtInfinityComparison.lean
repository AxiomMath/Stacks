module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescentExistence
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityClass

/-!
# Comparing the construction of the class at infinity for two modifications

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. For `i = 1, 2` let
`X_i` be locally of finite type over `S`, let `b_i : W_i ⟶ 𝐏¹_{X_i}` be proper and an isomorphism
over `𝐀¹_{X_i}`, and let `g_i : T ⟶ X_i` be test schemes with the same source, lying over the
same morphism `T ⟶ S`. Stacks 0F9J computes the cap operation of its class at infinity on `T` as
`C_i ∩ α = i_∞^* β_i`, for a class `β_i` on `W_i ×_{X_i} T` restricting over the affine chart to
the flat pullback of `α`.

Both lemmas that compare two such classes — Stacks 0FAQ, for a proper `g : W' ⟶ W` which is an
isomorphism over `𝐀¹_X`, and Stacks 0GUH, for a base change `X' ⟶ X` — come down to one
comparison. Let `φ : W_1 ×_{X_1} T ⟶ W_2 ×_{X_2} T` be proper, over `T`, and compatible with the
two maps to `𝐏¹_S`, and let `φ_∞` be a morphism of the fibres at infinity compatible with `φ`.
Then

* `φ` carries the chart over `𝐀¹` of the first base change *isomorphically* onto that of the
  second, both being the affine line over `T`;
* hence the pushforward `φ_* β` of a lift of `α` is a lift of `α` (Stacks 02RG for the chart);
* and `i_∞^* (φ_* β) = φ_{∞,*} (i_∞^* β)` (Stacks 02TA for the pulled-back divisor at infinity).

Together, `C_2 ∩ α = φ_{∞,*} (C_1 ∩ α)`.

## Main definitions

* `Stacks.Chow.modificationAffineChartComparison` — the morphism of charts over `𝐀¹` induced by
  `φ`.

## Main results

* `Stacks.Chow.isPullback_modificationAffineChartComparison` — the chart of the first base
  change is the inverse image under `φ` of the chart of the second.
* `Stacks.Chow.isIso_modificationAffineChartComparison` — the induced morphism of charts is an
  isomorphism.
* `Stacks.Chow.IsModificationLift.properChowPushforward_of_comparison` — the pushforward along
  `φ` of a lift is a lift.
* `Stacks.Chow.gysinCapOfLift_comparison` — `C_2 ∩ α = φ_{∞,*} (C_1 ∩ α)`.

The third step, the commutation of the Gysin map at infinity with pushforward along `φ`, is
`Stacks.Chow.modificationInfinityGysin_properChowPushforward_of_comparison`, proved with the other
behaviour of the construction under morphisms of test schemes.

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0FAQ](https://stacks.math.columbia.edu/tag/0FAQ)
* [Stacks Project, Tag 0GUH](https://stacks.math.columbia.edu/tag/0GUH)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The chart over `𝐀¹` as an inverse image in `𝐏¹_S` -/

section Geometry

/-- The chart `b^{-1}(𝐀¹_X) ×_X T` is the inverse image in `W ×_X T` of the affine chart of
`𝐏¹_S`. -/
theorem isPullback_modificationAffineChart_relativeLine {X S W T : Scheme.{u}} (f : X ⟶ S)
    (b : W ⟶ projectiveLineProduct f) (g : T ⟶ X) :
    IsPullback (pullback.snd (modificationBaseChangeToLine f b g) (projectiveLineAffineChart f) ≫
        affineLineOverMap f)
      (modificationAffineChartι f b g) (affineChart S)
      (modificationBaseChangeToRelativeLine f b g) :=
  (IsPullback.of_hasPullback _ _).flip.paste_horiz
    (isPullback_affineLineOverMap_projectiveLineAffineChart f)

variable {S X₁ X₂ W₁ W₂ T : Scheme.{u}} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
  {b₁ : W₁ ⟶ projectiveLineProduct f₁} {b₂ : W₂ ⟶ projectiveLineProduct f₂}
  {g₁ : T ⟶ X₁} {g₂ : T ⟶ X₂}
  (φ : modificationBaseChange f₁ b₁ g₁ ⟶ modificationBaseChange f₂ b₂ g₂)
  (hφ : φ ≫ modificationBaseChangeToRelativeLine f₂ b₂ g₂ =
    modificationBaseChangeToRelativeLine f₁ b₁ g₁)

include hφ in
/-- The morphism of charts over `𝐀¹` induced by a morphism `φ` of base-changed modifications
compatible with the maps to `𝐏¹_S`. -/
def modificationAffineChartComparison :
    modificationAffineChart f₁ b₁ g₁ ⟶ modificationAffineChart f₂ b₂ g₂ :=
  (isPullback_modificationAffineChart_relativeLine f₂ b₂ g₂).lift
    (pullback.snd _ _ ≫ affineLineOverMap f₁) (modificationAffineChartι f₁ b₁ g₁ ≫ φ)
    (by
      rw [Category.assoc (modificationAffineChartι f₁ b₁ g₁), hφ]
      exact (isPullback_modificationAffineChart_relativeLine f₁ b₁ g₁).w)

/-- The morphism of charts preserves the coordinate in `𝐀¹_S`. -/
@[reassoc (attr := simp)]
theorem modificationAffineChartComparison_coordinate :
    modificationAffineChartComparison φ hφ ≫
        (pullback.snd (modificationBaseChangeToLine f₂ b₂ g₂) (projectiveLineAffineChart f₂) ≫
          affineLineOverMap f₂) =
      pullback.snd (modificationBaseChangeToLine f₁ b₁ g₁) (projectiveLineAffineChart f₁) ≫
        affineLineOverMap f₁ :=
  IsPullback.lift_fst _ _ _ _

/-- The morphism of charts lies over `φ`. -/
@[reassoc (attr := simp)]
theorem modificationAffineChartComparison_ι :
    modificationAffineChartComparison φ hφ ≫ modificationAffineChartι f₂ b₂ g₂ =
      modificationAffineChartι f₁ b₁ g₁ ≫ φ :=
  IsPullback.lift_snd _ _ _ _

/-- **The chart over `𝐀¹` is an inverse image under `φ`.** -/
theorem isPullback_modificationAffineChartComparison :
    IsPullback (modificationAffineChartι f₁ b₁ g₁) (modificationAffineChartComparison φ hφ) φ
      (modificationAffineChartι f₂ b₂ g₂) := by
  refine IsPullback.of_bot ?_ (modificationAffineChartComparison_ι φ hφ).symm
    (isPullback_modificationAffineChart_relativeLine f₂ b₂ g₂).flip
  rw [modificationAffineChartComparison_coordinate, hφ]
  exact (isPullback_modificationAffineChart_relativeLine f₁ b₁ g₁).flip

/-- A morphism of base-changed modifications over the test scheme is a morphism over the base. -/
theorem comp_modificationBaseChangeOver_of_comp_snd (hT : g₁ ≫ f₁ = g₂ ≫ f₂)
    (hφT : φ ≫ pullback.snd (modificationProjection f₂ b₂) g₂ =
      pullback.snd (modificationProjection f₁ b₁) g₁) :
    φ ≫ modificationBaseChangeOver f₂ b₂ g₂ = modificationBaseChangeOver f₁ b₁ g₁ := by
  rw [← modificationBaseChange_snd_over, ← modificationBaseChange_snd_over, ← hT,
    ← Category.assoc, hφT]

variable (hφT : φ ≫ pullback.snd (modificationProjection f₂ b₂) g₂ =
  pullback.snd (modificationProjection f₁ b₁) g₁)

include hφT in
/-- The morphism of charts lies over the test scheme. -/
theorem modificationAffineChartComparison_projection :
    modificationAffineChartComparison φ hφ ≫ modificationAffineChartProjection f₂ b₂ g₂ =
      modificationAffineChartProjection f₁ b₁ g₁ := by
  rw [modificationAffineChartProjection, modificationAffineChartComparison_ι_assoc, hφT]

include hφT in
/-- **The morphism of charts is an isomorphism.** When both modifications are isomorphisms over
`𝐀¹`, each chart is the affine line over `T`, and the morphism of charts preserves the coordinate
and the projection to `T`. -/
theorem isIso_modificationAffineChartComparison (hT : g₁ ≫ f₁ = g₂ ≫ f₂)
    (hA₁ : IsIso (pullback.snd b₁ (projectiveLineAffineChart f₁)))
    (hA₂ : IsIso (pullback.snd b₂ (projectiveLineAffineChart f₂))) :
    IsIso (modificationAffineChartComparison φ hφ) := by
  have h₁ := isPullback_modificationAffineChart_affineLineOverMap f₁ b₁ g₁ hA₁
  have h₂ := isPullback_modificationAffineChart_affineLineOverMap f₂ b₂ g₂ hA₂
  rw [hT] at h₁
  have he : modificationAffineChartComparison φ hφ = (h₁.isoIsPullback _ _ h₂).hom := by
    refine h₂.hom_ext ?_ ?_
    · rw [IsPullback.isoIsPullback_hom_fst, modificationAffineChartComparison_coordinate]
    · rw [IsPullback.isoIsPullback_hom_snd, modificationAffineChartComparison_projection φ hφ hφT]
  rw [he]
  infer_instance

end Geometry

/-! ### Lifts and the Gysin map at infinity under a comparison -/

section Comparison

variable (C : ChowSituation.{u}) {X₁ X₂ W₁ W₂ T : Scheme.{u}} {f₁ : X₁ ⟶ C.S}
  [LocallyOfFiniteType f₁] {f₂ : X₂ ⟶ C.S} [LocallyOfFiniteType f₂]
  {b₁ : W₁ ⟶ projectiveLineProduct f₁} [IsProper b₁] {b₂ : W₂ ⟶ projectiveLineProduct f₂}
  [IsProper b₂] {g₁ : T ⟶ X₁} [LocallyOfFiniteType g₁] {g₂ : T ⟶ X₂} [LocallyOfFiniteType g₂]
  (φ : modificationBaseChange f₁ b₁ g₁ ⟶ modificationBaseChange f₂ b₂ g₂)

variable [IsProper φ]

/-- **The pushforward of a lift along a comparison is a lift** (Stacks 02RG). Let
`φ : W_1 ×_{X_1} T ⟶ W_2 ×_{X_2} T` be proper, over `T` and over `𝐏¹_S`. If `β` lifts `α`
for the first modification, then `φ_* β` lifts `α` for the second: restriction to the chart
commutes with `φ_*` because the first chart is the inverse image of the second, and the morphism
of charts is an isomorphism over `T`, along which flat pullback is pushforward. -/
theorem IsModificationLift.properChowPushforward_of_comparison (hT : g₁ ≫ f₁ = g₂ ≫ f₂)
    (hA₁ : IsIso (pullback.snd b₁ (projectiveLineAffineChart f₁)))
    (hA₂ : IsIso (pullback.snd b₂ (projectiveLineAffineChart f₂)))
    (hφT : φ ≫ pullback.snd (modificationProjection f₂ b₂) g₂ =
      pullback.snd (modificationProjection f₁ b₁) g₁)
    (hφ : φ ≫ modificationBaseChangeToRelativeLine f₂ b₂ g₂ =
      modificationBaseChangeToRelativeLine f₁ b₁ g₁) (k : ℤ)
    {α : chowGroup C (g₁ ≫ f₁) k} {β : chowGroup C (modificationBaseChangeOver f₁ b₁ g₁) (k + 1)}
    (hβ : IsModificationLift C f₁ b₁ hA₁ g₁ k α β) :
    IsModificationLift C f₂ b₂ hA₂ g₂ k (chowGroupCongr C hT k α)
      (properChowPushforward C (modificationBaseChangeOver f₁ b₁ g₁)
        (modificationBaseChangeOver f₂ b₂ g₂) φ
        (comp_modificationBaseChangeOver_of_comp_snd φ hT hφT) (k + 1)
        (properPushforwardDescends C _ _ _ _ _) β) := by
  have := isIso_modificationAffineChartComparison φ hφ hφT hT hA₁ hA₂
  have := flat_modificationAffineChartProjection f₁ b₁ g₁ hA₁
  have := flat_modificationAffineChartProjection f₂ b₂ g₂ hA₂
  have hψ : modificationAffineChartComparison φ hφ ≫ modificationAffineChartOver C f₂ b₂ g₂ =
      modificationAffineChartOver C f₁ b₁ g₁ := by
    rw [modificationAffineChartOver, modificationAffineChartComparison_ι_assoc,
      comp_modificationBaseChangeOver_of_comp_snd φ hT hφT]
  have hsq : IsPullback (modificationAffineChartProjection f₁ b₁ g₁)
      (modificationAffineChartComparison φ hφ) (𝟙 T) (modificationAffineChartProjection f₂ b₂ g₂) :=
    IsPullback.of_vert_isIso ⟨by
      rw [Category.comp_id, modificationAffineChartComparison_projection φ hφ hφT]⟩
  unfold IsModificationLift at hβ ⊢
  rw [chowGroupRestrict_properChowPushforward C (modificationBaseChangeOver f₁ b₁ g₁)
      (modificationBaseChangeOver f₂ b₂ g₂) (modificationAffineChartOver C f₁ b₁ g₁)
      (modificationAffineChartOver C f₂ b₂ g₂) φ
      (comp_modificationBaseChangeOver_of_comp_snd φ hT hφT) (modificationAffineChartι f₁ b₁ g₁)
      rfl (modificationAffineChartι f₂ b₂ g₂) rfl (modificationAffineChartComparison φ hφ) hψ
      (isPullback_modificationAffineChartComparison φ hφ) (k + 1) _
      (properPushforwardDescends C _ _ _ _ _) β, hβ]
  have h02RG := flatPullbackChow_properChowPushforward_of_isProper C (g₁ ≫ f₁) (g₂ ≫ f₂)
    (modificationAffineChartOver C f₁ b₁ g₁) (modificationAffineChartOver C f₂ b₂ g₂) (𝟙 T)
    (modificationAffineChartProjection f₂ b₂ g₂) (modificationAffineChartProjection f₁ b₁ g₁)
    (modificationAffineChartComparison φ hφ) hsq (by rw [Category.id_comp, hT])
    (modificationAffineChartProjection_over C f₂ b₂ g₂)
    (modificationAffineChartProjection_over C f₁ b₁ g₁) 1
    (relativeDimension_modificationAffineChartProjection f₂ b₂ g₂ hA₂) k α
  refine Eq.trans ?_ (h02RG.symm.trans ?_)
  · rfl
  · exact DFunLike.congr_arg _ (chowPush_id_eq_chowGroupCongr C (g₁ ≫ f₁) (g₂ ≫ f₂) _ k α)

variable (φInf : pullback (modificationProjectionAtInfinity f₁ b₁) g₁ ⟶
    pullback (modificationProjectionAtInfinity f₂ b₂) g₂) [IsProper φInf]

/-- **The cap operations of two classes at infinity under a comparison.** For
`φ : W_1 ×_{X_1} T ⟶ W_2 ×_{X_2} T` proper, over `T` and over `𝐏¹_S`, and `φ_∞` a morphism of the
base-changed fibres at infinity compatible with it, the cap operation of Stacks 0F9J for the second
modification is the pushforward along `φ_∞` of the one for the first:
`C_2 ∩ α = φ_{∞,*} (C_1 ∩ α)`. Pick a lift `β` of `α` on `W_1 ×_{X_1} T`; then `φ_* β` is a lift on
`W_2 ×_{X_2} T`, and `i_∞^* (φ_* β) = φ_{∞,*} (i_∞^* β)`. -/
theorem gysinCapOfLift_comparison (hT : g₁ ≫ f₁ = g₂ ≫ f₂)
    (hA₁ : IsIso (pullback.snd b₁ (projectiveLineAffineChart f₁)))
    (hA₂ : IsIso (pullback.snd b₂ (projectiveLineAffineChart f₂)))
    (hφT : φ ≫ pullback.snd (modificationProjection f₂ b₂) g₂ =
      pullback.snd (modificationProjection f₁ b₁) g₁)
    (hφ : φ ≫ modificationBaseChangeToRelativeLine f₂ b₂ g₂ =
      modificationBaseChangeToRelativeLine f₁ b₁ g₁)
    (hφInf : φInf ≫ modificationInfinityBaseChange f₂ b₂ g₂ =
      modificationInfinityBaseChange f₁ b₁ g₁ ≫ φ) (k : ℤ) (α : chowGroup C (g₁ ≫ f₁) k) :
    gysinCapAtInfinity C f₂ b₂ hA₂ g₂ k (chowGroupCongr C hT k α) =
      properChowPushforward C (modificationInfinityBaseChangeOver f₁ b₁ g₁)
        (modificationInfinityBaseChangeOver f₂ b₂ g₂) φInf
        (comp_modificationInfinityBaseChangeOver_of_comp φ
          (comp_modificationBaseChangeOver_of_comp_snd φ hT hφT) φInf hφInf) k
        (properPushforwardDescends C _ _ _ _ _) (gysinCapAtInfinity C f₁ b₁ hA₁ g₁ k α) := by
  obtain ⟨β, hβ⟩ := exists_isModificationLift C f₁ b₁ hA₁ g₁ k α
  rw [gysinCapAtInfinity_eq_of_isModificationLift C f₁ b₁ hA₁ g₁ k α β hβ,
    gysinCapAtInfinity_eq_of_isModificationLift C f₂ b₂ hA₂ g₂ k _ _
      (hβ.properChowPushforward_of_comparison C φ hT hA₁ hA₂ hφT hφ k)]
  exact modificationInfinityGysin_properChowPushforward_of_comparison C φ φInf k _ hφ hφInf β

end Comparison

end Stacks.Chow

end
