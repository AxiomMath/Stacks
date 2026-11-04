module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityLift
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquarePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquareFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardPulledBackModule
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackPulledBackModule

/-!
# The construction of the class at infinity along a morphism of test schemes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, and let
`h : T' ⟶ T` be a morphism of schemes over `X`, with `T ⟶ X` locally of finite type. The
construction of Stacks 0F9J on `T` and on `T'` is related by the base change `W ×_X T' ⟶ W ×_X T`
of `h`, which carries the chart over `𝐀¹_X` and the fibre at infinity of the one to those of the
other. This file records that geometry, and the behaviour of the two halves of the construction —
the lifts and the Gysin map at infinity — under proper pushforward and flat pullback along `h`.

## Main definitions

* `Stacks.Chow.modificationAffineChartMap` — the map of the charts over `𝐀¹_X` induced by `h`.

## Main results

* `Stacks.Chow.isPullback_modificationAffineChartMap` — the chart over `𝐀¹_X` of `W ×_X T'` is
  the inverse image of that of `W ×_X T`.
* `Stacks.Chow.isPullback_modificationAffineChartProjection_map` — the projections of the two
  charts to `T'` and `T` form a cartesian square.
* `Stacks.Chow.IsModificationLift.properPushforward` — the pushforward of a lift is a lift of
  the pushforward (Stacks 02RG).
* `Stacks.Chow.modificationInfinityGysin_properChowPushforward_of_comparison` — the Gysin map at
  infinity commutes with pushforward along any proper morphism of base-changed modifications
  compatible with the maps to `𝐏¹_S` (Stacks 02TA).
* `Stacks.Chow.modificationInfinityGysin_properChowPushforward` — the Gysin map at infinity
  commutes with proper pushforward along `h` (Stacks 02TA).
* `Stacks.Chow.gysinCapOfLift_properChowPushforward` — the cap operation at infinity commutes with
  proper pushforward along `h` (Stacks 0B76 (1)).
* `Stacks.Chow.IsModificationLift.flatPullback` — the flat pullback of a lift is a lift of the
  flat pullback (Stacks 02RD).
* `Stacks.Chow.modificationInfinityGysin_flatPullbackChow` — the Gysin map at infinity commutes
  with flat pullback along `h` (Stacks 0B71).
* `Stacks.Chow.gysinCapOfLift_flatPullbackChow` — the cap operation at infinity commutes with
  flat pullback along `h` (Stacks 0B76 (2)).

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Geometry

variable {X S W T T' : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (g : T ⟶ X)
  (h : T' ⟶ T)

/-- The base change of `h` to the modification is compatible with the maps to `W`. -/
@[reassoc (attr := simp)]
theorem modificationBaseChangeMap_fst :
    bivariantBaseChangeMap (modificationProjection f b) g h ≫
        pullback.fst (modificationProjection f b) g =
      pullback.fst (modificationProjection f b) (h ≫ g) :=
  bivariantBaseChangeMap_fst _ _ _

/-- The base change of `h` to the modification is compatible with the coordinates. -/
@[reassoc (attr := simp)]
theorem modificationBaseChangeMap_toLine :
    bivariantBaseChangeMap (modificationProjection f b) g h ≫ modificationBaseChangeToLine f b g =
      modificationBaseChangeToLine f b (h ≫ g) := by
  rw [modificationBaseChangeToLine, modificationBaseChangeMap_fst_assoc]

/-- The base change of `h` to the modification is compatible with the coordinates in `𝐏¹_S`. -/
@[reassoc (attr := simp)]
theorem modificationBaseChangeMap_toRelativeLine :
    bivariantBaseChangeMap (modificationProjection f b) g h ≫
        modificationBaseChangeToRelativeLine f b g =
      modificationBaseChangeToRelativeLine f b (h ≫ g) := by
  rw [modificationBaseChangeToRelativeLine, modificationBaseChangeToRelativeLine,
    ← Category.assoc, modificationBaseChangeMap_toLine]

/-- The map of the charts over `𝐀¹_X` induced by `h`. -/
def modificationAffineChartMap :
    modificationAffineChart f b (h ≫ g) ⟶ modificationAffineChart f b g :=
  pullback.lift (modificationAffineChartι f b (h ≫ g) ≫
      bivariantBaseChangeMap (modificationProjection f b) g h)
    (pullback.snd _ _) (by rw [Category.assoc, modificationBaseChangeMap_toLine,
      pullback.condition])

/-- The map of the charts is compatible with their open immersions into `W ×_X T'` and `W ×_X T`
and the base change of `h`. -/
@[reassoc (attr := simp)]
theorem modificationAffineChartMap_ι :
    modificationAffineChartMap f b g h ≫ modificationAffineChartι f b g =
      modificationAffineChartι f b (h ≫ g) ≫
        bivariantBaseChangeMap (modificationProjection f b) g h :=
  pullback.lift_fst _ _ _

/-- The map of the charts is compatible with their projections to `𝐀¹_X`. -/
@[reassoc (attr := simp)]
theorem modificationAffineChartMap_snd :
    modificationAffineChartMap f b g h ≫
        pullback.snd (modificationBaseChangeToLine f b g) (projectiveLineAffineChart f) =
      pullback.snd (modificationBaseChangeToLine f b (h ≫ g)) (projectiveLineAffineChart f) :=
  pullback.lift_snd _ _ _

/-- **The chart over `𝐀¹_X` of `W ×_X T'` is the inverse image of that of `W ×_X T`.** -/
theorem isPullback_modificationAffineChartMap :
    IsPullback (modificationAffineChartι f b (h ≫ g)) (modificationAffineChartMap f b g h)
      (bivariantBaseChangeMap (modificationProjection f b) g h)
      (modificationAffineChartι f b g) := by
  refine (IsPullback.of_right ?_ (modificationAffineChartMap_ι f b g h)
    (IsPullback.of_hasPullback (modificationBaseChangeToLine f b g)
      (projectiveLineAffineChart f)).flip).flip
  rw [modificationAffineChartMap_snd, modificationBaseChangeMap_toLine]
  exact (IsPullback.of_hasPullback _ _).flip

/-- The map of the charts lies over `h`. -/
@[reassoc (attr := simp)]
theorem modificationAffineChartMap_projection :
    modificationAffineChartMap f b g h ≫ modificationAffineChartProjection f b g =
      modificationAffineChartProjection f b (h ≫ g) ≫ h := by
  rw [modificationAffineChartProjection, modificationAffineChartMap_ι_assoc,
    modificationAffineChartProjection, Category.assoc]
  congr 1
  exact (isPullback_bivariantBaseChangeMap _ _ _).w.symm

/-- **The projections of the two charts form a cartesian square over `h`.** -/
theorem isPullback_modificationAffineChartProjection_map :
    IsPullback (modificationAffineChartMap f b g h) (modificationAffineChartProjection f b (h ≫ g))
      (modificationAffineChartProjection f b g) h :=
  (isPullback_modificationAffineChartMap f b g h).flip.paste_vert
    (isPullback_bivariantBaseChangeMap (modificationProjection f b) g h).flip

/-- The base change of `h` carries the fibre at infinity of `W ×_X T'` into that of `W ×_X T`: any
morphism of the two fibres over `h` and over `W_∞` is compatible with the two inclusions. -/
theorem modificationInfinityBaseChange_comp_map
    (h' : pullback (modificationProjectionAtInfinity f b) (h ≫ g) ⟶
      pullback (modificationProjectionAtInfinity f b) g)
    (hsnd : h' ≫ pullback.snd (modificationProjectionAtInfinity f b) g =
      pullback.snd (modificationProjectionAtInfinity f b) (h ≫ g) ≫ h)
    (hfst : h' ≫ pullback.fst (modificationProjectionAtInfinity f b) g =
      pullback.fst (modificationProjectionAtInfinity f b) (h ≫ g)) :
    h' ≫ modificationInfinityBaseChange f b g =
      modificationInfinityBaseChange f b (h ≫ g) ≫
        bivariantBaseChangeMap (modificationProjection f b) g h := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, modificationInfinityBaseChange_comp_fst, ← Category.assoc, hfst,
      Category.assoc, modificationBaseChangeMap_fst, modificationInfinityBaseChange_comp_fst]
  · rw [Category.assoc, modificationInfinityBaseChange_comp_snd, hsnd, Category.assoc,
      ← (isPullback_bivariantBaseChangeMap _ _ _).w, ← Category.assoc,
      modificationInfinityBaseChange_comp_snd]

/-- If `h` is proper, then so is the map of the charts over `𝐀¹_X` induced by `h`. -/
theorem isProper_modificationAffineChartMap [IsProper h] :
    IsProper (modificationAffineChartMap f b g h) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
    (isPullback_modificationAffineChartMap f b g h) inferInstance

/-- The base change of `h` to the modification is a morphism over the base. -/
theorem modificationBaseChangeMap_over :
    bivariantBaseChangeMap (modificationProjection f b) g h ≫ modificationBaseChangeOver f b g =
      modificationBaseChangeOver f b (h ≫ g) := by
  rw [modificationBaseChangeOver, modificationBaseChangeMap_fst_assoc]

/-- The base change of a morphism locally of finite type between two base changes. -/
instance locallyOfFiniteType_bivariantBaseChangeMap {X Y T T' : Scheme.{u}} (f : X ⟶ Y)
    (g : T ⟶ Y) (h : T' ⟶ T) [LocallyOfFiniteType h] :
    LocallyOfFiniteType (bivariantBaseChangeMap f g h) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    (isPullback_bivariantBaseChangeMap f g h) inferInstance

/-- The base change of a flat morphism between two base changes. -/
instance flat_bivariantBaseChangeMap {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    (h : T' ⟶ T) [Flat h] : Flat (bivariantBaseChangeMap f g h) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_bivariantBaseChangeMap f g h)
    inferInstance

/-- The base change of a morphism of relative dimension `r` between two base changes has relative
dimension `r` (Stacks 02NK). -/
theorem bivariantBaseChangeMap_relativeDimension {X Y T T' : Scheme.{u}} (f : X ⟶ Y)
    (g : T ⟶ Y) (h : T' ⟶ T) [LocallyOfFiniteType h] {r : ℕ} (hr : RelativeDimension h r) :
    RelativeDimension (bivariantBaseChangeMap f g h) r :=
  RelativeDimension.of_isPullback (isPullback_bivariantBaseChangeMap f g h) hr

/-- If `h` is locally of finite type, then so is the map of the charts induced by `h`. -/
instance locallyOfFiniteType_modificationAffineChartMap [LocallyOfFiniteType h] :
    LocallyOfFiniteType (modificationAffineChartMap f b g h) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    (isPullback_modificationAffineChartMap f b g h) inferInstance

/-- If `h` is flat, then so is the map of the charts induced by `h`. -/
instance flat_modificationAffineChartMap [Flat h] : Flat (modificationAffineChartMap f b g h) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_modificationAffineChartMap f b g h)
    inferInstance

/-- If `h` has relative dimension `r`, then so does the map of the charts induced by `h`. -/
theorem relativeDimension_modificationAffineChartMap [LocallyOfFiniteType h] {r : ℕ}
    (hr : RelativeDimension h r) : RelativeDimension (modificationAffineChartMap f b g h) r :=
  RelativeDimension.of_isPullback (isPullback_modificationAffineChartMap f b g h)
    (bivariantBaseChangeMap_relativeDimension _ g h hr)

end Geometry

/-! ### The Gysin map at infinity along a morphism of base-changed modifications -/

section Comparison

variable {S X₁ X₂ W₁ W₂ T₁ T₂ : Scheme.{u}} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
  {b₁ : W₁ ⟶ projectiveLineProduct f₁} {b₂ : W₂ ⟶ projectiveLineProduct f₂}
  {g₁ : T₁ ⟶ X₁} {g₂ : T₂ ⟶ X₂}
  (φ : modificationBaseChange f₁ b₁ g₁ ⟶ modificationBaseChange f₂ b₂ g₂)

/-- A morphism of base-changed fibres at infinity compatible with a morphism of base-changed
modifications over the base is a morphism over the base. -/
theorem comp_modificationInfinityBaseChangeOver_of_comp
    (hφover : φ ≫ modificationBaseChangeOver f₂ b₂ g₂ = modificationBaseChangeOver f₁ b₁ g₁)
    (φInf : pullback (modificationProjectionAtInfinity f₁ b₁) g₁ ⟶
      pullback (modificationProjectionAtInfinity f₂ b₂) g₂)
    (hφInf : φInf ≫ modificationInfinityBaseChange f₂ b₂ g₂ =
      modificationInfinityBaseChange f₁ b₁ g₁ ≫ φ) :
    φInf ≫ modificationInfinityBaseChangeOver f₂ b₂ g₂ =
      modificationInfinityBaseChangeOver f₁ b₁ g₁ := by
  rw [← modificationInfinityBaseChange_over, ← modificationInfinityBaseChange_over,
    ← Category.assoc, hφInf, Category.assoc, hφover]

/-- A morphism of base-changed modifications compatible with the maps to `𝐏¹_S` and with a morphism
`φ_∞` of the fibres at infinity restricts to a morphism of the zero schemes of the pulled-back
canonical sections, which is the base change of `φ` and is compatible with `φ_∞`. -/
private theorem exists_isPullback_zeroScheme_infinity
    (hφ : φ ≫ modificationBaseChangeToRelativeLine f₂ b₂ g₂ =
      modificationBaseChangeToRelativeLine f₁ b₁ g₁)
    (φInf : pullback (modificationProjectionAtInfinity f₁ b₁) g₁ ⟶
      pullback (modificationProjectionAtInfinity f₂ b₂) g₂)
    (hφInf : φInf ≫ modificationInfinityBaseChange f₂ b₂ g₂ =
      modificationInfinityBaseChange f₁ b₁ g₁ ≫ φ) :
    ∃ J : (Stacks.Divisors.zeroScheme (modificationBaseChange f₁ b₁ g₁)
        (modificationInfinityModule f₁ b₁ g₁) (modificationInfinitySection f₁ b₁ g₁)).subscheme ⟶
      (Stacks.Divisors.zeroScheme (modificationBaseChange f₂ b₂ g₂)
        (modificationInfinityModule f₂ b₂ g₂) (modificationInfinitySection f₂ b₂ g₂)).subscheme,
    IsPullback (Stacks.Divisors.zeroScheme (modificationBaseChange f₁ b₁ g₁)
        (modificationInfinityModule f₁ b₁ g₁) (modificationInfinitySection f₁ b₁ g₁)).subschemeι
      J φ (Stacks.Divisors.zeroScheme (modificationBaseChange f₂ b₂ g₂)
        (modificationInfinityModule f₂ b₂ g₂) (modificationInfinitySection f₂ b₂ g₂)).subschemeι ∧
    J ≫ (modificationInfinityZeroSchemeIso f₂ b₂ g₂).hom =
      (modificationInfinityZeroSchemeIso f₁ b₁ g₁).hom ≫ φInf := by
  have := lineInfinityDivisor_isEffectiveCartierDivisor S
  have hcomap : (Stacks.Divisors.zeroScheme (modificationBaseChange f₂ b₂ g₂)
      (modificationInfinityModule f₂ b₂ g₂) (modificationInfinitySection f₂ b₂ g₂)).comap φ =
      Stacks.Divisors.zeroScheme (modificationBaseChange f₁ b₁ g₁)
        (modificationInfinityModule f₁ b₁ g₁) (modificationInfinitySection f₁ b₁ g₁) := by
    rw [zeroScheme_lineInfinityModuleSection, zeroScheme_lineInfinityModuleSection,
      ← Scheme.IdealSheafData.comap_comp, hφ]
  have hle := Scheme.IdealSheafData.le_map_iff_comap_le.2 (le_of_eq hcomap)
  have hJsq := Scheme.IdealSheafData.subschemeMap_subschemeι _ _ φ hle
  refine ⟨_, AlgebraicGeometry.isPullback_of_isClosedImmersion _ _ _ _ hJsq.symm
    (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι, hcomap]),
    (cancel_mono (modificationInfinityBaseChange f₂ b₂ g₂)).1 ?_⟩
  rw [Category.assoc, modificationInfinityZeroSchemeIso_hom_comp, hJsq, Category.assoc, hφInf,
    ← Category.assoc, modificationInfinityZeroSchemeIso_hom_comp]

end Comparison

section ComparisonGysin

variable (C : ChowSituation.{u}) {X₁ X₂ W₁ W₂ T₁ T₂ : Scheme.{u}} {f₁ : X₁ ⟶ C.S}
  [LocallyOfFiniteType f₁] {f₂ : X₂ ⟶ C.S} [LocallyOfFiniteType f₂]
  {b₁ : W₁ ⟶ projectiveLineProduct f₁} [IsProper b₁] {b₂ : W₂ ⟶ projectiveLineProduct f₂}
  [IsProper b₂] {g₁ : T₁ ⟶ X₁} [LocallyOfFiniteType g₁] {g₂ : T₂ ⟶ X₂} [LocallyOfFiniteType g₂]
  (φ : modificationBaseChange f₁ b₁ g₁ ⟶ modificationBaseChange f₂ b₂ g₂) [IsProper φ]
  (φInf : pullback (modificationProjectionAtInfinity f₁ b₁) g₁ ⟶
    pullback (modificationProjectionAtInfinity f₂ b₂) g₂) [IsProper φInf]

/-- **The Gysin map at infinity commutes with pushforward along a comparison** (Stacks 02TA). For
`φ : W_1 ×_{X_1} T_1 ⟶ W_2 ×_{X_2} T_2` proper, over the base and over `𝐏¹_S`, and `φ_∞` a morphism
of the base-changed fibres at infinity compatible with it, `i_∞^* (φ_* β) = φ_{∞,*} (i_∞^* β)`. -/
theorem modificationInfinityGysin_properChowPushforward_of_comparison (k : ℤ)
    (hφover : φ ≫ modificationBaseChangeOver f₂ b₂ g₂ = modificationBaseChangeOver f₁ b₁ g₁)
    (hφ : φ ≫ modificationBaseChangeToRelativeLine f₂ b₂ g₂ =
      modificationBaseChangeToRelativeLine f₁ b₁ g₁)
    (hφInf : φInf ≫ modificationInfinityBaseChange f₂ b₂ g₂ =
      modificationInfinityBaseChange f₁ b₁ g₁ ≫ φ)
    (β : chowGroup C (modificationBaseChangeOver f₁ b₁ g₁) (k + 1)) :
    modificationInfinityGysin C f₂ b₂ g₂ k
        (properChowPushforward C (modificationBaseChangeOver f₁ b₁ g₁)
          (modificationBaseChangeOver f₂ b₂ g₂) φ hφover (k + 1)
          (properPushforwardDescends C _ _ _ _ _) β) =
      properChowPushforward C (modificationInfinityBaseChangeOver f₁ b₁ g₁)
        (modificationInfinityBaseChangeOver f₂ b₂ g₂) φInf
        (comp_modificationInfinityBaseChangeOver_of_comp φ hφover φInf hφInf) k
        (properPushforwardDescends C _ _ _ _ _) (modificationInfinityGysin C f₁ b₁ g₁ k β) := by
  have := lineInfinityDivisor_isEffectiveCartierDivisor C.S
  obtain ⟨J, hpb, hcomp⟩ := exists_isPullback_zeroScheme_infinity φ hφ φInf hφInf
  have : IsProper J := MorphismProperty.of_isPullback (P := @IsProper) hpb inferInstance
  have hJ : J ≫ modificationZeroSchemeOver C f₂ b₂ g₂ (modificationInfinityModule f₂ b₂ g₂)
      (modificationInfinitySection f₂ b₂ g₂) =
      modificationZeroSchemeOver C f₁ b₁ g₁ (modificationInfinityModule f₁ b₁ g₁)
        (modificationInfinitySection f₁ b₁ g₁) := by
    rw [modificationZeroSchemeOver, ← Category.assoc, hpb.w.symm, Category.assoc, hφover]
  have h02TA := gysinSystemOfInvertible_properPushforward_pullbackModule C
    (modificationBaseChangeOver f₁ b₁ g₁) (modificationBaseChangeOver f₂ b₂ g₂)
    (modificationBaseChangeToRelativeLine f₁ b₁ g₁) (modificationBaseChangeToRelativeLine f₂ b₂ g₂)
    φ hφover hφ (Stacks.Divisors.divisorSheaf (lineInfinityDivisor C.S))
    (Stacks.Divisors.divisorSheafGlobalSection (lineInfinityDivisor C.S)) k J hpb.w.symm hJ β
  have hInf := comp_modificationInfinityBaseChangeOver_of_comp φ hφover φInf hφInf
  rw [modificationInfinityGysin, modificationInfinityGysin, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, h02TA]
  rw [chowPushforwardOfIso, chowPushforwardOfIso,
    ← properChowPushforward_comp_apply C _ _ (modificationInfinityBaseChangeOver f₂ b₂ g₂) J _ _
      rfl hJ (modificationInfinityZeroSchemeIso_over C f₂ b₂ g₂) (by
        rw [Category.assoc, modificationInfinityZeroSchemeIso_over, hJ]) k _ _
      (properPushforwardDescends C _ _ _ _ _),
    ← properChowPushforward_comp_apply C _ (modificationInfinityBaseChangeOver f₁ b₁ g₁)
      (modificationInfinityBaseChangeOver f₂ b₂ g₂) _ φInf _ rfl
      (modificationInfinityZeroSchemeIso_over C f₁ b₁ g₁) _ (by
        rw [Category.assoc, hInf, modificationInfinityZeroSchemeIso_over]) k _ _
      (properPushforwardDescends C _ _ _ _ _)]
  exact DFunLike.congr_fun (properChowPushforward_congr C _ _ _ _ hcomp _ _ k _ _) _

end ComparisonGysin

/-! ### Proper pushforward along a morphism of test schemes -/

section Proper

variable (C : ChowSituation.{u}) {X W T T' : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b] (g : T ⟶ X) [LocallyOfFiniteType g]
  (h : T' ⟶ T) [IsProper h]

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType g] [IsProper h] in
/-- The map of the charts over `𝐀¹_X` is a morphism over the base. -/
theorem modificationAffineChartMap_over :
    modificationAffineChartMap f b g h ≫ modificationAffineChartOver C f b g =
      modificationAffineChartOver C f b (h ≫ g) := by
  rw [modificationAffineChartOver, modificationAffineChartMap_ι_assoc,
    modificationBaseChangeMap_over]

/-- **The pushforward of a lift is a lift of the pushforward** (Stacks 02RG). If `β` lifts `α` on
`W ×_X T'`, then its pushforward along the proper base change of `h` lifts `h_* α` on `W ×_X T`. -/
theorem IsModificationLift.properPushforward
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (k : ℤ)
    {α : chowGroup C ((h ≫ g) ≫ f) k}
    {β : chowGroup C (modificationBaseChangeOver f b (h ≫ g)) (k + 1)}
    (hβ : IsModificationLift C f b hA (h ≫ g) k α β) :
      IsModificationLift C f b hA g k
      (properChowPushforward C ((h ≫ g) ≫ f) (g ≫ f) h (by rw [Category.assoc]) k
        (properPushforwardDescends C _ _ _ _ k) α)
      (properChowPushforward C (modificationBaseChangeOver f b (h ≫ g))
        (modificationBaseChangeOver f b g) (bivariantBaseChangeMap (modificationProjection f b) g h)
        (modificationBaseChangeMap_over f b g h) (k + 1) (properPushforwardDescends C _ _ _ _ _)
        β) := by
  have := isProper_modificationAffineChartMap f b g h
  have := flat_modificationAffineChartProjection f b g hA
  have := flat_modificationAffineChartProjection f b (h ≫ g) hA
  unfold IsModificationLift at hβ ⊢
  rw [chowGroupRestrict_properChowPushforward C (modificationBaseChangeOver f b (h ≫ g))
      (modificationBaseChangeOver f b g) (modificationAffineChartOver C f b (h ≫ g))
      (modificationAffineChartOver C f b g)
      (bivariantBaseChangeMap (modificationProjection f b) g h)
      (modificationBaseChangeMap_over f b g h) (modificationAffineChartι f b (h ≫ g)) rfl
      (modificationAffineChartι f b g) rfl (modificationAffineChartMap f b g h)
      (modificationAffineChartMap_over C f b g h) (isPullback_modificationAffineChartMap f b g h)
      (k + 1) _ (properPushforwardDescends C _ _ _ _ _) β, hβ]
  exact (flatPullbackChow_properChowPushforward_of_isProper C ((h ≫ g) ≫ f) (g ≫ f)
    (modificationAffineChartOver C f b (h ≫ g)) (modificationAffineChartOver C f b g) h
    (modificationAffineChartProjection f b g) (modificationAffineChartProjection f b (h ≫ g))
    (modificationAffineChartMap f b g h)
    (isPullback_modificationAffineChartProjection_map f b g h).flip (by rw [Category.assoc])
    (modificationAffineChartProjection_over C f b g)
    (modificationAffineChartProjection_over C f b (h ≫ g)) 1
    (relativeDimension_modificationAffineChartProjection f b g hA) k α).symm

/-- **The Gysin map at infinity commutes with proper pushforward** (Stacks 02TA). For `h : T' ⟶ T`
proper and `h'` the induced morphism of base-changed fibres at infinity, pushing forward along the
base change of `h` and then applying `i_∞^*` on `W ×_X T` is applying `i_∞^*` on `W ×_X T'` and
then pushing forward along `h'`. -/
theorem modificationInfinityGysin_properChowPushforward (k : ℤ)
    (h' : pullback (modificationProjectionAtInfinity f b) (h ≫ g) ⟶
      pullback (modificationProjectionAtInfinity f b) g) [IsProper h']
    (hsnd : h' ≫ pullback.snd (modificationProjectionAtInfinity f b) g =
      pullback.snd (modificationProjectionAtInfinity f b) (h ≫ g) ≫ h)
    (hfst : h' ≫ pullback.fst (modificationProjectionAtInfinity f b) g =
      pullback.fst (modificationProjectionAtInfinity f b) (h ≫ g))
    (β : chowGroup C (modificationBaseChangeOver f b (h ≫ g)) (k + 1)) :
      modificationInfinityGysin C f b g k
        (properChowPushforward C (modificationBaseChangeOver f b (h ≫ g))
          (modificationBaseChangeOver f b g)
          (bivariantBaseChangeMap (modificationProjection f b) g h)
          (modificationBaseChangeMap_over f b g h) (k + 1) (properPushforwardDescends C _ _ _ _ _)
          β) =
      properChowPushforward C (modificationInfinityBaseChangeOver f b (h ≫ g))
        (modificationInfinityBaseChangeOver f b g) h'
        (by rw [modificationInfinityBaseChangeOver, ← Category.assoc, hfst]) k
        (properPushforwardDescends C _ _ _ _ _)
        (modificationInfinityGysin C f b (h ≫ g) k β) :=
  modificationInfinityGysin_properChowPushforward_of_comparison C
    (bivariantBaseChangeMap (modificationProjection f b) g h) h' k
    (modificationBaseChangeMap_over f b g h) (modificationBaseChangeMap_toRelativeLine f b g h)
    (modificationInfinityBaseChange_comp_map f b g h h' hsnd hfst) β

/-- **The cap operation at infinity commutes with proper pushforward** (Stacks 0B76 (1)). -/
theorem gysinCapOfLift_properChowPushforward
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (k : ℤ)
    (h' : pullback (modificationProjectionAtInfinity f b) (h ≫ g) ⟶
      pullback (modificationProjectionAtInfinity f b) g) [IsProper h']
    (hsnd : h' ≫ pullback.snd (modificationProjectionAtInfinity f b) g =
      pullback.snd (modificationProjectionAtInfinity f b) (h ≫ g) ≫ h)
    (hfst : h' ≫ pullback.fst (modificationProjectionAtInfinity f b) g =
      pullback.fst (modificationProjectionAtInfinity f b) (h ≫ g))
    (α : chowGroup C ((h ≫ g) ≫ f) k) :
    gysinCapAtInfinity C f b hA g k
        (properChowPushforward C ((h ≫ g) ≫ f) (g ≫ f) h (by rw [Category.assoc]) k
          (properPushforwardDescends C _ _ _ _ k) α) =
      properChowPushforward C (modificationInfinityBaseChangeOver f b (h ≫ g))
        (modificationInfinityBaseChangeOver f b g) h'
        (by rw [modificationInfinityBaseChangeOver, ← Category.assoc, hfst]) k
        (properPushforwardDescends C _ _ _ _ _)
        (gysinCapAtInfinity C f b hA (h ≫ g) k α) := by
  obtain ⟨β, hβ⟩ := exists_isModificationLift C f b hA (h ≫ g) k α
  rw [gysinCapAtInfinity_eq_of_isModificationLift C f b hA (h ≫ g) k α β hβ,
    gysinCapAtInfinity_eq_of_isModificationLift C f b hA g k _ _
      (hβ.properPushforward C f b g h hA k)]
  exact modificationInfinityGysin_properChowPushforward C f b g h k h' hsnd hfst β

end Proper

/-! ### Flat pullback along a morphism of test schemes -/

section Flat

variable (C : ChowSituation.{u}) {X W T T' : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b] (g : T ⟶ X) [LocallyOfFiniteType g]
  (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ) (hr : RelativeDimension h r)

/-- Restriction of Chow classes along an open immersion commutes with transport of degrees. -/
theorem chowGroupRestrict_chowGroupDegreeEquiv {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (j : B ⟶ A)
    [IsOpenImmersion j] (hj : j ≫ sA = sB) {m n : ℤ} (hmn : m = n) (x : chowGroup C sA m) :
    chowGroupRestrict C sA sB j hj n (chowGroupDegreeEquiv C sA hmn x) =
      chowGroupDegreeEquiv C sB hmn (chowGroupRestrict C sA sB j hj m x) := by
  subst hmn
  rfl

/-- **The flat pullback of a lift is a lift of the flat pullback** (Stacks 02RD). If `β` lifts `α`
on `W ×_X T`, then its flat pullback along the base change of `h` lifts `h^* α` on `W ×_X T'`. -/
theorem IsModificationLift.flatPullback
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (k : ℤ)
    {α : chowGroup C (g ≫ f) k} {β : chowGroup C (modificationBaseChangeOver f b g) (k + 1)}
    (hβ : IsModificationLift C f b hA g k α β) :
    IsModificationLift C f b hA (h ≫ g) (k + (r : ℤ))
      (flatPullbackChow C ((h ≫ g) ≫ f) (g ≫ f) h (by rw [Category.assoc]) r hr k
        (flatPullbackDescends C _ _ _ _ _ _ _) α)
      (chowGroupDegreeEquiv C _ (by ring : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
        (flatPullbackChow C (modificationBaseChangeOver f b (h ≫ g))
          (modificationBaseChangeOver f b g)
          (bivariantBaseChangeMap (modificationProjection f b) g h)
          (modificationBaseChangeMap_over f b g h) r
          (bivariantBaseChangeMap_relativeDimension _ g h hr)
          (k + 1) (flatPullbackDescends C _ _ _ _ _ _ _) β)) := by
  have := flat_modificationAffineChartProjection f b g hA
  have := flat_modificationAffineChartProjection f b (h ≫ g) hA
  unfold IsModificationLift at hβ ⊢
  rw [chowGroupRestrict_chowGroupDegreeEquiv, chowGroupRestrict_flatPullbackChow C
      (modificationBaseChangeOver f b (h ≫ g)) (modificationBaseChangeOver f b g)
      (modificationAffineChartOver C f b (h ≫ g)) (modificationAffineChartOver C f b g)
      (bivariantBaseChangeMap (modificationProjection f b) g h)
      (modificationBaseChangeMap_over f b g h) r (bivariantBaseChangeMap_relativeDimension _ g h hr)
      (modificationAffineChartι f b (h ≫ g)) rfl (modificationAffineChartι f b g) rfl
      (modificationAffineChartMap f b g h) (modificationAffineChartMap_over C f b g h)
      (isPullback_modificationAffineChartMap f b g h)
      (relativeDimension_modificationAffineChartMap f b g h hr) (k + 1) _
      (flatPullbackDescends C _ _ _ _ _ _ _) β, hβ]
  refine (chowGroupDegreeEquiv_eq_iff_heq C _ _ _ _).2 ?_
  exact flatPullbackChow_comm_of_comp_eq C (modificationAffineChartOver C f b (h ≫ g))
    (modificationAffineChartOver C f b g) ((h ≫ g) ≫ f) (g ≫ f)
    (modificationAffineChartMap f b g h) (modificationAffineChartProjection f b g)
    (modificationAffineChartProjection f b (h ≫ g)) h (modificationAffineChartMap_over C f b g h)
    (modificationAffineChartProjection_over C f b g)
    (by rw [modificationAffineChartProjection_over]) (by rw [Category.assoc]) r 1
    (relativeDimension_modificationAffineChartMap f b g h hr)
    (relativeDimension_modificationAffineChartProjection f b g hA)
    (relativeDimension_modificationAffineChartProjection f b (h ≫ g) hA) hr
    (modificationAffineChartMap_projection f b g h) k _ _ _ _ α

/-- **The Gysin map at infinity commutes with flat pullback** (Stacks 0B71). -/
theorem modificationInfinityGysin_flatPullbackChow (k : ℤ)
    (h' : pullback (modificationProjectionAtInfinity f b) (h ≫ g) ⟶
      pullback (modificationProjectionAtInfinity f b) g) [LocallyOfFiniteType h'] [Flat h']
    (hsnd : h' ≫ pullback.snd (modificationProjectionAtInfinity f b) g =
      pullback.snd (modificationProjectionAtInfinity f b) (h ≫ g) ≫ h)
    (hfst : h' ≫ pullback.fst (modificationProjectionAtInfinity f b) g =
      pullback.fst (modificationProjectionAtInfinity f b) (h ≫ g))
    (hr' : RelativeDimension h' r)
    (β : chowGroup C (modificationBaseChangeOver f b g) (k + 1)) :
    modificationInfinityGysin C f b (h ≫ g) (k + (r : ℤ))
        (chowGroupDegreeEquiv C _ (by ring : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
          (flatPullbackChow C (modificationBaseChangeOver f b (h ≫ g))
            (modificationBaseChangeOver f b g)
            (bivariantBaseChangeMap (modificationProjection f b) g h)
            (modificationBaseChangeMap_over f b g h) r
            (bivariantBaseChangeMap_relativeDimension _ g h hr) (k + 1)
            (flatPullbackDescends C _ _ _ _ _ _ _) β)) =
      flatPullbackChow C (modificationInfinityBaseChangeOver f b (h ≫ g))
        (modificationInfinityBaseChangeOver f b g) h'
        (by rw [modificationInfinityBaseChangeOver, ← Category.assoc, hfst]) r hr' k
        (flatPullbackDescends C _ _ _ _ _ _ _) (modificationInfinityGysin C f b g k β) := by
  have := lineInfinityDivisor_isEffectiveCartierDivisor C.S
  obtain ⟨J, hpb, hcomp⟩ := exists_isPullback_zeroScheme_infinity
    (bivariantBaseChangeMap (modificationProjection f b) g h)
    (modificationBaseChangeMap_toRelativeLine f b g h) h'
    (modificationInfinityBaseChange_comp_map f b g h h' hsnd hfst)
  have : LocallyOfFiniteType J :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance
  have : Flat J := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
  have hJr : RelativeDimension J r :=
    RelativeDimension.of_isPullback hpb (bivariantBaseChangeMap_relativeDimension _ g h hr)
  have hJ : J ≫ modificationZeroSchemeOver C f b g (modificationInfinityModule f b g)
      (modificationInfinitySection f b g) =
      modificationZeroSchemeOver C f b (h ≫ g) (modificationInfinityModule f b (h ≫ g))
        (modificationInfinitySection f b (h ≫ g)) := by
    rw [modificationZeroSchemeOver, ← Category.assoc, hpb.w.symm, Category.assoc,
      modificationBaseChangeMap_over]
  have hFP := gysinSystemOfInvertible_flatPullback_pullbackModule C
    (modificationBaseChangeOver f b (h ≫ g)) (modificationBaseChangeOver f b g)
    (modificationBaseChangeToRelativeLine f b (h ≫ g)) (modificationBaseChangeToRelativeLine f b g)
    (bivariantBaseChangeMap (modificationProjection f b) g h)
    (modificationBaseChangeMap_over f b g h) (modificationBaseChangeMap_toRelativeLine f b g h) r
    (bivariantBaseChangeMap_relativeDimension _ g h hr)
    (Stacks.Divisors.divisorSheaf (lineInfinityDivisor C.S))
    (Stacks.Divisors.divisorSheafGlobalSection (lineInfinityDivisor C.S)) k J hpb.w.symm hJ hJr β
  rw [modificationInfinityGysin, modificationInfinityGysin, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, hFP]
  exact (flatPullbackChow_chowPushforwardOfIso C _ _ _ _
    (modificationInfinityZeroSchemeIso f b g).hom
    (modificationInfinityZeroSchemeIso_over C f b g)
    (modificationInfinityZeroSchemeIso f b (h ≫ g)).hom
    (modificationInfinityZeroSchemeIso_over C f b (h ≫ g)) J hJ h' _ hcomp r hJr hr' k _ _ _).symm

/-- **The cap operation at infinity commutes with flat pullback** (Stacks 0B76 (2)). -/
theorem gysinCapOfLift_flatPullbackChow
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (k : ℤ)
    (h' : pullback (modificationProjectionAtInfinity f b) (h ≫ g) ⟶
      pullback (modificationProjectionAtInfinity f b) g) [LocallyOfFiniteType h'] [Flat h']
    (hsnd : h' ≫ pullback.snd (modificationProjectionAtInfinity f b) g =
      pullback.snd (modificationProjectionAtInfinity f b) (h ≫ g) ≫ h)
    (hfst : h' ≫ pullback.fst (modificationProjectionAtInfinity f b) g =
      pullback.fst (modificationProjectionAtInfinity f b) (h ≫ g))
    (hr' : RelativeDimension h' r) (α : chowGroup C (g ≫ f) k) :
    gysinCapAtInfinity C f b hA (h ≫ g) (k + (r : ℤ))
        (flatPullbackChow C ((h ≫ g) ≫ f) (g ≫ f) h (by rw [Category.assoc]) r hr k
          (flatPullbackDescends C _ _ _ _ _ _ _) α) =
      flatPullbackChow C (modificationInfinityBaseChangeOver f b (h ≫ g))
        (modificationInfinityBaseChangeOver f b g) h'
        (by rw [modificationInfinityBaseChangeOver, ← Category.assoc, hfst]) r hr' k
        (flatPullbackDescends C _ _ _ _ _ _ _) (gysinCapAtInfinity C f b hA g k α) := by
  obtain ⟨β, hβ⟩ := exists_isModificationLift C f b hA g k α
  rw [gysinCapAtInfinity_eq_of_isModificationLift C f b hA g k α β hβ,
    gysinCapAtInfinity_eq_of_isModificationLift C f b hA (h ≫ g) (k + (r : ℤ)) _ _
      (hβ.flatPullback C f b g h r hr hA k)]
  exact modificationInfinityGysin_flatPullbackChow C f b g h r hr k h' hsnd hfst hr' β

end Flat

end Stacks.Chow

end
