module

public import StacksFrontier.AlgebraicGeometry.GenericFlatness.ImageStratification
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallyProperOverLimit
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalDescentAlongLimit
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Proper morphisms smooth of a fixed relative dimension come from a Noetherian base

Let `S` be quasi-compact and quasi-separated and `f : X ⟶ S` proper and smooth of relative
dimension `n`. Then `f` is the base change of a proper morphism, smooth of relative dimension
`n`, to a Noetherian scheme. This is the absolute Noetherian approximation with which the proof
of [Stacks, Tag 0G8I] reduces existence to a Noetherian base; over an affine base the
corresponding statement without the relative dimension is
`AlgebraicGeometry.exists_isPullback_isNoetherian_properSmooth`.

## Main results

* `AlgebraicGeometry.exists_isPullback_isNoetherian_smoothOfRelativeDimension`

## References

* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 0C0C](https://stacks.math.columbia.edu/tag/0C0C)
* [Stacks Project, Tag 0G8I](https://stacks.math.columbia.edu/tag/0G8I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A property of morphisms respecting isomorphisms holds for the base change of `f₁ : Y ⟶ T`,
viewed as a morphism of schemes over `T` to the terminal one, exactly when it holds for
`pullback.snd f₁ b`. -/
theorem overPullback_map_homMk_toUnit_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {T Y T' : Scheme.{u}} (f₁ : Y ⟶ T) (b : T' ⟶ T) :
    P ((Over.pullback b).map
      (Over.homMk f₁ (Category.comp_id f₁) : Over.mk f₁ ⟶ Over.mk (𝟙 T))).left ↔
      P (pullback.snd f₁ b) := by
  have hw : ((Over.pullback b).map
      (Over.homMk f₁ (Category.comp_id f₁) : Over.mk f₁ ⟶ Over.mk (𝟙 T))).left ≫
        pullback.snd (𝟙 T) b = pullback.snd f₁ b := Over.w _
  rw [← hw]
  exact (MorphismProperty.cancel_right_of_respectsIso P _ _).symm

/-- A property of morphisms respecting isomorphisms holding for `f` holds for the base change,
along `π`, of `f₁` viewed as a morphism over `T` to the terminal one, when `f` is the base change
of `f₁` along `π`. -/
theorem overPullback_map_homMk_toUnit_of_isPullback (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {X S T Y : Scheme.{u}} {f : X ⟶ S} {f₁ : Y ⟶ T} {g : X ⟶ Y} {π : S ⟶ T}
    (h : IsPullback g f f₁ π) (hP : P f) :
    P ((Over.pullback π).map
      (Over.homMk f₁ (Category.comp_id f₁) : Over.mk f₁ ⟶ Over.mk (𝟙 T))).left := by
  rw [overPullback_map_homMk_toUnit_iff P f₁ π,
    ← MorphismProperty.cancel_left_of_respectsIso P h.isoPullback.hom, h.isoPullback_hom_snd]
  exact hP

/-- If `f` is the base change of `f₁` along the projection of a cone to the stage `j`, it is also
the base change of the pullback of `f₁` to any later stage `k`. -/
theorem isPullback_pullbackLift_of_isPullback_cone {C I : Type*} [Category C] [Category I]
    {D : I ⥤ C} (c : Cone D) {j k : I} (t : k ⟶ j) {X Y : C} {f : X ⟶ c.pt} {f₁ : Y ⟶ D.obj j}
    {g : X ⟶ Y} (h : IsPullback g f f₁ (c.π.app j)) [HasPullback f₁ (D.map t)] :
    IsPullback (pullback.lift g (f ≫ c.π.app k) (by rw [h.w, Category.assoc, c.w t])) f
      (pullback.snd f₁ (D.map t)) (c.π.app k) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst, c.w t]
  exact h

/-- If `f`, smooth of relative dimension `n`, is the base change of a morphism `f₁` of finite
presentation over a stage of a cofiltered limit of qcqs schemes with affine transition maps, then
the base change of `f₁` to some later stage is smooth and syntomic of relative dimension `n`. -/
theorem exists_smooth_syntomicOfRelativeDimension_pullbackSnd_of_isLimit {I : Type u}
    [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D) (hc : IsLimit c) {j : I} {X Y : Scheme.{u}}
    {f : X ⟶ c.pt} {f₁ : Y ⟶ D.obj j} {g : X ⟶ Y} (h : IsPullback g f f₁ (c.π.app j))
    [LocallyOfFinitePresentation f₁] [CompactSpace Y] [QuasiSeparatedSpace Y] (n : ℕ)
    [SmoothOfRelativeDimension n f] :
    ∃ (k : I) (t : k ⟶ j), Smooth (pullback.snd f₁ (D.map t)) ∧
      SyntomicOfRelativeDimension n (pullback.snd f₁ (D.map t)) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : MorphismProperty.RespectsIso (@Smooth.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (@SyntomicOfRelativeDimension n : MorphismProperty Scheme.{u}) :=
    syntomicOfRelativeDimension_isStableUnderBaseChange n
  have : MorphismProperty.RespectsIso
      (@SyntomicOfRelativeDimension n : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hfsyn : SyntomicOfRelativeDimension n f :=
    ⟨syntomic_of_smooth f, fun x => fiberDimensionAt_eq_of_smoothOfRelativeDimension f n x⟩
  let X₀ : Over (D.obj j) := Over.mk f₁
  let Y₀ : Over (D.obj j) := Over.mk (𝟙 (D.obj j))
  let a : X₀ ⟶ Y₀ := Over.homMk f₁ (Category.comp_id f₁)
  have : CompactSpace X₀.left := inferInstanceAs (CompactSpace Y)
  have : QuasiSeparatedSpace X₀.left := inferInstanceAs (QuasiSeparatedSpace Y)
  have : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj j))
  have : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj j))
  have : LocallyOfFinitePresentation a.left := inferInstanceAs (LocallyOfFinitePresentation f₁)
  have hsm : Smooth ((Over.pullback (c.π.app j)).map a).left :=
    overPullback_map_homMk_toUnit_of_isPullback (@Smooth) h inferInstance
  obtain ⟨k₁, g₁, hk₁⟩ := exists_smooth_baseChange_of_smooth_limitBaseChange D c j X₀ Y₀ a hc
  obtain ⟨k₂, g₂, hk₂⟩ := exists_syntomicOfRelativeDimension_baseChange_of_limitBaseChange n D c j
    X₀ Y₀ a hc
    (overPullback_map_homMk_toUnit_of_isPullback (@SyntomicOfRelativeDimension n) h hfsyn)
  obtain ⟨k, b₁, b₂, hb⟩ := IsCofiltered.cospan g₁ g₂
  have hsmk : Smooth ((Over.pullback (D.map (b₁ ≫ g₁))).map a).left := by
    rw [D.map_comp]
    exact overPullback_map_comp (@Smooth) (D.map g₁) (D.map b₁) a hk₁
  have hsynk : SyntomicOfRelativeDimension n ((Over.pullback (D.map (b₁ ≫ g₁))).map a).left := by
    rw [hb, D.map_comp]
    exact overPullback_map_comp (@SyntomicOfRelativeDimension n) (D.map g₂) (D.map b₂) a hk₂
  rw [overPullback_map_homMk_toUnit_iff (@Smooth)] at hsmk
  rw [overPullback_map_homMk_toUnit_iff (@SyntomicOfRelativeDimension n)] at hsynk
  exact ⟨k, b₁ ≫ g₁, hsmk, hsynk⟩

/-- A proper morphism, smooth of relative dimension `n`, to the limit of a cofiltered system of
qcqs schemes with affine transition maps is the base change of one, proper and smooth of relative
dimension `n`, over a stage of the system. -/
theorem exists_isPullback_smoothOfRelativeDimension_of_isLimit {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D)
    (hc : IsLimit c) {X : Scheme.{u}} (f : X ⟶ c.pt) [IsProper f] (n : ℕ)
    [SmoothOfRelativeDimension n f] :
    ∃ (k : I) (Y : Scheme.{u}) (h : Y ⟶ D.obj k) (q' : X ⟶ Y),
      IsProper h ∧ SmoothOfRelativeDimension n h ∧ IsPullback q' f h (c.π.app k) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hfp : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  have : IsProper (Over.mk f).hom := ‹IsProper f›
  obtain ⟨j, Xj, hfpj, hprj, ⟨e⟩⟩ :=
    exists_isProper_finitePresentation_overPullbackObj_of_isLimit D c hc (Over.mk f) hfp
  let f₁ : Xj.left ⟶ D.obj j := Xj.hom
  have : LocallyOfFinitePresentation f₁ := hfpj.1
  have : QuasiCompact f₁ := hfpj.2.1
  have : QuasiSeparated f₁ := hfpj.2.2
  have : IsProper f₁ := hprj
  have : CompactSpace Xj.left := QuasiCompact.compactSpace_of_compactSpace f₁
  have : QuasiSeparatedSpace Xj.left := quasiSeparatedSpace_of_quasiSeparated f₁
  let g₀ : X ⟶ Xj.left := e.hom.left ≫ pullback.fst f₁ (c.π.app j)
  have he : e.hom.left ≫ pullback.snd f₁ (c.π.app j) = f := by
    simpa using Over.w e.hom
  have hsq₀ : IsPullback g₀ f f₁ (c.π.app j) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ ((Over.forget _).mapIso e) rfl he
    change (e.hom.left ≫ pullback.fst f₁ (c.π.app j)) ≫ f₁ = f ≫ c.π.app j
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  obtain ⟨k, t, hsm, hsyn⟩ :=
    exists_smooth_syntomicOfRelativeDimension_pullbackSnd_of_isLimit D c hc hsq₀ n
  exact ⟨k, _, pullback.snd f₁ (D.map t), _,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback f₁ (D.map t)) inferInstance,
    Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq _ n hsyn.2,
    isPullback_pullbackLift_of_isPullback_cone c t hsq₀⟩

/-- **A proper morphism, smooth of relative dimension `n`, to a quasi-compact quasi-separated
scheme is the base change of one to a Noetherian scheme.** Write `S` as the limit of schemes of
finite type over `ℤ` with affine transition maps (absolute Noetherian approximation,
[Stacks, Tag 01ZA]); the morphism, being of finite presentation, descends to a proper one over
a stage ([Stacks, Tags 01ZM, 081F]), smoothness descends to a later stage ([Stacks, Tag 0C0C])
and so does the dimension of the fibres, through syntomicity of relative dimension `n`, and at
a common later stage the model is smooth of relative dimension `n`. -/
@[ega "IV 8.1.2" "special case"]
theorem exists_isPullback_isNoetherian_smoothOfRelativeDimension {X S : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] (f : X ⟶ S) [IsProper f] (n : ℕ)
    [SmoothOfRelativeDimension n f] :
    ∃ (T Y : Scheme.{u}) (h : Y ⟶ T) (q : S ⟶ T) (q' : X ⟶ Y),
      IsNoetherian T ∧ IsProper h ∧ SmoothOfRelativeDimension n h ∧ IsPullback q' f h q := by
  let apx := Stacks.GenericFlatness.finiteTypeApproximation (S := S)
  let := apx.indexPreorder
  have := apx.indexNonempty
  have := apx.indexDirected
  let D := apx.ambient
  let c : Cone D := Cone.mk S apx.ambientCone
  have hc : IsLimit c := apx.ambientCone_isLimit
  have : ∀ {i j : apx.indexTypeᵒᵈ} (e : i ⟶ j), IsAffineHom (D.map e) := apx.transition_affine
  have : ∀ i, LocallyOfFiniteType (terminal.from (D.obj i)) := apx.locallyOfFiniteType
  have : ∀ i, QuasiCompact (terminal.from (D.obj i)) := apx.quasiCompact
  have hnoeth : ∀ i, IsNoetherian (D.obj i) := fun i ↦
    AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType_terminal_from (D.obj i)
  have : ∀ i, CompactSpace (D.obj i) := fun i => by have := hnoeth i; infer_instance
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i => by have := hnoeth i; infer_instance
  obtain ⟨k, Y, h, q', hh, hs, hpb⟩ :=
    exists_isPullback_smoothOfRelativeDimension_of_isLimit D c hc f n
  exact ⟨D.obj k, Y, h, c.π.app k, q', hnoeth k, hh, hs, hpb⟩

end AlgebraicGeometry

end
