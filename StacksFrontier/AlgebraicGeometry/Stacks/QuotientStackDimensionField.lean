module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOverFieldTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.OverField.SmoothCharacteristicZero
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.Dimension
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionFlatChart
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsQuotientOfSpaceAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackChartRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothQuotientStack
public import StacksFrontier.Examples.Stacks.ClassifyingStackSmoothCovering
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dimension of a quotient stack over a field

Let `X` be an algebraic space locally of finite type over a field `k` and let `G` be a group
algebraic space locally of finite type over `k` acting on `X`. Then
`dim [X/G] = dim(X) - dim(G)`; in particular `dim BG = dim [Spec k/G] = -dim(G)`, so the dimension
of an algebraic stack can be a negative integer, unlike that of a scheme or an algebraic space.
This file proves these assertions for `G` smooth over `k`, and so for every group scheme locally
of finite type over a field of characteristic `0`. For an arbitrary `G` locally of finite type over
`k` it proves the dimension formula for every model of `[X/G]`, and the three assertions given
that quotient stacks of flat groupoids locally of finite presentation are algebraic.

The quotient stack has its morphisms one universe above those of the schemes, while
`AlgebraicGeometry.Stack.dimension` is defined on `AlgebraicGeometry.Stack.AlgebraicStacks`. So
each statement asserts that a model of the quotient stack in
`AlgebraicGeometry.Stack.AlgebraicStacks` exists and that *every* model has the stated dimension.

## Main results

* `AlgebraicGeometry.Space.dimension_terminalSpace_eq_zero`: the final algebraic space over the
  spectrum of a field has dimension `0`.
* `AlgebraicGeometry.Stack.dimensionSubNat_iSup`: subtracting a fixed finite relative dimension
  from a dimension of an algebraic space commutes with suprema.
* `AlgebraicGeometry.Stack.dimension_eq_dimensionSubNat_of_chart`: one smooth, locally of finite
  type 1-morphism `T ⟶ 𝒳` from an algebraic space, surjective on points and of relative
  dimension `d` at every point, computes `dim(𝒳) = dim(T) - d`.
* `AlgebraicGeometry.Stack.dimension_eq_dimensionSubNat_of_flatChart`: the same for a flat chart,
  locally of finite type, surjective on points and of constant relative dimension.
* `AlgebraicGeometry.Stack.isSmooth_quotientStackModelProjection`,
  `AlgebraicGeometry.Stack.isLocallyOfFiniteType_quotientStackModelProjection` and
  `AlgebraicGeometry.Stack.exists_point_quotientStackModelProjection`: the chart `X ⟶ [X/G]`,
  read on a model of the quotient stack, is smooth, locally of finite type and surjective on
  points as soon as the groupoid is smooth.
* `AlgebraicGeometry.Stack.isLocallyNoetherianStack_of_quotientStackModel`: a model of the
  quotient stack of a smooth groupoid with locally Noetherian object space is locally Noetherian.
* `AlgebraicGeometry.Stack.dimension_quotientStack_eq_of_isSmooth`: `dim [X/G] = dim(X) - dim(G)`
  for `G` smooth over `k`.
* `AlgebraicGeometry.Stack.dimension_classifyingStack_eq_neg_of_isSmooth`: `dim BG = -dim(G)` for
  `G` smooth over `k`.
* `AlgebraicGeometry.Stack.dimension_classifyingStack_lt_zero_of_isSmooth_of_pos`: `dim BG < 0`
  when `G` is smooth over `k` and `dim(G) > 0`.
* `AlgebraicGeometry.Stack.dimension_quotientStack_eq_of_charZero`,
  `AlgebraicGeometry.Stack.dimension_classifyingStack_eq_neg_of_charZero` and
  `AlgebraicGeometry.Stack.dimension_classifyingStack_lt_zero_of_charZero_of_pos`: the same three
  assertions for every group scheme locally of finite type over a field of characteristic `0`.
* `AlgebraicGeometry.Stack.dimension_eq_of_quotientStackModel`: for every group locally of finite
  type over a field, every model of `[X/G]` is locally Noetherian of dimension `dim(X) - dim(G)`.
* `AlgebraicGeometry.Stack.dimension_quotientStack_eq_of_isAlgebraicStack_flat`,
  `AlgebraicGeometry.Stack.dimension_classifyingStack_eq_neg_of_isAlgebraicStack_flat` and
  `AlgebraicGeometry.Stack.dimension_classifyingStack_lt_zero_of_isAlgebraicStack_flat`: the three
  assertions for every group locally of finite type over a field, given that quotient stacks of
  flat groupoids locally of finite presentation are algebraic.

## References

* [Stacks Project, Tag 0AFR](https://stacks.math.columbia.edu/tag/0AFR)
* [Stacks Project, Tag 0AFM](https://stacks.math.columbia.edu/tag/0AFM)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0AFP](https://stacks.math.columbia.edu/tag/0AFP)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 06FH](https://stacks.math.columbia.edu/tag/06FH)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.Space

universe u

/-- The final algebraic space over the spectrum of a field has dimension `0`. -/
theorem dimension_terminalSpace_eq_zero {k : Type u} [Field k] (C : BigFppfSite.{u})
    (hk : C.Contains (Spec (.of k))) :
    dimension C (Spec (.of k)) hk (terminalSpace C (Spec (.of k)) hk).obj
      (terminalSpace C (Spec (.of k)) hk).property = ((0 : ℕ) : WithBot ℕ∞) := by
  have hbase : (BigFppfOver.toScheme C (Spec (.of k)) hk).obj
      (baseTerminal C (Spec (.of k)) hk) = Spec (.of k) := rfl
  refine (dimension_yoneda_eq_topologicalKrullDim C (Spec (.of k)) hk
    (baseTerminal C (Spec (.of k)) hk)).trans ?_
  rw [hbase]
  have h0 : ((0 : ℕ) : WithBot ℕ∞) = 0 := rfl
  rw [h0]
  exact topologicalKrullDim_eq_zero_of_discreteTopology_nonempty

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u v w

/-- Subtracting a fixed finite relative dimension is a left adjoint: for every extended integer
`b` there is a dimension `c` of an algebraic space such that `b < δ - d` exactly when `c < δ`. -/
private theorem exists_lt_dimensionSubNat_iff (b : EInt) (d : ℕ) :
    ∃ c : WithBot ℕ∞, ∀ x : WithBot ℕ∞, b < dimensionSubNat x d ↔ c < x := by
  have hshape : ∀ x : WithBot ℕ∞,
      x = ⊥ ∨ x = ((⊤ : ℕ∞) : WithBot ℕ∞) ∨ ∃ m : ℕ, x = ((m : ℕ∞) : WithBot ℕ∞) := by
    intro x
    induction x using WithBot.recBotCoe with
    | bot => exact Or.inl rfl
    | coe a =>
      induction a using ENat.recTopCoe with
      | top => exact Or.inr (Or.inl rfl)
      | coe m => exact Or.inr (Or.inr ⟨m, rfl⟩)
  have hvbot : dimensionSubNat (⊥ : WithBot ℕ∞) d = (⊥ : EInt) := rfl
  have hvtop : dimensionSubNat ((⊤ : ℕ∞) : WithBot ℕ∞) d = (⊤ : EInt) := rfl
  have hvcoe : ∀ m : ℕ, dimensionSubNat ((m : ℕ∞) : WithBot ℕ∞) d =
    (((m : ℤ) - (d : ℤ) : ℤ) : EInt) := fun _ => rfl
  induction b using WithBotTop.rec with
  | top => exact ⟨⊤, fun _ => iff_of_false not_top_lt not_top_lt⟩
  | bot =>
    refine ⟨⊥, fun x => ?_⟩
    rcases hshape x with h | h | ⟨m, h⟩
    · rw [h, hvbot]
      exact iff_of_false not_lt_bot not_lt_bot
    · rw [h, hvtop]
      exact iff_of_true (bot_lt_iff_ne_bot.mpr WithBotTop.top_ne_bot)
        (bot_lt_iff_ne_bot.mpr WithBot.coe_ne_bot)
    · rw [h, hvcoe m]
      exact iff_of_true (bot_lt_iff_ne_bot.mpr (WithBotTop.coe_ne_bot _))
        (bot_lt_iff_ne_bot.mpr WithBot.coe_ne_bot)
  | coe z =>
    rcases Int.lt_or_le (z + d) 0 with hz | hz
    · refine ⟨⊥, fun x => ?_⟩
      rcases hshape x with h | h | ⟨m, h⟩
      · rw [h, hvbot]
        exact iff_of_false not_lt_bot not_lt_bot
      · rw [h, hvtop]
        exact iff_of_true (lt_top_iff_ne_top.mpr (WithBotTop.coe_ne_top z))
          (bot_lt_iff_ne_bot.mpr WithBot.coe_ne_bot)
      · rw [h, hvcoe m]
        exact iff_of_true (WithBotTop.coe_lt_coe.mpr (by omega))
          (bot_lt_iff_ne_bot.mpr WithBot.coe_ne_bot)
    · refine ⟨(((z + d).toNat : ℕ∞) : WithBot ℕ∞), fun x => ?_⟩
      rcases hshape x with h | h | ⟨m, h⟩
      · rw [h, hvbot]
        exact iff_of_false not_lt_bot not_lt_bot
      · rw [h, hvtop]
        exact iff_of_true (lt_top_iff_ne_top.mpr (WithBotTop.coe_ne_top z))
          (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))
      · rw [h, hvcoe m]
        have harith : (z < (m : ℤ) - (d : ℤ)) ↔ ((z + (d : ℤ)).toNat < m) := by omega
        refine WithBotTop.coe_lt_coe.trans (harith.trans ?_)
        exact (WithBot.coe_lt_coe.trans ENat.natCast_lt_natCast).symm

/-- Subtracting a fixed finite relative dimension commutes with suprema. -/
theorem dimensionSubNat_iSup {ι : Sort v} (δ : ι → WithBot ℕ∞) (d : ℕ) :
    dimensionSubNat (⨆ i, δ i) d = ⨆ i, dimensionSubNat (δ i) d := by
  refine le_antisymm (le_iSup_iff_forall_lt.mpr fun b hb => ?_)
    (iSup_le fun i => le_of_forall_lt fun b hb => ?_)
  swap
  · obtain ⟨c, hc⟩ := exists_lt_dimensionSubNat_iff b d
    exact (hc _).mpr (((hc _).mp hb).trans_le (le_iSup δ i))
  obtain ⟨c, hc⟩ := exists_lt_dimensionSubNat_iff b d
  obtain ⟨i, hi⟩ := lt_iSup_iff.mp ((hc _).mp hb)
  exact ⟨i, (hc _).mpr hi⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **One smooth chart computes the dimension of a stack.** Let `f : T ⟶ 𝒳` be a smooth,
locally of finite type 1-morphism from an algebraic space which is surjective on points and has
relative dimension `d` at every point of `T`. Then `dim(𝒳) = dim(T) - d`. -/
theorem dimension_eq_dimensionSubNat_of_chart (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hsm : AlgebraicStacks.IsSmooth B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hsurj : ∀ x : points B S hS 𝒳.val.val 𝒳.val.property, ∃ t : Space.points B S hS T,
      pointsMap B S hS (fibredCategory B S hS T).val (fibredCategory B S hS T).property
        𝒳.val.property f.hom.hom (stackPointOfSpacePoint B S hS T t) = x)
    (d : ℕ) (hd : ∀ t : Space.points B S hS T,
      relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t = (d : WithBot ℕ∞)) :
    dimension B S hS 𝒳 h𝒳 = dimensionSubNat (Space.dimension B S hS T hT) d := by
  have hsup : dimensionSubNat (Space.dimension B S hS T hT) d =
      ⨆ t : Space.points B S hS T, dimensionSubNat (Space.dimensionAtPoint B S hS T hT t) d :=
    dimensionSubNat_iSup (fun t => Space.dimensionAtPoint B S hS T hT t) d
  rw [hsup]
  refine le_antisymm (iSup_le fun x => ?_) (iSup_le fun t => ?_)
  · obtain ⟨t, ht⟩ := hsurj x
    rw [dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒳 h𝒳 x hT f hsm hf t ht d
      (hd t)]
    exact le_iSup (fun s => dimensionSubNat (Space.dimensionAtPoint B S hS T hT s) d) t
  · rw [← dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒳 h𝒳 _ hT f hsm hf t
      rfl d (hd t)]
    exact le_iSup (dimensionAtPoint B S hS 𝒳 h𝒳) _

/-! ### A group of finite type, not necessarily smooth: the dimension through the flat atlas -/

/-- **One flat chart of constant relative dimension computes the dimension of a stack.** Let
`f : X ⟶ 𝒳` be flat, locally of finite type and surjective on points, from a locally Noetherian
algebraic space, of relative dimension `e` at every point. Then `dim(𝒳) = dim(X) - e`. -/
theorem dimension_eq_dimensionSubNat_of_flatChart (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (hNT : Space.HasEtaleLocalProperty B S hS T (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hsurj : ∀ x : points B S hS 𝒳.val.val 𝒳.val.property, ∃ t : Space.points B S hS T,
      pointsMap B S hS (fibredCategory B S hS T).val (fibredCategory B S hS T).property
        𝒳.val.property f.hom.hom (stackPointOfSpacePoint B S hS T t) = x)
    (d : ℕ) (hd : ∀ t : Space.points B S hS T,
      relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t = (d : WithBot ℕ∞)) :
    dimension B S hS 𝒳 h𝒳 = dimensionSubNat (Space.dimension B S hS T hT) d := by
  have hsup : dimensionSubNat (Space.dimension B S hS T hT) d =
      ⨆ t : Space.points B S hS T, dimensionSubNat (Space.dimensionAtPoint B S hS T hT t) d :=
    dimensionSubNat_iSup (fun t => Space.dimensionAtPoint B S hS T hT t) d
  rw [hsup]
  refine le_antisymm (iSup_le fun x => ?_) (iSup_le fun t => ?_)
  · obtain ⟨t, ht⟩ := hsurj x
    rw [dimensionAtPoint_eq_dimensionSubNat_of_isFlat.{u, w} B S hS 𝒳 h𝒳 x hT hNT f hflat hf d
      hd t ht]
    exact le_iSup (fun s => dimensionSubNat (Space.dimensionAtPoint B S hS T hT s) d) t
  · rw [← dimensionAtPoint_eq_dimensionSubNat_of_isFlat.{u, w} B S hS 𝒳 h𝒳 _ hT hNT f hflat hf d
      hd t rfl]
    exact le_iSup (dimensionAtPoint B S hS 𝒳 h𝒳) _

/-! ### The tautological chart `X ⟶ [X/G]` -/

section Chart

variable (A : AlgebraicSpaces B S hS) (H : GroupoidInAlgebraicSpaces B S hS A)
  (𝒬 : AlgebraicStacks.{u, w} B S hS)
  (e : StacksRepresentableCFG.EquivalenceOver (quotientStack H).p 𝒬.val.val.p)

/-- For a smooth groupoid `(U, R)`, the atlas `U ⟶ [U/R]`, read on a model `𝒬` of the quotient
stack, is a smooth 1-morphism of algebraic stacks. -/
theorem isSmooth_quotientStackModelProjection
    (hH : GroupoidInAlgebraicSpaces.IsSmooth B S hS H) :
    AlgebraicStacks.IsSmooth B S hS
      (quotientStackModelProjection.{u, w} B S hS A H 𝒬 e) := by
  have hrep := isRepresentableByAlgebraicSpaces_quotientStackModelProjection H 𝒬 e
  have h𝒰 := isAlgebraicStack_fibredCategory.{u, w} B S hS _ H.objects.property
  have hBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsSmooth B S hS h)).IsStableUnderBaseChange :=
    Space.isSmooth_isStableUnderBaseChange B S hS
  have hLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsSmooth B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.smooth_isLocalAtTarget_fppf B S hS
  exact (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) h𝒰 𝒬.property _ hrep).2
    (hasRelativeProperty_quotientStackModelProjection H 𝒬 e _ hH.1)

/-- For a smooth groupoid `(U, R)`, the atlas `U ⟶ [U/R]`, read on a model `𝒬` of the quotient
stack, is locally of finite type. -/
theorem isLocallyOfFiniteType_quotientStackModelProjection
    (hH : GroupoidInAlgebraicSpaces.IsSmooth B S hS H) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (quotientStackModelProjection.{u, w} B S hS A H 𝒬 e) :=
  AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
    (quotientModelAtlasFppf H 𝒬 e
      (Space.isFlat_of_isSmooth B S hS _ hH.1) (Space.isFlat_of_isSmooth B S hS _ hH.2)
      (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hH.1)
      (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hH.2)).2.2.2

/-- The atlas `U ⟶ [U/R]`, read on a model `𝒬` of the quotient stack, is surjective. -/
private theorem isSurjective_quotientStackModelProjection :
    IsSurjective B S hS (quotientStackModelProjection.{u, w} B S hS A H 𝒬 e) :=
  (pointsMap_surjective_iff_isRelativelySurjective.{u, w} B S hS _
    (isRepresentableByAlgebraicSpaces_quotientStackModelProjection H 𝒬 e)).2
    (hasRelativeProperty_quotientStackModelProjection H 𝒬 e _
      (QuotientAtlas.isSurjective_source H))

/-- The atlas `U ⟶ [U/R]`, read on a model `𝒬` of the quotient stack, is surjective on points:
every point of `𝒬` is the image of a point of the object space `U`. -/
theorem exists_point_quotientStackModelProjection
    (x : points B S hS 𝒬.val.val 𝒬.val.property) :
    ∃ t : Space.points B S hS H.objects.obj,
      pointsMap B S hS (fibredCategory B S hS H.objects.obj).val
        (fibredCategory B S hS H.objects.obj).property 𝒬.val.property
        (quotientStackModelProjection.{u, w} B S hS A H 𝒬 e).hom.hom
        (stackPointOfSpacePoint B S hS H.objects.obj t) = x := by
  have hcomp := spacePointMap_eq_pointsMap_comp_spacePointsEquiv B S hS
    H.objects.property (quotientStackModelProjection.{u, w} B S hS A H 𝒬 e)
  have hsp := spacePointMap_comp B S hS H.objects.obj
    (fibredCategory B S hS H.objects.obj) 𝒬.val
    (BasedFunctor.id (fibredCategory B S hS H.objects.obj).val)
    (quotientStackModelProjection.{u, w} B S hS A H 𝒬 e).hom.hom
  obtain ⟨q, hq⟩ := isSurjective_quotientStackModelProjection B S hS A H 𝒬 e x
  refine ⟨(spacePointsEquiv B S hS H.objects.obj).symm q, ?_⟩
  have h1 := congrFun hsp ((spacePointsEquiv B S hS H.objects.obj).symm q)
  have h2 := congrFun hcomp ((spacePointsEquiv B S hS H.objects.obj).symm q)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at h1 h2
  exact h1.symm.trans (h2.trans hq)

end Chart

section OverField

/-- Every model of the quotient stack `[U/R]` of a smooth groupoid with locally Noetherian
object space `U` is locally Noetherian. -/
theorem isLocallyNoetherianStack_of_quotientStackModel
    (A : AlgebraicSpaces B S hS) (H : GroupoidInAlgebraicSpaces B S hS A)
    (𝒬 : AlgebraicStacks.{u, w} B S hS)
    (e : StacksRepresentableCFG.EquivalenceOver (quotientStack H).p 𝒬.val.val.p)
    (hH : GroupoidInAlgebraicSpaces.IsSmooth B S hS H)
    (hU : Space.HasEtaleLocalProperty B S hS H.objects.obj
      (fun Z : Scheme.{u} => IsLocallyNoetherian Z)) :
    IsLocallyNoetherianStack.{u, w} B S hS 𝒬 := by
  let : ObjectProperty.IsLocal (fun Z : Scheme.{u} => IsLocallyNoetherian Z)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  exact (exists_scheme_atlas_iff_exists_space_atlas.{u, w} B S hS
    (fun Z : Scheme.{u} => IsLocallyNoetherian Z) 𝒬).mpr
    ⟨H.objects.obj, H.objects.property, quotientStackModelProjection.{u, w} B S hS A H 𝒬 e,
      isSurjective_quotientStackModelProjection B S hS A H 𝒬 e,
      isSmooth_quotientStackModelProjection.{u, w} B S hS A H 𝒬 e hH, hU⟩

variable {k : Type u} [Field k] (C : BigFppfSite.{u}) (hk : C.Contains (Spec (.of k)))

/-- An algebraic space locally of finite type over a field is locally Noetherian. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_field
    {Z : (BigFppfOver C (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace C (Spec (.of k)) hk Z)
    (z : Z ⟶ (Space.terminalSpace C (Spec (.of k)) hk).obj)
    (hz : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk z) :
    Space.HasEtaleLocalProperty C (Spec (.of k)) hk Z
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType C (Spec (.of k)) hk
    hZ (Space.terminalSpace C (Spec (.of k)) hk).property z hz
    (Space.hasEtaleLocalProperty_of_representable C (Spec (.of k)) hk _ _
      (Space.baseTerminal C (Spec (.of k)) hk) (Iso.refl _)
      ((AlgebraicGeometry.isLocallyNoetherian_Spec (R := CommRingCat.of k)).2 inferInstance))

variable (G : Space.GroupAlgebraicSpace C (Spec (.of k)) hk
    (Space.terminalSpace C (Spec (.of k)) hk).obj
    (Space.terminalSpace C (Spec (.of k)) hk).property)

/-- The identity of the terminal algebraic space over a field is locally of finite type. -/
private theorem isLocallyOfFiniteType_id_terminalSpace :
    Space.IsLocallyOfFiniteType C (Spec (.of k)) hk
      (𝟙 (Space.terminalSpace C (Spec (.of k)) hk).obj) :=
  Space.isLocallyOfFiniteType_of_isSmooth C (Spec (.of k)) hk
    (Space.isSmooth_id C (Spec (.of k)) hk (Space.terminalSpace C (Spec (.of k)) hk).property)

/-- Subtracting `m` from the dimension `0` of the terminal algebraic space gives `-m`. -/
private theorem dimensionSubNat_dimension_terminalSpace (m : ℕ) :
    dimensionSubNat (Space.dimension C (Spec (.of k)) hk
      (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)).left
      (Space.terminalSpace C (Spec (.of k)) hk).property) m = ((-(m : ℤ) : ℤ) : EInt) := by
  have h0 : Space.dimension C (Spec (.of k)) hk
      (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)).left
      (Space.terminalSpace C (Spec (.of k)) hk).property = ((0 : ℕ) : WithBot ℕ∞) :=
    Space.dimension_terminalSpace_eq_zero C hk
  have hz : dimensionSubNat ((0 : ℕ) : WithBot ℕ∞) m =
    (((0 : ℤ) - (m : ℤ) : ℤ) : EInt) := rfl
  rw [h0, hz, zero_sub]

/-- A positive dimension `m` gives a negative `-m` as an extended integer. -/
private theorem neg_natCast_lt_zero_of_pos {m : ℕ} {δ : WithBot ℕ∞} (hm : δ = (m : WithBot ℕ∞))
    (hpos : 0 < δ) : ((-(m : ℤ) : ℤ) : EInt) < 0 := by
  rw [hm] at hpos
  have hm0 : 0 < m := by exact_mod_cast hpos
  rw [show (0 : EInt) = ((0 : ℤ) : EInt) from rfl, WithBotTop.coe_lt_coe]
  omega

/-- **The dimension of a quotient stack by a smooth group, at a given model.** Let `G` be a group
algebraic space smooth over a field `k`, acting on an algebraic space `X` locally of finite type
over `k`. Every algebraic stack `𝒬` equivalent over the site to the quotient stack `[X/G]` is
locally Noetherian, `G` has finite dimension, and `dim 𝒬 = dim(X) - dim(G)`. -/
theorem dimension_eq_of_quotientStackModel_of_isSmooth
    (X : Over (Space.terminalSpace C (Spec (.of k)) hk).obj) [ModObj G.obj.X X]
    (hX : IsAlgebraicSpace C (Spec (.of k)) hk X.left)
    (hXft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk X.hom)
    (hGsm : Space.IsSmooth C (Spec (.of k)) hk G.obj.X.hom)
    (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
    (e : StacksRepresentableCFG.EquivalenceOver
      (quotientStack (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk) G.obj.X X
        G.property hX).groupoid).p 𝒬.val.val.p) :
    ∃ m : ℕ, Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = (m : WithBot ℕ∞) ∧
      ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
        dimension C (Spec (.of k)) hk 𝒬 hN =
          dimensionSubNat (Space.dimension C (Spec (.of k)) hk X.left hX) m := by
  let A := Space.terminalSpace C (Spec (.of k)) hk
  let H := (Space.groupoidOfAction A G.obj.X X G.property hX).groupoid
  have hGft := Space.isLocallyOfFiniteType_of_isSmooth C (Spec (.of k)) hk hGsm
  obtain ⟨m, hm⟩ := exists_dimension_eq_natCast_of_groupAlgebraicSpace C hk G hGft
  have hH : GroupoidInAlgebraicSpaces.IsSmooth C (Spec (.of k)) hk H :=
    Space.isSmooth_groupoidOfAction A G.obj.X X G.property hX hGsm
  have hN := isLocallyNoetherianStack_of_quotientStackModel.{u, w} C (Spec (.of k)) hk A H 𝒬 e hH
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_field C hk hX X.hom hXft)
  have hlft := isLocallyOfFiniteType_quotientStackModelProjection.{u, w} C (Spec (.of k)) hk A H
    𝒬 e hH
  refine ⟨m, hm, hN, dimension_eq_dimensionSubNat_of_chart.{u, w} C (Spec (.of k)) hk 𝒬 hN
    X.left hX (quotientStackModelProjection.{u, w} C (Spec (.of k)) hk A H 𝒬 e)
    (isSmooth_quotientStackModelProjection.{u, w} C (Spec (.of k)) hk A H 𝒬 e hH) hlft
    (exists_point_quotientStackModelProjection.{u, w} C (Spec (.of k)) hk A H 𝒬 e) m
    (fun t => ?_)⟩
  rw [relativeDimensionAt_quotientStackModelProjection_eq_dimension.{u, w} C hk G X hX hGft 𝒬 e
    hlft t, hm]

/-- **The dimension of a quotient stack by a smooth group.** Let `X` be an algebraic space locally
of finite type over a field `k` and let `G` be a group algebraic space smooth over `k` acting on
`X`. Then the quotient stack `[X/G]` is an algebraic stack — it has a model `𝒬` in the 2-category
of algebraic stacks — and every such model is locally Noetherian of dimension
`dim [X/G] = dim(X) - dim(G)`, the dimension of `G` being a natural number. -/
@[stacks 0AFR "`dim [X/G] = dim X - dim G` for a group smooth over the field; the quotient stack \
is constructed, and every model of it has this dimension"]
theorem dimension_quotientStack_eq_of_isSmooth
    (X : Over (Space.terminalSpace C (Spec (.of k)) hk).obj) [ModObj G.obj.X X]
    (hX : IsAlgebraicSpace C (Spec (.of k)) hk X.left)
    (hXft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk X.hom)
    (hGsm : Space.IsSmooth C (Spec (.of k)) hk G.obj.X.hom) :
    ∃ m : ℕ, Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = (m : WithBot ℕ∞) ∧
      (∃ 𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk,
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (quotientStack (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk)
            G.obj.X X G.property hX).groupoid).p 𝒬.val.val.p)) ∧
      ∀ (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_ : StacksRepresentableCFG.EquivalenceOver
          (quotientStack (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk)
            G.obj.X X G.property hX).groupoid).p 𝒬.val.val.p),
        ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
          dimension C (Spec (.of k)) hk 𝒬 hN =
            dimensionSubNat (Space.dimension C (Spec (.of k)) hk X.left hX) m := by
  have hGft := Space.isLocallyOfFiniteType_of_isSmooth C (Spec (.of k)) hk hGsm
  obtain ⟨m, hm⟩ := exists_dimension_eq_natCast_of_groupAlgebraicSpace C hk G hGft
  have hQ := isAlgebraicStack_quotientStackOfAction.{u, w} (Space.terminalSpace C (Spec (.of k)) hk)
    G.obj.X X G.property hX hGsm
  refine ⟨m, hm, ⟨AlgebraicStacks.smallModel C (Spec (.of k)) hk _ hQ,
    ⟨AlgebraicStacks.smallModelEquivalenceOver C (Spec (.of k)) hk _ hQ⟩⟩, fun 𝒬 e => ?_⟩
  obtain ⟨m', hm', hN, hdim⟩ :=
    dimension_eq_of_quotientStackModel_of_isSmooth.{u, w} C hk G X hX hXft hGsm 𝒬 e
  have hmm : m' = m := by exact_mod_cast hm'.symm.trans hm
  exact ⟨hN, hmm ▸ hdim⟩

/-- **The dimension of the classifying stack of a smooth group.** Let `G` be a group algebraic
space smooth over a field `k`. Then the classifying stack `BG = [Spec k/G]` is an algebraic stack
— it has a model `𝒬` in the 2-category of algebraic stacks — and every such model is locally
Noetherian of dimension `dim BG = -dim(G)`, the dimension of `G` being a natural number. -/
@[stacks 0AFR "`dim BG = -dim G` for the classifying stack of a group smooth over the field; the \
classifying stack is constructed, and every model of it has this dimension"]
theorem dimension_classifyingStack_eq_neg_of_isSmooth
    (hGsm : Space.IsSmooth C (Spec (.of k)) hk G.obj.X.hom) :
    ∃ m : ℕ, Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = (m : WithBot ℕ∞) ∧
      (∃ 𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk,
        Nonempty (StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p
          𝒬.val.val.p)) ∧
      ∀ (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_ : StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p
          𝒬.val.val.p),
        ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
          dimension C (Spec (.of k)) hk 𝒬 hN = ((-(m : ℤ) : ℤ) : EInt) := by
  let : ModObj G.obj.X (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) :=
    ModObj.trivialAction _ _
  obtain ⟨m, hm, hex, hall⟩ := dimension_quotientStack_eq_of_isSmooth.{u, w} C hk G
    (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj))
    (Space.terminalSpace C (Spec (.of k)) hk).property
    (isLocallyOfFiniteType_id_terminalSpace C hk) hGsm
  refine ⟨m, hm, hex, fun 𝒬 e => ?_⟩
  obtain ⟨hN, hdim⟩ := hall 𝒬 e
  exact ⟨hN, hdim.trans (dimensionSubNat_dimension_terminalSpace C hk m)⟩

/-- **The dimension of an algebraic stack can be a negative integer.** Let `G` be a group algebraic
space of positive dimension, smooth over a field `k`. Then the classifying stack `BG` is an
algebraic stack, and every model of it is a locally Noetherian algebraic stack of negative
dimension. -/
@[stacks 0AFR "the dimension of an algebraic stack can be a negative integer: `dim BG < 0` for a \
group of positive dimension smooth over the field"]
theorem dimension_classifyingStack_lt_zero_of_isSmooth_of_pos
    (hGsm : Space.IsSmooth C (Spec (.of k)) hk G.obj.X.hom)
    (hpos : 0 < Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property) :
    (∃ 𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk,
        Nonempty (StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p
          𝒬.val.val.p)) ∧
      ∀ (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_ : StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p
          𝒬.val.val.p),
        ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
          dimension C (Spec (.of k)) hk 𝒬 hN < 0 := by
  obtain ⟨m, hm, hex, hall⟩ := dimension_classifyingStack_eq_neg_of_isSmooth.{u, w} C hk G hGsm
  refine ⟨hex, fun 𝒬 e => ?_⟩
  obtain ⟨hN, hdim⟩ := hall 𝒬 e
  exact ⟨hN, hdim ▸ neg_natCast_lt_zero_of_pos hm hpos⟩

/-! ### A group of finite type over a field, given the algebraicity of the quotient -/

/-- The terminal algebraic space over the spectrum of a field is locally Noetherian. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_terminalSpace :
    Space.HasEtaleLocalProperty C (Spec (.of k)) hk (Space.terminalSpace C (Spec (.of k)) hk).obj
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_field C hk
    (Space.terminalSpace C (Spec (.of k)) hk).property (𝟙 _)
    (isLocallyOfFiniteType_id_terminalSpace C hk)

open scoped CategoryTheory.MonObj in
/-- The source and the target of the action groupoid of a group locally of finite type over a
field are flat and locally of finite presentation. -/
@[sga "3 I 6.6" "special case"]
theorem isFlat_isLocallyOfFinitePresentation_groupoidOfAction
    (X : Over (Space.terminalSpace C (Spec (.of k)) hk).obj) [ModObj G.obj.X X]
    (hX : IsAlgebraicSpace C (Spec (.of k)) hk X.left)
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom) :
    let H := (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk) G.obj.X X
      G.property hX).groupoid
    (Space.IsFlat C (Spec (.of k)) hk H.source.hom ∧
      Space.IsFlat C (Spec (.of k)) hk H.target.hom) ∧
    (Space.IsLocallyOfFinitePresentation C (Spec (.of k)) hk H.source.hom ∧
      Space.IsLocallyOfFinitePresentation C (Spec (.of k)) hk H.target.hom) := by
  intro H
  let A := Space.terminalSpace C (Spec (.of k)) hk
  have hGflat : Space.IsFlat C (Spec (.of k)) hk G.obj.X.hom :=
    Space.isFlat_to_field C (Spec (.of k)) hk G.property (k := k) (Iso.refl _) G.obj.X.hom
  have hGlfp : Space.IsLocallyOfFinitePresentation C (Spec (.of k)) hk G.obj.X.hom :=
    Space.isLocallyOfFinitePresentation_of_isLocallyOfFiniteType C (Spec (.of k)) hk G.property
      A.property G.obj.X.hom (hasEtaleLocalProperty_isLocallyNoetherian_terminalSpace C hk) hGft
  have hprod : IsAlgebraicSpace C (Spec (.of k)) hk (Limits.pullback G.obj.X.hom X.hom) :=
    isAlgebraicSpace_pullback C (Spec (.of k)) hk G.obj.X.hom X.hom G.property hX A.property
  have hpb := AlgebraicSpaces.isPullback_fiberProduct C (Spec (.of k)) hk
    (ObjectProperty.homMk G.obj.X.hom : (⟨G.obj.X.left, G.property⟩ :
      AlgebraicSpaces C (Spec (.of k)) hk) ⟶ A)
    (ObjectProperty.homMk X.hom : (⟨X.left, hX⟩ : AlgebraicSpaces C (Spec (.of k)) hk) ⟶ A)
  have hsflat : Space.IsFlat C (Spec (.of k)) hk (snd G.obj.X X).left :=
    (Space.isFlat_isStableUnderBaseChange C (Spec (.of k)) hk).of_isPullback hpb hGflat
  have hslfp : Space.IsLocallyOfFinitePresentation C (Spec (.of k)) hk (snd G.obj.X X).left :=
    (Space.isLocallyOfFinitePresentation_isStableUnderBaseChange C (Spec (.of k)) hk).of_isPullback
      hpb hGlfp
  have hinviso : IsIso ((Stacks.Groupoids.ActionGroupoid.inverse G.obj.X X).left) := by
    refine ⟨(Stacks.Groupoids.ActionGroupoid.inverse G.obj.X X).left, ?_, ?_⟩ <;>
      exact congrArg (fun q : (G.obj.X ⊗ X) ⟶ (G.obj.X ⊗ X) => q.left)
        (Stacks.Groupoids.ActionGroupoid.inverse_comp_inverse G.obj.X X)
  have htgt : (γ[G.obj.X, X] : G.obj.X ⊗ X ⟶ X).left =
      (Stacks.Groupoids.ActionGroupoid.inverse G.obj.X X).left ≫ (snd G.obj.X X).left :=
    congrArg (fun q : (G.obj.X ⊗ X) ⟶ X => q.left)
      (Stacks.Groupoids.ActionGroupoid.inverse_source G.obj.X X).symm
  refine ⟨⟨hsflat, ?_⟩, ⟨hslfp, ?_⟩⟩
  · change Space.IsFlat C (Spec (.of k)) hk (γ[G.obj.X, X] : G.obj.X ⊗ X ⟶ X).left
    rw [htgt]
    exact Space.isFlat_comp C (Spec (.of k)) hk hprod hprod hX _ _
      (Space.isFlat_of_isIso _ hprod) hsflat
  · change Space.IsLocallyOfFinitePresentation C (Spec (.of k)) hk
      (γ[G.obj.X, X] : G.obj.X ⊗ X ⟶ X).left
    rw [htgt]
    exact Space.isLocallyOfFinitePresentation_comp C (Spec (.of k)) hk hprod hprod hX _ _
      (Space.isLocallyOfFinitePresentation_of_isSmooth C (Spec (.of k)) hk
        (Space.isSmooth_of_isIso C (Spec (.of k)) hk hprod hprod _)) hslfp

/-- **The dimension of a quotient stack by a group locally of finite type over a field, at a given
model.** Let `G` be a group algebraic space locally of finite type over a field `k`, acting on an
algebraic space `X` locally of finite type over `k`, and let `𝒬` be an algebraic stack equivalent
over the site to `[X/G]`. Then `𝒬` is locally Noetherian, `G` has finite dimension, and
`dim 𝒬 = dim(X) - dim(G)`. -/
theorem dimension_eq_of_quotientStackModel
    (X : Over (Space.terminalSpace C (Spec (.of k)) hk).obj) [ModObj G.obj.X X]
    (hX : IsAlgebraicSpace C (Spec (.of k)) hk X.left)
    (hXft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk X.hom)
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom)
    (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
    (e : StacksRepresentableCFG.EquivalenceOver
      (quotientStack (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk) G.obj.X X
        G.property hX).groupoid).p 𝒬.val.val.p) :
    ∃ m : ℕ, Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = (m : WithBot ℕ∞) ∧
      ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
        dimension C (Spec (.of k)) hk 𝒬 hN =
          dimensionSubNat (Space.dimension C (Spec (.of k)) hk X.left hX) m := by
  let A := Space.terminalSpace C (Spec (.of k)) hk
  let H := (Space.groupoidOfAction A G.obj.X X G.property hX).groupoid
  obtain ⟨m, hm⟩ := exists_dimension_eq_natCast_of_groupAlgebraicSpace C hk G hGft
  obtain ⟨⟨hsflat, htflat⟩, ⟨hslfp, htlfp⟩⟩ :=
    isFlat_isLocallyOfFinitePresentation_groupoidOfAction C hk G X hX hGft
  obtain ⟨hrep, hsurj, hflat, hlfp⟩ := quotientModelAtlasFppf (A := A) H 𝒬 e hsflat htflat
    hslfp htlfp
  have hlft := AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation
    C (Spec (.of k)) hk hlfp
  have hNX := hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_field C hk hX
    X.hom hXft
  have hcomp : AlgebraicStacks.IsLocallyOfFiniteType C (Spec (.of k)) hk
      (quotientStackModelProjection.{u, w} C (Spec (.of k)) hk A H 𝒬 e ≫
        quotientStackModelToBaseOfGroupoid.{u, w} C (Spec (.of k)) hk A H 𝒬 e) := by
    refine (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} C (Spec (.of k)) hk
      (fun _ _ h => Space.IsLocallyOfFiniteType C (Spec (.of k)) hk h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType C (Spec (.of k)) hk)
      (algebraicSpaceStack.{u, w} C (Spec (.of k)) hk H.objects.obj H.objects.property).property
      (algebraicSpaceStack.{u, w} C (Spec (.of k)) hk A.obj A.property).property _).2 ?_
    refine (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} C (Spec (.of k)) hk _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType C (Spec (.of k)) hk)
      (algebraicSpaceStack.{u, w} C (Spec (.of k)) hk H.objects.obj H.objects.property).property
      (algebraicSpaceStack.{u, w} C (Spec (.of k)) hk A.obj A.property).property
      H.objects.obj A.obj H.objects.property A.property
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) _).2 ?_
    rw [representingMap_quotientStackModelProjection_comp]
    exact hXft
  have hbase := AlgebraicStacks.isLocallyOfFiniteType_of_comp_of_fppf C (Spec (.of k)) hk _ _
    hcomp hrep hsurj hflat hlfp
  have hNA : HasPropertyOnSomeSchemeAtlas C (Spec (.of k)) hk
      (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (algebraicSpaceStack.{u, w} C (Spec (.of k)) hk A.obj A.property) := by
    let : ObjectProperty.IsLocal (fun Z : Scheme.{u} => IsLocallyNoetherian Z)
        (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
      ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
    exact (exists_scheme_atlas_iff_exists_space_atlas.{u, w} C (Spec (.of k)) hk _ _).mpr
      ((exists_space_atlas_iff_space.{u, w} C (Spec (.of k)) hk _ A.obj A.property).mpr
        (hasEtaleLocalProperty_isLocallyNoetherian_terminalSpace C hk))
  have hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬 :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType C (Spec (.of k)) hk _ hbase hNA
  refine ⟨m, hm, hN, dimension_eq_dimensionSubNat_of_flatChart.{u, w} C (Spec (.of k)) hk 𝒬 hN
    X.left hX hNX (quotientStackModelProjection.{u, w} C (Spec (.of k)) hk A H 𝒬 e) hflat hlft
    (exists_point_quotientStackModelProjection.{u, w} C (Spec (.of k)) hk A H 𝒬 e) m
    (fun t => ?_)⟩
  rw [relativeDimensionAt_quotientStackModelProjection_eq_dimension.{u, w} C hk G X hX hGft 𝒬 e
    hlft t, hm]

/-- **The dimension of a quotient stack by a group locally of finite type over a field, given the
algebraicity of quotients by flat groupoids.** Let `X` be an algebraic space locally of finite
type over a field `k` and let `G` be a group algebraic space locally of finite type over `k`
acting on `X`. Assume `h06FI`: the quotient stack of every groupoid in algebraic spaces whose
source and target are flat and locally of finite presentation is algebraic. Then the quotient
stack `[X/G]` has a model in the 2-category of algebraic stacks, and every model is locally
Noetherian of dimension `dim(X) - dim(G)`. -/
theorem dimension_quotientStack_eq_of_isAlgebraicStack_flat
    (h06FI : ∀ (A' : AlgebraicSpaces C (Spec (.of k)) hk)
      (H' : GroupoidInAlgebraicSpaces C (Spec (.of k)) hk A'),
      Space.IsFlat C (Spec (.of k)) hk H'.source.hom →
      Space.IsFlat C (Spec (.of k)) hk H'.target.hom →
      Space.IsLocallyOfFinitePresentation C (Spec (.of k)) hk H'.source.hom →
      Space.IsLocallyOfFinitePresentation C (Spec (.of k)) hk H'.target.hom →
      IsAlgebraicStack.{u, w} C (Spec (.of k)) hk (quotientStack H'))
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom)
    (X : Over (Space.terminalSpace C (Spec (.of k)) hk).obj) [ModObj G.obj.X X]
    (hX : IsAlgebraicSpace C (Spec (.of k)) hk X.left)
    (hXft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk X.hom) :
    ∃ m : ℕ, Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = (m : WithBot ℕ∞) ∧
      (∃ 𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk,
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (quotientStack (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk)
            G.obj.X X G.property hX).groupoid).p 𝒬.val.val.p)) ∧
      ∀ (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_ : StacksRepresentableCFG.EquivalenceOver
          (quotientStack (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk)
            G.obj.X X G.property hX).groupoid).p 𝒬.val.val.p),
        ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
          dimension C (Spec (.of k)) hk 𝒬 hN =
            dimensionSubNat (Space.dimension C (Spec (.of k)) hk X.left hX) m := by
  obtain ⟨m, hm⟩ := exists_dimension_eq_natCast_of_groupAlgebraicSpace C hk G hGft
  obtain ⟨⟨hsflat, htflat⟩, ⟨hslfp, htlfp⟩⟩ :=
    isFlat_isLocallyOfFinitePresentation_groupoidOfAction C hk G X hX hGft
  have hQ := h06FI _ _ hsflat htflat hslfp htlfp
  refine ⟨m, hm, ⟨AlgebraicStacks.smallModel C (Spec (.of k)) hk _ hQ,
    ⟨AlgebraicStacks.smallModelEquivalenceOver C (Spec (.of k)) hk _ hQ⟩⟩, fun 𝒬 e => ?_⟩
  obtain ⟨m', hm', hN, hdim⟩ :=
    dimension_eq_of_quotientStackModel.{u, w} C hk G X hX hXft hGft 𝒬 e
  have hmm : m' = m := by exact_mod_cast hm'.symm.trans hm
  exact ⟨hN, hmm ▸ hdim⟩

/-- **The dimension of the classifying stack of a group locally of finite type over a field, given
the algebraicity of quotients by flat groupoids.** Assume `h06FI`: the quotient stack of every
groupoid in algebraic spaces whose source and target are flat and locally of finite presentation is
algebraic. Then the classifying stack `BG` of a group algebraic space `G` locally of finite type
over a field has a model, and every model is locally Noetherian of dimension `-dim(G)`. -/
theorem dimension_classifyingStack_eq_neg_of_isAlgebraicStack_flat
    (h06FI : ∀ (A' : AlgebraicSpaces C (Spec (.of k)) hk)
      (H' : GroupoidInAlgebraicSpaces C (Spec (.of k)) hk A'),
      Space.IsFlat C (Spec (.of k)) hk H'.source.hom →
      Space.IsFlat C (Spec (.of k)) hk H'.target.hom →
      Space.IsLocallyOfFinitePresentation C (Spec (.of k)) hk H'.source.hom →
      Space.IsLocallyOfFinitePresentation C (Spec (.of k)) hk H'.target.hom →
      IsAlgebraicStack.{u, w} C (Spec (.of k)) hk (quotientStack H'))
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom) :
    ∃ m : ℕ, Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = (m : WithBot ℕ∞) ∧
      (∃ 𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk,
        Nonempty (StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p
          𝒬.val.val.p)) ∧
      ∀ (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_ : StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p
          𝒬.val.val.p),
        ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
          dimension C (Spec (.of k)) hk 𝒬 hN = ((-(m : ℤ) : ℤ) : EInt) := by
  let : ModObj G.obj.X (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) :=
    ModObj.trivialAction _ _
  obtain ⟨m, hm, hex, hall⟩ := dimension_quotientStack_eq_of_isAlgebraicStack_flat.{u, w} C hk G
    h06FI hGft (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj))
    (Space.terminalSpace C (Spec (.of k)) hk).property
    (isLocallyOfFiniteType_id_terminalSpace C hk)
  refine ⟨m, hm, hex, fun 𝒬 e => ?_⟩
  obtain ⟨hN, hdim⟩ := hall 𝒬 e
  exact ⟨hN, hdim.trans (dimensionSubNat_dimension_terminalSpace C hk m)⟩

/-- **The dimension of an algebraic stack can be a negative integer, given the algebraicity of
quotients by flat groupoids.** Assume `h06FI`: the quotient stack of every groupoid in algebraic
spaces whose source and target are flat and locally of finite presentation is algebraic. Then the
classifying stack of a group algebraic space of positive dimension, locally of finite type over a
field, has a model, and every model has negative dimension. -/
theorem dimension_classifyingStack_lt_zero_of_isAlgebraicStack_flat
    (h06FI : ∀ (A' : AlgebraicSpaces C (Spec (.of k)) hk)
      (H' : GroupoidInAlgebraicSpaces C (Spec (.of k)) hk A'),
      Space.IsFlat C (Spec (.of k)) hk H'.source.hom →
      Space.IsFlat C (Spec (.of k)) hk H'.target.hom →
      Space.IsLocallyOfFinitePresentation C (Spec (.of k)) hk H'.source.hom →
      Space.IsLocallyOfFinitePresentation C (Spec (.of k)) hk H'.target.hom →
      IsAlgebraicStack.{u, w} C (Spec (.of k)) hk (quotientStack H'))
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom)
    (hpos : 0 < Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property) :
    (∃ 𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk,
        Nonempty (StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p
          𝒬.val.val.p)) ∧
      ∀ (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_ : StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p
          𝒬.val.val.p),
        ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
          dimension C (Spec (.of k)) hk 𝒬 hN < 0 := by
  obtain ⟨m, hm, hex, hall⟩ :=
    dimension_classifyingStack_eq_neg_of_isAlgebraicStack_flat.{u, w} C hk G h06FI hGft
  refine ⟨hex, fun 𝒬 e => ?_⟩
  obtain ⟨hN, hdim⟩ := hall 𝒬 e
  exact ⟨hN, hdim ▸ neg_natCast_lt_zero_of_pos hm hpos⟩

/-! ### Characteristic zero: every group scheme locally of finite type -/

/-- **The dimension of a quotient stack in characteristic zero.** Let `X` be an algebraic space
locally of finite type over a field `k` of characteristic `0`, and let `G` be a group scheme
locally of finite type over `k` acting on `X`. Then `[X/G]` is an algebraic stack, and every model
of it is locally Noetherian of dimension `dim(X) - dim(G)`, the dimension of `G` being a natural
number. -/
@[stacks 0AFR "`dim [X/G] = dim X - dim G` over a field of characteristic zero, for every group \
scheme locally of finite type; the quotient stack is constructed"]
theorem dimension_quotientStack_eq_of_charZero [CharZero k]
    [G.obj.X.left.IsRepresentable]
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom)
    (X : Over (Space.terminalSpace C (Spec (.of k)) hk).obj) [ModObj G.obj.X X]
    (hX : IsAlgebraicSpace C (Spec (.of k)) hk X.left)
    (hXft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk X.hom) :
    ∃ m : ℕ, Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = (m : WithBot ℕ∞) ∧
      (∃ 𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk,
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (quotientStack (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk)
            G.obj.X X G.property hX).groupoid).p 𝒬.val.val.p)) ∧
      ∀ (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_ : StacksRepresentableCFG.EquivalenceOver
          (quotientStack (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk)
            G.obj.X X G.property hX).groupoid).p 𝒬.val.val.p),
        ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
          dimension C (Spec (.of k)) hk 𝒬 hN =
            dimensionSubNat (Space.dimension C (Spec (.of k)) hk X.left hX) m :=
  dimension_quotientStack_eq_of_isSmooth.{u, w} C hk G X hX hXft
    (Space.GroupAlgebraicSpace.isSmooth_of_charZero G hGft)

/-- **The dimension of the classifying stack in characteristic zero.** For a group scheme `G`
locally of finite type over a field `k` of characteristic `0`, the classifying stack `BG` is an
algebraic stack and every model of it is locally Noetherian of dimension `-dim(G)`. -/
@[stacks 0AFR "`dim BG = -dim G` over a field of characteristic zero, for every group scheme \
locally of finite type; the classifying stack is constructed"]
theorem dimension_classifyingStack_eq_neg_of_charZero [CharZero k]
    [G.obj.X.left.IsRepresentable]
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom) :
    ∃ m : ℕ, Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = (m : WithBot ℕ∞) ∧
      (∃ 𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk,
        Nonempty (StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p
          𝒬.val.val.p)) ∧
      ∀ (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_ : StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p
          𝒬.val.val.p),
        ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
          dimension C (Spec (.of k)) hk 𝒬 hN = ((-(m : ℤ) : ℤ) : EInt) :=
  dimension_classifyingStack_eq_neg_of_isSmooth.{u, w} C hk G
    (Space.GroupAlgebraicSpace.isSmooth_of_charZero G hGft)

/-- **The dimension of an algebraic stack can be a negative integer, in characteristic zero.** For
a group scheme `G` of positive dimension, locally of finite type over a field of characteristic
`0`, the classifying stack `BG` is an algebraic stack of negative dimension. -/
@[stacks 0AFR "the dimension of an algebraic stack can be a negative integer: `dim BG < 0` over a \
field of characteristic zero, for every group scheme of positive dimension locally of finite type"]
theorem dimension_classifyingStack_lt_zero_of_charZero_of_pos [CharZero k]
    [G.obj.X.left.IsRepresentable]
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom)
    (hpos : 0 < Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property) :
    (∃ 𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk,
        Nonempty (StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p
          𝒬.val.val.p)) ∧
      ∀ (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
        (_ : StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p
          𝒬.val.val.p),
        ∃ hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬,
          dimension C (Spec (.of k)) hk 𝒬 hN < 0 :=
  dimension_classifyingStack_lt_zero_of_isSmooth_of_pos.{u, w} C hk G
    (Space.GroupAlgebraicSpace.isSmooth_of_charZero G hGft) hpos

end OverField

end AlgebraicGeometry.Stack

end
