module

public import Mathlib.Topology.Semicontinuity.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# Semicontinuity of the fibre dimension of a morphism of algebraic spaces

The two semicontinuity statements about the fibre-dimension function of
**Stacks 0D4P** and **Stacks 0D4Q** both reduce the question to an étale scheme chart of the
target. This file carries that reduction: the comparison of the fibre dimension of a morphism
with the fibre dimension of a chart of it, the identification of the absolute dimension of a
represented algebraic space with the Krull dimension of the representing scheme, and the
characterisation of a fibre-dimension bound as a condition on the relative dimension at each
point above the given one.

## Main results

* `AlgebraicGeometry.Space.relativeDimensionAt_eq_of_etale_chart`: for a morphism to a
  represented algebraic space, having relative dimension `d` at the image of a point of an
  étale chart is the same as having relative dimension `d` at that point of the chart.
* `AlgebraicGeometry.Space.fiberDimension_eq_of_surjective_etale_chart`: the fibre-dimension
  function is unchanged on passing to a surjective étale chart of the source.
* `AlgebraicGeometry.Space.dimension_yoneda_eq_topologicalKrullDim`: the dimension of a
  represented algebraic space is the Krull dimension of the representing scheme.
* `AlgebraicGeometry.Space.fiberDimension_le_iff`: a fibre-dimension bound by a natural number
  is a bound on the relative dimension at every point above the given one.
* `lowerSemicontinuous_of_open_surjective`: lower semicontinuity descends along a surjective
  open map.

## Implementation notes

`AlgebraicGeometry.Space.fiberDimension` is an infimum over `WithBot ℕ∞`, so turning a bound on
it into a pointwise statement needs the infimum to be attained below a natural number; that is
what `AlgebraicGeometry.Space.fiberDimension_le_iff` supplies, using that `n` is not a
predecessor prelimit in `WithBot ℕ∞`.

The point topology of Tag 03BX, `AlgebraicGeometry.Space.pointTopology`, is defined for an
arbitrary presheaf, so none of the statements here carries an algebraicity hypothesis for the
sake of the topology alone.

## References

* [Stacks Project, Tag 0D4M](https://stacks.math.columbia.edu/tag/0D4M)
* [Stacks Project, Tag 0D4P](https://stacks.math.columbia.edu/tag/0D4P)
* [Stacks Project, Tag 0D4Q](https://stacks.math.columbia.edu/tag/0D4Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- Lower semicontinuity descends along a surjective open map: the superlevel sets of the
function downstairs are the images of the superlevel sets of its composite with the map. -/
theorem lowerSemicontinuous_of_open_surjective {A C : Type*} [TopologicalSpace A]
    [TopologicalSpace C] {α : Type*} [Preorder α] (f : C → α) (g : A → C)
    (hg : IsOpenMap g) (hgsurj : Function.Surjective g)
    (hfg : LowerSemicontinuous (f ∘ g)) : LowerSemicontinuous f := by
  rw [lowerSemicontinuous_iff_isOpen_preimage] at hfg ⊢
  intro a
  rw [← Set.image_preimage_eq (f ⁻¹' Set.Ioi a) hgsurj]
  exact hg _ (hfg a)

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The dimension of a represented algebraic space is the Krull dimension of the representing
scheme: the identity is an étale chart, so the dimension at each point is the local dimension
of the scheme at the corresponding scheme point, and the Krull dimension of a topological space
is the supremum of its local dimensions. -/
theorem dimension_yoneda_eq_topologicalKrullDim (U : BigFppfOver B S hS) :
    dimension B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) =
      topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) := by
  classical
  let X := (BigFppfOver.toScheme B S hS).obj U
  have hdim : topologicalKrullDim X = ⨆ x : X, topologicalKrullDimAt X x := by
    simpa only [TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim] using
      TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim X
  have hchart (p : FieldValuedPoint B S hS (yoneda.obj U)) :
      dimensionAtPoint B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
        (p.class B S hS (yoneda.obj U)) = topologicalKrullDimAt X (schemePoint B S hS U p) :=
    dimensionAtPoint_eq_of_etale_chart B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      _ U (𝟙 (yoneda.obj U)) (presheaf_etale_id B S hS U) p rfl
  unfold dimension
  rw [hdim]
  refine le_antisymm (iSup_le fun x ↦ ?_) (iSup_le fun x ↦ ?_)
  · obtain ⟨p, rfl⟩ := Quot.exists_rep x
    rw [hchart p]
    exact le_iSup (fun z : X ↦ topologicalKrullDimAt X z) (schemePoint B S hS U p)
  · rw [← schemePointRepresentative_point B S hS U x, ← hchart]
    exact le_iSup (fun y : points B S hS (yoneda.obj U) ↦
      dimensionAtPoint B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) y) _

/-- Relative dimension at a point is detected on an étale chart of the source: for a morphism
to a represented algebraic space, having relative dimension `d` at the image of a point of an
étale chart is having relative dimension `d` at that point of the chart. -/
theorem relativeDimensionAt_eq_of_etale_chart
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (V : BigFppfOver B S hS) (f : F ⟶ yoneda.obj V)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hcomm : yoneda.map h = a ≫ f)
    (d : ℕ∞) (x : points B S hS (yoneda.obj U)) :
    HasRelativeDimensionAt d B S hS f (pointsMap B S hS (yoneda.obj U) a x) ↔
      HasRelativeDimensionAt d B S hS (yoneda.map h) x := by
  classical
  have hV := isAlgebraicSpace_yoneda B S hS V
  let Q := @AlgebraicGeometry.HasFiberDimensionAt.{u} d
  have hQ : MorphismOfGerms.IsEtaleLocalOnSourceAndTarget Q :=
    AlgebraicGeometry.fiberDimensionAt_isEtaleLocalOnSourceAndTarget d
  have hidV := presheaf_etale_id B S hS V
  refine Quot.inductionOn x fun p ↦ ?_
  let x' := pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U))
  change HoldsOnEveryEtaleChartAtPoint B S hS Q f x' ↔
    HoldsOnEveryEtaleChartAtPoint B S hS Q (yoneda.map h) (p.class B S hS (yoneda.obj U))
  let c : EtaleChartAtPoint B S hS f x' :=
    { U := U
      V := V
      a := a
      b := 𝟙 (yoneda.obj V)
      h := h
      a_etale := ha
      b_etale := hidV
      comm := by simpa using hcomm
      representative := p
      point := IsLocalRing.closedPoint p.carrier
      maps_to := rfl }
  let c' : EtaleChartAtPoint B S hS (yoneda.map h) (p.class B S hS (yoneda.obj U)) :=
    { U := U
      V := V
      a := 𝟙 (yoneda.obj U)
      b := 𝟙 (yoneda.obj V)
      h := h
      a_etale := presheaf_etale_id B S hS U
      b_etale := hidV
      comm := by simp
      representative := p
      point := IsLocalRing.closedPoint p.carrier
      maps_to := rfl }
  have hc : c.sourcePoint B S hS = c'.sourcePoint B S hS := rfl
  exact ⟨fun hleft ↦ (holdsOnEveryEtaleChartAtPoint_iff_some B S hS Q hQ
      (isAlgebraicSpace_yoneda B S hS U) hV (yoneda.map h)
      (p.class B S hS (yoneda.obj U))).mpr ⟨c', by simpa [Q, hc] using hleft c⟩,
    fun hright ↦ (holdsOnEveryEtaleChartAtPoint_iff_some B S hS Q hQ hF hV f x').mpr
      ⟨c, by simpa [Q, hc] using hright c'⟩⟩

/-- The fibre-dimension function of a morphism to a represented algebraic space is unchanged on
replacing the source by a surjective étale chart of it: the two index sets of the defining
infimum correspond under the surjection on points, and the relative dimensions agree by
`AlgebraicGeometry.Space.relativeDimensionAt_eq_of_etale_chart`. -/
theorem fiberDimension_eq_of_surjective_etale_chart
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (V : BigFppfOver B S hS) (f : F ⟶ yoneda.obj V)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F) (h : U ⟶ V)
    (haEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haSurjective : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hcomm : yoneda.map h = a ≫ f) :
    fiberDimension B S hS f = fiberDimension B S hS (yoneda.map h) := by
  classical
  have hcomp : pointsMap B S hS (yoneda.obj U) (yoneda.map h) =
      pointsMap B S hS F f ∘ pointsMap B S hS (yoneda.obj U) a := by
    rw [← pointsMap_comp, hcomm]
  funext y
  unfold fiberDimension
  congr 1
  ext d
  change (∀ x : points B S hS F, pointsMap B S hS F f x = y →
      ∃ e : ℕ∞, HasRelativeDimensionAt e B S hS f x ∧ (e : WithBot ℕ∞) ≤ d) ↔
    ∀ x : points B S hS (yoneda.obj U),
      pointsMap B S hS (yoneda.obj U) (yoneda.map h) x = y →
        ∃ e : ℕ∞, HasRelativeDimensionAt e B S hS (yoneda.map h) x ∧ (e : WithBot ℕ∞) ≤ d
  refine ⟨fun hall u huy ↦ ?_, fun hall x hxy ↦ ?_⟩
  · have hxy : pointsMap B S hS F f (pointsMap B S hS (yoneda.obj U) a u) = y := by
      simpa using (congrFun hcomp u).symm.trans huy
    obtain ⟨e, he, hed⟩ := hall _ hxy
    exact ⟨e,
      (relativeDimensionAt_eq_of_etale_chart B S hS hF V f U a h haEtale hcomm e u).mp he, hed⟩
  · obtain ⟨u, rfl⟩ := (surjective_iff_surjective_pointsMap B S hS F hF U a).mp haSurjective x
    have huy : pointsMap B S hS (yoneda.obj U) (yoneda.map h) u = y := by
      rw [hcomp]
      simpa using hxy
    obtain ⟨e, he, hed⟩ := hall _ huy
    exact ⟨e,
      (relativeDimensionAt_eq_of_etale_chart B S hS hF V f U a h haEtale hcomm e u).mpr he, hed⟩

/-- A fibre-dimension bound by a natural number is exactly a bound on the relative dimension at
every point above the given point of the target: the infimum defining the fibre dimension is
attained at `n`, because `n` is not a predecessor prelimit in `WithBot ℕ∞`. -/
theorem fiberDimension_le_iff {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (y : points B S hS Y) (n : ℕ) :
    fiberDimension B S hS f y ≤ (n : WithBot ℕ∞) ↔
      ∀ x : points B S hS X, pointsMap B S hS X f x = y →
        ∃ e : ℕ∞, HasRelativeDimensionAt e B S hS f x ∧ (e : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
  rw [fiberDimension, sInf_le_iff_of_not_isPredPrelimit]
  · refine ⟨fun ⟨d, hd, hdn⟩ x hx ↦ ?_, fun h ↦ ⟨(n : WithBot ℕ∞), h, le_rfl⟩⟩
    obtain ⟨e, he, hed⟩ := hd x hx
    exact ⟨e, he, hed.trans hdn⟩
  · refine Order.not_isPredPrelimit_iff.2 ⟨((SuccOrder.succ (n : ℕ∞)) : WithBot ℕ∞), ?_⟩
    change ((n : ℕ∞) : WithBot ℕ∞) ⋖ ((SuccOrder.succ (n : ℕ∞)) : WithBot ℕ∞)
    exact WithBot.coe_covBy_coe.mpr (Order.covBy_succ_of_not_isMax (by simp))

end AlgebraicGeometry.Space

end
