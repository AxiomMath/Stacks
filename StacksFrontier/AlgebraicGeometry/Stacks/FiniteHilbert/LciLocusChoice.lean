module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMapIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocus
public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointComparison

/-!
# The local complete intersection locus does not depend on the choice of data

The relative map `x_α : Z ⟶ X_y` of **Stacks 06CK** attached to an object `Ξ = (U, Z, y, x, α)`
of the relative finite Hilbert category `ℋ_d(𝒳/𝒴)` is read off a
`AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData` for `Ξ`: a scheme-valued point of `𝒴`
over `U` extending the object `y`, an algebraic space `X_y` over `U` representing the 2-fibre
product `(Sch/U)_{fppf} ×_{y, 𝒴, F} 𝒳`, and a comparison isomorphism of the restriction of the
point to `Z` with `F x`. None of these is canonical, and
`AlgebraicGeometry.Stack.FiniteHilbert.lciLocus` quantifies over all of them.

The remark following Stacks 06CK is that the choice does not matter, and this file proves it: any
two sets of data for one quintuple give isomorphic relative maps, so the condition cutting out the
locus has only to be checked for *one* set of data.

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.pointIso`: two sets of data for one
  quintuple have 2-isomorphic scheme-valued points.
* `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.alpha_eq`: the 2-isomorphism of the
  points identifies the two comparison isomorphisms.
* `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.exists_iso_map`: **the remark following
  Stacks 06CK**, the two relative maps agree up to an isomorphism of their targets.
* `AlgebraicGeometry.Stack.FiniteHilbert.lciLocus_iff`: a quintuple lies in the local complete
  intersection locus exactly when the relative map of *one* chosen set of data is unramified and a
  local complete intersection morphism.

## References

* [Stacks Project, Tag 06CJ](https://stacks.math.columbia.edu/tag/06CJ)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
* [Stacks Project, Tag 06CL](https://stacks.math.columbia.edu/tag/06CL)
-/

@[expose] public section

open CategoryTheory Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w} (BigFppfOver B S hS) (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} {d : ℕ}

namespace FiniteHilbert

/-! ### The two scheme-valued points of a quintuple are 2-isomorphic -/

/-- The comparison morphism of a `RelativeMapData` to the object `y` of the quintuple is
invertible. -/
theorem RelativeMapData.isIso_yUnit {P : Object B S hS 𝒳 𝒴 F d} (D : RelativeMapData P) :
    IsIso D.yUnit :=
  have := D.yUnit_over
  have := 𝒴.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift (𝟙 P.U) D.yUnit
  Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒴.toBasedCategory.p (𝟙 P.U) D.yUnit

/-- The morphism of the values of the two points at the terminal object of the big fppf site of
`U` obtained by composing the first comparison morphism with the inverse of the second. -/
noncomputable def RelativeMapData.unitComparison {P : Object B S hS 𝒳 𝒴 F d}
    (D₁ D₂ : RelativeMapData P) : D₁.y.obj P.baseOver ⟶ D₂.y.obj P.baseOver :=
  have := D₂.isIso_yUnit
  D₁.yUnit ≫ CategoryTheory.inv D₂.yUnit

/-- The morphism of the values at the terminal object is vertical. -/
theorem RelativeMapData.isHomLift_unitComparison {P : Object B S hS 𝒳 𝒴 F d}
    (D₁ D₂ : RelativeMapData P) :
    𝒴.toBasedCategory.p.IsHomLift (𝟙 P.U) (D₁.unitComparison D₂) := by
  have := D₁.yUnit_over
  have := D₂.yUnit_over
  have := D₂.isIso_yUnit
  have hinv : 𝒴.toBasedCategory.p.IsHomLift (𝟙 P.U) (CategoryTheory.inv D₂.yUnit) :=
    IsHomLift.lift_id_inv_isIso 𝒴.toBasedCategory.p P.U D₂.yUnit
  exact IsHomLift.comp_of_lift_id 𝒴.toBasedCategory.p P.U D₁.yUnit
    (CategoryTheory.inv D₂.yUnit)

/-- **Two sets of data for one quintuple have 2-isomorphic scheme-valued points.** The two points
take isomorphic values at the terminal object of the big fppf site of `U`, both being identified
with the object `y` of the quintuple, so the 2-Yoneda lemma extends that isomorphism to a natural
isomorphism of the points with vertical components. -/
noncomputable def RelativeMapData.pointIso {P : Object B S hS 𝒳 𝒴 F d}
    (D₁ D₂ : RelativeMapData P) : D₁.y ≅ D₂.y :=
  Functor.slicePointIso 𝒴.toBasedCategory.p P.U D₁.y D₂.y
    𝒴.isStackInGroupoids.isFiberedInGroupoids D₁.y_comp D₂.y_comp
    (D₁.unitComparison D₂) (D₁.isHomLift_unitComparison D₂)

/-- Every component of the 2-isomorphism of the two points is vertical. -/
theorem RelativeMapData.isHomLift_pointIso_hom_app {P : Object B S hS 𝒳 𝒴 F d}
    (D₁ D₂ : RelativeMapData P) (a : BigFppfOver B P.U.left.1 P.U.left.2) :
    𝒴.toBasedCategory.p.IsHomLift (𝟙 ((Over.map P.U.hom).obj a))
      ((D₁.pointIso D₂).hom.app a) :=
  Functor.isHomLift_slicePointApp 𝒴.toBasedCategory.p P.U D₁.y D₂.y
    𝒴.isStackInGroupoids.isFiberedInGroupoids D₁.y_comp D₂.y_comp
    (D₁.unitComparison D₂) (D₁.isHomLift_unitComparison D₂) a

/-- The factorisation characterising the 2-isomorphism of the two points, at the cover of the
quintuple: its component there, followed by the restriction of the second point to the cover, is
the restriction of the first point to the cover followed by the comparison of the values at the
terminal object. -/
theorem RelativeMapData.pointIso_hom_app_fac {P : Object B S hS 𝒳 𝒴 F d}
    (D₁ D₂ : RelativeMapData P) :
    (D₁.pointIso D₂).hom.app P.coverOver ≫ D₂.y.map P.coverToBase =
      D₁.y.map P.coverToBase ≫ D₁.unitComparison D₂ :=
  Functor.slicePointApp_fac 𝒴.toBasedCategory.p P.U D₁.y D₂.y
    𝒴.isStackInGroupoids.isFiberedInGroupoids D₁.y_comp D₂.y_comp
    (D₁.unitComparison D₂) (D₁.isHomLift_unitComparison D₂) P.coverOver

/-! ### The two comparison isomorphisms correspond -/

/-- **The 2-isomorphism of the points identifies the two comparison isomorphisms.** -/
theorem RelativeMapData.alpha_eq {P : Object B S hS 𝒳 𝒴 F d} (D₁ D₂ : RelativeMapData P) :
    D₁.α.hom = (D₁.pointIso D₂).hom.app P.coverOver ≫ D₂.α.hom := by
  have hp := 𝒴.isStackInGroupoids.isFiberedInGroupoids
  have hmap₂ : 𝒴.toBasedCategory.p.IsHomLift ((Over.map P.U.hom).map P.coverToBase)
      (D₂.y.map P.coverToBase) :=
    TwoFibreProductOver.DiagonalFibre.VertHom.isHomLift_map D₂.y_comp P.coverToBase
  have h₂u := D₂.yUnit_over
  have hrestr : 𝒴.toBasedCategory.p.IsHomLift ((Over.map P.U.hom).map P.coverToBase)
      (D₂.y.map P.coverToBase ≫ D₂.yUnit) :=
    IsHomLift.comp_lift_id_right' 𝒴.toBasedCategory.p ((Over.map P.U.hom).map P.coverToBase)
      (D₂.y.map P.coverToBase) P.U D₂.yUnit
  have hcart : 𝒴.toBasedCategory.p.IsStronglyCartesian
      ((Over.map P.U.hom).map P.coverToBase) (D₂.y.map P.coverToBase ≫ D₂.yUnit) :=
    hp.isStronglyCartesian_homLift _ _
  have h₁α := D₁.α_over
  have h₂α := D₂.α_over
  have hθ := D₁.isHomLift_pointIso_hom_app D₂ P.coverOver
  have key : D₁.α.inv ≫ (D₁.pointIso D₂).hom.app P.coverOver = D₂.α.inv := by
    refine Functor.IsStronglyCartesian.ext 𝒴.toBasedCategory.p
      ((Over.map P.U.hom).map P.coverToBase) (D₂.y.map P.coverToBase ≫ D₂.yUnit)
      (𝟙 ((Over.map P.U.hom).obj P.coverOver)) ?_
    have := D₂.isIso_yUnit
    rw [D₂.α_comp, ← D₁.α_comp]
    simp [reassoc_of% D₁.pointIso_hom_app_fac D₂, RelativeMapData.unitComparison]
  rw [(Iso.inv_comp_eq _).1 key]
  simp

/-! ### Independence of the relative map -/

/-- Two sets of data exhibiting the relative map of one object of `ℋ_d(𝒳/𝒴)` give the same
morphism up to an isomorphism of its target. -/
@[stacks 06CK "the remark following the tag: the relative map does not depend on the data \
exhibiting it"]
theorem RelativeMapData.exists_iso_map {P : Object B S hS 𝒳 𝒴 F d}
    (D₁ D₂ : RelativeMapData P) :
    ∃ i : D₁.Xy ≅ D₂.Xy, D₁.map.hom ≫ i.hom = D₂.map.hom :=
  ⟨relativeSpaceIso F D₁.e D₂.e (D₁.pointIso D₂) (D₁.isHomLift_pointIso_hom_app D₂),
    relativeMap_hom_comp_relativeSpaceIso F D₁.e D₂.e (D₁.pointIso D₂)
      (D₁.isHomLift_pointIso_hom_app D₂) (hXy₁ := D₁.isAlgebraicSpace)
      (hXy₂ := D₂.isAlgebraicSpace) P.coverOver P.x P.x_over_coverOver D₁.α D₁.α_over
      D₂.α D₂.α_over (D₁.alpha_eq D₂)⟩

/-- A condition on morphisms of algebraic spaces which is tested on étale charts is unchanged by
composing with an isomorphism of the target. -/
private theorem holdsOnEveryEtaleChart_comp_iso_iff {V : Scheme.{u}} (hV : B.Contains V)
    (Q : MorphismProperty Scheme.{u})
    {X Y Y' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (j : Y ≅ Y') :
    Space.HoldsOnEveryEtaleChart B V hV Q (f ≫ j.hom) ↔
      Space.HoldsOnEveryEtaleChart B V hV Q f := by
  have hR := Space.holdsOnEveryEtaleChart_respectsIso_presheaf B V hV Q
  exact MorphismProperty.cancel_right_of_respectsIso
    (P := fun ⦃X Y : (BigFppfOver B V hV)ᵒᵖ ⥤ Type u⦄ (g : X ⟶ Y) =>
      Space.HoldsOnEveryEtaleChart B V hV Q g) f j.hom

/-- A quintuple lies in the local complete intersection locus exactly when the relative map
attached to *one* set of data exhibiting it is unramified and a local complete intersection
morphism. -/
@[stacks 06CJ "membership of the locus is testable on a single choice of the data exhibiting the \
relative map"]
theorem lciLocus_iff {P : Object B S hS 𝒳 𝒴 F d} (D : RelativeMapData P) :
    lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) P ↔
      (Space.IsUnramified B P.U.left.1 P.U.left.2 D.map.hom ∧
        Space.IsLocalCompleteIntersection B P.U.left.1 P.U.left.2 D.map.hom) := by
  refine ⟨fun h => h D, fun h D' => ?_⟩
  obtain ⟨i, hi⟩ := D'.exists_iso_map D
  rw [← hi] at h
  exact ⟨(holdsOnEveryEtaleChart_comp_iso_iff P.U.left.2 _ _ i).mp h.1,
    (holdsOnEveryEtaleChart_comp_iso_iff P.U.left.2 _ _ i).mp h.2⟩

end FiniteHilbert

end AlgebraicGeometry.Stack

end
