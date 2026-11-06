module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Conditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.MonomorphicFieldRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFieldRepresentative

/-!
# Finite chart fibres and a quasi-compact monomorphic field-valued representative

Let `X` be an algebraic space over a scheme `S` and let `x` be a point of `|X|`. Stacks 03JV
lists six equivalent conditions on `x`. Condition (1) is that for every étale chart
`φ : h_U ⟶ X` by an affine scheme, setting `R = h_U ×_X h_U`, the fibres of `|U| → |X|` and of
`|R| → |X|` above `x` are finite; condition (4) is that `x` is in the class of a quasi-compact
monomorphism `Spec k ⟶ X` with `k` a field. This file proves that the two are equivalent.

Decency, `AlgebraicGeometry.Space.IsDecentSpace`, is condition (4) at every point, and
condition (1) is property `(γ)` of Stacks 03JX at a point
(`AlgebraicGeometry.Space.HasFiniteChartAndRelationFibersAt`), so a decent space is exactly one
with property `(γ)`.

## Main results

The names below live in the namespace `AlgebraicGeometry.Space`, which is omitted where a name
is too long to spell with it.

* `hasFiniteChartAndRelationFibersAt_of_hasQuasiCompactMonomorphicFieldRepresentative` and
  `hasQuasiCompactMonomorphicFieldRepresentative_of_hasFiniteChartAndRelationFibersAt` are the
  two implications, and
  `hasFiniteChartAndRelationFibersAt_iff_hasQuasiCompactMonomorphicFieldRepresentative` the
  resulting equivalence of conditions (1) and (4) of Stacks 03JV.
* `isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint`: decency of an algebraic
  space is property `(γ)` of Stacks 03JX.

## References

* [Stacks Project, Tag 024X](https://stacks.math.columbia.edu/tag/024X)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 06RV](https://stacks.math.columbia.edu/tag/06RV)
* [Stacks Project, Tag 0ABU](https://stacks.math.columbia.edu/tag/0ABU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

local instance (priority := high) : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W)
    (g : Z ⟶ W) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

/-! ### Condition (1) implies condition (4) -/

/-- The fibre product of an étale chart with a monomorphism from the spectrum of a field has
finitely many points, as soon as the fibre of the chart above the point presented by that field
has. -/
private theorem finite_toScheme_of_isPullback_fieldMorphism
    (p : FieldValuedPoint B S hS X) (hmono : Mono (fieldMorphism B S hS X p))
    {V W : BigFppfOver B S hS} (ψ : yoneda.obj V ⟶ X)
    (hfib : (pointsMap B S hS (yoneda.obj V) ψ ⁻¹' {p.class B S hS X}).Finite)
    (a : W ⟶ V) (g : W ⟶ p.siteObject)
    (sq : IsPullback (yoneda.map a) (yoneda.map g) ψ (fieldMorphism B S hS X p)) :
    Finite ((BigFppfOver.toScheme B S hS).obj W) := by
  have _ : Mono (yoneda.map a) := sq.mono_fst_of_mono hmono
  have hinj : Function.Injective (pointsMap B S hS (yoneda.obj W) (yoneda.map a)) :=
    pointsMap_injective_of_mono B S hS _
  have _ : Finite ↥(pointsMap B S hS (yoneda.obj V) ψ ⁻¹' {p.class B S hS X}) :=
    hfib.to_subtype
  have hmem : ∀ w : points B S hS (yoneda.obj W),
      pointsMap B S hS (yoneda.obj W) (yoneda.map a) w ∈
        pointsMap B S hS (yoneda.obj V) ψ ⁻¹' {p.class B S hS X} := by
    intro w
    show pointsMap B S hS (yoneda.obj V) ψ _ = p.class B S hS X
    rw [pointsMap_apply_comm B S hS sq.w w]
    exact pointsMap_fieldMorphism_eq_class B S hS p _
  have _ : Finite (points B S hS (yoneda.obj W)) :=
    Finite.of_injective (fun w ↦ (⟨_, hmem w⟩ :
        ↥(pointsMap B S hS (yoneda.obj V) ψ ⁻¹' {p.class B S hS X})))
      fun _ _ huv ↦ hinj (congrArg Subtype.val huv)
  exact Finite.of_equiv _ (pointsEquivScheme B S hS W)

/-- The fibre product of an étale chart with a monomorphism from the spectrum of a field is
finite over that spectrum, as soon as the fibre of the chart above the point presented by the
field is finite. -/
private theorem isFinite_toScheme_map_of_isPullback_fieldMorphism
    (p : FieldValuedPoint B S hS X) (hmono : Mono (fieldMorphism B S hS X p))
    {V W : BigFppfOver B S hS} (ψ : yoneda.obj V ⟶ X)
    (hψ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) ψ)
    (hfib : (pointsMap B S hS (yoneda.obj V) ψ ⁻¹' {p.class B S hS X}).Finite)
    (a : W ⟶ V) (g : W ⟶ p.siteObject)
    (sq : IsPullback (yoneda.map a) (yoneda.map g) ψ (fieldMorphism B S hS X p)) :
    _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map g) := by
  have _ : Finite ((BigFppfOver.toScheme B S hS).obj W) :=
    finite_toScheme_of_isPullback_fieldMorphism B S hS X p hmono ψ hfib a g sq
  have hetale : Etale ((BigFppfOver.toScheme B S hS).map g) :=
    hψ.property (fieldMorphism B S hS X p) (yoneda.map a) g sq
  have _ : QuasiCompact ((BigFppfOver.toScheme B S hS).map g) := by
    rw [quasiCompact_iff_forall_isAffineOpen]
    exact fun _ _ ↦ (Set.toFinite _).isCompact
  obtain ⟨hft, hur⟩ :=
    (etale_iff_unramified_over_field p.carrier
      ((BigFppfOver.toScheme B S hS).map g)).mp hetale
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj W) :=
    isAffine_of_unramified_quasiCompact p.carrier ((BigFppfOver.toScheme B S hS).map g)
  exact isFinite_of_isAffine_of_etale_over_field p.carrier
    ((BigFppfOver.toScheme B S hS).map g)

/-- A monomorphism from the spectrum of a field into an algebraic space over `S` is
quasi-compact as soon as every étale chart by an affine scheme has a finite fibre above the
point it presents. -/
private theorem isQuasiCompact_fieldMorphism_of_finite_chart_fibres
    (hX : IsAlgebraicSpace B S hS X) (p : FieldValuedPoint B S hS X)
    (hmono : Mono (fieldMorphism B S hS X p))
    (hfib : ∀ V : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ ψ : yoneda.obj V ⟶ X, (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) ψ →
        (pointsMap B S hS (yoneda.obj V) ψ ⁻¹' {p.class B S hS X}).Finite) :
    IsQuasiCompact B S hS (fieldMorphism B S hS X p) :=
  isQuasiCompact_fieldMorphism_of_isFinite_pullback B S hS hX p
    fun V hV ψ hψ {_W} a g sq ↦ isFinite_toScheme_map_of_isPullback_fieldMorphism B S hS X p
      hmono ψ hψ (hfib V hV ψ hψ) a g sq

/-- If every étale chart of an algebraic space over `S` by an affine scheme and its
self-intersection have finite fibres above `x`, then `x` is in the class of a quasi-compact
monomorphism from the spectrum of a field. -/
theorem hasQuasiCompactMonomorphicFieldRepresentative_of_hasFiniteChartAndRelationFibersAt
    (hX : IsAlgebraicSpace B S hS X) (x : points B S hS X)
    (h : HasFiniteChartAndRelationFibersAt B S hS X x) :
    HasQuasiCompactMonomorphicFieldRepresentative B S hS X x := by
  obtain ⟨U, φ, a, hUaff, hφ, hax⟩ := exists_affine_etale_chart_of_point B S hS X hX x
  obtain ⟨hfinU, hfinR⟩ := h U hUaff φ hφ
  have hrel : HasFiniteRelationFiberAt B S hS X x := by
    refine ⟨U, φ, a, a, (isEtale_iff_presheaf_of_yoneda B S hS φ).2 hφ, hax, hax, ?_⟩
    refine hfinR.subset fun r hr ↦ ?_
    show pointsMap B S hS (pullback φ φ) (pullback.fst φ φ ≫ φ) r = x
    rw [pointsMap_comp_apply, hr.1, hax]
  obtain ⟨p, hpx, hmono⟩ :=
    hasMonomorphicFieldRepresentative_of_hasEtaleQuasiCompactFieldRepresentative B S hS hX x
      ((hasFiniteRelationFiberAtEveryEtaleChart_iff_hasEtaleQuasiCompactFieldRepresentative
        B S hS X hX x).mp
        (hasFiniteRelationFiberAtEveryEtaleChart_of_hasFiniteRelationFiberAt B S hS X hX x hrel))
  refine ⟨p, hpx, hmono, isQuasiCompact_fieldMorphism_of_finite_chart_fibres B S hS X hX p hmono
    fun V hV ψ hψ ↦ ?_⟩
  rw [hpx]
  exact (h V hV ψ hψ).1

/-! ### Condition (4) implies condition (1) -/

/-- If a point of an algebraic space over `S` is in the class of a quasi-compact monomorphism
from the spectrum of a field, then every étale chart by an affine scheme and its
self-intersection have finite fibres above it. -/
theorem hasFiniteChartAndRelationFibersAt_of_hasQuasiCompactMonomorphicFieldRepresentative
    (hX : IsAlgebraicSpace B S hS X) (x : points B S hS X)
    (h : HasQuasiCompactMonomorphicFieldRepresentative B S hS X x) :
    HasFiniteChartAndRelationFibersAt B S hS X x := by
  obtain ⟨p, hpx, hmono, hqc⟩ := h
  have hevery : HasFiniteRelationFiberAtEveryEtaleChart B S hS X x :=
    hasFiniteRelationFiberAtEveryEtaleChart_of_hasMonomorphicFieldRepresentative B S hS X hX x
      ⟨p, hpx, hmono⟩
  intro U hU φ hφ
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hfinU : (pointsMap B S hS (yoneda.obj U) φ ⁻¹' {x}).Finite := by
    rw [← hpx]
    exact finite_fibre_pointsMap_of_isQuasiCompact_fieldMorphism B S hS p hqc inferInstance φ hφ
  refine ⟨hfinU, ?_⟩
  have hetale : IsEtale B S hS φ := (isEtale_iff_presheaf_of_yoneda B S hS φ).2 hφ
  have hcover : pointsMap B S hS (pullback φ φ) (pullback.fst φ φ ≫ φ) ⁻¹' {x} ⊆
      ⋃ c ∈ pointsMap B S hS (yoneda.obj U) φ ⁻¹' {x},
        ⋃ d ∈ pointsMap B S hS (yoneda.obj U) φ ⁻¹' {x},
          {r : points B S hS (pullback φ φ) |
            pointsMap B S hS (pullback φ φ) (pullback.fst φ φ) r = c ∧
            pointsMap B S hS (pullback φ φ) (pullback.snd φ φ) r = d} := by
    intro r hr
    have hc : pointsMap B S hS (yoneda.obj U) φ
        (pointsMap B S hS (pullback φ φ) (pullback.fst φ φ) r) = x := by
      rw [← pointsMap_comp_apply]
      exact hr
    have hd : pointsMap B S hS (yoneda.obj U) φ
        (pointsMap B S hS (pullback φ φ) (pullback.snd φ φ) r) = x := by
      rw [← pointsMap_comp_apply, ← pullback.condition]
      exact hr
    exact Set.mem_biUnion hc (Set.mem_biUnion hd ⟨rfl, rfl⟩)
  exact Set.Finite.subset (hfinU.biUnion fun c hc ↦ hfinU.biUnion fun d hd ↦
    hevery U φ c d hetale hc hd) hcover

/-! ### The equivalence -/

/-- For a point of an algebraic space over `S`, finiteness of the fibres of every affine étale
chart and of its self-intersection above the point is equivalent to the point being in the class
of a quasi-compact monomorphism from the spectrum of a field. -/
@[stacks 03JV "conditions (1) and (4)"]
theorem hasFiniteChartAndRelationFibersAt_iff_hasQuasiCompactMonomorphicFieldRepresentative
    (hX : IsAlgebraicSpace B S hS X) (x : points B S hS X) :
    HasFiniteChartAndRelationFibersAt B S hS X x ↔
      HasQuasiCompactMonomorphicFieldRepresentative B S hS X x :=
  ⟨hasQuasiCompactMonomorphicFieldRepresentative_of_hasFiniteChartAndRelationFibersAt
      B S hS X hX x,
    hasFiniteChartAndRelationFibersAt_of_hasQuasiCompactMonomorphicFieldRepresentative
      B S hS X hX x⟩

/-- An algebraic space over `S` is decent exactly when every étale chart of it by an affine
scheme and the self-intersection of that chart have finite fibres above every point. -/
theorem isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint
    (hX : IsAlgebraicSpace B S hS X) :
    IsDecentSpace B S hS X ↔ HasFiniteChartAndRelationFibersAtEveryPoint B S hS X :=
  forall_congr' fun x ↦
    (hasFiniteChartAndRelationFibersAt_iff_hasQuasiCompactMonomorphicFieldRepresentative
      B S hS X hX x).symm

end AlgebraicGeometry.Space

end
