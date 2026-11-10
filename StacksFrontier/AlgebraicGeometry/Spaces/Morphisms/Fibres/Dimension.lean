module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart

/-!
# The dimension of a fibre of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `y` be a point of
`Y`. The *fibre dimension* of `f` at `y` is the least bound `d` for which `f` has relative
dimension `≤ d` at every point of `X` above `y`; it is `⊥` when there is no such point, that
is when `y` is not in the image of `|f|`. This is the quantity (1) of **Stacks 0D4M**, and the
source lemma identifies it with the dimension of the algebraic space `X_k` cut out by any
field-valued representative of `y`.

## Main definitions

* `AlgebraicGeometry.Space.fiberDimension` is the fibre dimension of a morphism of presheaves
  at a point of its target.

## Main results

* `AlgebraicGeometry.Space.relativeDimensionAt_fieldTarget_iff_dimensionAtPoint`: when the
  target is the presheaf represented by the spectrum of a field, having relative dimension `d`
  at a point is having absolute dimension `d` at that point. This is the step that turns a
  relative-dimension bound over a field-valued point into a statement about the dimension of
  the fibre.
* `AlgebraicGeometry.Space.dimensionAtPoint_ne_bot`: an algebraic space has dimension `≠ ⊥` at
  each of its points, so only an empty fibre produces the value `⊥`.
* `AlgebraicGeometry.Space.dimension_eq_of_iso`: isomorphic algebraic spaces have the same
  dimension.

## Implementation notes

Values lie in `WithBot ℕ∞`: the source's `-∞` is `⊥`, and the bound is formed as an infimum, so
an empty fibre receives `⊥` from the empty infimum. A field-valued point of the target
determines a morphism from its representable field spectrum by Yoneda, and the fibre is the
presheaf pullback along that morphism.

`AlgebraicGeometry.Space.fiberDimension` carries no algebraicity hypothesis: the infimum is
meaningful for an arbitrary presheaf, and the hypotheses enter only in the results about it.

`AlgebraicGeometry.fiberDimensionAt_comp_openImmersion` is a scheme-level statement about the
local dimension of a fibre; it is stated in the `AlgebraicGeometry` namespace rather than
`AlgebraicGeometry.Space` because no algebraic space occurs in it.

## References

* [Stacks Project, Tag 0D4M](https://stacks.math.columbia.edu/tag/0D4M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The fibre of a morphism to the spectrum of a field is the whole source, so the local
dimension of a fibre coincides with the local dimension of the source. -/
theorem topologicalKrullDimAt_fiber_eq_of_field {k : Type u} [Field k]
    {U : Scheme.{u}} (f : U ⟶ Spec (.of k)) (x : U) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = topologicalKrullDimAt U x := by
  let s : Set U := f ⁻¹' {f x}
  have hs : s = Set.univ := by
    ext z
    simp only [Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have hxs : x ∈ s := rfl
  let e₁ := f.fiberHomeo (f x)
  let e₂ : ↥s ≃ₜ U := (Homeomorph.setCongr hs).trans (Homeomorph.Set.univ U)
  let e : f.fiber (f x) ≃ₜ U := e₁.trans e₂
  have hfi : e₁ (f.asFiber x) = ⟨x, hxs⟩ := Subtype.ext (Scheme.Hom.fiberι_asFiber f x)
  have hp : e (f.asFiber x) = x := by
    dsimp [e, e₂]
    rw [hfi]
    change ((Homeomorph.setCongr hs) (⟨x, hxs⟩ : s) : Set.univ) = x
    rfl
  exact (topologicalKrullDimAt_eq_of_homeomorph e (f.asFiber x)).trans
    (congrArg (topologicalKrullDimAt U) hp)

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of presheaves on the big fppf site of `S` is étale: composing with it is an
isomorphism of arrows, and the étale property of a relatively representable morphism is
invariant under isomorphism of arrows. -/
theorem isEtale_of_iso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    IsEtale B S hS e.hom := by
  intro U φ hφ
  have : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  exact ((MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))).arrow_mk_iso_iff
      (Arrow.isoMk (Iso.refl (yoneda.obj U)) e
        (Category.id_comp (φ ≫ e.hom)))).mp hφ

/-- Isomorphic algebraic spaces have the same dimension: an isomorphism is étale in both
directions, and an étale morphism preserves the dimension at a point. -/
theorem dimension_eq_of_iso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (e : F ≅ G) :
    dimension B S hS F hF = dimension B S hS G hG := by
  classical
  unfold dimension
  refine le_antisymm (iSup_le fun x ↦ ?_) (iSup_le fun y ↦ ?_)
  · rw [dimensionAtPoint_eq_of_isEtale B S hS hF hG e.hom (isEtale_of_iso B S hS e) x]
    exact le_iSup_of_le (pointsMap B S hS F e.hom x) le_rfl
  · rw [dimensionAtPoint_eq_of_isEtale B S hS hG hF e.inv (isEtale_of_iso B S hS e.symm) y]
    exact le_iSup_of_le (pointsMap B S hS G e.inv y) le_rfl

/-- The field-valued point of the presheaf represented by the site object a field-valued point
determines: the same field and structure morphism, with the identity as its section. -/
noncomputable def fieldPointOfYoneda {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : FieldValuedPoint B S hS F) :
    FieldValuedPoint B S hS (yoneda.obj (p.siteObject B S hS F)) where
  carrier := p.carrier
  field := p.field
  contained := p.contained
  toBase := p.toBase
  value := 𝟙 (p.siteObject B S hS F)

/-- The presheaf represented by the site object of a field-valued point has exactly one point:
every field-valued point of it is dominated by itself over the canonical one. -/
theorem points_yoneda_eq_fieldPoint {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : FieldValuedPoint B S hS F)
    (q : FieldValuedPoint B S hS (yoneda.obj (p.siteObject B S hS F))) :
    q.class B S hS (yoneda.obj (p.siteObject B S hS F)) =
      (fieldPointOfYoneda B S hS p).class B S hS
        (yoneda.obj (p.siteObject B S hS F)) := by
  apply FieldValuedPoint.class_eq_class_of_hasCommonExtension
  refine ⟨q, FieldValuedPoint.dominates_refl B S hS _ q, q.value, ?_⟩
  change (yoneda.obj (p.siteObject B S hS F)).map
    q.value.op (𝟙 (p.siteObject B S hS F)) = q.value
  simp

/-- **Stacks 0D4M.** When the target of a morphism of algebraic spaces is the presheaf
represented by the spectrum of a field, relative dimension `d` at a point is absolute
dimension `d` at that point: over a field the fibre of a chart is the chart itself. -/
theorem relativeDimensionAt_fieldTarget_iff_dimensionAtPoint
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS G)
    (f : F ⟶ yoneda.obj (p.siteObject B S hS G))
    (x : points B S hS F) (d : ℕ∞) :
    HasRelativeDimensionAt d B S hS f x ↔
      dimensionAtPoint B S hS F hF x = (d : WithBot ℕ∞) := by
  let T := p.siteObject B S hS G
  have hiff := holdsOnEveryEtaleChartAtPoint_iff_some B S hS
    (@AlgebraicGeometry.HasFiberDimensionAt.{u} d)
    (AlgebraicGeometry.fiberDimensionAt_isEtaleLocalOnSourceAndTarget d) hF
    (isAlgebraicSpace_yoneda B S hS T) f x
  obtain ⟨U, a, ha, q, hq⟩ := exists_etale_chart_at_point B S hS F hF x
  let c : EtaleChartAtPoint B S hS f x :=
    { U := U
      V := T
      a := a
      b := 𝟙 (yoneda.obj T)
      h := yoneda.preimage (a ≫ f)
      a_etale := ha
      b_etale := presheaf_etale_id B S hS T
      comm := by simp
      representative := q
      point := IsLocalRing.closedPoint q.carrier
      maps_to := hq }
  have hdimOfChart :
      AlgebraicGeometry.HasFiberDimensionAt d
        (MorphismOfGerms.ofSchemeHom ((BigFppfOver.toScheme B S hS).map c.h)
          (c.sourcePoint B S hS)) ↔
      dimensionAtPoint B S hS F hF x = (d : WithBot ℕ∞) := by
    rw [AlgebraicGeometry.hasFiberDimensionAt_ofSchemeHom_iff,
      AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_field]
    exact (dimensionAtPoint_eq_of_etale_chart B S hS F hF x c.U c.a c.a_etale
      c.representative c.maps_to).symm ▸ Iff.rfl
  exact ⟨fun hall ↦ hdimOfChart.mp (hall c), fun hdim ↦ hiff.mpr ⟨c, hdimOfChart.mpr hdim⟩⟩

/-- An algebraic space has dimension `≠ ⊥` at every one of its points: the dimension there is
the local dimension of an étale chart at a point above it, which is never `⊥`. -/
theorem dimensionAtPoint_ne_bot (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) :
    dimensionAtPoint B S hS F hF x ≠ ⊥ := by
  obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point B S hS F hF x
  rw [dimensionAtPoint_eq_of_etale_chart B S hS F hF x U a ha p hp]
  exact topologicalKrullDimAt_ne_bot
    (X := ↥((BigFppfOver.toScheme B S hS).obj U)) (schemePoint B S hS U p)

/-- **Stacks 0D4M, quantity (1).** The dimension of the fibre of a morphism of presheaves over
a point `y` of the target: the least `d` for which the morphism has relative dimension `≤ d` at
every point above `y`.

It is `⊥` exactly when no point lies above `y`, the infimum then being over all of
`WithBot ℕ∞`. -/
noncomputable def fiberDimension {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (y : points B S hS Y) : WithBot ℕ∞ :=
  sInf {d : WithBot ℕ∞ | ∀ x : points B S hS X, pointsMap B S hS X f x = y →
    ∃ e : ℕ∞, HasRelativeDimensionAt e B S hS f x ∧ (e : WithBot ℕ∞) ≤ d}

end Space

end AlgebraicGeometry

end
