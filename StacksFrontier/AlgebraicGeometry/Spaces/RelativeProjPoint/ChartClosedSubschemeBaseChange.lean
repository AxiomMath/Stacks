module

public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.TwistKerRestrict
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Algebra
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeRepresentation

/-!
# The chart closed subschemes of a closed subspace of a relative Proj, at two scheme points

In Situation 0849 let `i : Z ⟶ Proj_X(𝒜)` be a closed immersion of algebraic spaces. Over a scheme
point `f : T ⟶ X` it becomes the closed subscheme
`AlgebraicGeometry.Space.RelativeProjSituation.chartClosedSubscheme` of `Proj_T(f^*𝒜)`, and
Tag 0801 attaches to it a graded ideal of `f^*𝒜`. This file compares these data at `f` and at
`f ∘ k` for a morphism `k : T' ⟶ T` of test objects: the two closed subschemes form a cartesian
square over the comparison morphism of Stacks 084B (3), and the graded ideals are related by the
restriction along `k` as in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/TwistKerRestrict.lean`.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.chartClosedSubschemeComparison`: the morphism
  `Z ×_X T' ⟶ Z ×_X T` of the base changes.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointTwistKerRestrict`: the restriction
  `a ↦ Φ⁻¹(k^*a)` of homogeneous local sections, `Φ` the identification of the restriction datum.

## Main results

* `…isPullback_chartClosedSubschemeComparison`: the cartesian square.
* `…mem_pointTwistKer_restrict`: the restriction carries the ideal at `f` into the ideal at
  `f ∘ k`.
* `…pointTwistKer_le_span_restrict`: for `k` flat, over affine opens the ideal at `f ∘ k` is
  spanned by the restrictions of the ideal at `f`.
* `…etale_toScheme_map_of_isEtale`: `k` is étale when `f` and `f ∘ k` are.

## References

* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

universe u

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable {s : RelativeProjSituation.{u, u}} {Z : AlgebraicSpaces s.site s.base s.containsBase}
  (i : Z ⟶ s.Proj) (hi : IsClosedImmersion s.site s.base s.containsBase i.hom)
  {T T' : BigFppfOver s.site s.base s.containsBase} (k : T' ⟶ T)
  (f : yoneda.obj T ⟶ s.space.1)

/-- **The comparison of the base changes of a closed subspace to two scheme points**: the
morphism `Z ×_X T' ⟶ Z ×_X T` over the comparison morphism of Stacks 084B (3). -/
def chartClosedSubschemeComparison :
    (closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.pullback
        (s.relativeProjPoints.fibreToSpace T' (yoneda.map k ≫ f)) ⟶
      (closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.pullback
        (s.relativeProjPoints.fibreToSpace T f) :=
  (closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.lift
    ((closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.fst _)
    ((closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.snd _ ≫
      s.quadrupleRestriction.projComparison s.shrink.contains_relativeProj_pointAlgebra f k)
    (((closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.w _).trans
      ((congrArg (fun t => yoneda.map ((closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.snd
          (s.relativeProjPoints.fibreToSpace T' (yoneda.map k ≫ f))) ≫ t)
        (s.isPullback_projComparison f k).2.1.symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ s.relativeProjPoints.fibreToSpace T f)
        (yoneda.map_comp _ _).symm))))

/-- The chart closed subscheme is the base change of the closed subspace, the identification of
the fibre with the relative Proj being the identity. -/
theorem chartClosedSubscheme_eq :
    chartClosedSubscheme i hi T f = (BigFppfOver.toScheme s.site s.base s.containsBase).map
      ((closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.snd
        (s.relativeProjPoints.fibreToSpace T f)) :=
  Category.comp_id _

/-- **The chart closed subschemes at `f` and at `f ∘ k` form a cartesian square over the
comparison morphism of Stacks 084B (3).** The base changes of `Z` along the two fibres are
represented pullbacks, and the second fibre maps to the first, so the square is a pasting of
cartesian squares of presheaves, read on schemes. -/
theorem isPullback_chartClosedSubschemeComparison :
    IsPullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map
        (chartClosedSubschemeComparison i hi k f))
      (chartClosedSubscheme i hi T' (yoneda.map k ≫ f)) (chartClosedSubscheme i hi T f)
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map
        (s.quadrupleRestriction.projComparison s.shrink.contains_relativeProj_pointAlgebra f
          k)) := by
  rw [chartClosedSubscheme_eq, chartClosedSubscheme_eq]
  refine AlgebraicGeometry.Stack.ChartBaseChange.isPullback_toScheme_of_isPullback_yoneda ?_
  have e1 : yoneda.map (chartClosedSubschemeComparison i hi k f) ≫
      (closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.fst
        (s.relativeProjPoints.fibreToSpace T f) =
      (closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.fst
        (s.relativeProjPoints.fibreToSpace T' (yoneda.map k ≫ f)) :=
    (closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.lift_fst _ _ _
  have e2 := (s.isPullback_projComparison f k).2.1
  refine IsPullback.of_right (h₁₂ := (closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.fst
      (s.relativeProjPoints.fibreToSpace T f))
    (h₂₂ := s.relativeProjPoints.fibreToSpace T f) ?_ ?_
    ((closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.isPullback _)
  · rw [e1]
    exact e2 ▸ (closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.isPullback _
  · exact (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map
      ((closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.lift_snd _ _ _)).trans
      (yoneda.map_comp _ _))

/-! ### The graded ideal of Tag 0801 at two scheme points -/

/-- **The restriction of a homogeneous local section along a morphism of test objects**: for a
scheme point `f` at `T`, `k : T' ⟶ T` and opens `W₁ ≤ k⁻¹W`, a section `a` of `(f^*𝒜)_n` over `W`
goes to `Φ⁻¹(k^*a)`, a section of `((f ∘ k)^*𝒜)_n` over `W₁`, where `Φ` is the identification
`(f ∘ k)^*𝒜 ≅ k^*(f^*𝒜)` of the restriction datum. -/
def pointTwistKerRestrict (n : ℤ)
    {W : ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj T').Opens}
    (hW : W₁ ≤ (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k ⁻¹ᵁ W)
    (a : Γ((s.shrink.pointAlgebra T f).piece n, W)) :
    Γ((s.shrink.pointAlgebra T' (yoneda.map k ≫ f)).piece n, W₁) :=
  twistKerRestrict (s.shrink.pointAlgebra T f)
    ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
    (A₁ := s.shrink.pointAlgebra T' (yoneda.map k ≫ f))
    (s.quadrupleRestriction.restrict k f (yoneda.map k ≫ f) rfl)
    (s.quadrupleRestriction.isIso_restrict_app k f _ rfl) n hW a

variable
  {W : ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj T).Opens}
  {W₁ : ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj T').Opens}
  (hW : W₁ ≤ (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k ⁻¹ᵁ W)

/-- `pointTwistKerRestrict` is `twistKerRestrict` for the restriction datum, on the nose. -/
theorem pointTwistKerRestrict_eq_twistKerRestrict (n : ℤ)
    (a : Γ((s.shrink.pointAlgebra T f).piece n, W)) :
    pointTwistKerRestrict k f n hW a =
      twistKerRestrict (s.shrink.pointAlgebra T f)
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
        (A₁ := s.shrink.pointAlgebra T' (yoneda.map k ≫ f))
        (s.quadrupleRestriction.restrict k f (yoneda.map k ≫ f) rfl)
        (s.quadrupleRestriction.isIso_restrict_app k f _ rfl) n hW a := rfl

/-- `pointTwistKerRestrict` is the inverse of the restriction datum applied to the pulled-back
section, on the nose. -/
theorem pointTwistKerRestrict_eq (n : ℤ) (a : Γ((s.shrink.pointAlgebra T f).piece n, W)) :
    pointTwistKerRestrict k f n hW a =
      (@inv _ _ _ _ ((s.quadrupleRestriction.restrict k f (yoneda.map k ≫ f) rfl).app n)
        (s.quadrupleRestriction.isIso_restrict_app k f (yoneda.map k ≫ f) rfl n)).val.app (op W₁)
        (Scheme.Modules.pullbackSection
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
          ((s.shrink.pointAlgebra T f).piece n) W W₁ hW a) := rfl

/-- `pointTwistKerRestrict` is additive. -/
theorem pointTwistKerRestrict_add (n : ℤ) (a b : Γ((s.shrink.pointAlgebra T f).piece n, W)) :
    pointTwistKerRestrict k f n hW (a + b) =
      pointTwistKerRestrict k f n hW a + pointTwistKerRestrict k f n hW b :=
  twistKerRestrict_add _ _ _ _ n hW a b

/-- `pointTwistKerRestrict` is semilinear along `k.appLE W W₁`. -/
theorem pointTwistKerRestrict_smul (n : ℤ)
    (r : Γ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj T, W))
    (a : Γ((s.shrink.pointAlgebra T f).piece n, W)) :
    pointTwistKerRestrict k f n hW (r • a) =
      (Scheme.Hom.appLE
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
        W W₁ hW).hom r •
        pointTwistKerRestrict k f n hW a :=
  twistKerRestrict_smul _ _ _ _ n hW r a

variable (hπ : IsQuasiCompact s.site s.base s.containsBase s.π.hom)

/-- The quasi-compactness and closed immersion instances needed at the two scheme points. -/
private theorem quasiCompact_isClosedImmersion_chartClosedSubscheme
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.π.hom) :
    QuasiCompact (relativeProj (s.shrink.pointAlgebra T f)).toBase ∧
    QuasiCompact (relativeProj (s.shrink.pointAlgebra T' (yoneda.map k ≫ f))).toBase ∧
    @AlgebraicGeometry.IsClosedImmersion _ (relativeProj (s.shrink.pointAlgebra T f)).scheme
      (chartClosedSubscheme i hi T f) ∧
    @AlgebraicGeometry.IsClosedImmersion _
      (relativeProj (s.shrink.pointAlgebra T' (yoneda.map k ≫ f))).scheme
      (chartClosedSubscheme i hi T' (yoneda.map k ≫ f)) :=
  ⟨quasiCompact_relativeProj_toBase hπ T f,
    quasiCompact_relativeProj_toBase hπ T' (yoneda.map k ≫ f),
    isClosedImmersion_chartClosedSubscheme i hi T f,
    isClosedImmersion_chartClosedSubscheme i hi T' (yoneda.map k ≫ f)⟩

/-- **The restriction carries the graded ideal of Tag 0801 of `Z ×_X T` into that of
`Z ×_X T'`.** -/
theorem mem_pointTwistKer_restrict (n : ℤ) (a : Γ((s.shrink.pointAlgebra T f).piece n, W))
    (ha : haveI := quasiCompact_relativeProj_toBase hπ T f
      a ∈ ((twistKerGradedIdeal (s.relativeProjPoints.algebra T f)
          (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
          (chartClosedSubscheme i hi T f)).piece n).toSubmodule.obj (op W)) :
    haveI := quasiCompact_relativeProj_toBase hπ T' (yoneda.map k ≫ f)
    pointTwistKerRestrict k f n hW a ∈
      ((twistKerGradedIdeal (s.relativeProjPoints.algebra T' (yoneda.map k ≫ f))
          (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
          (chartClosedSubscheme i hi T' (yoneda.map k ≫ f))).piece n).toSubmodule.obj (op W₁) := by
  obtain ⟨_, _, _, _⟩ := quasiCompact_isClosedImmersion_chartClosedSubscheme i hi k f hπ
  exact mem_twistKer_restrict (s.shrink.pointAlgebra T f)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map k)
    (A₁ := s.shrink.pointAlgebra T' (yoneda.map k ≫ f))
    (s.quadrupleRestriction.restrict k f (yoneda.map k ≫ f) rfl)
    (s.quadrupleRestriction.isIso_restrict_app k f _ rfl)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map
      (s.quadrupleRestriction.projComparison s.shrink.contains_relativeProj_pointAlgebra f k))
    (s.isPullback_projComparison f k).2.2
    (chartClosedSubscheme i hi T f) (chartClosedSubscheme i hi T' (yoneda.map k ≫ f))
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map
      (chartClosedSubschemeComparison i hi k f))
    (isPullback_chartClosedSubschemeComparison i hi k f).w n hW a ha

/-- **Along a flat morphism of test objects, over affine opens, the graded ideal of Tag 0801 of
`Z ×_X T'` is spanned by the restrictions of the graded ideal of `Z ×_X T`.** -/
theorem pointTwistKer_le_span_restrict
    [Flat ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)]
    (n : ℤ) (hWa : IsAffineOpen W) (hW₁a : IsAffineOpen W₁) :
    haveI := quasiCompact_relativeProj_toBase hπ T f
    haveI := quasiCompact_relativeProj_toBase hπ T' (yoneda.map k ≫ f)
    ((twistKerGradedIdeal (s.relativeProjPoints.algebra T' (yoneda.map k ≫ f))
          (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
          (chartClosedSubscheme i hi T' (yoneda.map k ≫ f))).piece n).toSubmodule.obj (op W₁) ≤
      Submodule.span
        Γ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj T', W₁)
        (pointTwistKerRestrict k f n hW ''
          SetLike.coe (((twistKerGradedIdeal (s.relativeProjPoints.algebra T f)
          (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
          (chartClosedSubscheme i hi T f)).piece n).toSubmodule.obj (op W))) := by
  obtain ⟨_, _, _, _⟩ := quasiCompact_isClosedImmersion_chartClosedSubscheme i hi k f hπ
  exact twistKer_le_span_restrict (s.shrink.pointAlgebra T f)
    ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
    (A₁ := s.shrink.pointAlgebra T' (yoneda.map k ≫ f))
    (s.quadrupleRestriction.restrict k f (yoneda.map k ≫ f) rfl)
    (s.quadrupleRestriction.isIso_restrict_app k f _ rfl)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map
      (s.quadrupleRestriction.projComparison s.shrink.contains_relativeProj_pointAlgebra f k))
    (s.isPullback_projComparison f k).2.2
    (chartClosedSubscheme i hi T f) (chartClosedSubscheme i hi T' (yoneda.map k ≫ f))
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map
      (chartClosedSubschemeComparison i hi k f))
    (isPullback_chartClosedSubschemeComparison i hi k f) n hW hWa hW₁a

omit i hi in
/-- A morphism of test objects between two étale scheme points of the base, compatible
with the points, is étale: it is a morphism between algebraic spaces étale over the base (Stacks
03FV), and for a represented morphism that is étaleness of the morphism of schemes. -/
theorem etale_toScheme_map_of_isEtale
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom)
    (hf' : IsEtale s.site s.base s.containsBase
      (pointHom (X := s.space) (yoneda.map k ≫ f)).hom) :
    Etale ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k) :=
  etale_of_isEtale_yoneda_map _ _ _ (isEtale_of_isEtale_over _ _ _ (yonedaSpace _ _ _ T').2
    (yonedaSpace _ _ _ T).2 s.space.2 (yoneda.map k) (yoneda.map k ≫ f) f hf' hf rfl)

end AlgebraicGeometry.Space.RelativeProjSituation

end
