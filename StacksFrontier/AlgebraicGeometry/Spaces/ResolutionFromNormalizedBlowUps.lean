module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAtClosedPointIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.BirationalDominant
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionLocalRings
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFiniteQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqsIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionByNormalizedBlowUps
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionOfSingularities
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# A resolution by normalized blowups is a resolution of singularities

Let `S` be a scheme and let `Y` be a two dimensional integral Noetherian algebraic space over
`S`. If `Y` has a resolution of singularities by normalized blowups in the sense of Stacks 0BHX,
then the top member `Yₙ ⟶ Y` of such a sequence is a resolution of singularities of `Y` in the
sense of Stacks 0BHW.

This is the implication (3) `⇒` (2) of Stacks 0BHY.

## Main results

* `AlgebraicGeometry.Space.NormalizationData.ofIso`: normalization data transported along an
  isomorphism of the normalization.
* `AlgebraicGeometry.Space.NormalizedBlowUpChain.isIntegralSpace_and_isBirational`: every member
  of a sequence of normalized blowups over a two dimensional integral space is integral, and its
  morphism to the base is proper and birational.
* `AlgebraicGeometry.Space.exists_resolutionOfSingularities_of_hasResolutionByNormalizedBlowUps`:
  the implication (3) `⇒` (2) of Stacks 0BHY.

## Implementation notes

The source calls the implication immediate. Its content is that every member `Yᵢ` of the
sequence is integral and `Yᵢ ⟶ Y` birational; properness is part of the definition. This is
proved along the sequence:

* `Y₀ ⟶ Y` is the normalization of the integral space `Y`, which is integral and birational by
  `AlgebraicGeometry.Space.NormalizationData.isIntegralSpace` and
  `AlgebraicGeometry.Space.NormalizationData.isBirational_hom`.
* For a step `Yᵢ ⟶ Yᵢ₋₁`, the normalization of the blowup `b : X' ⟶ Yᵢ₋₁` at a closed point
  `x`: the space `Yᵢ` is decent because it is proper, hence quasi-separated, over the decent
  space `Y` (Stacks 0ABY); then so is `X'`, the target of the integral, hence quasi-compact, and
  surjective normalization morphism (Stacks 03L2). The point `x` is not the only point of
  `|Yᵢ₋₁|`: otherwise it would be the generic point, and since `Yᵢ₋₁ ⟶ Y` is proper and
  dominant, hence surjective, every point of `|Y|` would be the generic point of `Y`, whose local
  ring has dimension zero (Stacks 0ABV), contradicting `dim(Y) = 2` (Stacks 0BAN). So
  `AlgebraicGeometry.Space.isIntegralSpace_and_isBirational_of_isBlowupAlong_closedPoint`
  applies to `b`, and the normalization of the integral space `X'` is integral and birational
  over it.

Birationality composes by `AlgebraicGeometry.Space.IsBirational.comp`.

The resolution is stated in the shape consumed by
`AlgebraicGeometry.Space.exists_regular_alteration_of_exists_resolutionOfSingularities`, the
implication (2) `⇒` (1).

## References

* [Stacks Project, Tag 0BHY](https://stacks.math.columbia.edu/tag/0BHY)
* [Stacks Project, Tag 0BHX](https://stacks.math.columbia.edu/tag/0BHX)
* [Stacks Project, Tag 0BHW](https://stacks.math.columbia.edu/tag/0BHW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace NormalizationData

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Normalization data transported along an isomorphism `Y ≅ F^ν`: the space is `Y` and the
normalization morphism is the isomorphism followed by `F^ν ⟶ F`. -/
def ofIso (D : NormalizationData B S hS F) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (e : Y ≅ D.space) : NormalizationData B S hS F where
  space := Y
  isAlgebraicSpace := hY
  hom := e.hom ≫ D.hom
  chart U f hf hfe := by
    obtain ⟨hU, Uν, p, g, e', hp, hpb⟩ := D.chart U f hf hfe
    refine ⟨hU, Uν, p, g ≫ e.inv, e', hp, ?_⟩
    refine hpb.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp

/-- The normalization morphism of `D.ofIso hY e` is `e.hom` followed by the normalization
morphism of `D`. -/
@[simp]
theorem ofIso_hom (D : NormalizationData B S hS F) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (e : Y ≅ D.space) : (D.ofIso hY e).hom = e.hom ≫ D.hom :=
  rfl

end NormalizationData

/-- A two dimensional algebraic space has a point whose local ring has nonzero dimension
(Stacks 0BAN). -/
theorem exists_localRingDimension_ne_zero_of_dimension_eq_two
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYdim : dimension B S hS Y hY = 2) :
    ∃ y : points B S hS Y, localRingDimension B S hS y ≠ 0 := by
  by_contra h
  push Not at h
  rw [dimension_eq_iSup_localRingDimension] at hYdim
  have hle : (⨆ y : points B S hS Y, (localRingDimension B S hS y : WithBot ℕ∞)) ≤ 0 :=
    iSup_le fun y => by rw [h y]; rfl
  rw [hYdim] at hle
  exact absurd hle (by decide)

/-- **The members of a sequence of normalized blowups are integral and birational over the
base.** Let `Y` be a two dimensional integral algebraic space over `S` and let `f : X ⟶ Y` be the
composite of a sequence `X = Yₙ ⟶ … ⟶ Y₀ ⟶ Y` as in Stacks 0BHX. Then `f` is proper, `X` is
integral and `f` is birational. -/
theorem NormalizedBlowUpChain.isIntegralSpace_and_isBirational {Y : AlgebraicSpaces B S hS}
    (hYdim : dimension B S hS Y.obj Y.property = 2) (hYint : IsIntegralSpace B S hS Y.obj)
    {X : AlgebraicSpaces B S hS} {f : X ⟶ Y} (h : NormalizedBlowUpChain B S hS Y X f) :
    IsProper B S hS f.hom ∧ ∃ hXint : IsIntegralSpace B S hS X.obj,
      IsBirational B S hS X.property Y.property (hXint.isDecentSpace B S hS X.obj)
        (hYint.isDecentSpace B S hS Y.obj)
        (hXint.finite_irreducibleComponents B S hS X.obj)
        (hYint.finite_irreducibleComponents B S hS Y.obj) f.hom := by
  have hYdec : IsDecentSpace B S hS Y.obj := hYint.isDecentSpace B S hS Y.obj
  have hYfin := hYint.finite_irreducibleComponents B S hS Y.obj
  induction h with
  | normalization f hnorm hproper =>
    rename_i Y₀
    obtain ⟨D, e, hf⟩ := hnorm
    let D' := D.ofIso Y₀.property e
    have hD'hom : D'.hom = f.hom := (NormalizationData.ofIso_hom D Y₀.property e).trans hf.symm
    refine ⟨hproper, ?_⟩
    have hint : IsIntegralSpace B S hS D'.space := D'.isIntegralSpace Y.property hYint
    refine ⟨hint, ?_⟩
    have hbir := D'.isBirational_hom Y.property hYdec hYint.1 hYfin
    rw [hD'hom] at hbir
    exact hbir
  | normalizedBlowUp previous g x hx hg hproper ih =>
    rename_i Yprev Ynext fprev
    obtain ⟨hprevproper, hprevint, hprevbir⟩ := ih
    obtain ⟨X', b, hb, D, e, hgeq⟩ := hg
    obtain ⟨W, b', hb', e', he'⟩ := hb
    have hbA : IsBlowupAlong B S hS (closedPointSubspace B S hS x hx) b := by
      rw [← he']; exact IsBlowupAlong.of_iso_over hb' e'
    let D' := D.ofIso Ynext.property e
    have hgD : g.hom = D'.hom ≫ b.hom := hgeq.trans (Category.assoc _ _ _).symm
    refine ⟨hproper, ?_⟩
    -- Decency of `Yᵢ` and of the blowup.
    have hYnextdec : IsDecentSpace B S hS Ynext.obj :=
      isDecentSpace_source_of_isQuasiSeparated B S hS Ynext.property Y.property (g ≫ fprev).hom
        (isQuasiSeparated_of_isSeparated B S hS hproper.1) hYdec
    have hX'dec : IsDecentSpace B S hS X'.obj :=
      isDecentSpace_of_surjective_isQuasiCompact B S hS Ynext.property X'.property D'.hom
        (isQuasiCompact_of_isIntegralHom D'.hom Ynext.property X'.property
          (D'.isIntegralHom X'.property))
        (D'.isSurjective_hom X'.property) hYnextdec
    -- The centre is not the only point of `|Yᵢ₋₁|`.
    have hne : ∃ y : points B S hS Yprev.obj, y ≠ x := by
      by_contra hall
      push Not at hall
      have hprevdec := hprevint.isDecentSpace B S hS Yprev.obj
      have hsober := stacksSober_points_of_isDecentSpace B S hS Yprev.property hprevdec
      let : QuasiSober (points B S hS Yprev.obj) := (stacksSober_iff_t0_and_quasiSober.mp hsober).2
      let : T0Space (points B S hS Yprev.obj) := (stacksSober_iff_t0_and_quasiSober.mp hsober).1
      let : IrreducibleSpace (points B S hS Yprev.obj) := hprevint.2.2
      have hgen : x ∈ genericPoints (points B S hS Yprev.obj) := by
        rw [genericPoints_eq_singleton, hall (genericPoint _)]
        exact Set.mem_singleton x
      have hfx : pointsMap B S hS Yprev.obj fprev.hom x ∈ genericPoints (points B S hS Y.obj) :=
        hprevbir.1.mapsTo hgen
      have hclosed : IsClosedMap (pointsMap B S hS Yprev.obj fprev.hom) :=
        isClosedMap_pointsMap_of_pullback_fst_id B S hS fprev.hom
          (hprevproper.2.2 Y.obj Y.property (𝟙 Y.obj))
      have hdense : DenseRange (pointsMap B S hS Yprev.obj fprev.hom) :=
        isDominant_of_isBirational B S hS Yprev.property Y.property _ _ _ _ hprevbir
      have hsurj : Function.Surjective (pointsMap B S hS Yprev.obj fprev.hom) := by
        rw [← Set.range_eq_univ, ← (hclosed.isClosed_range).closure_eq]
        exact hdense.closure_range
      obtain ⟨y, hy⟩ := exists_localRingDimension_ne_zero_of_dimension_eq_two Y.property hYdim
      obtain ⟨p, rfl⟩ := hsurj y
      rw [hall p] at hy
      exact hy (localRingDimension_eq_zero_of_mem_genericPoints B S hS Y.property hYdec hfx)
    -- The blowup is integral and birational, and so is its normalization.
    obtain ⟨hX'int, hbbir⟩ :=
      isIntegralSpace_and_isBirational_of_isBlowupAlong_closedPoint hprevint hx hne hbA hX'dec
    have hint : IsIntegralSpace B S hS D'.space := D'.isIntegralSpace X'.property hX'int
    refine ⟨hint, ?_⟩
    have hD'bir := D'.isBirational_hom X'.property hX'dec hX'int.1
      (hX'int.finite_irreducibleComponents B S hS X'.obj)
    have hcomp := (hD'bir.comp hbbir).comp hprevbir
    have hgf : (g ≫ fprev).hom = (D'.hom ≫ b.hom) ≫ fprev.hom := by
      rw [← hgD]; rfl
    rw [hgf]
    exact hcomp

/-- **Stacks 0BHY, (3) `⇒` (2).** If a two dimensional integral Noetherian algebraic space `Y`
over `S` has a resolution of singularities by normalized blowups, then it has a resolution of
singularities: the top member `Yₙ ⟶ Y` of the sequence is a modification with regular source.

Decency of `Y`, which Stacks 0BHW asks for in order to speak of birationality, is the decency of
an integral space (Stacks 0AD4); the conclusion is stated in the shape consumed by
`AlgebraicGeometry.Space.exists_regular_alteration_of_exists_resolutionOfSingularities`. -/
theorem exists_resolutionOfSingularities_of_hasResolutionByNormalizedBlowUps
    (hZ : B.Contains (⊤_ Scheme.{u})) (Y : AlgebraicSpaces B S hS)
    (hYdim : dimension B S hS Y.obj Y.property = 2) (hYnoeth : IsNoetherian B S hS hZ Y.obj)
    (hYint : IsIntegralSpace B S hS Y.obj)
    (h : HasResolutionByNormalizedBlowUps B S hS hZ Y hYdim hYnoeth hYint) :
    ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
      (hdecentX : IsDecentSpace B S hS X) (f : X ⟶ Y.obj),
      IsResolutionOfSingularities B S hS hZ hX Y.property hYnoeth hYint hdecentX
        (hYint.isDecentSpace B S hS Y.obj) f := by
  obtain ⟨X, f, hchain, hreg⟩ := h
  obtain ⟨hproper, hXint, hbir⟩ := hchain.isIntegralSpace_and_isBirational hYdim hYint
  exact ⟨X.obj, X.property, hXint.isDecentSpace B S hS X.obj, f.hom, ⟨hXint, hbir, hproper⟩,
    hreg⟩

end AlgebraicGeometry.Space

end
