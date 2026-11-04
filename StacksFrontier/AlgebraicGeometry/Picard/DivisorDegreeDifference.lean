module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.RelativeDifference
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorDegreeSum

/-!
# The degree of a difference of divisors on a smooth relative curve

Let `f : X ⟶ S` be a morphism of schemes smooth of relative dimension one and let `D₁ ⊆ D₂` be
closed subschemes of `X` that are finite locally free over `S` of degrees `d₁` and `d₂`. Then
there is a closed subscheme `D` of `X`, finite locally free over `S` of degree `d₂ - d₁`, with
`D₂ = D₁ + D`.

Both `D₁` and `D₂` are relative effective Cartier divisors, so the ideal of `D₁` divides that of
`D₂` and the quotient cuts out an effective Cartier divisor `D`, which is again flat over `S`.
Hence `D` is locally quasi-finite, flat and locally of finite presentation over `S`; it is a
closed subscheme of `D₂` and so finite over `S`, hence finite locally free. Its degree is read on
the fibres, where additivity of the degree of a sum of divisors gives `d₁ + deg D = d₂`.

## Main results

* `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_sub_mul_eq_of_le`: the difference of two
  nested finite locally free divisors on a smooth relative curve is finite locally free of the
  difference of the degrees.

## References

* [Stacks Project, Tag 0B9F](https://stacks.math.columbia.edu/tag/0B9F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A finite locally free morphism is finite and flat. -/
private theorem isFinite_and_flat_of_isFiniteLocallyFree {X S : Scheme.{u}} (g : X ⟶ S)
    [Stacks.Morphisms.IsFiniteLocallyFree g] : IsFinite g ∧ Flat g :=
  let ⟨h₁, h₂, _⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).1
      inferInstance
  ⟨h₁, h₂⟩

/-- The degree of a divisor and of the divisor it is subtracted from add up to the degree of the
sum, checked at a single point of the base by passing to the fibre there. -/
private theorem finrank_add_eq_of_mul_eq
    {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
    (D₁ D₂ E : X.IdealSheafData) (d₁ d₂ : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D₁.subschemeι ≫ f) d₁]
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D₂.subschemeι ≫ f) d₂]
    [Stacks.Morphisms.IsFiniteLocallyFree (E.subschemeι ≫ f)]
    (hmul : D₂ = D₁ * E) (s : S) :
    d₁ + (E.subschemeι ≫ f).finrank s = d₂ := by
  obtain ⟨hfinE, hflatE⟩ := isFinite_and_flat_of_isFiniteLocallyFree (E.subschemeι ≫ f)
  have h₂fl : Stacks.Morphisms.IsFiniteLocallyFree (D₂.subschemeι ≫ f) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d₂
  obtain ⟨hfin₂, hflat₂⟩ := isFinite_and_flat_of_isFiniteLocallyFree (D₂.subschemeι ≫ f)
  let f' := f.fiberToSpecResidueField s
  let g' := f.fiberι s
  have sq : IsPullback g' f' f (S.fromSpecResidueField s) :=
    IsPullback.of_hasPullback f (S.fromSpecResidueField s)
  obtain ⟨a₁, hp₁⟩ := exists_isPullback_subschemeι_baseChange sq D₁
  obtain ⟨a₂, hp₂⟩ := exists_isPullback_subschemeι_baseChange sq D₂
  obtain ⟨aE, hpE⟩ := exists_isPullback_subschemeι_baseChange sq E
  have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have hsm : SmoothOfRelativeDimension 1 f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq
      (inferInstance : SmoothOfRelativeDimension 1 f)
  have h₁ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((D₁.comap g').subschemeι ≫ f') d₁ :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback hp₁
  have h₂ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((D₂.comap g').subschemeι ≫ f') d₂ :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback hp₂
  have hfinE' : IsFinite ((E.comap g').subschemeι ≫ f') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpE hfinE
  have hflatE' : Flat ((E.comap g').subschemeι ≫ f') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpE hflatE
  have hfin₂' : IsFinite ((D₂.comap g').subschemeι ≫ f') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hp₂ hfin₂
  have hflat₂' : Flat ((D₂.comap g').subschemeι ≫ f') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hp₂ hflat₂
  have hE' : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((E.comap g').subschemeι ≫ f')
      ((E.subschemeι ≫ f).finrank s) := by
    refine (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ _).2 fun y => ?_
    rw [Scheme.Hom.finrank_of_isPullback aE ((E.comap g').subschemeι ≫ f')
      (E.subschemeι ≫ f) (S.fromSpecResidueField s) hpE y,
      Scheme.fromSpecResidueField_apply]
  have hprod : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((D₂.comap g').subschemeι ≫ f') (d₁ + (E.subschemeι ≫ f).finrank s) := by
    have h := isFiniteLocallyFreeOfRank_mul f' (D₁.comap g') (E.comap g') d₁
      ((E.subschemeι ≫ f).finrank s)
    rwa [← AlgebraicGeometry.comap_mul, ← hmul] at h
  let y : Spec (S.residueField s) := IsLocalRing.closedPoint (S.residueField s)
  have hy₁ := (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq
    ((D₂.comap g').subschemeι ≫ f') (d₁ + (E.subschemeι ≫ f).finrank s)).1 hprod y
  have hy₂ := (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq
    ((D₂.comap g').subschemeι ≫ f') d₂).1 h₂ y
  omega

/-- **Stacks Project, Tag 0B9F.** Let `f : X ⟶ S` be smooth of relative dimension one and let
`D₁` and `D₂` be quasi-coherent sheaves of ideals on `X` whose closed subschemes are finite
locally free over `S` of degrees `d₁` and `d₂`. If the closed subscheme of `D₁` is contained in
that of `D₂`, that is `D₂ ≤ D₁`, then there is a quasi-coherent sheaf of ideals `D` with
`D₂ = D₁ * D`, the sum of the two divisors, whose closed subscheme is finite locally free over
`S` of degree `d₂ - d₁`. -/
@[stacks 0B9F]
theorem exists_isFiniteLocallyFreeOfRank_sub_mul_eq_of_le
    {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
    (D₁ D₂ : X.IdealSheafData) (d₁ d₂ : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D₁.subschemeι ≫ f) d₁]
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D₂.subschemeι ≫ f) d₂]
    (hle : D₂ ≤ D₁) :
    ∃ D : X.IdealSheafData, D₂ = D₁ * D ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ f) (d₂ - d₁) := by
  have h₁fl : Stacks.Morphisms.IsFiniteLocallyFree (D₁.subschemeι ≫ f) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d₁
  have h₂fl : Stacks.Morphisms.IsFiniteLocallyFree (D₂.subschemeι ≫ f) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d₂
  have hD₁ : Stacks.Divisors.IsRelativeEffectiveCartierDivisor f D₁ :=
    isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree f D₁
  have hD₂ : Stacks.Divisors.IsRelativeEffectiveCartierDivisor f D₂ :=
    isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree f D₂
  obtain ⟨E, hE, hmul⟩ :=
    exists_isEffectiveCartierDivisor_mul_eq_of_le D₁ D₂ hD₁.1 hD₂.1 hle
  have hrel : Stacks.Divisors.IsRelativeEffectiveCartierDivisor f E :=
    Stacks.Divisors.isRelativeEffectiveCartierDivisor_of_mul_eq f D₁ D₂ E hD₁ hD₂ hE hmul
  obtain ⟨-, -, hflat, hlfp⟩ :=
    (isRelativeEffectiveCartierDivisor_iff_locallyQuasiFinite_flat f E).1 hrel
  -- `E` is a closed subscheme of `D₂`, hence finite over `S`.
  have hsub : D₂ ≤ E.map (𝟙 X) := by
    intro U
    simp only [Scheme.IdealSheafData.map_id]
    rw [hmul]
    simp only [Scheme.IdealSheafData.ideal_mul]
    exact Ideal.mul_le_right
  let iE : E.subscheme ⟶ D₂.subscheme := E.subschemeMap D₂ (𝟙 X) hsub
  have hiE : iE ≫ D₂.subschemeι = E.subschemeι := by
    simp [iE]
  have : IsClosedImmersion (iE ≫ D₂.subschemeι) := by
    rw [hiE]; infer_instance
  have : IsClosedImmersion iE := IsClosedImmersion.of_comp_isClosedImmersion iE D₂.subschemeι
  have := (isFinite_and_flat_of_isFiniteLocallyFree (D₂.subschemeι ≫ f)).1
  have hfinE : IsFinite (E.subschemeι ≫ f) := by
    rw [← hiE, Category.assoc]
    infer_instance
  have hflE : Stacks.Morphisms.IsFiniteLocallyFree (E.subschemeι ≫ f) :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (E.subschemeι ≫ f)).2 ⟨hfinE, hflat, hlfp⟩
  have : Flat (E.subschemeι ≫ f) := hflat
  refine ⟨E, hmul, ?_⟩
  refine (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ (d₂ - d₁)).2
    fun s => ?_
  have h := finrank_add_eq_of_mul_eq f D₁ D₂ E d₁ d₂ hmul s
  omega

end AlgebraicGeometry

end
