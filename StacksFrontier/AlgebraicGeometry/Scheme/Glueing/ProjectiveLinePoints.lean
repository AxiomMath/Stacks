module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineDimension

/-!
# The points of the projective line

The projective line over a field is the first chart together with the point at infinity, and the
points of the first chart `Spec k[X]` are the generic point together with the closed points cut
out by the monic irreducible polynomials. The overlap of the two charts is the locus where the
coordinate is invertible, and its complement in a chart is the single point `(X)`. The projective
line over a field is infinite.

## Main definitions

* `AlgebraicGeometry.affineLineGenerator` — the monic irreducible polynomial cutting out a point
  of the affine line over a field.

## Main results

* `AlgebraicGeometry.mem_range_projectiveLinePuncturedChart_iff` and
  `AlgebraicGeometry.mem_range_projectiveLineOverlapYInclusion_iff` — the overlap of the two
  charts is the locus where the coordinate is invertible.
* `AlgebraicGeometry.eq_affineLineOrigin_of_X_mem` — the only point of the affine line over a
  field at which the coordinate vanishes is the origin.
* `AlgebraicGeometry.exists_monic_irreducible_asIdeal_eq_span` — a point of the affine line over a
  field other than the generic point is cut out by a unique monic irreducible polynomial.
* `AlgebraicGeometry.affineLineGenerator` and
  `AlgebraicGeometry.bijOn_affineLineGenerator` — the resulting bijection between the closed
  points of the affine line and the monic irreducible polynomials.
* `AlgebraicGeometry.mem_range_projectiveLineXChart_or_eq_infinity` — every point of the
  projective line is either in the first chart or the point at infinity.
* `AlgebraicGeometry.projectiveLineXChart_genericPoint_eq` — the first chart carries the generic
  point of the projective line.
* `AlgebraicGeometry.projectiveLineZero_ne_projectiveLineInfinity` — the points `0` and `∞` are
  distinct.
* `AlgebraicGeometry.infinite_setOf_monic_irreducible` — there are infinitely many monic
  irreducible polynomials over a field.
* `AlgebraicGeometry.infinite_affineLine` and `AlgebraicGeometry.infinite_projectiveLine` — the
  affine and the projective line over a field are infinite.

## References

* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The overlap of the two charts -/

section CommRing

variable (k : Type u) [CommRing k]

/-- The overlap `U₁₂` of the two charts of the projective line, seen in the first chart, is
`D(x)`, the locus where the coordinate is invertible. -/
@[stacks 01JE "projective_line_overlap"]
theorem mem_range_projectiveLinePuncturedChart_iff (y : Spec (.of (Polynomial k))) :
    y ∈ Set.range (projectiveLinePuncturedChart k).base ↔
      (Polynomial.X : Polynomial k) ∉ y.asIdeal := by
  have hr := PrimeSpectrum.localization_away_comap_range (R := Polynomial k)
    (LaurentPolynomial k) (Polynomial.X : Polynomial k)
  have hid : y ∈ Set.range (projectiveLinePuncturedChart k).base ↔
      y ∈ Set.range (PrimeSpectrum.comap
        (algebraMap (Polynomial k) (LaurentPolynomial k))) := Iff.rfl
  rw [hid, hr]
  exact PrimeSpectrum.mem_basicOpen _ _

/-- The overlap `U₂₁` of the two charts of the projective line, seen in the second chart, is
`D(y)`, the locus where the coordinate of that chart is invertible. -/
@[stacks 01JE "projective_line_overlap"]
theorem mem_range_projectiveLineOverlapYInclusion_iff (y : Spec (.of (Polynomial k))) :
    y ∈ Set.range (projectiveLineOverlapYInclusion k).base ↔
      (Polynomial.X : Polynomial k) ∉ y.asIdeal := by
  rw [← mem_range_projectiveLinePuncturedChart_iff k y,
    show projectiveLineOverlapYInclusion k =
      (projectiveLineInversionIso k).hom ≫ projectiveLinePuncturedChart k from
    (projectiveLineInversionIso_hom_comp_puncturedChart k).symm]
  rw [Scheme.Hom.comp_base, TopCat.coe_comp,
    ((projectiveLineInversionIso k).hom.surjective).range_comp]

end CommRing

/-! ### The points of a chart -/

variable {k : Type u} [Field k]

/-- An irreducible polynomial over a field is associated to a monic irreducible polynomial. -/
private theorem exists_monic_irreducible_associated {q : Polynomial k} (hq : Irreducible q) :
    ∃ p : Polynomial k, p.Monic ∧ Irreducible p ∧ Associated p q := by
  classical
  exact ⟨normalize q, Polynomial.monic_normalize hq.ne_zero,
    (normalize_associated q).symm.irreducible hq, normalize_associated q⟩

/-- The complement of the overlap in a chart is the single point `0` of that chart: the only
point of the affine line over a field at which the coordinate vanishes is the origin. -/
@[stacks 01JE "projective_line_overlap"]
theorem eq_affineLineOrigin_of_X_mem (y : Spec (.of (Polynomial k)))
    (hy : (Polynomial.X : Polynomial k) ∈ y.asIdeal) : y = affineLineOrigin k := by
  refine PrimeSpectrum.ext ?_
  have hmax : (Ideal.span {(Polynomial.X : Polynomial k)}).IsMaximal := by
    simpa [← Ideal.submodule_span_eq] using
      PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
  have hle : Ideal.span {(Polynomial.X : Polynomial k)} ≤ y.asIdeal := by
    rw [Ideal.span_le]
    simpa using hy
  exact (hmax.eq_of_le y.2.ne_top hle).symm

/-- Every point of the affine line over a field other than the generic point is cut out by a
monic irreducible polynomial. -/
theorem exists_monic_irreducible_asIdeal_eq_span (y : Spec (.of (Polynomial k)))
    (hy : y.asIdeal ≠ ⊥) :
    ∃ p : Polynomial k, p.Monic ∧ Irreducible p ∧ y.asIdeal = Ideal.span {p} := by
  obtain ⟨q, hq⟩ := (IsPrincipalIdealRing.principal y.asIdeal).principal
  rw [Ideal.submodule_span_eq] at hq
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, Ideal.span_singleton_eq_bot.2 rfl] at hq
    exact hy hq
  obtain ⟨p, hpm, hpi, hpq⟩ := exists_monic_irreducible_associated
    ((Ideal.span_singleton_prime hq0).mp (hq ▸ y.2)).irreducible
  exact ⟨p, hpm, hpi, hq ▸ (Ideal.span_singleton_eq_span_singleton.2 hpq.symm)⟩

open scoped Classical in
/-- The monic irreducible polynomial cutting out a point of the affine line over a field, and
zero at the generic point. -/
noncomputable def affineLineGenerator (y : Spec (.of (Polynomial k))) : Polynomial k :=
  if h : y.asIdeal = ⊥ then 0 else (exists_monic_irreducible_asIdeal_eq_span y h).choose

/-- Away from the generic point, `AlgebraicGeometry.affineLineGenerator` is a monic irreducible
generator of the prime ideal of the point. -/
theorem affineLineGenerator_spec (y : Spec (.of (Polynomial k))) (hy : y.asIdeal ≠ ⊥) :
    (affineLineGenerator y).Monic ∧ Irreducible (affineLineGenerator y) ∧
      y.asIdeal = Ideal.span {affineLineGenerator y} := by
  classical
  rw [affineLineGenerator, dite_eq_right hy]
  exact (exists_monic_irreducible_asIdeal_eq_span y hy).choose_spec

/-- `AlgebraicGeometry.affineLineGenerator` is a bijection from the points of the affine line over
a field other than the generic point onto the monic irreducible polynomials. -/
theorem bijOn_affineLineGenerator :
    Set.BijOn (affineLineGenerator (k := k)) {y | y.asIdeal ≠ ⊥}
      {p : Polynomial k | p.Monic ∧ Irreducible p} := by
  refine ⟨fun y hy ↦ ⟨(affineLineGenerator_spec y hy).1, (affineLineGenerator_spec y hy).2.1⟩,
    fun y hy z hz hyz ↦ ?_, fun p hp ↦ ?_⟩
  · refine PrimeSpectrum.ext ?_
    rw [(affineLineGenerator_spec y hy).2.2, (affineLineGenerator_spec z hz).2.2, hyz]
  · obtain ⟨hpm, hpi⟩ := hp
    refine ⟨⟨Ideal.span {p}, (Ideal.span_singleton_prime hpi.ne_zero).2 hpi.prime⟩, ?_, ?_⟩
    · exact fun h ↦ hpi.ne_zero (Ideal.span_singleton_eq_bot.1 h)
    · have hne : (⟨Ideal.span {p}, (Ideal.span_singleton_prime hpi.ne_zero).2 hpi.prime⟩ :
          Spec (.of (Polynomial k))).asIdeal ≠ ⊥ :=
        fun h ↦ hpi.ne_zero (Ideal.span_singleton_eq_bot.1 h)
      obtain ⟨hgm, -, hgspan⟩ := affineLineGenerator_spec _ hne
      have hspan : Ideal.span {p} =
          Ideal.span {affineLineGenerator
            (⟨Ideal.span {p}, (Ideal.span_singleton_prime hpi.ne_zero).2 hpi.prime⟩ :
              Spec (.of (Polynomial k)))} := hgspan
      refine Polynomial.eq_of_monic_of_associated hgm hpm (associated_of_dvd_dvd ?_ ?_)
      · exact Ideal.span_singleton_le_span_singleton.1 hspan.le
      · exact Ideal.span_singleton_le_span_singleton.1 hspan.ge

/-! ### The points of the projective line -/

/-- Every point of the projective line lies in the first chart or is the point at infinity. -/
@[ega "II 7.4.14" "partial"]
theorem mem_range_projectiveLineXChart_or_eq_infinity (x : projectiveLine k) :
    x ∈ Set.range (projectiveLineXChart k).base ∨ x = projectiveLineInfinity k := by
  obtain ⟨i, y, rfl⟩ := (projectiveLineGluingData k).ι_jointly_surjective x
  obtain ⟨i⟩ := i
  cases i
  · exact Or.inl ⟨y, rfl⟩
  · by_cases hy : (Polynomial.X : Polynomial k) ∈ y.asIdeal
    · right
      rw [eq_affineLineOrigin_of_X_mem y hy]
      rfl
    · obtain ⟨w, hw⟩ := (mem_range_projectiveLineOverlapYInclusion_iff k y).2 hy
      refine Or.inl ⟨(projectiveLinePuncturedChart k).base w, ?_⟩
      calc (projectiveLineXChart k).base ((projectiveLinePuncturedChart k).base w)
          = (projectiveLinePuncturedChart k ≫ projectiveLineXChart k).base w := rfl
        _ = (projectiveLineOverlapYInclusion k ≫ projectiveLineYChart k).base w := by
          rw [(isPullback_projectiveLineCharts k).w]
        _ = (projectiveLineYChart k).base y := by rw [← hw]; rfl

/-- The first chart of the projective line sends the generic point of `Spec k[X]` to the generic
point of the projective line. -/
theorem projectiveLineXChart_genericPoint_eq :
    (projectiveLineXChart k).base (genericPoint (Spec (.of (Polynomial k)))) =
      genericPoint (projectiveLine k) :=
  genericPoint_eq_of_isOpenImmersion (projectiveLineXChart k)

/-- A point of the affine line over a field whose prime ideal is zero is its generic point. -/
theorem eq_genericPoint_of_asIdeal_eq_bot (y : Spec (.of (Polynomial k)))
    (hy : y.asIdeal = ⊥) : y = genericPoint (Spec (.of (Polynomial k))) := by
  rw [genericPoint_eq_bot_of_affine]
  exact PrimeSpectrum.ext (by simpa using hy)

/-- The base map of the first chart of the projective line is injective. -/
theorem projectiveLineXChart_base_injective :
    Function.Injective (projectiveLineXChart k).base :=
  (projectiveLineXChart k).isOpenEmbedding.injective

/-- The points `0` and `∞` of the projective line are distinct. -/
@[stacks 01JE "projective_line_gluing"]
theorem projectiveLineZero_ne_projectiveLineInfinity (k : Type u) [Field k] :
    projectiveLineZero k ≠ projectiveLineInfinity k := by
  intro h
  obtain ⟨w, hw, -⟩ := (projectiveLineXChart_base_eq_projectiveLineYChart_base_iff k
    (affineLineOrigin k) (affineLineOrigin k)).mp h
  exact (mem_range_projectiveLinePuncturedChart_iff k _).mp ⟨w, hw⟩ (Ideal.subset_span rfl)

/-! ### The projective line is infinite -/

/-- Given finitely many monic polynomials over a field, there is a monic irreducible polynomial
not among them. -/
theorem exists_monic_irreducible_notMem (k : Type u) [Field k] (s : Finset (Polynomial k))
    (hs : ∀ p ∈ s, p.Monic) :
    ∃ q : Polynomial k, q.Monic ∧ Irreducible q ∧ q ∉ s := by
  classical
  set P : Polynomial k := ∏ p ∈ s, p with hP
  have hPm : P.Monic := Polynomial.monic_prod_of_monic _ _ hs
  have hXPdeg : 0 < (Polynomial.X * P : Polynomial k).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos,
      Polynomial.natDegree_mul Polynomial.X_ne_zero hPm.ne_zero, Polynomial.natDegree_X]
    omega
  have hdeg : 0 < (Polynomial.X * P + 1 : Polynomial k).degree := by
    rw [Polynomial.degree_add_eq_left_of_degree_lt (by rw [Polynomial.degree_one]; exact hXPdeg)]
    exact hXPdeg
  obtain ⟨q₀, hq₀i, hq₀d⟩ := Polynomial.exists_irreducible_of_degree_pos hdeg
  obtain ⟨p, hpm, hpi, hpq⟩ := exists_monic_irreducible_associated hq₀i
  refine ⟨p, hpm, hpi, fun hmem ↦ hpi.not_isUnit (isUnit_of_dvd_one ?_)⟩
  have hpP : p ∣ P := hP ▸ Finset.dvd_prod_of_mem (fun p ↦ p) hmem
  simpa using dvd_sub (hpq.dvd.trans hq₀d) (hpP.mul_left Polynomial.X)

/-- There are infinitely many monic irreducible polynomials over a field. -/
theorem infinite_setOf_monic_irreducible (k : Type u) [Field k] :
    {p : Polynomial k | p.Monic ∧ Irreducible p}.Infinite := by
  intro hfin
  obtain ⟨q, hqm, hqi, hq⟩ := exists_monic_irreducible_notMem k hfin.toFinset
    (fun p hp ↦ (hfin.mem_toFinset.mp hp).1)
  exact hq (hfin.mem_toFinset.mpr ⟨hqm, hqi⟩)

/-- The affine line over a field is infinite. -/
theorem infinite_affineLine (k : Type u) [Field k] : Infinite (Spec (.of (Polynomial k))) := by
  have h1 : {y : Spec (.of (Polynomial k)) | y.asIdeal ≠ ⊥}.Infinite := by
    intro hfin
    refine infinite_setOf_monic_irreducible k ?_
    rw [← bijOn_affineLineGenerator.image_eq]
    exact hfin.image _
  exact @Infinite.of_injective _ _ h1.to_subtype Subtype.val Subtype.val_injective

/-- The projective line over a field is infinite. -/
@[stacks 01JE "projective_line_infinite"]
instance infinite_projectiveLine (k : Type u) [Field k] : Infinite (projectiveLine k) :=
  @Infinite.of_injective _ _ (infinite_affineLine k) _
    (projectiveLineXChart_base_injective (k := k))

end AlgebraicGeometry

end
