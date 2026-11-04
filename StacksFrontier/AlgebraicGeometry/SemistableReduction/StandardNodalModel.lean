module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalChartIsNodal
public import StacksFrontier.AlgebraicGeometry.F6Rank136.SmoothIsNodal
public import StacksFrontier.RingTheory.NodalChart.Regularity
public import StacksFrontier.RingTheory.NodalChart.Smooth
public import StacksCore.Tactic.StacksAttribute

/-!
# The standard nodal model `Spec R[x, y]/(xy - πⁿ)` over a discrete valuation ring

Let `R` be a discrete valuation ring with uniformizer `π`, let `n ≥ 0`, and consider the ring map
`R → A = R[x, y]/(xy - πⁿ)`. The *standard nodal model* of exponent `n` is the affine scheme
`X = Spec A` over `S = Spec R`. This file packages that family as a morphism of schemes and
records the facts of [Stacks, Tag 0CDC] about it:

* for `n = 0` the morphism `X → S` is smooth;
* for every `n` the morphism `X → S` is at-worst-nodal of relative dimension one;
* for `n = 1` the scheme `X` is regular;
* for `n > 1` it is not, the obstruction being that the two coordinates `x` and `y` no longer
  generate the maximal ideal `𝔪 = (π, x, y)` of the origin.

The last point is made precise as a statement about the ideal `𝔪 = (π, x, y)` of `A`: the
parameter of the defining relation always lies in `(x, y)`, because the relation reads `πⁿ = xy`,
so for `n = 1` the two ideals agree; for `n ≥ 2` the inclusion `(x, y) ⊆ 𝔪` is strict, since
mapping a relation `π = ax + by` into `R ⧸ (πⁿ)` by killing both coordinates would make
`π^(n-1)` a unit.

## Main definitions

* `Stacks.nodalModel` — the scheme `X = Spec R[x, y]/(xy - πⁿ)`.
* `Stacks.nodalModelHom` — its structure morphism `X ⟶ S = Spec R`.
* `Stacks.nodalModelOrigin` — the ideal `𝔪 = (π, x, y)` of the origin of `X`.

## Main results

* `Stacks.smooth_nodalModelHom_zero` — the exponent zero model is smooth over `S`.
* `Stacks.isMaximal_nodalModelOrigin` — `𝔪 = (π, x, y)` is a maximal ideal of `A` for `n ≥ 1`.
* `Stacks.span_nodalGen_eq_nodalModelOrigin_one` and
  `Stacks.span_nodalGen_lt_nodalModelOrigin_of_two_le` — the two coordinates span `𝔪` for
  `n = 1` and span a strictly smaller ideal for `n ≥ 2`.
* `Stacks.smoothOfRelativeDimension_one_nodalModelHom_zero` and
  `Stacks.isAtWorstNodalOfRelativeDimensionOne_nodalModelHom_zero` — the exponent zero model is
  smooth of relative dimension one, hence at-worst-nodal of relative dimension one.
* `Stacks.isAtWorstNodalOfRelativeDimensionOne_nodalModelHom` — every member of the family is
  at-worst-nodal of relative dimension one.
* `Stacks.isRegular_nodalModel_one` — the exponent one model is a regular scheme.
* `Stacks.not_isRegular_nodalModel_of_one_lt` — a model of exponent greater than one is not.

## Implementation notes

The ring `A` is `Stacks.nodalChartRing R (π ^ n)`, and the smoothness and regularity facts are
the statements of `StacksFrontier.RingTheory.NodalChart.Smooth` and
`StacksFrontier.RingTheory.NodalChart.Regularity` transported to the family. Smoothness at `n = 0`
needs no hypothesis on `R` or `π`, since `π⁰ = 1` turns the relation into `xy = 1` and makes `A`
the localization `R[x]ₓ`.

The failure of `(x, y)` to span is proved with the `R`-algebra map `A → R ⧸ (πⁿ)` sending both
coordinates to zero, which exists because `0 · 0` and `πⁿ` agree in `R ⧸ (πⁿ)`; it is
`Stacks.nodalLift` at the zero pair. Maximality of `𝔪` is inherited from
`Stacks.isMaximal_nodalOriginIdeal` for the ideal `(π, x, y)` of `R[x, y]`, whose image `𝔪` is
maximal because the defining relation lies in it, so that the image is not the unit ideal.

Relative dimension one at `n = 0` is read off a submersive presentation of `A` with two variables
and the single relation `xy - 1`, whose Jacobian `∂(xy - 1)/∂y = x` is a unit there; the relative
dimension `2 - 1 = 1` is then the dimension of that presentation, and the passage to the morphism
of schemes is `AlgebraicGeometry.HasRingHomProperty.Spec_iff` for
`AlgebraicGeometry.SmoothOfRelativeDimension`. Being at-worst-nodal then follows from Tag 0CD7,
`AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_of_smoothOfRelativeDimension`. The tag
asserts the at-worst-nodal property for every `n`, and that is
`Stacks.isAtWorstNodalOfRelativeDimensionOne_specMap_nodalChartRing` of
`StacksFrontier.AlgebraicGeometry.Curves.NodalChartIsNodal`, read off the presentation of the chart
ring by two variables and the single relation `xy - πⁿ`: the fibres of that presentation have
dimension `2 - 1 = 1`, and the first Fitting ideal of the relative differentials is the ideal
`(x, y)` of the two coordinates, whose closed subscheme is `Spec R/(πⁿ)` and so is a closed
immersion over `S`. The exponent zero statement is kept because it is the tag's own, and because
it comes from smoothness rather than from that computation.

Tag 0CDC continues with the blowup of `X` at the origin for `n > 1`, its three charts, and the
chain of blowups that the exponent drop `n ↦ n - 2` of the central chart produces. The chart
algebras are `Stacks.nodalCentralChart`, `Stacks.nodalXChart` and `Stacks.nodalYChart` of
`StacksFrontier.RingTheory.NodalChart.Blowup`, and the regularity of the two outer charts is
`Stacks.isRegular_spec_nodalXChart` and `Stacks.isRegular_spec_nodalYChart`; the blowup itself,
as a morphism of schemes, is not treated here.

## References

* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks

variable {R : Type u} [CommRing R]

/-! ### The family -/

/-- The standard nodal model `X = Spec R[x, y]/(xy - πⁿ)` of exponent `n`, an affine scheme over
`S = Spec R`. -/
@[stacks 0CDC "the scheme X = Spec A of the family A = R[x, y]/(xy - πⁿ)"]
public def nodalModel (R : Type u) [CommRing R] (π : R) (n : ℕ) : Scheme.{u} :=
  Spec (CommRingCat.of (nodalChartRing R (π ^ n)))

/-- The structure morphism `X ⟶ S = Spec R` of the standard nodal model, the morphism of schemes
induced by the ring map `R → A = R[x, y]/(xy - πⁿ)`. -/
@[stacks 0CDC "the morphism X ⟶ S = Spec R induced by R → A = R[x, y]/(xy - πⁿ)"]
public def nodalModelHom (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    nodalModel R π n ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R (π ^ n))))

/-! ### Smoothness at exponent zero -/

/-- **The exponent zero model is smooth over the base.** For `n = 0` the defining relation reads
`xy = 1`, and `X ⟶ S` is smooth; no hypothesis on `R` or `π` is needed. -/
@[stacks 0CDC "if n = 0 then X → S is smooth"]
public theorem smooth_nodalModelHom_zero (π : R) : Smooth (nodalModelHom R π 0) :=
  smooth_specMap_nodalChartRing_pow_zero R π

/-! ### The maximal ideal of the origin -/

/-- The ideal `𝔪 = (π, x, y)` of the origin of the standard nodal model, as an ideal of
`A = R[x, y]/(xy - πⁿ)`. -/
public def nodalModelOrigin (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Ideal (nodalChartRing R (π ^ n)) :=
  Ideal.span {algebraMap R (nodalChartRing R (π ^ n)) π, nodalGen R (π ^ n) 0,
    nodalGen R (π ^ n) 1}

/-- The ideal of the origin is the image of the origin ideal `(π, x, y)` of `R[x, y]`. -/
public theorem nodalModelOrigin_eq_map (π : R) (n : ℕ) :
    nodalModelOrigin R π n =
      Ideal.map (algebraMap (MvPolynomial (Fin 2) R) (nodalChartRing R (π ^ n)))
        (nodalOriginIdeal R π) := by
  rw [nodalModelOrigin, nodalOriginIdeal, Ideal.map_span]
  congr 1
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  rfl

/-- **The ideal of the origin is maximal** as soon as `(π)` is maximal in `R` and the exponent is
positive: it is the image of the maximal ideal `(π, x, y)` of `R[x, y]`, which contains the
defining relation. -/
public theorem isMaximal_nodalModelOrigin {π : R} (hπ : (Ideal.span {π}).IsMaximal) {n : ℕ}
    (hn : 1 ≤ n) : (nodalModelOrigin R π n).IsMaximal := by
  have hmax := isMaximal_nodalOriginIdeal hπ
  have hrel : nodalEquation R (π ^ n) ∈ nodalOriginIdeal R π := by
    rw [nodalEquation_def]
    refine sub_mem (Ideal.mul_mem_right _ _ (X_mem_nodalOriginIdeal π 0)) ?_
    rw [map_pow]
    exact Ideal.pow_mem_of_mem _ (C_mem_nodalOriginIdeal π) n hn
  have hker : Ideal.span ({nodalEquation R (π ^ n)} : Set (MvPolynomial (Fin 2) R))
      ≤ nodalOriginIdeal R π := by
    rw [Ideal.span_le]
    simpa using hrel
  rw [nodalModelOrigin_eq_map]
  have := hmax
  exact Ideal.IsMaximal.map_of_surjective_of_ker_le
    (f := Ideal.Quotient.mk (Ideal.span ({nodalEquation R (π ^ n)} :
      Set (MvPolynomial (Fin 2) R)))) Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

/-- The parameter of a nodal chart ring lies in the ideal spanned by the two coordinates, the
defining relation being `h = xy`. -/
public theorem algebraMap_mem_span_nodalGen (h : R) :
    algebraMap R (nodalChartRing R h) h ∈
      Ideal.span {nodalGen R h 0, nodalGen R h 1} := by
  rw [← nodalGen_zero_mul_nodalGen_one h]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))

/-- Adjoining the relation parameter to the two coordinates of a nodal chart ring does not
enlarge the ideal they span. -/
public theorem span_nodalGen_eq_span_insert (h : R) :
    Ideal.span {nodalGen R h 0, nodalGen R h 1} =
      Ideal.span {algebraMap R (nodalChartRing R h) h, nodalGen R h 0, nodalGen R h 1} := by
  refine le_antisymm (Ideal.span_mono (Set.subset_insert _ _)) (Ideal.span_le.2 ?_)
  rintro z (rfl | rfl | rfl)
  · exact algebraMap_mem_span_nodalGen h
  · exact Ideal.subset_span (Set.mem_insert _ _)
  · exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

/-- **At exponent one the two coordinates generate the maximal ideal of the origin.** The
defining relation reads `π = xy`, so the uniformizer already lies in `(x, y)` and
`𝔪 = (π, x, y) = (x, y)`. -/
@[stacks 0CDC "if n = 1 then (x, y) generate the maximal ideal 𝔪 = (π, x, y)"]
public theorem span_nodalGen_eq_nodalModelOrigin_one (π : R) :
    Ideal.span {nodalGen R (π ^ 1) 0, nodalGen R (π ^ 1) 1} = nodalModelOrigin R π 1 := by
  rw [nodalModelOrigin, pow_one]
  exact span_nodalGen_eq_span_insert π

/-- For exponent at least two the uniformizer is not in the ideal spanned by the two coordinates
of `R[x, y]/(xy - πⁿ)`: mapping a relation `π = ax + by` into `R ⧸ (πⁿ)` by killing both
coordinates would make `π^(n-1)` a unit. -/
public theorem algebraMap_notMem_span_nodalGen_of_two_le [IsDomain R] {π : R}
    (hπ : Irreducible π) {n : ℕ} (hn : 2 ≤ n) :
    algebraMap R (nodalChartRing R (π ^ n)) π ∉
      Ideal.span {nodalGen R (π ^ n) 0, nodalGen R (π ^ n) 1} := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  intro hmem
  set J : Ideal R := Ideal.span {π ^ (m + 2)} with hJ
  have hvanish : algebraMap R (R ⧸ J) (π ^ (m + 2)) = 0 := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, hJ]
    exact Ideal.mem_span_singleton_self _
  have hu : (0 : Fin 2 → R ⧸ J) 0 * (0 : Fin 2 → R ⧸ J) 1
      = algebraMap R (R ⧸ J) (π ^ (m + 2)) := by
    simp only [Pi.zero_apply, mul_zero, hvanish]
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hmem
  have hπJ : algebraMap R (R ⧸ J) π = 0 := by
    have h := congrArg (nodalLift (0 : Fin 2 → R ⧸ J) hu) hab
    rw [map_add, map_mul, map_mul, nodalLift_nodalGen, nodalLift_nodalGen,
      AlgHom.commutes] at h
    simpa using h.symm
  have hπmem : π ∈ J := by
    rwa [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hπJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hJ ▸ hπmem)
  have hcancel : c * π ^ (m + 1) = 1 := by
    refine mul_left_cancel₀ hπ.ne_zero ?_
    rw [mul_one]
    linear_combination hc
  exact hπ.not_isUnit (IsUnit.of_mul_eq_one (c * π ^ m) (by linear_combination hcancel))

/-- **For exponent at least two the two coordinates no longer generate the maximal ideal of the
origin.** The ideal `(x, y)` of `R[x, y]/(xy - πⁿ)` is strictly smaller than `𝔪 = (π, x, y)`. -/
@[stacks 0CDC "if n > 1 then (x, y) no longer generate the maximal ideal 𝔪 = (π, x, y)"]
public theorem span_nodalGen_lt_nodalModelOrigin_of_two_le [IsDomain R] {π : R}
    (hπ : Irreducible π) {n : ℕ} (hn : 2 ≤ n) :
    Ideal.span {nodalGen R (π ^ n) 0, nodalGen R (π ^ n) 1} < nodalModelOrigin R π n := by
  refine lt_of_le_of_ne (Ideal.span_mono (Set.subset_insert _ _)) fun hEq ↦ ?_
  refine algebraMap_notMem_span_nodalGen_of_two_le hπ hn ?_
  rw [hEq, nodalModelOrigin]
  exact Ideal.subset_span (Set.mem_insert _ _)

/-! ### At-worst-nodal at exponent zero -/

/-- A constant map out of `Fin 1` is injective. -/
private theorem injective_const_fin_one (j : Fin 2) :
    Function.Injective (fun _ : Fin 1 ↦ j) :=
  fun a b _ ↦ Subsingleton.elim a b

variable (R) in
/-- The presentation of `R[x, y]/(xy - 1)` by the two coordinates and the single relation
`xy - 1`, with the relation assigned to the second coordinate. -/
private def nodalOnePre :
    Algebra.PreSubmersivePresentation R
      (MvPolynomial (Fin 2) R ⧸ Ideal.span (Set.range fun _ : Fin 1 ↦ nodalEquation R 1))
      (Fin 2) (Fin 1) :=
  Algebra.PreSubmersivePresentation.naive (v := fun _ : Fin 1 ↦ nodalEquation R 1)
    (fun _ ↦ (1 : Fin 2)) (injective_const_fin_one 1)

variable (R) in
/-- The Jacobian of that presentation is `∂(xy - 1)/∂y = x`, a unit because the relation reads
`xy = 1`. -/
private theorem isUnit_jacobian_nodalOnePre : IsUnit (nodalOnePre R).jacobian := by
  have hzero : algebraMap (MvPolynomial (Fin 2) R)
      (MvPolynomial (Fin 2) R ⧸ Ideal.span (Set.range fun _ : Fin 1 ↦ nodalEquation R 1))
      (nodalEquation R 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨0, rfl⟩)
  rw [nodalEquation_def, map_sub, sub_eq_zero, MvPolynomial.C_1, map_one] at hzero
  have hpd : MvPolynomial.pderiv ((nodalOnePre R).map 0) ((nodalOnePre R).relation 0)
      = MvPolynomial.X 0 := by
    change MvPolynomial.pderiv (1 : Fin 2) (nodalEquation R 1) = MvPolynomial.X 0
    simp [nodalEquation_def]
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_fin_one,
    Algebra.PreSubmersivePresentation.jacobiMatrix_apply, hpd]
  exact IsUnit.of_mul_eq_one _ (by rw [← map_mul]; exact hzero)

variable (R) in
/-- The presentation of `R[x, y]/(xy - 1)` above, as a submersive presentation. -/
private def nodalOnePresentation :
    Algebra.SubmersivePresentation R
      (MvPolynomial (Fin 2) R ⧸ Ideal.span (Set.range fun _ : Fin 1 ↦ nodalEquation R 1))
      (Fin 2) (Fin 1) where
  __ := nodalOnePre R
  jacobian_isUnit := isUnit_jacobian_nodalOnePre R

variable (R) in
/-- The nodal chart ring with parameter one is standard smooth of relative dimension one over
`R`: two coordinates subject to one relation with invertible Jacobian. -/
private theorem isStandardSmoothOfRelativeDimension_one_nodalChartRing :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (nodalChartRing R 1) := by
  have hspan : Ideal.span (Set.range fun _ : Fin 1 ↦ nodalEquation R 1) =
      Ideal.span ({nodalEquation R 1} : Set (MvPolynomial (Fin 2) R)) := by
    rw [Set.range_const]
  let := (nodalOnePresentation R).isStandardSmoothOfRelativeDimension
    (n := 1) (by simp [Algebra.Presentation.dimension])
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
    (Ideal.quotientEquivAlgOfEq R hspan)

variable (R) in
/-- **The structure morphism `Spec R[x, y]/(xy - 1) → Spec R` is smooth of relative dimension
one.** -/
public theorem smoothOfRelativeDimension_one_specMap_nodalChartRing_one :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R (1 : R))))) :=
  HasRingHomProperty.Spec_iff.2
    (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).2
        (isStandardSmoothOfRelativeDimension_one_nodalChartRing R)))

/-- **The exponent zero model is smooth of relative dimension one over the base.** -/
public theorem smoothOfRelativeDimension_one_nodalModelHom_zero (π : R) :
    SmoothOfRelativeDimension 1 (nodalModelHom R π 0) := by
  change SmoothOfRelativeDimension 1
    (Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R (π ^ 0)))))
  rw [pow_zero]
  exact smoothOfRelativeDimension_one_specMap_nodalChartRing_one R

/-- **The exponent zero model is at-worst-nodal of relative dimension one over the base.** It is
smooth of relative dimension one, and a smooth family of curves has empty relative singular
subscheme. -/
@[stacks 0CDC "the exponent zero member of the family is at-worst-nodal of relative dimension one"]
public theorem isAtWorstNodalOfRelativeDimensionOne_nodalModelHom_zero (π : R) :
    IsAtWorstNodalOfRelativeDimensionOne (nodalModelHom R π 0) :=
  let := smoothOfRelativeDimension_one_nodalModelHom_zero π
  isAtWorstNodalOfRelativeDimensionOne_of_smoothOfRelativeDimension _

/-- **Every member of the family is at-worst-nodal of relative dimension one over the base.** For
every exponent `n` the morphism `X = Spec R[x, y]/(xy - πⁿ) ⟶ S = Spec R` is syntomic of relative
dimension one and its relative singular subscheme, cut out by the two coordinates, is unramified
over `S`. No hypothesis on `R` or `π` is needed. -/
@[stacks 0CDC "for all n the morphism X → S is at-worst-nodal of relative dimension 1"]
public theorem isAtWorstNodalOfRelativeDimensionOne_nodalModelHom (π : R) (n : ℕ) :
    IsAtWorstNodalOfRelativeDimensionOne (nodalModelHom R π n) :=
  isAtWorstNodalOfRelativeDimensionOne_specMap_nodalChartRing (π ^ n)

/-! ### Regularity over a discrete valuation ring -/

section DiscreteValuationRing

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- **The exponent one model is regular.** For `π` a uniformizer of a discrete valuation ring the
scheme `Spec R[x, y]/(xy - π)` is regular. -/
@[stacks 0CDC "if n = 1 then X is regular", sga "7 XVI 1.13" "Case 1, special case"]
public theorem isRegular_nodalModel_one {π : R} (hπ : Irreducible π) :
    IsRegular (nodalModel R π 1) :=
  isRegular_spec_nodalChartRing_pow_one hπ

/-- **A model of exponent greater than one is not regular.** It is singular at the origin
`(π, x, y)`, where the two coordinates no longer span the maximal ideal. -/
@[stacks 0CDC "if n > 1 then X is not regular"]
public theorem not_isRegular_nodalModel_of_one_lt {π : R} (hπ : Irreducible π) {n : ℕ}
    (hn : 1 < n) : ¬ IsRegular (nodalModel R π n) :=
  not_isRegular_spec_nodalChartRing_pow_of_one_lt hπ hn

end DiscreteValuationRing

end Stacks

end
