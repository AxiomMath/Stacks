module

public import Mathlib.Algebra.Polynomial.Reverse
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineOrders

/-!
# The order of vanishing at the point at infinity of the projective line

The point at infinity of `ℙ¹_k` is the origin of the second chart, and the coordinate of the
second chart is the inverse of the coordinate of the first. So the order of vanishing of a
rational function at infinity is its order at the origin after the substitution `x ↦ x⁻¹`, which
on `RatFunc k` is minus the integer degree, namely `Stacks.Chow.ordAtInfty`. The residue degree
there is one, the degree of the polynomial `X` cutting out the origin of a chart.

This completes the dictionary begun in
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineFunctionField`,
whose implementation notes list exactly this statement as the one still missing: with it every
term of the sum of Stacks 02RU for `ℙ¹_k` is identified with a term of
`Stacks.Chow.finsum_ordAt_mul_natDegree_add_ordAtInfty_eq_zero`.

## Main definitions

* `AlgebraicGeometry.projectiveLineFunctionFieldEquivY` — the identification of the function
  field of the projective line with that of the second chart.
* `AlgebraicGeometry.projectiveLineChartInversion` — the automorphism `x ↦ x⁻¹` of `RatFunc k`
  that glues the two charts, read on the function field through the first chart.

## Main results

* `Stacks.Chow.ordAt_X_map_eq_ordAtInfty` — **the algebraic heart**: for any ring endomorphism of
  `RatFunc k` fixing the constants and inverting the coordinate, the order at `X` of the image of
  `g` is `Stacks.Chow.ordAtInfty g`.
* `Stacks.Chow.dominantFunctionFieldMap_algebraMap_spec` — for a dominant morphism of affine
  integral schemes the induced extension of function fields extends the ring map.
* `AlgebraicGeometry.dominantFunctionFieldMap_chart_overlap_eq` — the two charts induce the same
  identification of the function field of `ℙ¹` with that of the overlap.
* `AlgebraicGeometry.projectiveLineChartInversion_C` and
  `AlgebraicGeometry.projectiveLineChartInversion_X` — the transition fixes the constants and
  inverts the coordinate.
* `AlgebraicGeometry.ord_projectiveLine_infinity` — **the order of vanishing at infinity is
  `Stacks.Chow.ordAtInfty`.**
* `AlgebraicGeometry.residueDegree_projectiveLine_infinity` — the point at infinity has residue
  degree one over the base field.

## Implementation notes

The algebraic identity is stated for an arbitrary ring homomorphism `σ : RatFunc k →+* RatFunc k`
with `σ(c) = c` for `c ∈ k` and `σ(x) = x⁻¹`, rather than for a constructed automorphism: that is
the only form in which it is applied, and it needs no uniqueness statement. The computation is
`Polynomial.eval₂_reverse_mul_pow`, which says that evaluating the reverse of `p` at `x⁻¹` and
multiplying by `x ^ deg p` recovers the value of `p` at `x`; it turns `σ(p)` into
`p.reverse / x ^ deg p`, whose order at `X` is `-deg p` because `X` does not divide a reverse.

`Stacks.Chow.dominantFunctionFieldMap_algebraMap_spec` is the `⊤`-to-`⊤` case of the compatibility
of `AlgebraicGeometry.dominantFunctionFieldMap` with germs; the general statement exists in
`StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula` but is private there, and
only the affine case is needed here, where it reads as an identity between the two canonical
`Algebra` structures on a function field.

The transition between the two charts is obtained from the commuting square
`AlgebraicGeometry.isPullback_projectiveLineCharts` by applying
`Stacks.Chow.dominantFunctionFieldMap_comp` to both of its sides; the two composites are the two
routes from the function field of `ℙ¹` to that of the overlap `Spec k[T, T⁻¹]`, where the
coordinate of the first chart is `T` and that of the second is `T⁻¹`.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-! ### The order at the origin after inverting the coordinate -/

section Inversion

open Polynomial UniqueFactorizationMonoid

namespace Stacks.Chow

variable {k : Type u} [Field k] [DecidableEq k]

omit [DecidableEq k] in
/-- The coordinate of the affine line is a nonzero rational function. -/
theorem algebraMap_X_ne_zero : (algebraMap k[X] (RatFunc k)) X ≠ 0 :=
  RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero

omit [DecidableEq k] in
/-- **Inverting the coordinate reverses a polynomial.** A ring endomorphism of `RatFunc k`
fixing the constants and inverting the coordinate sends a polynomial `p` to `p.reverse` divided
by `x ^ deg p`: evaluating the reverse at `x⁻¹` and multiplying by `x ^ deg p` recovers the value
of `p` at `x`. -/
theorem map_algebraMap_mul_pow_eq_reverse (σ : RatFunc k →+* RatFunc k)
    (hC : ∀ c : k, σ (algebraMap k[X] (RatFunc k) (C c)) = algebraMap k[X] (RatFunc k) (C c))
    (hX : σ (algebraMap k[X] (RatFunc k) X) = (algebraMap k[X] (RatFunc k) X)⁻¹) (p : k[X]) :
    σ (algebraMap k[X] (RatFunc k) p) * (algebraMap k[X] (RatFunc k) X) ^ p.natDegree =
      algebraMap k[X] (RatFunc k) p.reverse := by
  have hX0 : (algebraMap k[X] (RatFunc k)) X ≠ 0 := algebraMap_X_ne_zero
  let inv : Invertible (((algebraMap k[X] (RatFunc k)) X)⁻¹ : RatFunc k) :=
    ⟨algebraMap k[X] (RatFunc k) X, mul_inv_cancel₀ hX0, inv_mul_cancel₀ hX0⟩
  have hinvOf : (⅟ (((algebraMap k[X] (RatFunc k)) X)⁻¹) : RatFunc k) =
      algebraMap k[X] (RatFunc k) X := rfl
  set i : k →+* RatFunc k := (algebraMap k[X] (RatFunc k) : k[X] →+* RatFunc k).comp
    (Polynomial.C (R := k))
  have hbase : ∀ q : k[X], algebraMap k[X] (RatFunc k) q =
      Polynomial.eval₂ i (algebraMap k[X] (RatFunc k) X) q := by
    intro q
    conv_lhs => rw [← Polynomial.eval₂_C_X (p := q)]
    exact Polynomial.hom_eval₂ q Polynomial.C (algebraMap k[X] (RatFunc k) : k[X] →+* RatFunc k) X
  have hsig : σ (algebraMap k[X] (RatFunc k) p) =
      Polynomial.eval₂ i ((algebraMap k[X] (RatFunc k) X)⁻¹) p := by
    rw [hbase p, Polynomial.hom_eval₂ p i σ (algebraMap k[X] (RatFunc k) X), hX]
    congr 1
    ext c
    exact hC c
  have hrev := Polynomial.eval₂_reverse_mul_pow i ((algebraMap k[X] (RatFunc k) X)⁻¹) p
  rw [hinvOf] at hrev
  rw [hsig, ← hrev, ← hbase p.reverse, mul_assoc, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero _ hX0), mul_one]

/-- The coordinate does not divide a reverse polynomial, so its multiplicity there is zero: the
constant term of `p.reverse` is the leading coefficient of `p`. -/
theorem count_normalizedFactors_reverse_eq_zero {q : k[X]} (hq : q ≠ 0) :
    (normalizedFactors q.reverse).count X = 0 := by
  refine Multiset.count_eq_zero_of_notMem fun hmem => ?_
  have hdvd : (X : k[X]) ∣ q.reverse := dvd_of_mem_normalizedFactors hmem
  rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_reverse] at hdvd
  exact hq (Polynomial.leadingCoeff_eq_zero.mp hdvd)

/-- The multiplicity of the coordinate in one of its powers is the exponent. -/
theorem count_normalizedFactors_X_pow (m : ℕ) :
    (normalizedFactors ((X : k[X]) ^ m)).count X = m := by
  rw [normalizedFactors_pow, normalizedFactors_irreducible Polynomial.irreducible_X,
    Polynomial.monic_X.normalize_eq_self, Multiset.count_nsmul]
  simp

/-- The multiplicity of the coordinate in `p.reverse * X ^ m` is `m`. -/
theorem count_normalizedFactors_reverse_mul_X_pow {q : k[X]} (hq : q ≠ 0) (m : ℕ) :
    (normalizedFactors (q.reverse * (X : k[X]) ^ m)).count X = m := by
  rw [normalizedFactors_mul (mt Polynomial.reverse_eq_zero.mp hq)
      (pow_ne_zero m Polynomial.X_ne_zero), Multiset.count_add,
    count_normalizedFactors_reverse_eq_zero hq, count_normalizedFactors_X_pow, zero_add]

/-- **The order at infinity is the order at the origin after inverting the coordinate.** Let
`σ` be a ring endomorphism of `RatFunc k` fixing the constants and sending the coordinate to its
inverse. Then the order of vanishing of `σ g` at the closed point `(X)` is
`Stacks.Chow.ordAtInfty g`, minus the integer degree of `g`.

Writing `g = a / b` with `a, b ∈ k[X]`, the function `σ g` is
`(a.reverse · X ^ deg b) / (b.reverse · X ^ deg a)`, and the coordinate divides neither reverse,
so the order is `deg b - deg a`. -/
theorem ordAt_X_map_eq_ordAtInfty (σ : RatFunc k →+* RatFunc k)
    (hC : ∀ c : k, σ (algebraMap k[X] (RatFunc k) (C c)) = algebraMap k[X] (RatFunc k) (C c))
    (hX : σ (algebraMap k[X] (RatFunc k) X) = (algebraMap k[X] (RatFunc k) X)⁻¹)
    (h : RatFunc k) :
    ordAt X (σ h) = ordAtInfty h := by
  by_cases hh : h = 0
  · subst hh
    simp
  have hX0 : (algebraMap k[X] (RatFunc k)) X ≠ 0 := algebraMap_X_ne_zero
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := k[X]) h
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hab
    exact hh hab.symm
  have hra : a.reverse ≠ 0 := mt Polynomial.reverse_eq_zero.mp ha0
  have hrb : b.reverse ≠ 0 := mt Polynomial.reverse_eq_zero.mp hb0
  have ha' := map_algebraMap_mul_pow_eq_reverse σ hC hX a
  have hb' := map_algebraMap_mul_pow_eq_reverse σ hC hX b
  have hrb0 : (algebraMap k[X] (RatFunc k) b.reverse : RatFunc k) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hrb
  have hsb : σ (algebraMap k[X] (RatFunc k) b) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hb'
    exact hrb0 hb'.symm
  have hform : σ h = algebraMap k[X] (RatFunc k) (a.reverse * X ^ b.natDegree) /
      algebraMap k[X] (RatFunc k) (b.reverse * X ^ a.natDegree) := by
    rw [← hab, map_div₀, map_mul, map_mul, map_pow, map_pow, ← ha', ← hb']
    field_simp
  rw [hform, ordAt_div X (mul_ne_zero hra (pow_ne_zero _ Polynomial.X_ne_zero))
      (mul_ne_zero hrb (pow_ne_zero _ Polynomial.X_ne_zero)),
    count_normalizedFactors_reverse_mul_X_pow ha0,
    count_normalizedFactors_reverse_mul_X_pow hb0, ordAtInfty, ← hab,
    RatFunc.intDegree_div (RatFunc.algebraMap_ne_zero ha0)
      (RatFunc.algebraMap_ne_zero hb0),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
  ring

end Stacks.Chow

end Inversion

/-! ### Function fields of affine schemes along a dominant morphism -/

namespace Stacks.Chow

/-- An open immersion with nonempty source into a preirreducible scheme is dominant: its range
is a nonempty open, hence dense.

The prime marks the weaker hypothesis on the target: `Stacks.Chow.isDominant_of_isOpenImmersion`
is the same conclusion asked of an irreducible target. -/
theorem isDominant_of_isOpenImmersion' {X Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i]
    [PreirreducibleSpace Y] [Nonempty X] : IsDominant i :=
  ⟨(i.isOpenEmbedding.isOpen_range).dense (Set.range_nonempty _)⟩

/-- The extension of function fields induced by a dominant morphism depends only on the
morphism, not on the proof that it is dominant. -/
theorem dominantFunctionFieldMap_congr {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f g : X ⟶ Y) [IsDominant f] [IsDominant g] (h : f = g) :
    dominantFunctionFieldMap f = dominantFunctionFieldMap g := by
  subst h
  rfl

/-- The canonical algebra structure on the function field of an affine scheme is the germ at the
generic point of the corresponding global section. -/
theorem algebraMap_functionField_spec_eq_germ (R : CommRingCat.{u}) [IsDomain R] (r : R) :
    algebraMap R (Spec R).functionField r =
      (Spec R).presheaf.germ ⊤ (genericPoint (Spec R)) trivial ((Scheme.ΓSpecIso R).inv r) := by
  rw [RingHom.algebraMap_toAlgebra]
  rfl

/-- **The function-field extension of a dominant morphism of affine schemes extends the ring
map.** This is the `⊤`-to-`⊤` compatibility of
`AlgebraicGeometry.dominantFunctionFieldMap` with germs, read through the identification of the
function field of `Spec R` with a fraction field of `R`. -/
theorem dominantFunctionFieldMap_algebraMap_spec {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [IsDomain R] [IsDomain S] [IsDominant (Spec.map φ)] (r : R) :
    dominantFunctionFieldMap (Spec.map φ) (algebraMap R (Spec R).functionField r) =
      algebraMap S (Spec S).functionField (φ r) := by
  have hgen : (Spec.map φ).base (genericPoint (Spec S)) = genericPoint (Spec R) :=
    ((tfae_isDominant_of_isIntegral (Spec.map φ)).out 1 2).mp
      (inferInstance : IsDominant (Spec.map φ))
  rw [algebraMap_functionField_spec_eq_germ R r, algebraMap_functionField_spec_eq_germ S (φ r)]
  change (hgen ▸ (Spec.map φ).stalkMap (genericPoint (Spec S))).hom _ = _
  rw [stalkMap_germ_transport (Spec.map φ) (genericPoint (Spec S)) ⊤ hgen trivial,
    Scheme.Hom.germ_stalkMap_apply]
  congr 1
  have hnat : (Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop = φ ≫ (Scheme.ΓSpecIso S).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  exact ConcreteCategory.congr_hom hnat r

end Stacks.Chow

/-! ### The transition between the two charts of the projective line -/

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- Mathlib's algebra structure on the function field of the punctured affine line, re-registered
at the spelling used here; compare
`AlgebraicGeometry.algebra_polynomial_affineLine_functionField`. -/
instance algebra_laurentPolynomial_functionField :
    Algebra (LaurentPolynomial k) ((Spec (.of (LaurentPolynomial k))).functionField) :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (LaurentPolynomial k))

/-- The second chart of the projective line is dominant. -/
instance projectiveLineYChart_isDominant : IsDominant (projectiveLineYChart k) :=
  Stacks.Chow.isDominant_of_isOpenImmersion' _

/-- The overlap of the two charts is dominant in the first chart. -/
instance projectiveLinePuncturedChart_isDominant : IsDominant (projectiveLinePuncturedChart k) :=
  Stacks.Chow.isDominant_of_isOpenImmersion' _

/-- The overlap of the two charts is dominant in the second chart. -/
instance projectiveLineOverlapYInclusion_isDominant :
    IsDominant (projectiveLineOverlapYInclusion k) :=
  Stacks.Chow.isDominant_of_isOpenImmersion' _

/-- The function field of the second chart, read on the overlap, sends a polynomial to the
corresponding Laurent polynomial in `T⁻¹`. -/
theorem dominantFunctionFieldMap_overlapYInclusion_algebraMap (a : Polynomial k) :
    dominantFunctionFieldMap (projectiveLineOverlapYInclusion k)
        (algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) a) =
      algebraMap (LaurentPolynomial k) ((Spec (.of (LaurentPolynomial k))).functionField)
        (projectiveLineOverlapInverseCoordinate k a) :=
  Stacks.Chow.dominantFunctionFieldMap_algebraMap_spec
    (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate k).toRingHom) a

/-- The function field of the first chart, read on the overlap, sends a polynomial to the
corresponding Laurent polynomial in `T`. -/
theorem dominantFunctionFieldMap_puncturedChart_algebraMap (a : Polynomial k) :
    dominantFunctionFieldMap (projectiveLinePuncturedChart k)
        (algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) a) =
      algebraMap (LaurentPolynomial k) ((Spec (.of (LaurentPolynomial k))).functionField)
        (Polynomial.toLaurent a) :=
  Stacks.Chow.dominantFunctionFieldMap_algebraMap_spec
    (CommRingCat.ofHom (Polynomial.toLaurent (R := k))) a

/-- **The two charts agree on the overlap.** The two routes from the function field of the
projective line to the function field of the overlap `Spec k[T, T⁻¹]` coincide, because the
square `AlgebraicGeometry.isPullback_projectiveLineCharts` commutes and
`AlgebraicGeometry.dominantFunctionFieldMap` is contravariantly functorial. -/
theorem dominantFunctionFieldMap_chart_overlap_eq (w : (projectiveLine k).functionField) :
    dominantFunctionFieldMap (projectiveLinePuncturedChart k)
        (dominantFunctionFieldMap (projectiveLineXChart k) w) =
      dominantFunctionFieldMap (projectiveLineOverlapYInclusion k)
        (dominantFunctionFieldMap (projectiveLineYChart k) w) := by
  have h := Stacks.Chow.dominantFunctionFieldMap_congr _ _ (isPullback_projectiveLineCharts k).w
  rw [Stacks.Chow.dominantFunctionFieldMap_comp, Stacks.Chow.dominantFunctionFieldMap_comp] at h
  exact RingHom.congr_fun h w

private theorem overlapYInclusion_functionField_injective :
    Function.Injective (dominantFunctionFieldMap (projectiveLineOverlapYInclusion k)) :=
  RingHom.injective _

/-- The second chart reads a constant rational function as the same constant. -/
theorem dominantFunctionFieldMap_yChart_C (c : k) (w : (projectiveLine k).functionField)
    (hw : dominantFunctionFieldMap (projectiveLineXChart k) w =
      algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) (Polynomial.C c)) :
    dominantFunctionFieldMap (projectiveLineYChart k) w =
      algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) (Polynomial.C c) := by
  refine overlapYInclusion_functionField_injective k ?_
  rw [dominantFunctionFieldMap_overlapYInclusion_algebraMap,
    ← dominantFunctionFieldMap_chart_overlap_eq, hw,
    dominantFunctionFieldMap_puncturedChart_algebraMap]
  congr 1
  simp [projectiveLineOverlapInverseCoordinate]

/-- **The transition inverts the coordinate.** The second chart reads the coordinate of the first
as its inverse, which is the substitution `x ↦ x⁻¹` gluing the two charts. -/
theorem dominantFunctionFieldMap_yChart_X (w : (projectiveLine k).functionField)
    (hw : dominantFunctionFieldMap (projectiveLineXChart k) w =
      algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) Polynomial.X) :
    dominantFunctionFieldMap (projectiveLineYChart k) w =
      (algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) Polynomial.X)⁻¹ := by
  refine overlapYInclusion_functionField_injective k ?_
  have hT : (algebraMap (LaurentPolynomial k) ((Spec (.of (LaurentPolynomial k))).functionField)
        (LaurentPolynomial.T (-1 : ℤ)))⁻¹ =
      algebraMap (LaurentPolynomial k) ((Spec (.of (LaurentPolynomial k))).functionField)
        (LaurentPolynomial.T (1 : ℤ)) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← map_mul, ← LaurentPolynomial.T_add]
    simp
  rw [map_inv₀, dominantFunctionFieldMap_overlapYInclusion_algebraMap,
    ← dominantFunctionFieldMap_chart_overlap_eq, hw,
    dominantFunctionFieldMap_puncturedChart_algebraMap,
    show projectiveLineOverlapInverseCoordinate k Polynomial.X = LaurentPolynomial.T (-1 : ℤ) by
      simp [projectiveLineOverlapInverseCoordinate],
    hT]
  congr 1
  simp

/-! ### The inversion on the rational function field -/

/-- The function field of the projective line, identified with that of the second chart. -/
def projectiveLineFunctionFieldEquivY :
    (projectiveLine k).functionField ≃+* (Spec (.of (Polynomial k))).functionField :=
  Stacks.Chow.functionFieldEquiv_openImmersion (projectiveLineYChart k)

/-- **The inversion gluing the two charts of the projective line**, read on `RatFunc k` through
the identification coming from the first chart: the automorphism sending a rational function to
the same function written in the coordinate of the second chart. -/
def projectiveLineChartInversion : RatFunc k ≃+* RatFunc k :=
  ((projectiveLineFunctionFieldEquiv k).symm.trans (projectiveLineFunctionFieldEquivY k)).trans
    (affineLineFunctionFieldEquiv k).toRingEquiv

/-- The inversion is the comparison of the two chart identifications of the function field. -/
theorem projectiveLineChartInversion_apply (g : (projectiveLine k).functionField) :
    projectiveLineChartInversion k (projectiveLineFunctionFieldEquiv k g) =
      affineLineFunctionFieldEquiv k (projectiveLineFunctionFieldEquivY k g) := by
  simp [projectiveLineChartInversion]

private theorem xChart_eq_of_equiv (a : Polynomial k) (w : (projectiveLine k).functionField)
    (hw : projectiveLineFunctionFieldEquiv k w = algebraMap (Polynomial k) (RatFunc k) a) :
    dominantFunctionFieldMap (projectiveLineXChart k) w =
      algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) a := by
  refine (affineLineFunctionFieldEquiv k).injective ?_
  rwa [AlgEquiv.commutes]

private theorem chartInversion_algebraMap_eq (a : Polynomial k)
    (y : (Spec (.of (Polynomial k))).functionField)
    (h : ∀ w : (projectiveLine k).functionField,
      dominantFunctionFieldMap (projectiveLineXChart k) w =
        algebraMap (Polynomial k) ((Spec (.of (Polynomial k))).functionField) a →
      dominantFunctionFieldMap (projectiveLineYChart k) w = y) :
    projectiveLineChartInversion k (algebraMap (Polynomial k) (RatFunc k) a) =
      affineLineFunctionFieldEquiv k y := by
  obtain ⟨w, hw⟩ := (projectiveLineFunctionFieldEquiv k).surjective
    (algebraMap (Polynomial k) (RatFunc k) a)
  rw [← hw, projectiveLineChartInversion_apply, ← h w (xChart_eq_of_equiv k a w hw)]
  rfl

/-- The inversion fixes the constants. -/
theorem projectiveLineChartInversion_C (c : k) :
    projectiveLineChartInversion k (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c)) =
      algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c) := by
  rw [chartInversion_algebraMap_eq k _ _ (dominantFunctionFieldMap_yChart_C k c),
    AlgEquiv.commutes]

/-- The inversion sends the coordinate to its inverse. -/
theorem projectiveLineChartInversion_X :
    projectiveLineChartInversion k (algebraMap (Polynomial k) (RatFunc k) Polynomial.X) =
      (algebraMap (Polynomial k) (RatFunc k) Polynomial.X)⁻¹ := by
  rw [chartInversion_algebraMap_eq k _ _ (dominantFunctionFieldMap_yChart_X k), map_inv₀,
    AlgEquiv.commutes]

/-! ### The point at infinity -/

/-- **The residue degree at the point at infinity is one.** Infinity is the origin of the second
chart, cut out by the polynomial `X` of degree one. -/
theorem residueDegree_projectiveLine_infinity :
    (projectiveLine k ↘ Spec (.of k)).residueDegree (projectiveLineInfinity k) = 1 := by
  rw [projectiveLineInfinity,
    ← Stacks.Chow.residueDegree_isOpenImmersion_comp (projectiveLineYChart k)
      (projectiveLine k ↘ Spec (.of k)) (affineLineOrigin k),
    projectiveLineYChart_comp_structureMorphism,
    residueDegree_projectiveLineAffineStructureMorphism_eq_natDegree k Polynomial.irreducible_X
      (affineLineOrigin k) rfl]
  simp

/-- **The order of vanishing at the point at infinity of the projective line** is
`Stacks.Chow.ordAtInfty`, minus the integer degree of the rational function.

Infinity is the origin of the second chart, so the order there is the order at the closed point
`(X)` of the affine line of the function written in the coordinate of the second chart; and that
coordinate is the inverse of the coordinate of the first chart, by
`AlgebraicGeometry.projectiveLineChartInversion_X`. -/
theorem ord_projectiveLine_infinity (g : (projectiveLine k).functionField) :
    (projectiveLine k).ord g (projectiveLineInfinity k) =
      Stacks.Chow.ordAtInfty (projectiveLineFunctionFieldEquiv k g) := by
  classical
  rw [projectiveLineInfinity,
    ← Stacks.Chow.ord_dominantFunctionFieldMap_of_isOpenImmersion (projectiveLineYChart k) g
      (affineLineOrigin k),
    ord_spec_polynomial_eq_ordAt k Polynomial.irreducible_X Polynomial.monic_X
      (affineLineOrigin k) rfl,
    show (affineLineFunctionFieldEquiv k
          (dominantFunctionFieldMap (projectiveLineYChart k) g) : RatFunc k) =
        projectiveLineChartInversion k (projectiveLineFunctionFieldEquiv k g) from
      (projectiveLineChartInversion_apply k g).symm]
  exact Stacks.Chow.ordAt_X_map_eq_ordAtInfty (projectiveLineChartInversion k).toRingHom
    (projectiveLineChartInversion_C k) (projectiveLineChartInversion_X k) _

end AlgebraicGeometry

end

end
