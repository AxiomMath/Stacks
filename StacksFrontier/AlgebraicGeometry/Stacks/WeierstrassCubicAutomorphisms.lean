module

public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicIsoAction
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicIso

/-!
# Isomorphisms of plane Weierstrass cubics are coordinate changes

Let `C` and `C'` be Weierstrass equations over a commutative ring `R`, with no condition on their
discriminants, and let `E_C`, `E_{C'}` be their plane cubics, pointed by `(0 : 1 : 0)`, over
`Spec R`. A coordinate change `γ = (u, r, s, t)` with `γ • C = C'` induces an isomorphism of
pointed families `changeIso γ C : E_{γ • C} ≅ E_C`. This file proves the converse, the
mathematical heart of the torsor property of Tag 072T: every isomorphism of the pointed families
`E_{C'} ≅ E_C` over `Spec R` is induced by a unique coordinate change.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.exists_unique_variableChange`: for every
  isomorphism `α : E_{C'} ≅ E_C` of pointed families over `Spec R` there is a unique `γ` with
  `γ • C = C'` whose isomorphism `changeIso γ C` is `α` on total spaces.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.exists_variableChange` and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.variableChange_eq_of_changeIso_eq`: the
  existence and the uniqueness separately, with the equation written `C' = γ • C`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.eq_of_comp_chartZ_eq`: a morphism out of a
  plane cubic is determined by its restriction to the chart `D₊(z)` and to the zero section.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.eq_of_affineChartHom_mk_cubicOf_eq_zero`:
  a Weierstrass equation is determined by its affine coordinate ring.

## Implementation notes

An isomorphism `α` preserving the zero sections acts on the charts `D₊(z)` by `x ↦ u²x + r`,
`y ↦ u³y + u²sx + t` (`WeierstrassCubicIsoAction.lean`). Applying it to the equation of `C`
gives `u⁶` times the equation of `γ • C` at the coordinates of `C'`, and since the equation of `C'`
vanishes there and `1, y` is a basis of `R[x, y]/(f_{C'})` over `R[x]`, `γ • C = C'`. Then `α` and
`changeIso γ C` agree on `D₊(z)` and on the zero section, hence everywhere: an endomorphism of a
plane cubic which is the identity there is the identity on points, so it preserves the chart
`D₊(y)`, where it is a ring endomorphism which becomes the identity after inverting `Z`, and `Z`
is a nonzerodivisor because the chart is free over `R[Z]`. No separatedness or reducedness is
used. The coordinate change is unique because it is read off from the action on `x` and `y`.

## References

* [Stacks Project, Tag 072T](https://stacks.math.columbia.edu/tag/072T)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {W W' : WeierstrassCurve R}

/-! ### Coefficients in the affine coordinate ring -/

/-- In `R[x, y]/(f)`, regarded as an `R[x]`-module, `p • 1 + q • y = p(x) + q(x) y`. -/
theorem smul_basis_eq_eval₂ (W : WeierstrassCurve R) (p q : Polynomial R) :
    p • (1 : W.toAffine.CoordinateRing) + q • WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
      Polynomial.X =
        p.eval₂ (algebraMap R _) (affX W) + q.eval₂ (algebraMap R _) (affX W) * affY W := by
  change _ + q • affY W = _
  rw [← smul_one_mul q, smul_one_eq_eval₂, smul_one_eq_eval₂]

/-- The coefficients of `r + s x + t y` in `R[x, y]/(f)` are determined by it. -/
theorem eq_of_add_mul_add_mul_eq (W : WeierstrassCurve R) {r s t r' s' t' : R}
    (h : algebraMap R _ r + algebraMap R _ s * affX W + algebraMap R _ t * affY W =
      algebraMap R W.toAffine.CoordinateRing r' + algebraMap R _ s' * affX W +
        algebraMap R _ t' * affY W) : r = r' ∧ s = s' ∧ t = t' := by
  have h0 := smul_basis_eq_eval₂ W (Polynomial.C (r - r') + Polynomial.C (s - s') * Polynomial.X)
    (Polynomial.C (t - t'))
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
    at h0
  obtain ⟨hp, hq⟩ := WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero
    (h0.trans (by
      linear_combination h + map_sub (algebraMap R W.toAffine.CoordinateRing) r r' +
        affX W * map_sub (algebraMap R W.toAffine.CoordinateRing) s s' +
        affY W * map_sub (algebraMap R W.toAffine.CoordinateRing) t t'))
  have h1 := congrArg (Polynomial.coeff · 0) hp
  have h2 := congrArg (Polynomial.coeff · 1) hp
  have h3 := congrArg (Polynomial.coeff · 0) hq
  simp only [Polynomial.coeff_add, Polynomial.coeff_C,
    Polynomial.coeff_zero, Polynomial.coeff_C_mul, Polynomial.coeff_X] at h1 h2 h3
  norm_num at h1 h2 h3
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2, sub_eq_zero.mp h3⟩

/-- The equation of `W` vanishes in the coordinate ring of its plane cubic. -/
private theorem mk_cubicOf_self (W : WeierstrassCurve R) :
    Ideal.Quotient.mk (cubicIdealOf W).toIdeal (cubicOf W) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

/-- The Weierstrass equation of `V`, evaluated at the affine coordinates of `W`. -/
theorem affineChartHom_mk_cubicOf (W V : WeierstrassCurve R) :
    affineChartHom W (Ideal.Quotient.mk _ (cubicOf V)) =
      affY W ^ 2 + algebraMap R _ V.a₁ * affX W * affY W + algebraMap R _ V.a₃ * affY W -
        (affX W ^ 3 + algebraMap R _ V.a₂ * affX W ^ 2 + algebraMap R _ V.a₄ * affX W +
          algebraMap R _ V.a₆) := by
  simp only [affineChartHom, coordLift_mk, cubicOf, WeierstrassCurve.Projective.polynomial,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, Matrix.cons_val, affX, affY,
    AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  simp only [WeierstrassCurve.toProjective]
  ring

/-- **The Weierstrass equation is determined by its affine coordinate ring.** If the equation of
`V` holds at the affine coordinates of `W`, then `V = W`. -/
theorem eq_of_affineChartHom_mk_cubicOf_eq_zero {W V : WeierstrassCurve R}
    (h : affineChartHom W (Ideal.Quotient.mk _ (cubicOf V)) = 0) : V = W := by
  have hW : affineChartHom W (Ideal.Quotient.mk _ (cubicOf W)) = 0 := by
    rw [mk_cubicOf_self, map_zero]
  rw [affineChartHom_mk_cubicOf] at h hW
  have h0 := smul_basis_eq_eval₂ W
    (-(Polynomial.C (V.a₂ - W.a₂) * Polynomial.X ^ 2 + Polynomial.C (V.a₄ - W.a₄) * Polynomial.X +
      Polynomial.C (V.a₆ - W.a₆)))
    (Polynomial.C (V.a₁ - W.a₁) * Polynomial.X + Polynomial.C (V.a₃ - W.a₃))
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_neg, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X] at h0
  obtain ⟨hp, hq⟩ := WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero
    (h0.trans (by
      linear_combination h - hW -
        affX W ^ 2 * map_sub (algebraMap R W.toAffine.CoordinateRing) V.a₂ W.a₂ -
        affX W * map_sub (algebraMap R W.toAffine.CoordinateRing) V.a₄ W.a₄ -
        map_sub (algebraMap R W.toAffine.CoordinateRing) V.a₆ W.a₆ +
        affX W * affY W * map_sub (algebraMap R W.toAffine.CoordinateRing) V.a₁ W.a₁ +
        affY W * map_sub (algebraMap R W.toAffine.CoordinateRing) V.a₃ W.a₃))
  have e1 := congrArg (Polynomial.coeff · 1) hq
  have e3 := congrArg (Polynomial.coeff · 0) hq
  have e2 := congrArg (Polynomial.coeff · 2) hp
  have e4 := congrArg (Polynomial.coeff · 1) hp
  have e6 := congrArg (Polynomial.coeff · 0) hp
  simp only [Polynomial.coeff_neg, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_zero] at e1 e2 e3 e4 e6
  norm_num at e1 e2 e3 e4 e6
  ext
  · linear_combination e1
  · linear_combination -e2
  · linear_combination e3
  · linear_combination -e4
  · linear_combination -e6

/-! ### Points with `z = 1` through the chart `D₊(z)` -/

/-- The inverse of `chartZEquiv W` sends `a` to `b` if the lift of `affineChartHom W` sends `b`
to `a`. -/
private theorem chartZEquiv_symm_eq (W : WeierstrassCurve R) {a b}
    (h : awayLiftOf W (affineChartHom W) 2 (affineChartHom_coordOf_two W) b = a) :
    (chartZEquiv W).symm a = b :=
  (RingEquiv.symm_apply_eq _).2 h.symm

/-- The inverse of `chartZEquiv W` sends `x` to the coordinate `x/z` of the chart `D₊(z)`. -/
theorem chartZEquiv_symm_affX (W : WeierstrassCurve R) :
    (chartZEquiv W).symm (affX W) = awayCoord W 2 0 :=
  chartZEquiv_symm_eq W (by rw [awayLiftOf_awayCoord]; simp [affineChartHom, coordLift_mk])

/-- The inverse of `chartZEquiv W` sends `y` to the coordinate `y/z` of the chart `D₊(z)`. -/
theorem chartZEquiv_symm_affY (W : WeierstrassCurve R) :
    (chartZEquiv W).symm (affY W) = awayCoord W 2 1 :=
  chartZEquiv_symm_eq W (by rw [awayLiftOf_awayCoord]; simp [affineChartHom, coordLift_mk])

/-- The inverse of `chartZEquiv W` sends a constant `a : R` to the constant `a`. -/
theorem chartZEquiv_symm_algebraMap (W : WeierstrassCurve R) (a : R) :
    (chartZEquiv W).symm (algebraMap R _ a) = awayConst W 2 a :=
  chartZEquiv_symm_eq W (by
    rw [awayLiftOf_awayConst]
    simp [affineChartHom, coordLift_mk, algebraMap_coordinateRing])

/-- The homomorphism `R[x, y]/(f) → S` of a homomorphism `κ` out of `R[x, y, z]/(F)` with
`κ z = 1`: `x ↦ κ x`, `y ↦ κ y`. -/
def chartZLift {S : Type*} [CommRing S] (κ : coordRingOf W →+* S) (h : κ (coordOf W 2) = 1) :
    W.toAffine.CoordinateRing →+* S :=
  (awayLiftOf W κ 2 h).comp (chartZEquiv W).symm.toRingHom

/-- `chartZLift κ h` sends `x` to `κ x`. -/
theorem chartZLift_affX {S : Type*} [CommRing S] (κ : coordRingOf W →+* S) (h) :
    chartZLift κ h (affX W) = κ (coordOf W 0) := by
  simp [chartZLift, chartZEquiv_symm_affX, awayLiftOf_awayCoord]

/-- `chartZLift κ h` sends `y` to `κ y`. -/
theorem chartZLift_affY {S : Type*} [CommRing S] (κ : coordRingOf W →+* S) (h) :
    chartZLift κ h (affY W) = κ (coordOf W 1) := by
  simp [chartZLift, chartZEquiv_symm_affY, awayLiftOf_awayCoord]

/-- `chartZLift κ h` sends a constant `a : R` to `κ a`. -/
theorem chartZLift_algebraMap {S : Type*} [CommRing S] (κ : coordRingOf W →+* S) (h) (a : R) :
    chartZLift κ h (algebraMap R _ a) = κ (algebraMap R _ a) := by
  simp [chartZLift, chartZEquiv_symm_algebraMap, awayLiftOf_awayConst, algebraMap_coordRingOf]

/-- The point of the plane cubic given by `κ` with `κ z = 1` factors through the chart `D₊(z)`
as the spectrum of `chartZLift κ h`. -/
theorem SpecMap_chartZLift {S : Type u} [CommRing S] (κ : coordRingOf W →+* S) (h) (hκ) :
    Spec.map (CommRingCat.ofHom (chartZLift κ h)) ≫ chartZ W = specPoint W κ hκ := by
  rw [chartZ_eq_awayι, ← Category.assoc, ← Spec.map_comp, specPoint_eq_awayι W κ 2 h]
  congr 2
  ext b
  simp [chartZLift]

/-! ### The chart `D₊(z)` of a coordinate change -/

/-- The chart `D₊(z)` of `E_{γ • W}` followed by `changeMap γ W` is the point of `E_W` given by
the coordinate change `γ` on homogeneous coordinates followed by dehomogenization at `z`. -/
theorem chartZ_comp_changeMap (γ : WeierstrassCurve.VariableChange R) (W : WeierstrassCurve R) :
    chartZ (γ • W) ≫ changeMap γ W = specPoint W ((affineChartHom (γ • W)).comp
      (changeHom γ W).toRingHom) (by
        rw [← Ideal.map_map]
        refine top_unique ((map_irrelevant_eq_top_of_isUnit (γ • W) _ 2
          (by rw [affineChartHom_coordOf_two]; exact isUnit_one)).symm.le.trans
          (Ideal.map_mono ?_))
        exact irrelevant_le_map_changeHom γ W) := by
  refine (Proj.fromOfGlobalSections_comp_map _ _ _ _ ?_).trans
    (Proj.fromOfGlobalSections_congr (RingHom.comp_assoc _ _ _) _ _)
  rw [← Ideal.map_map, ← Ideal.map_map]
  refine top_unique ?_
  rw [← Ideal.map_top (Scheme.ΓSpecIso (CommRingCat.of (γ • W).toAffine.CoordinateRing)).inv.hom,
    ← map_irrelevant_eq_top_of_isUnit (γ • W) (affineChartHom (γ • W)) 2
      (by rw [affineChartHom_coordOf_two]; exact isUnit_one)]
  exact Ideal.map_mono (Ideal.map_mono (irrelevant_le_map_changeHom γ W))

/-! ### Morphisms out of a plane cubic are determined on `D₊(z)` and the zero section -/

/-- `Z` is a nonzerodivisor in the coordinate ring of the chart `D₊(y)`, which is free over
`R[Z]`. -/
theorem chartYZ_mem_nonZeroDivisors (W : WeierstrassCurve R) :
    chartYZ W ∈ nonZeroDivisors (ChartYRing W) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  have hX : (Polynomial.X : Polynomial R) • y = 0 := by
    rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq, mul_comm]
    exact hy
  have h := congrArg (chartYPowerBasis W).basis.repr hX
  rw [map_smul, map_zero] at h
  have h0 : (chartYPowerBasis W).basis.repr y = 0 := by
    refine Finsupp.ext fun i => ?_
    have hi := congrArg (· i) h
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at hi
    exact (mem_nonZeroDivisors_iff_left.mp Polynomial.X_mem_nonZeroDivisors) _ hi
  exact (chartYPowerBasis W).basis.repr.map_eq_zero_iff.mp h0

/-- **An endomorphism of the plane cubic which is the identity on the chart `D₊(z)` and on the
zero section is the identity.** On points it is the identity, since the zero section is the
complement of `D₊(z)`; so it preserves the chart `D₊(y)`, where it is given by a ring
endomorphism which is the identity after inverting `Z`, hence the identity because `Z` is a
nonzerodivisor. -/
theorem eq_id_of_comp_chartZ (W : WeierstrassCurve R) (δ : projOf W ⟶ projOf W)
    (h1 : chartZ W ≫ δ = chartZ W) (h2 : zeroOf W ≫ δ = zeroOf W) : δ = 𝟙 _ := by
  have hpt : ∀ p, δ p = p := by
    intro p
    by_cases hp : p ∈ basicOpenOf W (coordOf W 2)
    · rw [← opensRange_chartZ] at hp
      obtain ⟨q, rfl⟩ := hp
      rw [← Scheme.Hom.comp_apply, h1]
    · obtain ⟨r, rfl⟩ : p ∈ Set.range (zeroOf W) := by
        rw [range_zeroOf]
        exact hp
      rw [← Scheme.Hom.comp_apply, h2]
  have hrange : Set.range (chartY W ≫ δ) ⊆ Set.range (chartY W) := by
    rintro _ ⟨q, rfl⟩
    exact ⟨q, by rw [Scheme.Hom.comp_apply, hpt]⟩
  let η := (Spec.preimage (IsOpenImmersion.lift (chartY W) (chartY W ≫ δ) hrange)).hom
  have hη : Spec.map (CommRingCat.ofHom η) ≫ chartY W = chartY W ≫ δ := by
    simp only [η, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  let L := Localization.Away (chartYZ W)
  have hv : algebraMap _ L (chartYZ W) * IsLocalization.Away.invSelf (chartYZ W) = 1 :=
    IsLocalization.Away.mul_invSelf _
  have hloc : (algebraMap _ L).comp η = algebraMap _ L := by
    apply ringHom_ext_of_SpecMap_chartY
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hη, ← Category.assoc,
      ← SpecMap_chartZOfChartY_chartZ W (algebraMap _ L) _ hv, Category.assoc, h1,
      SpecMap_chartZOfChartY_chartZ]
  have hinj : Function.Injective (algebraMap (ChartYRing W) L) :=
    IsLocalization.injective L (Submonoid.powers_le.mpr (chartYZ_mem_nonZeroDivisors W))
  have hη1 : η = RingHom.id _ := RingHom.ext fun b => hinj (congr($hloc b))
  have hY : chartY W ≫ δ = chartY W := by
    rw [← hη, hη1]
    simp
  let U : Fin 2 → (projOf W).Opens := ![(chartZ W).opensRange, (chartY W).opensRange]
  have hU : TopologicalSpace.IsOpenCover U := by
    refine eq_top_iff.mpr fun p _ => ?_
    have hcov : p ∈ basicOpenOf W (coordOf W 2) ⊔ basicOpenOf W (coordOf W 1) := by
      rw [basicOpenOf_two_sup_basicOpenOf_one]
      trivial
    rw [TopologicalSpace.Opens.mem_iSup]
    rcases hcov with h | h
    · exact ⟨0, by change p ∈ (chartZ W).opensRange; rw [opensRange_chartZ]; exact h⟩
    · exact ⟨1, by change p ∈ (chartY W).opensRange; rw [opensRange_chartY]; exact h⟩
  have key {Y : Scheme.{u}} (f : Y ⟶ projOf W) [IsOpenImmersion f] (h : f ≫ δ = f) :
      f.opensRange.ι ≫ δ = f.opensRange.ι ≫ 𝟙 _ := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, h, Category.comp_id]
  refine Scheme.Cover.hom_ext ((projOf W).openCoverOfIsOpenCover U hU) _ _ fun (i : Fin 2) => ?_
  fin_cases i
  exacts [key _ h1, key _ hY]

/-- Two morphisms out of a plane cubic, the second an isomorphism, which agree on the chart
`D₊(z)` and on the zero section are equal. -/
theorem eq_of_comp_chartZ_eq {X : Scheme.{u}} (F G : projOf W' ⟶ X) [IsIso G]
    (h1 : chartZ W' ≫ F = chartZ W' ≫ G) (h2 : zeroOf W' ≫ F = zeroOf W' ≫ G) : F = G := by
  have key {Y : Scheme.{u}} (A : Y ⟶ projOf W') (h : A ≫ F = A ≫ G) : A ≫ F ≫ inv G = A := by
    rw [← Category.assoc, h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have h := eq_id_of_comp_chartZ W' (F ≫ inv G) (key _ h1) (key _ h2)
  exact (cancel_mono (inv G)).mp (h.trans (IsIso.hom_inv_id G).symm)

/-! ### Isomorphisms of plane cubics are coordinate changes -/

/-- The coordinate change `γ` on homogeneous coordinates, followed by dehomogenization at `z` on
`E_{γ • W}`: `x ↦ u²x + r`, `y ↦ u³y + u²sx + t`, `z ↦ 1`. -/
abbrev changeChartHom (γ : WeierstrassCurve.VariableChange R) (W : WeierstrassCurve R) :
    coordRingOf W →+* (γ • W).toAffine.CoordinateRing :=
  (affineChartHom (γ • W)).comp (changeHom γ W).toRingHom

/-- The graded substitution of `γ` agrees with the substitution `substOf γ` on polynomials. -/
theorem substGradedHom_apply_eq (γ : WeierstrassCurve.VariableChange R)
    (p : MvPolynomial (Fin 3) R) : substGradedHom γ p = substOf γ p := rfl

/-- `affineChartHom W` sends a constant `a : R` to the constant `a`. -/
private theorem affineChartHom_algebraMap (W : WeierstrassCurve R) (a : R) :
    affineChartHom W (algebraMap R _ a) = algebraMap R _ a := by
  simp [algebraMap_coordRingOf, affineChartHom, coordLift_mk]

/-- `changeChartHom γ W` sends a constant `a : R` to the constant `a`. -/
theorem changeChartHom_algebraMap (γ : WeierstrassCurve.VariableChange R)
    (W : WeierstrassCurve R) (a : R) :
    changeChartHom γ W (algebraMap R _ a) = algebraMap R _ a := by
  rw [algebraMap_coordRingOf]
  simp only [changeChartHom, RingHom.comp_apply, changeHom, GradedRingHom.coe_toRingHom,
    coordHom_mk, substGradedHom_apply_eq]
  rw [show substOf γ (MvPolynomial.C a) = MvPolynomial.C a from (substOf γ).commutes a,
    ← algebraMap_coordRingOf, affineChartHom_algebraMap]

/-- `changeChartHom γ W` sends `z` to `1`. -/
theorem changeChartHom_coordOf_two (γ : WeierstrassCurve.VariableChange R)
    (W : WeierstrassCurve R) : changeChartHom γ W (coordOf W 2) = 1 := by
  simp [changeChartHom, changeHom, coordHom_mk, substGradedHom_apply_eq, substOf, affineChartHom,
    coordLift_mk]

/-- `changeChartHom γ W` sends `x` to `u²x + r`. -/
theorem changeChartHom_coordOf_zero (γ : WeierstrassCurve.VariableChange R)
    (W : WeierstrassCurve R) : changeChartHom γ W (coordOf W 0) =
      algebraMap R _ ((γ.u : R) ^ 2) * affX (γ • W) + algebraMap R _ γ.r := by
  simp [changeChartHom, changeHom, coordHom_mk, substGradedHom_apply_eq, substOf, affineChartHom,
    coordLift_mk, algebraMap_coordinateRing, affX]

/-- `changeChartHom γ W` sends `y` to `u³y + u²sx + t`. -/
theorem changeChartHom_coordOf_one (γ : WeierstrassCurve.VariableChange R)
    (W : WeierstrassCurve R) : changeChartHom γ W (coordOf W 1) =
      algebraMap R _ ((γ.u : R) ^ 3) * affY (γ • W) +
        algebraMap R _ ((γ.u : R) ^ 2 * γ.s) * affX (γ • W) + algebraMap R _ γ.t := by
  simp [changeChartHom, changeHom, coordHom_mk, substGradedHom_apply_eq, substOf, affineChartHom,
    coordLift_mk, algebraMap_coordinateRing, affX, affY]

/-- On the charts `D₊(z)`, the isomorphism of plane cubics induced by a coordinate change is the
affine substitution `x ↦ u²x + r`, `y ↦ u³y + u²sx + t`. -/
theorem zChartHom_changeMap (γ : WeierstrassCurve.VariableChange R) (W : WeierstrassCurve R)
    (hz : zeroOf (γ • W) ≫ changeMap γ W = zeroOf W) :
    zChartHom (changeMap γ W) hz =
      chartZLift (changeChartHom γ W) (changeChartHom_coordOf_two γ W) :=
  zChartHom_eq _ hz (by rw [SpecMap_chartZLift, chartZ_comp_changeMap])

/-- **The coordinate change read off from an isomorphism.** If `F = eqToHom ≫ changeMap γ W`,
then on the charts `D₊(z)` it is `x ↦ u²x + r`, `y ↦ u³y + u²sx + t`. -/
theorem zChartHom_of_eq_changeMap (γ : WeierstrassCurve.VariableChange R) (h : γ • W = W')
    (F : projOf W' ⟶ projOf W) [IsIso F] (hz : zeroOf W' ≫ F = zeroOf W)
    (hF : F = eqToHom (congrArg projOf h.symm) ≫ changeMap γ W) :
    zChartHom F hz (affX W) = algebraMap R _ ((γ.u : R) ^ 2) * affX W' + algebraMap R _ γ.r ∧
      zChartHom F hz (affY W) = algebraMap R _ ((γ.u : R) ^ 3) * affY W' +
        algebraMap R _ ((γ.u : R) ^ 2 * γ.s) * affX W' + algebraMap R _ γ.t := by
  subst h
  rw [eqToHom_refl, Category.id_comp] at hF
  subst hF
  rw [zChartHom_changeMap, chartZLift_affX, chartZLift_affY, changeChartHom_coordOf_zero,
    changeChartHom_coordOf_one]
  exact ⟨rfl, rfl⟩

section Iso

variable (F : projOf W' ⟶ projOf W) [IsIso F] (hz : zeroOf W' ≫ F = zeroOf W)
  (hF : F ≫ projectionOf W = projectionOf W')

include hF in
/-- An isomorphism `F : E_{W'} ≅ E_W` over `Spec R` preserving the zero sections acts on the
charts `D₊(z)` by `x ↦ u²x + r`, `y ↦ u³y + u²sx + t` for some coordinate change
`(u, r, s, t)`. -/
theorem exists_variableChange_zChartHom : ∃ γ : WeierstrassCurve.VariableChange R,
    zChartHom F hz (affX W) = algebraMap R _ ((γ.u : R) ^ 2) * affX W' + algebraMap R _ γ.r ∧
      zChartHom F hz (affY W) = algebraMap R _ ((γ.u : R) ^ 3) * affY W' +
        algebraMap R _ ((γ.u : R) ^ 2 * γ.s) * affX W' + algebraMap R _ γ.t := by
  obtain ⟨r, hr⟩ := exists_zChartHom_affX F hz hF
  obtain ⟨t, s', hs⟩ := exists_zChartHom_affY F hz hF
  set u := tangentInv F hz hF
  have hu : (u : R) ^ 2 * ((u⁻¹ : Rˣ) : R) ^ 2 = 1 := by rw [← mul_pow, Units.mul_inv, one_pow]
  refine ⟨⟨u, r, ((u⁻¹ : Rˣ) : R) ^ 2 * s', t⟩, ?_, ?_⟩
  · rw [hr]
    ring
  · rw [hs]
    simp only
    rw [show (u : R) ^ 2 * (((u⁻¹ : Rˣ) : R) ^ 2 * s') = s' by linear_combination s' * hu]
    ring

include hF in
/-- **An isomorphism preserving the zero sections acts on `D₊(z)` by a coordinate change `γ`, and
then `γ • W = W'`.** -/
theorem smul_eq_of_zChartHom (γ : WeierstrassCurve.VariableChange R)
    (hx : zChartHom F hz (affX W) = algebraMap R _ ((γ.u : R) ^ 2) * affX W' + algebraMap R _ γ.r)
    (hy : zChartHom F hz (affY W) = algebraMap R _ ((γ.u : R) ^ 3) * affY W' +
      algebraMap R _ ((γ.u : R) ^ 2 * γ.s) * affX W' + algebraMap R _ γ.t) :
    γ • W = W' := by
  have hcomp : ((zChartHom F hz).comp (affineChartHom W)).comp (Ideal.Quotient.mk _) =
      ((affineChartHom W').comp (Ideal.Quotient.mk _)).comp (substOf γ).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun i => ?_
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [show substOf γ (MvPolynomial.C a) = MvPolynomial.C a from (substOf γ).commutes a,
        ← algebraMap_coordRingOf, ← algebraMap_coordRingOf, affineChartHom_algebraMap,
        affineChartHom_algebraMap, zChartHom_algebraMap F hz hF]
    · fin_cases i
      · simp only [RingHom.comp_apply]
        change zChartHom F hz (affineChartHom W (coordOf W 0)) = _
        rw [show affineChartHom W (coordOf W 0) = affX W by simp [affineChartHom, coordLift_mk],
          hx]
        simp [substOf, affineChartHom, coordLift_mk, algebraMap_coordinateRing, affX]
      · simp only [RingHom.comp_apply]
        change zChartHom F hz (affineChartHom W (coordOf W 1)) = _
        rw [show affineChartHom W (coordOf W 1) = affY W by simp [affineChartHom, coordLift_mk],
          hy]
        simp [substOf, affineChartHom, coordLift_mk, algebraMap_coordinateRing, affX, affY]
      · simp only [RingHom.comp_apply]
        change zChartHom F hz (affineChartHom W (coordOf W 2)) = _
        rw [affineChartHom_coordOf_two, map_one]
        simp [substOf, affineChartHom, coordLift_mk]
  have h := congr($hcomp (cubicOf W))
  simp only [RingHom.comp_apply, mk_cubicOf_self, map_zero, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, substOf_cubicOf, map_mul] at h
  apply eq_of_affineChartHom_mk_cubicOf_eq_zero
  have hu : IsUnit (affineChartHom W' (Ideal.Quotient.mk _ (MvPolynomial.C ((γ.u : R) ^ 6)))) := by
    rw [← algebraMap_coordRingOf]
    simp only [affineChartHom, coordLift_mk, algebraMap_coordRingOf, MvPolynomial.eval₂_C]
    exact (γ.u.isUnit.pow 6).map _
  exact (hu.mul_right_eq_zero).mp h.symm

end Iso

/-- The coordinate change determined by an isomorphism of plane cubics is unique. -/
theorem variableChange_unique {γ₁ γ₂ : WeierstrassCurve.VariableChange R} (h₁ : γ₁ • W = W')
    (h₂ : γ₂ • W = W') (F : projOf W' ⟶ projOf W) [IsIso F] (hz : zeroOf W' ≫ F = zeroOf W)
    (hF₁ : F = eqToHom (congrArg projOf h₁.symm) ≫ changeMap γ₁ W)
    (hF₂ : F = eqToHom (congrArg projOf h₂.symm) ≫ changeMap γ₂ W) : γ₁ = γ₂ := by
  obtain ⟨hx₁, hy₁⟩ := zChartHom_of_eq_changeMap γ₁ h₁ F hz hF₁
  obtain ⟨hx₂, hy₂⟩ := zChartHom_of_eq_changeMap γ₂ h₂ F hz hF₂
  obtain ⟨er, eu2, -⟩ := eq_of_add_mul_add_mul_eq W' (r := γ₁.r) (s := (γ₁.u : R) ^ 2) (t := 0)
    (r' := γ₂.r) (s' := (γ₂.u : R) ^ 2) (t' := 0) (by
      rw [map_zero, zero_mul, add_zero, add_zero]
      linear_combination hx₂ - hx₁)
  obtain ⟨et, es, eu3⟩ := eq_of_add_mul_add_mul_eq W' (r := γ₁.t) (s := (γ₁.u : R) ^ 2 * γ₁.s)
    (t := (γ₁.u : R) ^ 3) (r' := γ₂.t) (s' := (γ₂.u : R) ^ 2 * γ₂.s) (t' := (γ₂.u : R) ^ 3)
    (by linear_combination hy₂ - hy₁)
  have hu : γ₁.u = γ₂.u := by
    have e2 : γ₁.u ^ 2 = γ₂.u ^ 2 := Units.ext (by exact_mod_cast eu2)
    have e3 : γ₁.u ^ 3 = γ₂.u ^ 3 := Units.ext (by exact_mod_cast eu3)
    calc γ₁.u = γ₁.u ^ 3 * (γ₁.u ^ 2)⁻¹ := by group
      _ = γ₂.u ^ 3 * (γ₂.u ^ 2)⁻¹ := by rw [e2, e3]
      _ = γ₂.u := by group
  have hs : γ₁.s = γ₂.s := by
    rw [hu] at es
    exact ((γ₂.u.isUnit.pow 2).mul_left_cancel) es
  exact WeierstrassCurve.VariableChange.ext hu er hs et

/-- **Isomorphisms of plane Weierstrass cubics are coordinate changes.** For Weierstrass
equations `C` and `C'` over any commutative ring `R`, every isomorphism `α` of the pointed
families `(E_{C'}, f, (0 : 1 : 0)) ≅ (E_C, f, (0 : 1 : 0))` over `Spec R` is induced by a unique
coordinate change `γ` with `γ • C = C'`: its morphism of total spaces is `changeIso γ C`,
preceded by the identification `E_{C'} = E_{γ • C}`. -/
theorem exists_unique_variableChange (C C' : WeierstrassCurve R)
    (α : FamilyIso (familyOf C') (familyOf C)) :
    ∃! γ : WeierstrassCurve.VariableChange R, ∃ h : γ • C = C',
      α.iso.hom = eqToHom (congrArg projOf h.symm) ≫ (changeIso γ C).iso.hom := by
  let F : projOf C' ⟶ projOf C := α.iso.hom
  have : IsIso F := α.iso.isIso_hom
  have hz : zeroOf C' ≫ F = zeroOf C := α.zero_iso
  have hF : F ≫ projectionOf C = projectionOf C' := α.iso_map
  obtain ⟨γ, hx, hy⟩ := exists_variableChange_zChartHom F hz hF
  have hγ := smul_eq_of_zChartHom F hz hF γ hx hy
  have hex : F = eqToHom (congrArg projOf hγ.symm) ≫ changeMap γ C := by
    clear_value F
    subst hγ
    rw [eqToHom_refl, Category.id_comp]
    refine eq_of_comp_chartZ_eq F (changeMap γ C) ?_ ?_
    · rw [← SpecMap_zChartHom F hz, chartZ_comp_changeMap, ← SpecMap_chartZLift
        (changeChartHom γ C) (changeChartHom_coordOf_two γ C)]
      congr 3
      refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun a => ?_) ?_) ?_
      · change zChartHom F hz (algebraMap R _ a) =
          chartZLift _ (changeChartHom_coordOf_two γ C) (algebraMap R _ a)
        rw [zChartHom_algebraMap F hz hF, chartZLift_algebraMap _ (changeChartHom_coordOf_two γ C),
          changeChartHom_algebraMap]
      · change zChartHom F hz (affX C) = chartZLift _ (changeChartHom_coordOf_two γ C) (affX C)
        rw [hx, chartZLift_affX, changeChartHom_coordOf_zero]
      · change zChartHom F hz (affY C) = chartZLift _ (changeChartHom_coordOf_two γ C) (affY C)
        rw [hy, chartZLift_affY, changeChartHom_coordOf_one]
    · rw [hz, zeroOf_changeMap]
  exact ⟨γ, ⟨hγ, hex⟩, fun γ' ⟨h', hα'⟩ => variableChange_unique h' hγ F hz hα' hex⟩

/-- **Existence.** Every isomorphism `α` of the pointed families of the plane cubics of `C'` and
`C` over `Spec R` is, on total spaces, the isomorphism `changeIso γ C` of a coordinate change `γ`
with `C' = γ • C`, preceded by the identification `E_{C'} = E_{γ • C}`. -/
theorem exists_variableChange (C C' : WeierstrassCurve R)
    (α : FamilyIso (familyOf C') (familyOf C)) :
    ∃ γ : WeierstrassCurve.VariableChange R, ∃ h : C' = γ • C,
      α.iso.hom = eqToHom (congrArg projOf h) ≫ (changeIso γ C).iso.hom := by
  obtain ⟨γ, ⟨h, hα⟩, -⟩ := exists_unique_variableChange C C' α
  exact ⟨γ, h.symm, hα⟩

/-- **Uniqueness.** The coordinate change inducing an isomorphism of plane cubics is determined by
it: if `C' = γ₁ • C` and `C' = γ₂ • C` and the induced isomorphisms `E_{C'} ≅ E_C` agree, then
`γ₁ = γ₂`. -/
theorem variableChange_eq_of_changeIso_eq {C C' : WeierstrassCurve R}
    {γ₁ γ₂ : WeierstrassCurve.VariableChange R} (h₁ : C' = γ₁ • C) (h₂ : C' = γ₂ • C)
    (h : eqToHom (congrArg projOf h₁) ≫ (changeIso γ₁ C).iso.hom =
      eqToHom (congrArg projOf h₂) ≫ (changeIso γ₂ C).iso.hom) : γ₁ = γ₂ := by
  let F : projOf C' ⟶ projOf C := eqToHom (congrArg projOf h₁) ≫ changeMap γ₁ C
  have : IsIso F := by dsimp only [F]; infer_instance
  have hz : zeroOf C' ≫ F = zeroOf C := by
    dsimp only [F]
    subst h₁
    rw [eqToHom_refl, Category.id_comp, zeroOf_changeMap]
  exact variableChange_unique h₁.symm h₂.symm F hz rfl h

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass
