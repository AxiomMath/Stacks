module

public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicPoles

/-!
# The action of an isomorphism of plane Weierstrass cubics on the affine coordinates

Let `W`, `W'` be Weierstrass equations over a commutative ring `R`, with no condition on their
discriminants, and let `F : E_{W'} ⟶ E_W` be an isomorphism of their plane cubics over `Spec R`
carrying the zero section `(0 : 1 : 0)` to the zero section. Since the complement of the zero
section is the chart `D₊(z)`, `F` restricts to an isomorphism of the affine curves, given by a ring
homomorphism `zChartHom F hz : R[x, y]/(f_W) → R[x, y]/(f_{W'})`. This file proves that

* `zChartHom F hz` sends `x` to `u² x + r` and `y` to `u³ y + s x + t` for some `r, s, t ∈ R` and a
  unit `u`, namely the inverse of the tangent of `F` at the zero section.

This is the pole-order argument: `x` and `y` have poles of order `2` and `3` at the zero section,
and `F` preserves pole orders because it preserves the zero section.

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.zChartHom`: the action of `F` on the charts
  `D₊(z)`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.arc` and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.arcChartHom`: the formal arc
  `Spec R⟦X⟧ ⟶ E_W` at the zero section, and the homomorphism `R[X, Z]/(F(X, 1, Z)) → R⟦X⟧` by
  which the arc of `W'` followed by `F` factors through the chart `D₊(y)` of `W`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.thick`: the first-order thickening
  `Spec R[ε] ⟶ E_W` of the zero section with a given tangent, and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.tangentOf` the tangent of `F` at the zero
  section.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.preimage_basicOpenOf_two`: `F` carries
  `D₊(z)` onto `D₊(z)`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isUnit_tangentOf`: the tangent of `F` at the
  zero section is a unit.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.laurentHom_comp_zChartHom`: `zChartHom F hz`
  read along the punctured formal arc of `W'` is the change of charts of `W` along the image of
  the formal arc.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.exists_zChartHom_affX` and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.exists_zChartHom_affY`: the images of `x`
  and `y`.

## Implementation notes

The formal arc of `W'` followed by `F` lands in the chart `D₊(y)` of `W`, because every point of
`Spec R⟦X⟧` specializes to a point over `X = 0`, where the arc is the zero section, and the zero
section of `W` lies in `D₊(y)`. The image of `X` along it is `X h` with `h(0)` the tangent of `F`;
that this is a unit is seen on first-order thickenings, on which `F` and `F⁻¹` act by rescaling the
tangent. The pole orders are then those of `WeierstrassCubicPoles.lean`.

## References

* [Stacks Project, Tag 072T](https://stacks.math.columbia.edu/tag/072T)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {W W' : WeierstrassCurve R}

/-! ### Charts and `Spec` -/

/-- Two ring homomorphisms out of `R[x, y]/(f_W)` are equal if they induce the same morphism to
the plane cubic through the chart `D₊(z)`. -/
theorem ringHom_ext_of_SpecMap_chartZ {S : Type u} [CommRing S]
    {φ φ' : W.toAffine.CoordinateRing →+* S}
    (h : Spec.map (CommRingCat.ofHom φ) ≫ chartZ W = Spec.map (CommRingCat.ofHom φ') ≫ chartZ W) :
    φ = φ' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono (chartZ W)).mp h))

/-- Two ring homomorphisms out of the coordinate ring of the chart `D₊(y)` are equal if they induce
the same morphism to the plane cubic through that chart. -/
theorem ringHom_ext_of_SpecMap_chartY {S : Type u} [CommRing S] {φ φ' : ChartYRing W →+* S}
    (h : Spec.map (CommRingCat.ofHom φ) ≫ chartY W = Spec.map (CommRingCat.ofHom φ') ≫ chartY W) :
    φ = φ' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono (chartY W)).mp h))

/-- A ring homomorphism inducing a morphism `F` over `Spec R` on charts is compatible with the
structure maps from `R`. -/
private theorem comp_eq_of_SpecMap_comp_eq {A S : Type u} [CommRing A] [CommRing S] {a : R →+* A}
    {b : R →+* S} {c : Spec (CommRingCat.of A) ⟶ projOf W} {d : Spec (CommRingCat.of S) ⟶ projOf W'}
    {F : projOf W' ⟶ projOf W} (hF : F ≫ projectionOf W = projectionOf W')
    (hc : c ≫ projectionOf W = Spec.map (CommRingCat.ofHom a))
    (hd : d ≫ projectionOf W' = Spec.map (CommRingCat.ofHom b)) {φ : A →+* S}
    (h : Spec.map (CommRingCat.ofHom φ) ≫ c = d ≫ F) : φ.comp a = b := by
  have h' : Spec.map (CommRingCat.ofHom (φ.comp a)) = Spec.map (CommRingCat.ofHom b) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, ← hc, ← Category.assoc, h, Category.assoc, hF, hd]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h')

/-! ### An isomorphism preserving the zero section preserves the chart `D₊(z)` -/

section Iso

variable (F : projOf W' ⟶ projOf W) [IsIso F] (hz : zeroOf W' ≫ F = zeroOf W)

include hz in
/-- An isomorphism preserving the zero sections carries a point into the zero section if and only
if the point lies in the zero section. -/
theorem mem_range_zeroOf_iff (p : projOf W') :
    F p ∈ Set.range (zeroOf W) ↔ p ∈ Set.range (zeroOf W') := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, (F.homeomorph).injective ?_⟩
    rw [Scheme.Hom.homeomorph_apply, Scheme.Hom.homeomorph_apply, ← hr, ← Scheme.Hom.comp_apply, hz]
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rw [← Scheme.Hom.comp_apply, hz]⟩

include hz in
/-- An isomorphism preserving the zero sections carries `D₊(z)` onto `D₊(z)`: the preimage of
`D₊(z)` is `D₊(z)`. -/
theorem preimage_basicOpenOf_two :
    F ⁻¹ᵁ basicOpenOf W (coordOf W 2) = basicOpenOf W' (coordOf W' 2) := by
  ext p
  have h1 := congrArg (F p ∈ ·) (range_zeroOf W)
  have h2 := congrArg (p ∈ ·) (range_zeroOf W')
  simp only [eq_iff_iff, Set.mem_compl_iff, SetLike.mem_coe] at h1 h2
  show F p ∈ basicOpenOf W (coordOf W 2) ↔ p ∈ basicOpenOf W' (coordOf W' 2)
  rw [← not_iff_not, ← h1, ← h2]
  exact mem_range_zeroOf_iff F hz p

include hz in
/-- The image of the chart `D₊(z)` of `W'` under `F` lies in the chart `D₊(z)` of `W`. -/
theorem range_chartZ_comp_subset :
    Set.range (chartZ W' ≫ F) ⊆ Set.range (chartZ W) := by
  rintro _ ⟨q, rfl⟩
  rw [← Scheme.Hom.coe_opensRange (chartZ W), opensRange_chartZ]
  have hq : chartZ W' q ∈ basicOpenOf W' (coordOf W' 2) := by
    rw [← opensRange_chartZ]
    exact ⟨q, rfl⟩
  rw [← preimage_basicOpenOf_two F hz] at hq
  exact SetLike.mem_coe.mpr hq

/-- The ring homomorphism `R[x, y]/(f_W) → R[x, y]/(f_W')` by which an isomorphism of plane cubics
preserving the zero section acts on the charts `D₊(z)`, the complements of the zero sections. -/
def zChartHom : W.toAffine.CoordinateRing →+* W'.toAffine.CoordinateRing :=
  (Spec.preimage (IsOpenImmersion.lift (chartZ W) (chartZ W' ≫ F)
    (range_chartZ_comp_subset F hz))).hom

/-- `zChartHom F hz` induces the restriction of `F` to the charts `D₊(z)`. -/
theorem SpecMap_zChartHom :
    Spec.map (CommRingCat.ofHom (zChartHom F hz)) ≫ chartZ W = chartZ W' ≫ F := by
  rw [zChartHom, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

/-- `zChartHom F hz` is the only ring homomorphism inducing the restriction of `F` to the charts
`D₊(z)`. -/
theorem zChartHom_eq {φ : W.toAffine.CoordinateRing →+* W'.toAffine.CoordinateRing}
    (h : Spec.map (CommRingCat.ofHom φ) ≫ chartZ W = chartZ W' ≫ F) : zChartHom F hz = φ :=
  ringHom_ext_of_SpecMap_chartZ ((SpecMap_zChartHom F hz).trans h.symm)

include hz in
/-- If `F` commutes with the projections to `Spec R`, then `zChartHom F hz` fixes the image of
every `a : R`. -/
theorem zChartHom_algebraMap (hF : F ≫ projectionOf W = projectionOf W') (a : R) :
    zChartHom F hz (algebraMap R _ a) = algebraMap R _ a := by
  exact RingHom.congr_fun (comp_eq_of_SpecMap_comp_eq hF (chartZ_projectionOf W)
    (chartZ_projectionOf W') (SpecMap_zChartHom F hz)) a

end Iso

/-! ### The formal arc at the zero section -/

/-- The formal arc `Spec R⟦X⟧ ⟶ E` of the plane cubic at its zero section. -/
def arc (W : WeierstrassCurve R) : Spec (CommRingCat.of (PowerSeries R)) ⟶ projOf W :=
  Spec.map (CommRingCat.ofHom (arcHom W)) ≫ chartY W

/-- `X` lies in every maximal ideal of `R⟦X⟧`. -/
theorem X_mem_of_isMaximal (M : Ideal (PowerSeries R)) [M.IsMaximal] : PowerSeries.X ∈ M := by
  by_contra hX
  obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv ‹_› hX
  have hu : IsUnit i := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have := congrArg PowerSeries.constantCoeff hyi
    rw [map_add, map_mul, PowerSeries.constantCoeff_X, mul_zero, zero_add, map_one] at this
    rw [this]
    exact isUnit_one
  exact (Ideal.IsMaximal.ne_top ‹_›) (Ideal.eq_top_of_isUnit_mem _ hi hu)

/-- The formal arc carries a point of `Spec R⟦X⟧` into `D₊(z)` if and only if its prime ideal does
not contain `formalZ W`. -/
theorem arc_mem_basicOpenOf_two_iff (W : WeierstrassCurve R)
    (m : Spec (CommRingCat.of (PowerSeries R))) :
    arc W m ∈ basicOpenOf W (coordOf W 2) ↔ formalZ W ∉ m.asIdeal := by
  show Spec.map (CommRingCat.ofHom (arcHom W)) m ∈ chartY W ⁻¹ᵁ basicOpenOf W (coordOf W 2) ↔ _
  rw [chartY, specPoint_preimage_basicOpenOf W _ _ one_pos (coordOf_mem W 2), chartYHom_coordOf_two]
  show chartYZ W ∉ Ideal.comap (arcHom W) m.asIdeal ↔ _
  rw [Ideal.mem_comap, arcHom_chartYZ]

section Iso

variable (F : projOf W' ⟶ projOf W) [IsIso F] (hz : zeroOf W' ≫ F = zeroOf W)

include hz in
/-- The image of the formal arc of `W'` under `F` lies in the chart `D₊(y)` of `W`. -/
theorem range_arc_comp_subset : Set.range (arc W' ≫ F) ⊆ Set.range (chartY W) := by
  rintro _ ⟨q, rfl⟩
  rw [← Scheme.Hom.coe_opensRange (chartY W), opensRange_chartY]
  obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
  let m : Spec (CommRingCat.of (PowerSeries R)) := ⟨M, hM.isPrime⟩
  have hm : (arc W' ≫ F) m ∈ basicOpenOf W (coordOf W 1) := by
    have h1 : arc W' m ∉ basicOpenOf W' (coordOf W' 2) := by
      rw [arc_mem_basicOpenOf_two_iff, not_not, formalZ]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (X_mem_of_isMaximal M) 3 (by norm_num))
    have h2 : F (arc W' m) ∉ basicOpenOf W (coordOf W 2) :=
      fun h => h1 (by rwa [← preimage_basicOpenOf_two F hz])
    have hcov : F (arc W' m) ∈ basicOpenOf W (coordOf W 2) ⊔ basicOpenOf W (coordOf W 1) := by
      rw [basicOpenOf_two_sup_basicOpenOf_one]
      trivial
    rcases hcov with h | h
    · exact absurd h h2
    · exact h
  have hqm : q ⤳ m := (PrimeSpectrum.le_iff_specializes q m).mp hqM
  exact SetLike.mem_coe.mpr (hqm.mem_open ((arc W' ≫ F) ⁻¹ᵁ basicOpenOf W (coordOf W 1)).isOpen hm)

/-- The formal arc of `W'` at its zero section, carried to `W` by an isomorphism preserving the
zero sections, lands in the chart `D₊(y)` of `W`; this is the induced homomorphism from its
coordinate ring to `R⟦X⟧`. -/
def arcChartHom : ChartYRing W →+* PowerSeries R :=
  (Spec.preimage (IsOpenImmersion.lift (chartY W) (arc W' ≫ F)
    (range_arc_comp_subset F hz))).hom

/-- Through the chart `D₊(y)` of `W`, `arcChartHom F hz` induces the formal arc of `W'` followed
by `F`. -/
theorem SpecMap_arcChartHom :
    Spec.map (CommRingCat.ofHom (arcChartHom F hz)) ≫ chartY W = arc W' ≫ F := by
  rw [arcChartHom, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

include hz in
/-- If `F` commutes with the projections to `Spec R`, then `arcChartHom F hz` sends the image of
`a : R` to the constant power series `a`. -/
theorem arcChartHom_algebraMap (hF : F ≫ projectionOf W = projectionOf W') (a : R) :
    arcChartHom F hz (algebraMap R _ a) = PowerSeries.C a := by
  have hd : arc W' ≫ projectionOf W' = Spec.map (CommRingCat.ofHom PowerSeries.C) := by
    rw [arc, Category.assoc, chartY_projectionOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (Spec.map ∘ CommRingCat.ofHom) (RingHom.ext fun a => arcHom_algebraMap W' a)
  exact RingHom.congr_fun (comp_eq_of_SpecMap_comp_eq hF (chartY_projectionOf W) hd
    (SpecMap_arcChartHom F hz)) a

/-- The formal arc restricted to `X = 0` is the zero section. -/
theorem SpecMap_constantCoeff_arc (W : WeierstrassCurve R) :
    Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := R))) ≫ arc W = zeroOf W := by
  rw [arc, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, constantCoeff_arcHom,
    zeroOf_eq_chartY]

/-- The constant coefficient of `arcChartHom F hz` is evaluation at the zero section on the chart
`D₊(y)`. -/
theorem constantCoeff_comp_arcChartHom :
    (PowerSeries.constantCoeff).comp (arcChartHom F hz) = chartYEvalZero W := by
  refine ringHom_ext_of_SpecMap_chartY ?_
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, SpecMap_arcChartHom, ← Category.assoc,
    SpecMap_constantCoeff_arc, hz, zeroOf_eq_chartY]

end Iso

/-! ### The tangent of an isomorphism at the zero section -/

/-- The first-order thickening `Spec R[ε] ⟶ E` of the zero section with tangent `p`. -/
def thick (W : WeierstrassCurve R) (p : R) : Spec (CommRingCat.of (DualNumber R)) ⟶ projOf W :=
  Spec.map (CommRingCat.ofHom (tangentHom W p)) ≫ chartY W

/-- The first-order thickening with tangent `1` is the formal arc restricted to `Spec R[ε]`. -/
theorem thick_one_eq (W : WeierstrassCurve R) :
    thick W 1 = Spec.map (CommRingCat.ofHom powerSeriesToDual) ≫ arc W := by
  rw [thick, arc, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    powerSeriesToDual_comp_arcHom]

/-- Rescaling `ε` by `p` carries the first-order thickening with tangent `q` to the one with
tangent `p * q`. -/
theorem SpecMap_rescaleDual_thick (W : WeierstrassCurve R) (p q : R) :
    Spec.map (CommRingCat.ofHom (rescaleDual p).toRingHom) ≫ thick W q = thick W (p * q) := by
  rw [thick, thick, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    rescaleDual_comp_tangentHom]

/-- A first-order thickening of the zero section determines its tangent. -/
theorem thick_injective (W : WeierstrassCurve R) {p q : R} (h : thick W p = thick W q) : p = q :=
  tangentHom_injective W (ringHom_ext_of_SpecMap_chartY h)

section Iso

variable (F : projOf W' ⟶ projOf W) [IsIso F] (hz : zeroOf W' ≫ F = zeroOf W)

/-- The tangent at the zero section of an isomorphism of plane cubics preserving the zero
sections: the coefficient of `X` in the image of `X = x / y` along the formal arc. -/
def tangentOf : R := PowerSeries.coeff 1 (arcChartHom F hz (chartYX W))

include hz in
/-- An isomorphism preserving the zero sections carries the first-order thickening with tangent
`1` to the one with tangent `tangentOf F hz`. -/
theorem thick_one_comp (hF : F ≫ projectionOf W = projectionOf W') :
    thick W' 1 ≫ F = thick W (tangentOf F hz) := by
  have h : powerSeriesToDual.comp (arcChartHom F hz) = tangentHom W (tangentOf F hz) := by
    rw [eq_tangentHom W (powerSeriesToDual.comp (arcChartHom F hz))]
    · simp [tangentOf]
    · intro a
      rw [RingHom.comp_apply, arcChartHom_algebraMap F hz hF]
      exact TrivSqZeroExt.ext (by simp [TrivSqZeroExt.algebraMap_eq_inl])
        (by simp [TrivSqZeroExt.algebraMap_eq_inl])
    · intro b
      rw [RingHom.comp_apply, fst_powerSeriesToDual, ← RingHom.comp_apply,
        constantCoeff_comp_arcChartHom]
  rw [thick_one_eq, Category.assoc, ← SpecMap_arcChartHom F hz, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, h, thick]

include hz in
/-- **The tangent at the zero section of an isomorphism is a unit.** -/
theorem isUnit_tangentOf (hF : F ≫ projectionOf W = projectionOf W') :
    IsUnit (tangentOf F hz) := by
  have hz' : zeroOf W ≫ inv F = zeroOf W' := by
    rw [← hz, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hF' : inv F ≫ projectionOf W' = projectionOf W := by rw [← hF, IsIso.inv_hom_id_assoc]
  have h : thick W' 1 = thick W' (tangentOf F hz * tangentOf (inv F) hz') := by
    calc thick W' 1 = thick W' 1 ≫ F ≫ inv F := by rw [IsIso.hom_inv_id, Category.comp_id]
      _ = thick W (tangentOf F hz) ≫ inv F := by rw [← Category.assoc, thick_one_comp F hz hF]
      _ = Spec.map (CommRingCat.ofHom (rescaleDual (tangentOf F hz)).toRingHom) ≫
            thick W 1 ≫ inv F := by
        rw [← Category.assoc, SpecMap_rescaleDual_thick, mul_one]
      _ = _ := by rw [thick_one_comp (inv F) hz' hF', SpecMap_rescaleDual_thick]
  exact IsUnit.of_mul_eq_one _ (thick_injective W' h).symm

end Iso

/-! ### The action on the affine coordinates -/

/-- The function `1 + a₁X + a₃Z - a₂X² - a₄XZ - a₆Z²` on the chart `D₊(y)`, with `Z w = X³`. -/
def chartYW (W : WeierstrassCurve R) : ChartYRing W :=
  1 + algebraMap R _ W.a₁ * chartYX W + algebraMap R _ W.a₃ * chartYZ W -
    algebraMap R _ W.a₂ * chartYX W ^ 2 - algebraMap R _ W.a₄ * chartYX W * chartYZ W -
    algebraMap R _ W.a₆ * chartYZ W ^ 2

/-- On the chart `D₊(y)`, `Z w = X³`. -/
theorem chartYZ_mul_chartYW (W : WeierstrassCurve R) : chartYZ W * chartYW W = chartYX W ^ 3 := by
  rw [chartYW]
  linear_combination chartY_equation W

/-- The function `chartYW W` takes the value `1` at the zero section. -/
theorem chartYEvalZero_chartYW (W : WeierstrassCurve R) : chartYEvalZero W (chartYW W) = 1 := by
  simp [chartYW]

section Iso

variable (F : projOf W' ⟶ projOf W) [IsIso F] (hz : zeroOf W' ≫ F = zeroOf W)
  (hF : F ≫ projectionOf W = projectionOf W')

/-- The power series `h` with `θ(X) = X h` along the formal arc. -/
def arcShift : PowerSeries R :=
  PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (arcChartHom F hz (chartYX W))

/-- The image of `X` under `arcChartHom F hz` is `X * arcShift F hz`. -/
theorem arcChartHom_chartYX : arcChartHom F hz (chartYX W) = PowerSeries.X * arcShift F hz := by
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (arcChartHom F hz (chartYX W))]
  rw [← RingHom.comp_apply PowerSeries.constantCoeff, constantCoeff_comp_arcChartHom,
    chartYEvalZero_chartYX, map_zero, add_zero, arcShift]

/-- The constant coefficient of `arcShift F hz` is the tangent `tangentOf F hz`. -/
theorem constantCoeff_arcShift : PowerSeries.constantCoeff (arcShift F hz) = tangentOf F hz := by
  simp [arcShift, tangentOf]

include hF in
/-- `arcShift F hz` is a unit of `R⟦X⟧`. -/
theorem isUnit_arcShift : IsUnit (arcShift F hz) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_arcShift]
  exact isUnit_tangentOf F hz hF

/-- The image of `chartYW W` under `arcChartHom F hz` is a unit of `R⟦X⟧`. -/
theorem isUnit_arcChartHom_chartYW : IsUnit (arcChartHom F hz (chartYW W)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← RingHom.comp_apply, constantCoeff_comp_arcChartHom,
    chartYEvalZero_chartYW]
  exact isUnit_one

/-- The inverse of `arcShift F hz`. -/
def arcShiftInv : PowerSeries R := ↑(isUnit_arcShift F hz hF).unit⁻¹

/-- `arcShiftInv F hz hF` is the inverse of `arcShift F hz`. -/
theorem arcShift_mul_arcShiftInv : arcShift F hz * arcShiftInv F hz hF = 1 :=
  (isUnit_arcShift F hz hF).mul_val_inv

/-- The power series `h⁻³ θ(w)`, with `X⁻³ h⁻³ θ(w)` the inverse of `θ(Z)`. -/
def arcInvZ : PowerSeries R := arcShiftInv F hz hF ^ 3 * arcChartHom F hz (chartYW W)

/-- In Laurent series, `X⁻³ arcInvZ F hz hF` is the inverse of the image of `Z` under
`arcChartHom F hz`. -/
theorem arcChartHom_chartYZ_mul :
    ofPS (arcChartHom F hz (chartYZ W)) * (HahnSeries.single (-3) 1 * ofPS (arcInvZ F hz hF)) =
      1 := by
  have key : arcChartHom F hz (chartYZ W) * arcInvZ F hz hF = PowerSeries.X ^ 3 := by
    have e := congrArg (arcChartHom F hz) (chartYZ_mul_chartYW W)
    rw [map_mul, map_pow, arcChartHom_chartYX] at e
    rw [arcInvZ]
    linear_combination (arcShiftInv F hz hF) ^ 3 * e + PowerSeries.X ^ 3 *
      ((arcShift F hz * arcShiftInv F hz hF) ^ 2 + arcShift F hz * arcShiftInv F hz hF + 1) *
        arcShift_mul_arcShiftInv F hz hF
  calc _ = HahnSeries.single (-3) 1 * ofPS (arcChartHom F hz (chartYZ W) * arcInvZ F hz hF) := by
        rw [map_mul]
        ring
    _ = 1 := by
      rw [key, ofPS_X_pow, single_mul_single_one]
      simp

/-- **The action on the affine coordinates, read along the punctured formal arc.** -/
theorem laurentHom_comp_zChartHom :
    (laurentHom W').comp (zChartHom F hz) = chartZOfChartY W ((ofPS).comp (arcChartHom F hz))
      (HahnSeries.single (-3) 1 * ofPS (arcInvZ F hz hF)) (arcChartHom_chartYZ_mul F hz hF) := by
  refine ringHom_ext_of_SpecMap_chartZ ?_
  have h := SpecMap_arcChartHom F hz
  rw [arc] at h
  rw [SpecMap_chartZOfChartY_chartZ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    SpecMap_zChartHom, ← Category.assoc, SpecMap_laurentHom_chartZ, CommRingCat.ofHom_comp,
    Spec.map_comp]
  simp only [Category.assoc] at h ⊢
  rw [h]

/-- Along the punctured formal arc of `W'`, the image of `x` under `zChartHom F hz` is
`X⁻² h⁻² θ(w)`, with `h = arcShift F hz`, `θ = arcChartHom F hz` and `w = chartYW W`. -/
theorem laurentHom_zChartHom_affX : laurentHom W' (zChartHom F hz (affX W)) =
    HahnSeries.single (-((2 : ℕ) : ℤ)) 1 *
      ofPS (arcShiftInv F hz hF ^ 2 * arcChartHom F hz (chartYW W)) := by
  rw [← RingHom.comp_apply, laurentHom_comp_zChartHom F hz hF, chartZOfChartY_x,
    RingHom.comp_apply, arcChartHom_chartYX, arcInvZ]
  have e : arcShift F hz * arcShiftInv F hz hF ^ 3 = arcShiftInv F hz hF ^ 2 := by
    linear_combination arcShiftInv F hz hF ^ 2 * arcShift_mul_arcShiftInv F hz hF
  calc _ = (ofPS PowerSeries.X * HahnSeries.single (-3) 1) *
        ofPS (arcShift F hz * arcShiftInv F hz hF ^ 3 * arcChartHom F hz (chartYW W)) := by
        simp only [map_mul]
        ring
    _ = _ := by
      rw [e, ← pow_one (PowerSeries.X : PowerSeries R), ofPS_X_pow, single_mul_single_one]
      norm_num

/-- Along the punctured formal arc of `W'`, the image of `y` under `zChartHom F hz` is
`X⁻³ arcInvZ F hz hF`. -/
theorem laurentHom_zChartHom_affY : laurentHom W' (zChartHom F hz (affY W)) =
    HahnSeries.single (-((3 : ℕ) : ℤ)) 1 * ofPS (arcInvZ F hz hF) := by
  rw [← RingHom.comp_apply, laurentHom_comp_zChartHom F hz hF, chartZOfChartY_y]
  norm_num

/-- The image of `chartYW W` under `arcChartHom F hz` has constant coefficient `1`. -/
theorem constantCoeff_arcChartHom_chartYW :
    PowerSeries.constantCoeff (arcChartHom F hz (chartYW W)) = 1 := by
  rw [← RingHom.comp_apply, constantCoeff_comp_arcChartHom, chartYEvalZero_chartYW]

/-- The inverse of the tangent at the zero section, a unit. -/
def tangentInv : Rˣ := (isUnit_tangentOf F hz hF).unit⁻¹

/-- The constant coefficient of `arcShiftInv F hz hF` is `tangentInv F hz hF`. -/
theorem constantCoeff_arcShiftInv :
    PowerSeries.constantCoeff (arcShiftInv F hz hF) = tangentInv F hz hF := by
  have h1 := congrArg PowerSeries.constantCoeff (arcShift_mul_arcShiftInv F hz hF)
  rw [map_mul, constantCoeff_arcShift, map_one,
    ← IsUnit.unit_spec (isUnit_tangentOf F hz hF)] at h1
  exact (Units.inv_eq_of_mul_eq_one_right h1).symm

/-- **The image of `x`.** An isomorphism of plane cubics preserving the zero sections sends `x` to
`u² x + r` on the charts `D₊(z)`, with `u` the inverse of its tangent at the zero section. -/
theorem exists_zChartHom_affX : ∃ r : R, zChartHom F hz (affX W) =
    algebraMap R _ r + algebraMap R _ ((tangentInv F hz hF : R) ^ 2) * affX W' := by
  obtain ⟨r, hr⟩ := exists_eq_of_laurentHom_eq_two W' (laurentHom_zChartHom_affX F hz hF)
  refine ⟨r, hr.trans ?_⟩
  rw [map_mul, constantCoeff_arcChartHom_chartYW, mul_one, map_pow, constantCoeff_arcShiftInv]

/-- **The image of `y`.** An isomorphism of plane cubics preserving the zero sections sends `y` to
`u³ y + s x + t` on the charts `D₊(z)`, with `u` the inverse of its tangent at the zero section. -/
theorem exists_zChartHom_affY : ∃ r s : R, zChartHom F hz (affY W) =
    algebraMap R _ r + algebraMap R _ s * affX W' +
      algebraMap R _ ((tangentInv F hz hF : R) ^ 3) * affY W' := by
  obtain ⟨r, s, hr⟩ := exists_eq_of_laurentHom_eq_three W' (laurentHom_zChartHom_affY F hz hF)
  refine ⟨r, s, hr.trans ?_⟩
  rw [arcInvZ, map_mul, constantCoeff_arcChartHom_chartYW, mul_one, map_pow,
    constantCoeff_arcShiftInv]

end Iso

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass
