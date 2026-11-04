module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamily
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.HomogeneousRescale
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.UnitRescale
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.FromGlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.GradedNaturality
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Basic

/-!
# Points of a plane Weierstrass cubic with values in a ring

Let `W` be a Weierstrass equation over a commutative ring `R` and let
`E = Proj R[x, y, z]/(F) ⊂ P²_R` be its plane cubic. A ring homomorphism
`κ : R[x, y, z]/(F) → S` under which the homogeneous coordinates generate the unit ideal is a
point of `E` with values in `S`: a morphism `Spec S ⟶ E`. This file sets up that construction
and the three facts about it which the charts of `E` are computed from: it is natural in `S`,
it is unchanged when the homogeneous coordinates are rescaled by a unit, and when the `i`-th
coordinate is `1` it factors through the standard chart `D₊(tᵢ) = Spec R[x, y, z]/(F)_{(tᵢ)}`.
It also proves the dehomogenization formula on `R[x, y, z]/(F)_{(tᵢ)}` and, from it, a criterion
for a homomorphism out of that degree-zero localization to be bijective.

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.coordOf`: the class of the `i`-th
  homogeneous coordinate in `R[x, y, z]/(F)`, and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.coordLift`: a ring homomorphism out of
  `R[x, y, z]/(F)` given by the images of the coordinates.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.specPoint`: the morphism `Spec S ⟶ E` of
  a ring homomorphism `R[x, y, z]/(F) → S` under which the coordinates generate the unit ideal.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.awayιOf` and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.basicOpenOf`: the open immersion of the
  standard chart `D₊(tᵢ)` and the standard open `D₊(f)`, with the plane cubic as target.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.awayLiftOf`: the homomorphism
  `R[x, y, z]/(F)_{(tᵢ)} → S`, `p / tᵢᵏ ↦ κ p`, of a homomorphism `κ` with `κ tᵢ = 1`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.awayCoord`: the affine coordinate
  `tⱼ / tᵢ` of the chart `D₊(tᵢ)`.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.SpecMap_specPoint`: naturality in `S`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.specPoint_congr_unit`: rescaling the
  coordinates by a unit does not change the point.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.specPoint_projectionOf`: the point lies
  over `Spec S ⟶ Spec R`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.specPoint_eq_awayι`: a point whose `i`-th
  coordinate is `1` is `Spec` of `awayLiftOf` followed by the chart `D₊(tᵢ)`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.specPoint_preimage_basicOpenOf`: the
  inverse image of `D₊(f)` is the basic open of `κ f`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.eval₂_awayCoord`: dehomogenization, a
  homogeneous polynomial of degree `k` evaluated at the affine coordinates is `P / tᵢᵏ`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.awayLiftOf_bijective`: `awayLiftOf` is
  bijective as soon as it has a section sending the coordinates to the affine coordinates.

## Implementation notes

The points are Mathlib's `AlgebraicGeometry.Proj.fromOfGlobalSections` for `X = Spec S`, the ring
homomorphism being composed with `Γ(Spec S) ≅ S`. Rescaling is
`AlgebraicGeometry.Proj.fromOfGlobalSections_congr_unit`, applied through the homogeneity of the
representatives (`MvPolynomial.IsHomogeneous.eval₂_const_mul`); naturality is
`AlgebraicGeometry.Proj.comp_fromOfGlobalSections`. The factorization through a chart is proved
for an arbitrary graded ring, `fromOfGlobalSections_eq_SpecMap_awayι`, from the computation of
the chart morphism on sections in `Stacks.ProjGlobalSectionsAppTop`.

The plane cubic `projOf W` is a definition, not a reducible abbreviation, of `Proj` of the
graded ring; `awayιOf` and `basicOpenOf` restate `AlgebraicGeometry.Proj.awayι` and
`AlgebraicGeometry.Proj.basicOpen` with `projOf W` in their types, so that statements about
morphisms into the plane cubic can be rewritten.

## References

* [Stacks Project, Tag 072S](https://stacks.math.columbia.edu/tag/072S)
* [Stacks Project, Tag 072T](https://stacks.math.columbia.edu/tag/072T)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial HomogeneousLocalization

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-! ### Homogeneous coordinates -/

/-- The class in `R[x, y, z]/(F)` of the `i`-th homogeneous coordinate. -/
abbrev coordOf (i : Fin 3) : coordRingOf W := Ideal.Quotient.mk _ (X i)

/-- The homogeneous coordinates have degree one. -/
theorem coordOf_mem (i : Fin 3) : coordOf W i ∈ gradingOf W 1 :=
  Stacks.HomogeneousIdeal.mk_mem_quotientGrading _
    (by rw [mem_homogeneousSubmodule]; exact isHomogeneous_X _ _)

/-- A ring homomorphism out of `R[x, y, z]/(F)`, given by a ring homomorphism out of `R` and the
images of `x`, `y`, `z`, subject to the homogeneous Weierstrass equation. -/
def coordLift {S : Type*} [CommRing S] (κ : R →+* S) (v : Fin 3 → S)
    (hv : v 2 * v 1 ^ 2 + κ W.a₁ * v 0 * v 1 * v 2 + κ W.a₃ * v 1 * v 2 ^ 2 -
      (v 0 ^ 3 + κ W.a₂ * v 0 ^ 2 * v 2 + κ W.a₄ * v 0 * v 2 ^ 2 + κ W.a₆ * v 2 ^ 3) = 0) :
    coordRingOf W →+* S :=
  Ideal.Quotient.lift _ (eval₂Hom κ v) <| by
    intro a ha
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp only [map_mul, coe_eval₂Hom, cubicOf, WeierstrassCurve.Projective.polynomial,
      eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    linear_combination (eval₂ κ v g) * hv

/-- `coordLift` on the class of a polynomial is evaluation of the polynomial. -/
theorem coordLift_mk {S : Type*} [CommRing S] (κ : R →+* S) (v : Fin 3 → S) (hv) (P) :
    coordLift W κ v hv (Ideal.Quotient.mk _ P) = eval₂ κ v P := rfl


/-! ### Points of the plane cubic with values in a ring -/

/-- If one homogeneous coordinate becomes a unit under `κ`, then the image of the irrelevant
ideal under `κ` generates the unit ideal. -/
theorem map_irrelevant_eq_top_of_isUnit {S : Type*} [CommRing S] (κ : coordRingOf W →+* S)
    (i : Fin 3) (h : IsUnit (κ (coordOf W i))) :
    (HomogeneousIdeal.irrelevant (gradingOf W)).toIdeal.map κ = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv'.mp h
  rw [← hw]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos (coordOf_mem W i)))

/-- The morphism `Spec S ⟶ E` given by homogeneous coordinates with values in `S`: a ring
homomorphism `κ` out of `R[x, y, z]/(F)` under which the coordinates generate the unit ideal. -/
def specPoint {S : Type u} [CommRing S] (κ : coordRingOf W →+* S)
    (hκ : (HomogeneousIdeal.irrelevant (gradingOf W)).toIdeal.map κ = ⊤) :
    Spec (CommRingCat.of S) ⟶ projOf W :=
  Proj.fromOfGlobalSections (gradingOf W) ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom.comp κ)
    (by rw [← Ideal.map_map, hκ, Ideal.map_top])

/-- `specPoint` depends only on the ring homomorphism, not on the proof that it generates. -/
theorem specPoint_congr {S : Type u} [CommRing S] {κ κ' : coordRingOf W →+* S} (h : κ = κ')
    (hκ hκ') : specPoint W κ hκ = specPoint W κ' hκ' := by
  subst h; rfl

/-- Two ring homomorphisms out of `R[x, y, z]/(F)` agreeing on the constants and on `x`, `y`, `z`
are equal. -/
theorem coordRingOf_ringHom_ext {S : Type*} [CommRing S] {κ κ' : coordRingOf W →+* S}
    (hC : ∀ a, κ (algebraMap R _ a) = κ' (algebraMap R _ a))
    (hX : ∀ i, κ (coordOf W i) = κ' (coordOf W i)) : κ = κ' :=
  Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext hC hX)

/-- The zero section is the point with homogeneous coordinates `(0 : 1 : 0)`. -/
theorem zeroOf_eq_specPoint : zeroOf W = specPoint W (evalZeroOf W)
    (map_irrelevant_eq_top_of_isUnit W _ 1 (by simp [evalZeroOf])) := rfl

/-- A point with values in `S`, composed with `Spec S' ⟶ Spec S`, is the point with values in
`S'` obtained by composing the homogeneous coordinates with `S → S'`. -/
theorem SpecMap_specPoint {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (κ : coordRingOf W →+* S) (hκ) (hκ') :
    Spec.map (CommRingCat.ofHom φ) ≫ specPoint W κ hκ = specPoint W (φ.comp κ) hκ' := by
  refine (Proj.comp_fromOfGlobalSections _ _ _ _ ?_).trans
    (Proj.fromOfGlobalSections_congr ?_ _ _)
  · rw [← Ideal.map_map, ← Ideal.map_map, hκ, Ideal.map_top, Ideal.map_top]
  · refine RingHom.ext fun a => ?_
    exact congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).hom (κ a)).symm

/-- A ring homomorphism out of `R[x, y, z]/(F)` is the evaluation of polynomials at the images of
the coordinates. -/
theorem comp_mk_eq_eval₂Hom {S : Type*} [CommRing S] (κ : coordRingOf W →+* S) :
    κ.comp (Ideal.Quotient.mk _) =
      eval₂Hom ((κ.comp (Ideal.Quotient.mk _)).comp MvPolynomial.C) (fun i => κ (coordOf W i)) :=
  MvPolynomial.ringHom_ext (fun _ => by simp) (fun _ => by simp)

/-- Rescaling the homogeneous coordinates of a point by a unit does not change it. -/
theorem specPoint_congr_unit {S : Type u} [CommRing S] (κ κ' : coordRingOf W →+* S) (w : Sˣ)
    (hC : ∀ a : R, κ' (Ideal.Quotient.mk _ (MvPolynomial.C a)) =
      κ (Ideal.Quotient.mk _ (MvPolynomial.C a)))
    (hX : ∀ i, κ' (coordOf W i) = w * κ (coordOf W i)) (hκ hκ') :
    specPoint W κ hκ = specPoint W κ' hκ' := by
  refine Proj.fromOfGlobalSections_congr_unit (gradingOf W) _ _
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom.toMonoidHom w) ?_ _ _
  intro d a ha
  obtain ⟨P, hP, rfl⟩ := (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ a).mp ha
  rw [mem_homogeneousSubmodule] at hP
  have key : κ' (Ideal.Quotient.mk _ P) = (w : S) ^ d * κ (Ideal.Quotient.mk _ P) := by
    have h1 := congr($(comp_mk_eq_eval₂Hom W κ) P)
    have h2 := congr($(comp_mk_eq_eval₂Hom W κ') P)
    simp only [RingHom.comp_apply] at h1 h2
    rw [h1, h2, coe_eval₂Hom, coe_eval₂Hom, ← hP.eval₂_const_mul]
    congr 1
    · exact RingHom.ext fun a => hC a
    · exact funext hX
  simp only [RingHom.comp_apply, key, map_mul, map_pow, Units.coe_map]
  rfl

/-- A point with values in `S` lies over `Spec S ⟶ Spec R` given by the coefficients. -/
theorem specPoint_projectionOf {S : Type u} [CommRing S] (κ : coordRingOf W →+* S) (hκ) :
    specPoint W κ hκ ≫ projectionOf W =
      Spec.map (CommRingCat.ofHom (κ.comp (algebraMap R (coordRingOf W)))) := by
  show Proj.fromOfGlobalSections _ _ _ ≫ Proj.toSpecZero (gradingOf W) ≫
    Spec.map (CommRingCat.ofHom (toGradingZeroOf W)) = _
  rw [Proj.fromOfGlobalSections_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom.comp κ).comp
      (algebraMap (gradingOf W 0) (coordRingOf W))).comp (toGradingZeroOf W) =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom.comp (κ.comp (algebraMap R (coordRingOf W))) :=
    RingHom.ext fun _ => rfl
  rw [this, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, ← Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.id_comp]

/-- The induced homomorphism `(A_t)₀ → S` of a ring homomorphism `κ` with `κ t = 1` sends the
fraction `p / tᵏ` to `κ p`. -/
private theorem awayLift_comp_algebraMap_mk {σ : Type*} {A : Type*} {S : Type*} [CommRing A]
    [CommRing S] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (κ : A →+* S)
    {t : A} {d : ℕ} (hd : t ∈ 𝒜 d) (h : κ t = 1) (k : ℕ) (p : A) (hp : p ∈ 𝒜 (k • d)) :
    ((Localization.awayLift κ t (h ▸ isUnit_one)).comp
      (algebraMap (Away 𝒜 t) (Localization.Away t))) (Away.mk 𝒜 hd k p hp) = κ p := by
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  simpa using Localization.awayLift_mk κ t p 1 (by rw [h, one_mul]) k

/-- The ring homomorphism out of the degree-zero localization `R[x, y, z]/(F)_{(tᵢ)}` induced by
a ring homomorphism `κ` with `κ tᵢ = 1`: the fraction `p / tᵢᵏ` goes to `κ p`. -/
def awayLiftOf {S : Type*} [CommRing S] (κ : coordRingOf W →+* S) (i : Fin 3)
    (h : κ (coordOf W i) = 1) : Away (gradingOf W) (coordOf W i) →+* S :=
  (Localization.awayLift κ _ (h ▸ isUnit_one)).comp
    (algebraMap _ (Localization.Away (coordOf W i)))

/-- `awayLiftOf` sends the fraction `p / tᵢᵏ` to `κ p`. -/
theorem awayLiftOf_mk {S : Type*} [CommRing S] (κ : coordRingOf W →+* S) (i : Fin 3)
    (h : κ (coordOf W i) = 1) (k : ℕ) (p : coordRingOf W) (hp : p ∈ gradingOf W (k • 1)) :
    awayLiftOf W κ i h (Away.mk _ (coordOf_mem W i) k p hp) = κ p := by
  exact awayLift_comp_algebraMap_mk _ κ (coordOf_mem W i) h k p hp

section General

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **A morphism `Spec S ⟶ Proj 𝒜` given by global sections, one of which is `1`, factors through
the standard chart of that section.** If `κ t = 1` for `t` homogeneous of positive degree, then
`AlgebraicGeometry.Proj.fromOfGlobalSections` of `κ` is `Spec` of the induced ring homomorphism
`(A_t)₀ → S`, `p / tᵏ ↦ κ p`, followed by `AlgebraicGeometry.Proj.awayι`. -/
theorem fromOfGlobalSections_eq_SpecMap_awayι {S : Type u} [CommRing S] (κ : A →+* S) {t : A}
    {d : ℕ} (hd : t ∈ 𝒜 d) (h0d : 0 < d) (h : κ t = 1) (hκ) :
    Proj.fromOfGlobalSections 𝒜 ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom.comp κ) hκ =
      Spec.map (CommRingCat.ofHom ((Localization.awayLift κ t (h ▸ isUnit_one)).comp
        (algebraMap (Away 𝒜 t) (Localization.Away t)))) ≫ Proj.awayι 𝒜 t hd h0d := by
  let X := Spec (CommRingCat.of S)
  let f := (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom.comp κ
  have hf1 : f t = 1 := by simp [f, h]
  have hU : X.basicOpen (f t) = ⊤ := by rw [hf1, Scheme.basicOpen_one]
  have : IsIso (X.basicOpen (f t)).ι := by
    rw [hU, ← Scheme.topIso_hom]; infer_instance
  refine (cancel_epi (X.basicOpen (f t)).ι).mp ?_
  rw [Stacks.ProjGlobalSectionsAppTop.ι_comp_fromOfGlobalSections _ _ _ h0d hd,
    ← Proj.basicOpenIsoSpec_inv_ι]
  suffices e : Proj.toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd ≫
      (Proj.basicOpenIsoSpec 𝒜 t hd h0d).hom = (X.basicOpen (f t)).ι ≫
        Spec.map (CommRingCat.ofHom ((Localization.awayLift κ t (h ▸ isUnit_one)).comp
          (algebraMap (Away 𝒜 t) (Localization.Away t)))) by
    rw [← reassoc_of% e, Iso.hom_inv_id_assoc]
  rw [Stacks.ProjGlobalSectionsAppTop.toBasicOpenOfGlobalSections_basicOpenIsoSpec_hom]
  have hι : (X.basicOpen (f t)).ι = (X.basicOpen (f t)).toSpecΓ ≫
      Spec.map (X.presheaf.map (homOfLE le_top).op) ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of S)).inv := by
    rw [← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [hι, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext _ hd
    fun k p hp => ?_)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  rw [Stacks.ProjGlobalSectionsAppTop.projAwayHom_apply_mk_of_mul_eq_one _ f
    hd k p hp (v := 1) (by rw [hf1, map_one, one_mul])]
  simp only [one_pow, mul_one]
  have e := awayLift_comp_algebraMap_mk 𝒜 κ hd h k p hp
  rw [RingHom.comp_apply] at e
  rw [e]
  rfl

end General

/-- The open immersion `Spec R[x, y, z]/(F)_{(tᵢ)} ⟶ E` of the standard chart `D₊(tᵢ)`. -/
def awayιOf (i : Fin 3) : Spec (CommRingCat.of (Away (gradingOf W) (coordOf W i))) ⟶ projOf W :=
  Proj.awayι (gradingOf W) (coordOf W i) (coordOf_mem W i) one_pos

/-- The chart `awayιOf W i` is an open immersion. -/
instance (i : Fin 3) : IsOpenImmersion (awayιOf W i) :=
  inferInstanceAs (IsOpenImmersion (Proj.awayι (gradingOf W) (coordOf W i) _ one_pos))

/-- The standard open `D₊(f)` of the plane cubic, for `f` in its homogeneous coordinate ring. -/
def basicOpenOf (f : coordRingOf W) : (projOf W).Opens := Proj.basicOpen (gradingOf W) f

/-- A point lies in `D₊(f)` when `f` is not in its homogeneous prime. -/
theorem mem_basicOpenOf (f : coordRingOf W) (p : projOf W) :
    p ∈ basicOpenOf W f ↔ f ∉ (p : ProjectiveSpectrum (gradingOf W)).asHomogeneousIdeal :=
  Iff.rfl

/-- The image of the chart `awayιOf W i` is `D₊(tᵢ)`. -/
theorem opensRange_awayιOf (i : Fin 3) : (awayιOf W i).opensRange = basicOpenOf W (coordOf W i) :=
  Proj.opensRange_awayι (gradingOf W) (coordOf W i) _ one_pos

/-- **A point whose `i`-th homogeneous coordinate is `1` factors through the standard chart
`D₊(tᵢ)`**, as `Spec` of the ring homomorphism `awayLiftOf` followed by `awayιOf`. -/
theorem specPoint_eq_awayι {S : Type u} [CommRing S] (κ : coordRingOf W →+* S) (i : Fin 3)
    (h : κ (coordOf W i) = 1) (hκ) :
    specPoint W κ hκ = Spec.map (CommRingCat.ofHom (awayLiftOf W κ i h)) ≫ awayιOf W i :=
  fromOfGlobalSections_eq_SpecMap_awayι _ κ (coordOf_mem W i) one_pos h _

/-! ### Dehomogenization -/

/-- The constants `R → R[x, y, z]/(F)_{(tᵢ)}`. -/
def awayConst (i : Fin 3) : R →+* Away (gradingOf W) (coordOf W i) :=
  (algebraMap (gradingOf W 0) _).comp (toGradingZeroOf W)

/-- The homogeneous coordinates have degree `1 • 1`, the degree of a fraction `tⱼ / tᵢ`. -/
theorem coordOf_mem_smul (j : Fin 3) : coordOf W j ∈ gradingOf W (1 • 1) := by
  simpa using coordOf_mem W j

/-- The affine coordinate `tⱼ / tᵢ` of the chart `D₊(tᵢ)`. -/
def awayCoord (i j : Fin 3) : Away (gradingOf W) (coordOf W i) :=
  Away.mk _ (coordOf_mem W i) 1 (coordOf W j) (coordOf_mem_smul W j)

/-- The affine coordinate `tᵢ / tᵢ` is `1`. -/
theorem awayCoord_self (i : Fin 3) : awayCoord W i i = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [awayCoord]

/-- A constant of the chart `D₊(tᵢ)` is the fraction `a / tᵢ⁰`. -/
theorem awayConst_eq (i : Fin 3) (a : R) :
    awayConst W i a = Away.mk _ (coordOf_mem W i) 0 (Ideal.Quotient.mk _ (MvPolynomial.C a))
      (Stacks.HomogeneousIdeal.mk_mem_quotientGrading _
        (by rw [mem_homogeneousSubmodule]; exact isHomogeneous_C _ _)) := by
  apply HomogeneousLocalization.val_injective
  simp only [awayConst, toGradingZeroOf, HomogeneousLocalization.algebraMap_eq,
    HomogeneousLocalization.fromZeroRingHom, RingHom.comp_apply, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk,
    HomogeneousLocalization.Away.val_mk]
  congr 1

/-- `awayLiftOf` sends the constant `a` to the image of `a`. -/
theorem awayLiftOf_awayConst {S : Type*} [CommRing S] (κ : coordRingOf W →+* S) (i : Fin 3)
    (h : κ (coordOf W i) = 1) (a : R) :
    awayLiftOf W κ i h (awayConst W i a) = κ (Ideal.Quotient.mk _ (MvPolynomial.C a)) := by
  rw [awayConst_eq, awayLiftOf_mk]

/-- `awayLiftOf` sends the affine coordinate `tⱼ / tᵢ` to `κ tⱼ`. -/
theorem awayLiftOf_awayCoord {S : Type*} [CommRing S] (κ : coordRingOf W →+* S) (i : Fin 3)
    (h : κ (coordOf W i) = 1) (j : Fin 3) :
    awayLiftOf W κ i h (awayCoord W i j) = κ (coordOf W j) :=
  awayLiftOf_mk W κ i h 1 _ _

/-- **Dehomogenization.** A homogeneous polynomial `P` of degree `k`, evaluated at the affine
coordinates `tⱼ / tᵢ` of the chart `D₊(tᵢ)`, is the fraction `P / tᵢᵏ`. -/
theorem eval₂_awayCoord (i : Fin 3) {P : MvPolynomial (Fin 3) R} {k : ℕ} (hP : P.IsHomogeneous k)
    (hp : Ideal.Quotient.mk (cubicIdealOf W).toIdeal P ∈ gradingOf W (k • 1)) :
    eval₂ (awayConst W i) (awayCoord W i) P =
      Away.mk _ (coordOf_mem W i) k (Ideal.Quotient.mk _ P) hp := by
  apply HomogeneousLocalization.val_injective
  let u : Localization.Away (coordOf W i) := Localization.mk 1 ⟨coordOf W i, 1, pow_one _⟩
  rw [← HomogeneousLocalization.algebraMap_apply, MvPolynomial.eval₂_comp_left]
  have hv : (⇑(algebraMap (Away (gradingOf W) (coordOf W i)) (Localization.Away (coordOf W i))) ∘
      awayCoord W i) = fun j => u * algebraMap _ _ (coordOf W j) := by
    funext j
    simp only [Function.comp_apply, HomogeneousLocalization.algebraMap_apply, awayCoord,
      HomogeneousLocalization.Away.val_mk, u, ← Localization.mk_one_eq_algebraMap,
      Localization.mk_mul, one_mul, mul_one, pow_one]
  rw [hv, hP.eval₂_const_mul, HomogeneousLocalization.Away.val_mk]
  have hc : (algebraMap (Away (gradingOf W) (coordOf W i)) (Localization.Away (coordOf W i))).comp
      (awayConst W i) = (algebraMap (coordRingOf W) (Localization.Away (coordOf W i))).comp
        ((Ideal.Quotient.mk _).comp MvPolynomial.C) := RingHom.ext fun a => by
    simp only [awayConst, toGradingZeroOf, HomogeneousLocalization.algebraMap_eq,
      HomogeneousLocalization.fromZeroRingHom, RingHom.comp_apply, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, HomogeneousLocalization.algebraMap_apply,
      ← Localization.mk_one_eq_algebraMap]
    rfl
  have h2 := congr($(comp_mk_eq_eval₂Hom W (algebraMap (coordRingOf W)
    (Localization.Away (coordOf W i)))) P)
  simp only [RingHom.comp_apply, coe_eval₂Hom, RingHom.comp_assoc] at h2
  rw [hc, ← h2]
  simp only [u, ← Localization.mk_one_eq_algebraMap, Localization.mk_pow,
    Localization.mk_mul, one_pow, one_mul, mul_one]
  rfl

/-- The affine coordinates of the chart `D₊(tᵢ)` satisfy the homogeneous Weierstrass
equation. -/
theorem awayCoord_equation (i : Fin 3) :
    awayCoord W i 2 * awayCoord W i 1 ^ 2 +
        awayConst W i W.a₁ * awayCoord W i 0 * awayCoord W i 1 * awayCoord W i 2 +
        awayConst W i W.a₃ * awayCoord W i 1 * awayCoord W i 2 ^ 2 -
      (awayCoord W i 0 ^ 3 + awayConst W i W.a₂ * awayCoord W i 0 ^ 2 * awayCoord W i 2 +
        awayConst W i W.a₄ * awayCoord W i 0 * awayCoord W i 2 ^ 2 +
        awayConst W i W.a₆ * awayCoord W i 2 ^ 3) = 0 := by
  have hmem : Ideal.Quotient.mk (cubicIdealOf W).toIdeal (cubicOf W) ∈ gradingOf W (3 • 1) :=
    Stacks.HomogeneousIdeal.mk_mem_quotientGrading _ (by simpa using cubicOf_mem W)
  have h := eval₂_awayCoord W i ((mem_homogeneousSubmodule _ _).mp (cubicOf_mem W)) hmem
  have h0 : Ideal.Quotient.mk (cubicIdealOf W).toIdeal (cubicOf W) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hz : Away.mk (gradingOf W) (coordOf_mem W i) 3 _ hmem = 0 := by
    apply HomogeneousLocalization.val_injective
    simp [h0, Localization.mk_zero]
  rw [hz] at h
  rw [← h]
  simp only [cubicOf, WeierstrassCurve.Projective.polynomial, eval₂_sub, eval₂_add, eval₂_mul,
    eval₂_pow, eval₂_X, eval₂_C]
  ring

/-- **The chart identification.** Let `κ` be a ring homomorphism out of `R[x, y, z]/(F)` with
`κ tᵢ = 1`, and `σ` a ring homomorphism into `R[x, y, z]/(F)_{(tᵢ)}` sending `κ tⱼ` to `tⱼ / tᵢ`
and the constants to the constants. If `σ` is a section of the induced homomorphism
`awayLiftOf W κ i h`, then `awayLiftOf W κ i h` is bijective. -/
theorem awayLiftOf_bijective {S : Type*} [CommRing S] (κ : coordRingOf W →+* S) (i : Fin 3)
    (h : κ (coordOf W i) = 1) (σ : S →+* Away (gradingOf W) (coordOf W i))
    (hσX : ∀ j, σ (κ (coordOf W j)) = awayCoord W i j)
    (hσC : ∀ a, σ (κ (Ideal.Quotient.mk _ (MvPolynomial.C a))) = awayConst W i a)
    (hsec : ∀ s, awayLiftOf W κ i h (σ s) = s) :
    Function.Bijective (awayLiftOf W κ i h) := by
  refine ⟨Function.LeftInverse.injective (g := σ) fun z => ?_, fun s => ⟨σ s, hsec s⟩⟩
  obtain ⟨k, p, hp, rfl⟩ := Away.mk_surjective _ (coordOf_mem W i) z
  rw [awayLiftOf_mk]
  obtain ⟨P, hP, rfl⟩ := (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ p).mp hp
  rw [mem_homogeneousSubmodule, smul_eq_mul, mul_one] at hP
  have hσC' : ((σ.comp κ).comp (Ideal.Quotient.mk _)).comp MvPolynomial.C = awayConst W i :=
    RingHom.ext hσC
  have h1 := congr($(comp_mk_eq_eval₂Hom W (σ.comp κ)) P)
  simp only [RingHom.comp_apply, hσX, hσC', coe_eval₂Hom] at h1
  rw [h1]
  exact eval₂_awayCoord W i hP hp

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass
