module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SplitConicProjection

/-!
# The generic fibre of the split conic is the projective line

Let `K` be a field and `a ∈ K` nonzero. The parametrization `[u : v] ↦ [uv : v² : au²]`
identifies `ℙ¹_K` with the conic `V(T₁T₂ - aT₀²) ⊆ ℙ²_K`; its inverse is the projection
`[T₀ : T₁ : T₂] ↦ [T₀ : T₁]`. Over a discrete valuation ring `R` with fraction field `K` and
uniformizer `π`, the generic fibre of `V(T₁T₂ - πT₀²)` is `V(T₁T₂ - πT₀²)` over `K`, so it is
`ℙ¹_K`.

## Main definitions

* `Stacks.Models.GenusZero.conicHom`: the homomorphism `R[T₀, T₁, T₂]/(T₁T₂ - aT₀²) → C` evaluating
  at a point of the conic.
* `Stacks.Models.GenusZero.parametrization`: the parametrization `ℙ¹_K ⟶ V(T₁T₂ - aT₀²)`.

## Main results

* `Stacks.Models.GenusZero.point_conicHom_eq_of_mul`: rescaling a point of the conic does not
  change the point of `Proj` it determines.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization

universe u

namespace Stacks.Models.GenusZero

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Rescaling evaluations of homogeneous polynomials -/

/-- Rescaling all the coordinates by `μ` rescales a homogeneous form of degree `n` by `μⁿ`. -/
theorem eval₂_mul_of_isHomogeneous {σ R C : Type*} [Finite σ] [CommSemiring R] [CommSemiring C]
    (f : R →+* C) (μ : C) (v : σ → C) {n : ℕ} {p : MvPolynomial σ R} (hp : p.IsHomogeneous n) :
    eval₂ f (fun i => μ * v i) p = μ ^ n * eval₂ f v p := by
  have := Fintype.ofFinite σ
  simp only [eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have := hp (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-! ### Points of the conic -/

section ConicHom

variable {R : Type u} [CommRing R] (a : R) {C : Type u} [CommRing C]

/-- Evaluation along `f : R →+* C` at a point `x` of the conic `x₁x₂ = f(a)x₀²` vanishes on the
ideal `(T₁T₂ - aT₀²)`. -/
theorem eval₂_conicIdeal (f : R →+* C) (x : Fin 3 → C) (hx : x 1 * x 2 = f a * x 0 ^ 2) :
    ∀ p ∈ conicIdeal a, eval₂Hom f x p = 0 := by
  intro p hp
  change p ∈ Ideal.span {conicEquation a} at hp
  rw [Ideal.mem_span_singleton] at hp
  obtain ⟨q, rfl⟩ := hp
  simp [conicEquation, hx]

/-- **The homomorphism `R[T₀, T₁, T₂]/(T₁T₂ - aT₀²) → C` evaluating at a point** `x` of the conic,
for a homomorphism `f : R →+* C` of coefficients. -/
def conicHom (f : R →+* C) (x : Fin 3 → C) (hx : x 1 * x 2 = f a * x 0 ^ 2) :
    MvPolynomial (Fin 3) R ⧸ conicIdeal a →+* C :=
  Ideal.Quotient.lift (conicIdeal a) (eval₂Hom f x) (eval₂_conicIdeal a f x hx)

/-- `conicHom` sends the class of a polynomial `p` to its evaluation `eval₂ f x p`. -/
theorem conicHom_mk (f : R →+* C) (x : Fin 3 → C) (hx : x 1 * x 2 = f a * x 0 ^ 2)
    (p : MvPolynomial (Fin 3) R) :
    conicHom a f x hx (Ideal.Quotient.mk (conicIdeal a) p) = eval₂ f x p :=
  Ideal.Quotient.lift_mk _ _ _

/-- `conicHom` sends the coordinate `Tᵢ` to `xᵢ`. -/
@[simp] theorem conicHom_coord (f : R →+* C) (x : Fin 3 → C)
    (hx : x 1 * x 2 = f a * x 0 ^ 2) (i : Fin 3) :
    conicHom a f x hx (conicCoord a i) = x i := by
  rw [conicCoord, conicHom_mk, eval₂_X]

/-- `conicHom` is natural in the ring of values. -/
theorem comp_conicHom {D : Type u} [CommRing D] (g : C →+* D) (f : R →+* C) (x : Fin 3 → C)
    (hx : x 1 * x 2 = f a * x 0 ^ 2) :
    g.comp (conicHom a f x hx) =
      conicHom a (g.comp f) (fun i => g (x i)) (by simp [← map_mul, ← map_pow, hx]) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
  · simp only [RingHom.comp_apply, conicHom_mk, eval₂_C]
  · simp only [RingHom.comp_apply, conicHom_mk, eval₂_X]

/-- Rescaling the point by `μ` rescales the values in degree `n` by `μⁿ`. -/
theorem conicHom_mul (f : R →+* C) (μ : C) (x : Fin 3 → C) (hx : x 1 * x 2 = f a * x 0 ^ 2)
    (hx' : (μ * x 1) * (μ * x 2) = f a * (μ * x 0) ^ 2) {n : ℕ}
    {b : MvPolynomial (Fin 3) R ⧸ conicIdeal a} (hb : b ∈ conicGrading a n) :
    conicHom a f (fun i => μ * x i) hx' b = μ ^ n * conicHom a f x hx b := by
  obtain ⟨p, hp, rfl⟩ := (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ b).1 hb
  rw [conicHom_mk, conicHom_mk]
  exact eval₂_mul_of_isHomogeneous f μ x ((mem_homogeneousSubmodule _ _).1 hp)

/-- **Rescaling a point of the conic does not change the point of `Proj`.** -/
theorem point_conicHom_eq_of_mul (f : R →+* C) (μ : Cˣ) (x : Fin 3 → C)
    (hx : x 1 * x 2 = f a * x 0 ^ 2) (hx' : (μ * x 1) * (μ * x 2) = f a * (μ * x 0) ^ 2)
    (s s' : Fin 3) (hu : IsUnit (x s)) (hu' : IsUnit (μ * x s')) :
    ProjPoint.point (conicGrading a) (conicHom a f x hx) (conicCoord a s) (conicCoord_mem a s)
        one_pos (by rw [conicHom_coord]; exact hu) =
      ProjPoint.point (conicGrading a) (conicHom a f (fun i => μ * x i) hx') (conicCoord a s')
        (conicCoord_mem a s') one_pos (by rw [conicHom_coord]; exact hu') := by
  have hus' : IsUnit (x s') := by
    have := (μ⁻¹).isUnit.mul hu'
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this
  rw [ProjPoint.point_indep (conicGrading a) _ (conicCoord_mem a s) (conicCoord_mem a s')
    one_pos one_pos _ (by rw [conicHom_coord]; exact hus')]
  exact ProjPoint.point_eq_of_scale _ μ (fun n b hb => conicHom_mul a f μ x hx hx' hb) _ _ _ _ _

/-- `conicHom a f x hx` depends only on `f` and `x`. -/
theorem conicHom_congr {f f' : R →+* C} {x x' : Fin 3 → C} (hf : f = f') (hxx : x = x')
    (hx : x 1 * x 2 = f a * x 0 ^ 2) (hx' : x' 1 * x' 2 = f' a * x' 0 ^ 2) :
    conicHom a f x hx = conicHom a f' x' hx' := by
  subst hf hxx
  rfl

end ConicHom

/-! ### The parametrization `ℙ¹_K ⟶ V(T₁T₂ - aT₀²)` -/

section Parametrization

open Stacks.AlgebraicGeometry.ProjPolyChart

variable {K : Type u} [Field K] (a : K)

/-- The grading of `K[u, v]`. -/
abbrev lineGrading (K : Type u) [Field K] := polyGrading K 1

/-- The fraction `vⱼ / vᵢ` on the chart `D₊(vᵢ)` of `ℙ¹_K`. -/
def lineFrac (i j : Fin 2) : Away (lineGrading K) (X i) :=
  Away.mk (lineGrading K) (X_mem K i) 1 (X j) (by simpa using X_mem K j)

/-- The constants on the chart `D₊(vᵢ)` of `ℙ¹_K`. -/
def lineConst (i : Fin 2) : K →+* Away (lineGrading K) (X i) :=
  (fromZeroRingHom (lineGrading K) _).comp (algebraMap K (lineGrading K 0))

/-- The point of the conic attached to the chart `D₊(vᵢ)`: `(u/v, 1, a(u/v)²)` on `D₊(v)` and
`(v/u, (v/u)², a)` on `D₊(u)`, the parametrization `[u : v] ↦ [uv : v² : au²]` read there. -/
def paramVec : (i : Fin 2) → Fin 3 → Away (lineGrading K) (X i)
  | 0 => ![lineFrac 0 1, lineFrac 0 1 ^ 2, lineConst 0 a]
  | 1 => ![lineFrac 1 0, 1, lineConst 1 a * lineFrac 1 0 ^ 2]

/-- The point `paramVec a i` lies on the conic `T₁T₂ = aT₀²`. -/
theorem paramVec_rel (i : Fin 2) :
    paramVec a i 1 * paramVec a i 2 = lineConst i a * paramVec a i 0 ^ 2 := by
  fin_cases i
  · simp [paramVec]; ring
  · simp [paramVec]

/-- The coordinate of `ℙ²` that is a unit on the image of the chart `D₊(vᵢ)`. -/
def paramS : Fin 2 → Fin 3 := ![2, 1]

variable {a}

/-- For `a ≠ 0`, the coordinate `paramS i` of `paramVec a i` is a unit. -/
theorem isUnit_paramVec (ha : a ≠ 0) (i : Fin 2) : IsUnit (paramVec a i (paramS i)) := by
  fin_cases i
  · exact (isUnit_iff_ne_zero.mpr ha).map (lineConst 0)
  · simp [paramVec, paramS]

/-- The parametrization on the chart `D₊(vᵢ)`. -/
def paramChart (ha : a ≠ 0) (i : Fin 2) :
    Spec (.of (Away (lineGrading K) (X i))) ⟶ conicScheme a :=
  ProjPoint.point (conicGrading a) (conicHom a (lineConst i) (paramVec a i) (paramVec_rel a i))
    (conicCoord a (paramS i)) (conicCoord_mem a _) one_pos
    (by rw [conicHom_coord]; exact isUnit_paramVec ha i)

/-- The inclusion of the chart `D₊(vⱼ)` into `D₊(vᵢvⱼ)`. -/
private abbrev overlapLeft (i j : Fin 2) :=
  awayMap (lineGrading K) (X_mem K j) (rfl : (X i : MvPolynomial (Fin (1 + 1)) K) * X j = X i * X j)

/-- The inclusion of the chart `D₊(vᵢ)` into `D₊(vᵢvⱼ)`. -/
private abbrev overlapRight (i j : Fin 2) :=
  awayMap (lineGrading K) (X_mem K i) (mul_comm (X i : MvPolynomial (Fin (1 + 1)) K) (X j))

/-- On `D₊(vᵢvⱼ)`, the fractions `vⱼ/vᵢ` and `vᵢ/vⱼ` are inverse to each other. -/
private theorem overlapRight_lineFrac_sq_mul (i j : Fin 2) :
    overlapRight (K := K) i j (lineFrac j i) ^ 2 * overlapLeft i j (lineFrac i j) ^ 2 = 1 ∧
    overlapRight (K := K) i j (lineFrac j i) =
      overlapRight i j (lineFrac j i) ^ 2 * overlapLeft i j (lineFrac i j) := by
  obtain ⟨wi, hwi⟩ : ∃ w : Localization.Away ((X i : MvPolynomial (Fin (1 + 1)) K) * X j),
      algebraMap _ _ (X i : MvPolynomial (Fin (1 + 1)) K) * w = 1 :=
    isUnit_iff_exists_inv.mp (isUnit_of_dvd_unit (map_dvd (algebraMap _ _)
      (dvd_mul_right (X i : MvPolynomial (Fin (1 + 1)) K) (X j)))
      (IsLocalization.Away.algebraMap_isUnit _))
  obtain ⟨wj, hwj⟩ : ∃ w : Localization.Away ((X i : MvPolynomial (Fin (1 + 1)) K) * X j),
      algebraMap _ _ (X j : MvPolynomial (Fin (1 + 1)) K) * w = 1 :=
    isUnit_iff_exists_inv.mp (isUnit_of_dvd_unit (map_dvd (algebraMap _ _)
      (dvd_mul_left (X j : MvPolynomial (Fin (1 + 1)) K) (X i)))
      (IsLocalization.Away.algebraMap_isUnit _))
  have hL : (overlapLeft i j (lineFrac i j)).val =
      algebraMap _ _ (X j : MvPolynomial (Fin (1 + 1)) K) * wi := by
    rw [lineFrac, ProjPoint.val_awayMap_mk _ _ _ _ _ _ _ wi hwi, pow_one]
  have hR : (overlapRight i j (lineFrac j i)).val =
      algebraMap _ _ (X i : MvPolynomial (Fin (1 + 1)) K) * wj := by
    rw [lineFrac, ProjPoint.val_awayMap_mk _ _ _ _ _ _ _ wj hwj, pow_one]
  constructor
  · apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
      HomogeneousLocalization.val_one, hL, hR]
    linear_combination (algebraMap _ _ (X i : MvPolynomial (Fin (1 + 1)) K) * wi *
      (algebraMap _ _ (X j : MvPolynomial (Fin (1 + 1)) K) * wj) + 1) *
      ((algebraMap _ _ (X i : MvPolynomial (Fin (1 + 1)) K) * wi) * hwj + hwi)
  · apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, hL, hR]
    linear_combination (-(algebraMap _ _ (X i : MvPolynomial (Fin (1 + 1)) K) * wj *
      (algebraMap _ _ (X i : MvPolynomial (Fin (1 + 1)) K) * wi))) * hwj -
      (algebraMap _ _ (X i : MvPolynomial (Fin (1 + 1)) K) * wj) * hwi

/-- The constants of the two charts agree on `D₊(vᵢvⱼ)`. -/
private theorem overlapLeft_lineConst (i j : Fin 2) (c : K) :
    overlapLeft i j (lineConst i c) = overlapRight i j (lineConst j c) := by
  simp only [lineConst, RingHom.comp_apply, awayMap_fromZeroRingHom]

/-- The charts of the parametrization agree on the overlap, given the comparison of the two
points of the conic up to the unit `(vᵢ/vⱼ)⁻²`. -/
private theorem paramChart_compat_of_comp (ha : a ≠ 0) (i j : Fin 2)
    (hcomp : ∀ k, overlapRight (K := K) i j (lineFrac j i) ^ 2 * overlapLeft i j (paramVec a i k) =
      overlapRight i j (paramVec a j k)) :
    Spec.map (CommRingCat.ofHom (overlapLeft i j)) ≫ paramChart ha i =
      Spec.map (CommRingCat.ofHom (overlapRight i j)) ≫ paramChart ha j := by
  obtain ⟨hprod, -⟩ := overlapRight_lineFrac_sq_mul (K := K) i j
  let μ : (Away (lineGrading K) ((X i : MvPolynomial (Fin (1 + 1)) K) * X j))ˣ :=
    ⟨overlapRight i j (lineFrac j i) ^ 2, overlapLeft i j (lineFrac i j) ^ 2, hprod,
      (mul_comm _ _).trans hprod⟩
  have hf : (overlapLeft (K := K) i j).comp (lineConst i) = (overlapRight i j).comp (lineConst j) :=
    RingHom.ext fun c => overlapLeft_lineConst i j c
  unfold paramChart
  rw [ProjPoint.SpecMap_comp_point, ProjPoint.SpecMap_comp_point,
    ProjPoint.point_congr_ringHom _ (comp_conicHom a (overlapLeft i j) _ _ _) _ _ _ _
      (by rw [conicHom_coord]; exact (isUnit_paramVec ha i).map _),
    ProjPoint.point_congr_ringHom _ (comp_conicHom a (overlapRight i j) _ _ _) _ _ _ _
      (by rw [conicHom_coord]; exact (isUnit_paramVec ha j).map _)]
  have hrel := congrArg (overlapLeft i j) (paramVec_rel a i)
  simp only [map_mul, map_pow] at hrel
  have hx' : ((μ : Away (lineGrading K) ((X i : MvPolynomial (Fin (1 + 1)) K) * X j)) *
      overlapLeft i j (paramVec a i 1)) * (μ * overlapLeft i j (paramVec a i 2)) =
      ((overlapLeft i j).comp (lineConst i)) a * (μ * overlapLeft i j (paramVec a i 0)) ^ 2 := by
    rw [RingHom.comp_apply]
    linear_combination
      (μ : Away (lineGrading K) ((X i : MvPolynomial (Fin (1 + 1)) K) * X j)) ^ 2 * hrel
  have hu' : IsUnit ((μ : Away (lineGrading K) ((X i : MvPolynomial (Fin (1 + 1)) K) * X j)) *
      overlapLeft i j (paramVec a i (paramS j))) := by
    rw [show _ = _ from hcomp _]; exact (isUnit_paramVec ha j).map _
  refine (point_conicHom_eq_of_mul a ((overlapLeft i j).comp (lineConst i)) μ
    (fun k => overlapLeft i j (paramVec a i k)) _ hx' (paramS i) (paramS j)
    ((isUnit_paramVec ha i).map _) hu').trans ?_
  exact ProjPoint.point_congr_ringHom _ (conicHom_congr a hf (funext hcomp) _ _) _ _ _ _ _

/-- The charts of the parametrization agree on the overlap. -/
theorem param_compat (ha : a ≠ 0) : ∀ i j : Fin 2,
    Spec.map (CommRingCat.ofHom (awayMap (lineGrading K) (X_mem K j)
        (rfl : (X i : MvPolynomial (Fin (1 + 1)) K) * X j = X i * X j))) ≫ paramChart ha i =
      Spec.map (CommRingCat.ofHom (awayMap (lineGrading K) (X_mem K i)
        (mul_comm (X i : MvPolynomial (Fin (1 + 1)) K) (X j)))) ≫ paramChart ha j
  | 0, 0 => rfl
  | 1, 1 => rfl
  | 0, 1 => by
    obtain ⟨hprod, hfrac⟩ := overlapRight_lineFrac_sq_mul (K := K) 0 1
    refine paramChart_compat_of_comp ha 0 1 fun k => ?_
    fin_cases k
    · change overlapRight 0 1 (lineFrac 1 0) ^ 2 * overlapLeft 0 1 (lineFrac 0 1) =
        overlapRight 0 1 (lineFrac 1 0)
      exact hfrac.symm
    · change overlapRight 0 1 (lineFrac 1 0) ^ 2 * overlapLeft 0 1 (lineFrac 0 1 ^ 2) =
        overlapRight 0 1 1
      rw [map_pow, hprod, map_one]
    · change overlapRight 0 1 (lineFrac 1 0) ^ 2 * overlapLeft 0 1 (lineConst 0 a) =
        overlapRight 0 1 (lineConst 1 a * lineFrac 1 0 ^ 2)
      rw [overlapLeft_lineConst, map_mul, map_pow]
      ring
  | 1, 0 => by
    obtain ⟨hprod, hfrac⟩ := overlapRight_lineFrac_sq_mul (K := K) 1 0
    refine paramChart_compat_of_comp ha 1 0 fun k => ?_
    fin_cases k
    · change overlapRight 1 0 (lineFrac 0 1) ^ 2 * overlapLeft 1 0 (lineFrac 1 0) =
        overlapRight 1 0 (lineFrac 0 1)
      exact hfrac.symm
    · change overlapRight 1 0 (lineFrac 0 1) ^ 2 * overlapLeft 1 0 1 =
        overlapRight 1 0 (lineFrac 0 1 ^ 2)
      rw [map_one, mul_one, map_pow]
    · change overlapRight 1 0 (lineFrac 0 1) ^ 2 *
        overlapLeft 1 0 (lineConst 1 a * lineFrac 1 0 ^ 2) = overlapRight 1 0 (lineConst 0 a)
      rw [← overlapLeft_lineConst, map_mul, map_pow]
      linear_combination (overlapLeft 1 0 (lineConst 1 a)) * hprod

/-- **The parametrization `[u : v] ↦ [uv : v² : au²]`** of the conic `V(T₁T₂ - aT₀²)` by the
polynomial model `Proj K[u, v]` of `ℙ¹_K`, glued from its two charts. -/
def parametrizationP (ha : a ≠ 0) : AlgebraicGeometry.Proj (lineGrading K) ⟶ conicScheme a :=
  ProjPoint.glue (lineGrading K) (fun i : Fin 2 => (X i : MvPolynomial (Fin (1 + 1)) K))
    (X_mem K) (fun _ => one_pos) (irrelevant_le_span_X K 1) (paramChart ha) (param_compat ha)

/-- The parametrization, on points of the chart `D₊(v)`. -/
theorem point_comp_parametrizationP (ha : a ≠ 0) {L : Type u} [CommRing L]
    (ψ : MvPolynomial (Fin (1 + 1)) K →+* L) (hu : IsUnit (ψ (X 1))) :
    ProjPoint.point (lineGrading K) ψ (X 1) (X_mem K 1) one_pos hu ≫ parametrizationP ha =
      ProjPoint.point (conicGrading a)
        (conicHom a ((ProjPoint.awayEval _ ψ _ hu).comp (lineConst 1))
          (fun k => ProjPoint.awayEval _ ψ _ hu (paramVec a 1 k))
          (by simp only [RingHom.comp_apply, ← map_mul, ← map_pow]; rw [paramVec_rel]))
        (conicCoord a 1) (conicCoord_mem a 1) one_pos
        (by rw [conicHom_coord]; simp [paramVec]) := by
  rw [parametrizationP]
  exact ((ProjPoint.point_comp_glue (lineGrading K)
    (fun i : Fin 2 => (X i : MvPolynomial (Fin (1 + 1)) K))
    (X_mem K) (fun _ => one_pos) (irrelevant_le_span_X K 1) (paramChart ha) (param_compat ha)
    ψ 1 hu).trans (ProjPoint.SpecMap_comp_point _ _ _ _ _ _ _)).trans
    (ProjPoint.point_congr_ringHom _ (comp_conicHom a _ _ _ _) _ _ _ _ _)

/-- `awayEval` on the fraction `vⱼ / vᵢ`. -/
theorem awayEval_lineFrac {L : Type u} [CommRing L] (ψ : MvPolynomial (Fin (1 + 1)) K →+* L)
    (i j : Fin 2) (hu : IsUnit (ψ (X i))) :
    ProjPoint.awayEval _ ψ _ hu (lineFrac i j) = ψ (X j) * ↑hu.unit⁻¹ := by
  rw [lineFrac, ProjPoint.awayEval_mk, pow_one]

/-- `awayEval` on the constants. -/
theorem awayEval_lineConst {L : Type u} [CommRing L] (ψ : MvPolynomial (Fin (1 + 1)) K →+* L)
    (i : Fin 2) (hu : IsUnit (ψ (X i))) (c : K) :
    ProjPoint.awayEval _ ψ _ hu (lineConst i c) = ψ (C c) := by
  rw [lineConst, RingHom.comp_apply, ProjPoint.awayEval_fromZeroRingHom _ _ _ (X_mem K i)]
  rfl

end Parametrization

/-! ### The parametrization is an isomorphism -/

section Iso

open Stacks.AlgebraicGeometry.ProjBaseChange Stacks.AlgebraicGeometry.ProjPolyChart

variable {K : Type u} [Field K] {a : K}

/-- A homomorphism out of `B[T₀, T₁]`, restricted to `ℤ[T₀, T₁]`, is evaluation at the images of
the coordinates. -/
theorem comp_coordinateMap_eq_vecHom {B L : Type u} [CommRing B] [CommRing L]
    (φ : MvPolynomial (Fin (1 + 1)) B →+* L) :
    φ.comp ((polynomialComparison B 1).coordinateMap :
      MvPolynomial (Fin (1 + 1)) (ULift.{u} ℤ) →+* MvPolynomial (Fin (1 + 1)) B) =
      vecHom L (φ (X 0)) (φ (X 1)) := by
  refine MvPolynomial.ringHom_ext (fun n => ?_) (fun i => ?_)
  · simp [(polynomialComparison B 1).coordinateMap_apply, vecHom]
  · fin_cases i <;> simp [(polynomialComparison B 1).coordinateMap_apply, vecHom]

/-- The structure morphism of a scheme to the terminal scheme is separated when the scheme is
separated over an affine scheme. -/
theorem isSeparated_terminal_from {Y : Scheme.{u}} {B : CommRingCat.{u}} (p : Y ⟶ Spec B)
    [IsSeparated p] : IsSeparated (terminal.from Y) := by
  rw [show terminal.from Y = p ≫ terminal.from _ from terminal.hom_ext _ _]
  infer_instance

/-- In a field, the images of the coordinates are units. -/
theorem isUnit_algebraMap_X {σ : Type*} (i : σ) :
    IsUnit (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (X i)) :=
  isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (X_ne_zero i))

/-- **The parametrization followed by the first projection is the identity of `ℙ¹_K`**, read
through the comparison of the polynomial and base-change models. -/
theorem parametrizationP_comp_firstProjection (ha : a ≠ 0) :
    parametrizationP ha ≫ firstProjection a = (polynomialComparison K 1).iso.inv := by
  have : IsSeparated (terminal.from (projectiveSpaceOverRing 1 (.of K))) :=
    isSeparated_terminal_from (projectiveSpaceOverRing 1 (.of K) ↘ Spec (.of K))
  let φ := algebraMap (MvPolynomial (Fin (1 + 1)) K) (FractionRing (MvPolynomial (Fin (1 + 1)) K))
  refine ProjPoint.hom_ext_of_point (lineGrading K) (terminal.from _) (terminal.hom_ext _ _)
    (fun i : Fin 2 => (X i : MvPolynomial (Fin (1 + 1)) K)) (X_mem K) (fun _ => one_pos)
    (irrelevant_le_span_X K 1) φ (fun i => isUnit_algebraMap_X i)
    (fun i => ProjPoint.injective_awayEval_algebraMap _ _ _) (fun i => ?_)
  rw [ProjPoint.point_indep _ φ (X_mem K i) (X_mem K 1) one_pos one_pos
    (isUnit_algebraMap_X i) (isUnit_algebraMap_X 1), ← Category.assoc,
    point_comp_parametrizationP, point_comp_firstProjection, point_comp_iso_inv]
  have hu1 := isUnit_algebraMap_X (K := K) (σ := Fin (1 + 1)) 1
  refine pullback.hom_ext ?_ ?_
  · simp only [pullback.lift_fst]
    congr 2
    ext c
    simp only [RingHom.comp_apply, conicHom_mk, eval₂_C]
    rw [awayEval_lineConst]
    rfl
  · simp only [pullback.lift_snd]
    unfold intPointOf
    rw [ProjPoint.point_congr_ringHom _ (comp_coordinateMap_eq_vecHom φ) _ _ _ _
      (by rw [vecHom_X_one]; exact hu1)]
    refine point_vecHom_eq_of_mul_eq _ ?_ _ _ _ _
    simp only [firstA, firstB, map_one, awayEval_frac, conicHom_coord, paramVec,
      awayEval_lineFrac, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [Units.val_inv_eq_inv_val, IsUnit.unit_spec, inv_one, mul_one]
    have : φ (X 1) ≠ 0 := hu1.ne_zero
    field_simp

/-- The coordinates do not vanish in the homogeneous coordinate ring of the conic: `T₁T₂ - aT₀²`
has degree two and does not divide a coordinate. -/
theorem conicCoord_ne_zero {R : Type u} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {b : R} (hb : b ≠ 0) (i : Fin 3) : conicCoord b i ≠ 0 := by
  intro h
  rw [conicCoord, Ideal.Quotient.eq_zero_iff_mem] at h
  change X i ∈ Ideal.span {conicEquation b} at h
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨q, hq⟩ := h
  have hF : conicEquation b ≠ 0 := (prime_conicEquation hb).ne_zero
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have h1 := congrArg MvPolynomial.totalDegree hq
  rw [totalDegree_mul_of_isDomain hF hq0, totalDegree_X,
    (isHomogeneous_conicEquation b).totalDegree hF] at h1
  omega

/-- **The first projection followed by the parametrization is the identity of the conic.** -/
theorem firstProjection_comp_parametrizationP (ha : a ≠ 0) :
    firstProjection a ≫ (polynomialComparison K 1).iso.hom ≫ parametrizationP ha = 𝟙 _ := by
  have : IsSeparated (terminal.from (conicScheme a)) :=
    isSeparated_terminal_from (conicToSpec a)
  have := isDomain_conicRing ha
  let A := MvPolynomial (Fin 3) K ⧸ conicIdeal a
  let ψ := algebraMap A (FractionRing A)
  have hψ : ∀ i, IsUnit (ψ (conicCoord a i)) := fun i =>
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (conicCoord_ne_zero ha i))
  refine ProjPoint.hom_ext_of_point (conicGrading a) (terminal.from _) (terminal.hom_ext _ _)
    (conicCoord a) (conicCoord_mem a) (fun _ => one_pos) (irrelevant_le_span_mk_X _) ψ hψ
    (fun i => ProjPoint.injective_awayEval_algebraMap _ _ _) (fun i => ?_)
  rw [ProjPoint.point_indep _ ψ (conicCoord_mem a i) (conicCoord_mem a 1) one_pos one_pos
    (hψ i) (hψ 1), Category.comp_id, ← Category.assoc, point_comp_firstProjection]
  let x0 := ProjPoint.awayEval _ ψ _ (hψ 1) (firstA a 1)
  let f := ψ.comp ((Ideal.Quotient.mk (conicIdeal a)).comp C)
  let φ' : MvPolynomial (Fin (1 + 1)) K →+* FractionRing A := eval₂Hom f ![x0, 1]
  have hφ'1 : IsUnit (φ' (X 1)) := by simp [φ']
  have hlift := point_comp_iso_inv K φ' 1 hφ'1
  have hlift' : pullback.lift (Spec.map (CommRingCat.ofHom f))
      (intPointOf (vecHom (FractionRing A) x0 (ProjPoint.awayEval _ ψ _ (hψ 1) (firstB a 1)))
        (firstS 1) (by rw [← comp_vecHom, RingHom.comp_apply]; exact (isUnit_first a 1).map _))
      (terminal.hom_ext _ _) =
      ProjPoint.point (lineGrading K) φ' (X 1) (X_mem K 1) one_pos hφ'1 ≫
        (polynomialComparison K 1).iso.inv := by
    rw [hlift]
    refine pullback.hom_ext ?_ ?_
    · simp only [pullback.lift_fst]
      congr 2
      ext c
      simp [φ']
    · simp only [pullback.lift_snd]
      unfold intPointOf
      refine ProjPoint.point_congr_ringHom _ ?_ _ _ _ _ _
      rw [comp_coordinateMap_eq_vecHom]
      simp [φ', firstB]
  rw [hlift', Category.assoc, Iso.inv_hom_id_assoc, point_comp_parametrizationP]
  have hψconic : ψ = conicHom a f (fun k => ψ (conicCoord a k))
      (by rw [← map_mul, ← map_pow, conic_relation, map_mul, map_pow]; rfl) := by
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_))
    · simp [f, conicHom_mk]
    · simp only [RingHom.comp_apply, conicHom_mk, eval₂_X]
  have hrel : ψ (conicCoord a 1) * ψ (conicCoord a 2) = f a * ψ (conicCoord a 0) ^ 2 := by
    rw [← map_mul, ← map_pow, conic_relation, map_mul, map_pow]; rfl
  let μ := (hψ 1).unit⁻¹
  have hx' : ((μ : FractionRing A) * ψ (conicCoord a 1)) * (μ * ψ (conicCoord a 2)) =
      f a * (μ * ψ (conicCoord a 0)) ^ 2 := by
    linear_combination (μ : FractionRing A) ^ 2 * hrel
  have hne : ψ (conicCoord a 1) ≠ 0 := (hψ 1).ne_zero
  have hμ : (μ : FractionRing A) = (ψ (conicCoord a 1))⁻¹ := by
    simp [μ, Units.val_inv_eq_inv_val]
  have hx0 : x0 = ψ (conicCoord a 0) * (ψ (conicCoord a 1))⁻¹ := by
    simp only [x0, firstA]
    rw [awayEval_frac, Units.val_inv_eq_inv_val, IsUnit.unit_spec]
  have hf : (ProjPoint.awayEval (lineGrading K) φ' (X 1) hφ'1).comp (lineConst 1) = f := by
    ext c
    rw [RingHom.comp_apply, awayEval_lineConst]
    simp [φ']
  have hxx : (fun k => ProjPoint.awayEval (lineGrading K) φ' (X 1) hφ'1 (paramVec a 1 k)) =
      fun k => (μ : FractionRing A) * ψ (conicCoord a k) := by
    have hφ'X0 : φ' (X 0) = x0 := by simp [φ']
    have hφ'X1 : φ' (X 1) = 1 := by simp [φ']
    have hinv1 : (↑hφ'1.unit⁻¹ : FractionRing A) = 1 := by
      simp [hφ'X1]
    funext k
    fin_cases k
    · change ProjPoint.awayEval _ φ' _ hφ'1 (lineFrac 1 0) =
        (μ : FractionRing A) * ψ (conicCoord a 0)
      rw [awayEval_lineFrac, hinv1, mul_one, hφ'X0, hx0, hμ]
      ring
    · change ProjPoint.awayEval _ φ' _ hφ'1 1 = (μ : FractionRing A) * ψ (conicCoord a 1)
      rw [map_one, hμ, inv_mul_cancel₀ hne]
    · change ProjPoint.awayEval _ φ' _ hφ'1 (lineConst 1 a * lineFrac 1 0 ^ 2) =
        (μ : FractionRing A) * ψ (conicCoord a 2)
      rw [map_mul, map_pow, awayEval_lineFrac, hinv1, mul_one, hφ'X0, hx0, hμ,
        awayEval_lineConst]
      have hfa : φ' (C a) = f a := by simp [φ']
      rw [hfa]
      have hinv : ψ (conicCoord a 1) * (ψ (conicCoord a 1))⁻¹ = 1 := mul_inv_cancel₀ hne
      linear_combination (-((ψ (conicCoord a 1))⁻¹ * (ψ (conicCoord a 1))⁻¹)) * hrel +
        ((ψ (conicCoord a 1))⁻¹ * ψ (conicCoord a 2)) * hinv
  rw [ProjPoint.point_congr_ringHom _ hψconic _ _ _ _ (by rw [conicHom_coord]; exact hψ 1)]
  refine Eq.trans ?_ (point_conicHom_eq_of_mul a f μ _ _ hx' 1 1 (hψ 1)
    (by rw [hμ, inv_mul_cancel₀ hne]; exact isUnit_one)).symm
  exact ProjPoint.point_congr_ringHom _ (conicHom_congr a hf hxx _ _) _ _ _ _ _

end Iso

/-! ### Change of coefficients -/

section BaseChange

open PlaneCurveModel

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (π : R)

/-- The image of `T₁T₂ - πT₀²` under `φ` lies in the ideal `(T₁T₂ - φ(π)T₀²)`. -/
theorem map_conicEquation_mem :
    (GradedRingHom.id (homogeneousSubmodule (Fin 3) S)) (MvPolynomial.map φ (conicEquation π)) ∈
      (equationIdeal (conicEquation (φ π)) (isHomogeneous_conicEquation (φ π))).toIdeal := by
  change MvPolynomial.map φ (conicEquation π) ∈ Ideal.span {conicEquation (φ π)}
  rw [map_conicEquation]
  exact Ideal.subset_span rfl

/-- The form `T₁T₂ - φ(π)T₀²` lies in the ideal generated by the image of `T₁T₂ - πT₀²`. -/
theorem conicEquation_map_mem :
    (GradedRingHom.id (homogeneousSubmodule (Fin 3) S)) (conicEquation (φ π)) ∈
      (equationIdeal (MvPolynomial.map φ (conicEquation π))
        ((isHomogeneous_conicEquation π).map φ)).toIdeal := by
  change conicEquation (φ π) ∈ Ideal.span {MvPolynomial.map φ (conicEquation π)}
  rw [map_conicEquation]
  exact Ideal.subset_span rfl

/-- The identification of the conic `V(T₁T₂ - φ(π)T₀²)` with the base change
`V(φ(T₁T₂ - πT₀²))`. -/
def conicChange : conicScheme (φ π) ⟶
    scheme (MvPolynomial.map φ (conicEquation π)) ((isHomogeneous_conicEquation π).map φ) :=
  changeMap (GradedRingHom.id _) (GradedRingHom.id _) rfl (map_conicEquation_mem φ π)
    (conicEquation_map_mem φ π)

/-- The identification `conicChange φ π` is an isomorphism. -/
instance : IsIso (conicChange φ π) :=
  isIso_changeMap _ _ rfl rfl _ _

/-- The image of `T₁T₂ - πT₀²` under the graded map induced by `φ` lies in the ideal
`(T₁T₂ - φ(π)T₀²)`. -/
theorem polyGradedMap_conicEquation_mem :
    Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) φ (conicEquation π) ∈
      (equationIdeal (conicEquation (φ π)) (isHomogeneous_conicEquation (φ π))).toIdeal := by
  change MvPolynomial.map φ (conicEquation π) ∈ Ideal.span {conicEquation (φ π)}
  rw [map_conicEquation]
  exact Ideal.subset_span rfl

/-- The change of coefficients `R[T]/(T₁T₂ - πT₀²) → S[T]/(T₁T₂ - φ(π)T₀²)`. -/
abbrev baseHom : conicGrading π →+*ᵍ conicGrading (φ π) :=
  PlaneCurveModel.coordHom (Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) φ)
    (polyGradedMap_conicEquation_mem φ π)

/-- `baseHom φ π` is the change of coefficients `mapHom` followed by the identification of
`φ(T₁T₂ - πT₀²)` with `T₁T₂ - φ(π)T₀²`. -/
theorem baseHom_eq :
    baseHom φ π = (PlaneCurveModel.coordHom (GradedRingHom.id _) (map_conicEquation_mem φ π)).comp
      (mapHom (conicEquation π) (isHomogeneous_conicEquation π) φ) := by
  refine GradedRingHom.ext fun y => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

/-- The irrelevant ideal over `S` is contained in the image of the irrelevant ideal over `R`
under `baseHom φ π`. -/
theorem irrelevant_le_map_baseHom :
    HomogeneousIdeal.irrelevant (conicGrading (φ π)) ≤
      (HomogeneousIdeal.irrelevant (conicGrading π)).map (baseHom φ π) := by
  rw [baseHom_eq]
  exact HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_mapHom _ _ φ)
    (irrelevant_le_map_coordHom _ _ rfl (map_conicEquation_mem φ π) (conicEquation_map_mem φ π))

/-- **The change of coefficients `V(T₁T₂ - φ(π)T₀²) ⟶ V(T₁T₂ - πT₀²)`** along `φ : R →+* S`. -/
def baseConic : conicScheme (φ π) ⟶ conicScheme π :=
  Proj.map (baseHom φ π) (irrelevant_le_map_baseHom φ π)

/-- `baseConic φ π` is the identification `conicChange φ π` followed by the base change map
`mapMap`. -/
theorem baseConic_eq :
    baseConic φ π =
      conicChange φ π ≫ mapMap (conicEquation π) (isHomogeneous_conicEquation π) φ := by
  unfold baseConic conicChange PlaneCurveModel.changeMap mapMap
  rw [← Proj.map_comp]
  congr 1
  exact baseHom_eq φ π

/-- `conicChange φ π` commutes with the structure morphisms to `Spec S`. -/
theorem conicChange_toSpec :
    conicChange φ π ≫ toSpec (MvPolynomial.map φ (conicEquation π))
      ((isHomogeneous_conicEquation π).map φ) = conicToSpec (φ π) :=
  changeMap_toSpec _ _ rfl _ _ (fun _ => rfl)

/-- `baseConic φ π` lies over `Spec φ : Spec S ⟶ Spec R`. -/
theorem baseConic_toSpec :
    baseConic φ π ≫ conicToSpec π = conicToSpec (φ π) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [baseConic_eq, Category.assoc, mapMap_toSpec, ← Category.assoc, conicChange_toSpec]

/-- **The change of coefficients, on points.** -/
theorem point_comp_baseConic {L : Type u} [CommRing L] (f : S →+* L) (x : Fin 3 → L)
    (hx : x 1 * x 2 = f (φ π) * x 0 ^ 2) (s : Fin 3) (hu : IsUnit (x s)) :
    ProjPoint.point (conicGrading (φ π)) (conicHom (φ π) f x hx) (conicCoord (φ π) s)
        (conicCoord_mem _ s) one_pos (by rw [conicHom_coord]; exact hu) ≫ baseConic φ π =
      ProjPoint.point (conicGrading π) (conicHom π (f.comp φ) x
        (by rw [RingHom.comp_apply]; exact hx)) (conicCoord π s)
        (conicCoord_mem _ s) one_pos (by rw [conicHom_coord]; exact hu) := by
  have hmt : baseHom φ π (conicCoord π s) = conicCoord (φ π) s := by
    change Ideal.Quotient.mk _ (MvPolynomial.map φ (X s)) = _
    rw [map_X]
  have hring : (conicHom (φ π) f x hx).comp (baseHom φ π :
      MvPolynomial (Fin 3) R ⧸ conicIdeal π →+* MvPolynomial (Fin 3) S ⧸ conicIdeal (φ π)) =
      conicHom π (f.comp φ) x (by rw [RingHom.comp_apply]; exact hx) := by
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
    · simp only [RingHom.comp_apply, conicHom_mk, eval₂_C]
      change conicHom (φ π) f x hx (Ideal.Quotient.mk _ (MvPolynomial.map φ (C r))) = _
      rw [map_C, conicHom_mk, eval₂_C]
    · simp only [RingHom.comp_apply, conicHom_mk, eval₂_X]
      change conicHom (φ π) f x hx (Ideal.Quotient.mk _ (MvPolynomial.map φ (X i))) = _
      rw [map_X, conicHom_mk, eval₂_X]
  rw [ProjPoint.point_congr _ _ hmt.symm _ ((baseHom φ π).2 (conicCoord_mem π s)) _ _
    (by rw [hmt, conicHom_coord]; exact hu), baseConic, ProjPoint.point_comp_map]
  exact ProjPoint.point_congr_ringHom _ hring _ _ _ _ _

end BaseChange

end Stacks.Models.GenusZero

end
