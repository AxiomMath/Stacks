module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineUnimodularPoints

/-!
# Möbius automorphisms of the projective line over a ring

Let `R` be a commutative ring and `M = (a b; c d)` a two-by-two matrix over `R` with invertible
determinant. The *Möbius map* `μ_M : ℙ¹_R ⟶ ℙ¹_R` is `[s : t] ↦ [a s + b t : c s + d t]`: on the
first chart it is the point `[a x + b : c x + d]` of `Spec R[x]`, and on the second chart the
point `[a + b y : c + d y]` of `Spec R[y]`. These maps satisfy `μ_N ≫ μ_M = μ_{M N}` and
`μ_1 = 𝟙`, so `μ_M` is an automorphism of `ℙ¹_R` over `R`; moreover `μ_M = μ_N` if and only if
`N = w M` for a unit `w`, and the construction commutes with base change.

Conversely, every automorphism of `ℙ¹_R` over `R` which sends the section `∞` to a point
`[a : c]` with `a, c ∈ R` is a Möbius map.

## Main definitions

* `AlgebraicGeometry.projectiveLineMobius`: the Möbius map `μ_M`.
* `AlgebraicGeometry.projectiveLineMobiusIso`: `μ_M` as an automorphism of `ℙ¹_R`.

## Main results

* `AlgebraicGeometry.projectiveLineHomogeneousPoint_comp_projectiveLineMobius`: `[s : t] ≫ μ_M` is
  `[a s + b t : c s + d t]`.
* `AlgebraicGeometry.projectiveLineMobius_comp`, `AlgebraicGeometry.projectiveLineMobius_one`:
  the group law.
* `AlgebraicGeometry.projectiveLineMobius_smul`: scalar multiples act alike.
* `AlgebraicGeometry.projectiveLineMobius_eq_iff`: `μ_M = μ_N` if and only if `N = w M` for a
  unit `w`.
* `AlgebraicGeometry.projectiveLineMap_comp_projectiveLineMobius`: compatibility with base
  change.
* `AlgebraicGeometry.exists_eq_projectiveLineMobius`: **the classification**: an automorphism of
  `ℙ¹_R` over `R` sending `∞` to a point `[a : c]` with `a, c ∈ R` is a Möbius map.

## References

* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Polynomial

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R]

/-! ### Matrices acting on pairs -/

section Pairs

variable {B : Type u} [CommRing B] (f : R →+* B) (M : Matrix (Fin 2) (Fin 2) R)

/-- The first entry `a s + b t` of the image of a pair `(s, t)` under `M = (a b; c d)`. -/
abbrev mobiusFst (s t : B) : B := f (M 0 0) * s + f (M 0 1) * t

/-- The second entry `c s + d t` of the image of a pair `(s, t)` under `M = (a b; c d)`. -/
abbrev mobiusSnd (s t : B) : B := f (M 1 0) * s + f (M 1 1) * t

variable {M}

/-- An invertible matrix sends unimodular pairs to unimodular pairs. -/
theorem isCoprime_mobius (hM : IsUnit M.det) {s t : B} (h : IsCoprime s t) :
    IsCoprime (mobiusFst f M s t) (mobiusSnd f M s t) := by
  obtain ⟨α, β, hαβ⟩ := h
  obtain ⟨w, hw⟩ : ∃ w : B, w * f M.det = 1 := ⟨_, (hM.map f).val_inv_mul⟩
  rw [Matrix.det_fin_two, map_sub, map_mul, map_mul] at hw
  refine ⟨w * (α * f (M 1 1) - β * f (M 1 0)), w * (β * f (M 0 0) - α * f (M 0 1)), ?_⟩
  linear_combination (w * (f (M 0 0) * f (M 1 1) - f (M 0 1) * f (M 1 0))) * hαβ + hw

/-- The first entry of the image under `N` and then `M` is the first entry of the image under
`M * N`. -/
theorem mobiusFst_mul (N : Matrix (Fin 2) (Fin 2) R) (s t : B) :
    mobiusFst f M (mobiusFst f N s t) (mobiusSnd f N s t) = mobiusFst f (M * N) s t := by
  simp only [mobiusFst, mobiusSnd, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]
  ring

/-- The second entry of the image under `N` and then `M` is the second entry of the image under
`M * N`. -/
theorem mobiusSnd_mul (N : Matrix (Fin 2) (Fin 2) R) (s t : B) :
    mobiusSnd f M (mobiusFst f N s t) (mobiusSnd f N s t) = mobiusSnd f (M * N) s t := by
  simp only [mobiusFst, mobiusSnd, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]
  ring

end Pairs

/-- Equal pairs give equal points. -/
theorem projectiveLineHomogeneousPoint_congr {B : Type u} [CommRing B] (f : R →+* B) {u v u' v' : B}
    (h : IsCoprime u v) (h' : IsCoprime u' v') (hu : u = u') (hv : v = v') :
    projectiveLineHomogeneousPoint f u v h = projectiveLineHomogeneousPoint f u' v' h' := by
  subst hu hv
  rfl

/-! ### The Möbius map -/

/-- Evaluating a constant polynomial with `eval₂RingHom g r` applies `g` to it. -/
theorem eval₂RingHom_comp_C {B : Type u} [CommRing B] (g : R →+* B) (r : B) :
    (eval₂RingHom g r).comp C = g :=
  RingHom.ext fun a ↦ by simp

variable {M : Matrix (Fin 2) (Fin 2) R} (hM : IsUnit M.det)

/-- The points `[a x + b : c x + d]` and `[a + b y : c + d y]` agree on the overlap of the two
charts. -/
theorem projectiveLineMobius_overlap :
    projectiveLinePuncturedChart R ≫
        projectiveLineHomogeneousPoint C (mobiusFst C M X 1) (mobiusSnd C M X 1)
          (isCoprime_mobius C hM isCoprime_one_right) =
      Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate R).toRingHom) ≫
        projectiveLineHomogeneousPoint C (mobiusFst C M 1 X) (mobiusSnd C M 1 X)
          (isCoprime_mobius C hM isCoprime_one_left) := by
  rw [projectiveLinePuncturedChart, Spec_map_comp_projectiveLineHomogeneousPoint,
    Spec_map_comp_projectiveLineHomogeneousPoint]
  have hC : (Polynomial.toLaurent (R := R)).comp C =
      (projectiveLineOverlapInverseCoordinate R).toRingHom.comp C :=
    RingHom.ext fun a ↦ by
      simp [projectiveLineOverlapInverseCoordinate, LaurentPolynomial.algebraMap_apply]
  rw [hC]
  apply projectiveLineHomogeneousPoint_eq_of_mul_eq_mul
  have h1 : (LaurentPolynomial.T 1 : LaurentPolynomial R) * LaurentPolynomial.T (-1) = 1 := by
    rw [← LaurentPolynomial.T_add]
    exact LaurentPolynomial.T_zero
  simp only [mobiusFst, mobiusSnd, map_add, map_mul, map_one, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    projectiveLineOverlapInverseCoordinate, aeval_X, aeval_C, LaurentPolynomial.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]
  linear_combination (LaurentPolynomial.C (M 0 0) * LaurentPolynomial.C (M 1 1) -
    LaurentPolynomial.C (M 0 1) * LaurentPolynomial.C (M 1 0)) * h1

/-- **The Möbius map `[s : t] ↦ [a s + b t : c s + d t]`** of a two-by-two matrix
`M = (a b; c d)` with invertible determinant: on the first chart the point `[a x + b : c x + d]`,
on the second chart the point `[a + b y : c + d y]`. -/
def projectiveLineMobius : projectiveLine R ⟶ projectiveLine R :=
  projectiveLineDesc
    (projectiveLineHomogeneousPoint C (mobiusFst C M X 1) (mobiusSnd C M X 1)
      (isCoprime_mobius C hM isCoprime_one_right))
    (projectiveLineHomogeneousPoint C (mobiusFst C M 1 X) (mobiusSnd C M 1 X)
      (isCoprime_mobius C hM isCoprime_one_left))
    (projectiveLineMobius_overlap hM)

/-- On the first chart, the Möbius map is the point `[a x + b : c x + d]`. -/
@[reassoc (attr := simp)]
theorem projectiveLineXChart_comp_projectiveLineMobius :
    projectiveLineXChart R ≫ projectiveLineMobius hM =
      projectiveLineHomogeneousPoint C (mobiusFst C M X 1) (mobiusSnd C M X 1)
        (isCoprime_mobius C hM isCoprime_one_right) :=
  projectiveLineXChart_comp_desc _ _ _

/-- On the second chart, the Möbius map is the point `[a + b y : c + d y]`. -/
@[reassoc (attr := simp)]
theorem projectiveLineYChart_comp_projectiveLineMobius :
    projectiveLineYChart R ≫ projectiveLineMobius hM =
      projectiveLineHomogeneousPoint C (mobiusFst C M 1 X) (mobiusSnd C M 1 X)
        (isCoprime_mobius C hM isCoprime_one_left) :=
  projectiveLineYChart_comp_desc _ _ _

/-- **A Möbius map sends `[s : t]` to `[a s + b t : c s + d t]`.** -/
@[reassoc (attr := simp)]
theorem projectiveLineHomogeneousPoint_comp_projectiveLineMobius {B : Type u} [CommRing B]
    (f : R →+* B)
    {s t : B} (h : IsCoprime s t) :
    projectiveLineHomogeneousPoint f s t h ≫ projectiveLineMobius hM =
      projectiveLineHomogeneousPoint f (mobiusFst f M s t) (mobiusSnd f M s t)
          (isCoprime_mobius f hM h) := by
  refine hom_ext_of_isCoprime h (fun φ hs ↦ ?_) (fun φ ht ↦ ?_)
  · have hr := mul_isUnit_unit_inv_mul hs (φ t)
    rw [← Category.assoc, Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left h φ hs _ hr,
      projectiveLineYPoint, Category.assoc, projectiveLineYChart_comp_projectiveLineMobius,
      Spec_map_comp_projectiveLineHomogeneousPoint, Spec_map_comp_projectiveLineHomogeneousPoint,
          eval₂RingHom_comp_C]
    apply projectiveLineHomogeneousPoint_eq_of_mul_eq_mul
    simp only [mobiusFst, mobiusSnd, coe_eval₂RingHom, eval₂_C, eval₂_X, eval₂_one, map_add,
      map_mul, RingHom.coe_comp, Function.comp_apply]
    linear_combination (φ (f (M 0 1)) * φ (f (M 1 0)) - φ (f (M 0 0)) * φ (f (M 1 1))) * hr
  · have hr := mul_isUnit_unit_inv_mul ht (φ s)
    rw [← Category.assoc, Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right h φ ht _ hr,
      projectiveLineXPoint, Category.assoc, projectiveLineXChart_comp_projectiveLineMobius,
      Spec_map_comp_projectiveLineHomogeneousPoint, Spec_map_comp_projectiveLineHomogeneousPoint,
          eval₂RingHom_comp_C]
    apply projectiveLineHomogeneousPoint_eq_of_mul_eq_mul
    simp only [mobiusFst, mobiusSnd, coe_eval₂RingHom, eval₂_C, eval₂_X, eval₂_one, map_add,
      map_mul, RingHom.coe_comp, Function.comp_apply]
    linear_combination (φ (f (M 0 0)) * φ (f (M 1 1)) - φ (f (M 0 1)) * φ (f (M 1 0))) * hr

/-- Morphisms out of `ℙ¹_R` are determined by their composites with the points `[x : 1]` and
`[1 : y]`. -/
theorem projectiveLine_hom_ext_point {Y : Scheme.{u}} {g h : projectiveLine R ⟶ Y}
    (hX : projectiveLineHomogeneousPoint (C : R →+* R[X]) X 1 isCoprime_one_right ≫ g =
      projectiveLineHomogeneousPoint (C : R →+* R[X]) X 1 isCoprime_one_right ≫ h)
    (hY : projectiveLineHomogeneousPoint (C : R →+* R[X]) 1 X isCoprime_one_left ≫ g =
      projectiveLineHomogeneousPoint (C : R →+* R[X]) 1 X isCoprime_one_left ≫ h) : g = h := by
  rw [projectiveLineHomogeneousPoint_X_one] at hX
  rw [projectiveLineHomogeneousPoint_one_X] at hY
  exact projectiveLine_hom_ext hX hY

/-- **The group law**: `μ_N` followed by `μ_M` is `μ_{M N}`. -/
theorem projectiveLineMobius_comp {N : Matrix (Fin 2) (Fin 2) R} (hN : IsUnit N.det)
    (hMN : IsUnit (M * N).det) :
    projectiveLineMobius hN ≫ projectiveLineMobius hM = projectiveLineMobius hMN := by
  refine projectiveLine_hom_ext_point ?_ ?_ <;>
  · rw [projectiveLineHomogeneousPoint_comp_projectiveLineMobius_assoc,
      projectiveLineHomogeneousPoint_comp_projectiveLineMobius,
      projectiveLineHomogeneousPoint_comp_projectiveLineMobius]
    exact projectiveLineHomogeneousPoint_congr _ _ _ (mobiusFst_mul _ _ _ _) (mobiusSnd_mul _ _ _ _)

/-- **The identity matrix acts as the identity.** -/
theorem projectiveLineMobius_one (h1 : IsUnit (1 : Matrix (Fin 2) (Fin 2) R).det) :
    projectiveLineMobius h1 = 𝟙 _ := by
  refine projectiveLine_hom_ext_point ?_ ?_ <;>
  · rw [projectiveLineHomogeneousPoint_comp_projectiveLineMobius, Category.comp_id]
    exact projectiveLineHomogeneousPoint_congr _ _ _ (by simp [mobiusFst])
      (by simp [mobiusSnd])

/-- Scalar multiples of a matrix send a point to the same point. -/
theorem projectiveLineHomogeneousPoint_mobius_smul {B : Type u} [CommRing B] (f : R →+* B) {w : R}
    (hw : IsUnit w) (hwM : IsUnit (w • M).det) {s t : B} (h : IsCoprime s t) :
    projectiveLineHomogeneousPoint f (mobiusFst f (w • M) s t) (mobiusSnd f (w • M) s t)
        (isCoprime_mobius f hwM h) =
      projectiveLineHomogeneousPoint f (mobiusFst f M s t) (mobiusSnd f M s t)
          (isCoprime_mobius f hM h) := by
  have e1 : mobiusFst f (w • M) s t = f w * mobiusFst f M s t := by
    simp only [mobiusFst, Matrix.smul_apply, smul_eq_mul, map_mul]; ring
  have e2 : mobiusSnd f (w • M) s t = f w * mobiusSnd f M s t := by
    simp only [mobiusSnd, Matrix.smul_apply, smul_eq_mul, map_mul]; ring
  rw [projectiveLineHomogeneousPoint_congr f _
      (by rw [← e1, ← e2]; exact isCoprime_mobius f hwM h) e1 e2]
  exact projectiveLineHomogeneousPoint_smul _ (hw.map f) _

/-- **Scalar multiples of a matrix act alike.** -/
theorem projectiveLineMobius_smul {w : R} (hw : IsUnit w) (hwM : IsUnit (w • M).det) :
    projectiveLineMobius hwM = projectiveLineMobius hM := by
  refine projectiveLine_hom_ext_point ?_ ?_
  · rw [projectiveLineHomogeneousPoint_comp_projectiveLineMobius,
      projectiveLineHomogeneousPoint_comp_projectiveLineMobius]
    exact projectiveLineHomogeneousPoint_mobius_smul hM _ hw hwM isCoprime_one_right
  · rw [projectiveLineHomogeneousPoint_comp_projectiveLineMobius,
      projectiveLineHomogeneousPoint_comp_projectiveLineMobius]
    exact projectiveLineHomogeneousPoint_mobius_smul hM _ hw hwM isCoprime_one_left

/-- **A Möbius map lies over `Spec R`.** -/
@[reassoc (attr := simp)]
theorem projectiveLineMobius_comp_structureMorphism :
    projectiveLineMobius hM ≫ (projectiveLine R ↘ Spec (.of R)) =
      projectiveLine R ↘ Spec (.of R) := by
  refine projectiveLine_hom_ext ?_ ?_
  · rw [projectiveLineXChart_comp_projectiveLineMobius_assoc,
      projectiveLineHomogeneousPoint_comp_structureMorphism,
          projectiveLineXChart_comp_structureMorphism]
  · rw [projectiveLineYChart_comp_projectiveLineMobius_assoc,
      projectiveLineHomogeneousPoint_comp_structureMorphism,
          projectiveLineYChart_comp_structureMorphism]

/-- **Möbius maps are compatible with base change**: for `g : R ⟶ S`, the square formed by
`μ_M`, `μ_{g M}` and `ℙ¹_S ⟶ ℙ¹_R` commutes. -/
theorem projectiveLineMap_comp_projectiveLineMobius {S : Type u} [CommRing S] (g : R →+* S)
    (hgM : IsUnit (M.map g).det) :
    projectiveLineMap g ≫ projectiveLineMobius hM =
      projectiveLineMobius hgM ≫ projectiveLineMap g := by
  refine projectiveLine_hom_ext_point ?_ ?_ <;>
  · rw [projectiveLineHomogeneousPoint_comp_projectiveLineMap_assoc,
      projectiveLineHomogeneousPoint_comp_projectiveLineMobius_assoc,
      projectiveLineHomogeneousPoint_comp_projectiveLineMobius,
      projectiveLineHomogeneousPoint_comp_projectiveLineMap]
    exact projectiveLineHomogeneousPoint_congr _ _ _ (by simp [mobiusFst]) (by simp [mobiusSnd])

/-- Equal matrices give equal Möbius maps. -/
theorem projectiveLineMobius_congr {N : Matrix (Fin 2) (Fin 2) R} (hN : IsUnit N.det)
    (h : M = N) : projectiveLineMobius hM = projectiveLineMobius hN := by
  subst h
  rfl

include hM in
/-- **The Möbius automorphism** `μ_M` of `ℙ¹_R`, with inverse `μ_{M⁻¹}`. -/
def projectiveLineMobiusIso : projectiveLine R ≅ projectiveLine R where
  hom := projectiveLineMobius hM
  inv := projectiveLineMobius (Matrix.isUnit_nonsing_inv_det _ hM)
  hom_inv_id := by
    have h1 : IsUnit (1 : Matrix (Fin 2) (Fin 2) R).det := by simp
    rw [projectiveLineMobius_comp _ _ (by rw [Matrix.nonsing_inv_mul M hM]; exact h1),
      projectiveLineMobius_congr _ h1 (Matrix.nonsing_inv_mul M hM), projectiveLineMobius_one]
  inv_hom_id := by
    have h1 : IsUnit (1 : Matrix (Fin 2) (Fin 2) R).det := by simp
    rw [projectiveLineMobius_comp _ _ (by rw [Matrix.mul_nonsing_inv M hM]; exact h1),
      projectiveLineMobius_congr _ h1 (Matrix.mul_nonsing_inv M hM), projectiveLineMobius_one]

/-- The forward map of the Möbius automorphism is the Möbius map. -/
@[simp]
theorem projectiveLineMobiusIso_hom :
    (projectiveLineMobiusIso hM).hom = projectiveLineMobius hM := rfl

/-- If `s ≫ ψ = s ≫ μ_M`, then `s` is fixed by `ψ` followed by the inverse of `μ_M`. -/
private theorem comp_trans_projectiveLineMobiusIso_symm_hom {X : Scheme.{u}}
    {s : X ⟶ projectiveLine R} (ψ : projectiveLine R ≅ projectiveLine R)
    (h : s ≫ ψ.hom = s ≫ projectiveLineMobius hM) :
    s ≫ (ψ ≪≫ (projectiveLineMobiusIso hM).symm).hom = s := by
  rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, h, Category.assoc,
    ← projectiveLineMobiusIso_hom hM, Iso.hom_inv_id, Category.comp_id]

/-- **The section `∞` is sent to `[a : c]`.** -/
theorem projectiveLineInfinitySection_comp_projectiveLineMobius :
    projectiveLineInfinitySection R ≫ projectiveLineMobius hM =
      projectiveLineHomogeneousPoint (RingHom.id R) (mobiusFst (RingHom.id R) M 1 0)
        (mobiusSnd (RingHom.id R) M 1 0) (isCoprime_mobius _ hM isCoprime_one_left) := by
  rw [projectiveLineInfinitySection_eq_projectiveLineHomogeneousPoint,
    projectiveLineHomogeneousPoint_comp_projectiveLineMobius]

/-- **The section `0` is sent to `[b : d]`.** -/
theorem projectiveLineZeroSection_comp_projectiveLineMobius :
    projectiveLineZeroSection R ≫ projectiveLineMobius hM =
      projectiveLineHomogeneousPoint (RingHom.id R) (mobiusFst (RingHom.id R) M 0 1)
        (mobiusSnd (RingHom.id R) M 0 1) (isCoprime_mobius _ hM isCoprime_one_right) := by
  rw [projectiveLineZeroSection_eq_projectiveLineHomogeneousPoint,
    projectiveLineHomogeneousPoint_comp_projectiveLineMobius]

/-- **The scaling `x ↦ u x` is the Möbius map of `diag(u, 1)`.** -/
theorem projectiveLineScaling_eq_projectiveLineMobius (w : Rˣ)
    (hw : IsUnit (!![(w : R), 0; 0, 1] : Matrix (Fin 2) (Fin 2) R).det) :
    projectiveLineScaling w = projectiveLineMobius hw := by
  refine projectiveLine_hom_ext ?_ ?_
  · rw [projectiveLineScaling, projectiveLineXChart_comp_projectiveLineHom,
      projectiveLineXChart_comp_projectiveLineMobius,
      ← Spec_map_id_comp (projectiveLineHomogeneousPoint _ _ _ _),
      Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right _ (RingHom.id _)
          (by simp [mobiusSnd])
        (C (w : R) * X) (by simp [mobiusFst, mobiusSnd])]
  · rw [projectiveLineScaling, projectiveLineYChart_comp_projectiveLineHom,
      projectiveLineYChart_comp_projectiveLineMobius,
      ← Spec_map_id_comp (projectiveLineHomogeneousPoint _ _ _ _),
      Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left _ (RingHom.id _)
        (by simp [mobiusFst]) (C (↑w⁻¹ : R) * X)
        (by
          simp only [mobiusFst, mobiusSnd, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, map_zero, zero_mul,
            add_zero, mul_one, map_one, one_mul, zero_add, RingHom.id_apply]
          rw [mul_comm, ← mul_assoc, ← C_mul, Units.mul_inv, C_1, one_mul])]

/-- **A Möbius map is the identity only for a scalar matrix.** -/
theorem exists_eq_smul_one_of_projectiveLineMobius_eq_id (h : projectiveLineMobius hM = 𝟙 _) :
    ∃ w : R, IsUnit w ∧ M = w • 1 := by
  have e := projectiveLineXChart_comp_projectiveLineMobius hM
  rw [h, Category.comp_id, ← projectiveLineHomogeneousPoint_X_one,
      projectiveLineHomogeneousPoint_eq_iff] at e
  simp only [mobiusFst, mobiusSnd, mul_one] at e
  have c0 := congrArg (Polynomial.coeff · 0) e
  have c1 := congrArg (Polynomial.coeff · 1) e
  have c2 := congrArg (Polynomial.coeff · 2) e
  simp only [Fin.isValue, mul_coeff_zero, coeff_X, one_ne_zero, ↓reduceIte, coeff_add, coeff_C,
    mul_zero, zero_add, zero_mul, coeff_X_mul, coeff_mul_X, add_zero] at c0 c1 c2
  have hM' : M = M 0 0 • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← c0, c2, c1]
  refine ⟨M 0 0, ?_, hM'⟩
  have := hM
  rw [hM', Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
  simpa using this

/-- **Two matrices define the same Möbius map if and only if they are proportional.** -/
theorem projectiveLineMobius_eq_iff {N : Matrix (Fin 2) (Fin 2) R} (hN : IsUnit N.det) :
    projectiveLineMobius hM = projectiveLineMobius hN ↔ ∃ w : R, IsUnit w ∧ N = w • M := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hN' := Matrix.isUnit_nonsing_inv_det _ hN
    have h1 : IsUnit (1 : Matrix (Fin 2) (Fin 2) R).det := by simp
    have hNM : IsUnit (N⁻¹ * M).det := by rw [Matrix.det_mul]; exact hN'.mul hM
    have key : projectiveLineMobius hNM = 𝟙 _ := by
      rw [← projectiveLineMobius_comp hN' hM, h,
        projectiveLineMobius_comp hN' hN (by rw [Matrix.nonsing_inv_mul N hN]; exact h1),
        projectiveLineMobius_congr _ h1 (Matrix.nonsing_inv_mul N hN), projectiveLineMobius_one]
    obtain ⟨w, hw, hw'⟩ := exists_eq_smul_one_of_projectiveLineMobius_eq_id hNM key
    have hMN : M = w • N := by
      calc M = N * (N⁻¹ * M) := by rw [← mul_assoc, Matrix.mul_nonsing_inv N hN, one_mul]
        _ = w • N := by rw [hw', Matrix.mul_smul, mul_one]
    refine ⟨↑hw.unit⁻¹, Units.isUnit _, ?_⟩
    rw [hMN, smul_smul, IsUnit.val_inv_mul, one_smul]
  · rintro ⟨w, hw, rfl⟩
    exact (projectiveLineMobius_smul hM hw hN).symm

/-! ### The classification -/

/-- The composite `0 ⟶ ℙ¹_R` of the origin of the first chart with a chart endomorphism
`x ↦ p(x)` is the point `x = p(0)`. -/
theorem affineLineOriginHom_comp_Spec_map_eval₂RingHom (p : R[X]) :
    affineLineOriginHom R ≫ Spec.map (CommRingCat.ofHom (eval₂RingHom C p)) =
      Spec.map (CommRingCat.ofHom (eval₂RingHom (RingHom.id R) (p.eval 0))) := by
  rw [affineLineOriginHom, Spec_map_ofHom_comp_Spec_map_ofHom]
  congr 2
  exact Polynomial.ringHom_ext (fun r ↦ by simp) (by simp)

/-- **An automorphism of `ℙ¹_R` over `R` sending `∞` to a point `[a : c]` with `a, c ∈ R` is a
Möbius map.** -/
theorem exists_eq_projectiveLineMobius (χ : projectiveLine R ≅ projectiveLine R)
    (hχ : χ.hom ≫ (projectiveLine R ↘ Spec (.of R)) = projectiveLine R ↘ Spec (.of R))
    {a c : R} (hac : IsCoprime a c)
    (hinf : projectiveLineInfinitySection R ≫ χ.hom =
        projectiveLineHomogeneousPoint (RingHom.id R) a c hac) :
    ∃ (N : Matrix (Fin 2) (Fin 2) R) (hN : IsUnit N.det), χ.hom = projectiveLineMobius hN := by
  obtain ⟨r, s, hrs⟩ := hac
  let M₁ : Matrix (Fin 2) (Fin 2) R := !![a, -s; c, r]
  have hM₁ : IsUnit M₁.det := by
    rw [Matrix.det_fin_two_of]
    convert isUnit_one
    linear_combination hrs
  have e₁ : projectiveLineInfinitySection R ≫ projectiveLineMobius hM₁ =
      projectiveLineInfinitySection R ≫ χ.hom := by
    rw [projectiveLineInfinitySection_comp_projectiveLineMobius, hinf]
    exact projectiveLineHomogeneousPoint_congr _ _ _ (by simp [M₁, mobiusFst])
        (by simp [M₁, mobiusSnd])
  let ψ₁ := χ ≪≫ (projectiveLineMobiusIso hM₁).symm
  have hψ₁ : ψ₁.hom ≫ (projectiveLine R ↘ Spec (.of R)) = projectiveLine R ↘ Spec (.of R) := by
    simp [ψ₁, projectiveLineMobiusIso, hχ]
  have hinf₁ : projectiveLineInfinitySection R ≫ ψ₁.hom = projectiveLineInfinitySection R := by
    exact comp_trans_projectiveLineMobiusIso_symm_hom hM₁ χ e₁.symm
  obtain ⟨φ, hφ⟩ := exists_ringHom_of_range_subset (projectiveLineXChart R) ψ₁.hom
    (range_comp_subset_of_fix _ _ range_projectiveLineXChart_eq_compl ψ₁ hinf₁)
  have eφ := ringHom_eq_eval₂RingHom_of_chart (projectiveLineXChart_comp_structureMorphism R)
    hψ₁ hφ
  set b := (φ.hom X).eval 0
  let M₂ : Matrix (Fin 2) (Fin 2) R := !![1, b; 0, 1]
  have hM₂ : IsUnit M₂.det := by simp [M₂, Matrix.det_fin_two_of]
  have h0₁ : projectiveLineZeroSection R ≫ ψ₁.hom =
      projectiveLineZeroSection R ≫ projectiveLineMobius hM₂ := by
    rw [projectiveLineZeroSection_comp_projectiveLineMobius, projectiveLineZeroSection,
      Category.assoc, ← hφ, ← Category.assoc]
    have : φ = CommRingCat.ofHom (eval₂RingHom C (φ.hom X)) := by ext1; exact eφ
    rw [this, affineLineOriginHom_comp_Spec_map_eval₂RingHom,
      ← Spec_map_id_comp (projectiveLineHomogeneousPoint _ _ _ _),
      Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right _ (RingHom.id _)
        (by simp [M₂, mobiusSnd]) b (by simp [M₂, mobiusFst, mobiusSnd])]
  have hinf₂' : projectiveLineInfinitySection R ≫ projectiveLineMobius hM₂ =
      projectiveLineInfinitySection R := by
    rw [projectiveLineInfinitySection_comp_projectiveLineMobius,
      projectiveLineInfinitySection_eq_projectiveLineHomogeneousPoint]
    exact projectiveLineHomogeneousPoint_congr _ _ _ (by simp [M₂, mobiusFst])
        (by simp [M₂, mobiusSnd])
  let ψ₂ := ψ₁ ≪≫ (projectiveLineMobiusIso hM₂).symm
  have hψ₂ : ψ₂.hom ≫ (projectiveLine R ↘ Spec (.of R)) = projectiveLine R ↘ Spec (.of R) := by
    simp only [ψ₂, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [show (projectiveLineMobiusIso hM₂).inv =
        projectiveLineMobius (Matrix.isUnit_nonsing_inv_det _ hM₂) from rfl,
      projectiveLineMobius_comp_structureMorphism, hψ₁]
  have hinf₂ : projectiveLineInfinitySection R ≫ ψ₂.hom = projectiveLineInfinitySection R := by
    exact comp_trans_projectiveLineMobiusIso_symm_hom hM₂ ψ₁ (hinf₁.trans hinf₂'.symm)
  have h0₂ : projectiveLineZeroSection R ≫ ψ₂.hom = projectiveLineZeroSection R := by
    exact comp_trans_projectiveLineMobiusIso_symm_hom hM₂ ψ₁ h0₁
  obtain ⟨w, hw⟩ := exists_eq_projectiveLineScaling ψ₂ hψ₂ h0₂ hinf₂
  let D : Matrix (Fin 2) (Fin 2) R := !![(w : R), 0; 0, 1]
  have hD : IsUnit D.det := by simp [D, Matrix.det_fin_two_of]
  have hM₂D : IsUnit (M₂ * D).det := by rw [Matrix.det_mul]; exact hM₂.mul hD
  have hM₁M₂D : IsUnit (M₁ * (M₂ * D)).det := by rw [Matrix.det_mul]; exact hM₁.mul hM₂D
  refine ⟨_, hM₁M₂D, ?_⟩
  have hχ' : χ.hom = ψ₂.hom ≫ projectiveLineMobius hM₂ ≫ projectiveLineMobius hM₁ := by
    simp only [ψ₂, ψ₁, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← projectiveLineMobiusIso_hom hM₂, Iso.inv_hom_id_assoc, ← projectiveLineMobiusIso_hom hM₁,
      Iso.inv_hom_id, Category.comp_id]
  rw [hχ', hw, projectiveLineScaling_eq_projectiveLineMobius w hD, ← Category.assoc,
    projectiveLineMobius_comp hM₂ hD hM₂D, projectiveLineMobius_comp hM₁ hM₂D hM₁M₂D]

end AlgebraicGeometry
