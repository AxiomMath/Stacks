module

public import
  StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.HigherTorsMultiplicity
public import StacksFrontier.RingTheory.CompleteLocalRing.PowerSeriesMaps
public import StacksFrontier.RingTheory.GradedCompletion.MvPowerSeries

/-!
# Formal coordinates for a surface with two transverse branches

The sentence "To make an actual example, ..." of Tag 0B2S asserts that there are a nonsingular
fourfold `X`, a closed point `p`, and closed subvarieties `V`, `W` with
`𝒪_{X, p}^∧ ≅ ℂ[[x, y, z, w]]` carrying the ideal of `V` to `(xz, xw, yz, yw)` and the ideal of `W`
to `(x - z, y - w)`. This file carries out the power series computation behind one explicit
instance, with `X = 𝔸⁴ = Spec ℂ[a, b, c, d]` and `p` the origin:

* `V` is the image of `𝔸² → 𝔸⁴`, `(s, t) ↦ (s² - 1, t, s (s² - 1), s t)`, whose ideal is the kernel
  of `nodalSurfaceParam`; it is integral, being the image of an integral scheme. Its two branches
  through the origin come from `s = ±1`, that is from `s = ±√(1 + a)`, and are `c = ±u a`,
  `d = ±u b` with `u = √(1 + a) ∈ ℂ[[a, b, c, d]]`.
* `W` is the plane `c = d = 0`, transverse to both branches.

The formal coordinates are `y = (c - u a, d - u b, -c - u a, -d - u b)` (`branchCoord`): the first
two cut out one branch, the last two the other, and `y₀ - y₂ = 2c`, `y₁ - y₃ = 2d`. They form a
regular system of parameters, so the substitution `X i ↦ yᵢ` is an automorphism `branchCoordEquiv`
of `ℂ[[a, b, c, d]]` (Tag 07NM (1)), and under it

* the extension of the ideal of `V` is the image of `(xz, xw, yz, yw)`
  (`map_ker_nodalSurfaceParam`);
* the extension of the ideal of `W` is the image of `(x - z, y - w)` (`map_ker_planeParam`).

## Main definitions

* `Stacks.Intersection.TwoPlanes.sqrtOneAddX`: a square root of `1 + a` in `ℂ[[a, b, c, d]]`.
* `Stacks.Intersection.TwoPlanes.branchCoord`: the four formal coordinates adapted to the two
  branches.
* `Stacks.Intersection.TwoPlanes.branchCoordEquiv`: the automorphism `X i ↦ yᵢ`.
* `Stacks.Intersection.TwoPlanes.nodalSurfaceParam`, `Stacks.Intersection.TwoPlanes.planeParam`:
  the parametrizations whose kernels are the ideals of `V` and `W`.

## Main results

* `Stacks.Intersection.TwoPlanes.isRegularSystemOfParameters_branchCoordParams`.
* `Stacks.Intersection.TwoPlanes.map_ker_nodalSurfaceParam`: the completed ideal of `V` is
  `(xz, xw, yz, yw)` in the branch coordinates.
* `Stacks.Intersection.TwoPlanes.map_ker_planeParam`: the completed ideal of `W` is
  `(x - z, y - w)` in the branch coordinates.

## References

* [Stacks Project, Tag 0B2S](https://stacks.math.columbia.edu/tag/0B2S)
* [Stacks Project, Tag 07NM](https://stacks.math.columbia.edu/tag/07NM)
-/

@[expose] public noncomputable section

open IsLocalRing MvPowerSeries

namespace Stacks.Intersection.TwoPlanes

local notation "A" => MvPowerSeries (Fin 4) ℂ

local notation "P" => MvPolynomial (Fin 4) ℂ

/-! ### Formal coordinates adapted to the two branches -/

/-- **`1 + x` has a square root in `ℂ[[x, y, z, w]]`**, with constant term `1`. -/
theorem exists_sq_eq_one_add_X_zero : ∃ ρ : A, ρ ^ 2 = 1 + X 0 ∧ constantCoeff ρ = 1 := by
  obtain ⟨ρ, hroot, hρ⟩ := HenselianLocalRing.is_henselian
    (Polynomial.X ^ 2 - Polynomial.C (1 + X 0 : A))
    (Polynomial.monic_X_pow_sub_C _ (by norm_num)) 1 (by
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        one_pow, sub_add_cancel_left]
      exact (Ideal.neg_mem_iff _).mpr (X_mem_maximalIdeal 0)) (by
      simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
        sub_zero, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        one_pow, mul_one]
      rw [MvPowerSeries.isUnit_iff_constantCoeff, map_natCast]
      exact isUnit_iff_ne_zero.mpr (by norm_num))
  refine ⟨ρ, ?_, ?_⟩
  · simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] using hroot.eq_zero
  · have h := Stacks.MvPowerSeries.RegularParameters.constantCoeff_eq_zero_of_mem_maximalIdeal hρ
    rwa [map_sub, map_one, sub_eq_zero] at h

/-- A square root `√(1 + x)` of `1 + x` in `ℂ[[x, y, z, w]]`, with constant term `1`. -/
def sqrtOneAddX : A := exists_sq_eq_one_add_X_zero.choose

/-- `√(1 + x) ^ 2 = 1 + x`. -/
theorem sqrtOneAddX_sq : sqrtOneAddX ^ 2 = 1 + X 0 := exists_sq_eq_one_add_X_zero.choose_spec.1

/-- The constant term of `√(1 + x)` is `1`. -/
theorem constantCoeff_sqrtOneAddX : constantCoeff sqrtOneAddX = 1 :=
  exists_sq_eq_one_add_X_zero.choose_spec.2

/-- **The formal coordinates adapted to the two branches.** Writing `a, b, c, d` for the variables
of `ℂ[[a, b, c, d]]` and `u = √(1 + a)`, these are `(c - u a, d - u b, -c - u a, -d - u b)`. The
first two cut out the branch `s = u` of the surface `(a, b, c, d) = (s² - 1, t, s (s² - 1), s t)`
at the origin, the last two the branch `s = -u`, and the differences of the first and the third,
and of the second and the fourth, are `2c` and `2d`. -/
def branchCoord : Fin 4 → A :=
  ![X 2 - sqrtOneAddX * X 0, X 3 - sqrtOneAddX * X 1, -X 2 - sqrtOneAddX * X 0,
    -X 3 - sqrtOneAddX * X 1]

/-- The branch coordinates lie in the maximal ideal. -/
theorem branchCoord_mem (i : Fin 4) : branchCoord i ∈ maximalIdeal A := by
  have hu : ∀ j : Fin 4, (X j : A) ∈ maximalIdeal A := X_mem_maximalIdeal
  fin_cases i <;>
    simp only [branchCoord, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
    first
    | exact Ideal.sub_mem _ (hu _) (Ideal.mul_mem_left _ _ (hu _))
    | exact Ideal.sub_mem _ ((Ideal.neg_mem_iff _).mpr (hu _)) (Ideal.mul_mem_left _ _ (hu _))

/-- `√(1 + x)` is a unit. -/
theorem isUnit_sqrtOneAddX : IsUnit sqrtOneAddX := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, constantCoeff_sqrtOneAddX]; exact isUnit_one

/-- `2` is invertible in `ℂ[[x, y, z, w]]`, with inverse the constant `1 / 2`. -/
theorem C_half_mul_two : (C (1 / 2 : ℂ) : A) * 2 = 1 := by
  rw [show (2 : A) = C 2 from (map_ofNat C 2).symm, ← map_mul]
  norm_num

/-- `c = (1 / 2) (y₀ - y₂)`. -/
private theorem X_two_eq_half_mul :
    (X 2 : A) = C (1 / 2 : ℂ) * (branchCoord 0 - branchCoord 2) := by
  simp only [branchCoord, Matrix.cons_val]
  linear_combination (-(X 2)) * C_half_mul_two

/-- `d = (1 / 2) (y₁ - y₃)`. -/
private theorem X_three_eq_half_mul :
    (X 3 : A) = C (1 / 2 : ℂ) * (branchCoord 1 - branchCoord 3) := by
  simp only [branchCoord, Matrix.cons_val]
  linear_combination (-(X 3)) * C_half_mul_two

/-- **The branch coordinates generate the maximal ideal.** -/
theorem span_branchCoord : Ideal.span (Set.range branchCoord) = maximalIdeal A := by
  refine le_antisymm (Ideal.span_le.mpr ?_) ?_
  · rintro _ ⟨i, rfl⟩; exact branchCoord_mem i
  obtain ⟨v, hv⟩ : ∃ v : A, v * sqrtOneAddX = 1 :=
    ⟨(isUnit_sqrtOneAddX.unit⁻¹ : Aˣ), isUnit_sqrtOneAddX.val_inv_mul⟩
  have hy : ∀ i, branchCoord i ∈ Ideal.span (Set.range branchCoord) :=
    fun i => Ideal.subset_span ⟨i, rfl⟩
  have h2 := C_half_mul_two
  rw [maximalIdeal_eq_span_four, Ideal.span_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · have : (X 0 : A) = -(v * C (1 / 2 : ℂ)) * (branchCoord 0 + branchCoord 2) := by
      simp only [branchCoord, Matrix.cons_val]
      linear_combination (-(X 0) * (C (1 / 2 : ℂ) * 2)) * hv - X 0 * h2
    rw [this]; exact Ideal.mul_mem_left _ _ (add_mem (hy 0) (hy 2))
  · have : (X 1 : A) = -(v * C (1 / 2 : ℂ)) * (branchCoord 1 + branchCoord 3) := by
      simp only [branchCoord, Matrix.cons_val]
      linear_combination (-(X 1) * (C (1 / 2 : ℂ) * 2)) * hv - X 1 * h2
    rw [this]; exact Ideal.mul_mem_left _ _ (add_mem (hy 1) (hy 3))
  · rw [X_two_eq_half_mul]; exact Ideal.mul_mem_left _ _ (sub_mem (hy 0) (hy 2))
  · rw [X_three_eq_half_mul]; exact Ideal.mul_mem_left _ _ (sub_mem (hy 1) (hy 3))

/-- The branch coordinates, as elements of the maximal ideal. -/
def branchCoordParams : Fin 4 → maximalIdeal A := fun i => ⟨branchCoord i, branchCoord_mem i⟩

/-- **The branch coordinates are a regular system of parameters of `ℂ[[a, b, c, d]]`.** -/
theorem isRegularSystemOfParameters_branchCoordParams :
    IsRegularSystemOfParameters branchCoordParams := by
  have hspanR : Submodule.span A (Set.range branchCoordParams) = ⊤ := by
    apply Submodule.map_injective_of_injective (maximalIdeal A).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact span_branchCoord
  have hspan : Submodule.span (ResidueField A)
      (Set.range fun i => (maximalIdeal A).toCotangent (branchCoordParams i)) = ⊤ := by
    rw [Set.range_comp' (maximalIdeal A).toCotangent branchCoordParams]
    exact CotangentSpace.span_image_eq_top_iff.mpr hspanR
  refine ⟨linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge ?_, hspan⟩
  rw [Fintype.card_fin, Stacks.MvPowerSeries.RegularParameters.finrank_cotangentSpace_field]

/-- **The change of formal coordinates `X i ↦ yᵢ`**: the automorphism of `ℂ[[x, y, z, w]]`
substituting the branch coordinates for the variables. -/
def branchCoordEquiv : A ≃ₐ[ℂ] A :=
  AlgEquiv.ofBijective _
    (main_theorem_one ℂ 4 branchCoordParams isRegularSystemOfParameters_branchCoordParams).2

/-- The change of coordinates sends the `i`-th variable to the `i`-th branch coordinate. -/
theorem branchCoordEquiv_X (i : Fin 4) : branchCoordEquiv (X i) = branchCoord i :=
  (main_theorem_one ℂ 4 branchCoordParams isRegularSystemOfParameters_branchCoordParams).1 i

/-- The change of coordinates on an ideal generated by two variables. -/
theorem map_branchCoordEquiv_span_pair (i j : Fin 4) :
    Ideal.map branchCoordEquiv (Ideal.span {X i, X j}) =
      Ideal.span {branchCoord i, branchCoord j} := by
  rw [Ideal.map_span, Set.image_pair, branchCoordEquiv_X, branchCoordEquiv_X]

/-- **In the branch coordinates, `(xz, xw, yz, yw)` is the intersection of the two branches**: its
image is `(y₀, y₁) ∩ (y₂, y₃)`, the image of `(x, y) ∩ (z, w)`. -/
theorem map_branchCoordEquiv_unionOfPlanes_eq_inf :
    Ideal.map branchCoordEquiv unionOfPlanes =
      Ideal.span {branchCoord 0, branchCoord 1} ⊓ Ideal.span {branchCoord 2, branchCoord 3} := by
  rw [unionOfPlanes_eq_inf, ← map_branchCoordEquiv_span_pair, ← map_branchCoordEquiv_span_pair]
  refine le_antisymm (Ideal.map_inf_le branchCoordEquiv) ?_
  rintro x ⟨hxI, hxJ⟩
  obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_of_equiv branchCoordEquiv x).mp hxI
  obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_of_equiv branchCoordEquiv (branchCoordEquiv a)).mp hxJ
  rw [branchCoordEquiv.injective hab] at hb
  exact Ideal.mem_map_of_mem _ ⟨ha, hb⟩

/-- The image of `(xz, xw, yz, yw)` under the change of coordinates is generated by the four
products `yᵢ yⱼ`, `i ∈ {0, 1}`, `j ∈ {2, 3}`. -/
theorem map_branchCoordEquiv_unionOfPlanes :
    Ideal.map branchCoordEquiv unionOfPlanes =
      Ideal.span {branchCoord 0 * branchCoord 2, branchCoord 0 * branchCoord 3,
        branchCoord 1 * branchCoord 2, branchCoord 1 * branchCoord 3} := by
  rw [unionOfPlanes, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton, map_mul, branchCoordEquiv_X]

/-- **In the branch coordinates, `(x - z, y - w)` is the plane `c = d = 0`**: its image is
`(y₀ - y₂, y₁ - y₃) = (2c, 2d) = (c, d)`. -/
theorem map_branchCoordEquiv_diagonalPlane :
    Ideal.map branchCoordEquiv diagonalPlane = Ideal.span {X 2, X 3} := by
  rw [diagonalPlane, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton, map_sub, branchCoordEquiv_X]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · have : branchCoord 0 - branchCoord 2 = 2 * X 2 := by
        simp only [branchCoord, Matrix.cons_val]; ring
      rw [this]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · have : branchCoord 1 - branchCoord 3 = 2 * X 3 := by
        simp only [branchCoord, Matrix.cons_val]; ring
      rw [this]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · rw [Ideal.span_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · rw [X_two_eq_half_mul]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · rw [X_three_eq_half_mul]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

/-! ### The surface and the plane in `𝔸⁴`

The surface `V ⊂ 𝔸⁴ = Spec ℂ[a, b, c, d]` is the image of the finite map `𝔸² → 𝔸⁴`,
`(s, t) ↦ (s² - 1, t, s (s² - 1), s t)`, which is injective away from the two points `(±1, 0)`,
both sent to the origin, and immersive at both. Its ideal is the kernel of
`nodalSurfaceParam : ℂ[a, b, c, d] → ℂ[s, t]`, a prime ideal since `ℂ[s, t]` is a domain. The plane
`W` is `c = d = 0`, the kernel of `planeParam`. -/

/-- **The parametrization of the surface `V`**, `a ↦ s² - 1`, `b ↦ t`, `c ↦ s (s² - 1)`, `d ↦ s t`.
Its kernel is the ideal of `V`. -/
def nodalSurfaceParam : P →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.aeval ![MvPolynomial.X 0 ^ 2 - 1, MvPolynomial.X 1,
    MvPolynomial.X 0 * (MvPolynomial.X 0 ^ 2 - 1), MvPolynomial.X 0 * MvPolynomial.X 1]

/-- **The parametrization of the plane `W`**, `a ↦ s`, `b ↦ t`, `c, d ↦ 0`. Its kernel is the ideal
`(c, d)` of `W`. -/
def planeParam : P →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1, 0, 0]

/-- A polynomial read as a power series. -/
def polyToSeries : P →ₐ[ℂ] A := MvPolynomial.coeToMvPowerSeries.algHom ℂ

/-- A variable read as a power series is the variable. -/
theorem polyToSeries_X (i : Fin 4) : polyToSeries (MvPolynomial.X i) = X i := by
  simp [polyToSeries]

/-- **The extension of the ideal of a parametrized subvariety lies in the ideal of a formal
branch.** If `φ : ℂ[s] → ℂ[[a, b, c, d]]` is a formal reparametrization along which each coordinate
`aᵢ` agrees, modulo `J`, with its parametrization, then every polynomial vanishing on the
parametrized subvariety lies in `J`. -/
theorem map_ker_le_of_sub_mem {n : ℕ} (param : P →ₐ[ℂ] MvPolynomial (Fin n) ℂ)
    (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (J : Ideal A)
    (h : ∀ i, polyToSeries (MvPolynomial.X i) - φ (param (MvPolynomial.X i)) ∈ J) :
    (RingHom.ker (param : P →+* MvPolynomial (Fin n) ℂ)).map (polyToSeries : P →+* A) ≤ J := by
  have hext : (Ideal.Quotient.mkₐ ℂ J).comp polyToSeries =
      (Ideal.Quotient.mkₐ ℂ J).comp (φ.comp param) :=
    MvPolynomial.algHom_ext fun i => by
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.Quotient.eq.mpr (h i)
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  have := congrArg (fun F : P →ₐ[ℂ] A ⧸ J => F f) hext
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
  show Ideal.Quotient.mk J (polyToSeries f) = 0
  rw [this, show param f = 0 from hf, map_zero, map_zero]

/-- The ideal of `V` lies in any ideal containing `c - ε a` and `d - ε b` for a square root `ε`
of `1 + a`. -/
private theorem map_ker_nodalSurfaceParam_le_of_mem (ε : A) (hε : ε ^ 2 = 1 + X 0) (J : Ideal A)
    (h2 : X 2 - ε * X 0 ∈ J) (h3 : X 3 - ε * X 1 ∈ J) :
    (RingHom.ker (nodalSurfaceParam : P →+* MvPolynomial (Fin 2) ℂ)).map
      (polyToSeries : P →+* A) ≤ J := by
  refine map_ker_le_of_sub_mem nodalSurfaceParam
    (MvPolynomial.aeval ![ε, MvPowerSeries.X 1]) _ fun i => ?_
  fin_cases i <;>
    simp only [nodalSurfaceParam, polyToSeries_X, MvPolynomial.aeval_X, map_sub, map_mul, map_pow,
      map_one, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
  · convert Submodule.zero_mem _ using 1; linear_combination -hε
  · convert Submodule.zero_mem _ using 1; ring
  · convert h2 using 1; linear_combination -ε * hε
  · exact h3

/-- The ideal of `V` lies in the ideal `(y₀, y₁)` of the branch `s = √(1 + a)`, `t = b`. -/
theorem map_ker_nodalSurfaceParam_le_left :
    (RingHom.ker (nodalSurfaceParam : P →+* MvPolynomial (Fin 2) ℂ)).map
      (polyToSeries : P →+* A) ≤ Ideal.span {branchCoord 0, branchCoord 1} :=
  map_ker_nodalSurfaceParam_le_of_mem _ sqrtOneAddX_sq _ (Ideal.subset_span (by simp [branchCoord]))
    (Ideal.subset_span (by simp [branchCoord]))

/-- The ideal of `V` lies in the ideal `(y₂, y₃)` of the branch `s = -√(1 + a)`, `t = b`. -/
theorem map_ker_nodalSurfaceParam_le_right :
    (RingHom.ker (nodalSurfaceParam : P →+* MvPolynomial (Fin 2) ℂ)).map
      (polyToSeries : P →+* A) ≤ Ideal.span {branchCoord 2, branchCoord 3} := by
  refine map_ker_nodalSurfaceParam_le_of_mem (-sqrtOneAddX) (by rw [neg_sq, sqrtOneAddX_sq]) _
    ?_ ?_
  · have : -(X 2 - -sqrtOneAddX * X 0 : A) = branchCoord 2 := by
      simp only [branchCoord, Matrix.cons_val]; ring
    rw [← neg_mem_iff, this]; exact Ideal.subset_span (by simp)
  · have : -(X 3 - -sqrtOneAddX * X 1 : A) = branchCoord 3 := by
      simp only [branchCoord, Matrix.cons_val]; ring
    rw [← neg_mem_iff, this]; exact Ideal.subset_span (by simp)

/-- The ideal of `W` lies in `(c, d)`. -/
theorem map_ker_planeParam_le :
    (RingHom.ker (planeParam : P →+* MvPolynomial (Fin 2) ℂ)).map (polyToSeries : P →+* A) ≤
      Ideal.span {MvPowerSeries.X 2, MvPowerSeries.X 3} := by
  refine map_ker_le_of_sub_mem planeParam
    (MvPolynomial.aeval ![MvPowerSeries.X 0, MvPowerSeries.X 1]) _ fun i => ?_
  fin_cases i <;>
    simp only [planeParam, polyToSeries_X, MvPolynomial.aeval_X, map_zero, sub_zero, sub_self,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
  · exact Submodule.zero_mem _
  · exact Submodule.zero_mem _
  · exact Ideal.subset_span (by simp)
  · exact Ideal.subset_span (by simp)

/-- A polynomial vanishing under a parametrization lies, as a power series, in the extension of its
kernel. -/
theorem polyToSeries_mem_map_ker {n : ℕ} (param : P →ₐ[ℂ] MvPolynomial (Fin n) ℂ) {g : P}
    (hg : param g = 0) :
    polyToSeries g ∈
      (RingHom.ker (param : P →+* MvPolynomial (Fin n) ℂ)).map (polyToSeries : P →+* A) :=
  Ideal.mem_map_of_mem _ hg

/-- The products `yᵢ yⱼ`, `i ∈ {0, 1}`, `j ∈ {2, 3}`, lie in the extension of the ideal of `V`. -/
theorem span_branchCoord_mul_le :
    Ideal.span {branchCoord 0 * branchCoord 2, branchCoord 0 * branchCoord 3,
        branchCoord 1 * branchCoord 2, branchCoord 1 * branchCoord 3} ≤
      (RingHom.ker (nodalSurfaceParam : P →+* MvPolynomial (Fin 2) ℂ)).map
        (polyToSeries : P →+* A) := by
  set K := (RingHom.ker (nodalSurfaceParam : P →+* MvPolynomial (Fin 2) ℂ)).map
    (polyToSeries : P →+* A)
  have g1 : polyToSeries
      ((1 + MvPolynomial.X 0) * MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2) ∈ K :=
    polyToSeries_mem_map_ker nodalSurfaceParam (by simp [nodalSurfaceParam]; ring)
  have g2 : polyToSeries
      ((1 + MvPolynomial.X 0) * MvPolynomial.X 1 ^ 2 - MvPolynomial.X 3 ^ 2) ∈ K :=
    polyToSeries_mem_map_ker nodalSurfaceParam (by simp [nodalSurfaceParam]; ring)
  have g3 : polyToSeries ((1 + MvPolynomial.X 0) * MvPolynomial.X 0 * MvPolynomial.X 1 -
      MvPolynomial.X 2 * MvPolynomial.X 3) ∈ K :=
    polyToSeries_mem_map_ker nodalSurfaceParam (by simp [nodalSurfaceParam]; ring)
  have g4 : polyToSeries
      (MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2) ∈ K :=
    polyToSeries_mem_map_ker nodalSurfaceParam (by simp [nodalSurfaceParam]; ring)
  simp only [map_sub, map_mul, map_add, map_one, map_pow, polyToSeries_X] at g1 g2 g3 g4
  have hu := sqrtOneAddX_sq
  rw [Ideal.span_le]
  intro g hg
  rw [SetLike.mem_coe]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · convert g1 using 2; simp only [branchCoord, Matrix.cons_val]; linear_combination (X 0 ^ 2) * hu
  · convert add_mem g3 (K.mul_mem_left sqrtOneAddX g4) using 2
    simp only [branchCoord, Matrix.cons_val]; linear_combination (X 0 * X 1) * hu
  · convert sub_mem g3 (K.mul_mem_left sqrtOneAddX g4) using 2
    simp only [branchCoord, Matrix.cons_val]; linear_combination (X 0 * X 1) * hu
  · convert g2 using 2; simp only [branchCoord, Matrix.cons_val]; linear_combination (X 1 ^ 2) * hu

/-- **The completed ideal of `V` at the origin is `(xz, xw, yz, yw)` in the branch coordinates**:
the extension of the ideal of `V` to `ℂ[[a, b, c, d]]` is `(y₀, y₁) ∩ (y₂, y₃)`, the image of
`(xz, xw, yz, yw)` under the change of coordinates. -/
theorem map_ker_nodalSurfaceParam :
    (RingHom.ker (nodalSurfaceParam : P →+* MvPolynomial (Fin 2) ℂ)).map
      (polyToSeries : P →+* A) = Ideal.map branchCoordEquiv unionOfPlanes := by
  refine le_antisymm ?_ (map_branchCoordEquiv_unionOfPlanes ▸ span_branchCoord_mul_le)
  rw [map_branchCoordEquiv_unionOfPlanes_eq_inf]
  exact le_inf map_ker_nodalSurfaceParam_le_left map_ker_nodalSurfaceParam_le_right

/-- **The completed ideal of `W` at the origin is `(x - z, y - w)` in the branch coordinates**: the
extension of the ideal of `W` is `(c, d)`, the image of `(x - z, y - w)`. -/
theorem map_ker_planeParam :
    (RingHom.ker (planeParam : P →+* MvPolynomial (Fin 2) ℂ)).map
      (polyToSeries : P →+* A) = Ideal.map branchCoordEquiv diagonalPlane := by
  rw [map_branchCoordEquiv_diagonalPlane]
  refine le_antisymm map_ker_planeParam_le ?_
  rw [Ideal.span_le]
  intro g hg
  rw [SetLike.mem_coe]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl <;> rw [← polyToSeries_X] <;>
    exact polyToSeries_mem_map_ker planeParam (by simp [planeParam])

/-- Undoing the change of coordinates on an ideal. -/
theorem map_symm_map_branchCoordEquiv (I : Ideal A) :
    (Ideal.map branchCoordEquiv I).map branchCoordEquiv.symm = I := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_of_equiv branchCoordEquiv x).mp hx
    simpa using ha
  · intro x hx
    rw [← branchCoordEquiv.symm_apply_apply x]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hx)

end Stacks.Intersection.TwoPlanes

end
