module

public import StacksFrontier.AlgebraicGeometry.ProjectiveLineCube.TriquadraticSurface
public import StacksFrontier.RingTheory.Polynomial.QuadraticIrreducible
public import StacksFrontier.RingTheory.MvPolynomial.HypersurfaceDimension
public import StacksFrontier.Topology.Dimension.OpenCover
public import StacksFrontier.AlgebraicGeometry.Properties.AffineOpenSpectrum
public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Generation
import StacksFrontier.AlgebraicGeometry.AmplePredicateBridge.Basic

/-!
# A cyclically symmetric triquadratic surface over `ℚ`

In `ℙ¹ × ℙ¹ × ℙ¹` over `ℚ`, with coordinates `(x₀ : x₁), (y₀ : y₁), (z₀ : z₁)`, consider the
surface `X` cut out by

`F = x₁² y₀² z₀² + x₀² y₁² z₀² + x₀² y₀² z₁² + x₀ x₁ y₀ y₁ z₀ z₁ + x₁² y₁² z₁²`,

a form of tridegree `(2, 2, 2)` invariant under the cyclic permutation of the three factors.
As a binary quadratic form in `(z₀ : z₁)` it is `A z₀² + B z₀ z₁ + C z₁²` with
`A = x₁² y₀² + x₀² y₁²`, `B = x₀ x₁ y₀ y₁`, `C = x₀² y₀² + x₁² y₁²`.

On each of the eight standard charts `V_c` of `ℙ¹ × ℙ¹ × ℙ¹` the surface is the affine
hypersurface of `f_c = a z² + b z + c'` with `b = x y` and `{a, c'} = {x² + y², 1 + x² y²}`.
Such an `f_c` is irreducible: its coefficients generate the unit ideal (`(1 + x²y²) - (xy)² = 1`)
and its discriminant takes the negative value `1 - 16` at `x = y = 1`
(`Polynomial.irreducible_of_discrim_neg`). Hence:

* every chart of `X` is the spectrum of a domain of Krull dimension `2`;
* the charts all contain the points of the chart `x₀ y₀ z₀ ≠ 0` at which `x y z ≠ 0`, and these
  exist, so `X` is irreducible; being covered by reduced charts it is reduced, so `X` is an
  **integral surface**;
* `X` is proper over `ℚ`, `𝒪(1, 1, 1)|_X` is ample, and the cyclic permutation of the factors
  restricts to an automorphism of `X` over `ℚ`
  (`AlgebraicGeometry.projectiveLineCube.TriquadraticSurface`).

This is the surface on which the automorphisms of [Stacks, Tag 0DSR] act.

## Main definitions

* `AlgebraicGeometry.projectiveLineCube.cyclicTriquadricCoefficients`: the coefficients of `F`.
* `AlgebraicGeometry.projectiveLineCube.cyclicTriquadric`: the surface `X = Z(F)` over `ℚ`.
* `AlgebraicGeometry.projectiveLineCube.cyclicTriquadricRotation`: the automorphism of `X` induced
  by the cyclic permutation of the factors.

## Main results

* `AlgebraicGeometry.projectiveLineCube.isIntegral_cyclicTriquadric`: `X` is integral.
* `AlgebraicGeometry.projectiveLineCube.topologicalKrullDim_cyclicTriquadric`: `dim X = 2`.
* `AlgebraicGeometry.projectiveLineCube.isCyclicCoefficients_cyclicTriquadricCoefficients`: the
  cyclic symmetry of `F`.
* `AlgebraicGeometry.projectiveLineCube.exists_mem_nonvanishingOpen_cyclicTriquadricCoefficient`
  and `generatesStalks_triquadraticCoefficient_cyclicTriquadricCoefficients`: `A`, `B`, `C` have
  no common zero, i.e. they generate `𝓗₀² ⊗ 𝓗₁²` at every stalk.
* `AlgebraicGeometry.projectiveLineCube.irreducible_chartPolynomial`: the local equations are
  irreducible.

## References

* [Stacks Project, Tag 0DSR](https://stacks.math.columbia.edu/tag/0DSR)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace MvPolynomial

namespace AlgebraicGeometry

namespace projectiveLineCube

/-! ### The coefficients -/

/-- The coefficients of the form
`x₁² y₀² z₀² + x₀² y₁² z₀² + x₀² y₀² z₁² + x₀ x₁ y₀ y₁ z₀ z₁ + x₁² y₁² z₁²`: the coefficient of
`m_i(x) m_j(y) m_l(z)`, where `m₀ = T₀², m₁ = T₀ T₁, m₂ = T₁²`. -/
def cyclicTriquadricCoefficients (i j l : Fin 3) : ℤ :=
  if (i = 2 ∧ j = 0 ∧ l = 0) ∨ (i = 0 ∧ j = 2 ∧ l = 0) ∨ (i = 0 ∧ j = 0 ∧ l = 2) ∨
    (i = 1 ∧ j = 1 ∧ l = 1) ∨ (i = 2 ∧ j = 2 ∧ l = 2) then 1 else 0

/-- **The form is invariant under the cyclic permutation of the factors.** -/
theorem isCyclicCoefficients_cyclicTriquadricCoefficients :
    IsCyclicCoefficients cyclicTriquadricCoefficients := by
  unfold IsCyclicCoefficients cyclicTriquadricCoefficients
  decide

/-- **The cyclically symmetric triquadratic surface over `ℚ`.** -/
abbrev cyclicTriquadric : Scheme.{0} :=
  triquadraticSurface cyclicTriquadricCoefficients (Spec (.of ℚ))

/-- The automorphism of the surface induced by the cyclic permutation of the factors. -/
abbrev cyclicTriquadricRotation : cyclicTriquadric ≅ cyclicTriquadric :=
  surfaceRotation ℚ isCyclicCoefficients_cyclicTriquadricCoefficients

/-! ### The local equations -/

/-- The local equation of the surface on the chart `![c0, c1, c2]`: the dehomogenization of `F`,
in which `T₀^(2-k) T₁^k` becomes `X i ^ dehomExponent c k` in the `i`-th variable. -/
theorem triquadraticChartPolynomial_cyclicTriquadricCoefficients (c0 c1 c2 : Fin 2) :
    triquadraticChartPolynomial cyclicTriquadricCoefficients ![c0, c1, c2] =
      X 0 ^ dehomExponent c0 2 * X 1 ^ dehomExponent c1 0 * X 2 ^ dehomExponent c2 0 +
      X 0 ^ dehomExponent c0 0 * X 1 ^ dehomExponent c1 2 * X 2 ^ dehomExponent c2 0 +
      X 0 ^ dehomExponent c0 0 * X 1 ^ dehomExponent c1 0 * X 2 ^ dehomExponent c2 2 +
      X 0 * X 1 * X 2 +
      X 0 ^ dehomExponent c0 2 * X 1 ^ dehomExponent c1 2 * X 2 ^ dehomExponent c2 2 := by
  have h1 : ∀ a : Fin 2, dehomExponent a 1 = 1 := by decide
  simp [triquadraticChartPolynomial, biquadraticChartPolynomial, Fin.sum_univ_three,
    cyclicTriquadricCoefficients, h1]
  ring

/-- `ℚ[x₀, x₁, x₂] ≃ ℚ[x₀, x₁][z]` with `z = x₂`: the variable `x₂` of the third factor becomes
the polynomial variable. -/
def thirdVariableEquiv : MvPolynomial (Fin 3) ℚ ≃ₐ[ℚ] Polynomial (MvPolynomial (Fin 2) ℚ) :=
  (renameEquiv ℚ (Equiv.swap (0 : Fin 3) 2)).trans (finSuccEquiv ℚ 2)

/-- `thirdVariableEquiv` sends `x₀` to the constant `x₁`. -/
theorem thirdVariableEquiv_X_zero : thirdVariableEquiv (X 0) = Polynomial.C (X 1) := by
  change finSuccEquiv ℚ 2 (rename (Equiv.swap (0 : Fin 3) 2) (X 0)) = _
  rw [rename_X, Equiv.swap_apply_left]
  exact finSuccEquiv_X_succ (j := (1 : Fin 2))

/-- `thirdVariableEquiv` sends `x₁` to the constant `x₀`. -/
theorem thirdVariableEquiv_X_one : thirdVariableEquiv (X 1) = Polynomial.C (X 0) := by
  change finSuccEquiv ℚ 2 (rename (Equiv.swap (0 : Fin 3) 2) (X 1)) = _
  rw [rename_X, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  exact finSuccEquiv_X_succ (j := (0 : Fin 2))

/-- `thirdVariableEquiv` sends `x₂` to the polynomial variable. -/
theorem thirdVariableEquiv_X_two : thirdVariableEquiv (X 2) = Polynomial.X := by
  change finSuccEquiv ℚ 2 (rename (Equiv.swap (0 : Fin 3) 2) (X 2)) = _
  rw [rename_X, Equiv.swap_apply_right]
  exact finSuccEquiv_X_zero

/-- The local equation on a chart, as a quadratic polynomial in `x₂`: its coefficients are
`1 + x₀²x₁²`, `x₀x₁`, `x₀² + x₁²` in one order or the other. -/
theorem exists_thirdVariableEquiv_chartPolynomial (c : Fin 3 → Fin 2) :
    ∃ a c' : MvPolynomial (Fin 2) ℚ,
      thirdVariableEquiv (map (Int.castRingHom ℚ)
          (triquadraticChartPolynomial cyclicTriquadricCoefficients c)) =
        Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C (X 1 * X 0) * Polynomial.X +
          Polynomial.C c' ∧
      ((a = 1 + X 0 ^ 2 * X 1 ^ 2 ∧ c' = X 0 ^ 2 + X 1 ^ 2) ∨
        (a = X 0 ^ 2 + X 1 ^ 2 ∧ c' = 1 + X 0 ^ 2 * X 1 ^ 2)) := by
  have hc : c = ![c 0, c 1, c 2] := by funext i; fin_cases i <;> rfl
  rw [hc, triquadraticChartPolynomial_cyclicTriquadricCoefficients]
  simp only [map_add, map_mul, map_pow, MvPolynomial.map_X, thirdVariableEquiv_X_zero,
    thirdVariableEquiv_X_one, thirdVariableEquiv_X_two]
  generalize c 0 = c0
  generalize c 1 = c1
  generalize c 2 = c2
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2
  all_goals first
    | (refine ⟨_, _, ?_, Or.inl ⟨rfl, rfl⟩⟩; simp [dehomExponent]; ring1)
    | (refine ⟨_, _, ?_, Or.inr ⟨rfl, rfl⟩⟩; simp [dehomExponent]; ring1)

/-- **The local equations are irreducible.** -/
theorem irreducible_chartPolynomial (c : Fin 3 → Fin 2) :
    Irreducible (map (Int.castRingHom ℚ)
      (triquadraticChartPolynomial cyclicTriquadricCoefficients c)) := by
  obtain ⟨a, c', he, hac⟩ := exists_thirdVariableEquiv_chartPolynomial c
  rw [← MulEquiv.irreducible_iff thirdVariableEquiv, he]
  refine Polynomial.irreducible_of_discrim_neg (MvPolynomial.eval fun _ => (1 : ℚ)) ?_ ?_
  · rcases hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨1, -(X 1 * X 0), 0, by ring⟩
    · exact ⟨0, -(X 1 * X 0), 1, by ring⟩
  · rcases hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num

/-- The local equations do not divide the chart coordinates. -/
theorem not_dvd_X_chartPolynomial (c : Fin 3 → Fin 2) (i : Fin 3) :
    ¬ map (Int.castRingHom ℚ) (triquadraticChartPolynomial cyclicTriquadricCoefficients c) ∣
      X i := by
  intro hdvd
  obtain ⟨a, c', he, hac⟩ := exists_thirdVariableEquiv_chartPolynomial c
  have ha : a ≠ 0 := by
    rcases hac with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> intro h0 <;>
      simpa using congrArg (MvPolynomial.eval fun _ => (1 : ℚ)) h0
  have hdeg : (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C (X 1 * X 0) * Polynomial.X +
      Polynomial.C c').natDegree = 2 := Polynomial.natDegree_quadratic ha
  have h := map_dvd thirdVariableEquiv hdvd
  rw [he] at h
  have hX : thirdVariableEquiv (X i) ≠ 0 :=
    (map_ne_zero_iff _ thirdVariableEquiv.injective).mpr (X_ne_zero i)
  have hle := Polynomial.natDegree_le_of_dvd h hX
  rw [hdeg] at hle
  fin_cases i
  · rw [show ((⟨0, by decide⟩ : Fin 3)) = 0 from rfl, thirdVariableEquiv_X_zero,
      Polynomial.natDegree_C] at hle
    omega
  · rw [show ((⟨1, by decide⟩ : Fin 3)) = 1 from rfl, thirdVariableEquiv_X_one,
      Polynomial.natDegree_C] at hle
    omega
  · rw [show ((⟨2, by decide⟩ : Fin 3)) = 2 from rfl, thirdVariableEquiv_X_two,
      Polynomial.natDegree_X] at hle
    omega

/-- The local equations are prime. -/
theorem prime_chartPolynomial (c : Fin 3 → Fin 2) :
    Prime (map (Int.castRingHom ℚ)
      (triquadraticChartPolynomial cyclicTriquadricCoefficients c)) :=
  (irreducible_chartPolynomial c).prime

/-- The quotient of `ℚ[x₀, x₁, x₂]` by a local equation is a domain. -/
instance isDomain_quotient_chartPolynomial (c : Fin 3 → Fin 2) :
    IsDomain (MvPolynomial (Fin 3) ℚ ⧸ Ideal.span
      {map (Int.castRingHom ℚ) (triquadraticChartPolynomial cyclicTriquadricCoefficients c)}) :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr
    ((Ideal.span_singleton_prime (prime_chartPolynomial c).ne_zero).mpr (prime_chartPolynomial c))

/-! ### The coefficients have no common zero -/

/-- The dehomogenizations on the chart `c` of the coefficients `A`, `B`, `C` of `F`, in which the
monomial `m_k` of the `i`-th factor becomes `X i ^ dehomExponent (c i) k`; in particular `B`
becomes `X 0 * X 1`. -/
theorem biquadraticChartPolynomial_cyclicTriquadricCoefficients (c : Fin 3 → Fin 2) :
    (biquadraticChartPolynomial (fun i j => cyclicTriquadricCoefficients i j 0) c =
      X 0 ^ dehomExponent (c 0) 2 * X 1 ^ dehomExponent (c 1) 0 +
        X 0 ^ dehomExponent (c 0) 0 * X 1 ^ dehomExponent (c 1) 2) ∧
    (biquadraticChartPolynomial (fun i j => cyclicTriquadricCoefficients i j 1) c =
      X 0 * X 1) ∧
    (biquadraticChartPolynomial (fun i j => cyclicTriquadricCoefficients i j 2) c =
      X 0 ^ dehomExponent (c 0) 0 * X 1 ^ dehomExponent (c 1) 0 +
        X 0 ^ dehomExponent (c 0) 2 * X 1 ^ dehomExponent (c 1) 2) := by
  have h1 : ∀ a : Fin 2, dehomExponent a 1 = 1 := by decide
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [biquadraticChartPolynomial, Fin.sum_univ_three, cyclicTriquadricCoefficients, h1,
      add_comm]

/-- **On every chart the dehomogenized coefficients generate the unit ideal**: one of `a, c` is
`1 + x²y²` and `b = xy`, and `(1 + x²y²) - xy · xy = 1`. -/
theorem span_biquadraticChartPolynomial_eq_top (c : Fin 3 → Fin 2) :
    Ideal.span (Set.range fun l : Fin 3 => MvPolynomial.map (Int.castRingHom ℚ)
      (biquadraticChartPolynomial (fun i j => cyclicTriquadricCoefficients i j l) c)) = ⊤ := by
  obtain ⟨h0, h1, h2⟩ := biquadraticChartPolynomial_cyclicTriquadricCoefficients c
  rw [Ideal.eq_top_iff_one]
  set I := Ideal.span (Set.range fun l : Fin 3 => MvPolynomial.map (Int.castRingHom ℚ)
    (biquadraticChartPolynomial (fun i j => cyclicTriquadricCoefficients i j l) c)) with hI
  have hmem : ∀ l : Fin 3, MvPolynomial.map (Int.castRingHom ℚ)
      (biquadraticChartPolynomial (fun i j => cyclicTriquadricCoefficients i j l) c) ∈ I :=
    fun l => Ideal.subset_span ⟨l, rfl⟩
  have hb := hmem 1
  rw [h1] at hb
  simp only [map_mul, MvPolynomial.map_X] at hb
  have key : ∀ q, q ∈ I → q = 1 + X 0 ^ 2 * X 1 ^ 2 → (1 : MvPolynomial (Fin 3) ℚ) ∈ I := by
    intro q hq hqe
    have := Ideal.sub_mem _ hq (Ideal.mul_mem_left _ (X 0 * X 1) hb)
    rw [hqe] at this
    convert this using 1
    ring
  have ha := hmem 0
  have hc := hmem 2
  rw [h0] at ha
  rw [h2] at hc
  simp only [map_add, map_mul, map_pow, MvPolynomial.map_X] at ha hc
  generalize c 0 = c0 at ha hc
  generalize c 1 = c1 at ha hc
  fin_cases c0 <;> fin_cases c1
  · exact key _ hc (by simp [dehomExponent])
  · exact key _ ha (by simp [dehomExponent]; ring)
  · exact key _ ha (by simp [dehomExponent])
  · exact key _ hc (by simp [dehomExponent]; ring)

/-- **The coefficients `A, B, C` of the cyclically symmetric triquadric have no common zero on
`ℙ¹ × ℙ¹ × ℙ¹`.** -/
theorem exists_mem_nonvanishingOpen_cyclicTriquadricCoefficient
    (x : projectiveLineCube (Spec (.of ℚ))) :
    ∃ l, x ∈ Stacks.SheafOfModules.nonvanishingOpen
      (X := (projectiveLineCube (Spec (.of ℚ))).toRingedSpace) (biquadraticModule _)
      (Stacks.SheafOfModules.sectionsOfTop (biquadraticModule _)
        (triquadraticCoefficient cyclicTriquadricCoefficients (Spec (.of ℚ)) l)) :=
  exists_mem_nonvanishingOpen_triquadraticCoefficient ℚ cyclicTriquadricCoefficients
    span_biquadraticChartPolynomial_eq_top x

/-- **`A, B, C` generate `M = 𝓗₀² ⊗ 𝓗₁²` at every stalk**: the coefficients of the cyclically
symmetric triquadric form a generating triple, the hypothesis under which the covering involution
of the projection to the first two factors exists. -/
theorem generatesStalks_triquadraticCoefficient_cyclicTriquadricCoefficients :
    Stacks.ProjectiveFromSections.GeneratesStalks
      (triquadraticCoefficient cyclicTriquadricCoefficients (Spec (.of ℚ))) :=
  Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => by
    obtain ⟨l, hl⟩ := exists_mem_nonvanishingOpen_cyclicTriquadricCoefficient x
    refine ⟨l, ?_⟩
    have h := Stacks.AmplePredicateBridge.coe_nonvanishingOpen_sectionsOfTop _
      (biquadraticModule _) (triquadraticCoefficient cyclicTriquadricCoefficients (Spec (.of ℚ)) l)
    have hx : x ∈ Stacks.Ample.nonvanishingLocus (biquadraticModule _)
        (triquadraticCoefficient cyclicTriquadricCoefficients (Spec (.of ℚ)) l) := h ▸ hl
    exact hx

/-! ### The charts of the surface -/

/-- The ring of sections of every chart of the surface is a domain. -/
instance isDomain_surfaceChart (c : Fin 3 → Fin 2) :
    IsDomain Γ(cyclicTriquadric, surfaceChart ℚ cyclicTriquadricCoefficients c) :=
  MulEquiv.isDomain _ (surfaceChartEquiv ℚ cyclicTriquadricCoefficients c).symm.toMulEquiv

/-- **Every chart of the surface has dimension two.** -/
theorem topologicalKrullDim_surfaceChart (c : Fin 3 → Fin 2) :
    topologicalKrullDim (surfaceChart ℚ cyclicTriquadricCoefficients c) = (2 : ℕ) := by
  rw [(isAffineOpen_surfaceChart ℚ cyclicTriquadricCoefficients c).topologicalKrullDim_eq,
    ← ringKrullDim_eq_of_ringEquiv (surfaceChartEquiv ℚ cyclicTriquadricCoefficients c)]
  exact Stacks.MvPolynomial.ringKrullDim_quotient_span_singleton ℚ (Fin 3) (by simp) _
    (prime_chartPolynomial c).ne_zero (prime_chartPolynomial c).not_isUnit

/-- The cyclically symmetric triquadratic surface is reduced. -/
instance isReduced_cyclicTriquadric : IsReduced cyclicTriquadric := by
  let 𝒰 := Scheme.openCoverOfIsOpenCover _ _ (iSup_surfaceChart ℚ cyclicTriquadricCoefficients)
  have : ∀ c, IsReduced (𝒰.X c) := fun c => by
    have := isDomain_surfaceChart c
    exact (isAffineOpen_surfaceChart ℚ cyclicTriquadricCoefficients c).isReduced
  exact IsReduced.of_openCover _ 𝒰

/-- The chart `x₀ y₀ z₀ ≠ 0`. -/
abbrev originChart : Fin 3 → Fin 2 := fun _ => 0

/-- The function `x y z` on the chart `x₀ y₀ z₀ ≠ 0` of the surface. -/
def coordinateProduct :
    Γ(cyclicTriquadric, surfaceChart ℚ cyclicTriquadricCoefficients originChart) :=
  ((triquadraticSurfaceι cyclicTriquadricCoefficients _).app (chartOpen _ originChart)).hom
    (chartRingHom ℚ originChart (X 0 * X 1 * X 2))

/-- The function `x y z` on the chart `x₀ y₀ z₀ ≠ 0` of the surface is nonzero. -/
theorem coordinateProduct_ne_zero : coordinateProduct ≠ 0 := by
  rw [coordinateProduct, ← surfaceChartEquiv_mk, Ne, map_eq_zero_iff _ (RingEquiv.injective _),
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  intro h
  have hp := prime_chartPolynomial originChart
  rcases hp.dvd_or_dvd h with h' | h'
  · rcases hp.dvd_or_dvd h' with h'' | h''
    · exact not_dvd_X_chartPolynomial originChart 0 h''
    · exact not_dvd_X_chartPolynomial originChart 1 h''
  · exact not_dvd_X_chartPolynomial originChart 2 h'

/-- **The charts of the surface have a common point**: a point of the chart `x₀ y₀ z₀ ≠ 0` at
which `x y z ≠ 0`. -/
theorem exists_forall_mem_surfaceChart :
    ∃ s : cyclicTriquadric, ∀ c, s ∈ surfaceChart ℚ cyclicTriquadricCoefficients c := by
  have hne : cyclicTriquadric.basicOpen coordinateProduct ≠ ⊥ := fun h =>
    coordinateProduct_ne_zero ((basicOpen_eq_bot_iff _).mp h)
  obtain ⟨s, hs⟩ := (Opens.ne_bot_iff_nonempty _).mp hne
  refine ⟨s, fun c => ?_⟩
  have hs' : triquadraticSurfaceι cyclicTriquadricCoefficients _ s ∈
      (projectiveLineCube (Spec (.of ℚ))).basicOpen
        (chartRingHom ℚ originChart (X 0 * X 1 * X 2)) := by
    rw [coordinateProduct, ← Scheme.preimage_basicOpen] at hs
    exact hs
  simp only [map_mul, chartRingHom_X, Scheme.basicOpen_mul, basicOpen_chartCoordinate] at hs'
  refine (mem_chartOpen_iff _ c _).mpr fun i => ?_
  have h0 : cubeProduct.proj _ _ i (triquadraticSurfaceι cyclicTriquadricCoefficients _ s) ∈
      projectiveLineBasicOpen.{0} 0 :=
    (mem_chartOpen_iff _ originChart _).mp hs'.1.1.1 i
  have h1 : cubeProduct.proj _ _ i (triquadraticSurfaceι cyclicTriquadricCoefficients _ s) ∈
      projectiveLineBasicOpen.{0} 1 := by
    fin_cases i
    · exact hs'.1.1.2
    · exact hs'.1.2.2
    · exact hs'.2.2
  rcases Fin.exists_fin_two.mp ⟨c i, rfl⟩ with h | h
  · rw [h]; exact h0
  · rw [h]; exact h1

/-- The cyclically symmetric triquadratic surface is irreducible. -/
instance irreducibleSpace_cyclicTriquadric : IrreducibleSpace cyclicTriquadric := by
  obtain ⟨s, hs⟩ := exists_forall_mem_surfaceChart
  refine irreducibleSpace_of_isOpen_cover
    (fun c => ((surfaceChart ℚ cyclicTriquadricCoefficients c : cyclicTriquadric.Opens) :
      Set cyclicTriquadric)) (fun c => (surfaceChart ℚ cyclicTriquadricCoefficients c).isOpen)
    (fun c => ?_) (fun x => ?_) s hs
  · have := isDomain_surfaceChart c
    have hirr := (isAffineOpen_surfaceChart ℚ cyclicTriquadricCoefficients c).irreducibleSpace
    exact isIrreducible_iff_irreducibleSpace.mpr hirr
  · have hx : x ∈ ⨆ c, surfaceChart ℚ cyclicTriquadricCoefficients c := by
      rw [iSup_surfaceChart]; trivial
    exact Opens.mem_iSup.mp hx

/-- **The cyclically symmetric triquadratic surface is integral.** -/
instance isIntegral_cyclicTriquadric : IsIntegral cyclicTriquadric :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- **The cyclically symmetric triquadratic surface is a surface**: its dimension is `2`. -/
theorem topologicalKrullDim_cyclicTriquadric :
    topologicalKrullDim cyclicTriquadric = (2 : ℕ) := by
  refine le_antisymm (topologicalKrullDim_le_of_isOpen_cover
    (fun c => ((surfaceChart ℚ cyclicTriquadricCoefficients c : cyclicTriquadric.Opens) :
      Set cyclicTriquadric)) (fun c => (surfaceChart ℚ cyclicTriquadricCoefficients c).isOpen)
    (fun x => ?_) fun c => (topologicalKrullDim_surfaceChart c).le) ?_
  · have hx : x ∈ ⨆ c, surfaceChart ℚ cyclicTriquadricCoefficients c := by
      rw [iSup_surfaceChart]; trivial
    exact Opens.mem_iSup.mp hx
  · rw [← topologicalKrullDim_surfaceChart originChart]
    exact topologicalKrullDim_subspace_le _ _

end projectiveLineCube

end AlgebraicGeometry
