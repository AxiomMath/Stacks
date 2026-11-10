module

public import StacksFrontier.RingTheory.Koszul.ComparisonOddCellFiltration

/-!
# `R⟨x, z, u⟩` is graded free over `K_N` on the divided-power monomials `u⁽ᵐ⁾`

Let `f` be an element of a commutative ring `R` and let `N ≥ t ≥ 1`. The comparison algebra
`B_{N,t} = R⟨x, z, u⟩` of Tag 0GZ7 is the divided-power polynomial algebra in the even generator
`u` over its odd part `R⟨x, z⟩`, so as a graded module it is the direct sum over `m ∈ ℕ` of
copies of `R⟨x, z⟩`, the `m`-th copy being the multiples of the divided-power monomial `u⁽ᵐ⁾`.
The Koszul algebra `K_N = R⟨z⟩` acts through `κ : K_N → B_{N,t}`, which lands in the odd part,
so the decomposition is one of graded `K_N`-modules; and the differential is lower triangular
for it, since `d u⁽ᵐ⁾ = (z - f^{N-t} x) u⁽ᵐ⁻¹⁾` lowers the divided-power degree by exactly one.

This file records the decomposition as an instance of
`DifferentialGradedModule.ExhaustiveCellData` and concludes that `B_{N,t}`, as a left
differential graded `K_N`-module, is orthogonal on the left to the acyclic modules. The graded
pieces are the shifts of the odd part `R⟨x, z⟩` by `2 m`, which is the cohomological degree of
`u⁽ᵐ⁾`, and their orthogonality is
`Koszul.leftOrthogonal_acyclic_shift_comparisonOddRestrictedModule`.

The decomposition is infinite and no finite one exists: the differential takes the `m`-th piece
strictly into the `(m-1)`-st, so the pieces form a strictly descending chain of infinite length,
while the filtration by the degree in `x` is triangular in neither direction because
`d x = f^t` is nonzero. This is why the criterion used is the unbounded one.

## Main definitions

* `Koszul.comparisonOppCoeffEquiv`: the coordinates of `B_{N,t}` over `K_N`, that is, the family
  of coefficients of the divided-power monomials `u⁽ᵐ⁾`, read on the graded opposite algebras.
* `Koszul.exhaustiveCellDataComparisonRestrictedModule`: the unbounded triangular cell
  decomposition of `B_{N,t}` over `K_N` by divided-power degree.

## Main results

* `DividedPowers.TateResolution.EvenVariableAlgebra.mem_cohomologicalGrade_iff`: a
  divided-power polynomial is homogeneous of cohomological degree `n` exactly when its
  coefficient of `T⁽ᵐ⁾` is homogeneous of cohomological degree `n + d m`, where `d` is the degree
  of the variable.
* `DividedPowers.TateResolution.coeff_evenPolynomialDifferential`: the coefficient of `T⁽ⁿ⁾` in
  the differential of a divided-power polynomial is `d aₙ ± aₙ₊₁ c`, where `c` is the value of
  the differential on the variable.
* `Koszul.comparisonOppCoeffEquiv_mul`: the coordinates are compatible with multiplication by
  the image of a scalar of `K_N`. The two Koszul signs differ by the sign of `2 m` against the
  degree of the scalar, which is trivial.
* `Koszul.leftOrthogonal_acyclic_comparisonRestrictedModule`: `B_{N,t}`, as a left differential
  graded `K_N`-module, is orthogonal on the left to the acyclic modules.

## Implementation notes

The underlying graded module of a graded opposite algebra is opaque, reachable only through the
linear equivalence `DifferentialGradedAlgebra.Opposite.equiv`, so every statement below is proved
by pushing it across that equivalence to the corresponding statement about `B_{N,t}` and
`R⟨x, z⟩` themselves. The three compatibilities then come down to three facts about divided-power
polynomials: the homogeneous pieces are cut out coefficientwise, multiplication by a constant
acts coefficientwise, and the differential is `d aₙ ± aₙ₊₁ c` on the coefficient of `T⁽ⁿ⁾`.

Everything is stated for the graded opposite *algebra* rather than for the restricted *module*,
with the two identified only when the cell data is assembled. The right action of the graded
opposite of `K_N` on `B_{N,t}` is by definition multiplication by the image of the scalar, and
the differential of the `m`-th graded piece is by definition `(-1)^(2 m)` times that of the odd
part, so the fields of `DifferentialGradedModule.ExhaustiveCellData` are filled by the
algebra-level statements verbatim.

*Where the signs cancel.* For a scalar of degree `α` and an element of degree `n`, the graded
opposite algebra multiplies with the sign `(-1)^(n α)`, while on the coefficient of `u⁽ᵐ⁾`, which
has degree `n + 2 m`, the same multiplication carries `(-1)^((n + 2 m) α)`. The two differ by
`(-1)^(2 m α) = 1`. The shifted differential carries `(-1)^(2 m) = 1` for the same reason.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
* [Stacks Project, Tag 09PI](https://stacks.math.columbia.edu/tag/09PI), adjoining an even
  divided-power variable.
* [Stacks Project, Tag 09JG](https://stacks.math.columbia.edu/tag/09JG), the graded opposite
  algebra.
* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM), orthogonality to the
  acyclic modules.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped DirectSum ExteriorAlgebra

universe u v

namespace DividedPowers.TateResolution

namespace EvenVariableAlgebra

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- **The identification of a divided-power polynomial algebra with its coefficient families**,
as an `R`-linear equivalence. -/
def coeffLinearEquiv : EvenVariableAlgebra A ≃ₗ[R] (ℕ →₀ A) where
  toFun x := x.coeff
  map_add' := coeff_add
  map_smul' := coeff_smul
  invFun g := ⟨g⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `coeffLinearEquiv` sends an element to its family of coefficients. -/
theorem coeffLinearEquiv_apply (x : EvenVariableAlgebra A) :
    coeffLinearEquiv (R := R) x = x.coeff := rfl

/-- Multiplication by an integer is coefficientwise. -/
theorem coeff_zsmul (c : ℤ) (x : EvenVariableAlgebra A) (n : ℕ) :
    (c • x).coeff n = c • x.coeff n := by
  let φ : EvenVariableAlgebra A →+ A :=
    { toFun := fun y => y.coeff n
      map_zero' := by simp
      map_add' := fun y z => by simp }
  exact map_zsmul φ c x

/-- **Multiplication by a constant is coefficientwise.** The divided-power rule
`T⁽⁰⁾ T⁽ᵐ⁾ = T⁽ᵐ⁾` carries no binomial coefficient, so a constant multiplies each coefficient
without mixing them. -/
theorem coeff_coeffEmbedding_mul (a : A) (y : EvenVariableAlgebra A) (n : ℕ) :
    (coeffEmbedding a * y).coeff n = a * y.coeff n := by
  classical
  induction y using induction_on with
  | zero => simp
  | add k b y hy =>
      have hstep : coeffEmbedding a * (monomial k b + y)
          = monomial k (a * b) + coeffEmbedding a * y := by
        rw [mul_add, coeffEmbedding_apply, monomial_mul_monomial]
        simp
      rw [hstep, coeff_add, Finsupp.add_apply, hy, coeff_add, Finsupp.add_apply,
        coeff_monomial, coeff_monomial, mul_add]
      congr 1
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp

/-- The cohomological degree of the coefficient of `T⁽ᵐ⁾` of an element of homological degree
`k`: the condition `m d ≤ k` is exactly the nonpositivity of `-k + d m`. -/
theorem cohomologicalGrade_neg_natCast_add (𝒜 : ℕ → Submodule R A) (d k m : ℕ) :
    cohomologicalGrade 𝒜 (-(k : ℤ) + (d : ℤ) * (m : ℤ))
      = if m * d ≤ k then 𝒜 (k - m * d) else ⊥ := by
  by_cases hmd : m * d ≤ k
  · have hcast : -(k : ℤ) + (d : ℤ) * (m : ℤ) = -((k - m * d : ℕ) : ℤ) := by
      rw [Nat.cast_sub hmd]
      push_cast
      ring
    rw [hcast, cohomologicalGrade_neg_natCast]
    simp [hmd]
  · have hlt : (k : ℤ) < (m : ℤ) * (d : ℤ) := by exact_mod_cast Nat.lt_of_not_le hmd
    have hpos : (0 : ℤ) < -(k : ℤ) + (d : ℤ) * (m : ℤ) := by linarith
    rw [cohomologicalGrade_of_pos 𝒜 hpos]
    simp [hmd]

/-- **A divided-power polynomial is homogeneous of cohomological degree `n` exactly when all of
its coefficients are**: the coefficient of `T⁽ᵐ⁾` must have cohomological degree `n + d m`,
where `d` is the degree of the variable. This is
`DividedPowers.TateResolution.EvenVariableAlgebra.mem_grade_iff` read cohomologically. -/
theorem mem_cohomologicalGrade_iff (𝒜 : ℕ → Submodule R A) (d : ℕ) (n : ℤ)
    (x : EvenVariableAlgebra A) :
    x ∈ cohomologicalGrade (grade 𝒜 d) n ↔
      ∀ m : ℕ, x.coeff m ∈ cohomologicalGrade 𝒜 (n + (d : ℤ) * (m : ℤ)) := by
  by_cases hn : n ≤ 0
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
    rw [cohomologicalGrade_neg_natCast, mem_grade_iff]
    exact forall_congr' fun m => by rw [cohomologicalGrade_neg_natCast_add 𝒜 d k m]
  · have hdm : ∀ m : ℕ, (0 : ℤ) < n + (d : ℤ) * (m : ℤ) := fun m => by
      have : (0 : ℤ) ≤ (d : ℤ) * (m : ℤ) := by positivity
      omega
    simp only [cohomologicalGrade_of_pos (grade 𝒜 d) (show (0 : ℤ) < n by omega),
      cohomologicalGrade_of_pos 𝒜 (hdm _), Submodule.mem_bot]
    constructor
    · intro hx m
      simp [hx]
    · intro hx
      exact EvenVariableAlgebra.ext (Finsupp.ext fun m => by simpa using hx m)

end EvenVariableAlgebra

section Differential

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- **The coefficient of `T⁽ⁿ⁾` in the differential of a divided-power monomial.** This is
`DividedPowers.TateResolution.evenPolynomialDifferential_monomial` read coefficientwise. -/
theorem coeff_evenPolynomialDifferential_monomial (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) (c : A) (k n : ℕ) (a : A) :
    (evenPolynomialDifferential 𝒜 dA c (EvenVariableAlgebra.monomial k a)).coeff n =
      dA ((EvenVariableAlgebra.monomial k a).coeff n) +
        signRingHom 𝒜 1 ((EvenVariableAlgebra.monomial k a).coeff (n + 1)) * c := by
  classical
  have hsame : ∀ (j : ℕ) (b : A), (EvenVariableAlgebra.monomial j b).coeff j = b :=
    fun j b => by rw [EvenVariableAlgebra.coeff_monomial, Finsupp.single_eq_same]
  have hne : ∀ (j p : ℕ) (b : A), j ≠ p → (EvenVariableAlgebra.monomial j b).coeff p = 0 :=
    fun j p b hjp => by
      rw [EvenVariableAlgebra.coeff_monomial, Finsupp.single_eq_of_ne' hjp]
  rw [evenPolynomialDifferential_monomial]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [ite_eq_left rfl, add_zero]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [hsame, hsame, hne 0 1 a (by omega)]
      simp
    · rw [hne 0 n (dA a) (by omega), hne 0 n a (by omega), hne 0 (n + 1) a (by omega)]
      simp
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 1 := ⟨k - 1, by omega⟩
    rw [ite_eq_right (Nat.succ_ne_zero j), Nat.add_sub_cancel, EvenVariableAlgebra.coeff_add,
      Finsupp.add_apply]
    by_cases hn : j + 1 = n
    · subst hn
      rw [hsame, hne j (j + 1) (signRingHom 𝒜 1 a * c) (by omega), hsame,
        hne (j + 1) (j + 1 + 1) a (by omega)]
      simp
    · by_cases hj : j = n
      · subst hj
        rw [hne (j + 1) j (dA a) (by omega), hsame, hne (j + 1) j a (by omega), hsame]
        simp
      · rw [hne (j + 1) n (dA a) hn, hne j n (signRingHom 𝒜 1 a * c) hj,
          hne (j + 1) n a hn, hne (j + 1) (n + 1) a (by omega)]
        simp

/-- **The coefficient of `T⁽ⁿ⁾` in the differential of a divided-power polynomial** is
`d aₙ ± aₙ₊₁ c`, where `c` is the value of the differential on the variable and the sign is the
grading sign of `aₙ₊₁`. -/
theorem coeff_evenPolynomialDifferential (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) (c : A) (x : EvenVariableAlgebra A) (n : ℕ) :
    (evenPolynomialDifferential 𝒜 dA c x).coeff n =
      dA (x.coeff n) + signRingHom 𝒜 1 (x.coeff (n + 1)) * c := by
  induction x using EvenVariableAlgebra.induction_on with
  | zero => simp
  | add k a y hy =>
      rw [map_add]
      simp only [EvenVariableAlgebra.coeff_add, Finsupp.add_apply, map_add, add_mul]
      rw [coeff_evenPolynomialDifferential_monomial 𝒜 dA c k n a, hy]
      abel

end Differential

end DividedPowers.TateResolution

namespace Koszul

open DifferentialGradedAlgebra DifferentialGradedModule DifferentialGraded.Bimodule
open DividedPowers.TateResolution

variable {R : Type u} [CommRing R]

/-! ### The three algebras, read as divided-power and exterior data -/

/-- **The graded opposite of `K_N`, identified with the exterior algebra on `R`.** The graded
opposite algebra is opaque, so its underlying graded module is reachable only through this
identification. -/
def powOneOppEquiv (f : R) (N : ℕ) :
    (oppAlgebra (powOne f N)).A ≃ₗ[R] ExteriorAlgebra R (Fin 1 → R) :=
  (opposite R (powOne f N)).equiv.trans (LinearEquiv.refl R (ExteriorAlgebra R (Fin 1 → R)))

/-- **The graded opposite of the odd part `R⟨x, z⟩`, identified with the exterior algebra on
`R²`.** -/
def comparisonOddOppEquiv (f : R) (N t : ℕ) :
    (oppAlgebra (comparisonOddAlgebra f N t)).A ≃ₗ[R] comparisonExterior R :=
  (opposite R (comparisonOddAlgebra f N t)).equiv.trans
    (LinearEquiv.refl R (comparisonExterior R))

/-- **The graded opposite of `B_{N,t}`, identified with the divided-power polynomial algebra in
`u` over the odd part `R⟨x, z⟩`.** -/
def comparisonOppEquiv (f : R) {N t : ℕ} (h : t ≤ N) :
    (oppAlgebra (comparisonAlgebra f h)).A ≃ₗ[R]
      EvenVariableAlgebra (comparisonExterior R) :=
  (opposite R (comparisonAlgebra f h)).equiv.trans
    (LinearEquiv.refl R (EvenVariableAlgebra (comparisonExterior R)))

/-- Homogeneity in `B_{N,t}` is homogeneity of the divided-power polynomial, read
cohomologically. -/
theorem comparisonOppEquiv_mem_grading_iff (f : R) {N t : ℕ} (h : t ≤ N) (n : ℤ)
    (x : (oppAlgebra (comparisonAlgebra f h)).A) :
    x ∈ (oppAlgebra (comparisonAlgebra f h)).grading n ↔
      comparisonOppEquiv f h x ∈
        cohomologicalGrade (EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2) n :=
  (opposite R (comparisonAlgebra f h)).mem_grading_iff n x

/-- Homogeneity in the odd part `R⟨x, z⟩` is homogeneity in the exterior algebra, read
cohomologically. -/
theorem comparisonOddOppEquiv_mem_grading_iff (f : R) (N t : ℕ) (n : ℤ)
    (y : (oppAlgebra (comparisonOddAlgebra f N t)).A) :
    y ∈ (oppAlgebra (comparisonOddAlgebra f N t)).grading n ↔
      comparisonOddOppEquiv f N t y ∈ cohomologicalGrade (exteriorGrade R (Fin 2 → R)) n :=
  (opposite R (comparisonOddAlgebra f N t)).mem_grading_iff n y

/-- Under the identification the differential of `B_{N,t}` is the divided-power
differential. -/
theorem comparisonOppEquiv_d (f : R) {N t : ℕ} (h : t ≤ N)
    (x : (oppAlgebra (comparisonAlgebra f h)).A) :
    comparisonOppEquiv f h ((oppAlgebra (comparisonAlgebra f h)).d x)
      = comparisonDifferential f N t (comparisonOppEquiv f h x) :=
  (opposite R (comparisonAlgebra f h)).map_d x

/-- Under the identification the differential of the odd part is the Koszul contraction. -/
theorem comparisonOddOppEquiv_d (f : R) (N t : ℕ)
    (y : (oppAlgebra (comparisonOddAlgebra f N t)).A) :
    comparisonOddOppEquiv f N t ((oppAlgebra (comparisonOddAlgebra f N t)).d y)
      = comparisonExteriorDifferential f N t (comparisonOddOppEquiv f N t y) :=
  (opposite R (comparisonOddAlgebra f N t)).map_d y

/-- Multiplication in the graded opposite of `B_{N,t}`, on homogeneous elements. -/
theorem comparisonOppEquiv_mul_of_mem (f : R) {N t : ℕ} (h : t ≤ N) (n α : ℤ)
    (x c : (oppAlgebra (comparisonAlgebra f h)).A)
    (hx : x ∈ (oppAlgebra (comparisonAlgebra f h)).grading n)
    (hc : c ∈ (oppAlgebra (comparisonAlgebra f h)).grading α) :
    comparisonOppEquiv f h (x * c)
      = ((n * α).negOnePow : ℤ) • (comparisonOppEquiv f h c * comparisonOppEquiv f h x) :=
  (opposite R (comparisonAlgebra f h)).map_mul_of_mem n α x c hx hc

/-- Multiplication in the graded opposite of the odd part, on homogeneous elements. -/
theorem comparisonOddOppEquiv_mul_of_mem (f : R) (N t : ℕ) (n α : ℤ)
    (y c : (oppAlgebra (comparisonOddAlgebra f N t)).A)
    (hy : y ∈ (oppAlgebra (comparisonOddAlgebra f N t)).grading n)
    (hc : c ∈ (oppAlgebra (comparisonOddAlgebra f N t)).grading α) :
    comparisonOddOppEquiv f N t (y * c)
      = ((n * α).negOnePow : ℤ) •
        (comparisonOddOppEquiv f N t c * comparisonOddOppEquiv f N t y) :=
  (opposite R (comparisonOddAlgebra f N t)).map_mul_of_mem n α y c hy hc

/-! ### The image of a scalar of `K_N` -/

/-- **The image in the odd part `R⟨x, z⟩` of a scalar of the graded opposite of `K_N`**: the
generator of `K_N` goes to the odd generator `z`. -/
theorem comparisonOddOppEquiv_oppHom (f : R) (N t : ℕ) (a : (oppAlgebra (powOne f N)).A) :
    comparisonOddOppEquiv f N t ((oppHom (koszulToComparisonOdd f N t)).toAlgebraHom a)
      = ExteriorAlgebra.map (zInclusion R) (powOneOppEquiv f N a) :=
  (opposite R (comparisonOddAlgebra f N t)).equiv.apply_symm_apply
    ((koszulToComparisonOdd f N t).toAlgebraHom ((opposite R (powOne f N)).equiv a))

/-- **The image in `B_{N,t}` of a scalar of the graded opposite of `K_N`**: it is the constant
divided-power polynomial whose coefficient is the image in the odd part, because `κ` lands in the
odd part and carries no power of `f`. -/
theorem comparisonOppEquiv_oppKoszulToComparison (f : R) {N t : ℕ} (h : t ≤ N)
    (a : (oppAlgebra (powOne f N)).A) :
    comparisonOppEquiv f h ((oppKoszulToComparison f h).toAlgebraHom a)
      = EvenVariableAlgebra.coeffEmbedding
        (ExteriorAlgebra.map (zInclusion R) (powOneOppEquiv f N a)) :=
  (opposite R (comparisonAlgebra f h)).equiv.apply_symm_apply
    ((koszulToComparison f h).toAlgebraHom ((opposite R (powOne f N)).equiv a))

/-! ### The coordinates of `B_{N,t}` over `K_N` -/

/-- **The coordinates of `B_{N,t}` over `K_N`**: the family of coefficients of the divided-power
monomials `u⁽ᵐ⁾`, read through the identifications of the underlying graded modules with those of
the graded opposite algebras. -/
def comparisonOppCoeffEquiv (f : R) {N t : ℕ} (h : t ≤ N) :
    (oppAlgebra (comparisonAlgebra f h)).A ≃ₗ[R]
      ⨁ (_ : ℕ), (oppAlgebra (comparisonOddAlgebra f N t)).A :=
  (((comparisonOppEquiv f h).trans (EvenVariableAlgebra.coeffLinearEquiv (R := R))).trans
      (finsuppLEquivDirectSum R (comparisonExterior R) ℕ)).trans
    (DirectSum.congrLinearEquiv fun _ => (comparisonOddOppEquiv f N t).symm)

/-- Each coordinate is the corresponding coefficient of the divided-power expansion, read
through the identification of the underlying graded modules. -/
theorem comparisonOppCoeffEquiv_apply (f : R) {N t : ℕ} (h : t ≤ N)
    (x : (oppAlgebra (comparisonAlgebra f h)).A) (m : ℕ) :
    comparisonOddOppEquiv f N t ((comparisonOppCoeffEquiv f h x) m)
      = (comparisonOppEquiv f h x).coeff m :=
  (comparisonOddOppEquiv f N t).apply_symm_apply ((comparisonOppEquiv f h x).coeff m)

/-- A coordinate vanishes exactly when the corresponding coefficient does. -/
theorem comparisonOppCoeffEquiv_eq_zero_iff (f : R) {N t : ℕ} (h : t ≤ N)
    (x : (oppAlgebra (comparisonAlgebra f h)).A) (m : ℕ) :
    (comparisonOppCoeffEquiv f h x) m = 0 ↔ (comparisonOppEquiv f h x).coeff m = 0 := by
  rw [← comparisonOppCoeffEquiv_apply f h x m, LinearEquiv.map_eq_zero_iff]

/-! ### Compatibility with the grading -/

/-- **An element of `B_{N,t}` is homogeneous of degree `n` exactly when all of its coordinates
are**: the coordinate of divided-power degree `m` must have degree `n + 2 m`, the shift being the
cohomological degree of `u⁽ᵐ⁾`. -/
theorem comparisonOppCoeffEquiv_mem_grading_iff (f : R) {N t : ℕ} (h : t ≤ N) (n : ℤ)
    (x : (oppAlgebra (comparisonAlgebra f h)).A) :
    x ∈ (oppAlgebra (comparisonAlgebra f h)).grading n ↔
      ∀ m : ℕ, (comparisonOppCoeffEquiv f h x) m
        ∈ (oppAlgebra (comparisonOddAlgebra f N t)).grading (n + 2 * (m : ℤ)) := by
  rw [comparisonOppEquiv_mem_grading_iff f h n x,
    EvenVariableAlgebra.mem_cohomologicalGrade_iff]
  refine forall_congr' fun m => ?_
  rw [comparisonOddOppEquiv_mem_grading_iff f N t (n + 2 * (m : ℤ)),
    comparisonOppCoeffEquiv_apply f h x m]
  norm_num

/-! ### Compatibility with the action of `K_N` -/

/-- **The coordinates are compatible with multiplication by the image of a scalar of `K_N`**, for
a homogeneous scalar acting on a homogeneous element. The two Koszul signs differ by the sign of
`2 m` against the degree of the scalar, which is trivial. -/
theorem comparisonOppCoeffEquiv_mul_of_mem (f : R) {N t : ℕ} (h : t ≤ N) {α n : ℤ}
    {a : (oppAlgebra (powOne f N)).A} (ha : a ∈ (oppAlgebra (powOne f N)).grading α)
    {x : (oppAlgebra (comparisonAlgebra f h)).A}
    (hx : x ∈ (oppAlgebra (comparisonAlgebra f h)).grading n) (m : ℕ) :
    (comparisonOppCoeffEquiv f h (x * (oppKoszulToComparison f h).toAlgebraHom a)) m
      = (comparisonOppCoeffEquiv f h x) m *
          (oppHom (koszulToComparisonOdd f N t)).toAlgebraHom a := by
  have hcB : (oppKoszulToComparison f h).toAlgebraHom a
      ∈ (oppAlgebra (comparisonAlgebra f h)).grading α :=
    (oppKoszulToComparison f h).map_grading α a ha
  have hcO : (oppHom (koszulToComparisonOdd f N t)).toAlgebraHom a
      ∈ (oppAlgebra (comparisonOddAlgebra f N t)).grading α :=
    (oppHom (koszulToComparisonOdd f N t)).map_grading α a ha
  have hz : (comparisonOppCoeffEquiv f h x) m
      ∈ (oppAlgebra (comparisonOddAlgebra f N t)).grading (n + 2 * (m : ℤ)) :=
    (comparisonOppCoeffEquiv_mem_grading_iff f h n x).1 hx m
  refine (comparisonOddOppEquiv f N t).injective ?_
  rw [comparisonOppCoeffEquiv_apply f h _ m,
    comparisonOppEquiv_mul_of_mem f h n α _ _ hx hcB,
    EvenVariableAlgebra.coeff_zsmul, comparisonOppEquiv_oppKoszulToComparison f h a,
    EvenVariableAlgebra.coeff_coeffEmbedding_mul,
    comparisonOddOppEquiv_mul_of_mem f N t (n + 2 * (m : ℤ)) α _ _ hz hcO,
    comparisonOddOppEquiv_oppHom f N t a, comparisonOppCoeffEquiv_apply f h x m]
  congr 1
  rw [show (n + 2 * (m : ℤ)) * α = n * α + 2 * ((m : ℤ) * α) by ring,
    Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

/-- **The coordinates are compatible with multiplication by the image of a scalar of `K_N`.**
Both sides are additive in the scalar and in the element, so this follows from
`Koszul.comparisonOppCoeffEquiv_mul_of_mem` by decomposing both into homogeneous pieces. -/
theorem comparisonOppCoeffEquiv_mul (f : R) {N t : ℕ} (h : t ≤ N)
    (a : (oppAlgebra (powOne f N)).A) (x : (oppAlgebra (comparisonAlgebra f h)).A) (m : ℕ) :
    (comparisonOppCoeffEquiv f h (x * (oppKoszulToComparison f h).toAlgebraHom a)) m
      = (comparisonOppCoeffEquiv f h x) m *
          (oppHom (koszulToComparisonOdd f N t)).toAlgebraHom a := by
  induction a using DirectSum.Decomposition.inductionOn (oppAlgebra (powOne f N)).grading with
  | zero => simp
  | add a b hA hB =>
      rw [map_add, mul_add, map_add, DirectSum.add_apply, hA, hB, map_add, mul_add]
  | @homogeneous α a =>
      induction x using DirectSum.Decomposition.inductionOn
        (oppAlgebra (comparisonAlgebra f h)).grading with
      | zero => simp
      | add x y hX hY =>
          rw [add_mul, map_add, DirectSum.add_apply, hX, hY, map_add, DirectSum.add_apply,
            add_mul]
      | @homogeneous n x =>
          exact comparisonOppCoeffEquiv_mul_of_mem f h a.property x.property m

/-! ### Triangularity of the differential -/

/-- **The coefficient of `u⁽ᵐ⁾` in the differential of `B_{N,t}`**: the differential of the
coefficient of `u⁽ᵐ⁾`, plus the coefficient of `u⁽ᵐ⁺¹⁾` against the cycle `z - f^{N-t} x` that
`u` kills. -/
theorem coeff_comparisonOppEquiv_d (f : R) {N t : ℕ} (h : t ≤ N)
    (x : (oppAlgebra (comparisonAlgebra f h)).A) (m : ℕ) :
    (comparisonOppEquiv f h ((oppAlgebra (comparisonAlgebra f h)).d x)).coeff m
      = comparisonExteriorDifferential f N t ((comparisonOppEquiv f h x).coeff m)
        + signRingHom (exteriorGrade R (Fin 2 → R)) 1
            ((comparisonOppEquiv f h x).coeff (m + 1))
          * comparisonCycle f N t := by
  rw [comparisonOppEquiv_d f h x]
  exact coeff_evenPolynomialDifferential (exteriorGrade R (Fin 2 → R))
    (comparisonExteriorDifferential f N t) (comparisonCycle f N t) _ m

/-- **The differential preserves the vanishing of the coordinates in high divided-power
degrees**: this is the lower triangularity of the differential of `B_{N,t}`, which lowers the
divided-power degree. -/
theorem comparisonOppCoeffEquiv_d_eq_zero (f : R) {N t : ℕ} (h : t ≤ N) (k : ℕ)
    (x : (oppAlgebra (comparisonAlgebra f h)).A)
    (hx : ∀ m : ℕ, k ≤ m → (comparisonOppCoeffEquiv f h x) m = 0) (m : ℕ) (hm : k ≤ m) :
    (comparisonOppCoeffEquiv f h ((oppAlgebra (comparisonAlgebra f h)).d x)) m = 0 := by
  simp only [comparisonOppCoeffEquiv_eq_zero_iff] at hx ⊢
  rw [coeff_comparisonOppEquiv_d f h x m, hx m hm, hx (m + 1) (by omega)]
  simp

/-- **On the top coordinate the differential of `B_{N,t}` is the differential of the odd part**,
with the sign of the shift `2 k`, which is trivial. -/
theorem comparisonOppCoeffEquiv_d (f : R) {N t : ℕ} (h : t ≤ N) (k : ℕ)
    (x : (oppAlgebra (comparisonAlgebra f h)).A)
    (hx : ∀ m : ℕ, k + 1 ≤ m → (comparisonOppCoeffEquiv f h x) m = 0) :
    (comparisonOppCoeffEquiv f h ((oppAlgebra (comparisonAlgebra f h)).d x)) k
      = ((2 * (k : ℤ)).negOnePow • (oppAlgebra (comparisonOddAlgebra f N t)).d)
          ((comparisonOppCoeffEquiv f h x) k) := by
  have h1 : (comparisonOppEquiv f h x).coeff (k + 1) = 0 :=
    (comparisonOppCoeffEquiv_eq_zero_iff f h x (k + 1)).1 (hx (k + 1) (by omega))
  refine (comparisonOddOppEquiv f N t).injective ?_
  rw [comparisonOppCoeffEquiv_apply f h _ k, LinearMap.smul_apply, Units.smul_def,
    Int.negOnePow_two_mul, Units.val_one, one_smul, comparisonOddOppEquiv_d f N t,
    comparisonOppCoeffEquiv_apply f h x k, coeff_comparisonOppEquiv_d f h x k, h1]
  simp

/-! ### The cell decomposition and orthogonality -/

/-- **The unbounded triangular cell decomposition of `B_{N,t}` over `K_N` by divided-power
degree.** The `m`-th graded piece is the odd part `R⟨x, z⟩` placed in the cohomological degree
`-2 m` of the divided-power monomial `u⁽ᵐ⁾`, the coordinates are the coefficients of that
expansion, and the differential lowers the divided-power degree by exactly one. -/
def exhaustiveCellDataComparisonRestrictedModule (f : R) {N t : ℕ} (h : t ≤ N) :
    ExhaustiveCellData (comparisonRestrictedModule f h) where
  layer m := shift (comparisonOddRestrictedModule f N t) (2 * (m : ℤ))
  layer_leftOrthogonal m :=
    leftOrthogonal_acyclic_shift_comparisonOddRestrictedModule f N t (2 * (m : ℤ))
  coords := comparisonOppCoeffEquiv f h
  coords_smul := comparisonOppCoeffEquiv_mul f h
  mem_grading_iff := comparisonOppCoeffEquiv_mem_grading_iff f h
  d_coords_eq_zero := comparisonOppCoeffEquiv_d_eq_zero f h
  d_coords := comparisonOppCoeffEquiv_d f h

/-- **`B_{N,t} = R⟨x, z, u⟩`, as a left differential graded `K_N`-module, is orthogonal on the
left to the acyclic modules.** It is graded free over `K_N` on the products of the divided-power
monomials `u⁽ᵐ⁾` with `1` and `x`: the structure map `κ : K_N → B_{N,t}` sends the generator of
`K_N` to `z` with no power of `f` attached, so the odd part `R⟨x, z⟩` is `K_N ⊗_R K_t`, and
`B_{N,t}` is the direct sum of its shifts by the degrees of the `u⁽ᵐ⁾`. -/
theorem leftOrthogonal_acyclic_comparisonRestrictedModule (f : R) {N t : ℕ} (h : t ≤ N) :
    (acyclic' (oppAlgebra (powOne f N))).leftOrthogonal
      ((toHomotopyCategory (oppAlgebra (powOne f N))).obj (comparisonRestrictedModule f h)) :=
  leftOrthogonal_acyclic_of_exhaustiveCellData
    (exhaustiveCellDataComparisonRestrictedModule f h)

end Koszul

end
