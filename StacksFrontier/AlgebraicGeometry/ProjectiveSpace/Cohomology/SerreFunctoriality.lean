module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistCechComplex

/-!
# Functoriality of the identifications of Serre's computation on projective space

Let `R` be a commutative ring, `n = N + 1 ≥ 1` and `d` an integer. [Stacks, Equation 01XU]
identifies the cohomology of the twist `𝒪(d)` on `ℙⁿ_R`:

$$ H^q(\mathbf{P}^n_R, \mathcal{O}(d)) =
  \begin{cases} (R[T_0, \ldots, T_n])_d & q = 0 \\
    0 & q \neq 0, n \\
    \operatorname{Hom}_R((R[T_0, \ldots, T_n])_{-n-1-d}, R) & q = n \end{cases} $$

[Stacks, Tag 01XV] makes two assertions about *those identifications*:

1. they are **compatible with base change** along a ring map `R → R'`;
2. for `f ∈ R[T₀, …, Tₙ]` homogeneous of degree `m`, multiplication by `f`,
   `𝒪(d) ⟶ 𝒪(d + m)`, induces **multiplication by `f`** on `H⁰` and the **contragredient of
   multiplication by `f`**, `(R[T₀, …, Tₙ])_{-n-1-(d+m)} ⟶ (R[T₀, …, Tₙ])_{-n-1-d}`, on `Hⁿ`.

Both are proved here for the **monomial Čech model** of the identifications of
[Stacks, Equation 01XU] — that is, for the two identifications
`Stacks.ProjectiveSpace.Cohomology.laurentCechCohomologyZeroEquiv` and
`Stacks.ProjectiveSpace.Cohomology.laurentCechCohomologyTopEquiv` of the cohomology of the
monomial Čech complex of the standard cover, out of which
`Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology` builds the sheaf-cohomology form of the
equation. Each of the four statements is an equality of two composites, i.e. a commuting square.

Base change is the coefficientwise map
`Stacks.ProjectiveSpace.Cohomology.baseChangeCochain`, which is the map of Čech complexes `γ`
sending "the basis elements for the Čech complex over `R` to the corresponding basis elements for
the Čech complex over `R'`", and multiplication by `f` is the map of Čech complexes
`Stacks.ProjectiveSpace.Cohomology.laurentCochainMul`; that each is a map of complexes is
`laurentCechDiff_baseChangeCochain` and `laurentCechDiff_laurentCochainMul`. On `H⁰` both
operations are read off the diagonal cocycle. On `Hⁿ` everything reduces to one identity for the
residue pairing of `Stacks.ProjectiveSpace.Cohomology.residuePairing`: a cohomology class is
paired with a polynomial by using *any* representative
(`topDualEquiv_topCechCohomologyEquiv_mk`), because a Čech coboundary is a sum of sections
regular along some variable and such a section pairs to zero with a polynomial. The
contragredient then comes from the adjunction `⟨f · g, h⟩ = ⟨g, f · h⟩`, both sides being the
coefficient of `1/(T₀ ⋯ Tₙ)` in `f · g · h`.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.laurentMul`: multiplication by a Laurent polynomial on the
  coefficient model, with `laurentMul_single_single` recording that it is the multiplication of
  the Laurent polynomial ring.
* `Stacks.ProjectiveSpace.Cohomology.chartOfHomogeneous`: a homogeneous polynomial of degree `m`
  read as an element of the degree-`m` monomial chart.
* `Stacks.ProjectiveSpace.Cohomology.chartMul` and
  `Stacks.ProjectiveSpace.Cohomology.laurentCechCochainMul`: multiplication by `f` on the charts
  and on the Čech cochains, from degree `d` to degree `d + m`.
* `Stacks.ProjectiveSpace.Cohomology.baseChangeLaurent`,
  `Stacks.ProjectiveSpace.Cohomology.baseChangeChart` and
  `Stacks.ProjectiveSpace.Cohomology.baseChangeCechCochain`: base change along `φ : R →+* R'`,
  as `φ`-semilinear maps.
* `Stacks.ProjectiveSpace.Cohomology.cocycleMulZero` and
  `Stacks.ProjectiveSpace.Cohomology.cocycleBaseChangeZero`: the induced maps on the degree-zero
  Čech cohomology.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.laurentCechDiffRestrict_laurentCechCochainMul` and
  `Stacks.ProjectiveSpace.Cohomology.laurentCechDiffRestrict_baseChangeCechCochain`: both
  operations are **maps of Čech complexes**.
* `Stacks.ProjectiveSpace.Cohomology.residuePairing_laurentMul`: **the residue pairing is adjoint
  to multiplication**, which is what makes the top-degree map a contragredient.
* `Stacks.ProjectiveSpace.Cohomology.topDualEquiv_topCechCohomologyEquiv_mk`: **the top-degree
  identification is the residue pairing with an arbitrary representative.**
* `Stacks.ProjectiveSpace.Cohomology.cocycleMulZero_comp_laurentCechCohomologyZeroEquiv` and
  `Stacks.ProjectiveSpace.Cohomology.laurentCechCohomologyTopEquiv_laurentCechCochainMul`:
  the second assertion of [Stacks, Tag 01XV] on the monomial Čech model, on `H⁰` and on `Hⁿ`.
* `Stacks.ProjectiveSpace.Cohomology.cocycleBaseChangeZero_comp_laurentCechCohomologyZeroEquiv`
  and `Stacks.ProjectiveSpace.Cohomology.laurentCechCohomologyTopEquiv_baseChangeCechCochain`:
  the first assertion of [Stacks, Tag 01XV] on the monomial Čech model, on `H⁰` and on `Hⁿ`.

## Implementation notes

Multiplication by `Tᵢ` can turn a Laurent monomial
with every exponent negative into one with a nonnegative exponent, so it does not preserve
`Stacks.ProjectiveSpace.Cohomology.negativeTwistPart`; the source notes this ("which is zero if
`eᵢ + bᵢ ≥ 0`"). That is why the top degree is handled through the residue pairing with an
arbitrary representative rather than through the explicit complement.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
* [Stacks Project, Tag 01XV](https://stacks.math.columbia.edu/tag/01XV)
* [Stacks Project, Tag 01FD](https://stacks.math.columbia.edu/tag/01FD)
-/

@[expose] public noncomputable section

open Finsupp

universe u v

namespace Stacks.ProjectiveSpace.Cohomology

variable {R : Type u} [CommRing R] {R' : Type v} [CommRing R'] {n : ℕ} {d e m : ℤ}

/-! ### Multiplication by a Laurent polynomial -/

/-- **Multiplication by a Laurent polynomial**, on the coefficient model of the Laurent
polynomials in `T₀, …, Tₙ`: the convolution `(f * g)_k = ∑_{a + b = k} f_a g_b`, written as the
sum over the monomials `T^a` occurring in `f` of `f_a` times the shift of `g` by `a`. -/
def laurentMul (f : (Fin (n + 1) → ℤ) →₀ R) :
    ((Fin (n + 1) → ℤ) →₀ R) →ₗ[R] ((Fin (n + 1) → ℤ) →₀ R) :=
  f.sum fun a c => c • Finsupp.lmapDomain R R (fun k => a + k)

/-- Multiplication by `f` is the sum over the monomials of `f` of the shifted multiples. -/
theorem laurentMul_apply (f g : (Fin (n + 1) → ℤ) →₀ R) :
    laurentMul f g = ∑ a ∈ f.support, f a • Finsupp.mapDomain (fun k => a + k) g := by
  rw [laurentMul, Finsupp.sum, LinearMap.sum_apply]
  rfl

/-- Multiplication by a single Laurent monomial `c · T^a` shifts the exponents by `a` and scales
by `c`. -/
theorem laurentMul_single (a : Fin (n + 1) → ℤ) (c : R) (g : (Fin (n + 1) → ℤ) →₀ R) :
    laurentMul (Finsupp.single a c) g = c • Finsupp.mapDomain (fun k => a + k) g := by
  have h0 : (0 : R) • Finsupp.lmapDomain R R (fun k => a + k)
      = (0 : ((Fin (n + 1) → ℤ) →₀ R) →ₗ[R] ((Fin (n + 1) → ℤ) →₀ R)) := zero_smul _ _
  rw [laurentMul, Finsupp.sum_single_index h0]
  rfl

/-- **The product of two Laurent monomials is the Laurent monomial of the sum of the exponents**,
with the product of the coefficients: `laurentMul` is the multiplication of the Laurent
polynomial ring. -/
theorem laurentMul_single_single (a b : Fin (n + 1) → ℤ) (c c' : R) :
    laurentMul (Finsupp.single a c) (Finsupp.single b c') = Finsupp.single (a + b) (c * c') := by
  rw [laurentMul_single, Finsupp.mapDomain_single, Finsupp.smul_single, smul_eq_mul]

/-- Multiplication by the zero polynomial is zero. -/
@[simp]
theorem laurentMul_zero_left (g : (Fin (n + 1) → ℤ) →₀ R) :
    laurentMul (0 : (Fin (n + 1) → ℤ) →₀ R) g = 0 := by
  rw [laurentMul_apply, Finsupp.support_zero, Finset.sum_empty]

/-- **Multiplication is additive in the multiplier.** Together with
`Stacks.ProjectiveSpace.Cohomology.laurentMul_single_single`, which computes it on monomials, and
linearity in the multiplicand, which is built into `laurentMul`, this identifies `laurentMul`
with the multiplication of the Laurent polynomial ring. -/
theorem laurentMul_add_left (f f' g : (Fin (n + 1) → ℤ) →₀ R) :
    laurentMul (f + f') g = laurentMul f g + laurentMul f' g := by
  have h : laurentMul (f + f') = laurentMul f + laurentMul f' :=
    Finsupp.sum_add_index' (fun a => zero_smul R (Finsupp.lmapDomain R R (fun k => a + k)))
      fun a b₁ b₂ => add_smul b₁ b₂ (Finsupp.lmapDomain R R (fun k => a + k))
  rw [h]
  rfl

/-- Shifting the exponents by a fixed vector is injective. -/
theorem injective_add_left (a : Fin (n + 1) → ℤ) :
    Function.Injective (fun k : Fin (n + 1) → ℤ => a + k) := fun _ _ hxy => by simpa using hxy

/-- **Multiplying a degree-`d` Laurent section by a degree-`m` homogeneous polynomial gives a
degree-`(d + m)` Laurent section on the same chart.** The polynomial inverts no variable, so the
set `S` of inverted variables is unchanged and only the total degree shifts. -/
theorem laurentMul_mem_twistChart {S : Set (Fin (n + 1))} {f g : (Fin (n + 1) → ℤ) →₀ R}
    (hf : f ∈ twistChart R n m (∅ : Set (Fin (n + 1)))) (hg : g ∈ twistChart R n d S)
    (hde : d + m = e) : laurentMul f g ∈ twistChart R n e S := by
  rw [laurentMul_apply]
  refine Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ ?_
  have ha' : a ∈ laurentMonomials n m (∅ : Set (Fin (n + 1))) :=
    mem_twistChart.1 hf (Finset.mem_coe.2 ha)
  refine mem_twistChart.2 fun k hk => ?_
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support (Finset.mem_coe.1 hk))
  have hb' : b ∈ laurentMonomials n d S := mem_twistChart.1 hg (Finset.mem_coe.2 hb)
  refine ⟨?_, fun i hi => add_nonneg (ha'.2 i (by simp)) (hb'.2 i hi)⟩
  have hsum : ∑ i, (a + b) i = (∑ i, a i) + ∑ i, b i := Finset.sum_add_distrib
  rw [hsum, ha'.1, hb'.1, add_comm]
  exact hde

/-- **The residue pairing is adjoint to a shift of the exponents.** -/
theorem residuePairing_mapDomain_add (a : Fin (n + 1) → ℤ) (g h : (Fin (n + 1) → ℤ) →₀ R) :
    residuePairing R n (Finsupp.mapDomain (fun k => a + k) g) h
      = residuePairing R n g (Finsupp.mapDomain (fun k => a + k) h) := by
  rw [residuePairing_apply, residuePairing_apply,
    Finsupp.sum_mapDomain_index_inj (injective_add_left a)]
  refine Finsupp.sum_congr fun b _ => ?_
  refine congrArg (fun z => g b * z) ?_
  have hkey : (fun i => -b i - 1)
      = (fun k : Fin (n + 1) → ℤ => a + k) (fun i => -(a + b) i - 1) := by
    funext i
    show -b i - 1 = a i + (-(a i + b i) - 1)
    ring
  rw [hkey]
  exact (Finsupp.mapDomain_apply_of_injective (injective_add_left a) h _).symm

/-- **The residue pairing is adjoint to multiplication**: pairing `f · g` against `h` and
pairing `g` against `f · h` both compute the coefficient of `1/(T₀ ⋯ Tₙ)` in `f · g · h`. This is
what makes the map induced by multiplication by `f` on the top cohomology the *contragredient* of
multiplication by `f`. -/
theorem residuePairing_laurentMul (f g h : (Fin (n + 1) → ℤ) →₀ R) :
    residuePairing R n (laurentMul f g) h = residuePairing R n g (laurentMul f h) := by
  rw [laurentMul_apply, laurentMul_apply]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun a _ =>
    congrArg (fun z => f a • z) (residuePairing_mapDomain_add a g h)

/-! ### Base change of the coefficient ring -/

/-- **Base change of a Laurent polynomial along a ring map `R → R'`**: the coefficients are
pushed along `φ` and the Laurent monomials are unchanged. This is the map which, in the proof of
[Stacks, Tag 01XV], sends "the basis elements for the Čech complex over `R` to the corresponding
basis elements for the Čech complex over `R'`". -/
def baseChangeLaurent (φ : R →+* R') (n : ℕ) :
    ((Fin (n + 1) → ℤ) →₀ R) →ₛₗ[φ] ((Fin (n + 1) → ℤ) →₀ R') where
  toFun g := Finsupp.mapRange φ (map_zero φ) g
  map_add' _ _ := Finsupp.mapRange_add (map_add φ) _ _
  map_smul' r g := Finsupp.ext fun k => by
    rw [Finsupp.mapRange_apply, Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, smul_eq_mul, map_mul]

/-- Base change is the coefficientwise application of `φ`. -/
theorem baseChangeLaurent_eq_mapRange (φ : R →+* R') (g : (Fin (n + 1) → ℤ) →₀ R) :
    baseChangeLaurent φ n g = Finsupp.mapRange φ (map_zero φ) g :=
  rfl

/-- The coefficients of a base-changed Laurent polynomial. -/
@[simp]
theorem baseChangeLaurent_apply (φ : R →+* R') (g : (Fin (n + 1) → ℤ) →₀ R)
    (k : Fin (n + 1) → ℤ) : baseChangeLaurent φ n g k = φ (g k) :=
  Finsupp.mapRange_apply (hf := map_zero φ)

/-- **Base change preserves the charts**: a degree-`d` Laurent section over `R` regular away from
the variables in `S` becomes one over `R'` of the same degree and on the same chart. -/
theorem baseChangeLaurent_mem_twistChart (φ : R →+* R') {S : Set (Fin (n + 1))}
    {g : (Fin (n + 1) → ℤ) →₀ R} (hg : g ∈ twistChart R n d S) :
    baseChangeLaurent φ n g ∈ twistChart R' n d S :=
  mem_twistChart.2 fun _ hk => mem_twistChart.1 hg
    (Finset.mem_coe.2 (Finsupp.support_mapRange (hf := map_zero φ)
      (Finset.mem_coe.1 (by rw [baseChangeLaurent_eq_mapRange] at hk; exact hk))))

/-- **The residue pairing commutes with base change**: the coefficient of `1/(T₀ ⋯ Tₙ)` in a
product may be computed over `R` and then pushed to `R'`, or computed over `R'` after pushing
both factors. This is the compatibility of the top-degree identification of
[Stacks, Equation 01XU] with base change. -/
theorem residuePairing_baseChangeLaurent (φ : R →+* R') (g h : (Fin (n + 1) → ℤ) →₀ R) :
    φ (residuePairing R n g h)
      = residuePairing R' n (baseChangeLaurent φ n g) (baseChangeLaurent φ n h) := by
  rw [residuePairing_apply, residuePairing_apply, map_finsuppSum, baseChangeLaurent_eq_mapRange,
    Finsupp.sum_mapRange_index (fun _ => zero_mul _)]
  exact Finsupp.sum_congr fun b _ => by
    rw [map_mul, baseChangeLaurent_apply]

/-! ### The two operations on the charts -/

/-- **A homogeneous polynomial of degree `m` in `T₀, …, Tₙ`, read as an element of the degree-`m`
monomial chart with no variable inverted.** Every element of `twistChart R n m ∅` is of this
form, by `Stacks.ProjectiveSpace.Cohomology.twistChartEmptyLinearEquiv`. -/
def chartOfHomogeneous (R : Type u) [CommRing R] (n : ℕ) {m : ℕ}
    (f : MvPolynomial (Fin (n + 1)) R) (hf : f.IsHomogeneous m) :
    twistChart R n (m : ℤ) (∅ : Set (Fin (n + 1))) :=
  (twistChartEmptyLinearEquiv (R := R) n (d := (m : ℤ)) (Int.natCast_nonneg m)).symm
    ⟨f, by rw [Int.toNat_natCast]; exact hf⟩

/-- **Multiplication by a homogeneous polynomial `f` of degree `m`, as a map of charts**
`𝒪(d) ⟶ 𝒪(d + m)` on the standard open `D₊(∏_{i ∈ S} Tᵢ)`. The equation `hde : d + m = e`
records the degree shift. -/
def chartMul (f : twistChart R n m (∅ : Set (Fin (n + 1)))) (hde : d + m = e)
    (S : Set (Fin (n + 1))) : twistChart R n d S →ₗ[R] twistChart R n e S :=
  LinearMap.restrict (laurentMul (f : (Fin (n + 1) → ℤ) →₀ R))
    fun _ hx => laurentMul_mem_twistChart f.2 hx hde

/-- Multiplication by `f` on a chart is multiplication by `f` on Laurent coefficients. -/
@[simp]
theorem chartMul_coe (f : twistChart R n m (∅ : Set (Fin (n + 1)))) (hde : d + m = e)
    (S : Set (Fin (n + 1))) (x : twistChart R n d S) :
    (chartMul f hde S x : (Fin (n + 1) → ℤ) →₀ R)
      = laurentMul (f : (Fin (n + 1) → ℤ) →₀ R) (x : (Fin (n + 1) → ℤ) →₀ R) :=
  rfl

/-- **Base change of a chart along a ring map `R → R'`**, the Laurent monomials being
unchanged. -/
def baseChangeChart (φ : R →+* R') (n : ℕ) (d : ℤ) (S : Set (Fin (n + 1))) :
    twistChart R n d S →ₛₗ[φ] twistChart R' n d S where
  toFun x := ⟨baseChangeLaurent φ n (x : (Fin (n + 1) → ℤ) →₀ R),
    baseChangeLaurent_mem_twistChart φ x.2⟩
  map_add' _ _ := Subtype.ext (map_add (baseChangeLaurent φ n) _ _)
  map_smul' _ _ := Subtype.ext (map_smulₛₗ (baseChangeLaurent φ n) _ _)

/-- Base change of a chart is the coefficientwise application of `φ`. -/
@[simp]
theorem baseChangeChart_coe (φ : R →+* R') (S : Set (Fin (n + 1)))
    (x : twistChart R n d S) :
    (baseChangeChart φ n d S x : (Fin (n + 1) → ℤ) →₀ R')
      = baseChangeLaurent φ n (x : (Fin (n + 1) → ℤ) →₀ R) :=
  rfl

/-! ### The two operations on the Čech cochains -/

/-- Multiplication by a Laurent polynomial on all Čech cochains of the standard cover at once,
chartwise. -/
def laurentCochainMul (f : (Fin (n + 1) → ℤ) →₀ R) :
    LaurentCochain R n →ₗ[R] LaurentCochain R n where
  toFun c S := laurentMul f (c S)
  map_add' c c' := funext fun S => map_add (laurentMul f) (c S) (c' S)
  map_smul' r c := funext fun S => map_smul (laurentMul f) r (c S)

/-- Multiplication by `f` on Čech cochains is chartwise multiplication by `f`. -/
@[simp]
theorem laurentCochainMul_apply (f : (Fin (n + 1) → ℤ) →₀ R) (c : LaurentCochain R n)
    (S : Finset (Fin (n + 1))) : laurentCochainMul f c S = laurentMul f (c S) :=
  rfl

/-- Base change of all Čech cochains of the standard cover at once, chartwise. -/
def baseChangeCochain (φ : R →+* R') (n : ℕ) :
    LaurentCochain R n →ₛₗ[φ] LaurentCochain R' n where
  toFun c S := baseChangeLaurent φ n (c S)
  map_add' c c' := funext fun S => map_add (baseChangeLaurent φ n) (c S) (c' S)
  map_smul' r c := funext fun S => map_smulₛₗ (baseChangeLaurent φ n) r (c S)

/-- Base change of Čech cochains is chartwise base change. -/
@[simp]
theorem baseChangeCochain_apply (φ : R →+* R') (c : LaurentCochain R n)
    (S : Finset (Fin (n + 1))) : baseChangeCochain φ n c S = baseChangeLaurent φ n (c S) :=
  rfl

/-- The Čech differential commutes with any semilinear map applied chartwise. -/
private theorem laurentCechDiff_chartwise (σ : R →+* R')
    (F : ((Fin (n + 1) → ℤ) →₀ R) →ₛₗ[σ] ((Fin (n + 1) → ℤ) →₀ R')) (c : LaurentCochain R n) :
    laurentCechDiff R' n (fun S => F (c S)) = fun S => F (laurentCechDiff R n c S) := by
  refine funext fun S => ?_
  simp only [laurentCechDiff_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => (map_zsmul F _ _).symm

/-- **Multiplication by `f` commutes with the Čech differential**: it is a map of Čech complexes
`Č(𝒰, 𝒪(d)) ⟶ Č(𝒰, 𝒪(d + m))`, which is the map of Čech complexes the proof of
[Stacks, Tag 01XV] considers for the second assertion. -/
theorem laurentCechDiff_laurentCochainMul (f : (Fin (n + 1) → ℤ) →₀ R) (c : LaurentCochain R n) :
    laurentCechDiff R n (laurentCochainMul f c)
      = laurentCochainMul f (laurentCechDiff R n c) :=
  laurentCechDiff_chartwise (RingHom.id R) (laurentMul f) c

/-- **Base change commutes with the Čech differential**: it is the map of Čech complexes
`γ : Č(𝒰, 𝒪_{ℙⁿ_R}(d)) ⟶ Č(𝒰', 𝒪_{ℙⁿ_{R'}}(d))` of the proof of [Stacks, Tag 01XV], in the
monomial model. -/
theorem laurentCechDiff_baseChangeCochain (φ : R →+* R') (c : LaurentCochain R n) :
    laurentCechDiff R' n (baseChangeCochain φ n c)
      = baseChangeCochain φ n (laurentCechDiff R n c) :=
  laurentCechDiff_chartwise φ (baseChangeLaurent φ n) c

/-- Multiplication by a degree-`m` homogeneous polynomial takes degree-`q` Čech cochains of
`𝒪(d)` to degree-`q` Čech cochains of `𝒪(d + m)`. -/
theorem laurentCochainMul_mem {q : ℕ} {f : (Fin (n + 1) → ℤ) →₀ R}
    (hf : f ∈ twistChart R n m (∅ : Set (Fin (n + 1)))) {c : LaurentCochain R n}
    (hc : c ∈ laurentCechCochains R n d q) (hde : d + m = e) :
    laurentCochainMul f c ∈ laurentCechCochains R n e q :=
  ⟨fun S => by
      rw [laurentCochainMul_apply]
      exact laurentMul_mem_twistChart hf ((mem_laurentCechCochains.1 hc).1 S) hde,
    fun S hS => by
      rw [laurentCochainMul_apply, (mem_laurentCechCochains.1 hc).2 S hS, map_zero]⟩

/-- Base change takes degree-`q` Čech cochains of `𝒪(d)` over `R` to degree-`q` Čech cochains of
`𝒪(d)` over `R'`. -/
theorem baseChangeCochain_mem {q : ℕ} (φ : R →+* R') {c : LaurentCochain R n}
    (hc : c ∈ laurentCechCochains R n d q) :
    baseChangeCochain φ n c ∈ laurentCechCochains R' n d q :=
  ⟨fun S => by
      rw [baseChangeCochain_apply]
      exact baseChangeLaurent_mem_twistChart φ ((mem_laurentCechCochains.1 hc).1 S),
    fun S hS => by
      rw [baseChangeCochain_apply, (mem_laurentCechCochains.1 hc).2 S hS, map_zero]⟩

/-- **Multiplication by `f`, homogeneous of degree `m`, on the degree-`q` Čech cochains** of the
standard cover of `ℙⁿ_R`, as a map from the cochains of `𝒪(d)` to those of `𝒪(d + m)`. -/
def laurentCechCochainMul (f : twistChart R n m (∅ : Set (Fin (n + 1)))) (hde : d + m = e)
    (q : ℕ) : laurentCechCochains R n d q →ₗ[R] laurentCechCochains R n e q :=
  LinearMap.restrict (laurentCochainMul (f : (Fin (n + 1) → ℤ) →₀ R))
    fun _ hc => laurentCochainMul_mem f.2 hc hde

/-- **Base change on the degree-`q` Čech cochains** of the standard cover. -/
def baseChangeCechCochain (φ : R →+* R') (n : ℕ) (d : ℤ) (q : ℕ) :
    laurentCechCochains R n d q →ₛₗ[φ] laurentCechCochains R' n d q where
  toFun c := ⟨baseChangeCochain φ n (c : LaurentCochain R n), baseChangeCochain_mem φ c.2⟩
  map_add' _ _ := Subtype.ext (map_add (baseChangeCochain φ n) _ _)
  map_smul' _ _ := Subtype.ext (map_smulₛₗ (baseChangeCochain φ n) _ _)

/-- **Multiplication by `f` is a map of Čech complexes**: the square with the Čech differentials
commutes. -/
theorem laurentCechDiffRestrict_laurentCechCochainMul
    (f : twistChart R n m (∅ : Set (Fin (n + 1)))) (hde : d + m = e) (q : ℕ) :
    (laurentCechCochainMul f hde (q + 1)).comp (laurentCechDiffRestrict R n d q)
      = (laurentCechDiffRestrict R n e q).comp (laurentCechCochainMul f hde q) :=
  LinearMap.ext fun c => Subtype.ext
    (laurentCechDiff_laurentCochainMul (f : (Fin (n + 1) → ℤ) →₀ R)
      (c : LaurentCochain R n)).symm

/-- **Base change is a map of Čech complexes**: the square with the Čech differentials
commutes. -/
theorem laurentCechDiffRestrict_baseChangeCechCochain (φ : R →+* R') (n : ℕ) (d : ℤ) (q : ℕ) :
    (baseChangeCechCochain φ n d (q + 1)).comp (laurentCechDiffRestrict R n d q)
      = (laurentCechDiffRestrict R' n d q).comp (baseChangeCechCochain φ n d q) :=
  LinearMap.ext fun c => Subtype.ext
    (laurentCechDiff_baseChangeCochain φ (c : LaurentCochain R n)).symm

/-! ### The degree-zero identification -/

/-- The degree-zero identification of [Stacks, Equation 01XU], at the Čech level, is the diagonal
cochain. -/
theorem coe_coe_laurentCechCohomologyZeroEquiv (hn : 0 < n)
    (z : twistChart R n d (∅ : Set (Fin (n + 1)))) :
    (((laurentCechCohomologyZeroEquiv (R := R) (n := n) (d := d) hn z :
          LinearMap.ker (laurentCechDiffRestrict R n d 0)) : laurentCechCochains R n d 0) :
        LaurentCochain R n)
      = laurentDiagonalCochain R n d z :=
  rfl

/-- **Multiplication by `f` carries the diagonal cochain of `z` to the diagonal cochain of
`f · z`.** -/
theorem laurentCochainMul_laurentDiagonalCochain
    (f : twistChart R n m (∅ : Set (Fin (n + 1)))) (hde : d + m = e)
    (z : twistChart R n d (∅ : Set (Fin (n + 1)))) :
    laurentCochainMul (f : (Fin (n + 1) → ℤ) →₀ R) (laurentDiagonalCochain R n d z)
      = laurentDiagonalCochain R n e (chartMul f hde (∅ : Set (Fin (n + 1))) z) := by
  refine funext fun S => ?_
  by_cases hS : S.card = 1 <;> simp [hS]

/-- **Base change carries the diagonal cochain of `z` to the diagonal cochain of the base change
of `z`.** -/
theorem baseChangeCochain_laurentDiagonalCochain (φ : R →+* R')
    (z : twistChart R n d (∅ : Set (Fin (n + 1)))) :
    baseChangeCochain φ n (laurentDiagonalCochain R n d z)
      = laurentDiagonalCochain R' n d (baseChangeChart φ n d (∅ : Set (Fin (n + 1))) z) := by
  refine funext fun S => ?_
  by_cases hS : S.card = 1 <;> simp [hS]

/-- A semilinear map commuting with two differentials sends coboundaries to coboundaries. -/
private theorem mem_range_of_comp_eq {M₁ M₂ N₁ N₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
    [AddCommGroup N₁] [AddCommGroup N₂] [Module R M₁] [Module R' M₂] [Module R N₁]
    [Module R' N₂] {σ : R →+* R'} {d₁ : M₁ →ₗ[R] N₁} {d₂ : M₂ →ₗ[R'] N₂}
    {g : M₁ →ₛₗ[σ] M₂} {g' : N₁ →ₛₗ[σ] N₂} (h : g'.comp d₁ = d₂.comp g) {c : N₁}
    (hc : c ∈ LinearMap.range d₁) : g' c ∈ LinearMap.range d₂ := by
  obtain ⟨b, rfl⟩ := hc
  exact ⟨g b, (LinearMap.congr_fun h b).symm⟩

/-- **Multiplication by `f`, homogeneous of degree `m`, on the degree-zero Čech cohomology** of
the standard cover of `ℙⁿ_R`: the cocycles are sent to cocycles because multiplication by `f`
is a map of Čech complexes. -/
def cocycleMulZero (f : twistChart R n m (∅ : Set (Fin (n + 1)))) (hde : d + m = e) :
    LinearMap.ker (laurentCechDiffRestrict R n d 0) →ₗ[R]
      LinearMap.ker (laurentCechDiffRestrict R n e 0) :=
  LinearMap.restrict (laurentCechCochainMul f hde 0) fun c hc => by
    have h := LinearMap.congr_fun (laurentCechDiffRestrict_laurentCechCochainMul f hde 0) c
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
    exact LinearMap.mem_ker.2 (h.symm.trans (by rw [LinearMap.mem_ker.1 hc, map_zero]))

/-- **Base change on the degree-zero Čech cohomology** of the standard cover. -/
def cocycleBaseChangeZero (φ : R →+* R') (n : ℕ) (d : ℤ) :
    LinearMap.ker (laurentCechDiffRestrict R n d 0) →ₛₗ[φ]
      LinearMap.ker (laurentCechDiffRestrict R' n d 0) where
  toFun c := ⟨baseChangeCechCochain φ n d 0 (c : laurentCechCochains R n d 0),
    LinearMap.mem_ker.2 (Subtype.ext (by
      have hc : laurentCechDiff R n ((c : laurentCechCochains R n d 0) : LaurentCochain R n) = 0 :=
        congrArg Subtype.val (LinearMap.mem_ker.1 c.2)
      change laurentCechDiff R' n
        (baseChangeCochain φ n ((c : laurentCechCochains R n d 0) : LaurentCochain R n)) = 0
      rw [laurentCechDiff_baseChangeCochain, hc, map_zero]))⟩
  map_add' _ _ := Subtype.ext (Subtype.ext (map_add (baseChangeCochain φ n) _ _))
  map_smul' _ _ := Subtype.ext (Subtype.ext (map_smulₛₗ (baseChangeCochain φ n) _ _))

/-- **Multiplication by a homogeneous polynomial `f` of degree `m` induces multiplication by `f`
on `H⁰`**, through the degree-zero identification of [Stacks, Equation 01XU] at the Čech level:
the square

```
(R[T₀, …, Tₙ])_d ----≅----> H⁰(Č(𝒰, 𝒪(d)))
      | · f                       | · f
(R[T₀, …, Tₙ])_{d+m} --≅--> H⁰(Č(𝒰, 𝒪(d+m)))
```

commutes, the left vertical map being genuine multiplication by `f` on the degree-`d` part of
`R[T₀, …, Tₙ]` and the right vertical map the map induced by multiplication by `f` on the Čech
complex. -/
theorem cocycleMulZero_comp_laurentCechCohomologyZeroEquiv (hn : 0 < n)
    (f : twistChart R n m (∅ : Set (Fin (n + 1)))) (hde : d + m = e) :
    (cocycleMulZero f hde).comp
        (laurentCechCohomologyZeroEquiv (R := R) (n := n) (d := d) hn).toLinearMap
      = (laurentCechCohomologyZeroEquiv (R := R) (n := n) (d := e) hn).toLinearMap.comp
          (chartMul f hde (∅ : Set (Fin (n + 1)))) :=
  LinearMap.ext fun z => Subtype.ext (Subtype.ext
    (laurentCochainMul_laurentDiagonalCochain f hde z))

/-- **The degree-zero identification of [Stacks, Equation 01XU] is compatible with base change**
along a ring map `R → R'`, at the Čech level: the square

```
(R[T₀, …, Tₙ])_d -----≅----> H⁰(Č(𝒰, 𝒪_{ℙⁿ_R}(d)))
      | base change                 | base change
(R'[T₀, …, Tₙ])_d ----≅----> H⁰(Č(𝒰', 𝒪_{ℙⁿ_{R'}}(d)))
```

commutes. This is an equality of the two composites, not merely the existence of a comparison. -/
theorem cocycleBaseChangeZero_comp_laurentCechCohomologyZeroEquiv (φ : R →+* R') (hn : 0 < n)
    (d : ℤ) :
    (cocycleBaseChangeZero φ n d).comp
        (laurentCechCohomologyZeroEquiv (R := R) (n := n) (d := d) hn).toLinearMap
      = ((laurentCechCohomologyZeroEquiv (R := R') (n := n) (d := d) hn).toLinearMap).comp
          (baseChangeChart φ n d (∅ : Set (Fin (n + 1)))) :=
  LinearMap.ext fun z => Subtype.ext (Subtype.ext
    (baseChangeCochain_laurentDiagonalCochain φ z))

/-! ### The top-degree identification -/

/-- **The residue pairing of a polynomial against a section regular along one variable
vanishes.** If every monomial of `y` has a nonnegative exponent at `i`, the complementary
exponent vector has a negative entry at `i`, where a polynomial has no monomial. -/
theorem residuePairing_eq_zero_of_mem_twistChart_compl_singleton (i : Fin (n + 1))
    {y h : (Fin (n + 1) → ℤ) →₀ R}
    (hy : y ∈ twistChart R n d ({i}ᶜ : Set (Fin (n + 1))))
    (hh : h ∈ twistChart R n e (∅ : Set (Fin (n + 1)))) :
    residuePairing R n y h = 0 := by
  rw [residuePairing_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' : k ∈ laurentMonomials n d ({i}ᶜ : Set (Fin (n + 1))) :=
    mem_twistChart.1 hy (Finset.mem_coe.2 hk)
  have hki : 0 ≤ k i := hk'.2 i (by simp)
  have hzero : h (fun j => -k j - 1) = 0 := by
    refine Finsupp.notMem_support_iff.1 fun hcon => ?_
    have hmem := mem_twistChart.1 hh (Finset.mem_coe.2 hcon)
    have h2 : (0 : ℤ) ≤ -k i - 1 := hmem.2 i (by simp)
    omega
  rw [hzero, mul_zero]

/-- **The residue pairing of a polynomial against a Čech coboundary vanishes.** The image of the
top Čech differential is spanned by the sections regular along one variable. -/
theorem residuePairing_eq_zero_of_mem_range_topCechDiff
    {y h : (Fin (n + 1) → ℤ) →₀ R} (hy : y ∈ LinearMap.range (topCechDiff R n d))
    (hh : h ∈ twistChart R n e (∅ : Set (Fin (n + 1)))) :
    residuePairing R n y h = 0 := by
  have hle : LinearMap.range (topCechDiff R n d)
      ≤ LinearMap.ker ((residuePairing R n).flip h) := by
    rw [range_topCechDiff]
    refine iSup_le fun i => ?_
    intro z hz
    refine LinearMap.mem_ker.2 ?_
    rw [LinearMap.flip_apply]
    exact residuePairing_eq_zero_of_mem_twistChart_compl_singleton i hz hh
  have hker := LinearMap.mem_ker.1 (hle hy)
  rwa [LinearMap.flip_apply] at hker

/-- The projection onto the all-negative part is the identity on Laurent coefficients up to a
Čech coboundary: the top-degree Čech cohomology class of `x` is represented by `x` itself. -/
theorem coe_topCechCohomologyEquiv_mk
    (x : twistChart R n d (Set.univ : Set (Fin (n + 1)))) :
    ((topCechCohomologyEquiv R n d (Submodule.Quotient.mk x) : negativeTwistPart R n d)
        : (Fin (n + 1) → ℤ) →₀ R)
      = (((Submodule.quotientEquivOfIsCompl
            (Submodule.comap (twistChart R n d (Set.univ : Set (Fin (n + 1)))).subtype
              (LinearMap.range (topCechDiff R n d)))
            (Submodule.comap (twistChart R n d (Set.univ : Set (Fin (n + 1)))).subtype
              (negativeTwistPart R n d))
            (isCompl_negativeTwistPart R n d) (Submodule.Quotient.mk x))
          : twistChart R n d (Set.univ : Set (Fin (n + 1)))) : (Fin (n + 1) → ℤ) →₀ R) :=
  Submodule.comapSubtypeEquivOfLe_apply_coe (negativeTwistPart_le_twistChart_univ R n d) _

/-- **The top-degree identification of [Stacks, Equation 01XU] is the residue pairing with an
arbitrary representative.** The class of a degree-`d` Laurent section `x` on the total
intersection is sent to the functional "coefficient of `1/(T₀ ⋯ Tₙ)` in `x · (-)`" on the
degree-`(-n-1-d)` part of `R[T₀, …, Tₙ]`. -/
theorem topDualEquiv_topCechCohomologyEquiv_mk
    (x : twistChart R n d (Set.univ : Set (Fin (n + 1))))
    (h : twistChart R n (-d - ((n : ℤ) + 1)) (∅ : Set (Fin (n + 1)))) :
    topDualEquiv R n d (topCechCohomologyEquiv R n d (Submodule.Quotient.mk x)) h
      = residuePairing R n (x : (Fin (n + 1) → ℤ) →₀ R) h := by
  have hcompl := isCompl_negativeTwistPart R n d
  have hmk := (Submodule.quotientEquivOfIsCompl _ _ hcompl).symm_apply_apply
    (Submodule.Quotient.mk x)
  rw [Submodule.quotientEquivOfIsCompl_symm_apply] at hmk
  have hdiff := Submodule.mem_comap.1 ((Submodule.Quotient.eq _).1 hmk)
  rw [map_sub] at hdiff
  have h0 := residuePairing_eq_zero_of_mem_range_topCechDiff hdiff h.2
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h0
  rw [topDualEquiv_apply]
  exact Eq.trans (congrArg (fun z => residuePairing R n z (h : (Fin (n + 1) → ℤ) →₀ R))
    (coe_topCechCohomologyEquiv_mk x)) h0

/-- **The top-degree identification of [Stacks, Equation 01XU] at the Čech level is the residue
pairing with the value of a representative on the total intersection.** -/
theorem laurentCechCohomologyTopEquiv_mk_apply (R : Type u) [CommRing R] (N : ℕ) (d : ℤ)
    (c : laurentCechCochains R (N + 1) d (N + 1))
    (h : twistChart R (N + 1) (-d - (((N + 1 : ℕ) : ℤ) + 1)) (∅ : Set (Fin (N + 1 + 1)))) :
    laurentCechCohomologyTopEquiv R N d (Submodule.Quotient.mk c) h
      = residuePairing R (N + 1) ((c : LaurentCochain R (N + 1)) Finset.univ) h := by
  rw [show laurentCechCohomologyTopEquiv R N d (Submodule.Quotient.mk c)
        = topDualEquiv R (N + 1) d (topCechCohomologyEquiv R (N + 1) d
            (Submodule.Quotient.mk (topCochainEquiv R N d c))) from rfl,
    topDualEquiv_topCechCohomologyEquiv_mk, coe_topCochainEquiv_apply]

/-- The degree shift on the dual side: if `d + m = e`, then multiplication by a degree-`m`
polynomial carries the degree-`(-n-1-e)` part of `R[T₀, …, Tₙ]` to the degree-`(-n-1-d)`
part. -/
theorem dualDegree_add_of_add (N : ℕ) {d m e : ℤ} (hde : d + m = e) :
    -e - (((N + 1 : ℕ) : ℤ) + 1) + m = -d - (((N + 1 : ℕ) : ℤ) + 1) := by
  omega

/-- **Multiplication by `f` descends to the top-degree Čech cohomology**: it carries Čech
coboundaries of `𝒪(d)` to Čech coboundaries of `𝒪(d + m)`. -/
theorem laurentCechCochainMul_mem_range {q : ℕ}
    (f : twistChart R n m (∅ : Set (Fin (n + 1)))) (hde : d + m = e)
    {c : laurentCechCochains R n d (q + 1)}
    (hc : c ∈ LinearMap.range (laurentCechDiffRestrict R n d q)) :
    laurentCechCochainMul f hde (q + 1) c
      ∈ LinearMap.range (laurentCechDiffRestrict R n e q) :=
  mem_range_of_comp_eq (laurentCechDiffRestrict_laurentCechCochainMul f hde q) hc

/-- **Base change descends to the top-degree Čech cohomology**: it carries Čech coboundaries
over `R` to Čech coboundaries over `R'`. -/
theorem baseChangeCechCochain_mem_range {q : ℕ} (φ : R →+* R') (n : ℕ) (d : ℤ)
    {c : laurentCechCochains R n d (q + 1)}
    (hc : c ∈ LinearMap.range (laurentCechDiffRestrict R n d q)) :
    baseChangeCechCochain φ n d (q + 1) c
      ∈ LinearMap.range (laurentCechDiffRestrict R' n d q) :=
  mem_range_of_comp_eq (laurentCechDiffRestrict_baseChangeCechCochain φ n d q) hc

/-- **Multiplication by a homogeneous polynomial `f` of degree `m` induces the contragredient of
multiplication by `f` on `Hⁿ`**, through the top-degree identification of
[Stacks, Equation 01XU] at the Čech level. Writing `ψ_d` for that identification

`ψ_d : Hⁿ(Č(𝒰, 𝒪(d))) ≅ Hom_R((R[T₀, …, Tₙ])_{-n-1-d}, R)`,

this says `ψ_{d+m}(f · ξ) = ψ_d(ξ) ∘ (f · -)`: the functional attached to the image of the class
of `c` is the functional attached to the class of `c`, precomposed with genuine multiplication by
`f`

`(R[T₀, …, Tₙ])_{-n-1-(d+m)} ⟶ (R[T₀, …, Tₙ])_{-n-1-d}`.

The degree shift `d ↦ d + m` is recorded by `hde` and the shift it induces on the dual side by
`Stacks.ProjectiveSpace.Cohomology.dualDegree_add_of_add`. Both sides depend on `c` only through
its class, by `Stacks.ProjectiveSpace.Cohomology.laurentCechCochainMul_mem_range`, so this is the
commuting square for the induced map on cohomology. -/
theorem laurentCechCohomologyTopEquiv_laurentCechCochainMul {N : ℕ}
    (f : twistChart R (N + 1) m (∅ : Set (Fin (N + 1 + 1)))) (hde : d + m = e)
    (c : laurentCechCochains R (N + 1) d (N + 1))
    (h : twistChart R (N + 1) (-e - (((N + 1 : ℕ) : ℤ) + 1)) (∅ : Set (Fin (N + 1 + 1)))) :
    laurentCechCohomologyTopEquiv R N e
        (Submodule.Quotient.mk (laurentCechCochainMul f hde (N + 1) c)) h
      = laurentCechCohomologyTopEquiv R N d (Submodule.Quotient.mk c)
          (chartMul f (dualDegree_add_of_add N hde) (∅ : Set (Fin (N + 1 + 1))) h) := by
  rw [laurentCechCohomologyTopEquiv_mk_apply, laurentCechCohomologyTopEquiv_mk_apply]
  exact residuePairing_laurentMul _ _ _

/-- **The top-degree identification of [Stacks, Equation 01XU] is compatible with base change**
along a ring map `φ : R → R'`, at the Čech level. Writing `ψ_d^R` for that identification, this
says

`ψ_d^{R'}(base change of ξ)(base change of h) = φ (ψ_d^R(ξ)(h))`,

an equality of the two composites `Hⁿ(Č(𝒰, 𝒪_{ℙⁿ_R}(d))) × (R[T₀, …, Tₙ])_{-n-1-d} ⟶ R'`.
Since the base changes of the degree-`(-n-1-d)` monomials generate the degree-`(-n-1-d)` part of
`R'[T₀, …, Tₙ]`, this pins down the base-changed functional. Both sides depend on `c` only
through its class, by `Stacks.ProjectiveSpace.Cohomology.baseChangeCechCochain_mem_range`. -/
theorem laurentCechCohomologyTopEquiv_baseChangeCechCochain (φ : R →+* R') {N : ℕ} (d : ℤ)
    (c : laurentCechCochains R (N + 1) d (N + 1))
    (h : twistChart R (N + 1) (-d - (((N + 1 : ℕ) : ℤ) + 1)) (∅ : Set (Fin (N + 1 + 1)))) :
    laurentCechCohomologyTopEquiv R' N d
        (Submodule.Quotient.mk (baseChangeCechCochain φ (N + 1) d (N + 1) c))
        (baseChangeChart φ (N + 1) (-d - (((N + 1 : ℕ) : ℤ) + 1))
          (∅ : Set (Fin (N + 1 + 1))) h)
      = φ (laurentCechCohomologyTopEquiv R N d (Submodule.Quotient.mk c) h) := by
  rw [laurentCechCohomologyTopEquiv_mk_apply, laurentCechCohomologyTopEquiv_mk_apply]
  exact (residuePairing_baseChangeLaurent φ _ _).symm

end Stacks.ProjectiveSpace.Cohomology

end
