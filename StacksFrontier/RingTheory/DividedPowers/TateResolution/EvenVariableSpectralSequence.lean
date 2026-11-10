module

public import StacksFrontier.Algebra.Homology.SpectralSequence.HomologicalFiltration
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableFiltration
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedChainComplex
public import StacksCore.Tactic.StacksAttribute

/-!
# The spectral sequence of a degree-two divided-power variable

Let `(A, dA)` be a strictly graded-commutative differential graded algebra, let `f` be a cycle of
degree `1`, and let `A⟨T⟩` be the algebra obtained by adjoining a divided-power variable `T` of
degree `2` with `dT = f`, with the differential of Tag 09PM. Filtering `A⟨T⟩` by the subcomplexes
`Fᵖ = ⨁_{n ≤ p} A T⁽ⁿ⁾` makes it a filtered complex, and this file builds the resulting spectral
sequence and identifies its first page and first differential, which is part (2) of Tag 0GZ6.

The bookkeeping of the degrees is the following. The complex of `A⟨T⟩` is the complex of its
homogeneous pieces of Tag 09PK, placed in the non-positive degrees, so the degree-`m` piece sits
in degree `-m`. The graded piece `Fᵖ / Fᵖ⁻¹` of the filtration is `A T⁽ᵖ⁾`, which in total degree
`m` is `𝒜 (m - 2 p)`: the filtration is `A` shifted by the degree `2 p` of `T⁽ᵖ⁾`. So at
filtration index `i` and total degree `m = i + j` the first page is `H_{i + j - 2 i}(A) = H_{j -
i}(A)`, which is how Tag 0GZ6 writes it; here the pair `(i, j)` is the bidegree
`filtrationBidegree true i m = (i, m - i)` of the spectral sequence of a filtered complex, and
`j - i` is the degree `q` of the homology of `A` involved, so that `m = 2 i + q`. The first
differential lowers the filtration index by one and keeps `j`, hence raises `j - i` by one: it is
multiplication by `f`, which raises the degree in `A` by `deg f = 1`.

## Main definitions

* `DividedPowers.TateResolution.evenVariableCochainComplex` — the complex of `A⟨T⟩`, for the
  differential of Tag 09PM.
* `DividedPowers.TateResolution.evenVariableToCoeff` — the underlying divided-power polynomial of
  a term of that complex, in every integer degree.
* `DividedPowers.TateResolution.evenVariableStep` and
  `DividedPowers.TateResolution.evenVariableSubobject` — the filtration of the complex by the
  degree of the adjoined variable, by submodules and as a decreasing filtration by subobjects.
* `DividedPowers.TateResolution.evenVariableFiltration` — that filtration in homological
  indexing.
* `DividedPowers.TateResolution.evenVariableSpectralSequence` and
  `DividedPowers.TateResolution.evenVariableFiltrationData` — the spectral sequence of the
  filtration, together with the data presenting its pages by the cycle representatives of the
  filtration.
* `DividedPowers.TateResolution.evenVariableMonomialRep` and
  `DividedPowers.TateResolution.evenVariablePageOneRep` — the representative `ξ T⁽ⁱ⁾` of a
  degree-`q` cycle `ξ` of `A`, and its class on the first page.
* `DividedPowers.TateResolution.evenVariablePageOneEquiv` — the identification of the first page
  with the homology of `A`.
* `DividedPowers.TateResolution.evenVariableHomology` and
  `DividedPowers.TateResolution.evenVariableHomologyIso` — the homology of `A⟨T⟩` and its
  identification with the homology of the complex.

## Main results

* `DividedPowers.TateResolution.evenVariableFiltration_finite` — the filtration is finite in
  every degree, which is the boundedness of the spectral sequence.
* `DividedPowers.TateResolution.evenVariableFiltrationData_converges` — the spectral sequence
  converges.
* `DividedPowers.TateResolution.surjective_evenVariablePageOneRep` and
  `DividedPowers.TateResolution.ker_evenVariablePageOneRep` — the first page is onto the classes
  of the representatives `ξ T⁽ⁱ⁾`, with the boundaries of `A` as the kernel.
* `DividedPowers.TateResolution.evenVariablePageOneRep_d` — the first differential is
  multiplication by `f`, with the Koszul sign of the degree of the cycle.
* `DividedPowers.TateResolution.evenVariableSpectralSequence_degree_two` — part (2) of
  Tag 0GZ6: the four assertions together.

## Implementation notes

The spectral sequence is the one of `CochainComplex.Tor.homologicalSpectralSequence`, whose pages
are presented by `CochainComplex.Tor.TorFiltrationData`: the page classes of actual filtered
cycles, with the standard page relations as the kernel, and with differentials acting on
representatives as the differential of the complex. That presentation is what makes the first
page identification a statement about representatives rather than an abstract isomorphism, and it
is why the first differential can be computed from `evenPolynomialDifferential_monomial`.

The terms of the complex are the homogeneous pieces of `A⟨T⟩` transported along an extension of
complex shapes, so an element of the term in degree `i` is not literally a divided-power
polynomial. Everything is therefore said through `evenVariableToCoeff i`, the underlying
polynomial of a term in degree `i`, defined in every integer degree — as the inclusion of the
degree-`n` piece when `i = -n` and as zero in the positive degrees, where the complex vanishes.
Its three properties `evenVariableToCoeff_mem_grade`, `evenVariableToCoeff_injective` and
`evenVariableToCoeff_d` are all that the rest of the file uses, and they hold uniformly in `i`,
which keeps the degree arithmetic of the spectral sequence free of transports along equalities of
degrees. For the same reason every lemma about a degree presented as `-n` takes the presentation
as a hypothesis `i = -n` rather than being stated at `-n`.

The differential of `A⟨T⟩` is not a hypothesis: it is `evenPolynomialDifferential`, the explicit
differential whose existence and uniqueness is Tag 09PM, and the differential graded algebra
structure it carries is supplied by `evenPolynomialDifferential_two_isDGA`, which is Tag 09PM for
`d = 2`. Intermediate declarations take that structure as an instance argument, as the
construction of the complex does; the statement of Tag 0GZ6 part (2) assumes no such instance and
introduces it from `evenPolynomialDifferential_two_isDGA`.

The sign of the first differential is kept. On a monomial the differential of Tag 09PM is
`d (a T⁽ⁿ⁾) = (dA a) T⁽ⁿ⁾ + (signRingHom 𝒜 1 a * f) T⁽ⁿ⁻¹⁾`, so on the class of `ξ T⁽ⁱ⁺¹⁾` the
first differential is the class of `(signRingHom 𝒜 1 ξ * f) T⁽ⁱ⁾`, and
`signRingHom 𝒜 1 ξ * f = (-1) ^ q • (ξ f)` for `ξ` of degree `q`. Tag 0GZ6 writes `f ξ` unsigned;
the two agree up to the unit `(-1) ^ q` of the coefficient ring, and the signed form is the one
stated.

## References

* [Stacks Project, Tag 0GZ6](https://stacks.math.columbia.edu/tag/0GZ6)
* [Stacks Project, Tag 09PM](https://stacks.math.columbia.edu/tag/09PM)
* [Stacks Project, Tag 09PK](https://stacks.math.columbia.edu/tag/09PK)
* [Stacks Project, Tag 012K](https://stacks.math.columbia.edu/tag/012K)
-/

open CategoryTheory CategoryTheory.Limits CochainComplex.Tor

@[expose] public noncomputable section

namespace DividedPowers.TateResolution

universe u v w

/-- A coefficient algebra of `A` sitting in degree zero sits in degree zero in `A⟨T⟩`: the
image of a coefficient is a constant divided-power polynomial. -/
public theorem EvenVariableAlgebra.algebraMap_mem_grade_zero {R : Type u} {P : Type v}
    {A : Type w} [CommRing R] [CommRing P] [Ring A] [Algebra R A] [Algebra P A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (h0 : ∀ p : P, algebraMap P A p ∈ 𝒜 0) (d : ℕ) (p : P) :
    algebraMap P (EvenVariableAlgebra A) p ∈ EvenVariableAlgebra.grade 𝒜 d 0 := by
  rw [EvenVariableAlgebra.algebraMap_apply]
  exact (EvenVariableAlgebra.coeffEmbedding_mem_grade_iff 𝒜 d 0 _).2 (h0 p)

section Generic

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Ring A] [Algebra R A] [Algebra P A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A) (f : A)

omit [GradedAlgebra 𝒜] in
/-- The monomial `ξ T⁽ⁱ⁾` is homogeneous of degree `2 i + q` when `ξ` is homogeneous of degree
`q`, the adjoined variable having degree two. -/
public theorem monomial_mem_grade_two (i q : ℕ) {ξ : A} (hξ : ξ ∈ 𝒜 q) :
    EvenVariableAlgebra.monomial i ξ ∈ EvenVariableAlgebra.grade 𝒜 2 (2 * i + q) := by
  rw [show 2 * i + q = q + i * 2 by ring]
  exact EvenVariableAlgebra.monomial_mem_grade 𝒜 2 i q hξ

/-- **The differential of `A⟨T⟩` on a monomial, modulo the previous filtration step**: the
differential of `a T⁽ⁱ⁾` is `(dA a) T⁽ⁱ⁾` up to the term `± (a f) T⁽ⁱ⁻¹⁾`, which lies one step
down the filtration. -/
public theorem evenPolynomialDifferential_monomial_sub_mem (S : Type v) [CommRing S]
    [Algebra S A] (i : ℕ) (a : A) :
    evenPolynomialDifferential 𝒜 dA f (EvenVariableAlgebra.monomial i a) -
        EvenVariableAlgebra.monomial i (dA a) ∈
      EvenVariableAlgebra.coeffFiltration S A ((i : ℤ) - 1) := by
  rw [evenPolynomialDifferential_monomial]
  simp only [add_sub_cancel_left]
  rcases i with _ | k
  · simp
  · simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    exact EvenVariableAlgebra.monomial_mem_coeffFiltration S (by push_cast; omega) _

/-- **An element of `A⟨T⟩` on the filtration step `i` differs from the monomial of its
coefficient along `T⁽ⁱ⁾` by an element of the step `i - 1`.** -/
public theorem monomial_coeff_sub_mem (S : Type v) [CommRing S] [Algebra S A] (i : ℕ)
    {b : EvenVariableAlgebra A} (hb : b ∈ EvenVariableAlgebra.coeffFiltration S A (i : ℤ)) :
    EvenVariableAlgebra.monomial i (b.coeff i) - b ∈
      EvenVariableAlgebra.coeffFiltration S A ((i : ℤ) - 1) := by
  intro k hk
  rw [EvenVariableAlgebra.coeff_sub, Finsupp.sub_apply, EvenVariableAlgebra.coeff_monomial]
  rcases eq_or_lt_of_le (show i ≤ k by omega) with rfl | hik
  · rw [Finsupp.single_eq_same, sub_self]
  · rw [Finsupp.single_eq_of_ne (by omega), hb k (by omega), sub_self]

end Generic

section Complex

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Ring A] [Algebra R A] [Algebra P A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A) (f : A)
  [IsDifferentialGradedAlgebra (EvenVariableAlgebra.grade 𝒜 2)
    (evenPolynomialDifferential 𝒜 dA f)]
  (h0 : ∀ p : P, algebraMap P A p ∈ 𝒜 0)

/-- **The complex of homogeneous pieces of `A⟨T⟩`**, for an adjoined divided-power variable of
degree two with `dT = f`: the chain complex of Tag 09PK for the differential of Tag 09PM, placed
in the non-positive integer degrees, the piece of degree `n` sitting in degree `-n`. -/
public abbrev evenVariableCochainComplex : CochainComplex (ModuleCat.{w} P) ℤ :=
  gradedCochainComplex (EvenVariableAlgebra.grade 𝒜 2) (evenPolynomialDifferential 𝒜 dA f)
    (EvenVariableAlgebra.algebraMap_mem_grade_zero 𝒜 h0 2)

/-- The degree-`n` piece of `A⟨T⟩` over the coefficient algebra. -/
public abbrev evenVariableGrade (n : ℕ) : Submodule P (EvenVariableAlgebra A) :=
  coefficientGrade (EvenVariableAlgebra.grade 𝒜 2)
    (EvenVariableAlgebra.algebraMap_mem_grade_zero 𝒜 h0 2) n

/-- The degree-`-n` term of the complex is the degree-`n` piece of `A⟨T⟩`. -/
public abbrev evenVariableXIso (n : ℕ) :
    (evenVariableCochainComplex 𝒜 dA f h0).X (-(n : ℤ)) ≅
      ModuleCat.of P ↥(evenVariableGrade 𝒜 h0 n) :=
  gradedCochainComplexXIso (EvenVariableAlgebra.grade 𝒜 2)
    (evenPolynomialDifferential 𝒜 dA f)
    (EvenVariableAlgebra.algebraMap_mem_grade_zero 𝒜 h0 2) n

/-- **The underlying divided-power polynomial of a term of the complex in degree `-n`**: the
degree-`-n` term is the degree-`n` homogeneous piece of `A⟨T⟩`, and this is the inclusion of that
piece into `A⟨T⟩`. -/
public def evenVariableToCoeffNat (n : ℕ) :
    (evenVariableCochainComplex 𝒜 dA f h0).X (-(n : ℤ)) →ₗ[P] EvenVariableAlgebra A :=
  (evenVariableGrade 𝒜 h0 n).subtype.comp (evenVariableXIso 𝒜 dA f h0 n).hom.hom

/-- The underlying polynomial of a term of the complex in degree `-n`. -/
public theorem evenVariableToCoeffNat_apply (n : ℕ)
    (y : (evenVariableCochainComplex 𝒜 dA f h0).X (-(n : ℤ))) :
    evenVariableToCoeffNat 𝒜 dA f h0 n y =
      ((evenVariableXIso 𝒜 dA f h0 n).hom y : EvenVariableAlgebra A) := rfl

/-- The underlying divided-power polynomial of a term of the complex, in a degree presented as
`-n`. -/
public def evenVariableToCoeffOf (n : ℕ) : ∀ {i : ℤ}, -(n : ℤ) = i →
    ((evenVariableCochainComplex 𝒜 dA f h0).X i →ₗ[P] EvenVariableAlgebra A)
  | _, rfl => evenVariableToCoeffNat 𝒜 dA f h0 n

open scoped Classical in
/-- **The underlying divided-power polynomial of a term of the complex**, in every integer
degree: the inclusion of the degree-`n` homogeneous piece of `A⟨T⟩` in degree `-n`, and the zero
map in the positive degrees, where the complex vanishes. Stating the filtration and its page
representatives through this one map in all degrees is what keeps the degree bookkeeping of the
spectral sequence free of transports along equalities of degrees. -/
public def evenVariableToCoeff (i : ℤ) :
    (evenVariableCochainComplex 𝒜 dA f h0).X i →ₗ[P] EvenVariableAlgebra A :=
  if h : ∃ n : ℕ, -(n : ℤ) = i then
    evenVariableToCoeffOf 𝒜 dA f h0 h.choose h.choose_spec
  else 0

/-- Two presentations of the same degree as `-n` give the same map. -/
public theorem evenVariableToCoeffOf_congr (m n : ℕ) {i : ℤ} (hm : -(m : ℤ) = i)
    (hn : -(n : ℤ) = i) :
    evenVariableToCoeffOf 𝒜 dA f h0 m hm = evenVariableToCoeffOf 𝒜 dA f h0 n hn := by
  obtain rfl : m = n := by omega
  rfl

/-- The underlying polynomial of a term of the complex in a degree presented as `-n`. -/
public theorem evenVariableToCoeff_eq (n : ℕ) {i : ℤ} (hi : -(n : ℤ) = i) :
    evenVariableToCoeff 𝒜 dA f h0 i = evenVariableToCoeffOf 𝒜 dA f h0 n hi := by
  have hex : ∃ m : ℕ, -(m : ℤ) = i := ⟨n, hi⟩
  rw [evenVariableToCoeff, dite_eq_left hex]
  exact evenVariableToCoeffOf_congr 𝒜 dA f h0 _ n hex.choose_spec hi

/-- In a degree presented as `-n` the underlying polynomial is the inclusion of the degree-`n`
piece. -/
public theorem evenVariableToCoeff_natCast (n : ℕ) :
    evenVariableToCoeff 𝒜 dA f h0 (-(n : ℤ)) = evenVariableToCoeffNat 𝒜 dA f h0 n :=
  evenVariableToCoeff_eq 𝒜 dA f h0 n rfl

/-- In a positive degree the complex vanishes, and so does the underlying polynomial. -/
public theorem evenVariableToCoeff_of_pos {i : ℤ} (hi : 0 < i) :
    evenVariableToCoeff 𝒜 dA f h0 i = 0 := by
  rw [evenVariableToCoeff, dite_eq_right]
  rintro ⟨n, hn⟩
  omega

/-- The underlying polynomial of a term in degree `-n` is homogeneous of degree `n`. -/
public theorem evenVariableToCoeff_mem_grade (n : ℕ) {i : ℤ} (hi : -(n : ℤ) = i)
    (y : (evenVariableCochainComplex 𝒜 dA f h0).X i) :
    evenVariableToCoeff 𝒜 dA f h0 i y ∈ EvenVariableAlgebra.grade 𝒜 2 n := by
  subst hi
  rw [evenVariableToCoeff_natCast]
  exact ((evenVariableXIso 𝒜 dA f h0 n).hom y).2

/-- **A homogeneous element of `A⟨T⟩` of degree `n` is the underlying polynomial of a term of
the complex in degree `-n`**, and of exactly one such term. -/
public def evenVariableOfCoeffNat (n : ℕ) :
    ↥(evenVariableGrade 𝒜 h0 n) →ₗ[P] (evenVariableCochainComplex 𝒜 dA f h0).X (-(n : ℤ)) :=
  (evenVariableXIso 𝒜 dA f h0 n).inv.hom

/-- The underlying polynomial of the term built from a homogeneous element is that element. -/
public theorem evenVariableToCoeff_ofCoeffNat (n : ℕ) (b : ↥(evenVariableGrade 𝒜 h0 n)) :
    evenVariableToCoeff 𝒜 dA f h0 (-(n : ℤ)) (evenVariableOfCoeffNat 𝒜 dA f h0 n b) =
      (b : EvenVariableAlgebra A) := by
  rw [evenVariableToCoeff_natCast, evenVariableToCoeffNat_apply]
  change ((evenVariableXIso 𝒜 dA f h0 n).hom
    ((evenVariableXIso 𝒜 dA f h0 n).inv b) : EvenVariableAlgebra A) = _
  rw [Iso.inv_hom_id_apply]

/-- **A homogeneous element of `A⟨T⟩` of degree `n` is the underlying polynomial of a term of
the complex in degree `-n`.** -/
public theorem exists_evenVariableToCoeff_eq (n : ℕ) {i : ℤ} (hi : -(n : ℤ) = i)
    {b : EvenVariableAlgebra A} (hb : b ∈ EvenVariableAlgebra.grade 𝒜 2 n) :
    ∃ y : (evenVariableCochainComplex 𝒜 dA f h0).X i,
      evenVariableToCoeff 𝒜 dA f h0 i y = b := by
  subst hi
  exact ⟨evenVariableOfCoeffNat 𝒜 dA f h0 n ⟨b, hb⟩,
    evenVariableToCoeff_ofCoeffNat 𝒜 dA f h0 n ⟨b, hb⟩⟩

/-- **The underlying polynomial determines a term of the complex.** -/
public theorem evenVariableToCoeff_injective (i : ℤ) :
    Function.Injective (evenVariableToCoeff 𝒜 dA f h0 i) := by
  rcases le_or_gt i 0 with hi | hi
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
    rw [evenVariableToCoeff_natCast]
    exact (Submodule.injective_subtype _).comp
      ((ModuleCat.mono_iff_injective (gradedCochainComplexXIso
        (EvenVariableAlgebra.grade 𝒜 2) (evenPolynomialDifferential 𝒜 dA f)
        (EvenVariableAlgebra.algebraMap_mem_grade_zero 𝒜 h0 2) n).hom).1 inferInstance)
  · have := ModuleCat.subsingleton_of_isZero
      (isZero_gradedCochainComplex_X (EvenVariableAlgebra.grade 𝒜 2)
        (evenPolynomialDifferential 𝒜 dA f)
        (EvenVariableAlgebra.algebraMap_mem_grade_zero 𝒜 h0 2) hi)
    exact fun x y _ => Subsingleton.elim x y

/-- The differential of the complex from degree `-(n + 1)` to degree `-n` is the differential of
the degree-`n + 1` piece of `A⟨T⟩`. -/
public theorem evenVariableCochainComplex_d (n : ℕ) :
    (evenVariableCochainComplex 𝒜 dA f h0).d (-((n + 1 : ℕ) : ℤ)) (-((n : ℕ) : ℤ)) =
      (evenVariableXIso 𝒜 dA f h0 (n + 1)).hom ≫
        ModuleCat.ofHom (coefficientDifferential (EvenVariableAlgebra.grade 𝒜 2)
          (evenPolynomialDifferential 𝒜 dA f)
          (EvenVariableAlgebra.algebraMap_mem_grade_zero 𝒜 h0 2) n) ≫
        (evenVariableXIso 𝒜 dA f h0 n).inv := by
  rw [← gradedChainComplex_d]
  exact HomologicalComplex.extend_d_eq _ ComplexShape.embeddingDownNat rfl rfl

/-- **The differential of the complex is the differential of Tag 09PM** on underlying
polynomials. -/
public theorem evenVariableToCoeff_d {i j : ℤ} (hij : j = i + 1)
    (y : (evenVariableCochainComplex 𝒜 dA f h0).X i) :
    evenVariableToCoeff 𝒜 dA f h0 j ((evenVariableCochainComplex 𝒜 dA f h0).d i j y) =
      evenPolynomialDifferential 𝒜 dA f (evenVariableToCoeff 𝒜 dA f h0 i y) := by
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -((k + 1 : ℕ) : ℤ) := ⟨(-i - 1).toNat, by omega⟩
    obtain rfl : j = -((k : ℕ) : ℤ) := by push_cast at hij ⊢; omega
    rw [evenVariableToCoeff_natCast, evenVariableToCoeff_natCast,
      evenVariableCochainComplex_d, evenVariableToCoeffNat_apply, evenVariableToCoeffNat_apply]
    simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
    rfl
  · rw [evenVariableToCoeff_of_pos _ _ _ _ (by omega : (0 : ℤ) < j)]
    have hz := evenVariableToCoeff_mem_grade 𝒜 dA f h0 0 (by norm_num) y
    rw [LinearMap.zero_apply,
      IsDifferentialGradedAlgebra.d_grade_zero
        (𝒜 := EvenVariableAlgebra.grade 𝒜 2)
        (d := evenPolynomialDifferential 𝒜 dA f) hz]
  · rw [evenVariableToCoeff_of_pos _ _ _ _ (by omega : (0 : ℤ) < j),
      evenVariableToCoeff_of_pos _ _ _ _ hi]
    simp

/-! ### The filtration of the complex -/

/-- **The step `p` of the filtration of the complex of `A⟨T⟩`**: the terms whose underlying
divided-power polynomial has no coefficient along `T⁽ⁿ⁾` with `n > p`. -/
public def evenVariableStep (p i : ℤ) :
    Submodule P ((evenVariableCochainComplex 𝒜 dA f h0).X i) :=
  (EvenVariableAlgebra.coeffFiltration P A p).comap (evenVariableToCoeff 𝒜 dA f h0 i)

/-- Membership in a step of the filtration of the complex. -/
public theorem mem_evenVariableStep_iff {p i : ℤ}
    {y : (evenVariableCochainComplex 𝒜 dA f h0).X i} :
    y ∈ evenVariableStep 𝒜 dA f h0 p i ↔
      evenVariableToCoeff 𝒜 dA f h0 i y ∈ EvenVariableAlgebra.coeffFiltration P A p :=
  Iff.rfl

/-- The filtration of the complex is increasing. -/
public theorem evenVariableStep_mono (i : ℤ) :
    Monotone fun p => evenVariableStep 𝒜 dA f h0 p i :=
  fun _ _ hpq => Submodule.comap_mono (EvenVariableAlgebra.coeffFiltration_mono P hpq)

/-- **Each step of the filtration is carried into the next degree by the differential**, which is
the differential of Tag 09PM on underlying polynomials. -/
public theorem evenVariableStep_d (p : ℤ) {i j : ℤ} (hij : j = i + 1)
    {y : (evenVariableCochainComplex 𝒜 dA f h0).X i}
    (hy : y ∈ evenVariableStep 𝒜 dA f h0 p i) :
    (evenVariableCochainComplex 𝒜 dA f h0).d i j y ∈ evenVariableStep 𝒜 dA f h0 p j := by
  rw [mem_evenVariableStep_iff, evenVariableToCoeff_d 𝒜 dA f h0 hij]
  exact evenPolynomialDifferential_mem_coeffFiltration 𝒜 dA f P hy

/-- The negative steps of the filtration are zero. -/
public theorem evenVariableStep_eq_bot {p : ℤ} (hp : p < 0) (i : ℤ) :
    evenVariableStep 𝒜 dA f h0 p i = ⊥ := by
  rw [evenVariableStep, EvenVariableAlgebra.coeffFiltration_eq_bot P hp, Submodule.comap_bot,
    LinearMap.ker_eq_bot]
  exact evenVariableToCoeff_injective 𝒜 dA f h0 i

/-- **In a fixed degree the filtration is exhaustive**: the step `p` is everything as soon as
`n ≤ 2 * p`, the variable having degree two. -/
public theorem evenVariableStep_eq_top (n : ℕ) {i : ℤ} (hi : -(n : ℤ) = i) {p : ℤ}
    (hp : (n : ℤ) ≤ 2 * p) : evenVariableStep 𝒜 dA f h0 p i = ⊤ :=
  eq_top_iff.2 fun y _ =>
    EvenVariableAlgebra.mem_coeffFiltration_of_mem_grade P 𝒜 (d := 2) (by omega)
      (by push_cast; omega) (evenVariableToCoeff_mem_grade 𝒜 dA f h0 n hi y)

/-- In a positive degree the complex vanishes, so every step of the filtration is everything. -/
public theorem evenVariableStep_eq_top_of_pos {i : ℤ} (hi : 0 < i) (p : ℤ) :
    evenVariableStep 𝒜 dA f h0 p i = ⊤ := by
  rw [evenVariableStep, evenVariableToCoeff_of_pos 𝒜 dA f h0 hi, Submodule.comap_zero]

/-- A map of modules landing in a submodule factors through the corresponding subobject. -/
public theorem factors_subobjectModule_symm {M N : ModuleCat.{w} P} (S : Submodule P N)
    (g : M ⟶ N) (hg : ∀ x : M, g x ∈ S) :
    ((ModuleCat.subobjectModule N).symm S).Factors g :=
  ⟨ModuleCat.ofHom (LinearMap.codRestrict S g.hom hg),
    ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)⟩

/-- **The filtration of the complex of `A⟨T⟩` as a decreasing filtration by subobjects**, which
is the form the spectral sequence of a filtered complex is built from. The index is negated, a
decreasing filtration by subobjects corresponding to an increasing filtration by submodules. -/
public def evenVariableSubobject (a i : ℤ) :
    Subobject ((evenVariableCochainComplex 𝒜 dA f h0).X i) :=
  (ModuleCat.subobjectModule _).symm (evenVariableStep 𝒜 dA f h0 (-a) i)

/-- The submodule underlying a step of the subobject filtration is the step of the filtration by
submodules, at the negated index. -/
public theorem subobjectModule_evenVariableSubobject (a i : ℤ) :
    ModuleCat.subobjectModule ((evenVariableCochainComplex 𝒜 dA f h0).X i)
        (evenVariableSubobject 𝒜 dA f h0 a i) =
      evenVariableStep 𝒜 dA f h0 (-a) i :=
  (ModuleCat.subobjectModule _).apply_symm_apply _

/-- The subobject filtration is decreasing. -/
public theorem evenVariableSubobject_antitone (a a' i : ℤ) (h : a ≤ a') :
    evenVariableSubobject 𝒜 dA f h0 a' i ≤ evenVariableSubobject 𝒜 dA f h0 a i :=
  (ModuleCat.subobjectModule _).symm.monotone
    (evenVariableStep_mono 𝒜 dA f h0 i (by omega : -a' ≤ -a))

/-- **Each step of the subobject filtration is carried into the next degree by the
differential.** -/
public theorem evenVariableSubobject_factors (a i j : ℤ) (hij : j = i + 1) :
    (evenVariableSubobject 𝒜 dA f h0 a j).Factors
      ((evenVariableSubobject 𝒜 dA f h0 a i).arrow ≫
        (evenVariableCochainComplex 𝒜 dA f h0).d i j) := by
  refine factors_subobjectModule_symm _ _ fun x => ?_
  have hx : (evenVariableSubobject 𝒜 dA f h0 a i).arrow x ∈
      evenVariableStep 𝒜 dA f h0 (-a) i := by
    rw [← subobjectModule_evenVariableSubobject 𝒜 dA f h0 a i]
    exact ⟨x, rfl⟩
  rw [ConcreteCategory.comp_apply]
  exact evenVariableStep_d 𝒜 dA f h0 (-a) hij hx

/-- **The filtration of the complex of `A⟨T⟩`, in homological indexing.** -/
public def evenVariableFiltration :
    HomologicalFiltration (evenVariableCochainComplex 𝒜 dA f h0) :=
  homologicalFiltrationOfSubobjects _ (evenVariableSubobject 𝒜 dA f h0)
    (evenVariableSubobject_antitone 𝒜 dA f h0) (evenVariableSubobject_factors 𝒜 dA f h0)

/-- The step of the filtration at filtration index `p` and chain degree `n` is the step `p` in
the term of degree `-n`. -/
public theorem evenVariableFiltration_step (p n : ℤ) :
    (evenVariableFiltration 𝒜 dA f h0).step p n = evenVariableStep 𝒜 dA f h0 p (-n) := by
  rw [evenVariableFiltration, homologicalFiltrationOfSubobjects_step,
    subobjectModule_evenVariableSubobject, neg_neg]

/-- **The filtration is finite in every chain degree**: it vanishes below the step `-1`, and in
chain degree `n` it is everything from the step `n` on, the variable having degree two. -/
public theorem evenVariableFiltration_finite (n : ℤ) :
    ∃ a b : ℤ, a ≤ b ∧ (evenVariableFiltration 𝒜 dA f h0).step a n = ⊥ ∧
      (evenVariableFiltration 𝒜 dA f h0).step b n = ⊤ := by
  refine ⟨-1, max 0 n, by omega, ?_, ?_⟩
  · rw [evenVariableFiltration_step]
    exact evenVariableStep_eq_bot 𝒜 dA f h0 (by omega) _
  · rw [evenVariableFiltration_step]
    rcases le_or_gt 0 n with hn | hn
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, by omega⟩
      exact evenVariableStep_eq_top 𝒜 dA f h0 k (by omega) (by omega)
    · exact evenVariableStep_eq_top_of_pos 𝒜 dA f h0 (by omega) _

/-! ### The spectral sequence -/

/-- **The spectral sequence of the filtration of `A⟨T⟩` by the degree of the adjoined
divided-power variable**, in homological indexing, starting on the first page. Its `r`-th
differential has bidegree `(-r, r - 1)`. -/
public abbrev evenVariableSpectralSequence :
    SpectralSequence (ModuleCat.{w} P) (torSpectralSequenceShape true) 1 :=
  homologicalSpectralSequence (evenVariableCochainComplex 𝒜 dA f h0)
    (evenVariableSubobject 𝒜 dA f h0) (evenVariableSubobject_antitone 𝒜 dA f h0) true 1
    (by omega)

/-- **The pages of that spectral sequence are the pages of the filtered complex**: the
projections from the cycle representatives have the standard page relations as kernels, and the
differentials and the page-turning isomorphisms act on representatives as the differential of
the complex does. -/
public def evenVariableFiltrationData :
    TorFiltrationData (evenVariableSpectralSequence 𝒜 dA f h0)
      (evenVariableFiltration 𝒜 dA f h0) true :=
  (nonempty_torFiltrationData (evenVariableCochainComplex 𝒜 dA f h0)
    (evenVariableSubobject 𝒜 dA f h0) (evenVariableSubobject_antitone 𝒜 dA f h0)
    (evenVariableSubobject_factors 𝒜 dA f h0) true 1 (by omega)).some

/-- **The spectral sequence of the filtration converges**: the filtration is finite in every
chain degree. -/
public theorem evenVariableFiltrationData_converges :
    (evenVariableFiltrationData 𝒜 dA f h0).Converges :=
  TorFiltrationData.converges_of_finite (evenVariableFiltration 𝒜 dA f h0)
    (evenVariableFiltrationData 𝒜 dA f h0) (evenVariableFiltration_finite 𝒜 dA f h0)

/-! ### The first page -/

/-- **Membership in the representatives of the cycles on page `r`, read on underlying
polynomials**: the polynomial lies on the filtration step `p`, and its differential on the step
`p - r`. -/
public theorem mem_pageCycles_iff (r p n : ℤ)
    (y : (evenVariableCochainComplex 𝒜 dA f h0).X (-n)) :
    y ∈ (evenVariableFiltration 𝒜 dA f h0).pageCycles r p n ↔
      evenVariableToCoeff 𝒜 dA f h0 (-n) y ∈ EvenVariableAlgebra.coeffFiltration P A p ∧
        evenPolynomialDifferential 𝒜 dA f (evenVariableToCoeff 𝒜 dA f h0 (-n) y) ∈
          EvenVariableAlgebra.coeffFiltration P A (p - r) := by
  rw [HomologicalFiltration.pageCycles, Submodule.mem_inf]
  refine and_congr (by rw [evenVariableFiltration_step]; exact Iff.rfl) ?_
  rw [Submodule.mem_comap, evenVariableFiltration_step,
    ← evenVariableToCoeff_d 𝒜 dA f h0 (show (-(n - 1) : ℤ) = -n + 1 by ring) y]
  exact Iff.rfl

/-- The differential of a page on the classes of representatives, with the source and target
degrees presented as the degrees of the representatives. -/
public theorem evenVariableFiltrationData_differential (r : ℤ) (hr : 1 ≤ r) (p₀ n₀ p n : ℤ)
    (hp : p = p₀ - r) (hn : n = n₀ - 1)
    (x : (evenVariableCochainComplex 𝒜 dA f h0).X (-n₀))
    (hx : x ∈ (evenVariableFiltration 𝒜 dA f h0).pageCycles r p₀ n₀)
    (hdx : (evenVariableCochainComplex 𝒜 dA f h0).d (-n₀) (-n) x ∈
      (evenVariableFiltration 𝒜 dA f h0).pageCycles r p n) :
    ((evenVariableSpectralSequence 𝒜 dA f h0).page r hr).d (filtrationBidegree true p₀ n₀)
        (filtrationBidegree true p n)
        ((evenVariableFiltrationData 𝒜 dA f h0).projection r hr p₀ n₀ ⟨x, hx⟩) =
      (evenVariableFiltrationData 𝒜 dA f h0).projection r hr p n
        ⟨(evenVariableCochainComplex 𝒜 dA f h0).d (-n₀) (-n) x, hdx⟩ := by
  subst hp hn
  exact (evenVariableFiltrationData 𝒜 dA f h0).differential r hr p₀ n₀ x hx hdx

/-- The degree-`k` homology of `A⟨T⟩`: its degree-`k` cycles modulo its degree-`k`
boundaries. -/
public abbrev evenVariableHomology (k : ℕ) : Type w :=
  coefficientHomology (EvenVariableAlgebra.grade 𝒜 2) (evenPolynomialDifferential 𝒜 dA f)
    (EvenVariableAlgebra.algebraMap_mem_grade_zero 𝒜 h0 2) k

/-- **The homology of the complex in degree `-k` is the degree-`k` homology of `A⟨T⟩`**: the
degree-`k` cycles of `A⟨T⟩` modulo the differentials of its degree-`k + 1` elements. -/
public def evenVariableHomologyIso (k : ℕ) :
    (evenVariableCochainComplex 𝒜 dA f h0).homology (-(k : ℤ)) ≅
      ModuleCat.of P (evenVariableHomology 𝒜 dA f h0 k) :=
  (gradedChainComplex (EvenVariableAlgebra.grade 𝒜 2) (evenPolynomialDifferential 𝒜 dA f)
        (EvenVariableAlgebra.algebraMap_mem_grade_zero 𝒜 h0 2)).extendHomologyIso
      ComplexShape.embeddingDownNat (j := k) (j' := -(k : ℤ)) rfl ≪≫
    (gradedChainComplexHomologyEquiv (EvenVariableAlgebra.grade 𝒜 2)
      (evenPolynomialDifferential 𝒜 dA f)
      (EvenVariableAlgebra.algebraMap_mem_grade_zero 𝒜 h0 2) k).toModuleIso

end Complex

section PageOne

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Ring A] [Algebra R A] [Algebra P A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
  [IsDifferentialGradedAlgebra 𝒜 dA] (f : A)
  [IsDifferentialGradedAlgebra (EvenVariableAlgebra.grade 𝒜 2)
    (evenPolynomialDifferential 𝒜 dA f)]
  (h0 : ∀ p : P, algebraMap P A p ∈ 𝒜 0)

/-- The coefficient along `T⁽ⁱ⁾` of a homogeneous element of degree `2 i + q` of `A⟨T⟩` is
homogeneous of degree `q`. -/
private theorem coeff_mem_of_mem_grade_two (𝒜 : ℕ → Submodule R A) (i q n : ℕ) (hn : n = 2 * i + q)
    {b : EvenVariableAlgebra A} (hb : b ∈ EvenVariableAlgebra.grade 𝒜 2 n) : b.coeff i ∈ 𝒜 q := by
  have hle : i * 2 ≤ n := by omega
  have heq : n - i * 2 = q := by omega
  simpa [hle, heq] using (EvenVariableAlgebra.mem_grade_iff 𝒜 2 n b).1 hb i

/-- **The representative `ξ T⁽ⁱ⁾` of a degree-`q` cycle of `A`**, as a term of the complex of
`A⟨T⟩` in total degree `2 i + q`, where it lies on the filtration step `i`. -/
public def evenVariableMonomialRep (i q : ℕ) :
    ↥(coefficientCycles 𝒜 dA h0 q) →ₗ[P]
      (evenVariableCochainComplex 𝒜 dA f h0).X (-((2 * i + q : ℕ) : ℤ)) :=
  (evenVariableOfCoeffNat 𝒜 dA f h0 (2 * i + q)).comp
    (LinearMap.codRestrict _
      ((EvenVariableAlgebra.monomialLinearMap (R := P) i).comp
        (coefficientCycles 𝒜 dA h0 q).subtype)
      fun ξ => monomial_mem_grade_two 𝒜 i q ξ.2.1)

/-- The underlying polynomial of the representative of `ξ` is `ξ T⁽ⁱ⁾`. -/
@[simp]
public theorem evenVariableToCoeff_monomialRep (i q : ℕ)
    (ξ : ↥(coefficientCycles 𝒜 dA h0 q)) :
    evenVariableToCoeff 𝒜 dA f h0 (-((2 * i + q : ℕ) : ℤ))
        (evenVariableMonomialRep 𝒜 dA f h0 i q ξ) =
      EvenVariableAlgebra.monomial i (ξ : A) :=
  evenVariableToCoeff_ofCoeffNat 𝒜 dA f h0 (2 * i + q) _

/-- **The representative `ξ T⁽ⁱ⁾` of a degree-`q` cycle is a cycle representative on the first
page**, in filtration degree `i` and total degree `2 i + q`: its differential is `± (ξ f) T⁽ⁱ⁻¹⁾`,
one step down the filtration. -/
public theorem monomialRep_mem_pageCycles (i q : ℕ) (ξ : ↥(coefficientCycles 𝒜 dA h0 q)) :
    evenVariableMonomialRep 𝒜 dA f h0 i q ξ ∈
      (evenVariableFiltration 𝒜 dA f h0).pageCycles 1 (i : ℤ) ((2 * i + q : ℕ) : ℤ) := by
  rw [mem_pageCycles_iff, evenVariableToCoeff_monomialRep]
  refine ⟨EvenVariableAlgebra.monomial_mem_coeffFiltration P le_rfl _, ?_⟩
  have h := evenPolynomialDifferential_monomial_sub_mem 𝒜 dA f P i (ξ : A)
  rwa [ξ.2.2, EvenVariableAlgebra.monomial_zero, sub_zero] at h

/-- **The class on the first page of the representative `ξ T⁽ⁱ⁾` of a degree-`q` cycle `ξ` of
`A`**, in the bidegree with filtration index `i` and total degree `2 i + q`, that is in the
bidegree `(i, j)` with `j - i = q`. -/
public def evenVariablePageOneRep (i q : ℕ) :
    ↥(coefficientCycles 𝒜 dA h0 q) →ₗ[P]
      ((evenVariableSpectralSequence 𝒜 dA f h0).page 1 le_rfl).X
        (filtrationBidegree true (i : ℤ) ((2 * i + q : ℕ) : ℤ)) :=
  ((evenVariableFiltrationData 𝒜 dA f h0).projection 1 le_rfl (i : ℤ)
      ((2 * i + q : ℕ) : ℤ)).hom.comp
    (LinearMap.codRestrict _ (evenVariableMonomialRep 𝒜 dA f h0 i q)
      (monomialRep_mem_pageCycles 𝒜 dA f h0 i q))

/-- **The first-page class of a cycle is the page class of the representative `ξ T⁽ⁱ⁾`.** -/
public theorem evenVariablePageOneRep_apply (i q : ℕ) (ξ : ↥(coefficientCycles 𝒜 dA h0 q)) :
    evenVariablePageOneRep 𝒜 dA f h0 i q ξ =
      (evenVariableFiltrationData 𝒜 dA f h0).projection 1 le_rfl (i : ℤ)
        ((2 * i + q : ℕ) : ℤ)
        ⟨evenVariableMonomialRep 𝒜 dA f h0 i q ξ,
          monomialRep_mem_pageCycles 𝒜 dA f h0 i q ξ⟩ := rfl

/-- The bidegree of the first page carrying the filtration index `i` and the total degree
`2 i + q` is `(i, i + q)`: the complementary degree `j` satisfies `j - i = q`, which is the
degree of the homology of `A` that the first page is built from. -/
public theorem filtrationBidegree_evenVariable (i q : ℕ) :
    filtrationBidegree true (i : ℤ) ((2 * i + q : ℕ) : ℤ) = ((i : ℤ), (i : ℤ) + q) := by
  rw [show filtrationBidegree true (i : ℤ) ((2 * i + q : ℕ) : ℤ) =
      ((i : ℤ), ((2 * i + q : ℕ) : ℤ) - (i : ℤ)) from rfl]
  refine Prod.ext rfl ?_
  push_cast
  ring

/-- **The first page is onto the classes of the representatives `ξ T⁽ⁱ⁾`**: a cycle
representative on the first page agrees, modulo the page relations, with the monomial of its
coefficient along `T⁽ⁱ⁾`, and that coefficient is a cycle of `A`. -/
public theorem surjective_evenVariablePageOneRep (i q : ℕ) :
    Function.Surjective (evenVariablePageOneRep 𝒜 dA f h0 i q) := by
  intro y
  obtain ⟨x, rfl⟩ := (evenVariableFiltrationData 𝒜 dA f h0).surjective 1 le_rfl (i : ℤ)
    ((2 * i + q : ℕ) : ℤ) y
  obtain ⟨hfilt, hdfilt⟩ :=
    (mem_pageCycles_iff 𝒜 dA f h0 1 (i : ℤ) ((2 * i + q : ℕ) : ℤ) x.1).1 x.2
  set b := evenVariableToCoeff 𝒜 dA f h0 (-((2 * i + q : ℕ) : ℤ)) x.1 with hbdef
  have hgrade : b ∈ EvenVariableAlgebra.grade 𝒜 2 (2 * i + q) :=
    evenVariableToCoeff_mem_grade 𝒜 dA f h0 (2 * i + q) rfl x.1
  have hgradeξ : b.coeff i ∈ 𝒜 q := coeff_mem_of_mem_grade_two 𝒜 i q _ rfl hgrade
  have hcycleξ : dA (b.coeff i) = 0 := by
    have h1 := hdfilt i (by omega)
    rw [evenPolynomialDifferential_coeff 𝒜 dA f, hfilt (i + 1) (by push_cast; omega)] at h1
    simpa using h1
  have hξ : b.coeff i ∈ coefficientCycles 𝒜 dA h0 q := ⟨hgradeξ, hcycleξ⟩
  refine ⟨⟨b.coeff i, hξ⟩, ?_⟩
  have hdmon := evenPolynomialDifferential_monomial_sub_mem 𝒜 dA f P i (b.coeff i)
  rw [hcycleξ, EvenVariableAlgebra.monomial_zero, sub_zero] at hdmon
  have hmem : evenVariableMonomialRep 𝒜 dA f h0 i q ⟨b.coeff i, hξ⟩ - x.1 ∈
      (evenVariableFiltration 𝒜 dA f h0).pageRelations 1 (i : ℤ) ((2 * i + q : ℕ) : ℤ) := by
    refine Submodule.mem_sup_left ?_
    rw [mem_pageCycles_iff, map_sub, evenVariableToCoeff_monomialRep]
    refine ⟨monomial_coeff_sub_mem P i hfilt, ?_⟩
    rw [map_sub]
    exact EvenVariableAlgebra.coeffFiltration_mono P (by omega)
      (Submodule.sub_mem _ hdmon hdfilt)
  refine sub_eq_zero.1 ?_
  have hzero : ((evenVariableFiltrationData 𝒜 dA f h0).projection 1 le_rfl (i : ℤ)
        ((2 * i + q : ℕ) : ℤ)).hom
      (⟨evenVariableMonomialRep 𝒜 dA f h0 i q ⟨b.coeff i, hξ⟩,
        monomialRep_mem_pageCycles 𝒜 dA f h0 i q ⟨b.coeff i, hξ⟩⟩ - x) = 0 := by
    rw [← LinearMap.mem_ker,
      (evenVariableFiltrationData 𝒜 dA f h0).kernel 1 le_rfl (i : ℤ) ((2 * i + q : ℕ) : ℤ),
      Submodule.mem_comap]
    simpa using hmem
  rwa [map_sub] at hzero

/-- **The first-page class of a cycle vanishes exactly when its representative is a relation on
the first page.** -/
public theorem evenVariablePageOneRep_eq_zero_iff (i q : ℕ)
    (ξ : ↥(coefficientCycles 𝒜 dA h0 q)) :
    evenVariablePageOneRep 𝒜 dA f h0 i q ξ = 0 ↔
      evenVariableMonomialRep 𝒜 dA f h0 i q ξ ∈
        (evenVariableFiltration 𝒜 dA f h0).pageRelations 1 (i : ℤ) ((2 * i + q : ℕ) : ℤ) := by
  have hiff : evenVariablePageOneRep 𝒜 dA f h0 i q ξ = 0 ↔
      (⟨evenVariableMonomialRep 𝒜 dA f h0 i q ξ,
          monomialRep_mem_pageCycles 𝒜 dA f h0 i q ξ⟩ :
        ↥((evenVariableFiltration 𝒜 dA f h0).pageCycles 1 (i : ℤ) ((2 * i + q : ℕ) : ℤ))) ∈
      LinearMap.ker ((evenVariableFiltrationData 𝒜 dA f h0).projection 1 le_rfl (i : ℤ)
        ((2 * i + q : ℕ) : ℤ)).hom := Iff.rfl
  rw [hiff, (evenVariableFiltrationData 𝒜 dA f h0).kernel 1 le_rfl (i : ℤ)
    ((2 * i + q : ℕ) : ℤ), Submodule.mem_comap]
  exact Iff.rfl

/-- **The representative of a boundary is a relation on the first page**: if `dA η = ξ`, then
`ξ T⁽ⁱ⁾` is the differential of `η T⁽ⁱ⁾` up to a term one step down the filtration. -/
public theorem evenVariableMonomialRep_mem_pageRelations_of_eq (i q : ℕ)
    (ξ : ↥(coefficientCycles 𝒜 dA h0 q)) {η : A} (hη : η ∈ 𝒜 (q + 1)) (hdη : dA η = ξ) :
    evenVariableMonomialRep 𝒜 dA f h0 i q ξ ∈
      (evenVariableFiltration 𝒜 dA f h0).pageRelations 1 (i : ℤ) ((2 * i + q : ℕ) : ℤ) := by
  obtain ⟨y₂, hy₂⟩ := exists_evenVariableToCoeff_eq 𝒜 dA f h0 (2 * i + (q + 1))
    (show (-((2 * i + (q + 1) : ℕ) : ℤ)) = -(((2 * i + q : ℕ) : ℤ) + 1) by push_cast; ring)
    (monomial_mem_grade_two 𝒜 i (q + 1) hη)
  have hdmon := evenPolynomialDifferential_monomial_sub_mem 𝒜 dA f P i η
  have hy₂cyc : y₂ ∈ (evenVariableFiltration 𝒜 dA f h0).pageCycles (1 - 1)
      ((i : ℤ) + 1 - 1) (((2 * i + q : ℕ) : ℤ) + 1) := by
    rw [mem_pageCycles_iff, hy₂]
    refine ⟨EvenVariableAlgebra.monomial_mem_coeffFiltration P (by omega) _,
      EvenVariableAlgebra.coeffFiltration_mono P
        (show (i : ℤ) ≤ (i : ℤ) + 1 - 1 - (1 - 1) by omega) ?_⟩
    rw [show evenPolynomialDifferential 𝒜 dA f (EvenVariableAlgebra.monomial i η) =
        (evenPolynomialDifferential 𝒜 dA f (EvenVariableAlgebra.monomial i η) -
          EvenVariableAlgebra.monomial i (dA η)) + EvenVariableAlgebra.monomial i (dA η)
      by abel]
    exact Submodule.add_mem _
      (EvenVariableAlgebra.coeffFiltration_mono P (by omega) hdmon)
      (EvenVariableAlgebra.monomial_mem_coeffFiltration P le_rfl _)
  refine Submodule.mem_sup.2
    ⟨evenVariableMonomialRep 𝒜 dA f h0 i q ξ -
      (evenVariableCochainComplex 𝒜 dA f h0).d (-(((2 * i + q : ℕ) : ℤ) + 1))
        (-((2 * i + q : ℕ) : ℤ)) y₂, ?_,
      (evenVariableCochainComplex 𝒜 dA f h0).d (-(((2 * i + q : ℕ) : ℤ) + 1))
        (-((2 * i + q : ℕ) : ℤ)) y₂, ⟨y₂, hy₂cyc, rfl⟩, by abel⟩
  rw [mem_pageCycles_iff]
  have hdiff : evenVariableToCoeff 𝒜 dA f h0 (-((2 * i + q : ℕ) : ℤ))
      (evenVariableMonomialRep 𝒜 dA f h0 i q ξ -
        (evenVariableCochainComplex 𝒜 dA f h0).d (-(((2 * i + q : ℕ) : ℤ) + 1))
          (-((2 * i + q : ℕ) : ℤ)) y₂) =
      -(evenPolynomialDifferential 𝒜 dA f (EvenVariableAlgebra.monomial i η) -
        EvenVariableAlgebra.monomial i (dA η)) := by
    rw [map_sub, evenVariableToCoeff_monomialRep, evenVariableToCoeff_d 𝒜 dA f h0
      (show (-((2 * i + q : ℕ) : ℤ)) = -(((2 * i + q : ℕ) : ℤ) + 1) + 1 by ring), hy₂, hdη]
    abel
  rw [hdiff]
  refine ⟨Submodule.neg_mem _ hdmon, ?_⟩
  rw [map_neg]
  exact EvenVariableAlgebra.coeffFiltration_mono P
    (show (i : ℤ) - 1 ≤ (i : ℤ) - 1 - (1 - 1) by omega)
    (Submodule.neg_mem _
      (evenPolynomialDifferential_mem_coeffFiltration 𝒜 dA f P hdmon))

/-- **The first-page class of a cycle vanishes exactly when the cycle is a boundary**: the
coefficient along `T⁽ⁱ⁾` of a relation on the first page is a boundary of `A`, and conversely the
representative of a boundary `dA η` is the differential of `η T⁽ⁱ⁾` up to a term one step down
the filtration. -/
public theorem ker_evenVariablePageOneRep (i q : ℕ) :
    LinearMap.ker (evenVariablePageOneRep 𝒜 dA f h0 i q) =
      (coefficientBoundaries 𝒜 dA h0 q).comap (coefficientCycles 𝒜 dA h0 q).subtype := by
  ext ξ
  rw [LinearMap.mem_ker, evenVariablePageOneRep_eq_zero_iff, Submodule.mem_comap,
    Submodule.coe_subtype, mem_coefficientBoundaries]
  constructor
  · intro hrel
    obtain ⟨y₁, hy₁, z, ⟨y₂, hy₂, rfl⟩, hsum⟩ := Submodule.mem_sup.1 hrel
    have hy₁' := (mem_pageCycles_iff 𝒜 dA f h0 (1 - 1) ((i : ℤ) - 1)
      ((2 * i + q : ℕ) : ℤ) y₁).1 hy₁
    have hy₂' := (mem_pageCycles_iff 𝒜 dA f h0 (1 - 1) ((i : ℤ) + 1 - 1)
      (((2 * i + q : ℕ) : ℤ) + 1) y₂).1 hy₂
    have hcoe := congrArg
      (fun z => (evenVariableToCoeff 𝒜 dA f h0 (-((2 * i + q : ℕ) : ℤ)) z).coeff i) hsum
    simp only [map_add, EvenVariableAlgebra.coeff_add, Finsupp.add_apply] at hcoe
    rw [evenVariableToCoeff_monomialRep, evenVariableToCoeff_d 𝒜 dA f h0
      (show (-((2 * i + q : ℕ) : ℤ)) = -(((2 * i + q : ℕ) : ℤ) + 1) + 1 by ring),
      hy₁'.1 i (by omega), evenPolynomialDifferential_coeff 𝒜 dA f,
      hy₂'.1 (i + 1) (by push_cast; omega)] at hcoe
    refine ⟨(evenVariableToCoeff 𝒜 dA f h0 (-(((2 * i + q : ℕ) : ℤ) + 1)) y₂).coeff i, ?_, ?_⟩
    · exact coeff_mem_of_mem_grade_two 𝒜 i (q + 1) (2 * i + q + 1) (by omega)
        (evenVariableToCoeff_mem_grade 𝒜 dA f h0 (2 * i + q + 1) (by push_cast; ring) y₂)
    · rw [EvenVariableAlgebra.coeff_monomial, Finsupp.single_eq_same] at hcoe
      simpa using hcoe
  · rintro ⟨η, hη, hdη⟩
    exact evenVariableMonomialRep_mem_pageRelations_of_eq 𝒜 dA f h0 i q ξ hη hdη

/-- **The first page of the spectral sequence is the homology of `A`, shifted by the degree of
`T⁽ⁱ⁾`**: in the bidegree with filtration index `i` and total degree `2 i + q`, that is in the
bidegree `(i, j)` with `j - i = q`, it is the degree-`q` homology of `A`, by the map sending the
class of a degree-`q` cycle `ξ` to the page class of the representative `ξ T⁽ⁱ⁾`. -/
public def evenVariablePageOneEquiv (i q : ℕ) :
    coefficientHomology 𝒜 dA h0 q ≃ₗ[P]
      ((evenVariableSpectralSequence 𝒜 dA f h0).page 1 le_rfl).X
        (filtrationBidegree true (i : ℤ) ((2 * i + q : ℕ) : ℤ)) :=
  (Submodule.quotEquivOfEq _ _ (ker_evenVariablePageOneRep 𝒜 dA f h0 i q).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (surjective_evenVariablePageOneRep 𝒜 dA f h0 i q))

/-- **The identification of the first page carries the class of a degree-`q` cycle `ξ` of `A` to
the page class of the representative `ξ T⁽ⁱ⁾`.** -/
@[simp]
public theorem evenVariablePageOneEquiv_mk (i q : ℕ) (ξ : ↥(coefficientCycles 𝒜 dA h0 q)) :
    evenVariablePageOneEquiv 𝒜 dA f h0 i q (Submodule.Quotient.mk ξ) =
      (evenVariableFiltrationData 𝒜 dA f h0).projection 1 le_rfl (i : ℤ)
        ((2 * i + q : ℕ) : ℤ)
        ⟨evenVariableMonomialRep 𝒜 dA f h0 i q ξ,
          monomialRep_mem_pageCycles 𝒜 dA f h0 i q ξ⟩ := by
  rw [evenVariablePageOneEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, evenVariablePageOneRep_apply]

/-! ### The first differential -/

/-- The Koszul sign of a degree-`q` element against `f`: the signed product is
`(-1) ^ q • (ξ f)`. -/
public theorem signRingHom_mul_eq_smul (q : ℕ) {ξ : A} (hξ : ξ ∈ 𝒜 q) :
    signRingHom 𝒜 1 ξ * f = (-1 : R) ^ q • (ξ * f) := by
  rw [signRingHom_of_mem 𝒜 1 q hξ, one_mul, smul_mul_assoc]

omit [IsDifferentialGradedAlgebra (EvenVariableAlgebra.grade 𝒜 2)
  (evenPolynomialDifferential 𝒜 dA f)] in
/-- **The signed product of a cycle with `f` is a cycle one degree up.** -/
public theorem signRingHom_mul_mem_coefficientCycles (hf_grade : f ∈ 𝒜 1) (hf_cycle : dA f = 0)
    (q : ℕ) (ξ : ↥(coefficientCycles 𝒜 dA h0 q)) :
    signRingHom 𝒜 1 (ξ : A) * f ∈ coefficientCycles 𝒜 dA h0 (q + 1) := by
  rw [signRingHom_mul_eq_smul 𝒜 f q ξ.2.1]
  refine ⟨Submodule.smul_mem _ _ (SetLike.mul_mem_graded ξ.2.1 hf_grade), ?_⟩
  rw [map_smul, IsDifferentialGradedAlgebra.leibniz (𝒜 := 𝒜) (d := dA) ξ.2.1 hf_grade,
    ξ.2.2, hf_cycle]
  simp

/-- **The first differential of the spectral sequence is multiplication by `f`, with the Koszul
sign of the degree of the cycle.** On the first-page class of the representative `ξ T⁽ⁱ⁺¹⁾` of a
degree-`q` cycle `ξ` of `A` it is the class of the representative
`(signRingHom 𝒜 1 ξ * f) T⁽ⁱ⁾` of the degree-`q + 1` cycle `signRingHom 𝒜 1 ξ * f`, which is
`(-1) ^ q • (ξ f)` by `signRingHom_mul_eq_smul`. The sign is the one of
`evenPolynomialDifferential_monomial` and is not dropped: Tag 0GZ6 writes the differential
unsigned, which is this statement up to the unit `(-1) ^ q` of the coefficient ring. -/
public theorem evenVariablePageOneRep_d (hf_grade : f ∈ 𝒜 1) (hf_cycle : dA f = 0) (i q : ℕ)
    (ξ : ↥(coefficientCycles 𝒜 dA h0 q)) :
    ((evenVariableSpectralSequence 𝒜 dA f h0).page 1 le_rfl).d
        (filtrationBidegree true ((i + 1 : ℕ) : ℤ) ((2 * (i + 1) + q : ℕ) : ℤ))
        (filtrationBidegree true (i : ℤ) ((2 * i + (q + 1) : ℕ) : ℤ))
        (evenVariablePageOneRep 𝒜 dA f h0 (i + 1) q ξ) =
      evenVariablePageOneRep 𝒜 dA f h0 i (q + 1)
        ⟨signRingHom 𝒜 1 (ξ : A) * f,
          signRingHom_mul_mem_coefficientCycles 𝒜 dA f h0 hf_grade hf_cycle q ξ⟩ := by
  have hdx : (evenVariableCochainComplex 𝒜 dA f h0).d (-((2 * (i + 1) + q : ℕ) : ℤ))
        (-((2 * i + (q + 1) : ℕ) : ℤ)) (evenVariableMonomialRep 𝒜 dA f h0 (i + 1) q ξ) =
      evenVariableMonomialRep 𝒜 dA f h0 i (q + 1)
        ⟨signRingHom 𝒜 1 (ξ : A) * f,
          signRingHom_mul_mem_coefficientCycles 𝒜 dA f h0 hf_grade hf_cycle q ξ⟩ := by
    refine evenVariableToCoeff_injective 𝒜 dA f h0 _ ?_
    rw [evenVariableToCoeff_d 𝒜 dA f h0
        (show (-((2 * i + (q + 1) : ℕ) : ℤ)) = -((2 * (i + 1) + q : ℕ) : ℤ) + 1
          by push_cast; ring),
      evenVariableToCoeff_monomialRep, evenVariableToCoeff_monomialRep,
      evenPolynomialDifferential_monomial, ξ.2.2]
    simp
  have key := evenVariableFiltrationData_differential 𝒜 dA f h0 1 le_rfl
    ((i + 1 : ℕ) : ℤ) ((2 * (i + 1) + q : ℕ) : ℤ) (i : ℤ) ((2 * i + (q + 1) : ℕ) : ℤ)
    (by push_cast; ring) (by push_cast; ring)
    (evenVariableMonomialRep 𝒜 dA f h0 (i + 1) q ξ)
    (monomialRep_mem_pageCycles 𝒜 dA f h0 (i + 1) q ξ)
    (by rw [hdx]; exact monomialRep_mem_pageCycles 𝒜 dA f h0 i (q + 1) _)
  rw [evenVariablePageOneRep_apply, evenVariablePageOneRep_apply, key]
  congr 1
  exact Subtype.ext hdx

/-! ### Tag 0GZ6, part (2) -/

omit [IsDifferentialGradedAlgebra (EvenVariableAlgebra.grade 𝒜 2)
  (evenPolynomialDifferential 𝒜 dA f)] in
/-- For an even divided-power variable of degree two the explicit differential of Tag 09PM is a
differential graded algebra structure on the extension: the prescribed value `f` has degree
`2 - 1 = 1` and is a cycle. -/
public theorem evenPolynomialDifferential_two_isDGA [IsStrictlyGradedComm 𝒜] (hf_grade : f ∈ 𝒜 1)
    (hf_cycle : dA f = 0) :
    IsDifferentialGradedAlgebra (EvenVariableAlgebra.grade 𝒜 2)
      (evenPolynomialDifferential 𝒜 dA f) := by
  have : Fact (Even 2) := ⟨even_two⟩
  exact evenPolynomialDifferential_isDGA 𝒜 dA 2 (by norm_num) f (by simpa using hf_grade)
    hf_cycle

end PageOne

section Statement

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Ring A] [Algebra R A] [Algebra P A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] (dA : A →ₗ[R] A)
  [IsDifferentialGradedAlgebra 𝒜 dA] (f : A)

/-- **The spectral sequence of a degree-two divided-power variable, Tag 0GZ6 part (2).**

Let `(A, dA)` be a strictly graded-commutative differential graded algebra, let `f` be a cycle of
degree `1 = 2 - 1`, and let `A⟨T⟩` be the extension by a divided-power variable of degree two with
`dT = f`, with the differential of Tag 09PM. Filtering `A⟨T⟩` by `Fᵖ = ⨁_{n ≤ p} A T⁽ⁿ⁾` gives a
spectral sequence, and this records the four assertions of the tag:

* its first page in the bidegree with filtration index `i` and total degree `2 i + q` is the
  degree-`q` homology of `A`, by an isomorphism carrying the class of a degree-`q` cycle `ξ` to
  the page class of the representative `ξ T⁽ⁱ⁾`;
* that bidegree is `(i, j)` with `j - i = q`, so the first page in the bidegree `(i, j)` is
  `H_{j - i}(A) · T⁽ⁱ⁾`, as the tag writes it;
* its first differential sends the class of `ξ T⁽ⁱ⁺¹⁾` to the class of
  `(signRingHom 𝒜 1 ξ * f) T⁽ⁱ⁾ = ((-1) ^ q • (ξ f)) T⁽ⁱ⁾`, that is, it is multiplication by `f`
  with the Koszul sign of the degree of `ξ`;
* it converges, the filtration being finite in every degree, and abuts to the homology of the
  complex of `A⟨T⟩`, whose degree-`k` term is the degree-`k` homology of `A⟨T⟩`.

The sign of the first differential is the one of `evenPolynomialDifferential_monomial`; the tag
writes `f ξ` unsigned, which is the same up to the unit `(-1) ^ q` of the coefficient ring. -/
@[stacks 0GZ6 "degree_two"]
public theorem evenVariableSpectralSequence_degree_two (hf_grade : f ∈ 𝒜 1) (hf_cycle : dA f = 0)
    (h0 : ∀ p : P, algebraMap P A p ∈ 𝒜 0) :
    letI : IsDifferentialGradedAlgebra (EvenVariableAlgebra.grade 𝒜 2)
        (evenPolynomialDifferential 𝒜 dA f) :=
      evenPolynomialDifferential_two_isDGA 𝒜 dA f hf_grade hf_cycle
    (∀ i q : ℕ, ∃ e : coefficientHomology 𝒜 dA h0 q ≃ₗ[P]
          ((evenVariableSpectralSequence 𝒜 dA f h0).page 1 le_rfl).X
            (filtrationBidegree true (i : ℤ) ((2 * i + q : ℕ) : ℤ)),
        ∀ ξ : ↥(coefficientCycles 𝒜 dA h0 q),
          e (Submodule.Quotient.mk ξ) = evenVariablePageOneRep 𝒜 dA f h0 i q ξ) ∧
      (∀ i q : ℕ, filtrationBidegree true (i : ℤ) ((2 * i + q : ℕ) : ℤ) =
          ((i : ℤ), (i : ℤ) + q)) ∧
      (∀ (i q : ℕ) (ξ : ↥(coefficientCycles 𝒜 dA h0 q)),
          ((evenVariableSpectralSequence 𝒜 dA f h0).page 1 le_rfl).d
              (filtrationBidegree true ((i + 1 : ℕ) : ℤ) ((2 * (i + 1) + q : ℕ) : ℤ))
              (filtrationBidegree true (i : ℤ) ((2 * i + (q + 1) : ℕ) : ℤ))
              (evenVariablePageOneRep 𝒜 dA f h0 (i + 1) q ξ) =
            evenVariablePageOneRep 𝒜 dA f h0 i (q + 1)
              ⟨signRingHom 𝒜 1 (ξ : A) * f,
                signRingHom_mul_mem_coefficientCycles 𝒜 dA f h0 hf_grade hf_cycle q ξ⟩ ∧
            signRingHom 𝒜 1 (ξ : A) * f = (-1 : R) ^ q • ((ξ : A) * f)) ∧
      ((evenVariableFiltrationData 𝒜 dA f h0).Converges ∧
        HomologicalSpectralSequenceAbutsTo (evenVariableSpectralSequence 𝒜 dA f h0)
          (fun n => (evenVariableCochainComplex 𝒜 dA f h0).homology (-n)) ∧
        ∀ k : ℕ, Nonempty ((evenVariableCochainComplex 𝒜 dA f h0).homology (-(k : ℤ)) ≅
          ModuleCat.of P (evenVariableHomology 𝒜 dA f h0 k))) := by
  have : IsDifferentialGradedAlgebra (EvenVariableAlgebra.grade 𝒜 2)
      (evenPolynomialDifferential 𝒜 dA f) :=
    evenPolynomialDifferential_two_isDGA 𝒜 dA f hf_grade hf_cycle
  refine ⟨fun i q => ⟨evenVariablePageOneEquiv 𝒜 dA f h0 i q, fun ξ => ?_⟩,
    filtrationBidegree_evenVariable,
    fun i q ξ => ⟨evenVariablePageOneRep_d 𝒜 dA f h0 hf_grade hf_cycle i q ξ,
      signRingHom_mul_eq_smul 𝒜 f q ξ.2.1⟩,
    evenVariableFiltrationData_converges 𝒜 dA f h0,
    TorFiltrationData.abutsTo_homology (evenVariableFiltrationData 𝒜 dA f h0)
      (evenVariableFiltrationData_converges 𝒜 dA f h0),
    fun k => ⟨evenVariableHomologyIso 𝒜 dA f h0 k⟩⟩
  rw [evenVariablePageOneEquiv_mk, evenVariablePageOneRep_apply]

end Statement

end DividedPowers.TateResolution

end
