module

public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TopCech

/-!
# The residue pairing and the dual description of the top cohomology of a twist

Let `R` be a commutative ring and `n : ℕ`. The free `R`-modules
$$ R[T_0, \ldots, T_n] \quad\text{and}\quad
   \tfrac{1}{T_0 \cdots T_n} R[\tfrac{1}{T_0}, \ldots, \tfrac{1}{T_n}] $$
are paired by sending `(f, g)` to the coefficient of `1/(T₀ ⋯ Tₙ)` in `f * g`: the polynomial
monomial `T^m` pairs with the negative Laurent monomial `T^e` to `1` exactly when
`mᵢ + eᵢ = -1` for every `i`, and to `0` in all other cases. Since the degree-`m` monomials of
`R[T₀, …, Tₙ]` are finite in number, that pairing identifies

$$ \left(\tfrac{1}{T_0 \cdots T_n} R[\tfrac{1}{T_0}, \ldots, \tfrac{1}{T_n}]\right)_d
   = \operatorname{Hom}_R\bigl((R[T_0, \ldots, T_n])_{-n-1-d},\ R\bigr) $$

as `R`-modules, for every integer `d`. This is the identification with which
[Stacks, Tag 01XU] restates the cohomology of `𝒪(d)` on `ℙⁿ_R`: it turns the top-degree answer
of [Stacks, Tag 01XT] — the free module on the degree-`d` Laurent monomials with every exponent
negative — into the `R`-dual of a module of homogeneous polynomials, and it is what makes
`Hⁿ ≠ 0` exactly in the degrees `d ≤ -n - 1`.

Everything is in the monomial model of
`Stacks.ProjectiveSpace.Cohomology.twistChart`, where the left-hand side is
`Stacks.ProjectiveSpace.Cohomology.negativeTwistPart` and the degree-`m` part of
`R[T₀, …, Tₙ]` is the chart `Stacks.ProjectiveSpace.Cohomology.twistChart R n m ∅` with no
variable inverted — the module which
`Stacks.ProjectiveSpace.Cohomology.twistChartEmptyLinearEquiv` identifies with
`MvPolynomial.homogeneousSubmodule` in nonnegative degrees. Applied to the cokernel computed by
`Stacks.ProjectiveSpace.Cohomology.topCechCohomologyEquiv`, it puts the top Čech cohomology of
the standard cover in the dual form the source uses.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.residuePairing`: the coefficient of `1/(T₀ ⋯ Tₙ)` in a
  product of two Laurent polynomials, as an `R`-bilinear map.
* `Stacks.ProjectiveSpace.Cohomology.twistChartBasis` and
  `Stacks.ProjectiveSpace.Cohomology.negativeTwistPartBasis`: the Laurent monomial bases of a
  chart and of the negative part.
* `Stacks.ProjectiveSpace.Cohomology.residueDual`: the map to the dual that the residue pairing
  defines.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.finite_laurentMonomials_empty`: a polynomial chart has
  finitely many monomials in each degree, which is what makes the dual free of the same rank.
* `Stacks.ProjectiveSpace.Cohomology.topDualEquiv` and
  `Stacks.ProjectiveSpace.Cohomology.topDualEquiv_apply`: **the duality** — the degree-`d`
  negative Laurent part is the `R`-dual of the degree-`(-n-1-d)` polynomial chart, and the
  identification is the residue pairing.
* `Stacks.ProjectiveSpace.Cohomology.topDualPolynomialEquiv`: the same with the target written
  as the dual of `MvPolynomial.homogeneousSubmodule`, available in the degrees `d ≤ -n - 1`
  where that index is a natural number.
* `Stacks.ProjectiveSpace.Cohomology.topCechCohomologyDualEquiv` and
  `Stacks.ProjectiveSpace.Cohomology.topCechCohomologyPolynomialDualEquiv`: **the top-degree
  case of the displayed equation of [Stacks, Tag 01XU]**, at the Čech level: the cokernel of the
  top Čech differential of the standard cover of `ℙⁿ_R` for `𝒪(d)` is
  `Hom_R((R[T₀, …, Tₙ])_{-n-1-d}, R)`.

## Implementation notes

**No tag attribute is attached.** The displayed equation of [Stacks, Tag 01XU] has three
cases, `q = 0`, `q ≠ 0, n` and `q = n`, and all three are statements about the sheaf cohomology
`H^q(ℙⁿ_R, 𝒪(d))`. What this file supplies is the dual description of the module appearing in
the third case, and that description applied to the top Čech cohomology of the standard cover.
The passage from the Čech cohomology of the standard cover to sheaf cohomology is
[Stacks, Tag 01XD]; it is proved in general but is not applied to this complex, so no case of
the equation is a statement about `H^q(ℙⁿ_R, 𝒪(d))` yet.

**The complementary degree is spelled `-d - (n + 1)`.** That is the spelling of
`Stacks.ProjectiveSpace.Cohomology.negativeLaurentMonomialsEquiv`, which is reused rather than
reproved; it is the integer `-n - 1 - d` of the source.

**Why the map and the equivalence are built separately.** The equivalence is assembled from the
two monomial bases and the dual basis, which is where the finiteness of the index set is used;
the residue pairing is defined independently, by its formula. `topDualEquiv_toLinearMap`
identifies the two, and only has to be checked on a basis vector. Defining the equivalence by
the pairing instead would make the formula hold by definition but leave bijectivity to prove by
hand.

## References

* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
-/

@[expose] public noncomputable section

open Finsupp

universe u

namespace Stacks.ProjectiveSpace.Cohomology

variable {R : Type u} [CommRing R] {n : ℕ} {d : ℤ}

/-! ### Finiteness of a polynomial chart -/

/-- The Laurent monomials of total degree `d` with every exponent nonnegative are finite in
number: every exponent lies between `0` and `d`. -/
theorem finite_nonnegLaurentMonomials (n : ℕ) (d : ℤ) :
    {e : Fin (n + 1) → ℤ | (∑ i, e i) = d ∧ ∀ i, 0 ≤ e i}.Finite := by
  refine Set.Finite.subset
    (Set.Finite.pi fun _ : Fin (n + 1) => Set.finite_Icc (0 : ℤ) (max d 0)) fun e he => ?_
  refine Set.mem_univ_pi.2 fun i => ⟨he.2 i, ?_⟩
  have h : e i ≤ ∑ j, e j :=
    Finset.single_le_sum (f := e) (fun j _ => he.2 j) (Finset.mem_univ i)
  rw [he.1] at h
  exact le_trans h (le_max_left _ _)

/-- **The degree-`d` part of `R[T₀, …, Tₙ]` is finitely generated**: the chart with no variable
inverted has finitely many monomials. -/
theorem finite_laurentMonomials_empty (n : ℕ) (d : ℤ) :
    (laurentMonomials n d (∅ : Set (Fin (n + 1)))).Finite :=
  (finite_nonnegLaurentMonomials n d).subset fun _ he => ⟨he.1, fun i => he.2 i (by simp)⟩

/-- The type of Laurent monomials of degree `d` in the chart with no variable inverted is
finite. -/
instance instFiniteLaurentMonomialsEmpty (n : ℕ) (d : ℤ) :
    Finite (laurentMonomials n d (∅ : Set (Fin (n + 1)))) :=
  (finite_laurentMonomials_empty n d).to_subtype

/-! ### The monomial bases -/

/-- The single Laurent monomials are a basis of a module of supported families. -/
private theorem coe_supportedBasis_apply {α : Type*} (s : Set α) (j : s) :
    ((Finsupp.basisSingleOne.map
        (Finsupp.supportedEquivFinsupp (M := R) (R := R) s).symm) j : α →₀ R)
      = Finsupp.single j.1 1 := by
  classical
  rw [Module.Basis.map_apply]
  have h : (Finsupp.supportedEquivFinsupp (M := R) (R := R) s)
      ⟨Finsupp.single j.1 1, Finsupp.single_mem_supported R 1 j.2⟩
      = Finsupp.basisSingleOne (R := R) (ι := s) j := by
    ext k
    show (Finsupp.single j.1 (1 : R)) k.1 = _
    rw [Finsupp.coe_basisSingleOne, Finsupp.single_apply, Finsupp.single_apply]
    exact if_congr (by simp [Subtype.ext_iff]) rfl rfl
  rw [← h, LinearEquiv.symm_apply_apply]

/-- The coordinates of a supported family in that basis are its own values. -/
private theorem supportedBasis_repr_apply {α : Type*} (s : Set α)
    (f : Finsupp.supported R R s) (j : s) :
    (Finsupp.basisSingleOne.map
        (Finsupp.supportedEquivFinsupp (M := R) (R := R) s).symm).repr f j
      = (f : α →₀ R) j.1 := by
  rw [Module.Basis.map_repr]; rfl

/-- The Laurent monomial basis of the degree-`d` part of `R[T₀, …, Tₙ, 1/∏_{i ∈ S} Tᵢ]`. -/
def twistChartBasis (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (S : Set (Fin (n + 1))) :
    Module.Basis (laurentMonomials n d S) R (twistChart R n d S) :=
  Finsupp.basisSingleOne.map (Finsupp.supportedEquivFinsupp _).symm

/-- A basis vector of a chart is the corresponding Laurent monomial. -/
theorem coe_twistChartBasis_apply {S : Set (Fin (n + 1))} (e : laurentMonomials n d S) :
    ((twistChartBasis R n d S) e : (Fin (n + 1) → ℤ) →₀ R) = Finsupp.single e.1 1 :=
  coe_supportedBasis_apply _ e

/-- The coordinates of a section of a chart are its Laurent coefficients. -/
theorem twistChartBasis_repr_apply {S : Set (Fin (n + 1))} (f : twistChart R n d S)
    (e : laurentMonomials n d S) :
    (twistChartBasis R n d S).repr f e = (f : (Fin (n + 1) → ℤ) →₀ R) e.1 :=
  supportedBasis_repr_apply _ f e

/-- The Laurent monomial basis of the degree-`d` part of
`(1/(T₀ ⋯ Tₙ)) R[1/T₀, …, 1/Tₙ]`. -/
def negativeTwistPartBasis (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    Module.Basis (negativeLaurentMonomials n d) R (negativeTwistPart R n d) :=
  Finsupp.basisSingleOne.map (Finsupp.supportedEquivFinsupp _).symm

/-- A basis vector of the negative part is the corresponding negative Laurent monomial. -/
theorem coe_negativeTwistPartBasis_apply (e : negativeLaurentMonomials n d) :
    ((negativeTwistPartBasis R n d) e : (Fin (n + 1) → ℤ) →₀ R) = Finsupp.single e.1 1 :=
  coe_supportedBasis_apply _ e

/-! ### The residue pairing -/

/-- **The residue pairing**: the coefficient of the Laurent monomial `1/(T₀ ⋯ Tₙ)` in the
product `g * f` of two Laurent polynomials in `T₀, …, Tₙ`. Written out on coefficients it is
`(g, f) ↦ ∑ₑ gₑ fₗ` with `l` the exponent vector `-e - 1` complementary to `e`. -/
def residuePairing (R : Type u) [CommRing R] (n : ℕ) :
    ((Fin (n + 1) → ℤ) →₀ R) →ₗ[R] ((Fin (n + 1) → ℤ) →₀ R) →ₗ[R] R :=
  Finsupp.lsum R fun e =>
    LinearMap.toSpanSingleton R (((Fin (n + 1) → ℤ) →₀ R) →ₗ[R] R)
      (Finsupp.lapply (fun i => -e i - 1))

/-- The residue pairing, on coefficients. -/
theorem residuePairing_apply (g f : (Fin (n + 1) → ℤ) →₀ R) :
    residuePairing R n g f = g.sum fun e c => c * f (fun i => -e i - 1) := by
  simp [residuePairing, Finsupp.lsum_apply, LinearMap.toSpanSingleton, Finsupp.lapply,
    smul_eq_mul]

/-- A Laurent monomial `T^e` pairs with a Laurent polynomial by reading off its coefficient at
the complementary exponent vector `-e - 1`. -/
theorem residuePairing_single (e : Fin (n + 1) → ℤ) (r : R) (f : (Fin (n + 1) → ℤ) →₀ R) :
    residuePairing R n (Finsupp.single e r) f = r * f (fun i => -e i - 1) := by
  rw [residuePairing_apply, Finsupp.sum_single_index (by rw [zero_mul])]

/-! ### The duality -/

/-- The map from the degree-`d` negative Laurent part to the `R`-dual of the degree-`(-n-1-d)`
polynomial chart defined by the residue pairing. -/
def residueDual (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    negativeTwistPart R n d →ₗ[R]
      (twistChart R n (-d - ((n : ℤ) + 1)) (∅ : Set (Fin (n + 1))) →ₗ[R] R) :=
  (LinearMap.lcomp R R (Submodule.subtype
      (twistChart R n (-d - ((n : ℤ) + 1)) (∅ : Set (Fin (n + 1)))))).comp
    ((residuePairing R n).comp (Submodule.subtype (negativeTwistPart R n d)))

/-- `residueDual` is the residue pairing. -/
theorem residueDual_apply (g : negativeTwistPart R n d)
    (f : twistChart R n (-d - ((n : ℤ) + 1)) (∅ : Set (Fin (n + 1)))) :
    residueDual R n d g f = residuePairing R n (g : (Fin (n + 1) → ℤ) →₀ R) f :=
  rfl

open Classical in
/-- **The dual description of the top cohomology of `𝒪(d)`.** For every integer `d` the
degree-`d` part of `(1/(T₀ ⋯ Tₙ)) R[1/T₀, …, 1/Tₙ]` is the `R`-dual of the degree-`(-n-1-d)`
part of `R[T₀, …, Tₙ]`, the identification being the residue pairing
(`topDualEquiv_apply`). Both sides vanish when `-n ≤ d`. -/
def topDualEquiv (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    negativeTwistPart R n d ≃ₗ[R]
      (twistChart R n (-d - ((n : ℤ) + 1)) (∅ : Set (Fin (n + 1))) →ₗ[R] R) :=
  (negativeTwistPartBasis R n d).repr.trans
    ((Finsupp.domLCongr (negativeLaurentMonomialsEquiv n d)).trans
      (twistChartBasis R n (-d - ((n : ℤ) + 1)) (∅ : Set (Fin (n + 1)))).dualBasis.repr.symm)

/-- The duality is the map defined by the residue pairing. -/
theorem topDualEquiv_toLinearMap (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    (topDualEquiv R n d).toLinearMap = residueDual R n d := by
  classical
  refine (negativeTwistPartBasis R n d).ext fun e => ?_
  refine LinearMap.ext fun f => ?_
  rw [residueDual_apply, coe_negativeTwistPartBasis_apply, residuePairing_single, one_mul]
  show ((twistChartBasis R n (-d - ((n : ℤ) + 1))
      (∅ : Set (Fin (n + 1)))).dualBasis.repr.symm
    (Finsupp.domLCongr (negativeLaurentMonomialsEquiv n d)
      ((negativeTwistPartBasis R n d).repr ((negativeTwistPartBasis R n d) e)))) f = _
  rw [Module.Basis.repr_self, Finsupp.domLCongr_single, Module.Basis.repr_symm_single_one,
    Module.Basis.dualBasis_apply, twistChartBasis_repr_apply]
  rfl

/-- **The duality is the coefficient of `1/(T₀ ⋯ Tₙ)` in the product.** -/
theorem topDualEquiv_apply (g : negativeTwistPart R n d)
    (f : twistChart R n (-d - ((n : ℤ) + 1)) (∅ : Set (Fin (n + 1)))) :
    topDualEquiv R n d g f = residuePairing R n (g : (Fin (n + 1) → ℤ) →₀ R) f := by
  rw [← residueDual_apply, ← topDualEquiv_toLinearMap]; rfl

/-- **The dual description with the polynomials written as polynomials.** For `d ≤ -n - 1` the
degree-`d` part of `(1/(T₀ ⋯ Tₙ)) R[1/T₀, …, 1/Tₙ]` is `Hom_R((R[T₀, …, Tₙ])_{-n-1-d}, R)`. In
the remaining degrees `-n ≤ d` the left-hand side vanishes, by
`Stacks.ProjectiveSpace.Cohomology.negativeTwistPart_eq_bot_of_le`. -/
def topDualPolynomialEquiv (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (hd : d ≤ -(n : ℤ) - 1) :
    negativeTwistPart R n d ≃ₗ[R]
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (-d - ((n : ℤ) + 1)).toNat →ₗ[R] R) :=
  (topDualEquiv R n d).trans
    (twistChartEmptyLinearEquiv (R := R) n (d := -d - ((n : ℤ) + 1)) (by omega)).dualMap.symm

/-! ### The top Čech cohomology of the standard cover, in the dual form -/

/-- **The top-degree case of the displayed equation of [Stacks, Tag 01XU], at the Čech level.**
The cokernel of the top Čech differential of the standard cover of `ℙⁿ_R` for `𝒪(d)` — the
top-degree Čech cohomology, computed by
`Stacks.ProjectiveSpace.Cohomology.topCechCohomologyEquiv` — is the `R`-dual of the
degree-`(-n-1-d)` part of `R[T₀, …, Tₙ]`. -/
def topCechCohomologyDualEquiv (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    (↥(twistChart R n d (Set.univ : Set (Fin (n + 1)))) ⧸
        (LinearMap.range (topCechDiff R n d)).comap
          (twistChart R n d (Set.univ : Set (Fin (n + 1)))).subtype) ≃ₗ[R]
      (twistChart R n (-d - ((n : ℤ) + 1)) (∅ : Set (Fin (n + 1))) →ₗ[R] R) :=
  (topCechCohomologyEquiv R n d).trans (topDualEquiv R n d)

/-- **The top-degree case of the displayed equation of [Stacks, Tag 01XU], at the Čech level,
with the polynomials written as polynomials.** For `d ≤ -n - 1` the top-degree Čech cohomology
of the standard cover of `ℙⁿ_R` for `𝒪(d)` is `Hom_R((R[T₀, …, Tₙ])_{-n-1-d}, R)`; for
`-n ≤ d` it vanishes, by
`Stacks.ProjectiveSpace.Cohomology.topCechDiff_range_eq_twistChart_univ`. -/
def topCechCohomologyPolynomialDualEquiv (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (hd : d ≤ -(n : ℤ) - 1) :
    (↥(twistChart R n d (Set.univ : Set (Fin (n + 1)))) ⧸
        (LinearMap.range (topCechDiff R n d)).comap
          (twistChart R n d (Set.univ : Set (Fin (n + 1)))).subtype) ≃ₗ[R]
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (-d - ((n : ℤ) + 1)).toNat →ₗ[R] R) :=
  (topCechCohomologyEquiv R n d).trans (topDualPolynomialEquiv R n d hd)

end Stacks.ProjectiveSpace.Cohomology

end
