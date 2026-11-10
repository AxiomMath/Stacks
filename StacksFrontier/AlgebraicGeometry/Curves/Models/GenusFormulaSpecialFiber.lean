module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.GenusFormula
public import StacksFrontier.AlgebraicGeometry.Curves.Models.IntersectionForm
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberComponentProperCurve
public import Mathlib.Data.Rat.Cast.Order
import StacksCore.Tactic.StacksAttribute

/-!
# The genus of a curve from the numerical data of the special fibre of a model

In the situation of [Stacks, Tag 0C61] let `C₁, …, Cₙ` be the irreducible components of the
special fibre of a regular proper model `X ⟶ Spec(R)`, let `mᵢ` be their multiplicities, so that
`X_k = Σ mᵢCᵢ`, let `κᵢ = H⁰(Cᵢ, 𝒪_{Cᵢ})` and let `gᵢ` be the genus of `Cᵢ`. [Stacks, Tag 0CA3]
expresses the genus of the generic curve `C` in that data:

`g_C = 1 + Σᵢ mᵢ([κᵢ : k](gᵢ - 1) - ½(Cᵢ · Cᵢ))`.

## Main definitions

* `Stacks.Models.RegularProperModelSituation.specialFiberComponentWeight` — the weight
  `wᵢ = [κᵢ : k]` of a component, `κᵢ = Γ(Cᵢ, 𝒪_{Cᵢ})` being a finite field extension of the
  residue field by [Stacks, Tag 0C6P].
* `Stacks.Models.RegularProperModelSituation.specialFiberIntersectionProduct` and
  `Stacks.Models.RegularProperModelSituation.specialFiberDivisorDegree` — the intersection
  product of [Stacks, Tag 0C65] and the degree `deg(𝒪_X(Σ cⱼCⱼ)|_{Cᵢ})` on the *canonical*
  family of components, that is `Stacks.Models.intersectionProduct` and
  `Stacks.Models.componentDegree` with their properness and dimension hypotheses discharged by
  `StacksFrontier/AlgebraicGeometry/Curves/Models/SpecialFiberComponentProperCurve.lean`.
* `Stacks.Models.twoPartialEulerChar` — twice the closed form
  `Σᵢ cᵢχᵢ - ½((Σᵢⱼ cᵢcⱼaᵢⱼ) - Σᵢ cᵢaᵢᵢ)` predicted for `χ(𝒪_{D_c})`, `D_c = Σᵢ cᵢCᵢ`.
* `Stacks.Models.RegularProperModelSituation.SpecialFiberEulerRecursion` — the recursion of
  [Stacks, Tag 0CA2] along a chain of divisors supported on the special fibre.

## Main results

* `Stacks.Models.two_mul_eq_twoPartialEulerChar_of_recursion` — **the telescoping step of the
  proof of [Stacks, Tag 0CA3]**: a function on nonnegative coefficient families that vanishes at
  the empty divisor and satisfies the recursion of [Stacks, Tag 0CA2] is the closed form
  `Stacks.Models.twoPartialEulerChar`.
* `Stacks.Models.two_mul_eq_sum_of_recursion_of_ker` — the same at the multiplicity vector,
  where the quadratic term disappears because the intersection matrix kills that vector: this is
  the equality of which the source says that it "deserves some explanation".
* `Stacks.Models.two_mul_eq_twoPartialEulerChar_of_recursion_le` and
  `Stacks.Models.two_mul_eq_sum_of_recursion_le_of_ker` — the same two statements with the
  recursion asked only along chains below the multiplicity vector, which is the form the
  divisors contained in the special fibre supply; they are what
  `StacksFrontier/AlgebraicGeometry/Curves/Models/GenusFormulaModel.lean` uses.
* `Stacks.Models.RegularProperModelSituation.cast_genus_eq_sum_specialFiberComponents` — the
  formula of [Stacks, Tag 0CA3] from the three inputs listed below, taken as hypotheses.

## The argument

The source's proof chooses a chain `∅ = D₀ ⊂ D₁ ⊂ … ⊂ D_m = X_k` of effective Cartier divisors
with `D_{j+1} = D_j + C_{i_j}`, applies [Stacks, Tag 0CA2] at each step and collapses the
resulting sum. The collapse uses the orthogonality clause of [Stacks, Tag 0C66], which says that
the intersection matrix kills the multiplicity vector, to turn the off-diagonal part of the
double sum into minus the diagonal part.

Rather than enumerate a chain, the same bookkeeping is done here by induction on the partial
coefficient family `c`, which is what a chain is: `D_c = Σᵢ cᵢCᵢ`, and the chain's steps are the
transitions `c ↦ c + eₖ`. The function `E c = χ(X_k, 𝒪_{D_c})` is then pinned down by its value
at `c = 0` together with the one-step recursion, and `Stacks.Models.twoPartialEulerChar` is the
closed form it must take — the induction being on `Σᵢ cᵢ`, with one component removed at a time,
exactly as the source lowers one nonzero multiplicity at a time. Symmetry of the intersection
matrix is what makes the closed form satisfy the recursion for *every* index `k`, so it is a
hypothesis of the induction.

## Implementation notes

**What is carried as a hypothesis, and why.** This file is the bookkeeping of the proof of
[Stacks, Tag 0CA3] only. Its last statement,
`Stacks.Models.RegularProperModelSituation.cast_genus_eq_sum_specialFiberComponents`, takes three
inputs of the source's proof as named hypotheses and carries no attribute; the tag is carried
unconditionally, at the model's own data, by
`Stacks.Models.RegularProperModelSituation.cast_genus_eq_one_add_sum_specialFiberComponent` in
`StacksFrontier/AlgebraicGeometry/Curves/Models/GenusFormulaModel.lean`, where all three are proved.
The notes below record what the three hypotheses are.

* `hrec`, the recursion of [Stacks, Tag 0CA2]. Only the *second* equality of that tag is proved,
  as `Stacks.Models.eulerCharacteristic_negativeTwist_restrict_eq`; the first equality,
  `χ(𝒪_{D'}) - χ(𝒪_D) = χ(𝒪_X(-D)|_{Cᵢ})`, is not, and without it the two tagged halves do not
  compose into a recursion for `χ(𝒪_{D_c})`. See the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Curves/Models/GenusFormula.lean`. In `hrec` the increment
  `chi k` occupies exactly the slot of `χ(Cₖ, 𝒪_{Cₖ})` of Tag 0CA2, and is determined by `E`:
  taking `c = 0` in the recursion gives `chi k = E eₖ = χ(𝒪_{Cₖ})`.
* `hbasic`, the identity `1 - g_C = χ(X_k, 𝒪_{X_k})` that the source calls "the basic tool". It
  is the composite of [Stacks, Tag 0B9T], which has no occurrence in this library, with the
  comparison of `AlgebraicGeometry.genus` and the Euler characteristic of the structure sheaf,
  which has none either: `AlgebraicGeometry.genus` is `dim_k H¹(X, 𝒪_X)` by definition and the
  identification of `χ(𝒪_C)` with `1 - g_C` needs `H⁰(C, 𝒪_C) = K` together with the vanishing
  of the higher cohomology, i.e. [Stacks, Tag 02O6].
* `hchi`, the identity `χ(Cᵢ, 𝒪_{Cᵢ}) = [κᵢ : k](1 - gᵢ)`, which is the sentence of the source's
  proof following its citation of [Stacks, Tag 04L2]. It is also what pins down `gᵢ`: the
  component genus of the source is the genus of `Cᵢ` *over `κᵢ`*, not over `k`, and no structure
  morphism `Cᵢ ⟶ Spec(κᵢ)` is available in this library, so `gᵢ` is an integer family and
  `hchi` is its defining property. The weight `[κᵢ : k]` by contrast is *not* a hypothesis: it is
  `Stacks.Models.RegularProperModelSituation.specialFiberComponentWeight`, built from
  [Stacks, Tag 0C6P].

**The intersection matrix is an abstract family, pinned by `hexpand`.** As in
`Stacks.Models.sum_multiplicity_mul_intersectionMatrix_eq_zero_of_expansion` and
`Stacks.Models.intersectionProduct_comm_of_expansion_of_matrix_symm`, the matrix `(Cᵢ · Cⱼ)` is
an abstract `N : ι → ι → ℤ` constrained by the bilinear expansion `hexpand`, the invertible case
of [Stacks, Tag 0AYX]. That hypothesis determines `N` completely —
`Stacks.Models.RegularProperModelSituation.intersectionMatrix_eq_of_expansion` reads off
`N i j = (Cᵢ · Cⱼ)` from it — and it is also what supplies the orthogonality input `hker` of the
collapse, through the orthogonality clause of [Stacks, Tag 0C66]. Symmetry of `N` is the
separate hypothesis `hsymm`: it is [Stacks, Tag 0C65], and it is a theorem of this library at the
intersection matrix of the special fibre,
`Stacks.Models.RegularProperModelSituation.specialFiberIntersectionMatrix_comm` of
`StacksFrontier/AlgebraicGeometry/Curves/Models/DegreePairingSymmetry.lean`. It stays a hypothesis
here only because `N` is an abstract family; see
`StacksFrontier/AlgebraicGeometry/Curves/Models/IntersectionSymmetry.lean` for the reduction.

**The formula is stated over `ℚ`.** The term `½(Cᵢ · Cᵢ)` is not an integer term by term, only
after summation, exactly as for `AlgebraicGeometry.NumericalType.cast_genus`. Everything above
the final statement is integral, the halving being carried as a factor `2` on the other side.

## References

* [Stacks Project, Tag 0CA3](https://stacks.math.columbia.edu/tag/0CA3)
* [Stacks Project, Tag 0CA2](https://stacks.math.columbia.edu/tag/0CA2)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C65](https://stacks.math.columbia.edu/tag/0C65)
* [Stacks Project, Tag 0C66](https://stacks.math.columbia.edu/tag/0C66)
* [Stacks Project, Tag 0C6P](https://stacks.math.columbia.edu/tag/0C6P)
* [Stacks Project, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0B9T](https://stacks.math.columbia.edu/tag/0B9T)
* [Stacks Project, Tag 04L2](https://stacks.math.columbia.edu/tag/04L2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Models

/-! ### The arithmetic of the telescoping sum -/

section Arithmetic

variable {ι : Type*} [Fintype ι]

/-- The bilinear form `(x, y) ↦ Σᵢⱼ xᵢyⱼaᵢⱼ` of an integer matrix. -/
private def matrixPairing (N : ι → ι → ℤ) (x y : ι → ℤ) : ℤ := ∑ i, ∑ j, x i * y j * N i j

private theorem matrixPairing_add_left (N : ι → ι → ℤ) (x x' y : ι → ℤ) :
    matrixPairing N (x + x') y = matrixPairing N x y + matrixPairing N x' y := by
  simp only [matrixPairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem matrixPairing_add_right (N : ι → ι → ℤ) (x y y' : ι → ℤ) :
    matrixPairing N x (y + y') = matrixPairing N x y + matrixPairing N x y' := by
  simp only [matrixPairing, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

/-- A vector in the kernel of the matrix is isotropic for its bilinear form. -/
private theorem matrixPairing_self_eq_zero (N : ι → ι → ℤ) (x : ι → ℤ)
    (hker : ∀ i, ∑ j, x j * N i j = 0) : matrixPairing N x x = 0 :=
  Finset.sum_eq_zero fun i _ =>
    calc ∑ j, x i * x j * N i j = ∑ j, x i * (x j * N i j) :=
          Finset.sum_congr rfl fun j _ => by ring
      _ = x i * ∑ j, x j * N i j := (Finset.mul_sum _ _ _).symm
      _ = 0 := by rw [hker i, mul_zero]

/-- **Twice the Euler characteristic predicted for `𝒪_{D_c}`**, where `D_c = Σᵢ cᵢCᵢ`, `χᵢ` is
`χ(Cᵢ, 𝒪_{Cᵢ})` and `aᵢⱼ` is the intersection matrix:

`2χ(𝒪_{D_c}) = 2Σᵢ cᵢχᵢ - (Σᵢⱼ cᵢcⱼaᵢⱼ - Σᵢ cᵢaᵢᵢ)`.

The subtracted term is twice the sum `Σ_{j < j'} (C_{i_j} · C_{i_{j'}})` of the off-diagonal
pairs along a chain of divisors realizing `c`, which is what the repeated application of
[Stacks, Tag 0CA2] accumulates. -/
public def twoPartialEulerChar (chi : ι → ℤ) (N : ι → ι → ℤ) (c : ι → ℤ) : ℤ :=
  2 * (∑ i, c i * chi i) - (∑ i, ∑ j, c i * c j * N i j) + ∑ i, c i * N i i

/-- The quadratic term of `Stacks.Models.twoPartialEulerChar` is the bilinear form of the
intersection matrix at the coefficient family. -/
private theorem twoPartialEulerChar_eq (chi : ι → ℤ) (N : ι → ι → ℤ) (c : ι → ℤ) :
    twoPartialEulerChar chi N c =
      2 * (∑ i, c i * chi i) - matrixPairing N c c + ∑ i, c i * N i i := rfl

variable [DecidableEq ι]

private theorem sum_single_mul (k : ι) (f : ι → ℤ) :
    ∑ i, (Pi.single k 1 : ι → ℤ) i * f i = f k := by
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
    (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul]), Pi.single_eq_same, one_mul]

private theorem matrixPairing_single_left (N : ι → ι → ℤ) (k : ι) (y : ι → ℤ) :
    matrixPairing N (Pi.single k 1) y = ∑ j, y j * N k j := by
  rw [matrixPairing, Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
    (fun j _ hj => by simp [Pi.single_eq_of_ne hj])]
  exact Finset.sum_congr rfl fun j _ => by rw [Pi.single_eq_same, one_mul]

private theorem matrixPairing_single_right (N : ι → ι → ℤ) (k : ι) (x : ι → ℤ) :
    matrixPairing N x (Pi.single k 1) = ∑ i, x i * N i k := by
  rw [matrixPairing]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
    (fun j _ hj => by simp [Pi.single_eq_of_ne hj]), Pi.single_eq_same, mul_one]

private theorem matrixPairing_single_single (N : ι → ι → ℤ) (k : ι) :
    matrixPairing N (Pi.single k 1) (Pi.single k 1) = N k k := by
  rw [matrixPairing_single_left]; exact sum_single_mul k _

/-- **The closed form satisfies the recursion of [Stacks, Tag 0CA2]**: adding one more component
`Cₖ` to `D_c` changes `2χ(𝒪_{D_c})` by `2(χₖ - Σⱼ cⱼaₖⱼ)`, the subtracted sum being the
intersection product `(Cₖ · D_c)`.

Symmetry of the intersection matrix is what makes this hold at every index: the two cross terms
`Σᵢ cᵢaᵢₖ` and `Σⱼ cⱼaₖⱼ` of the quadratic form are equal only then. -/
public theorem twoPartialEulerChar_add_single (chi : ι → ℤ) (N : ι → ι → ℤ)
    (hsymm : ∀ i j, N i j = N j i) (c : ι → ℤ) (k : ι) :
    twoPartialEulerChar chi N (c + Pi.single k 1) =
      twoPartialEulerChar chi N c + 2 * (chi k - ∑ j, c j * N k j) := by
  have h1 : ∑ i, (c + Pi.single k 1 : ι → ℤ) i * chi i = (∑ i, c i * chi i) + chi k := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, sum_single_mul]
  have h2 : ∑ i, (c + Pi.single k 1 : ι → ℤ) i * N i i = (∑ i, c i * N i i) + N k k := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, sum_single_mul]
  have hcross : ∑ i, c i * N i k = ∑ j, c j * N k j :=
    Finset.sum_congr rfl fun i _ => by rw [hsymm i k]
  have h3 : matrixPairing N (c + Pi.single k 1) (c + Pi.single k 1) =
      matrixPairing N c c + 2 * (∑ j, c j * N k j) + N k k := by
    rw [matrixPairing_add_left, matrixPairing_add_right, matrixPairing_add_right,
      matrixPairing_single_left, matrixPairing_single_right, matrixPairing_single_single, hcross]
    ring
  rw [twoPartialEulerChar_eq, twoPartialEulerChar_eq, h1, h2, h3]
  ring

omit [Fintype ι] in
/-- Adding a basis vector to a nonnegative coefficient family commutes with the inclusion
`ℕ ⟶ ℤ`. -/
private theorem cast_add_single (c : ι → ℕ) (k : ι) :
    (fun i => (((c + Pi.single k 1 : ι → ℕ) i : ℕ) : ℤ)) =
      (fun i => ((c i : ℕ) : ℤ)) + Pi.single k 1 := by
  funext i
  by_cases h : i = k
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

/-- The telescoping induction, with the recursion asked only along chains below `m`. -/
private theorem two_mul_eq_twoPartialEulerChar_aux (chi : ι → ℤ) (N : ι → ι → ℤ)
    (hsymm : ∀ i j, N i j = N j i) (m : ι → ℕ) (E : (ι → ℕ) → ℤ) (hE0 : E 0 = 0)
    (hEstep : ∀ (c : ι → ℕ) (k : ι), c + Pi.single k 1 ≤ m →
      E (c + Pi.single k 1) = E c - (∑ j, (c j : ℤ) * N k j) + chi k)
    (c : ι → ℕ) (hc : c ≤ m) :
    2 * E c = twoPartialEulerChar chi N (fun i => (c i : ℤ)) := by
  suffices H : ∀ n (c : ι → ℕ), c ≤ m → ∑ i, c i = n →
      2 * E c = twoPartialEulerChar chi N (fun i => (c i : ℤ)) from H _ c hc rfl
  intro n
  induction n with
  | zero =>
    intro c _ hc
    have hc0 : c = 0 := funext fun i => Finset.sum_eq_zero_iff.mp hc i (Finset.mem_univ i)
    subst hc0
    rw [hE0, mul_zero]
    simp [twoPartialEulerChar]
  | succ n ih =>
    intro c hcm hc
    obtain ⟨k, hk⟩ : ∃ k, c k ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const_zero] at hc
      exact Nat.succ_ne_zero n hc.symm
    have hck : 1 ≤ c k := Nat.one_le_iff_ne_zero.mpr hk
    have hadd : Function.update c k (c k - 1) + Pi.single k 1 = c := by
      funext i
      by_cases h : i = k
      · subst h
        simp only [Pi.add_apply, Function.update_self, Pi.single_eq_same]
        omega
      · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
    have hsplit : ∑ i ∈ Finset.univ.erase k, c i + c k = ∑ i, c i :=
      Finset.sum_erase_add Finset.univ c (Finset.mem_univ k)
    have hsum : ∑ i, Function.update c k (c k - 1) i = n := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
      omega
    have hle : Function.update c k (c k - 1) ≤ m := by
      intro i
      by_cases h : i = k
      · subst h
        simp only [Function.update_self]
        exact (Nat.sub_le _ _).trans (hcm i)
      · rw [Function.update_of_ne h]
        exact hcm i
    have hrec := ih _ hle hsum
    rw [← hadd, hEstep _ _ (hadd.symm ▸ hcm), cast_add_single,
      twoPartialEulerChar_add_single chi N hsymm, ← hrec]
    ring

/-- **The telescoping step of the proof of [Stacks, Tag 0CA3].** A function `E` on nonnegative
coefficient families that vanishes at the empty divisor and satisfies the recursion of
[Stacks, Tag 0CA2] is the closed form `Stacks.Models.twoPartialEulerChar`, up to the factor two
that carries the halving.

The induction is on `Σᵢ cᵢ`, one component being removed at a time, which is the source's chain
`∅ = D₀ ⊂ D₁ ⊂ … ⊂ D_m = X_k` read backwards. -/
public theorem two_mul_eq_twoPartialEulerChar_of_recursion (chi : ι → ℤ) (N : ι → ι → ℤ)
    (hsymm : ∀ i j, N i j = N j i) (E : (ι → ℕ) → ℤ) (hE0 : E 0 = 0)
    (hEstep : ∀ (c : ι → ℕ) (k : ι),
      E (c + Pi.single k 1) = E c - (∑ j, (c j : ℤ) * N k j) + chi k)
    (c : ι → ℕ) :
    2 * E c = twoPartialEulerChar chi N (fun i => (c i : ℤ)) :=
  two_mul_eq_twoPartialEulerChar_aux chi N hsymm c E hE0 (fun c k _ => hEstep c k) c le_rfl

/-- **The collapse of the telescoping sum at the multiplicity vector**,

`2χ(X_k, 𝒪_{X_k}) = 2Σᵢ mᵢχᵢ + Σᵢ mᵢaᵢᵢ`.

The quadratic term of `Stacks.Models.twoPartialEulerChar` disappears because the intersection
matrix kills the multiplicity vector, which is the orthogonality clause of [Stacks, Tag 0C66];
this is the equality of which the source says that it "deserves some explanation". -/
public theorem two_mul_eq_sum_of_recursion_of_ker (chi : ι → ℤ) (N : ι → ι → ℤ)
    (hsymm : ∀ i j, N i j = N j i) (E : (ι → ℕ) → ℤ) (hE0 : E 0 = 0)
    (hEstep : ∀ (c : ι → ℕ) (k : ι),
      E (c + Pi.single k 1) = E c - (∑ j, (c j : ℤ) * N k j) + chi k)
    (m : ι → ℕ) (hker : ∀ i, ∑ j, (m j : ℤ) * N i j = 0) :
    2 * E m = 2 * (∑ i, (m i : ℤ) * chi i) + ∑ i, (m i : ℤ) * N i i := by
  rw [two_mul_eq_twoPartialEulerChar_of_recursion chi N hsymm E hE0 hEstep m,
    twoPartialEulerChar_eq, matrixPairing_self_eq_zero N _ hker]
  ring

/-- **The telescoping step of the proof of [Stacks, Tag 0CA3], below a bound.** The same as
`Stacks.Models.two_mul_eq_twoPartialEulerChar_of_recursion`, with the recursion of
[Stacks, Tag 0CA2] asked only along chains below a fixed family `m`: the divisors
`D_c = Σᵢ cᵢCᵢ` the source applies Tag 0CA2 to are the ones contained in `X_k = Σᵢ mᵢCᵢ`. -/
public theorem two_mul_eq_twoPartialEulerChar_of_recursion_le (chi : ι → ℤ) (N : ι → ι → ℤ)
    (hsymm : ∀ i j, N i j = N j i) (m : ι → ℕ) (E : (ι → ℕ) → ℤ) (hE0 : E 0 = 0)
    (hEstep : ∀ (c : ι → ℕ) (k : ι), c + Pi.single k 1 ≤ m →
      E (c + Pi.single k 1) = E c - (∑ j, (c j : ℤ) * N k j) + chi k)
    (c : ι → ℕ) (hc : c ≤ m) :
    2 * E c = twoPartialEulerChar chi N (fun i => (c i : ℤ)) :=
  two_mul_eq_twoPartialEulerChar_aux chi N hsymm m E hE0 hEstep c hc

/-- **The collapse of the telescoping sum at the multiplicity vector, below the bound.** The same
as `Stacks.Models.two_mul_eq_sum_of_recursion_of_ker`, with the recursion asked only along chains
below `m`. -/
public theorem two_mul_eq_sum_of_recursion_le_of_ker (chi : ι → ℤ) (N : ι → ι → ℤ)
    (hsymm : ∀ i j, N i j = N j i) (m : ι → ℕ) (E : (ι → ℕ) → ℤ) (hE0 : E 0 = 0)
    (hEstep : ∀ (c : ι → ℕ) (k : ι), c + Pi.single k 1 ≤ m →
      E (c + Pi.single k 1) = E c - (∑ j, (c j : ℤ) * N k j) + chi k)
    (hker : ∀ i, ∑ j, (m j : ℤ) * N i j = 0) :
    2 * E m = 2 * (∑ i, (m i : ℤ) * chi i) + ∑ i, (m i : ℤ) * N i i := by
  rw [two_mul_eq_twoPartialEulerChar_of_recursion_le chi N hsymm m E hE0 hEstep m le_rfl,
    twoPartialEulerChar_eq, matrixPairing_self_eq_zero N _ hker]
  ring

omit [DecidableEq ι] in
/-- The rearrangement of the collapsed sum into the shape of [Stacks, Tag 0CA3]. -/
public theorem cast_eq_one_add_sum (m : ι → ℕ) (N : ι → ι → ℤ) (chi w gcomp : ι → ℤ)
    (gC Em : ℤ)
    (hZ : 2 * Em = 2 * (∑ i, (m i : ℤ) * chi i) + ∑ i, (m i : ℤ) * N i i)
    (hbasic : 1 - gC = Em) (hchi : ∀ i, chi i = w i * (1 - gcomp i)) :
    (gC : ℚ) = 1 + ∑ i, (m i : ℚ) *
      ((w i : ℚ) * ((gcomp i : ℚ) - 1) - (N i i : ℚ) / 2) := by
  rw [← hbasic, Finset.sum_congr rfl (fun i _ => by rw [hchi i])] at hZ
  have hQ : (2 : ℚ) * (1 - (gC : ℚ)) =
      2 * (∑ i, (m i : ℚ) * ((w i : ℚ) * (1 - (gcomp i : ℚ)))) +
        ∑ i, (m i : ℚ) * (N i i : ℚ) := by
    have hcast := congrArg (fun x : ℤ => (x : ℚ)) hZ
    push_cast at hcast
    exact hcast
  have hsum : ∑ i, (m i : ℚ) * ((w i : ℚ) * ((gcomp i : ℚ) - 1) - (N i i : ℚ) / 2) =
      (-∑ i, (m i : ℚ) * ((w i : ℚ) * (1 - (gcomp i : ℚ)))) -
        (∑ i, (m i : ℚ) * (N i i : ℚ)) / 2 := by
    rw [← Finset.sum_neg_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  linarith

end Arithmetic

/-! ### The numerical data of the special fibre -/

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **The weight `wᵢ = [κᵢ : k]` of an irreducible component of the special fibre**, the degree
over the residue field of the field `κᵢ = Γ(Cᵢ, 𝒪_{Cᵢ})` of global functions on the component.

That `κᵢ` is a field, finite over `k`, is [Stacks, Tag 0C6P] applied to the component, in the
form `RegularProperModelSituation.isField_and_finite_globalSections_specialFiberComponent`. -/
public def specialFiberComponentWeight (Z : irreducibleComponents S.specialFiber) : ℕ :=
  letI : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
  Module.finrank S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤)

/-- **The weight of a component of the special fibre is positive**: `κᵢ` is a nonzero vector
space over `k`, being a field, and it is finite dimensional. -/
public theorem specialFiberComponentWeight_pos (Z : irreducibleComponents S.specialFiber) :
    0 < S.specialFiberComponentWeight Z := by
  let _ : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
  obtain ⟨hfield, hfin⟩ := S.isField_and_finite_globalSections_specialFiberComponent Z
  let _ : Field Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) := hfield.toField
  exact Module.finrank_pos

/-- **A morphism over `k` out of a component bounds its weight below by divisibility.** If
`g : Cᵢ ⟶ C'` is a morphism over `k` to a `k`-scheme whose global functions form a field `κ'`,
then `[κ' : k]` divides the weight `wᵢ = [κᵢ : k]`, the map `g^* : κ' ⟶ κᵢ` making `κᵢ` a
`κ'`-vector space. -/
public theorem finrank_dvd_specialFiberComponentWeight (Z : irreducibleComponents S.specialFiber)
    {C' : Scheme.{u}} (p' : C' ⟶ Spec (.of S.k))
    (g : (S.specialFiberComponentIdeal Z).subscheme ⟶ C')
    (hg : g ≫ p' = S.specialFiberComponentToSpec Z) (hC' : IsField Γ(C', ⊤)) :
    letI : Algebra S.k Γ(C', ⊤) := ((Scheme.ΓSpecIso (.of S.k)).inv ≫ p'.appTop).hom.toAlgebra
    Module.finrank S.k Γ(C', ⊤) ∣ S.specialFiberComponentWeight Z := by
  let : Algebra S.k Γ(C', ⊤) := ((Scheme.ΓSpecIso (.of S.k)).inv ≫ p'.appTop).hom.toAlgebra
  let : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
  let : Field Γ(C', ⊤) := hC'.toField
  let : Algebra Γ(C', ⊤) Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    g.appTop.hom.toAlgebra
  have : IsScalarTower S.k Γ(C', ⊤) Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom x =
        g.appTop.hom (((Scheme.ΓSpecIso (.of S.k)).inv ≫ p'.appTop).hom x)
      rw [← hg, Scheme.Hom.comp_appTop]
      rfl
  exact ⟨_, (Module.finrank_mul_finrank S.k Γ(C', ⊤)
    Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤)).symm⟩

variable [Fintype (irreducibleComponents S.specialFiber)]

/-- **The degree `deg(𝒪_X(Σⱼ cⱼCⱼ)|_{Cᵢ})` on a component of the special fibre.**

This is `Stacks.Models.componentDegree` at the canonical family of components, with the
structure morphism of the component, its properness and the dimension bound supplied rather than
assumed; see
`StacksFrontier/AlgebraicGeometry/Curves/Models/SpecialFiberComponentProperCurve.lean`. -/
public def specialFiberDivisorDegree (Z : irreducibleComponents S.specialFiber)
    (c : irreducibleComponents S.specialFiber → ℕ) : ℤ :=
  componentDegree S.k (S.specialFiberComponentIdeal Z) (S.specialFiberComponentToSpec Z)
    (S.isProper_specialFiberComponentToSpec Z)
    (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
    (divisorSheaf S Finset.univ (fun Y => S.specialFiberComponentIdeal Y) c)
    (isInvertible_divisorSheaf S Finset.univ (fun Y => S.specialFiberComponentIdeal Y) c
      (fun Y _ => S.isEffectiveCartierDivisor_specialFiberComponent Y))

/-- **The intersection product `(Σᵢ aᵢCᵢ · Σⱼ bⱼCⱼ)` of [Stacks, Tag 0C65] on the components of
the special fibre.**

This is `Stacks.Models.intersectionProduct` at the canonical family of components, with the
structure morphisms, their properness, the dimension bounds and the effective-Cartier property
of [Stacks, Tag 0C5Z] supplied rather than assumed. -/
public def specialFiberIntersectionProduct
    (a : irreducibleComponents S.specialFiber → ℤ)
    (b : irreducibleComponents S.specialFiber → ℕ) : ℤ :=
  intersectionProduct S Finset.univ (fun Y => S.specialFiberComponentIdeal Y)
    (fun Y => S.specialFiberComponentToSpec Y)
    (fun Y => S.isProper_specialFiberComponentToSpec Y)
    (fun Y => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Y) a b
    (fun Y _ => S.isEffectiveCartierDivisor_specialFiberComponent Y)

variable [DecidableEq (irreducibleComponents S.specialFiber)]

/-- **The intersection product against a single component is a degree**,
`(Cᵢ · Σⱼ cⱼCⱼ) = deg(𝒪_X(Σⱼ cⱼCⱼ)|_{Cᵢ})`: the degree pairing of [Stacks, Tag 0C64] against the
basis vector `eᵢ` keeps only the `i`-th term of its defining sum. -/
public theorem specialFiberIntersectionProduct_single (Z : irreducibleComponents S.specialFiber)
    (c : irreducibleComponents S.specialFiber → ℕ) :
    S.specialFiberIntersectionProduct (Pi.single Z 1) c = S.specialFiberDivisorDegree Z c :=
  intersectionProduct_single_eq_componentDegree S Finset.univ
    (fun Y => S.specialFiberComponentIdeal Y) (fun Y => S.specialFiberComponentToSpec Y)
    (fun Y => S.isProper_specialFiberComponentToSpec Y)
    (fun Y => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Y) Z
    (Finset.mem_univ Z) c (fun Y _ => S.isEffectiveCartierDivisor_specialFiberComponent Y)

/-- **The bilinear expansion pins down the intersection matrix**: a family `N` satisfying the
expansion of [Stacks, Tag 0AYX] has `N i j = (Cᵢ · Cⱼ)`. -/
public theorem intersectionMatrix_eq_of_expansion (N : irreducibleComponents S.specialFiber →
      irreducibleComponents S.specialFiber → ℤ)
    (hexpand : ∀ c Z, S.specialFiberDivisorDegree Z c = ∑ Y, (c Y : ℤ) * N Z Y)
    (Z Y : irreducibleComponents S.specialFiber) :
    N Z Y = S.specialFiberIntersectionProduct (Pi.single Z 1) (Pi.single Y 1) := by
  rw [S.specialFiberIntersectionProduct_single Z (Pi.single Y 1), hexpand]
  rw [Finset.sum_eq_single_of_mem Y (Finset.mem_univ Y)
    (fun W _ hW => by rw [Pi.single_eq_of_ne hW]; norm_num)]
  rw [Pi.single_eq_same]
  norm_num

/-- **The recursion of [Stacks, Tag 0CA2] along a chain of divisors supported on the special
fibre.** The value `E c` stands for the Euler characteristic `χ(X_k, 𝒪_{D_c})` of the divisor
`D_c = Σᵢ cᵢCᵢ`, and `chi k` for `χ(Cₖ, 𝒪_{Cₖ})`: the recursion says that the empty divisor has
Euler characteristic zero and that adding one more component `Cₖ` changes it by
`-(Cₖ · D_c) + χ(Cₖ, 𝒪_{Cₖ})`.

This is exactly the two equalities of Tag 0CA2 composed. Only the second of them is proved, as
`Stacks.Models.eulerCharacteristic_negativeTwist_restrict_eq`, so the recursion is a named
hypothesis rather than a result; see the module documentation. Note that `chi` is determined by
`E`, the case `c = 0` of the recursion giving `chi k = E eₖ`. -/
public def SpecialFiberEulerRecursion (chi : irreducibleComponents S.specialFiber → ℤ)
    (E : (irreducibleComponents S.specialFiber → ℕ) → ℤ) : Prop :=
  E 0 = 0 ∧ ∀ (c : irreducibleComponents S.specialFiber → ℕ)
    (Z : irreducibleComponents S.specialFiber),
      E (c + Pi.single Z 1) = E c - S.specialFiberIntersectionProduct (Pi.single Z 1) c + chi Z

/-- **The formula of [Stacks, Tag 0CA3] from its three inputs.** In the situation of
[Stacks, Tag 0C61], with `C₁, …, Cₙ` the irreducible components of the special fibre of the
model, `mᵢ` their multiplicities, `κᵢ = H⁰(Cᵢ, 𝒪_{Cᵢ})`, `wᵢ = [κᵢ : k]`, `gᵢ` the genus of `Cᵢ`
and `g_C` the genus of `C`,

`g_C = 1 + Σᵢ mᵢ(wᵢ(gᵢ - 1) - ½(Cᵢ · Cᵢ))`.

Three inputs of the source's proof are not available in this library and are carried as named
hypotheses: `hrec`, the recursion of [Stacks, Tag 0CA2] along a chain of divisors, of which only
the second equality is proved; `hbasic`, the identity `1 - g_C = χ(X_k, 𝒪_{X_k})` of
[Stacks, Tag 0B9T]; and `hchi`, the identity `χ(Cᵢ, 𝒪_{Cᵢ}) = wᵢ(1 - gᵢ)`, which also pins down
the component genus `gᵢ` — the genus of `Cᵢ` over `κᵢ`, which this library cannot form. The
intersection matrix is the abstract family `N` pinned by the bilinear expansion `hexpand` of
[Stacks, Tag 0AYX], whose symmetry `hsymm` is [Stacks, Tag 0C65]. See the module documentation.

What is proved is the source's own bookkeeping: the telescoping of the chain, the collapse of the
off-diagonal part of the double sum against its diagonal through the orthogonality clause of
[Stacks, Tag 0C66], and the rearrangement into the displayed formula. -/
public theorem cast_genus_eq_sum_specialFiberComponents
    (m : irreducibleComponents S.specialFiber → ℕ)
    (N : irreducibleComponents S.specialFiber → irreducibleComponents S.specialFiber → ℤ)
    (chi gcomp : irreducibleComponents S.specialFiber → ℤ) (gC : ℤ)
    (E : (irreducibleComponents S.specialFiber → ℕ) → ℤ)
    (hdec : S.specialFiberIdeal = ∏ Z, S.specialFiberComponentIdeal Z ^ m Z)
    (hexpand : ∀ c Z, S.specialFiberDivisorDegree Z c = ∑ Y, (c Y : ℤ) * N Z Y)
    (hsymm : ∀ Z Y, N Z Y = N Y Z)
    (hrec : S.SpecialFiberEulerRecursion chi E)
    (hbasic : 1 - gC = E m)
    (hchi : ∀ Z, chi Z = (S.specialFiberComponentWeight Z : ℤ) * (1 - gcomp Z)) :
    (gC : ℚ) = 1 + ∑ Z, (m Z : ℚ) *
      ((S.specialFiberComponentWeight Z : ℚ) * ((gcomp Z : ℚ) - 1) - (N Z Z : ℚ) / 2) := by
  have hker : ∀ Z, ∑ Y, (m Y : ℤ) * N Z Y = 0 :=
    sum_multiplicity_mul_intersectionMatrix_eq_zero_of_expansion S
      (fun Y => S.specialFiberComponentIdeal Y) (fun Y => S.specialFiberComponentToSpec Y)
      (fun Y => S.isProper_specialFiberComponentToSpec Y)
      (fun Y => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Y) N m
      (fun Y => S.isEffectiveCartierDivisor_specialFiberComponent Y) hexpand hdec
  have hEstep : ∀ (c : irreducibleComponents S.specialFiber → ℕ)
      (Z : irreducibleComponents S.specialFiber),
      E (c + Pi.single Z 1) = E c - (∑ Y, (c Y : ℤ) * N Z Y) + chi Z := by
    intro c Z
    rw [hrec.2 c Z, S.specialFiberIntersectionProduct_single Z c, hexpand]
  exact cast_eq_one_add_sum m N chi (fun Z => (S.specialFiberComponentWeight Z : ℤ)) gcomp gC
    (E m)
    (two_mul_eq_sum_of_recursion_of_ker chi N hsymm E hrec.1 hEstep m hker) hbasic hchi

end RegularProperModelSituation

end Stacks.Models

end
