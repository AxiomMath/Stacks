module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjShiftedSectionModule
public import StacksFrontier.AlgebraicGeometry.ProjSaturation.Basic

/-!
# The comparison `M_n ⟶ Γ(Proj 𝒮, M(n)~)` in all large degrees

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring generated in degree one over `𝒮 0`, let
`M = ⨁_{n ∈ ℤ} 𝒨 n` be a graded `S`-module and `X = Proj 𝒮`. Equation 01MR provides, in every
degree `n`, a canonical map

`𝒨 n ⟶ Γ(X, M(n)~)`

(`Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections`). Tag 0AG7 asserts that
these maps are isomorphisms for all sufficiently large `n`, when `𝒮 0` is Noetherian and `M` is
a finite `S`-module.

## Main results

* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.smul_eq_zero_of_irrelevant_pow_annihilates`:
  in a ring generated in degree one, an element killed by the `N`-th power of the irrelevant
  ideal is killed by every homogeneous scalar of degree at least `N`.
* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.exists_bijective_degreeNToGlobalSections`:
  **the conclusion of Tag 0AG7**, that the comparison maps are bijective in all large degrees,
  deduced from homogeneous generating data for the kernel and the cokernel.

## Implementation notes

The target is the associated sheaf `M(n)~` of the shift, not the twist `M̃(n)` of the associated
sheaf; the two agree canonically under the degree-one hypothesis of the source (Tag 01MT), and
`degreeNToGlobalSections` is the displayed map of Equation 01MR that Tag 01MT transports.

**This statement is weaker than the source.** The source hypotheses "`𝒮 0` Noetherian" and "`M`
finite" are not assumed; what is assumed instead is the *output* that the source extracts from
them through Tags 0AG5, 0AG6 and 01M7, namely homogeneous generating data for the kernel and for
the cokernel of the comparison:

* `x : Fin ck → M` with degree offsets `dx` generate the kernel degreewise (`hxgen`), and each
  `x j` is annihilated by a power of the irrelevant ideal (`hxtors`);
* `y k : Γ(X, M(dy k)~)` generate the cokernel degreewise (`hygen`), and a power of the
  irrelevant ideal pushes each `y k` into the image of the comparison (`hytors`).

Both generation hypotheses are statements about *every* degree `n` at or above the generator
degrees; neither mentions largeness of `n`, while the conclusion is a uniform degree bound.

Degrees of homogeneous scalars are recorded as `(n - dx j).toNat`, which is the honest degree
once `dx j ≤ n`; the resulting reindexing of a section group along an equality of degrees is
`ofDegreeEq`.

## References

* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
-/

@[expose] public noncomputable section

open DirectSum
open Stacks.AlgebraicGeometry.ProjShiftedSections
  (shiftedSectionsComponent degreeNToGlobalSections homogeneousScalarGlobalSections)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjLargeDegreeSections

universe u v w t

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- In a graded ring generated in degree one over `𝒮 0`, an element annihilated by the `N`-th
power of the irrelevant ideal is annihilated by every homogeneous scalar of degree at least
`N`. -/
theorem smul_eq_zero_of_irrelevant_pow_annihilates
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) {N : ℕ} {x : M}
    (hx : ∀ a ∈ (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ N, a • x = 0)
    {i : ℕ} (hi : N ≤ i) {a : S} (ha : a ∈ 𝒮 i) : a • x = 0 :=
  hx a (Ideal.pow_le_pow_right hi
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_irrelevant_pow_of_mem 𝒮 hgen i ha))

/-- Reindexing a group of shifted global sections along an equality of degrees. -/
def ofDegreeEq {p q : ℤ} (h : p = q) (s : shiftedSectionsComponent 𝒮 𝒨 p) :
    shiftedSectionsComponent 𝒮 𝒨 q :=
  h ▸ s

omit [Decomposition 𝒨] in
/-- Reindexing commutes with the canonical map from the homogeneous elements. -/
theorem ofDegreeEq_degreeNToGlobalSections {p q : ℤ} (h : p = q) (m : 𝒨 p) :
    ofDegreeEq 𝒮 𝒨 h (degreeNToGlobalSections 𝒮 𝒨 p m)
      = degreeNToGlobalSections 𝒮 𝒨 q (h ▸ m) := by
  subst h
  rfl

omit [Decomposition 𝒨] in
/-- The comparison maps are bijective in all large degrees, with the finiteness input of the
source replaced by homogeneous generating data for the kernel and the cokernel of the comparison.

In every degree `n` the canonical map `𝒨 n ⟶ Γ(Proj 𝒮, M(n)~)` of Equation 01MR is
`degreeNToGlobalSections`. Assume `S` is generated in degree one over `𝒮 0` and:

* the kernel is generated degreewise by `x : Fin ck → M` placed in degrees `dx`, and a power of
  the irrelevant ideal annihilates every `x j`;
* the cokernel is generated degreewise by sections `y k` of `M(dy k)~`, and a power of the
  irrelevant ideal carries every `y k` into the image of the comparison.

Then the comparison is bijective in every sufficiently large degree. The statement does not
assume that `𝒨` is a decomposition of `M`. -/
@[stacks 0AG7 "bijectivity in all large degrees, from homogeneous generators of the kernel and \
of the cokernel annihilated, respectively carried into the image, by a power of the irrelevant \
ideal"]
theorem exists_bijective_degreeNToGlobalSections
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤)
    {ck : ℕ} (x : Fin ck → M) (dx : Fin ck → ℤ) (Nx : Fin ck → ℕ)
    (hxtors : ∀ j, ∀ a ∈ (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ Nx j, a • x j = 0)
    (hxgen : ∀ n : ℤ, (∀ j, dx j ≤ n) → ∀ m : 𝒨 n,
      degreeNToGlobalSections 𝒮 𝒨 n m = 0 →
        ∃ a : (j : Fin ck) → 𝒮 (n - dx j).toNat, (m : M) = ∑ j, (a j : S) • x j)
    {cq : ℕ} (dy : Fin cq → ℤ) (Ny : Fin cq → ℕ)
    (y : (k : Fin cq) → shiftedSectionsComponent 𝒮 𝒨 (dy k))
    (hytors : ∀ (k : Fin cq) (i : ℕ) (a : 𝒮 i),
      (a : S) ∈ (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ Ny k →
        ∃ m : 𝒨 ((i : ℤ) + dy k),
          homogeneousScalarGlobalSections 𝒮 𝒨 i (dy k) a (y k)
            = degreeNToGlobalSections 𝒮 𝒨 ((i : ℤ) + dy k) m)
    (hygen : ∀ (n : ℤ) (hn : ∀ k, dy k ≤ n) (s : shiftedSectionsComponent 𝒮 𝒨 n),
      ∃ (m : 𝒨 n) (a : (k : Fin cq) → 𝒮 (n - dy k).toNat),
        s = degreeNToGlobalSections 𝒮 𝒨 n m +
          ∑ k, ofDegreeEq 𝒮 𝒨 (show (((n - dy k).toNat : ℤ) + dy k) = n by
              have := hn k; omega)
            (homogeneousScalarGlobalSections 𝒮 𝒨 ((n - dy k).toNat) (dy k) (a k) (y k))) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → Function.Bijective (degreeNToGlobalSections 𝒮 𝒨 n) := by
  classical
  refine ⟨(∑ j, (|dx j| + (Nx j : ℤ))) + ∑ k, (|dy k| + (Ny k : ℤ)), fun n hn ↦ ?_⟩
  have hle {ι : Type} [Fintype ι] (d : ι → ℤ) (N : ι → ℕ) (j : ι) :
      (N j : ℤ) + d j ≤ ∑ i, (|d i| + (N i : ℤ)) := by
    have := Finset.single_le_sum (f := fun i ↦ |d i| + (N i : ℤ)) (fun _ _ ↦ by positivity)
      (Finset.mem_univ j)
    linarith [le_abs_self (d j)]
  have hxle (j) : (Nx j : ℤ) + dx j ≤ n := by
    linarith [hle dx Nx j, show 0 ≤ ∑ k, (|dy k| + (Ny k : ℤ)) by positivity]
  have hyle (k) : (Ny k : ℤ) + dy k ≤ n := by
    linarith [hle dy Ny k, show 0 ≤ ∑ j, (|dx j| + (Nx j : ℤ)) by positivity]
  have hxdeg (j) : dx j ≤ n := by have := hxle j; omega
  have hydeg (k) : dy k ≤ n := by have := hyle k; omega
  constructor
  · rw [injective_iff_map_eq_zero]
    intro m hm
    obtain ⟨a, ha⟩ := hxgen n hxdeg m hm
    refine Subtype.ext ?_
    rw [ZeroMemClass.coe_zero, ha]
    exact Finset.sum_eq_zero fun j _ ↦ smul_eq_zero_of_irrelevant_pow_annihilates 𝒮 hgen
      (hxtors j) (by have := hxle j; omega) (a j).2
  · intro s
    obtain ⟨m, a, hs⟩ := hygen n hydeg s
    have hk (k) : ((n - dy k).toNat : ℤ) + dy k = n := by have := hydeg k; omega
    have hterm (k : Fin cq) : ∃ m' : 𝒨 n,
        ofDegreeEq 𝒮 𝒨 (hk k)
            (homogeneousScalarGlobalSections 𝒮 𝒨 ((n - dy k).toNat) (dy k) (a k) (y k))
          = degreeNToGlobalSections 𝒮 𝒨 n m' := by
      obtain ⟨m', hm'⟩ := hytors k ((n - dy k).toNat) (a k) <|
        Ideal.pow_le_pow_right (by have := hyle k; omega)
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_irrelevant_pow_of_mem 𝒮 hgen _ (a k).2)
      exact ⟨hk k ▸ m', by
        rw [hm', ofDegreeEq_degreeNToGlobalSections]⟩
    choose m' hm' using hterm
    refine ⟨m + ∑ k, m' k, ?_⟩
    rw [map_add, map_sum, hs]
    exact congrArg _ (Finset.sum_congr rfl fun k _ ↦ hm' k).symm

end Stacks.AlgebraicGeometry.ProjLargeDegreeSections

end
