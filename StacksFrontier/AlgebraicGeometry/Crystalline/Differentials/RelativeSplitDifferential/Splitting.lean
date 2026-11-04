module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamPerturbation
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BidegreeFiltration
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativePoincareSpecial
public import
  StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelTransition

/-!
# The bidegree projections and the splitting `d = d_rel + d_base` of the de Rham differential

Part of `StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSplitDifferential`, whose
module docstring explains the construction.  This file contains the projection onto one summand of
a direct sum decomposition (`Crystalline.DividedPowerPolynomial.conjugateSummandProjection`), the
bidegree projections `πᵢ` of the divided power forms of `P = B⟨x_w⟩`
(`Crystalline.DividedPowerPolynomial.formsBidegreeProjection`), the de Rham differential on the
image of a sector, the relative and base parts `d_rel` and `d_base` of the differential with the
splitting `d = d_rel + d_base`, the `B`-linearity of `d_rel`, `d_rel² = 0`, and the fact that the
relative homotopy preserves the coefficient degree.
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe uA uB uW uM

namespace Crystalline

namespace DividedPowerPolynomial

/-! ### Projecting onto one summand of a direct sum, through an equivalence -/

section DirectSumProjection

variable {R : Type*} [Semiring R] {iota : Type*} [DecidableEq iota] {M : iota → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] {X : Type*} [AddCommMonoid X] [Module R X]

/-- **The projection of `X` onto the summand `i` of a direct sum decomposition `e`**: read the
component, put it back, and read the result in `X` again.

This is stated for an arbitrary decomposition on purpose.  The decomposition it is used with
below, `Crystalline.DividedPowerPolynomial.dividedPowerPolynomialFormsEquiv`, has enormous types,
and every fact about the projection is a fact about an arbitrary direct sum: proving them here
means no unifier ever has to look inside the bidegree summands of `Ωⁿ_{P/A,δ'}`. -/
def conjugateSummandProjection (e : X ≃ₗ[R] DirectSum iota M) (i : iota) : X →ₗ[R] X :=
  e.symm.toLinearMap ∘ₗ
    (DirectSum.lof R iota M i ∘ₗ DirectSum.component R iota M i) ∘ₗ e.toLinearMap

/-- The summand projection, unfolded. -/
theorem conjugateSummandProjection_apply (e : X ≃ₗ[R] DirectSum iota M) (i : iota) (x : X) :
    conjugateSummandProjection e i x = e.symm (DirectSum.lof R iota M i (e x i)) :=
  rfl

/-- The decomposition of a summand projection is concentrated in that summand. -/
theorem apply_conjugateSummandProjection (e : X ≃ₗ[R] DirectSum iota M) (i : iota) (x : X) :
    e (conjugateSummandProjection e i x) = DirectSum.lof R iota M i (e x i) :=
  e.apply_symm_apply _

/-- **The summand projections on an element concentrated in one summand**: the projection onto
that summand is the identity and every other one is zero. -/
theorem conjugateSummandProjection_of_lof (e : X ≃ₗ[R] DirectSum iota M) (i j : iota) (x : X)
    (b : M j) (hx : e x = DirectSum.lof R iota M j b) :
    conjugateSummandProjection e i x = if i = j then x else 0 := by
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl, conjugateSummandProjection_apply, hx,
      DirectSum.lof_eq_of R iota M i b, DirectSum.of_eq_same, ← hx, e.symm_apply_apply]
  · rw [if_neg hij, conjugateSummandProjection_apply, hx,
      DirectSum.lof_eq_of R iota M j b, DirectSum.of_eq_of_ne j i b hij, map_zero, map_zero]

/-- A summand projection is an idempotent. -/
theorem conjugateSummandProjection_idem (e : X ≃ₗ[R] DirectSum iota M) (i : iota) (x : X) :
    conjugateSummandProjection e i (conjugateSummandProjection e i x) =
      conjugateSummandProjection e i x :=
  Eq.trans (conjugateSummandProjection_of_lof e i i (conjugateSummandProjection e i x) (e x i)
    (apply_conjugateSummandProjection e i x)) (if_pos rfl)

/-- Two different summand projections compose to zero. -/
theorem conjugateSummandProjection_comp_eq_zero (e : X ≃ₗ[R] DirectSum iota M) {i j : iota}
    (hij : i ≠ j) (x : X) :
    conjugateSummandProjection e i (conjugateSummandProjection e j x) = 0 :=
  Eq.trans (conjugateSummandProjection_of_lof e i j (conjugateSummandProjection e j x) (e x j)
    (apply_conjugateSummandProjection e j x)) (if_neg hij)

end DirectSumProjection

/-! ### The projections onto the bidegree summands -/

section Projections

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  [LinearOrder W]

/-- **The projection onto one summand of the bidegree decomposition of `Ωⁿ_{P/A,δ'}`**, read back
into the forms.  It is `P`-linear, the decomposition being `P`-linear. -/
def formsAntidiagonalProjection (n : ℕ) (kl : {ij : ℕ × ℕ // ij.1 + ij.2 = n}) :
    dividedPowerPolynomialForms A B W n →ₗ[setIndexedDividedPowerPolynomialAlgebra B W]
      dividedPowerPolynomialForms A B W n :=
  conjugateSummandProjection (dividedPowerPolynomialFormsEquiv A B W n) kl

/-- **The summand projection on a generator of the decomposition**: it keeps the generator whose
bidegree it reads and kills every other one. -/
theorem formsAntidiagonalProjection_decompositionGenerator (n : ℕ)
    (kl : {ij : ℕ × ℕ // ij.1 + ij.2 = n}) (i j : ℕ) (hij : i + j = n) (L : W →₀ ℕ)
    (J : Set.powersetCard W j)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    formsAntidiagonalProjection A B W n kl (decompositionGenerator A B W i j n hij L J omega) =
      if kl = ⟨(i, j), hij⟩ then decompositionGenerator A B W i j n hij L J omega else 0 :=
  conjugateSummandProjection_of_lof (dividedPowerPolynomialFormsEquiv A B W n) kl ⟨(i, j), hij⟩ _
    _ (dividedPowerPolynomialFormsEquiv_decompositionGenerator A B W i j n hij L J omega)

/-- The summand projection is an idempotent. -/
theorem formsAntidiagonalProjection_idem (n : ℕ) (kl : {ij : ℕ × ℕ // ij.1 + ij.2 = n})
    (x : dividedPowerPolynomialForms A B W n) :
    formsAntidiagonalProjection A B W n kl (formsAntidiagonalProjection A B W n kl x) =
      formsAntidiagonalProjection A B W n kl x :=
  conjugateSummandProjection_idem (dividedPowerPolynomialFormsEquiv A B W n) kl x

/-- Two different summand projections compose to zero. -/
theorem formsAntidiagonalProjection_comp_eq_zero (n : ℕ)
    {kl kl' : {ij : ℕ × ℕ // ij.1 + ij.2 = n}} (hne : kl ≠ kl')
    (x : dividedPowerPolynomialForms A B W n) :
    formsAntidiagonalProjection A B W n kl (formsAntidiagonalProjection A B W n kl' x) = 0 :=
  conjugateSummandProjection_comp_eq_zero (dividedPowerPolynomialFormsEquiv A B W n) hne x

/-- **The projection of `Ωⁿ_{P/A,δ'}` onto the forms with `i` coefficient differentials**, the
`πᵢ` of the proof of [Stacks, Lemma 60.21.2, Tag 07LD].  For `i > n` there is no such summand and
the projection is zero. -/
def formsBidegreeProjection (n i : ℕ) :
    dividedPowerPolynomialForms A B W n →ₗ[setIndexedDividedPowerPolynomialAlgebra B W]
      dividedPowerPolynomialForms A B W n :=
  if h : i ≤ n then
    formsAntidiagonalProjection A B W n ⟨(i, n - i), Nat.add_sub_cancel' h⟩
  else 0

/-- The coefficient-degree projection, in terms of the summand projection. -/
theorem formsBidegreeProjection_of_le {n i : ℕ} (hi : i ≤ n) :
    formsBidegreeProjection A B W n i =
      formsAntidiagonalProjection A B W n ⟨(i, n - i), Nat.add_sub_cancel' hi⟩ :=
  dif_pos hi

/-- Above the exterior degree there is no summand to project onto. -/
theorem formsBidegreeProjection_of_lt {n i : ℕ} (hi : n < i) :
    formsBidegreeProjection A B W n i = 0 :=
  dif_neg (Nat.not_le.2 hi)

/-- **The coefficient-degree projection on a generator of the decomposition.** -/
theorem formsBidegreeProjection_decompositionGenerator (n l i j : ℕ) (hij : i + j = n)
    (L : W →₀ ℕ) (J : Set.powersetCard W j)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    formsBidegreeProjection A B W n l (decompositionGenerator A B W i j n hij L J omega) =
      if l = i then decompositionGenerator A B W i j n hij L J omega else 0 := by
  by_cases hl : l ≤ n
  · rw [formsBidegreeProjection_of_le A B W hl,
      formsAntidiagonalProjection_decompositionGenerator]
    by_cases hli : l = i
    · subst hli
      obtain rfl : j = n - l := by omega
      rw [if_pos rfl, if_pos rfl]
    · refine Eq.trans (if_neg fun h ↦ hli ?_) (if_neg hli).symm
      exact congrArg (fun z : {ij : ℕ × ℕ // ij.1 + ij.2 = n} ↦ z.1.1) h
  · rw [formsBidegreeProjection_of_lt A B W (Nat.not_le.1 hl), LinearMap.zero_apply,
      if_neg fun h : l = i ↦ hl (by omega)]

/-- Two different coefficient-degree projections compose to zero. -/
theorem formsBidegreeProjection_comp_eq_zero (n : ℕ) {l i : ℕ} (hne : l ≠ i)
    (x : dividedPowerPolynomialForms A B W n) :
    formsBidegreeProjection A B W n l (formsBidegreeProjection A B W n i x) = 0 := by
  by_cases hl : l ≤ n
  · by_cases hi : i ≤ n
    · rw [formsBidegreeProjection_of_le A B W hl, formsBidegreeProjection_of_le A B W hi]
      refine formsAntidiagonalProjection_comp_eq_zero A B W n (fun h ↦ hne ?_) x
      exact congrArg (fun z : {ij : ℕ × ℕ // ij.1 + ij.2 = n} ↦ z.1.1) h
    · rw [formsBidegreeProjection_of_lt A B W (Nat.not_le.1 hi), LinearMap.zero_apply, map_zero]
  · rw [formsBidegreeProjection_of_lt A B W (Nat.not_le.1 hl), LinearMap.zero_apply]

/-- The coefficient-degree projection is an idempotent. -/
theorem formsBidegreeProjection_idem (n i : ℕ) (x : dividedPowerPolynomialForms A B W n) :
    formsBidegreeProjection A B W n i (formsBidegreeProjection A B W n i x) =
      formsBidegreeProjection A B W n i x := by
  by_cases hi : i ≤ n
  · rw [formsBidegreeProjection_of_le A B W hi, formsAntidiagonalProjection_idem]
  · rw [formsBidegreeProjection_of_lt A B W (Nat.not_le.1 hi)]
    simp only [LinearMap.zero_apply]

/-- **The coefficient-degree projections sum to the identity**, the index set of the bidegree
decomposition in exterior degree `n` being the antidiagonal of `n`.  This is the `hprojsum`
hypothesis of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`. -/
theorem formsBidegreeProjection_sum (n : ℕ) (x : dividedPowerPolynomialForms A B W n) :
    ∑ i ∈ Finset.range (n + 1), formsBidegreeProjection A B W n i x = x := by
  have key : (∑ i ∈ Finset.range (n + 1),
        (formsBidegreeProjection A B W n i).restrictScalars A) =
      (LinearMap.id : dividedPowerPolynomialForms A B W n →ₗ[A]
        dividedPowerPolynomialForms A B W n) := by
    refine dividedPowerPolynomialForms_linearMap_ext A B W n ?_
    intro i j hij L J omega
    rw [LinearMap.id_coe, id_eq, LinearMap.sum_apply]
    refine Eq.trans (Finset.sum_eq_single_of_mem i
      (Finset.mem_range.2 (by omega)) (fun l _ hl ↦ ?_)) ?_
    · exact Eq.trans (formsBidegreeProjection_decompositionGenerator A B W n l i j hij L J omega)
        (if_neg hl)
    · exact Eq.trans (formsBidegreeProjection_decompositionGenerator A B W n i i j hij L J omega)
        (if_pos rfl)
  simpa only [LinearMap.sum_apply, LinearMap.coe_restrictScalars, LinearMap.id_coe, id_eq]
    using DFunLike.congr_fun key x

end Projections

/-! ### The de Rham differential on the image of a sector -/

section Sector

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  [LinearOrder W]

/-- **A sector basis vector, read as a generator of the decomposition**, for an arbitrary total
multi-index: the subset is the image of the basis index in `W` and the exponent vector is `K`
lowered by one there. -/
theorem relativeSectorMapDeg_sectorExteriorBasis_eq_decompositionGenerator (K : W →₀ ℕ)
    (i j n : ℕ) (hn : i + j = n) (I : Set.powersetCard (K.support : Type uW) j)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    relativeSectorMapDeg A B W K i j n hn
        (sectorExteriorBasis B W K j I ⊗ₜ[(B : Type uB)] omega) =
      decompositionGenerator A B W i j n hn
        (K - finsetMultiIndex (sectorSubsetDown W K j I).val)
        (sectorSubsetDown W K j I) omega := by
  rw [relativeSectorMapDeg_apply, relativeSectorMap_sectorBasis]
  rfl

/-- **The image of a sector in bidegree `(i, j)` has coefficient degree `i`**: every other
coefficient-degree projection kills it.  A basis vector of the sector is a generator of the
decomposition in bidegree `(i, j)`, and the sector induction
`Crystalline.DividedPowerPolynomial.eq_zero_of_sectorExteriorBasis` extends that from the basis
vectors to the whole sector. -/
theorem formsBidegreeProjection_relativeSectorMapDeg_of_ne (K : W →₀ ℕ) (l i j n : ℕ)
    (hn : i + j = n) (hli : l ≠ i) (x : sectorModule A B W K i j) :
    formsBidegreeProjection A B W n l (relativeSectorMapDeg A B W K i j n hn x) = 0 := by
  refine eq_zero_of_sectorExteriorBasis A B W K i j n hn
    (formsBidegreeProjection A B W n l).toAddMonoidHom (fun I omega ↦ ?_) x
  show formsBidegreeProjection A B W n l (relativeSectorMapDeg A B W K i j n hn
    (sectorExteriorBasis B W K j I ⊗ₜ[(B : Type uB)] omega)) = 0
  rw [relativeSectorMapDeg_sectorExteriorBasis_eq_decompositionGenerator,
    formsBidegreeProjection_decompositionGenerator, if_neg hli]

/-- **The projection in coefficient degree `i` keeps the image of a sector in bidegree
`(i, j)`.** -/
theorem formsBidegreeProjection_relativeSectorMapDeg_self (K : W →₀ ℕ) (i j n : ℕ)
    (hn : i + j = n) (x : sectorModule A B W K i j) :
    formsBidegreeProjection A B W n i (relativeSectorMapDeg A B W K i j n hn x) =
      relativeSectorMapDeg A B W K i j n hn x := by
  have key : ∀ (I : Set.powersetCard (K.support : Type uW) j)
      (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i),
      ((formsBidegreeProjection A B W n i).toAddMonoidHom -
          AddMonoidHom.id (dividedPowerPolynomialForms A B W n))
        (relativeSectorMapDeg A B W K i j n hn
          (sectorExteriorBasis B W K j I ⊗ₜ[(B : Type uB)] omega)) = 0 := by
    intro I omega
    rw [AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero]
    show formsBidegreeProjection A B W n i (relativeSectorMapDeg A B W K i j n hn
      (sectorExteriorBasis B W K j I ⊗ₜ[(B : Type uB)] omega)) = _
    rw [relativeSectorMapDeg_sectorExteriorBasis_eq_decompositionGenerator,
      formsBidegreeProjection_decompositionGenerator, if_pos rfl]
  have h := eq_zero_of_sectorExteriorBasis A B W K i j n hn
    ((formsBidegreeProjection A B W n i).toAddMonoidHom -
      AddMonoidHom.id (dividedPowerPolynomialForms A B W n)) key x
  rw [AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero] at h
  exact h

end Sector

/-! ### The relative and the base part of the de Rham differential -/

section Differential

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  [LinearOrder W]

/-- **The de Rham differential raises the coefficient degree by `0` or by `1`.**

This is the one geometric input of the splitting, and it is the sector computation
`Crystalline.DividedPowerPolynomial.relativeSectorMapDeg_dividedPowerDeRham` read through the
bidegree decomposition: on a generator of bidegree `(i, j)` the differential is the sum of the
coefficient differential, landing in bidegree `(i + 1, j)`, and the Koszul differential, landing
in bidegree `(i, j + 1)`.  Neither has coefficient degree `l` for `l ∉ {i, i + 1}`. -/
theorem formsBidegreeProjection_dividedPowerDeRham_eq_zero (n : ℕ) {l i : ℕ} (hl : l ≠ i)
    (hl' : l ≠ i + 1) (x : dividedPowerPolynomialForms A B W n) :
    formsBidegreeProjection A B W (n + 1) l
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (formsBidegreeProjection A B W n i x)) = 0 := by
  have key : ((formsBidegreeProjection A B W (n + 1) l).restrictScalars A) ∘ₗ
      ((dividedPowerDeRhamLinearMap (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W) n) ∘ₗ
        ((formsBidegreeProjection A B W n i).restrictScalars A)) =
      (0 : dividedPowerPolynomialForms A B W n →ₗ[A]
        dividedPowerPolynomialForms A B W (n + 1)) := by
    refine dividedPowerPolynomialForms_linearMap_ext A B W n ?_
    intro i' j' hij' L J omega
    simp only [LinearMap.zero_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars]
    rw [formsBidegreeProjection_decompositionGenerator]
    by_cases hii : i = i'
    · subst hii
      rw [if_pos rfl, dividedPowerDeRhamLinearMap_apply,
        ← relativeSectorMapDeg_sectorExteriorBasis A B W i j' n hij' L J omega,
        relativeSectorMapDeg_dividedPowerDeRham, map_add,
        formsBidegreeProjection_relativeSectorMapDeg_of_ne A B W
          (L + finsetMultiIndex J.val) l (i + 1) j' (n + 1) (by omega) hl',
        formsBidegreeProjection_relativeSectorMapDeg_of_ne A B W
          (L + finsetMultiIndex J.val) l i (j' + 1) (n + 1) (by omega) hl, add_zero]
    · rw [if_neg hii, map_zero, map_zero]
  simpa only [LinearMap.zero_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    dividedPowerDeRhamLinearMap_apply] using DFunLike.congr_fun key x

/-- **The de Rham differential of a form of coefficient degree `i` is the sum of its components in
coefficient degrees `i` and `i + 1`**: the projections sum to the identity and the other summands
vanish. -/
theorem dividedPowerDeRham_formsBidegreeProjection_eq_add (n i : ℕ)
    (x : dividedPowerPolynomialForms A B W n) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
        (formsBidegreeProjection A B W n i x) =
      formsBidegreeProjection A B W (n + 1) i
          (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
            (formsBidegreeProjection A B W n i x)) +
        formsBidegreeProjection A B W (n + 1) (i + 1)
          (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
            (formsBidegreeProjection A B W n i x)) := by
  by_cases hi : i ≤ n
  · refine Eq.trans
      (formsBidegreeProjection_sum A B W (n + 1)
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (formsBidegreeProjection A B W n i x))).symm ?_
    refine Finset.sum_eq_add_of_mem i (i + 1) (Finset.mem_range.2 (by omega))
      (Finset.mem_range.2 (by omega)) (by omega) (fun c _ hc ↦ ?_)
    exact formsBidegreeProjection_dividedPowerDeRham_eq_zero A B W n hc.1 hc.2 x
  · rw [formsBidegreeProjection_of_lt A B W (Nat.not_le.1 hi), LinearMap.zero_apply,
      show dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
        (0 : dividedPowerPolynomialForms A B W n) = 0 from
          map_zero (dividedPowerDeRhamLinearMap (A := A)
            (setIndexedDividedPowerPolynomialDividedPowers B W) n),
      map_zero, map_zero, add_zero]

/-- **The relative part of the de Rham differential of `Ωⁿ_{P/A,δ'}`, read `A`-linearly**: the sum
over `i` of the component of `d` that preserves the coefficient degree `i`.
`Crystalline.DividedPowerPolynomial.formsRelDifferential` is the same map with its `B`-linearity
recorded, which is the form the perturbation argument needs. -/
def formsRelDifferentialAux (n : ℕ) :
    dividedPowerPolynomialForms A B W n →ₗ[A] dividedPowerPolynomialForms A B W (n + 1) :=
  ∑ i ∈ Finset.range (n + 1),
    ((formsBidegreeProjection A B W (n + 1) i).restrictScalars A) ∘ₗ
      ((dividedPowerDeRhamLinearMap (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W) n) ∘ₗ
        ((formsBidegreeProjection A B W n i).restrictScalars A))

/-- **The base part of the de Rham differential of `Ωⁿ_{P/A,δ'}`**: the sum over `i` of the
component of `d` that raises the coefficient degree from `i` to `i + 1`.  It is `A`-linear and no
more: the Leibniz correction `d_B b ∧ ω` of a base scalar `b` lies entirely in it. -/
def formsBaseDifferential (n : ℕ) :
    dividedPowerPolynomialForms A B W n →ₗ[A] dividedPowerPolynomialForms A B W (n + 1) :=
  ∑ i ∈ Finset.range (n + 1),
    ((formsBidegreeProjection A B W (n + 1) (i + 1)).restrictScalars A) ∘ₗ
      ((dividedPowerDeRhamLinearMap (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W) n) ∘ₗ
        ((formsBidegreeProjection A B W n i).restrictScalars A))

/-- The relative part, as a sum of projected differentials. -/
theorem formsRelDifferentialAux_apply (n : ℕ) (x : dividedPowerPolynomialForms A B W n) :
    formsRelDifferentialAux A B W n x =
      ∑ i ∈ Finset.range (n + 1), formsBidegreeProjection A B W (n + 1) i
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (formsBidegreeProjection A B W n i x)) := by
  simp only [formsRelDifferentialAux, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.coe_restrictScalars, dividedPowerDeRhamLinearMap_apply]

/-- The base part, as a sum of projected differentials. -/
theorem formsBaseDifferential_apply (n : ℕ) (x : dividedPowerPolynomialForms A B W n) :
    formsBaseDifferential A B W n x =
      ∑ i ∈ Finset.range (n + 1), formsBidegreeProjection A B W (n + 1) (i + 1)
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (formsBidegreeProjection A B W n i x)) := by
  simp only [formsBaseDifferential, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.coe_restrictScalars, dividedPowerDeRhamLinearMap_apply]

/-- **`d = d_rel + d_base`**: the de Rham differential of `Ωⁿ_{P/A,δ'}` is the sum of its
coefficient-degree-preserving and its coefficient-degree-raising part.  This is the `hsplit`
hypothesis of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`. -/
theorem dividedPowerDeRham_eq_formsRelDifferential_add (n : ℕ)
    (x : dividedPowerPolynomialForms A B W n) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n x =
      formsRelDifferentialAux A B W n x + formsBaseDifferential A B W n x := by
  rw [formsRelDifferentialAux_apply, formsBaseDifferential_apply, ← Finset.sum_add_distrib]
  refine Eq.trans (congrArg (dividedPowerDeRham
    (setIndexedDividedPowerPolynomialDividedPowers B W) n)
      (formsBidegreeProjection_sum A B W n x).symm) ?_
  refine Eq.trans ?_ (Finset.sum_congr rfl fun i _ ↦
    dividedPowerDeRham_formsBidegreeProjection_eq_add A B W n i x)
  simpa only [dividedPowerDeRhamLinearMap_apply] using
    map_sum (dividedPowerDeRhamLinearMap (A := A)
      (setIndexedDividedPowerPolynomialDividedPowers B W) n)
      (fun i ↦ formsBidegreeProjection A B W n i x) (Finset.range (n + 1))

/-- The de Rham differential of `0`, as an equation about the unbundled differential. -/
theorem dividedPowerDeRham_polynomial_zero (n : ℕ) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
      (0 : dividedPowerPolynomialForms A B W n) = 0 :=
  map_zero (dividedPowerDeRhamLinearMap (A := A)
    (setIndexedDividedPowerPolynomialDividedPowers B W) n)

/-- The de Rham differential is additive, as an equation about the unbundled differential. -/
theorem dividedPowerDeRham_polynomial_add (n : ℕ)
    (x y : dividedPowerPolynomialForms A B W n) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n (x + y) =
      dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n x +
        dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n y :=
  map_add (dividedPowerDeRhamLinearMap (A := A)
    (setIndexedDividedPowerPolynomialDividedPowers B W) n) x y

/-- Only the summand of index `i` survives in a sum of projected differentials of the
projection `πᵢ x`, by the orthogonality of the projections. -/
private theorem sum_formsBidegreeProjection_dividedPowerDeRham_projection (n i : ℕ) (c : ℕ → ℕ)
    (x : dividedPowerPolynomialForms A B W n) :
    ∑ m ∈ Finset.range (n + 1), formsBidegreeProjection A B W (n + 1) (c m)
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (formsBidegreeProjection A B W n m (formsBidegreeProjection A B W n i x))) =
      formsBidegreeProjection A B W (n + 1) (c i)
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (formsBidegreeProjection A B W n i x)) := by
  by_cases hi : i ≤ n
  · refine Eq.trans (Finset.sum_eq_single_of_mem i (Finset.mem_range.2 (by omega))
      (fun m _ hm ↦ ?_)) ?_
    · rw [formsBidegreeProjection_comp_eq_zero A B W n hm,
        dividedPowerDeRham_polynomial_zero, map_zero]
    · rw [formsBidegreeProjection_idem]
  · rw [formsBidegreeProjection_of_lt A B W (Nat.not_le.1 hi)]
    simp only [LinearMap.zero_apply, map_zero, dividedPowerDeRham_polynomial_zero,
      Finset.sum_const_zero]

/-- **On a form of coefficient degree `i` the relative part of the differential is the single
component `πᵢ ∘ d`**: the other summands of the sum defining it are killed by the orthogonality
of the projections. -/
theorem formsRelDifferentialAux_formsBidegreeProjection (n i : ℕ)
    (x : dividedPowerPolynomialForms A B W n) :
    formsRelDifferentialAux A B W n (formsBidegreeProjection A B W n i x) =
      formsBidegreeProjection A B W (n + 1) i
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (formsBidegreeProjection A B W n i x)) :=
  (formsRelDifferentialAux_apply A B W n _).trans
    (sum_formsBidegreeProjection_dividedPowerDeRham_projection A B W n i id x)

/-- **On a form of coefficient degree `i` the base part of the differential is the single component
`π_{i+1} ∘ d`.** -/
theorem formsBaseDifferential_formsBidegreeProjection (n i : ℕ)
    (x : dividedPowerPolynomialForms A B W n) :
    formsBaseDifferential A B W n (formsBidegreeProjection A B W n i x) =
      formsBidegreeProjection A B W (n + 1) (i + 1)
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (formsBidegreeProjection A B W n i x)) :=
  (formsBaseDifferential_apply A B W n _).trans
    (sum_formsBidegreeProjection_dividedPowerDeRham_projection A B W n i (· + 1) x)

/-- **The base part of the differential strictly raises the coefficient degree.**  This is the
`hprojbase` hypothesis of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`. -/
theorem formsBidegreeProjection_formsBaseDifferential_eq_zero (n : ℕ) {l i : ℕ} (hli : l ≤ i)
    (x : dividedPowerPolynomialForms A B W n) :
    formsBidegreeProjection A B W (n + 1) l
      (formsBaseDifferential A B W n (formsBidegreeProjection A B W n i x)) = 0 := by
  rw [formsBaseDifferential_formsBidegreeProjection,
    formsBidegreeProjection_comp_eq_zero A B W (n + 1) (show l ≠ i + 1 by omega)]

/-- **`d_rel² = 0`.**

This is the `hdrel` hypothesis of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`, and
it is `d² = 0` read in one coefficient degree: the coefficient-degree-`i` component of `d (d ω)`
for `ω` of coefficient degree `i` is `d_rel (d_rel ω)`, the other contribution coming from
`d_base ω`, which has coefficient degree `i + 1` and whose differential has no component in
degree `i`. -/
theorem formsRelDifferentialAux_formsRelDifferentialAux (n : ℕ)
    (x : dividedPowerPolynomialForms A B W n) :
    formsRelDifferentialAux A B W (n + 1) (formsRelDifferentialAux A B W n x) = 0 := by
  rw [formsRelDifferentialAux_apply A B W n x, map_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [formsRelDifferentialAux_formsBidegreeProjection]
  have hsplit := dividedPowerDeRham_formsBidegreeProjection_eq_add A B W n i x
  have hzero : formsBidegreeProjection A B W (n + 1 + 1) i
      (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (n + 1)
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (formsBidegreeProjection A B W n i x))) = 0 := by
    rw [dividedPowerDeRham_dividedPowerDeRham, map_zero]
  have hgoal : formsBidegreeProjection A B W (n + 1 + 1) i
      (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) (n + 1)
        (formsBidegreeProjection A B W (n + 1) i
            (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
              (formsBidegreeProjection A B W n i x)) +
          formsBidegreeProjection A B W (n + 1) (i + 1)
            (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
              (formsBidegreeProjection A B W n i x)))) = 0 := by
    rw [← hsplit]
    exact hzero
  rw [dividedPowerDeRham_polynomial_add, map_add,
    formsBidegreeProjection_dividedPowerDeRham_eq_zero A B W (n + 1)
      (show i ≠ i + 1 by omega) (show i ≠ i + 1 + 1 by omega), add_zero] at hgoal
  exact hgoal

/-! ### The relative part is linear over the base -/

/-- Scaling a generator by a base element scales its coefficient form: the generator is
`B`-linear in its coefficient form, the sector map being `B`-linear. -/
theorem smul_decompositionGenerator (i j n : ℕ) (hij : i + j = n) (b : (B : Type uB))
    (L : W →₀ ℕ) (J : Set.powersetCard W j)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    b • decompositionGenerator A B W i j n hij L J omega =
      decompositionGenerator A B W i j n hij L J (b • omega) := by
  rw [← relativeSectorMapDeg_sectorExteriorBasis A B W i j n hij L J omega,
    ← relativeSectorMapDeg_sectorExteriorBasis A B W i j n hij L J (b • omega),
    TensorProduct.tmul_smul, map_smul]

/-- **The relative part of the differential on a generator of the decomposition**: it is the
Koszul direction of the generator's own sector `K = L + 1_J`, which is the term of
`Crystalline.DividedPowerPolynomial.relativeSectorMapDeg_dividedPowerDeRham` that keeps the
coefficient degree. -/
theorem formsRelDifferentialAux_decompositionGenerator (i j n : ℕ) (hij : i + j = n)
    (L : W →₀ ℕ) (J : Set.powersetCard W j)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    formsRelDifferentialAux A B W n (decompositionGenerator A B W i j n hij L J omega) =
      relativeSectorMapDeg A B W (L + finsetMultiIndex J.val) i (j + 1) (n + 1) (by omega)
        (relativeSectorKoszulDifferential A B W (L + finsetMultiIndex J.val) i j
          (sectorExteriorBasis B W (L + finsetMultiIndex J.val) j
              (sectorLiftSubset W (L + finsetMultiIndex J.val) j J
                (subset_support_add_finsetMultiIndex J.val L)) ⊗ₜ[(B : Type uB)] omega)) := by
  rw [formsRelDifferentialAux_apply]
  refine Eq.trans (Finset.sum_eq_single_of_mem i (Finset.mem_range.2 (by omega))
    (fun m _ hm ↦ ?_)) ?_
  · rw [formsBidegreeProjection_decompositionGenerator, if_neg hm,
      dividedPowerDeRham_polynomial_zero, map_zero]
  · rw [formsBidegreeProjection_decompositionGenerator, if_pos rfl,
      ← relativeSectorMapDeg_sectorExteriorBasis A B W i j n hij L J omega,
      relativeSectorMapDeg_dividedPowerDeRham, map_add,
      formsBidegreeProjection_relativeSectorMapDeg_of_ne A B W
        (L + finsetMultiIndex J.val) i (i + 1) j (n + 1) (by omega) (by omega),
      formsBidegreeProjection_relativeSectorMapDeg_self, zero_add]

/-- **The relative part of the differential is linear over the base ring `B`.**

For `b ∈ B` the Leibniz correction `d_B b ∧ ω` carries one coefficient differential more than
`ω`, so the projection that defines the relative part deletes it.  Concretely, on a generator the
relative part is the Koszul direction of its sector, which is `B`-linear in the coefficient form.

It is **not** `P`-linear: for a variable `x_w` the correction `d x_w ∧ ω` has the same coefficient
degree as `ω` and is kept, which is why the base part is the one that must stay merely
additive. -/
theorem formsRelDifferentialAux_smul (n : ℕ) (b : (B : Type uB))
    (x : dividedPowerPolynomialForms A B W n) :
    formsRelDifferentialAux A B W n (b • x) = b • formsRelDifferentialAux A B W n x := by
  have key : (formsRelDifferentialAux A B W n) ∘ₗ
        ((LinearMap.lsmul (setIndexedDividedPowerPolynomialAlgebra B W)
            (dividedPowerPolynomialForms A B W n)
            (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W)
              b)).restrictScalars A) =
      ((LinearMap.lsmul (setIndexedDividedPowerPolynomialAlgebra B W)
            (dividedPowerPolynomialForms A B W (n + 1))
            (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W)
              b)).restrictScalars A) ∘ₗ (formsRelDifferentialAux A B W n) := by
    refine dividedPowerPolynomialForms_linearMap_ext A B W n ?_
    intro i j hij L J omega
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]
    rw [algebraMap_smul, algebraMap_smul, smul_decompositionGenerator,
      formsRelDifferentialAux_decompositionGenerator,
      formsRelDifferentialAux_decompositionGenerator, TensorProduct.tmul_smul,
      map_smul, map_smul]
  simpa only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearMap.lsmul_apply,
    algebraMap_smul] using DFunLike.congr_fun key x

/-- **The relative part of the de Rham differential of `Ωⁿ_{P/A,δ'}`, as a `B`-linear map.**

This is the shape the perturbation argument of [Stacks, Lemma 60.21.2, Tag 07LD] consumes: the
`drel` of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` is linear over the base, which
is what lets `1_M ⊗ d_rel` exist on `M ⊗̂ Ω^*` for a module `M` with a connection.  The underlying
map is `Crystalline.DividedPowerPolynomial.formsRelDifferentialAux`; nothing is added here beyond
the record of its linearity. -/
def formsRelDifferential (n : ℕ) :
    dividedPowerPolynomialForms A B W n →ₗ[(B : Type uB)]
      dividedPowerPolynomialForms A B W (n + 1) where
  toFun := formsRelDifferentialAux A B W n
  map_add' := map_add (formsRelDifferentialAux A B W n)
  map_smul' b x := formsRelDifferentialAux_smul A B W n b x

/-- The `B`-linear relative differential is the map it was built from. -/
theorem formsRelDifferential_apply (n : ℕ) (x : dividedPowerPolynomialForms A B W n) :
    formsRelDifferential A B W n x = formsRelDifferentialAux A B W n x :=
  rfl

/-- **`d = d_rel + d_base` with the relative part `B`-linear**, the splitting in the shape the
perturbation argument needs. -/
theorem dividedPowerDeRham_eq_formsRelDifferential_add_formsBaseDifferential (n : ℕ)
    (x : dividedPowerPolynomialForms A B W n) :
    dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n x =
      formsRelDifferential A B W n x + formsBaseDifferential A B W n x :=
  dividedPowerDeRham_eq_formsRelDifferential_add A B W n x

/-- **`d_rel² = 0` for the `B`-linear relative differential.** -/
theorem formsRelDifferential_formsRelDifferential (n : ℕ)
    (x : dividedPowerPolynomialForms A B W n) :
    formsRelDifferential A B W (n + 1) (formsRelDifferential A B W n x) = 0 :=
  formsRelDifferentialAux_formsRelDifferentialAux A B W n x

/-- **`d_rel² = 0`, as a composition of `B`-linear maps.** -/
theorem formsRelDifferential_comp_formsRelDifferential (n : ℕ) :
    (formsRelDifferential A B W (n + 1)).comp (formsRelDifferential A B W n) = 0 :=
  LinearMap.ext fun x ↦ formsRelDifferential_formsRelDifferential A B W n x

/-! ### The relative homotopy preserves the coefficient degree -/

/-- **The coefficient-degree projection of the relative homotopy of a generator.**  Either the
generator carries no variable differential, and then the homotopy kills it, or it is the sector
map of its own sector in bidegree `(i, j + 1)` and the homotopy carries it to bidegree `(i, j)`:
the coefficient degree is untouched in both cases. -/
theorem formsBidegreeProjection_relativeFormsHomotopy_decompositionGenerator (n i j : ℕ)
    (hij : i + j = n + 1) (L : W →₀ ℕ) (J : Set.powersetCard W j)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) (l : ℕ) :
    formsBidegreeProjection A B W n l (relativeFormsHomotopy A B W n
        (decompositionGenerator A B W i j (n + 1) hij L J omega)) =
      if l = i then relativeFormsHomotopy A B W n
        (decompositionGenerator A B W i j (n + 1) hij L J omega) else 0 := by
  cases j with
  | zero =>
    obtain rfl : i = n + 1 := by omega
    rw [relativeFormsHomotopy_decompositionGenerator_zero A B W n hij L J omega, map_zero]
    by_cases h : l = n + 1
    · rw [if_pos h]
    · rw [if_neg h]
  | succ j =>
    obtain rfl : i + j = n := by omega
    rw [← relativeSectorMapDeg_sectorExteriorBasis A B W i (j + 1) (i + j + 1) hij L J omega,
      relativeFormsHomotopy_relativeSectorMapDeg A B W (L + finsetMultiIndex J.val) i j
        (i + j) rfl]
    by_cases h : l = i
    · subst h
      rw [if_pos rfl, formsBidegreeProjection_relativeSectorMapDeg_self]
    · rw [if_neg h, formsBidegreeProjection_relativeSectorMapDeg_of_ne A B W
        (L + finsetMultiIndex J.val) l i j (i + j) rfl h]

/-- **The relative homotopy `h` preserves the coefficient degree**: it commutes with every
coefficient-degree projection.  This is the `hprojhhat` hypothesis of
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`. -/
theorem relativeFormsHomotopy_formsBidegreeProjection (n i : ℕ)
    (x : dividedPowerPolynomialForms A B W (n + 1)) :
    relativeFormsHomotopy A B W n (formsBidegreeProjection A B W (n + 1) i x) =
      formsBidegreeProjection A B W n i (relativeFormsHomotopy A B W n x) := by
  have key : (relativeFormsHomotopy A B W n) ∘ₗ
        ((formsBidegreeProjection A B W (n + 1) i).restrictScalars A) =
      ((formsBidegreeProjection A B W n i).restrictScalars A) ∘ₗ
        (relativeFormsHomotopy A B W n) := by
    refine dividedPowerPolynomialForms_linearMap_ext A B W (n + 1) ?_
    intro i' j' hij' L J omega
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars]
    rw [formsBidegreeProjection_decompositionGenerator,
      formsBidegreeProjection_relativeFormsHomotopy_decompositionGenerator]
    by_cases hii : i = i'
    · rw [if_pos hii, if_pos hii]
    · rw [if_neg hii, if_neg hii, map_zero]
  simpa only [LinearMap.comp_apply, LinearMap.coe_restrictScalars] using
    DFunLike.congr_fun key x

end Differential

end DividedPowerPolynomial

end Crystalline

end
