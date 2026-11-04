module

public import StacksFrontier.RingTheory.Fitting.GlobalEquations
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteLocallyFreeOfRank
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded pieces of the two filtrations over a ring that is not local

Let `M` be a finite module over a commutative ring `R`, not necessarily local, whose Fitting
ideals are cut out by nonzerodivisors `e_j` through `Fit_k(M) = ∏_{j > k} (e_j)^{j-k}`. Both graded
pieces of the two filtrations of Stacks tag 0ESU are then **finite locally free** of rank `i` over
`R ⧸ (e_i)`, which is what the source asserts ("the quotients are finite locally free of rank `i`
on `D_i`"). Over a local ring they are free
(`Stacks.FittingFiltration.exists_divisors_and_filtrations_of_finite`).

## Main results

* `Stacks.FittingFiltration.span_singleton_equation_eq_of_prod`: **the local equations are unique
  up to units.** Two families of nonzerodivisors, each cutting out the Fitting ideals by the
  product formula `Fit_k = ∏_{j > k} (e_j)^{j-k}`, generate the same ideals. The ring is
  arbitrary.
* `Stacks.FittingFiltration.nonempty_gradedQuot_equiv_of_prod`: the local form of the graded
  pieces with the equations **supplied** rather than produced.
* `Stacks.FittingFiltration.gradedQuotLocalizedEquiv`: the graded piece of a pair of submodules
  commutes with localization.
* `Stacks.FittingFiltration.fittingIdeal_gradedQuot_incr` and
  `Stacks.FittingFiltration.fittingIdeal_gradedQuot_decr`: over an arbitrary ring the `k`-th
  Fitting ideal of the graded piece in degree `i + 1` is `(e_{i+1})^{i+1-k}`; in particular the
  `i`-th is `(e_{i+1})` and the `(i+1)`-st is the unit ideal.
* `Stacks.FittingFiltration.isFiniteLocallyFreeOfRank_gradedQuot_incr` and
  `Stacks.FittingFiltration.isFiniteLocallyFreeOfRank_gradedQuot_decr`: **the graded pieces over a
  ring that need not be local.** Both are finite locally free of rank `i + 1` over
  `R ⧸ (e_{i+1})`.

* `Stacks.FittingFiltration.incr_zero_eq_bot` and `Stacks.FittingFiltration.decr_one_eq_top`: the
  two anchors `F^0 = 0` and `F_1 = M` of the source's filtrations, over an arbitrary ring.
* `Stacks.FittingFiltration.finite_decr`: **every step of the decreasing filtration is a finite
  module**, with no hypothesis on the ring, for a finitely presented `M`.
* `Stacks.FittingFiltration.isFiniteLocallyFreeOfRank_gradedQuot_decr_of_finitePresentation`: the
  decreasing graded clause for a finitely presented module, where the finiteness of the step is
  supplied rather than requested.
* `Stacks.FittingFiltration.isTorsionBySet_gradedQuot_decr_of_eq` and
  `Stacks.FittingFiltration.isFiniteLocallyFreeOfRank_gradedQuot_decr_of_eq`: the same two
  statements for submodules merely *equal* to the two filtration steps.

The two filtrations are not symmetric in one respect. A step of the increasing filtration is the
image of `M` under multiplication by a product of the equations, hence finite
(`Stacks.FittingFiltration.finite_incr`); a step of the decreasing filtration is a *kernel*, and
over a ring that is not Noetherian a kernel inside a finite module need not be finitely generated
for that reason alone. `Stacks.FittingFiltration.isFiniteLocallyFreeOfRank_gradedQuot_decr` is
accordingly stated for a finite step, and `Stacks.FittingFiltration.finite_decr` proves the step
finite whenever `M` is finitely presented.

## Implementation notes

The `R ⧸ (e_{i+1})`-module structure on a graded piece is not an instance: it comes from the
annihilation statements `Stacks.FittingFiltration.isTorsionBySet_gradedQuot_incr` and
`Stacks.FittingFiltration.isTorsionBySet_gradedQuot_decr` through
`Module.IsTorsionBySet.module`, and so appears as a `letI` in the statements below.

## References

* [Stacks Project, Tag 0ESU](https://stacks.math.columbia.edu/tag/0ESU)
* [Stacks Project, Tag 07ZD](https://stacks.math.columbia.edu/tag/07ZD)
-/

@[expose] public noncomputable section

universe u v

open scoped TensorProduct

namespace Stacks.FittingFiltration

variable {R : Type u} [CommRing R]

/-! ### Associated ring elements define the same filtration step

Both filtrations are defined from a product of the local equations — the increasing one as the
image of multiplication by it, the decreasing one as the kernel — and both of those depend on the
product only through the ideal it generates.
-/

section Associates

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Two ring elements generating the same ideal have the same multiples in every module. -/
theorem range_lsmul_eq_of_span_eq {a b : R} (h : Ideal.span {a} = Ideal.span {b}) :
    LinearMap.range (LinearMap.lsmul R M a) = LinearMap.range (LinearMap.lsmul R M b) := by
  have key : ∀ x y : R, Ideal.span ({x} : Set R) ≤ Ideal.span {y} →
      LinearMap.range (LinearMap.lsmul R M x) ≤ LinearMap.range (LinearMap.lsmul R M y) := by
    intro x y hxy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hxy (Ideal.mem_span_singleton_self x))
    rintro - ⟨z, rfl⟩
    refine ⟨c • z, ?_⟩
    simp only [LinearMap.lsmul_apply, ← hc, mul_smul]
    exact smul_comm y c z
  exact le_antisymm (key a b h.le) (key b a h.ge)

/-- Two ring elements generating the same ideal kill the same elements of every module. -/
theorem ker_lsmul_eq_of_span_eq {a b : R} (h : Ideal.span {a} = Ideal.span {b}) :
    LinearMap.ker (LinearMap.lsmul R M a) = LinearMap.ker (LinearMap.lsmul R M b) := by
  have key : ∀ x y : R, Ideal.span ({x} : Set R) ≤ Ideal.span {y} →
      LinearMap.ker (LinearMap.lsmul R M y) ≤ LinearMap.ker (LinearMap.lsmul R M x) := by
    intro x y hxy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hxy (Ideal.mem_span_singleton_self x))
    intro z hz
    simp only [LinearMap.mem_ker, LinearMap.lsmul_apply] at hz ⊢
    rw [← hc, mul_smul, hz, smul_zero]
  exact le_antisymm (key b a h.ge) (key a b h.le)

end Associates

/-! ### The local equations are unique up to units

The product formula `Fit_k = ∏_{j > k} (e_j)^{j-k}` determines each `(e_j)`, by the identity
`Fit_k · Fit_{k+2} = Fit_{k+1}² · (e_{k+1})` of
`Stacks.FittingFiltration.fittingIdeal_mul_fittingIdeal_of_prod` and the cancellation of the
nonzerodivisor generating `Fit_{k+1}`.
-/

/-- The weighted product of principal ideals is principal, generated by the weighted product of
the generators. -/
theorem prod_span_pow_eq_span_prod (e : ℕ → R) (N k : ℕ) :
    (∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k))
      = Ideal.span {∏ j ∈ Finset.Icc (k + 1) N, e j ^ (j - k)} := by
  rw [← Ideal.prod_span_singleton]
  exact Finset.prod_congr rfl fun j _ => Ideal.span_singleton_pow (e j) (j - k)

/-- A nonzerodivisor cancels from an equality of principal ideals. -/
theorem span_singleton_eq_of_mul_span_singleton_eq {c a b : R} (hc : c ∈ nonZeroDivisors R)
    (h : Ideal.span {c * a} = Ideal.span {c * b}) : Ideal.span ({a} : Set R) = Ideal.span {b} := by
  have hreg : IsRegular c := isRegular_iff_mem_nonZeroDivisors.mpr hc
  have key : ∀ x y : R, Ideal.span ({c * x} : Set R) ≤ Ideal.span {c * y} →
      Ideal.span ({x} : Set R) ≤ Ideal.span {y} := by
    intro x y hxy
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (hxy (Ideal.mem_span_singleton_self (c * x)))
    have hx : x = t * y := hreg.left (by linear_combination -ht)
    exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton'.mpr ⟨t, hx.symm⟩)
  exact le_antisymm (key a b h.le) (key b a h.ge)

/-- **The local equations of the divisors are unique up to units.** If two families `e` and `e'`
of nonzerodivisors, each a unit past its own bound, both cut out the Fitting ideals of a finite
module by the product formula `Fit_k = ∏_{j > k} (e_j)^{j-k}`, then they generate the same ideals,
so they cut out the same divisors `D_j`. -/
theorem span_singleton_equation_eq_of_prod {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {N N' : ℕ} {e e' : ℕ → R}
    (hmem : ∀ j, e j ∈ nonZeroDivisors R) (hunit : ∀ j, N < j → IsUnit (e j))
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k))
    (hunit' : ∀ j, N' < j → IsUnit (e' j))
    (hprod' : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N', Ideal.span {e' j} ^ (j - k)) (k : ℕ) :
    Ideal.span ({e (k + 1)} : Set R) = Ideal.span {e' (k + 1)} := by
  set c : R := ∏ j ∈ Finset.Icc (k + 2) N, e j ^ (j - (k + 1)) with hc
  have hcmem : c ∈ nonZeroDivisors R :=
    prod_mem fun j _ => pow_mem (hmem j) (j - (k + 1))
  have hfit1 : fittingIdeal (R := R) (M := M) ((k + 1 : ℕ) : ℤ) = Ideal.span {c} := by
    rw [hprod (k + 1), hc]
    exact prod_span_pow_eq_span_prod e N (k + 1)
  have key := (fittingIdeal_mul_fittingIdeal_of_prod (fun hj => hunit _ hj) hprod k).symm.trans
    (fittingIdeal_mul_fittingIdeal_of_prod (fun hj => hunit' _ hj) hprod' k)
  rw [hfit1] at key
  simp only [Ideal.span_singleton_mul_span_singleton] at key
  exact span_singleton_eq_of_mul_span_singleton_eq (mul_mem hcmem hcmem) key

/-- The local equations of two families cutting out the Fitting ideals generate the same ideals. -/
private theorem span_eq_of_prod (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {N N' : ℕ} {e e' : ℕ → R} (hmem : ∀ j, e j ∈ nonZeroDivisors R)
    (hunit : ∀ j, N < j → IsUnit (e j))
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k))
    (hunit' : ∀ j, N' < j → IsUnit (e' j))
    (hprod' : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N', Ideal.span {e' j} ^ (j - k)) :
    ∀ j, 1 ≤ j → Ideal.span ({e j} : Set R) = Ideal.span {e' j} := by
  intro j hj
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact span_singleton_equation_eq_of_prod hmem hunit hprod hunit' hprod' k

/-! ### The local form with the equations supplied -/

/-- A tail product of the local equations is unchanged by enlarging the range past the last
divisor, where the equations are units. -/
private theorem prod_span_extend (e : ℕ → R) {N : ℕ} (hunit : ∀ j, N < j → IsUnit (e j))
    (i T : ℕ) (hNT : N ≤ T) :
    (∏ j ∈ Finset.Icc i N, Ideal.span ({e j} : Set R))
      = ∏ j ∈ Finset.Icc i T, Ideal.span {e j} := by
  refine Finset.prod_subset (fun j hj => ?_) fun j hj hj' => ?_
  · simp only [Finset.mem_Icc] at hj ⊢
    omega
  · simp only [Finset.mem_Icc] at hj hj'
    exact (Ideal.span_singleton_eq_top.mpr (hunit j (by omega))).trans Ideal.one_eq_top.symm

/-- Families of local equations generating the same ideals have products generating the same
ideals, so they define the same steps of both filtrations. -/
theorem span_divisorProd_eq_of_span_eq {e e' : ℕ → R} {N N' : ℕ}
    (hunit : ∀ j, N < j → IsUnit (e j)) (hunit' : ∀ j, N' < j → IsUnit (e' j))
    (h : ∀ j, 1 ≤ j → Ideal.span ({e j} : Set R) = Ideal.span {e' j}) {i : ℕ} (hi : 1 ≤ i) :
    Ideal.span ({divisorProd e N i} : Set R) = Ideal.span {divisorProd e' N' i} := by
  have hb : ∀ (f : ℕ → R) (B : ℕ), Ideal.span ({divisorProd f B i} : Set R)
      = ∏ j ∈ Finset.Icc i B, Ideal.span {f j} := by
    intro f B
    rw [divisorProd, Ideal.prod_span_singleton]
  rw [hb e N, hb e' N', prod_span_extend e hunit i (max N N') (le_max_left _ _),
    prod_span_extend e' hunit' i (max N N') (le_max_right _ _)]
  exact Finset.prod_congr rfl fun j hj => h j (hi.trans (Finset.mem_Icc.mp hj).1)

section SameEquations

variable {M : Type v} [AddCommGroup M] [Module R M] {e e' : ℕ → R} {N N' : ℕ}

/-- The increasing filtration depends on the local equations only through the ideals they
generate. -/
theorem incr_eq_of_span_eq (hunit : ∀ j, N < j → IsUnit (e j))
    (hunit' : ∀ j, N' < j → IsUnit (e' j))
    (h : ∀ j, 1 ≤ j → Ideal.span ({e j} : Set R) = Ideal.span {e' j}) (i : ℕ) :
    incr M e N i = incr M e' N' i :=
  range_lsmul_eq_of_span_eq
    (span_divisorProd_eq_of_span_eq hunit hunit' h (Nat.le_add_left 1 i))

/-- The decreasing filtration depends on the local equations only through the ideals they
generate. -/
theorem decr_eq_of_span_eq (hunit : ∀ j, N < j → IsUnit (e j))
    (hunit' : ∀ j, N' < j → IsUnit (e' j))
    (h : ∀ j, 1 ≤ j → Ideal.span ({e j} : Set R) = Ideal.span {e' j}) {i : ℕ} (hi : 1 ≤ i) :
    decr M e N i = decr M e' N' i :=
  ker_lsmul_eq_of_span_eq (span_divisorProd_eq_of_span_eq hunit hunit' h hi)

end SameEquations

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The product formula exhibits every Fitting ideal as generated by a nonzerodivisor. -/
theorem exists_mem_nonZeroDivisors_fittingIdeal_eq_span_singleton [Module.Finite R M] {N : ℕ}
    {e : ℕ → R} (hmem : ∀ j, e j ∈ nonZeroDivisors R)
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) (k : ℕ) :
    ∃ g ∈ nonZeroDivisors R, fittingIdeal (R := R) (M := M) (k : ℤ) = Ideal.span {g} :=
  ⟨∏ j ∈ Finset.Icc (k + 1) N, e j ^ (j - k),
    prod_mem fun j _ => pow_mem (hmem j) (j - k),
    (hprod k).trans (prod_span_pow_eq_span_prod e N k)⟩

/-- **The graded pieces over a local ring, for the given equations.** Over a local ring, if the
nonzerodivisors `e_j` — units past `N` — cut out the Fitting ideals of a finite module `M` by
`Fit_k(M) = ∏_{j > k} (e_j)^{j-k}`, then both graded pieces in degree `i + 1` are free of rank
`i + 1` over `R ⧸ (e_{i+1})`. -/
theorem nonempty_gradedQuot_equiv_of_prod [IsLocalRing R] [Module.Finite R M] {N : ℕ} {e : ℕ → R}
    (hmem : ∀ j, e j ∈ nonZeroDivisors R) (hunit : ∀ j, N < j → IsUnit (e j))
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) (i : ℕ) :
    Nonempty (gradedQuot (incr M e N i) (incr M e N (i + 1))
        ≃ₗ[R] (Fin (i + 1) → R ⧸ Ideal.span {e (i + 1)})) ∧
      Nonempty (gradedQuot (decr M e N (i + 2)) (decr M e N (i + 1))
        ≃ₗ[R] (Fin (i + 1) → R ⧸ Ideal.span {e (i + 1)})) := by
  obtain ⟨n, e', hmem', hunit', hprod', -, -, -, -, -, -, higr, hdgr⟩ :=
    exists_divisors_and_filtrations_of_finite M
      (exists_mem_nonZeroDivisors_fittingIdeal_eq_span_singleton hmem hprod)
  have hsp := span_eq_of_prod M hmem hunit hprod hunit' hprod'
  have hincr : ∀ j, incr M e N j = incr M e' n j := incr_eq_of_span_eq hunit hunit' hsp
  have hdecr : ∀ j, 1 ≤ j → decr M e N j = decr M e' n j := fun _ hj =>
    decr_eq_of_span_eq hunit hunit' hsp hj
  rw [hincr i, hincr (i + 1), hdecr (i + 2) (by omega), hdecr (i + 1) (by omega),
    hsp (i + 1) (by omega)]
  exact ⟨higr i, hdgr i⟩

/-! ### The graded pieces commute with localization -/

/-- **The part of one submodule lying inside another localizes.** For submodules `N` and `P` of
`M`, the localization of `N ⊓ P` read inside `P` is the localization of `N` read inside the
localization of `P`. -/
@[ega "0 1.3.2"]
theorem localized_comap_subtype (q : Submonoid R) (N P : Submodule R M) :
    (N.comap P.subtype).localized' (Localization q) q (P.toLocalized q)
      = (N.localized q).comap (P.localized q).subtype := by
  ext x
  simp only [Submodule.mem_localized', Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · rintro ⟨m, hm, s, hs⟩
    rw [IsLocalizedModule.mk'_eq_iff] at hs
    refine ⟨(m : M), hm, s, ?_⟩
    rw [IsLocalizedModule.mk'_eq_iff]
    exact congrArg Subtype.val hs
  · rintro ⟨m, hm, s, hs⟩
    rw [IsLocalizedModule.mk'_eq_iff] at hs
    obtain ⟨m', hm', s', hs'⟩ := x.2
    rw [IsLocalizedModule.mk'_eq_iff] at hs'
    have hcomm : (LocalizedModule.mkLinearMap q M) ((s' : R) • m)
        = (LocalizedModule.mkLinearMap q M) ((s : R) • m') := by
      rw [map_smul, map_smul, hs, hs']
      simp only [Submonoid.smul_def, smul_smul, mul_comm]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := q) hcomm
    have hkey : ((c : R) * (s' : R)) • m = ((c : R) * (s : R)) • m' := by
      rw [mul_smul, mul_smul]
      exact hc
    have hmemP : ((c : R) * (s' : R)) • m ∈ P := by
      rw [hkey]
      exact P.smul_mem _ hm'
    refine ⟨⟨((c : R) * (s' : R)) • m, hmemP⟩, N.smul_mem _ hm, c * s' * s, ?_⟩
    rw [IsLocalizedModule.mk'_eq_iff]
    apply Subtype.ext
    show (LocalizedModule.mkLinearMap q M) (((c : R) * (s' : R)) • m) = _
    rw [map_smul, hs]
    simp [Submonoid.smul_def, mul_smul]

/-- **The graded piece of a pair of submodules localizes to the graded piece of the localized
pair.** This is `Stacks.FittingFiltration.gradedQuot` commuting with localization. -/
def gradedQuotLocalizedEquiv (q : Submonoid R) (N P : Submodule R M) :
    LocalizedModule q (gradedQuot N P)
      ≃ₗ[Localization q] gradedQuot (N.localized q) (P.localized q) :=
  ((IsLocalizedModule.linearEquiv q
        (LocalizedModule.mkLinearMap q (gradedQuot N P))
        ((N.comap P.subtype).toLocalizedQuotient' (Localization q) q
          (P.toLocalized q))).extendScalarsOfIsLocalization q (Localization q)).trans
    (Submodule.quotEquivOfEq _ _ (localized_comap_subtype q N P))

/-- The increasing filtration localizes to the increasing filtration of the localized module, for
the images of the local equations. -/
theorem incr_localized (p : Ideal R) [p.IsPrime] (e : ℕ → R) (n i : ℕ) :
    (incr M e n i).localized p.primeCompl
      = incr (LocalizedModule.AtPrime p M)
        (fun j => algebraMap R (Localization.AtPrime p) (e j)) n i := by
  rw [incr, range_lsmul_localized, incr, divisorProd, divisorProd, map_prod]

/-- The decreasing filtration localizes to the decreasing filtration of the localized module, for
the images of the local equations. -/
theorem decr_localized (p : Ideal R) [p.IsPrime] (e : ℕ → R) (n i : ℕ) :
    (decr M e n i).localized p.primeCompl
      = decr (LocalizedModule.AtPrime p M)
        (fun j => algebraMap R (Localization.AtPrime p) (e j)) n i := by
  rw [decr, ker_lsmul_localizedAtPrime, decr, divisorProd, divisorProd, map_prod]

/-! ### The Fitting ideals of the model graded piece

The local form identifies a graded piece with `(R ⧸ (a))^{i+1}`, the structure sheaf of the divisor
cut out by `a` to the power `i + 1`. Its Fitting ideals are the powers of `(a)`: this is the
scaled-presentation computation `fittingIdeal_quotient_span_smul` for the presentation `a · 1` of
that module.
-/

/-- Multiplication by `a` on `Rⁿ` is presented by the matrix `a · 1`. -/
private theorem mulVecLin_smul_one (r : ℕ) (a : R) :
    (a • (1 : Matrix (Fin r) (Fin r) R)).mulVecLin = LinearMap.lsmul R (Fin r → R) a := by
  ext v i
  simp

/-- **The Fitting ideals of the free module of rank `r` over `R ⧸ (a)`** are the powers
`(a)^{r-k}`. In degree `r - 1` this is `(a)` and in degree `r` the unit ideal, which is the
Fitting criterion for being finite locally free of rank `r` over `R ⧸ (a)`. -/
theorem fittingIdeal_pi_quotient_span_singleton (r : ℕ) (a : R) (k : ℕ) :
    fittingIdeal (R := R) (M := (Fin r → R ⧸ Ideal.span {a})) (k : ℤ)
      = Ideal.span {a} ^ (r - k) := by
  have hcol : Stacks.ScaledPresentation.smulSubmodule r a
      = (a • (1 : Matrix (Fin r) (Fin r) R)).columnSpan := by
    rw [Matrix.columnSpan_eq_range_mulVecLin, mulVecLin_smul_one]
  have hone : (1 : Matrix (Fin r) (Fin r) R).columnSpan = ⊤ := by
    rw [Matrix.columnSpan_eq_range_mulVecLin]
    refine LinearMap.range_eq_top.mpr fun v => ⟨v, ?_⟩
    simp
  have : Subsingleton ((Fin r → R) ⧸ (1 : Matrix (Fin r) (Fin r) R).columnSpan) :=
    subsingleton_quotient_of_eq_top hone
  have hfitone : fittingIdeal (R := R)
      (M := (Fin r → R) ⧸ (1 : Matrix (Fin r) (Fin r) R).columnSpan) (k : ℤ) = ⊤ := by
    rw [fittingIdeal_eq_of_linearEquiv
        (subsingletonEquiv ((Fin r → R) ⧸ (1 : Matrix (Fin r) (Fin r) R).columnSpan)
          (Fin 0 → R)) k,
      fittingIdeal_fin_eq_bot_or_top 0 (k : ℤ), if_neg (by push_cast; omega)]
  rw [← fittingIdeal_eq_of_linearEquiv (Stacks.ScaledPresentation.quotSmulEquivFree r a) k, hcol,
    fittingIdeal_quotient_span_smul 1 a k, hfitone, Ideal.mul_top]

/-! ### The graded pieces are killed by the equation of their divisor

This is what makes a graded piece a module over `R ⧸ (e_{i+1})`, the ring of functions on the
divisor `D_{i+1}`. It holds for any family of ring elements whatever: both statements are a
one-step identity between consecutive products of the equations.
-/

/-- **The graded piece of the increasing filtration in degree `i + 1` is killed by `e_{i+1}`.**
Its step `F^{i+1}` is the multiples of `e_{i+2} ⋯ e_n`, so `e_{i+1}` carries it into the multiples
of `e_{i+1} ⋯ e_n`, which is `F^i`. -/
theorem isTorsionBy_gradedQuot_incr (e : ℕ → R) (n i : ℕ) :
    Module.IsTorsionBy R (gradedQuot (incr M e n i) (incr M e n (i + 1))) (e (i + 1)) := by
  rw [Module.isTorsionBy_quotient_iff]
  intro x
  rw [mem_comap_subtype_iff]
  rcases le_or_gt (i + 1) n with hi | hi
  · obtain ⟨y, hy⟩ := x.2
    refine ⟨y, ?_⟩
    simp only [LinearMap.lsmul_apply, Submodule.coe_smul] at hy ⊢
    rw [divisorProd_succ e hi, ← hy, mul_smul]
  · have htop : incr M e n i = ⊤ :=
      range_lsmul_eq_top_of_eq_one (divisorProd_of_lt e (by omega))
    rw [htop]
    exact Submodule.mem_top

/-- **The graded piece of the decreasing filtration in degree `i + 1` is killed by `e_{i+1}`.**
Its step `F_{i+1}` is what `e_{i+1} ⋯ e_n` kills, so `e_{i+1}` carries it into what
`e_{i+2} ⋯ e_n` kills, which is `F_{i+2}`. -/
theorem isTorsionBy_gradedQuot_decr (e : ℕ → R) (n i : ℕ) :
    Module.IsTorsionBy R (gradedQuot (decr M e n (i + 2)) (decr M e n (i + 1))) (e (i + 1)) := by
  rw [Module.isTorsionBy_quotient_iff]
  intro x
  rw [mem_comap_subtype_iff]
  have hx : divisorProd e n (i + 1) • (x : M) = 0 := x.2
  have hco : ((e (i + 1) • x : ↥(decr M e n (i + 1))) : M) = e (i + 1) • (x : M) := rfl
  rw [hco]
  rcases le_or_gt (i + 1) n with hi | hi
  · show divisorProd e n (i + 2) • (e (i + 1) • (x : M)) = 0
    rw [smul_smul, mul_comm (divisorProd e n (i + 2)) (e (i + 1)), ← divisorProd_succ e hi, hx]
  · have hone : divisorProd e n (i + 1) = 1 := divisorProd_of_lt e (by omega)
    rw [hone, one_smul] at hx
    rw [hx, smul_zero]
    exact Submodule.zero_mem _

/-! ### The Fitting ideals of the graded pieces over an arbitrary ring -/

/-- The multiples of a ring element in a finite module form a finite module: they are the image
of `M`. -/
theorem finite_range_lsmul [Module.Finite R M] (c : R) :
    Module.Finite R ↥(LinearMap.range (LinearMap.lsmul R M c)) := by
  rw [Module.Finite.iff_fg, ← Submodule.map_top]
  exact (Module.finite_def.mp inferInstance).map _

/-- **Every step of the increasing filtration is a finite module**: it is the image of `M` under
multiplication by a product of the local equations. -/
instance finite_incr [Module.Finite R M] (e : ℕ → R) (N i : ℕ) :
    Module.Finite R ↥(incr M e N i) :=
  finite_range_lsmul (divisorProd e N (i + 1))

/-- The hypotheses on the local equations pass to a localization at a prime. -/
private theorem prod_localizedAtPrime [Module.Finite R M] {N : ℕ} {e : ℕ → R}
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k))
    (p : Ideal R) [p.IsPrime] (k : ℕ) :
    fittingIdeal (R := Localization.AtPrime p) (M := LocalizedModule.AtPrime p M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N,
        Ideal.span {algebraMap R (Localization.AtPrime p) (e j)} ^ (j - k) := by
  rw [fittingIdeal_localizedAtPrime_eq_map p k, hprod k, prod_span_pow_eq_span_prod, Ideal.map_span,
    Set.image_singleton, map_prod]
  simp only [map_pow]
  rw [← prod_span_pow_eq_span_prod]

/-- A module whose localizations at maximal ideals are free of rank `r` over `R ⧸ (a)` has Fitting
ideals `(a)^{r-k}`. -/
private theorem fittingIdeal_eq_pow_of_localized_equiv {X : Type v} [AddCommGroup X] [Module R X]
    [Module.Finite R X] (a : R) (r k : ℕ)
    (h : ∀ (P : Ideal R) [P.IsMaximal], Nonempty (LocalizedModule.AtPrime P X
      ≃ₗ[Localization.AtPrime P]
        (Fin r → Localization.AtPrime P ⧸ Ideal.span {algebraMap R (Localization.AtPrime P) a}))) :
    fittingIdeal (R := R) (M := X) (k : ℤ) = Ideal.span {a} ^ (r - k) := by
  refine Ideal.eq_of_localization_maximal fun P hP => ?_
  have : P.IsPrime := hP.isPrime
  obtain ⟨ψ⟩ := h P
  rw [← fittingIdeal_localizedAtPrime_eq_map P k, Ideal.map_pow, Ideal.map_span,
    Set.image_singleton, fittingIdeal_eq_of_linearEquiv ψ k,
    fittingIdeal_pi_quotient_span_singleton]

/-- **The Fitting ideals of the graded piece of the increasing filtration**, over a ring that need
not be local: `Fit_k(F^{i+1}/F^i) = (e_{i+1})^{i+1-k}`. In particular the `i`-th is `(e_{i+1})` and
the `(i+1)`-st is the unit ideal, which is the Fitting criterion for finite local freeness of rank
`i + 1` over `R ⧸ (e_{i+1})`. -/
theorem fittingIdeal_gradedQuot_incr [Module.Finite R M] {N : ℕ} {e : ℕ → R}
    (hmem : ∀ j, e j ∈ nonZeroDivisors R) (hunit : ∀ j, N < j → IsUnit (e j))
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) (i k : ℕ) :
    fittingIdeal (R := R) (M := gradedQuot (incr M e N i) (incr M e N (i + 1))) (k : ℤ)
      = Ideal.span {e (i + 1)} ^ (i + 1 - k) := by
  refine fittingIdeal_eq_pow_of_localized_equiv _ _ k fun P _ => ?_
  have : P.IsPrime := ‹P.IsMaximal›.isPrime
  have hiso := gradedQuotLocalizedEquiv (M := M) P.primeCompl
    (incr M e N i) (incr M e N (i + 1))
  rw [incr_localized P e N i, incr_localized P e N (i + 1)] at hiso
  obtain ⟨⟨φ⟩, -⟩ := nonempty_gradedQuot_equiv_of_prod (R := Localization.AtPrime P)
    (M := LocalizedModule.AtPrime P M)
    (fun j => mem_nonZeroDivisors_algebraMap_of_flat (hmem j))
    (fun j hj => (hunit j hj).map (algebraMap R (Localization.AtPrime P)))
    (prod_localizedAtPrime hprod P) i
  exact ⟨hiso.trans φ⟩

/-- **The Fitting ideals of the graded piece of the decreasing filtration**, over a ring that need
not be local: `Fit_k(F_{i+1}/F_{i+2}) = (e_{i+1})^{i+1-k}`, for a finite step `F_{i+1}`. -/
theorem fittingIdeal_gradedQuot_decr [Module.Finite R M] {N : ℕ} {e : ℕ → R} (i : ℕ)
    [Module.Finite R ↥(decr M e N (i + 1))]
    (hmem : ∀ j, e j ∈ nonZeroDivisors R) (hunit : ∀ j, N < j → IsUnit (e j))
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) (k : ℕ) :
    fittingIdeal (R := R) (M := gradedQuot (decr M e N (i + 2)) (decr M e N (i + 1))) (k : ℤ)
      = Ideal.span {e (i + 1)} ^ (i + 1 - k) := by
  refine fittingIdeal_eq_pow_of_localized_equiv _ _ k fun P _ => ?_
  have : P.IsPrime := ‹P.IsMaximal›.isPrime
  have hiso := gradedQuotLocalizedEquiv (M := M) P.primeCompl
    (decr M e N (i + 2)) (decr M e N (i + 1))
  rw [decr_localized P e N (i + 2), decr_localized P e N (i + 1)] at hiso
  have := Module.Finite.equiv hiso
  obtain ⟨-, ⟨φ⟩⟩ := nonempty_gradedQuot_equiv_of_prod (R := Localization.AtPrime P)
    (M := LocalizedModule.AtPrime P M)
    (fun j => mem_nonZeroDivisors_algebraMap_of_flat (hmem j))
    (fun j hj => (hunit j hj).map (algebraMap R (Localization.AtPrime P)))
    (prod_localizedAtPrime hprod P) i
  exact ⟨hiso.trans φ⟩

/-! ### From the Fitting ideals to finite local freeness over the ring of the divisor

A module killed by `a` is a module over `R ⧸ (a)`, and its Fitting ideals there are the images of
its Fitting ideals over `R`. So the pair `Fit_{r-1} = (a)`, `Fit_r = ⊤` over `R` becomes the pair
`Fit_{r-1} = ⊥`, `Fit_r = ⊤` over `R ⧸ (a)`, which is the Fitting criterion for being finite
locally free of rank `r` ([Stacks, Tag 07ZD]).
-/

section Quotient

variable {G : Type v} [AddCommGroup G] [Module R G] {a : R}

/-- A module killed by `a` is killed by the whole ideal `(a)`. -/
theorem smul_top_eq_bot_of_isTorsionBySet
    (hT : Module.IsTorsionBySet R G (Ideal.span {a} : Ideal R)) :
    (Ideal.span {a} : Ideal R) • (⊤ : Submodule R G) = ⊥ :=
  le_antisymm (Submodule.smul_le.mpr fun r hr x _ => (Submodule.mem_bot R).mpr (@hT x ⟨r, hr⟩))
    bot_le

/-- **The Fitting ideals of a module killed by `a`, computed over `R ⧸ (a)`**, are the images of
its Fitting ideals over `R`: the module is its own base change along `R → R ⧸ (a)`. -/
theorem fittingIdeal_quotient_eq_map [Module.Finite R G] [Module (R ⧸ Ideal.span {a}) G]
    [IsScalarTower R (R ⧸ Ideal.span {a}) G]
    (hT : Module.IsTorsionBySet R G (Ideal.span {a} : Ideal R)) (k : ℕ) :
    haveI : Module.Finite (R ⧸ Ideal.span {a}) G :=
      Module.Finite.of_restrictScalars_finite R _ G
    fittingIdeal (R := R ⧸ Ideal.span {a}) (M := G) (k : ℤ)
      = Ideal.map (algebraMap R (R ⧸ Ideal.span {a})) (fittingIdeal (R := R) (M := G) (k : ℤ)) := by
  have : Module.Finite (R ⧸ Ideal.span {a}) G := Module.Finite.of_restrictScalars_finite R _ G
  have eq0 : ((R ⧸ Ideal.span {a}) ⊗[R] G) ≃ₗ[R ⧸ Ideal.span {a}] G :=
    LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      ((TensorProduct.quotTensorEquivQuotSMul G (Ideal.span {a})).trans
        (Submodule.quotEquivOfEqBot _ (smul_top_eq_bot_of_isTorsionBySet hT)))
  rw [← fittingIdeal_eq_of_linearEquiv eq0 k]
  exact (fittingIdeal_basic_properties.{u, v, v, u} (R := R) (M := G)).2.2.1
    (R ⧸ Ideal.span {a}) k

/-- **A module killed by `a` whose Fitting ideals over `R` are the powers `(a)^{r-k}` is finite
locally free of rank `r` over `R ⧸ (a)`.** This is the Fitting criterion of [Stacks, Tag 07ZD],
read over the quotient ring. -/
theorem isFiniteLocallyFreeOfRank_of_fittingIdeal_eq_pow [Module.Finite R G]
    [Module (R ⧸ Ideal.span {a}) G] [IsScalarTower R (R ⧸ Ideal.span {a}) G]
    (hT : Module.IsTorsionBySet R G (Ideal.span {a} : Ideal R)) (r : ℕ)
    (hfit : ∀ k : ℕ, fittingIdeal (R := R) (M := G) (k : ℤ) = Ideal.span {a} ^ (r - k)) :
    Module.IsFiniteLocallyFreeOfRank (R ⧸ Ideal.span {a}) G r := by
  have : Module.Finite (R ⧸ Ideal.span {a}) G := Module.Finite.of_restrictScalars_finite R _ G
  have hpred : fittingIdeal (R := R ⧸ Ideal.span {a}) (M := G) ((r : ℤ) - 1) = ⊥ := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · rw [hr]
      rw [fittingIdeal, if_pos (by omega)]
    · obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
      rw [show ((s + 1 : ℕ) : ℤ) - 1 = (s : ℤ) from by omega,
        fittingIdeal_quotient_eq_map hT s, hfit s,
        show s + 1 - s = 1 from by omega, pow_one, Ideal.map_span, Set.image_singleton,
        Ideal.span_singleton_eq_bot]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a)
  have htop : fittingIdeal (R := R ⧸ Ideal.span {a}) (M := G) (r : ℤ) = ⊤ := by
    rw [fittingIdeal_quotient_eq_map hT r, hfit r, Nat.sub_self, pow_zero, Ideal.one_eq_top,
      Ideal.map_top]
  refine ((finiteLocallyFreeOfRank_fittingIdeal_tfae
    (R := R ⧸ Ideal.span {a}) (M := G) r).out 2 1).1 ?_
  exact ⟨hpred, htop⟩

end Quotient

/-! ### The graded pieces over a ring that is not local -/

/-- A graded piece of the increasing filtration is killed by the equation of its divisor, so it is
a module over `R ⧸ (e_{i+1})`. -/
theorem isTorsionBySet_gradedQuot_incr (e : ℕ → R) (N i : ℕ) :
    Module.IsTorsionBySet R (gradedQuot (incr M e N i) (incr M e N (i + 1)))
      (Ideal.span {e (i + 1)} : Ideal R) :=
  (Module.isTorsionBySet_span_singleton_iff _).mpr (isTorsionBy_gradedQuot_incr e N i)

/-- A graded piece of the decreasing filtration is killed by the equation of its divisor, so it is
a module over `R ⧸ (e_{i+1})`. -/
theorem isTorsionBySet_gradedQuot_decr (e : ℕ → R) (N i : ℕ) :
    Module.IsTorsionBySet R (gradedQuot (decr M e N (i + 2)) (decr M e N (i + 1)))
      (Ideal.span {e (i + 1)} : Ideal R) :=
  (Module.isTorsionBySet_span_singleton_iff _).mpr (isTorsionBy_gradedQuot_decr e N i)

/-- **A graded piece of the decreasing filtration is killed by the equation of its divisor,
stated for submodules merely *equal* to the two filtration steps.** -/
theorem isTorsionBySet_gradedQuot_decr_of_eq {P Q : _root_.Submodule R M} {e : ℕ → R} {N i : ℕ}
    (hP : P = decr M e N (i + 2)) (hQ : Q = decr M e N (i + 1)) :
    Module.IsTorsionBySet R (gradedQuot P Q) (Ideal.span {e (i + 1)} : Ideal R) := by
  subst hP
  subst hQ
  exact isTorsionBySet_gradedQuot_decr e N i

/-- **The graded piece of the increasing filtration over a ring that need not be local.** Let `M`
be a finite module over an arbitrary commutative ring `R` whose Fitting ideals are cut out by
nonzerodivisors `e_j` — units past `N` — through `Fit_k(M) = ∏_{j > k} (e_j)^{j-k}`. Then the
graded piece `F^{i+1}/F^i` is **finite locally free of rank `i + 1`** over `R ⧸ (e_{i+1})`, the
ring of functions on the divisor `D_{i+1}`. -/
theorem isFiniteLocallyFreeOfRank_gradedQuot_incr [Module.Finite R M] {N : ℕ} {e : ℕ → R}
    (hmem : ∀ j, e j ∈ nonZeroDivisors R) (hunit : ∀ j, N < j → IsUnit (e j))
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) (i : ℕ) :
    letI := (isTorsionBySet_gradedQuot_incr (M := M) e N i).module
    haveI := (isTorsionBySet_gradedQuot_incr (M := M) e N i).isScalarTower (S := R)
    Module.IsFiniteLocallyFreeOfRank (R ⧸ Ideal.span {e (i + 1)})
      (gradedQuot (incr M e N i) (incr M e N (i + 1))) (i + 1) := by
  let := (isTorsionBySet_gradedQuot_incr (M := M) e N i).module
  have := (isTorsionBySet_gradedQuot_incr (M := M) e N i).isScalarTower (S := R)
  exact isFiniteLocallyFreeOfRank_of_fittingIdeal_eq_pow
    (isTorsionBySet_gradedQuot_incr (M := M) e N i) (i + 1)
    (fun k => fittingIdeal_gradedQuot_incr hmem hunit hprod i k)

/-- **The graded piece of the decreasing filtration over a ring that need not be local.** Under the
hypotheses of `Stacks.FittingFiltration.isFiniteLocallyFreeOfRank_gradedQuot_incr`, and with the
step `F_{i+1}` finite, the graded piece `F_{i+1}/F_{i+2}` is **finite locally free of rank
`i + 1`** over `R ⧸ (e_{i+1})`. -/
theorem isFiniteLocallyFreeOfRank_gradedQuot_decr [Module.Finite R M] {N : ℕ} {e : ℕ → R} (i : ℕ)
    [Module.Finite R ↥(decr M e N (i + 1))]
    (hmem : ∀ j, e j ∈ nonZeroDivisors R) (hunit : ∀ j, N < j → IsUnit (e j))
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) :
    letI := (isTorsionBySet_gradedQuot_decr (M := M) e N i).module
    haveI := (isTorsionBySet_gradedQuot_decr (M := M) e N i).isScalarTower (S := R)
    Module.IsFiniteLocallyFreeOfRank (R ⧸ Ideal.span {e (i + 1)})
      (gradedQuot (decr M e N (i + 2)) (decr M e N (i + 1))) (i + 1) := by
  let := (isTorsionBySet_gradedQuot_decr (M := M) e N i).module
  have := (isTorsionBySet_gradedQuot_decr (M := M) e N i).isScalarTower (S := R)
  exact isFiniteLocallyFreeOfRank_of_fittingIdeal_eq_pow
    (isTorsionBySet_gradedQuot_decr (M := M) e N i) (i + 1)
    (fun k => fittingIdeal_gradedQuot_decr i hmem hunit hprod k)

/-! ### The anchors of the two filtrations over a ring that is not local

`F^0 = 0` and `F_1 = M` are the two anchors of the source's filtrations. Unlike their finiteness
and monotonicity they are not formal properties of the definitions: they say that the product
`e_1 ⋯ e_N` annihilates `M`.
-/

/-- **Both anchors over a local ring, for the given equations.** `F^0 = 0` and `F_1 = M` for any
family of nonzerodivisors cutting out the Fitting ideals by the product formula. -/
theorem incr_zero_eq_bot_and_decr_one_eq_top_of_prod [IsLocalRing R] [Module.Finite R M] {N : ℕ}
    {e : ℕ → R} (hmem : ∀ j, e j ∈ nonZeroDivisors R) (hunit : ∀ j, N < j → IsUnit (e j))
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) :
    incr M e N 0 = ⊥ ∧ decr M e N 1 = ⊤ := by
  obtain ⟨n, e', hmem', hunit', hprod', hz, -, -, ho, -, -, -, -⟩ :=
    exists_divisors_and_filtrations_of_finite M
      (exists_mem_nonZeroDivisors_fittingIdeal_eq_span_singleton hmem hprod)
  have hsp := span_eq_of_prod M hmem hunit hprod hunit' hprod'
  exact ⟨(incr_eq_of_span_eq hunit hunit' hsp 0).trans hz,
    (decr_eq_of_span_eq hunit hunit' hsp (le_refl 1)).trans ho⟩

/-- **The increasing filtration starts at zero over a ring that need not be local**: `F^0 = 0`,
that is, the product `e_1 ⋯ e_N` of all the local equations annihilates `M`. -/
theorem incr_zero_eq_bot [Module.Finite R M] {N : ℕ} {e : ℕ → R}
    (hmem : ∀ j, e j ∈ nonZeroDivisors R) (hunit : ∀ j, N < j → IsUnit (e j))
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) :
    incr M e N 0 = ⊥ := by
  refine Submodule.eq_bot_of_localization_maximal
    (fun P _ => Localization.AtPrime P) (fun P _ => LocalizedModule.AtPrime P M)
    (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M) _ fun P hP => ?_
  have : P.IsPrime := hP.isPrime
  rw [show Submodule.localized' (Localization.AtPrime P) P.primeCompl
      (LocalizedModule.mkLinearMap P.primeCompl M) (incr M e N 0)
        = (incr M e N 0).localized P.primeCompl from rfl, incr_localized P e N 0]
  exact (incr_zero_eq_bot_and_decr_one_eq_top_of_prod
    (fun j => mem_nonZeroDivisors_algebraMap_of_flat (hmem j))
    (fun j hj => (hunit j hj).map (algebraMap R (Localization.AtPrime P)))
    (prod_localizedAtPrime hprod P)).1

/-- **The decreasing filtration starts at the whole module over a ring that need not be local**:
`F_1 = M`, the other side of `Stacks.FittingFiltration.incr_zero_eq_bot`. -/
theorem decr_one_eq_top [Module.Finite R M] {N : ℕ} {e : ℕ → R}
    (hmem : ∀ j, e j ∈ nonZeroDivisors R) (hunit : ∀ j, N < j → IsUnit (e j))
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) :
    decr M e N 1 = ⊤ := by
  refine Submodule.eq_top_of_localization_maximal
    (fun P _ => Localization.AtPrime P) (fun P _ => LocalizedModule.AtPrime P M)
    (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M) _ fun P hP => ?_
  have : P.IsPrime := hP.isPrime
  rw [show Submodule.localized' (Localization.AtPrime P) P.primeCompl
      (LocalizedModule.mkLinearMap P.primeCompl M) (decr M e N 1)
        = (decr M e N 1).localized P.primeCompl from rfl, decr_localized P e N 1]
  exact (incr_zero_eq_bot_and_decr_one_eq_top_of_prod
    (fun j => mem_nonZeroDivisors_algebraMap_of_flat (hmem j))
    (fun j hj => (hunit j hj).map (algebraMap R (Localization.AtPrime P)))
    (prod_localizedAtPrime hprod P)).2

/-! ### Every step of the decreasing filtration is a finite module -/

/-- The quotient of a ring by a principal ideal is a finitely presented module over it: the
presentation is multiplication by the generator. -/
theorem finitePresentation_quotient_span_singleton (c : R) :
    Module.FinitePresentation R (R ⧸ Ideal.span {c}) :=
  Module.finitePresentation_of_surjective (Ideal.span {c}).mkQ
    (Submodule.mkQ_surjective _)
    (by rw [Submodule.ker_mkQ]; exact ⟨{c}, by simp⟩)

section FinitePresentation

variable {M : Type u} [AddCommGroup M] [Module R M]

/-- **A graded piece of the increasing filtration is a finitely presented `R`-module.** -/
theorem finitePresentation_gradedQuot_incr [Module.Finite R M] {N : ℕ} {e : ℕ → R}
    (hmem : ∀ j, e j ∈ nonZeroDivisors R) (hunit : ∀ j, N < j → IsUnit (e j))
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) (i : ℕ) :
    Module.FinitePresentation R (gradedQuot (incr M e N i) (incr M e N (i + 1))) := by
  let := (isTorsionBySet_gradedQuot_incr (M := M) e N i).module
  have := (isTorsionBySet_gradedQuot_incr (M := M) e N i).isScalarTower (S := R)
  obtain ⟨hfin, hproj⟩ :=
    (isFiniteLocallyFreeOfRank_gradedQuot_incr hmem hunit hprod i).finite_and_projective
  have := hfin
  have := hproj
  have : Module.FinitePresentation (R ⧸ Ideal.span {e (i + 1)})
      (gradedQuot (incr M e N i) (incr M e N (i + 1))) :=
    Module.finitePresentation_of_projective _ _
  have := finitePresentation_quotient_span_singleton (R := R) (e (i + 1))
  exact Module.FinitePresentation.trans (R := R)
    (M := gradedQuot (incr M e N i) (incr M e N (i + 1))) (S := R ⧸ Ideal.span {e (i + 1)})

/-- **Every step of the increasing filtration is a finitely presented module.** -/
theorem finitePresentation_incr [Module.FinitePresentation R M] {N : ℕ} {e : ℕ → R}
    (hmem : ∀ j, e j ∈ nonZeroDivisors R) (hunit : ∀ j, N < j → IsUnit (e j))
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) (i : ℕ) :
    Module.FinitePresentation R ↥(incr M e N i) := by
  induction i with
  | zero =>
    rw [incr_zero_eq_bot hmem hunit hprod]
    exact Module.finitePresentation_of_surjective (0 : R →ₗ[R] ↥(⊥ : Submodule R M))
      (fun _ => ⟨0, Subsingleton.elim _ _⟩)
      (by rw [LinearMap.ker_zero]; exact Module.Finite.fg_top)
  | succ j ih =>
    have := ih
    have := finitePresentation_gradedQuot_incr hmem hunit hprod j
    have hle : incr M e N j ≤ incr M e N (j + 1) := incr_monotone e N (Nat.le_succ j)
    have : Module.FinitePresentation R
        ↥(LinearMap.ker (Submodule.comap (incr M e N (j + 1)).subtype (incr M e N j)).mkQ) := by
      rw [Submodule.ker_mkQ]
      exact Module.FinitePresentation.of_equiv (Submodule.comapSubtypeEquivOfLe hle).symm
    exact Module.finitePresentation_of_ker
      (Submodule.comap (incr M e N (j + 1)).subtype (incr M e N j)).mkQ
      (Submodule.mkQ_surjective _)

/-- **Every step of the decreasing filtration is a finite module, over a ring that need not be
Noetherian**, for a finitely presented `M`. -/
theorem finite_decr [Module.FinitePresentation R M] {N : ℕ} {e : ℕ → R}
    (hmem : ∀ j, e j ∈ nonZeroDivisors R) (hunit : ∀ j, N < j → IsUnit (e j))
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) (i : ℕ) :
    Module.Finite R ↥(decr M e N (i + 1)) := by
  have := finitePresentation_incr hmem hunit hprod i
  have hmemincr : ∀ x : M, LinearMap.lsmul R M (divisorProd e N (i + 1)) x ∈ incr M e N i :=
    fun x => LinearMap.mem_range_self _ x
  let g : M →ₗ[R] ↥(incr M e N i) :=
    (LinearMap.lsmul R M (divisorProd e N (i + 1))).codRestrict (incr M e N i) hmemincr
  have hsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp (show y ∈ LinearMap.range _ from hy)
    exact ⟨x, rfl⟩
  have hker : LinearMap.ker g = decr M e N (i + 1) :=
    LinearMap.ker_codRestrict (incr M e N i) _ hmemincr
  exact Module.Finite.iff_fg.mpr (hker ▸ Module.FinitePresentation.fg_ker g hsurj)

/-- **The graded piece of the decreasing filtration over a ring that need not be local, with no
finiteness hypothesis on the filtration.** For a **finitely presented** module whose Fitting ideals
are cut out by the nonzerodivisors `e_j` through `Fit_k(M) = ∏_{j > k} (e_j)^{j-k}`, the graded
piece `F_{i+1}/F_{i+2}` is finite locally free of rank `i + 1` over `R ⧸ (e_{i+1})`. -/
theorem isFiniteLocallyFreeOfRank_gradedQuot_decr_of_finitePresentation
    [Module.FinitePresentation R M] {N : ℕ} {e : ℕ → R} (i : ℕ)
    (hmem : ∀ j, e j ∈ nonZeroDivisors R) (hunit : ∀ j, N < j → IsUnit (e j))
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) :
    letI := (isTorsionBySet_gradedQuot_decr (M := M) e N i).module
    haveI := (isTorsionBySet_gradedQuot_decr (M := M) e N i).isScalarTower (S := R)
    Module.IsFiniteLocallyFreeOfRank (R ⧸ Ideal.span {e (i + 1)})
      (gradedQuot (decr M e N (i + 2)) (decr M e N (i + 1))) (i + 1) := by
  have := finite_decr hmem hunit hprod i
  exact isFiniteLocallyFreeOfRank_gradedQuot_decr i hmem hunit hprod

/-- **The decreasing graded clause for submodules merely *equal* to the two filtration steps.**
`Stacks.FittingFiltration.isFiniteLocallyFreeOfRank_gradedQuot_decr_of_finitePresentation` with the
two equalities substituted into the type of the graded piece. -/
theorem isFiniteLocallyFreeOfRank_gradedQuot_decr_of_eq [Module.FinitePresentation R M]
    {P Q : _root_.Submodule R M} {N : ℕ} {e : ℕ → R} {i : ℕ}
    (hP : P = decr M e N (i + 2)) (hQ : Q = decr M e N (i + 1))
    (hmem : ∀ j, e j ∈ nonZeroDivisors R) (hunit : ∀ j, N < j → IsUnit (e j))
    (hprod : ∀ k : ℕ, fittingIdeal (R := R) (M := M) (k : ℤ) =
      ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) :
    letI := (isTorsionBySet_gradedQuot_decr_of_eq hP hQ).module
    haveI := (isTorsionBySet_gradedQuot_decr_of_eq hP hQ).isScalarTower (S := R)
    Module.IsFiniteLocallyFreeOfRank (R ⧸ Ideal.span {e (i + 1)}) (gradedQuot P Q) (i + 1) := by
  subst hP
  subst hQ
  exact isFiniteLocallyFreeOfRank_gradedQuot_decr_of_finitePresentation i hmem hunit hprod

end FinitePresentation

end Stacks.FittingFiltration

end
