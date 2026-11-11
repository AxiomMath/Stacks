module

public import StacksFrontier.Examples.Flatness.NonOpenFlatLocusSpace
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtalePullback
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.PullbackOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TwistedLineQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFiniteTypeOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedChartHenselization
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.EtaleBaseChange

/-!
# An algebraic space with two weakly associated points at which Stacks 0DLR fails

**Stacks 0DLR** asserts, for a morphism `f : X ⟶ Y` of algebraic spaces locally of finite
presentation and a quasi-coherent `𝒪_X`-module `F` of finite type, that the flat locus of `F`
over `Y` is open in `|X|` as soon as (3) the set `WeakAss(Y)` of weakly associated points of `Y`
is locally finite in `|Y|`.  That is false.  Its proof reads (3) as local finiteness of the
weakly associated points of a surjective étale scheme chart of `Y`, which is stronger when `Y`
is not decent.

The counterexample is the one of `Stacks.Examples.NonOpenFlatLocusSpace`: the ring
`A = ℚ[t, u_i : i ∈ ℤ]/((t - i) u_i : i ∈ ℤ)`, the quotient `Y = Spec A / ℤ` by the shift
`t ↦ t - n`, `u_i ↦ u_{i + n}`, the quotient map `f : X = Spec A ⟶ Y`, which is étale, and the
module `F = A ⧸ (u_i : i ≥ 1)`.  That file shows the flat locus of `F` over `Y` is not open in a
fibre of `f`; it is then not open in `|X|`.  This file shows that `Y` satisfies (3): `A` is
reduced, so its weakly associated primes are its minimal primes (Stacks 0EMA), which are the
line `(u_i : i ∈ ℤ)` and the axes `(t - i, u_j : j ≠ i)`; the axes form one orbit of the shift,
so `WeakAss(Y)` has at most two points, by Stacks 0CUU along the étale map `f` and Stacks 0CTW
on the represented space `X`.

## Main results

* `Stacks.Examples.NonOpenFlatLocusWeaklyAssociated.ambHom_injective` and the instance
  `Stacks.Examples.NonOpenFlatLocusWeaklyAssociated.isReduced_A`: `A` embeds into
  `ℚ[X] × ∏_{i : ℤ} ℚ[X]`, so it is reduced.
* `Stacks.Examples.NonOpenFlatLocusWeaklyAssociated.minimalPrimes_subset`: every minimal prime
  of `A` is the line or an axis.
* `Stacks.Examples.NonOpenFlatLocusWeaklyAssociated.weaklyAssociatedPointsOfSpace_Ysp_finite`:
  `WeakAss(Y)` is finite.
* `Stacks.Examples.NonOpenFlatLocusWeaklyAssociated.exists_not_isOpen_flatLocus`:
  **the refutation of Stacks 0DLR as printed.**

## References

* [Stacks Project, Tag 0DLR](https://stacks.math.columbia.edu/tag/0DLR)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 0CTW](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 0EMA](https://stacks.math.columbia.edu/tag/0EMA)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open Stacks.Examples.NonOpenFlatLocus Stacks.Examples.NonOpenFlatLocusSpace

namespace Stacks.Examples.NonOpenFlatLocusWeaklyAssociated

/-! ### `A` is reduced -/

/-- The normal-form model map `A → ℚ[X] × ∏_{i : ℤ} ℚ[X]`. -/
def ambHom : A →ₐ[ℚ] Amb := nfSubalgebra.val.comp nfHom

@[simp]
theorem ambHom_t : ambHom t = ambT := by
  simp [ambHom, coe_nfT]

@[simp]
theorem ambHom_u (i : ℤ) : ambHom (u i) = ambU i := by
  simp [ambHom, coe_nfU]

/-- The coefficient functionals dual to the normal-form monomials. -/
def coeffFun : ℕ ⊕ ℤ × ℕ → Amb →ₗ[ℚ] ℚ
  | .inl n => (Polynomial.lcoeff ℚ n).comp (LinearMap.fst ℚ ℚ[X] (ℤ → ℚ[X]))
  | .inr (i, a) => (Polynomial.lcoeff ℚ (a + 1)).comp
      ((LinearMap.proj (R := ℚ) (φ := fun _ : ℤ ↦ ℚ[X]) i).comp
        (LinearMap.snd ℚ ℚ[X] (ℤ → ℚ[X])))

/-- The coefficient functionals are dual to the images of the normal-form monomials. -/
theorem coeffFun_ambHom_nfMonomial (k j : ℕ ⊕ ℤ × ℕ) :
    coeffFun k (ambHom (nfMonomial j)) = if j = k then 1 else 0 := by
  rcases k with n | ⟨i, a⟩ <;> rcases j with m | ⟨i', b⟩
  · simp [coeffFun, nfMonomial, ambT, Polynomial.coeff_X_pow, eq_comm]
  · simp [coeffFun, nfMonomial, ambU]
  · simp only [coeffFun, nfMonomial, map_pow, ambHom_t, ambT, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.snd_apply, Prod.pow_snd, LinearMap.coe_proj,
      Function.eval, Pi.pow_apply, Polynomial.lcoeff_apply, reduceCtorEq, ite_false]
    rw [← map_pow, Polynomial.coeff_C]
    simp
  · simp only [coeffFun, nfMonomial, map_pow, ambHom_u, ambU, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.snd_apply, Prod.pow_snd, LinearMap.coe_proj,
      Function.eval, Pi.pow_apply, Polynomial.lcoeff_apply, Sum.inr.injEq, Prod.mk.injEq]
    by_cases hi : i = i'
    · subst hi
      simp [Polynomial.coeff_X_pow, eq_comm]
    · simp [hi, Ne.symm hi]

/-- **`A` embeds into `ℚ[X] × ∏_{i : ℤ} ℚ[X]`.** The normal-form monomials span `A`, and their
images are linearly independent. -/
theorem ambHom_injective : Function.Injective ambHom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hmem : x ∈ Submodule.span ℚ (Set.range nfMonomial) := span_nfMonomial ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
  suffices hc : c = 0 by simp [hc]
  ext k
  have h := congrArg (coeffFun k) hx
  simp only [Finsupp.sum, map_sum, map_smul, coeffFun_ambHom_nfMonomial, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finsupp.mem_support_iff, map_zero] at h
  by_cases hk : c k = 0
  · simp [hk]
  · simp [hk] at h

/-- **`A` is reduced**, being a subring of a product of polynomial rings over `ℚ`. -/
instance isReduced_A : IsReduced A :=
  isReduced_of_injective ambHom.toRingHom ambHom_injective

/-! ### The minimal primes of `A` -/

/-- The projection to the line `u_i = 0`: `t ↦ X`, `u_i ↦ 0`. -/
def lineHom : A →ₐ[ℚ] ℚ[X] := (AlgHom.fst ℚ ℚ[X] (ℤ → ℚ[X])).comp ambHom

/-- The projection to the `i`-th axis `t = i`: `t ↦ i`, `u_j ↦ δ_{ij} X`. -/
def axisHom (i : ℤ) : A →ₐ[ℚ] ℚ[X] :=
  (Pi.evalAlgHom ℚ (fun _ : ℤ ↦ ℚ[X]) i).comp ((AlgHom.snd ℚ ℚ[X] (ℤ → ℚ[X])).comp ambHom)

@[simp] theorem lineHom_t : lineHom t = Polynomial.X := by simp [lineHom, ambT]

@[simp] theorem lineHom_u (i : ℤ) : lineHom (u i) = 0 := by simp [lineHom, ambU]

@[simp] theorem axisHom_t (i : ℤ) : axisHom i t = C (i : ℚ) := by simp [axisHom, ambT]

theorem axisHom_u (i j : ℤ) :
    axisHom i (u j) = Pi.single (M := fun _ : ℤ ↦ ℚ[X]) j Polynomial.X i := by
  simp [axisHom, ambU]

/-- The line `(u_i : i ∈ ℤ)` of `Spec A`, as a prime. -/
def linePrime : PrimeSpectrum A := ⟨RingHom.ker lineHom, RingHom.ker_isPrime _⟩

/-- The `i`-th axis `(t - i, u_j : j ≠ i)` of `Spec A`, as a prime. -/
def axisPrime (i : ℤ) : PrimeSpectrum A := ⟨RingHom.ker (axisHom i), RingHom.ker_isPrime _⟩

/-- A prime containing every `u_i` contains the line. -/
theorem ker_lineHom_le {p : Ideal A} (hp : ∀ i, u i ∈ p) : RingHom.ker lineHom ≤ p := by
  have h : (Ideal.Quotient.mkₐ ℚ p).comp ((Polynomial.aeval t).comp lineHom) =
      Ideal.Quotient.mkₐ ℚ p := by
    refine algHom_ext' ?_ fun i ↦ ?_
    · simp
    · simp only [AlgHom.coe_comp, Function.comp_apply, lineHom_u, map_zero]
      exact ((Ideal.Quotient.eq_zero_iff_mem).mpr (hp i)).symm
  intro x hx
  rw [RingHom.mem_ker] at hx
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have := congrArg (fun φ : A →ₐ[ℚ] A ⧸ p ↦ φ x) h
  simp only [AlgHom.coe_comp, Function.comp_apply, hx, map_zero,
    Ideal.Quotient.mkₐ_eq_mk] at this
  exact this.symm

/-- A prime containing `t - i` and every `u_j`, `j ≠ i`, contains the `i`-th axis. -/
theorem ker_axisHom_le {p : Ideal A} (i : ℤ) (ht : t - (i : A) ∈ p)
    (hp : ∀ j, j ≠ i → u j ∈ p) : RingHom.ker (axisHom i) ≤ p := by
  have h : (Ideal.Quotient.mkₐ ℚ p).comp ((Polynomial.aeval (u i)).comp (axisHom i)) =
      Ideal.Quotient.mkₐ ℚ p := by
    refine algHom_ext' ?_ fun j ↦ ?_
    · simp only [AlgHom.coe_comp, Function.comp_apply, axisHom_t, Polynomial.aeval_C,
        Ideal.Quotient.mkₐ_eq_mk]
      rw [Ideal.Quotient.eq]
      have : (algebraMap ℚ A (i : ℚ)) - t = -(t - (i : A)) := by simp
      rw [this]
      exact p.neg_mem ht
    · simp only [AlgHom.coe_comp, Function.comp_apply, axisHom_u]
      by_cases hj : j = i
      · subst hj
        simp
      · rw [Pi.single_eq_of_ne (Ne.symm hj), map_zero, map_zero]
        exact ((Ideal.Quotient.eq_zero_iff_mem).mpr (hp j hj)).symm
  intro x hx
  rw [RingHom.mem_ker] at hx
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have := congrArg (fun φ : A →ₐ[ℚ] A ⧸ p ↦ φ x) h
  simp only [AlgHom.coe_comp, Function.comp_apply, hx, map_zero,
    Ideal.Quotient.mkₐ_eq_mk] at this
  exact this.symm

/-- **Every minimal prime of `A` is the line or an axis.** -/
theorem minimalPrimes_subset (p : PrimeSpectrum A) (hp : p.asIdeal ∈ minimalPrimes A) :
    p = linePrime ∨ ∃ i, p = axisPrime i := by
  have hmin : ∀ q : PrimeSpectrum A, q.asIdeal ≤ p.asIdeal → p = q := fun q hq ↦
    PrimeSpectrum.ext (le_antisymm (hp.2 ⟨q.2, bot_le⟩ hq) hq)
  by_cases h : ∀ i, u i ∈ p.asIdeal
  · exact Or.inl (hmin linePrime (ker_lineHom_le h))
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have ht : t - (i : A) ∈ p.asIdeal :=
      (p.2.mem_or_mem (by rw [t_sub_mul_u]; exact p.asIdeal.zero_mem)).resolve_right hi
    refine Or.inr ⟨i, hmin (axisPrime i) (ker_axisHom_le i ht fun j hj ↦ ?_)⟩
    refine (p.2.mem_or_mem (by rw [t_sub_mul_u]; exact p.asIdeal.zero_mem)).resolve_left ?_
    intro htj
    have hdiff : algebraMap ℚ A ((j : ℚ) - i) ∈ p.asIdeal := by
      have : algebraMap ℚ A ((j : ℚ) - i) = (t - (i : A)) - (t - (j : A)) := by simp
      rw [this]
      exact p.asIdeal.sub_mem ht htj
    have hne : ((j : ℚ) - i) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hj)
    exact p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hdiff
      ((isUnit_iff_ne_zero.mpr hne).map (algebraMap ℚ A)))

/-- The `n`-th shift carries the `i`-th axis to the `(i - n)`-th. -/
theorem axisHom_comp_shift (i n : ℤ) : (axisHom i).comp (shift n) = axisHom (i - n) := by
  refine algHom_ext' ?_ fun j ↦ ?_
  · simp only [AlgHom.coe_comp, Function.comp_apply, shift_t, map_sub, map_intCast, axisHom_t]
    push_cast
    simp
  · simp only [AlgHom.coe_comp, Function.comp_apply, shift_u, axisHom_u, Pi.single_apply]
    by_cases h : i = j + n
    · simp [h]
    · have h' : ¬ i - n = j := by omega
      simp [h, h']

/-- In the prime spectrum: the shift by `n` carries the `i`-th axis to the `(i - n)`-th. -/
theorem comap_shift_axisPrime (i n : ℤ) :
    PrimeSpectrum.comap (shift n).toRingHom (axisPrime i) = axisPrime (i - n) := by
  refine PrimeSpectrum.ext (Ideal.ext fun x ↦ ?_)
  change axisHom i (shift n x) = 0 ↔ axisHom (i - n) x = 0
  rw [← axisHom_comp_shift i n]
  rfl

/-- A weakly associated point of `Spec A` is a minimal prime of `A`. -/
theorem mem_minimalPrimes_of_mem_schemeWeaklyAssociatedPoints (s : PrimeSpectrum A)
    (hs : s ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints (Spec (CommRingCat.of A))) :
    s.asIdeal ∈ minimalPrimes A := by
  have h1 : Stacks.Divisors.IsWeaklyAssociatedPoint
      (tilde (ModuleCat.of (CommRingCat.of A) (CommRingCat.of A))) s :=
    (isWeaklyAssociatedPoint_iff_of_iso (tildeSelf (R := CommRingCat.of A)) s).mpr hs
  have h2 := (isWeaklyAssociatedPoint_tilde_iff (R := CommRingCat.of A)
    (ModuleCat.of (CommRingCat.of A) (CommRingCat.of A)) s).mp h1
  rw [← weakAss_eq_minimalPrimes0EMA]
  exact h2

/-! ### The weakly associated points of `Y` -/

attribute [local instance] AlgebraicGeometry.Space.pointTopology

section Site

variable (B : BigFppfSite.{0}) (hS : B.Contains (Spec (.of ℚ)))

/-- The point of the chart `Spec A` with prime `s`. -/
abbrev chartPointOf (s : PrimeSpectrum A) :
    Space.points B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS)) :=
  (Space.pointsEquivScheme B (Spec (.of ℚ)) hS (chart B hS)).symm s

/-- The quotient map identifies a point of `Spec A` with its shifts. -/
theorem pointsMap_fmap_comap_shift (n : ℤ) (s : PrimeSpectrum A) :
    Space.pointsMap B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS)) (fmap B hS).hom
        (chartPointOf B hS (PrimeSpectrum.comap (shift n).toRingHom s)) =
      Space.pointsMap B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS)) (fmap B hS).hom
        (chartPointOf B hS s) := by
  have hm : chartPointOf B hS (PrimeSpectrum.comap (shift n).toRingHom s) =
      Space.pointsMap B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS))
        (yoneda.map (Space.siteActionHom (Multiplicative ℤ) B hS (chart B hS)
          (chartAction B hS) (Multiplicative.ofAdd n))) (chartPointOf B hS s) := by
    have key : ∀ r : PrimeSpectrum A,
        Space.pointsToScheme B (Spec (.of ℚ)) hS (chart B hS) (chartPointOf B hS r) = r :=
      fun r ↦ (Space.pointsEquivScheme B (Spec (.of ℚ)) hS (chart B hS)).apply_symm_apply r
    refine Space.injective_pointsToScheme B (Spec (.of ℚ)) hS (chart B hS) ?_
    rw [Space.pointsToScheme_pointsMap_yoneda, key, key, toScheme_map_siteActionHom_eq,
      shiftAut_hom_left]
    change _ = (Spec.map (CommRingCat.ofHom (shift n).toRingHom)).base s
    rw [Spec.map_base]
    rfl
  have hcomp := Space.pointsMap_comp_apply B (Spec (.of ℚ)) hS
    (yoneda.map (Space.siteActionHom (Multiplicative ℤ) B hS (chart B hS) (chartAction B hS)
      (Multiplicative.ofAdd n)))
    (Space.actionProjection (Multiplicative ℤ) B hS (chart B hS) (chartAction B hS))
    (chartPointOf B hS s)
  rw [Space.siteActionHom_comp_actionProjection] at hcomp
  rw [hm, fmap_hom, ← hcomp]

/-- `f : X ⟶ Y` is étale. -/
theorem isEtale_fmap : Space.IsEtale B (Spec (.of ℚ)) hS (fmap B hS).hom :=
  Space.isEtale_of_presheaf_etale B (Spec (.of ℚ)) hS (isEtaleChart_fmap B hS)

/-- `f : X ⟶ Y` is surjective on points. -/
theorem surjective_pointsMap_fmap :
    Function.Surjective
      (Space.pointsMap B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS)) (fmap B hS).hom) := by
  have h := Space.quotientMap_surjective_unconditional B (Spec (.of ℚ)) hS
    (relSource B hS) (relTarget B hS)
  rw [Space.quotientMap_eq_actionProjection (Multiplicative ℤ) B hS (chart B hS)
    (chartAction B hS) (contains_relationScheme B hS)] at h
  exact Space.isSurjective_of_presheafSurjective B (Spec (.of ℚ)) hS _ h

/-- A weakly associated point of the represented space `X = Spec A` lies over a weakly
associated point of the scheme `Spec A`. -/
theorem mem_schemeWeaklyAssociatedPoints_of_mem_Xsp (s : PrimeSpectrum A)
    (hs : chartPointOf B hS s ∈ Space.weaklyAssociatedPointsOfSpace B (Spec (.of ℚ)) hS
      (Xsp B hS)) :
    s ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints (Spec (CommRingCat.of A)) := by
  have h := (Space.isWeaklyAssociatedPoint_restrictToChart_idEtaleChart_iff B (Spec (.of ℚ)) hS
    (chart B hS) _ s).mpr hs
  exact (isWeaklyAssociatedPoint_iff_of_iso
    (Space.restrictToChartUnitIso B (Spec (.of ℚ)) hS _ (Xsp B hS).2
      (Space.idEtaleChart B (Spec (.of ℚ)) hS (chart B hS))) s).mp h

/-- **The weakly associated points of `Y = Spec A / ℤ` lie in a two-element set**: the images
of the line and of the `0`-th axis. -/
theorem weaklyAssociatedPointsOfSpace_Ysp_subset :
    Space.weaklyAssociatedPointsOfSpace B (Spec (.of ℚ)) hS (Ysp B hS) ⊆
      {Space.pointsMap B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS)) (fmap B hS).hom
          (chartPointOf B hS linePrime),
        Space.pointsMap B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS)) (fmap B hS).hom
          (chartPointOf B hS (axisPrime 0))} := by
  intro y hy
  obtain ⟨x, rfl⟩ := surjective_pointsMap_fmap B hS y
  have hx : x ∈ Space.weaklyAssociatedPointsOfSpace B (Spec (.of ℚ)) hS (Xsp B hS) :=
    (Space.mem_weaklyAssociatedPointsOfSpace_iff_of_isEtale B (Spec (.of ℚ)) hS (fmap B hS)
      (isEtale_fmap B hS) x).mpr hy
  set s := Space.pointsEquivScheme B (Spec (.of ℚ)) hS (chart B hS) x with hsdef
  have hxs : x = chartPointOf B hS s := by simp [hsdef]
  rw [hxs] at hx ⊢
  rcases minimalPrimes_subset s (mem_minimalPrimes_of_mem_schemeWeaklyAssociatedPoints s
      (mem_schemeWeaklyAssociatedPoints_of_mem_Xsp B hS s hx)) with h | ⟨i, h⟩
  · exact Or.inl (by rw [h])
  · refine Or.inr ?_
    rw [h, ← pointsMap_fmap_comap_shift B hS i (axisPrime i), comap_shift_axisPrime, sub_self]
    rfl

/-- **`WeakAss(Y)` is finite.** -/
theorem weaklyAssociatedPointsOfSpace_Ysp_finite :
    (Space.weaklyAssociatedPointsOfSpace B (Spec (.of ℚ)) hS (Ysp B hS)).Finite :=
  (Set.toFinite _).subset (weaklyAssociatedPointsOfSpace_Ysp_subset B hS)

/-- The flat locus of `Fm` over `Y` is not open in `|X|`: its trace on a fibre is not open. -/
theorem not_isOpen_flatLocus_Fm :
    ¬ IsOpen (Space.flatLocus B (Spec (.of ℚ)) hS (Xsp B hS).2 (fmap B hS).hom (Fm B hS)) :=
  fun h ↦ not_isOpen_setOf_mem_flatLocus B hS (continuous_subtype_val.isOpen_preimage _ h)

end Site

/-- **Stacks 0DLR is false as printed.** There is a morphism `f : X ⟶ Y` of algebraic spaces
locally of finite presentation and a quasi-coherent module of finite type on `X`, such that
the weakly associated points of `Y` are locally finite in `|Y|` (condition (3) of the source),
and the flat locus of the module over `Y` is not open in `|X|`. -/
theorem exists_not_isOpen_flatLocus :
    ∃ (B : BigFppfSite.{0}) (S : Scheme.{0}) (hS : B.Contains S)
      (X Y : AlgebraicSpaces B S hS) (f : X ⟶ Y)
      (F : Space.Modules.{0, 0} B S hS X.1 X.2),
      Space.IsLocallyOfFinitePresentation B S hS f.hom ∧ F.IsQuasicoherentOnSite ∧
        SheafOfModules.IsFiniteTypeOnSite F ∧
        (∀ y : Space.points B S hS Y.1, ∃ W : Set (Space.points B S hS Y.1),
          IsOpen W ∧ y ∈ W ∧ (Space.weaklyAssociatedPointsOfSpace B S hS Y ∩ W).Finite) ∧
        ¬ IsOpen (Space.flatLocus B S hS X.2 f.hom F) := by
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing ({Spec (CommRingCat.of ℚ)} : Set Scheme.{0})
  have hS : B.Contains (Spec (.of ℚ)) := hB _ (by simp)
  refine ⟨B, Spec (.of ℚ), hS, Xsp B hS, Ysp B hS, fmap B hS, Fm B hS,
    Space.isLocallyOfFinitePresentation_of_isEtale B (Spec (.of ℚ)) hS (isEtale_fmap B hS),
    inferInstance, ?_, fun y ↦ ⟨Set.univ, isOpen_univ, Set.mem_univ y,
      (weaklyAssociatedPointsOfSpace_Ysp_finite B hS).subset Set.inter_subset_left⟩,
    not_isOpen_flatLocus_Fm B hS⟩
  exact Space.isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence B (Spec (.of ℚ)) hS
    (chart B hS) Mt (inferInstanceAs (SheafOfModules.IsQuasicoherent Mt))
    (inferInstanceAs (SheafOfModules.IsFiniteType Mt))

end Stacks.Examples.NonOpenFlatLocusWeaklyAssociated

end
