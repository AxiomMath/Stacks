module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.ProjectiveLineCover.Finite

/-!
# The multiplication of binary forms is surjective

The morphism `ℙ¹ × ℙⁿ ⟶ ℙⁿ⁺¹` of `Stacks.ProjectiveLineCover.multiplication` is surjective. It is
proper, so its image is closed, and it suffices that the image contain a point whose closure is
all of `ℙⁿ⁺¹`. Such a point is the image of the generic point of the chart `D₊(c₀)`: over an
algebraically closed field `L` containing the fraction field of `ℤ[c₁/c₀, …, c_{n+1}/c₀]`, the
generic binary form `Tⁿ⁺¹ + (c₁/c₀) Tⁿ + … + c_{n+1}/c₀` has a linear factor `T + x`, so it is
`(T + x) A(T)` with `A` monic of degree `n`. The corresponding `L`-point of the chart
`x ≠ 0`, `a₀ ≠ 0` of `ℙ¹ × ℙⁿ` gives a ring homomorphism `σ` out of the chart ring whose
composite with the chart map of the multiplication is the embedding of `ℤ[c/c₀]` into `L`; the
kernel of `σ` is therefore a prime lying over the zero ideal.

## Main results

* `Stacks.ProjectiveLineCover.surjective_multiplication`: the multiplication is surjective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.ProjectiveCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace Stacks.ProjectiveLineCover

private instance : IsDomain (ULift.{u} ℤ) :=
  MulEquiv.isDomain ℤ (ULift.ringEquiv (R := ℤ)).toMulEquiv

variable (n : ℕ)

/-- Any two ring homomorphisms out of `ULift ℤ` agree. -/
theorem ringHom_ulift_int_ext {L : Type*} [Ring L] (f g : ULift.{u} ℤ →+* L) : f = g := by
  have h := RingHom.ext_int (f.comp (ULift.ringEquiv (R := ℤ)).symm.toRingHom)
    (g.comp (ULift.ringEquiv (R := ℤ)).symm.toRingHom)
  refine RingHom.ext fun r => ?_
  obtain ⟨k⟩ := r
  exact DFunLike.congr_fun h k

/-- The chart ring `ℤ[c₁/c₀, …, c_{n+1}/c₀]` of `ℙⁿ⁺¹_ℤ`. -/
abbrev targetChart : Type u :=
  Away (Stacks.ProjectiveCohomology.polyGrading (ULift.{u} ℤ) (n + 1))
    (X 0 : MvPolynomial (Fin (n + 2)) (ULift.{u} ℤ))

/-- The form `a₀ + t · 0`, image of `c₀` under the substitution. -/
abbrev ellX : MvPolynomial (Fin (n + 1)) (chartRing.{u} 0) :=
  mulHom n 1 coordT (X 0 : MvPolynomial (Fin (n + 2)) (ULift.{u} ℤ))

/-- The form `ellX` is homogeneous of degree one. -/
theorem ellX_mem : ellX.{u} n ∈ Stacks.ProjectiveCohomology.polyGrading (chartRing.{u} 0) n 1 :=
  (mulHom n 1 coordT).2 (X_mem_one (ULift.{u} ℤ) (n + 1) 0)

/-- The chart ring `B₀[a]_{(a₀)}` of the piece `x ≠ 0` of `ℙ¹ × ℙⁿ`. -/
abbrev sourceChart : Type u :=
  Away (Stacks.ProjectiveCohomology.polyGrading (chartRing.{u} 0) n) (ellX.{u} n)

/-- The chart map of the multiplication at `c₀`. -/
abbrev chartMap : targetChart.{u} n →+* sourceChart.{u} n :=
  Away.map (mulHom n 1 coordT) (X 0 : MvPolynomial (Fin (n + 2)) (ULift.{u} ℤ))

/-- The chart coordinate `c_j / c₀` is the affine coordinate `tau`. -/
theorem chartCoord_eq_tau (j : {j : Fin (n + 2) // j ≠ 0}) :
    chartCoord (ULift.{u} ℤ) (n + 1) 0 j = tau.{u} n 0 j := by
  ext
  simp [chartCoord, tau, Away.val_mk, var, j.1.2]

section Point

variable {L : Type u} [Field L] (ι : targetChart.{u} n →+* L) (x : L)

/-- The coordinate `c₀ / c₀` maps to `1`. -/
private theorem map_tau_zero : ι (tau.{u} n 0 0) = 1 :=
  (congrArg ι (tau_self n 0)).trans (map_one ι)

/-- The coefficients `q_j` of the cofactor `A`: `q₀ = 1`, `q_{j+1} = ι(c_{j+1}/c₀) - x q_j`. -/
def cof : ℕ → L
  | 0 => 1
  | j + 1 => ι (tau.{u} n 0 (j + 1)) - x * cof j

/-- Closed form of the cofactor coefficients: `q_j = Σ_{m ≤ j} ι(c_m/c₀) (-x)^{j-m}`. -/
theorem cof_eq_sum (j : ℕ) :
    cof n ι x j = ∑ m ∈ Finset.range (j + 1), ι (tau.{u} n 0 m) * (-x) ^ (j - m) := by
  refine eq_sum_of_recursion (RingHom.id L) x (cof n ι x) (fun m => ι (tau.{u} n 0 m)) ?_ ?_ j
  · simp [cof, map_tau_zero]
  · intro m
    simp [cof]

/-- The generic binary form `Σ_m (c_m/c₀) (-X)^{n+1-m}`, read in `L`. -/
def genericForm : Polynomial L :=
  ∑ m ∈ Finset.range (n + 1 + 1), Polynomial.C (ι (tau.{u} n 0 m)) * (-Polynomial.X) ^ (n + 1 - m)

/-- The generic binary form is not constant. -/
theorem genericForm_degree_ne_zero : (genericForm n ι).degree ≠ 0 := by
  intro h
  have hc := coeff_sum_neg_X_pow (fun m => ι (tau.{u} n 0 m)) (n + 1) 0 (Nat.zero_le _)
  rw [map_tau_zero, one_mul, Nat.sub_zero] at hc
  have hnd : (genericForm n ι).natDegree = 0 := Polynomial.natDegree_eq_zero_iff_degree_le_zero.2
    (h ▸ le_rfl)
  have := Polynomial.coeff_eq_zero_of_natDegree_lt (p := genericForm n ι) (n := n + 1)
    (by omega)
  rw [genericForm, hc] at this
  exact (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) this

/-- If `x` is a root of the generic binary form, then the coefficient `q_{n+1}` vanishes. -/
theorem cof_top (hx : (genericForm n ι).eval x = 0) : cof n ι x (n + 1) = 0 := by
  rw [cof_eq_sum, ← hx, genericForm, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp

/-- The coefficient map `B₀ = ℤ[t] → L`, `t ↦ x`. -/
def lineEval : chartRing.{u} 0 →+* L :=
  (eval₂Hom (fromULiftInt L) fun _ => x).comp
    (chartEquiv (ULift.{u} ℤ) 1 0).symm.toRingHom

/-- The map `lineEval x` sends the coordinate `t` to `x`. -/
theorem lineEval_coordT : lineEval x coordT = x := by
  have h : (chartEquiv (ULift.{u} ℤ) 1 0).symm coordT = X ⟨1, by decide⟩ := by
    rw [RingEquiv.symm_apply_eq, chartEquiv_apply, chartHom_X]
    rfl
  simp only [lineEval, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, h,
    eval₂Hom_X']

/-- The polynomial map `B₀[a₀, …, aₙ] → L`, `a_j ↦ q_j`. -/
def polyEval : MvPolynomial (Fin (n + 1)) (chartRing.{u} 0) →+* L :=
  eval₂Hom (lineEval x) fun j => cof n ι x j

/-- If `x` is a root of the generic binary form, then `polyEval` sends `var n m` to `q_m` for
`m ≤ n + 1`. -/
theorem polyEval_var (hx : (genericForm n ι).eval x = 0) (m : ℕ) (hm : m ≤ n + 1) :
    polyEval n ι x (var n m) = cof n ι x m := by
  by_cases h : m < n + 1
  · simp [polyEval, var, h]
  · obtain rfl : m = n + 1 := by omega
    simp [var, cof_top n ι x hx]

/-- If `x` is a root of the generic binary form, then `polyEval` sends the `k`-th coefficient of
the product form to `ι(c_k/c₀)`. -/
theorem polyEval_mulForm (hx : (genericForm n ι).eval x = 0) (k : Fin (n + 2)) :
    polyEval n ι x (mulForm n 1 coordT k) = ι (tau.{u} n 0 k) := by
  rw [mulForm]
  by_cases hk : (k : ℕ) = 0
  · simp only [hk, if_true, mul_zero, add_zero, map_one, one_mul]
    rw [polyEval_var n ι x hx 0 (by omega)]
    exact (map_tau_zero n ι).symm
  · simp only [hk, if_false, map_add, map_mul, map_one, one_mul]
    rw [polyEval_var n ι x hx k (by omega), polyEval_var n ι x hx (k - 1) (by omega)]
    rw [show polyEval n ι x (C coordT) = x by simp [polyEval, lineEval_coordT]]
    obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = j + 1 := ⟨k - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel, cof]
    ring

/-- If `x` is a root of the generic binary form, then `polyEval` sends `ellX` to `1`. -/
theorem polyEval_ellX (hx : (genericForm n ι).eval x = 0) : polyEval n ι x (ellX.{u} n) = 1 := by
  rw [ellX, mulHom_X, polyEval_mulForm n ι x hx]
  exact map_tau_zero n ι

/-- The `L`-point of the chart `B₀[a]_{(a₀)}`: the extension of `polyEval` over the localization,
restricted to degree zero. -/
def chartPoint (hx : (genericForm n ι).eval x = 0) : sourceChart.{u} n →+* L :=
  (Localization.awayLift (polyEval n ι x) (ellX.{u} n)
      (by rw [polyEval_ellX n ι x hx]; exact isUnit_one)).comp
    (algebraMap (sourceChart.{u} n)
      (Localization (Submonoid.powers (ellX.{u} n))))

/-- The point `chartPoint` sends the fraction `a / ellX ^ k` to `polyEval a`. -/
theorem chartPoint_mk (hx : (genericForm n ι).eval x = 0) (k : ℕ)
    (a : MvPolynomial (Fin (n + 1)) (chartRing.{u} 0))
    (ha : a ∈ Stacks.ProjectiveCohomology.polyGrading (chartRing.{u} 0) n (k • 1)) :
    chartPoint n ι x hx (Away.mk _ (ellX_mem n) k a ha) = polyEval n ι x a := by
  set θ := Localization.awayLift (polyEval n ι x) (ellX.{u} n)
    (by rw [polyEval_ellX n ι x hx]; exact isUnit_one)
  have key : (Away.mk _ (ellX_mem n) k a ha).val *
      algebraMap (MvPolynomial (Fin (n + 1)) (chartRing.{u} 0)) _ (ellX.{u} n ^ k) =
      algebraMap (MvPolynomial (Fin (n + 1)) (chartRing.{u} 0)) _ a := by
    rw [Away.val_mk, ← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
      Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [OneMemClass.coe_one, one_mul, mul_one]; ring⟩
  have h2 := congrArg θ key
  rwa [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq,
    map_pow, polyEval_ellX n ι x hx, one_pow, mul_one] at h2

/-- **The `L`-point lies over `ι`.** -/
theorem chartPoint_comp_chartMap (hx : (genericForm n ι).eval x = 0) :
    (chartPoint n ι x hx).comp (chartMap.{u} n) = ι := by
  have hsurj := chartHom_surjective (ULift.{u} ℤ) (n + 1) 0
  suffices h : ((chartPoint n ι x hx).comp (chartMap.{u} n)).comp
      (chartHom (ULift.{u} ℤ) (n + 1) 0) = ι.comp (chartHom (ULift.{u} ℤ) (n + 1) 0) by
    refine RingHom.ext fun z => ?_
    obtain ⟨p, rfl⟩ := hsurj z
    exact congrArg (fun φ => φ p) h
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
  · exact DFunLike.congr_fun (ringHom_ulift_int_ext (L := L)
      ((((chartPoint n ι x hx).comp (chartMap.{u} n)).comp
        (chartHom (ULift.{u} ℤ) (n + 1) 0)).comp C)
      ((ι.comp (chartHom (ULift.{u} ℤ) (n + 1) 0)).comp C)) r
  · simp only [RingHom.comp_apply, chartHom_X]
    rw [chartCoord_eq_tau]
    conv_lhs => rw [← chartCoord_eq_tau, chartCoord, chartMap, Away.map_mk]
    rw [chartPoint_mk, mulHom_X, polyEval_mulForm n ι x hx]

end Point

/-- **Some prime of the chart ring of `ℙ¹ × ℙⁿ` lies over the zero ideal.** -/
theorem exists_comap_chartMap_eq_bot :
    ∃ p : PrimeSpectrum (sourceChart.{u} n),
      PrimeSpectrum.comap (chartMap.{u} n) p = ⟨⊥, Ideal.isPrime_bot⟩ := by
  set R := targetChart.{u} n
  let L := AlgebraicClosure (FractionRing R)
  let ι : R →+* L := (algebraMap (FractionRing R) L).comp (algebraMap R (FractionRing R))
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (genericForm n ι) (genericForm_degree_ne_zero n ι)
  rw [Polynomial.IsRoot.def] at hx
  refine ⟨⟨RingHom.ker (chartPoint n ι x hx), RingHom.ker_isPrime _⟩, ?_⟩
  ext1
  show (RingHom.ker (chartPoint n ι x hx)).comap (chartMap.{u} n) = ⊥
  rw [RingHom.comap_ker, chartPoint_comp_chartMap]
  exact (RingHom.injective_iff_ker_eq_bot ι).1
    ((algebraMap (FractionRing R) L).injective.comp (IsFractionRing.injective R (FractionRing R)))

/-- **The image of the multiplication contains a point whose closure is everything.** -/
theorem exists_dense_point_mem_range :
    ∃ y, closure {y} = (Set.univ : Set (projectiveSpaceAtUniverse.{u} (n + 1))) ∧
      y ∈ Set.range (multiplication.{u} n) := by
  set R := targetChart.{u} n
  obtain ⟨p, hp⟩ := exists_comap_chartMap_eq_bot.{u} n
  set bot : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  set ιR := Proj.awayι (Stacks.ProjectiveCohomology.polyGrading (ULift.{u} ℤ) (n + 1))
    (X 0 : MvPolynomial (Fin (n + 2)) (ULift.{u} ℤ)) (X_mem_one (ULift.{u} ℤ) (n + 1) 0)
    Nat.one_pos
  set ιS := Proj.awayι (Stacks.ProjectiveCohomology.polyGrading (chartRing.{u} 0) n)
    (ellX.{u} n) (ellX_mem n) Nat.one_pos
  refine ⟨ιR bot, ?_, ?_⟩
  · have hbot : closure ({bot} : Set (PrimeSpectrum R)) = Set.univ := by
      rw [PrimeSpectrum.closure_singleton]
      exact PrimeSpectrum.zeroLocus_bot
    have hrange : Set.range ιR ⊆ closure {ιR bot} := by
      rintro _ ⟨q, rfl⟩
      have hq : q ∈ closure ({bot} : Set (PrimeSpectrum R)) := hbot ▸ Set.mem_univ q
      exact specializes_iff_mem_closure.1
        ((specializes_iff_mem_closure.2 hq).map ιR.continuous)
    have hdense : Dense (Set.range ιR) :=
      (ιR.isOpenEmbedding.isOpen_range).dense ⟨_, ⟨bot, rfl⟩⟩
    exact Set.eq_univ_of_univ_subset
      (hdense.closure_eq ▸ closure_minimal hrange isClosed_closure)
  · have hsq := Proj.awayι_comp_map (mulHom n 1 coordT) (irrelevant_le_map_mulHom_one_left n coordT)
      Nat.one_pos (X 0 : MvPolynomial (Fin (n + 2)) (ULift.{u} ℤ))
      (X_mem_one (ULift.{u} ℤ) (n + 1) 0)
    have h1 : mulMapX.{u} n coordT (ιS p) = ιR bot := by
      rw [← hp]
      show (ιS ≫ mulMapX.{u} n coordT) p = _
      rw [mulMapX, hsq]
      rfl
    have h2 : (projModelIso (chartRing.{u} 0) n).hom ≫ (pieceIso.{u} n 0).inv ≫ pieceι n 0 ≫
        multiplication.{u} n = mulMapX.{u} n coordT := by
      rw [pieceι_multiplication]
      simp [chartMul]
      rfl
    refine ⟨pieceι n 0 ((pieceIso.{u} n 0).inv ((projModelIso (chartRing.{u} 0) n).hom (ιS p))),
      ?_⟩
    rw [← h1, ← h2]
    rfl

/-- **The multiplication of binary forms is surjective.** -/
instance surjective_multiplication : Surjective (multiplication.{u} n) := by
  obtain ⟨y, hy, hmem⟩ := exists_dense_point_mem_range.{u} n
  refine ⟨fun z => ?_⟩
  have hz : z ∈ closure {y} := hy ▸ Set.mem_univ z
  exact closure_minimal (Set.singleton_subset_iff.2 hmem)
    (multiplication.{u} n).isClosedMap.isClosed_range hz

end Stacks.ProjectiveLineCover
