module

public import StacksFrontier.AlgebraicGeometry.TwoGeneratorSquare
public import StacksCore.Tactic.StacksAttribute

/-!
# The square-zero kernel of the two-generator almost blowup

Let `f₁, f₂` be elements of a commutative ring `A` and let
`X' = Proj (A[T₀,T₁]/(f₂T₀-f₁T₁)) ⟶ X = Spec A` be the modification of the two-generator
almost blowup square. Pulling global functions back along it is a ring map
`Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})` whose kernel is an ideal of square zero.

## Main results

* `Stacks.AlmostBlowUp.modificationToBase_ker_sq_eq_bot`: the kernel of the map on global
  sections squares to zero.

## Implementation notes

A global function killed by the modification is already killed on each of the two standard
affine charts `D₊(T₀)` and `D₊(T₁)`. Dehomogenizing a chart turns the vanishing into
divisibility in `A[X]` by the linear form `f₂ - f₁X`, respectively `f₁ - f₂X`, and comparing
the coefficients of the two cofactors gives the product of two such functions is zero.

Both charts are handled by the one lemma `Stacks.AlmostBlowUp.coeff_rec_of_C_eq_sub_mul`,
applied with `f₁` and `f₂` interchanged.

## References

* [Stacks Project, Tag 0EVJ](https://stacks.math.columbia.edu/tag/0EVJ)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Stacks.AlmostBlowUp

universe u

variable {A : Type u} [CommRing A]

/-! ### Divisibility on the two standard charts -/

/-- If `C a = (C f₂ - C f₁ * X) * p` in `A[X]`, then `a = f₂ * p.coeff 0`, and the
coefficients of `p` satisfy the recursion `f₁ * p.coeff i = f₂ * p.coeff (i + 1)`.
Interchanging `f₁` and `f₂` gives the statement for the other standard chart. -/
private lemma coeff_rec_of_C_eq_sub_mul (f₁ f₂ a : A) (p : Polynomial A)
    (h : Polynomial.C a = (Polynomial.C f₂ - Polynomial.C f₁ * Polynomial.X) * p) :
    a = f₂ * p.coeff 0 ∧ ∀ i, f₁ * p.coeff i = f₂ * p.coeff (i + 1) := by
  refine ⟨?_, fun i => ?_⟩
  · simpa using congrArg (fun q : Polynomial A => q.coeff 0) h
  · have hi := congrArg (fun q : Polynomial A => q.coeff (i + 1)) h
    have hcoeff : 0 = f₂ * p.coeff (i + 1) - f₁ * p.coeff i := by
      calc
        0 = (Polynomial.C a).coeff (i + 1) := by simp
        _ = ((Polynomial.C f₂ - Polynomial.C f₁ * Polynomial.X) * p).coeff (i + 1) := hi
        _ = f₂ * p.coeff (i + 1) - f₁ * p.coeff i := by
          rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
            show (Polynomial.C f₁ * Polynomial.X) * p =
              Polynomial.C f₁ * (Polynomial.X * p) from mul_assoc _ _ _,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
    linear_combination hcoeff

/-- Dehomogenization along the `j`-th homogeneous coordinate: it sends `Tⱼ` to `1` and the
other coordinate to the variable of `A[X]`. -/
private def dehomogenize (j : Fin 2) : MvPolynomial (Fin 2) A →+* Polynomial A :=
  MvPolynomial.eval₂Hom Polynomial.C fun i => if i = j then 1 else Polynomial.X

/-- A constant annihilated by a power of `Tᵢ` in `A[T₀,T₁]/(f₂T₀-f₁T₁)` is a multiple of the
dehomogenized relation `f₂ * T₀ - f₁ * T₁` after dehomogenizing the chart `D₊(Tᵢ)`. -/
private lemma exists_dehomogenize_eq_of_pow_mul_C_eq_zero (f₁ f₂ a : A) (i : Fin 2) (n : ℕ)
    (h : Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X i) ^ n *
      Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C a) = 0) :
    ∃ q : MvPolynomial (Fin 2) A, Polynomial.C a = dehomogenize i q *
      (Polynomial.C f₂ * dehomogenize i (MvPolynomial.X 0) -
        Polynomial.C f₁ * dehomogenize i (MvPolynomial.X 1)) := by
  have hmem : MvPolynomial.X i ^ n * MvPolynomial.C a ∈ relationIdeal A f₁ f₂ := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul, map_pow] using h
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨q, ?_⟩
  simpa [dehomogenize, MvPolynomial.eval₂Hom_X'] using (congrArg (dehomogenize i) hq).symm

/-- A constant annihilated by a power of `T₀` in `A[T₀,T₁]/(f₂T₀-f₁T₁)` is divisible by
`f₂ - f₁X` after dehomogenizing the chart `D₊(T₀)`. -/
private lemma exists_factor_chart_zero (f₁ f₂ a : A) (n : ℕ)
    (h : Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X (0 : Fin 2)) ^ n *
      Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C a) = 0) :
    ∃ p : Polynomial A,
      Polynomial.C a = (Polynomial.C f₂ - Polynomial.C f₁ * Polynomial.X) * p := by
  obtain ⟨q, hq⟩ := exists_dehomogenize_eq_of_pow_mul_C_eq_zero f₁ f₂ a 0 n h
  refine ⟨dehomogenize 0 q, ?_⟩
  rw [hq]
  simp [dehomogenize]
  ring

/-- A constant annihilated by a power of `T₁` in `A[T₀,T₁]/(f₂T₀-f₁T₁)` is divisible by
`f₁ - f₂X` after dehomogenizing the chart `D₊(T₁)`. -/
private lemma exists_factor_chart_one (f₁ f₂ a : A) (n : ℕ)
    (h : Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X (1 : Fin 2)) ^ n *
      Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C a) = 0) :
    ∃ p : Polynomial A,
      Polynomial.C a = (Polynomial.C f₁ - Polynomial.C f₂ * Polynomial.X) * p := by
  obtain ⟨q, hq⟩ := exists_dehomogenize_eq_of_pow_mul_C_eq_zero f₁ f₂ a 1 n h
  refine ⟨-(dehomogenize 1 q), ?_⟩
  rw [hq]
  simp [dehomogenize]
  ring

/-! ### From vanishing on global sections to vanishing on a chart -/

/-- A global function on `Spec A` pulling back to zero on the modification pulls back to zero
in the degree-zero part of the localization at either homogeneous coordinate. -/
private lemma fromZero_eq_zero_of_global_kernel (f₁ f₂ a : A) (i : Fin 2)
    (hX : Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X i) ∈
      modificationGrading A f₁ f₂ 1)
    (hker : (Scheme.Γ.map (modificationToBase A f₁ f₂).op).hom
      ((Scheme.ΓSpecIso (.of A)).inv.hom a) = 0) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    HomogeneousLocalization.fromZeroRingHom (modificationGrading A f₁ f₂)
      (Submonoid.powers (Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X i)))
      ((twoGeneratorSquare A f₁ f₂).baseMap a) = 0 := by
  let 𝒮 := modificationGrading A f₁ f₂
  let _ : GradedRing 𝒮 := (twoGeneratorSquare A f₁ f₂).modificationGraded
  let x := Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X i)
  let φ : A →+* HomogeneousLocalization.Away 𝒮 x :=
    (HomogeneousLocalization.fromZeroRingHom 𝒮 (Submonoid.powers x)).comp
      (twoGeneratorSquare A f₁ f₂).baseMap
  have hdiag : Proj.awayι 𝒮 x hX (show 0 < 1 by decide) ≫ modificationToBase A f₁ f₂ =
      Spec.map (CommRingCat.ofHom φ) := by
    rw [modificationToBase, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    rfl
  have hcomp : Scheme.Γ.map (Spec.map (CommRingCat.ofHom φ)).op =
      Scheme.Γ.map (modificationToBase A f₁ f₂).op ≫
        Scheme.Γ.map (Proj.awayι 𝒮 x hX (show 0 < 1 by decide)).op := by
    rw [← hdiag, op_comp, ← Functor.map_comp]
  have hlocal : (Scheme.Γ.map (Spec.map (CommRingCat.ofHom φ)).op).hom
      ((Scheme.ΓSpecIso (.of A)).inv.hom a) = 0 := by
    rw [hcomp]
    rw [Scheme.Γ_map_op] at hker
    show (Scheme.Hom.appTop (Proj.awayι 𝒮 x hX (show 0 < 1 by decide))).hom
      ((Scheme.Hom.appTop (modificationToBase A f₁ f₂)).hom
        ((Scheme.ΓSpecIso (.of A)).inv.hom a)) = 0
    exact (congrArg (Scheme.Hom.appTop (Proj.awayι 𝒮 x hX (show 0 < 1 by decide))).hom
      hker).trans (map_zero _)
  have hnatApply := congrArg (fun f : CommRingCat.of A ⟶
      Γ(Spec (.of (HomogeneousLocalization.Away 𝒮 x)), ⊤) => f.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  change (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒮 x))).inv.hom (φ a) =
      (Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom φ))).hom
        ((Scheme.ΓSpecIso (.of A)).inv.hom a) at hnatApply
  have haway : (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒮 x))).inv.hom (φ a) = 0 :=
    hnatApply.trans hlocal
  have hφ : φ a = 0 := by
    simpa using congrArg (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒮 x))).hom.hom haway
  simpa [φ, RingHom.comp_apply] using hφ

/-- If a global function dies in the degree-zero part of the localization at a homogeneous
coordinate, then some power of that coordinate annihilates it in the modification ring. -/
private lemma exists_pow_mul_C_eq_zero_of_fromZero_eq_zero (f₁ f₂ a : A) (i : Fin 2)
    (h : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      HomogeneousLocalization.fromZeroRingHom (modificationGrading A f₁ f₂)
        (Submonoid.powers (Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X i)))
        ((twoGeneratorSquare A f₁ f₂).baseMap a) = 0) :
    ∃ n : ℕ, Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X i) ^ n *
      Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C a) = 0 := by
  let _ := (twoGeneratorSquare A f₁ f₂).modificationGraded
  let x := Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X i)
  have hv := congrArg (HomogeneousLocalization.val (𝒜 := modificationGrading A f₁ f₂)
    (x := Submonoid.powers x)) h
  dsimp only [HomogeneousLocalization.fromZeroRingHom] at hv
  change HomogeneousLocalization.val (HomogeneousLocalization.mk
    ⟨0, (twoGeneratorSquare A f₁ f₂).baseMap a, 1, one_mem _⟩) =
      HomogeneousLocalization.val 0 at hv
  rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero,
    Localization.mk_eq_mk'_apply] at hv
  obtain ⟨d, hd⟩ := (IsLocalization.mk'_eq_zero_iff
    (S := Localization (Submonoid.powers x)) _ _).mp hv
  obtain ⟨n, hn⟩ :=
    (Submonoid.mem_powers_iff (d : modificationRing A f₁ f₂) x).mp d.property
  refine ⟨n, ?_⟩
  have hd' : x ^ n *
      ((twoGeneratorSquare A f₁ f₂).baseMap a : modificationRing A f₁ f₂) = 0 := by
    simpa [hn] using hd
  rwa [(twoGeneratorSquare A f₁ f₂).baseMap_apply a] at hd'

/-- Two global functions, one divisible by `f₂ - f₁X` and the other by `f₁ - f₂X` after
dehomogenizing, have product zero. -/
private lemma mul_eq_zero_of_chart_factors (f₁ f₂ a a' : A) (p q : Polynomial A)
    (hp : Polynomial.C a = (Polynomial.C f₂ - Polynomial.C f₁ * Polynomial.X) * p)
    (hq : Polynomial.C a' = (Polynomial.C f₁ - Polynomial.C f₂ * Polynomial.X) * q) :
    a * a' = 0 := by
  obtain ⟨ha, hpr⟩ := coeff_rec_of_C_eq_sub_mul f₁ f₂ a p hp
  obtain ⟨ha', hqr⟩ := coeff_rec_of_C_eq_sub_mul f₂ f₁ a' q hq
  set N := p.natDegree + 1
  have htail : p.coeff N = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega
  have hstep (i : ℕ) :
      f₁ * f₂ * p.coeff i * q.coeff i =
        f₁ * f₂ * p.coeff (i + 1) * q.coeff (i + 1) := by
    linear_combination f₂ * q.coeff i * hpr i + f₂ * p.coeff (i + 1) * hqr i
  have hiter (n : ℕ) :
      f₁ * f₂ * p.coeff 0 * q.coeff 0 = f₁ * f₂ * p.coeff n * q.coeff n := by
    induction n with
    | zero => rfl
    | succ n ih => exact ih.trans (hstep n)
  calc
    a * a' = f₁ * f₂ * p.coeff 0 * q.coeff 0 := by linear_combination a' * ha + f₂ * p.coeff 0 * ha'
    _ = f₁ * f₂ * p.coeff N * q.coeff N := hiter N
    _ = 0 := by simp [htail]

/-! ### The square-zero kernel -/

/-- **Stacks Project, Tag 0EVJ.** The global functions on `Spec A` killed by the modification
of the two-generator almost blowup square form an ideal of square zero. -/
@[stacks 0EVJ "kernel_square_zero"]
theorem modificationToBase_ker_sq_eq_bot (A : Type u) [CommRing A] (f₁ f₂ : A) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    RingHom.ker (Scheme.Γ.map (modificationToBase A f₁ f₂).op).hom ^ 2 = ⊥ := by
  let _ := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have hX (i : Fin 2) :
      Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X i) ∈
        modificationGrading A f₁ f₂ 1 := by
    show Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X i) ∈
      (MvPolynomial.homogeneousSubmodule (Fin 2) A 1).toAddSubgroup.map
        (Ideal.Quotient.mk (relationIdeal A f₁ f₂)).toAddMonoidHom
    exact AddSubgroup.mem_map.mpr ⟨MvPolynomial.X i,
      (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X A i), rfl⟩
  rw [pow_two]
  refine le_antisymm (Ideal.mul_le.2 fun x hx y hy => ?_) bot_le
  rw [RingHom.mem_ker] at hx hy
  set e := Scheme.ΓSpecIso (.of A)
  have key (i : Fin 2) (z : Γ(Spec (.of A), ⊤))
      (hz : (Scheme.Γ.map (modificationToBase A f₁ f₂).op).hom z = 0) :
      ∃ n : ℕ, Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X i) ^ n *
        Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C (e.hom.hom z)) = 0 :=
    exists_pow_mul_C_eq_zero_of_fromZero_eq_zero f₁ f₂ _ i
      (fromZero_eq_zero_of_global_kernel f₁ f₂ _ i (hX i) (by rwa [e.hom_inv_id_apply z]))
  obtain ⟨n, hn⟩ := key 0 x hx
  obtain ⟨m, hm⟩ := key 1 y hy
  obtain ⟨p, hp⟩ := exists_factor_chart_zero f₁ f₂ (e.hom.hom x) n hn
  obtain ⟨q, hq⟩ := exists_factor_chart_one f₁ f₂ (e.hom.hom y) m hm
  have hmul : e.hom.hom (x * y) = 0 :=
    (map_mul _ _ _).trans (mul_eq_zero_of_chart_factors f₁ f₂ _ _ p q hp hq)
  show x * y = 0
  rw [← e.hom_inv_id_apply (x * y), hmul, map_zero]
  rfl

end Stacks.AlmostBlowUp

end
