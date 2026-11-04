module

public import StacksFrontier.RingTheory.Rig.JacobianAlgebraizationMulti
public import StacksFrontier.RingTheory.Rig.Lifting

/-!
# Polynomial approximation and the comparison map of the multi-generator Jacobian algebra

Let `A` be a commutative ring, `I ⊆ A` a finitely generated ideal and `B` an `I`-adically
complete `A`-algebra of finite type modulo `I`, presented as `B = A⟨x₁, …, x_r⟩/J` by a
completed polynomial presentation `P`.  This file supplies the two remaining inputs for the
Jacobian criterion for algebraization, given the algebra

`C = A[z₁, …, z_t, x₁, …, x_r] / (z₁Δ - a₁^c, …, z_tΔ - a_t^c, f₁, …, f_m)`

of `StacksFrontier.RingTheory.Rig.JacobianAlgebraizationMulti`.

The first is approximation.  A restricted power series `g ∈ A⟨x₁, …, x_r⟩` agrees with an
honest polynomial `p ∈ A[x₁, …, x_r]` to any prescribed accuracy: all coefficients of `g - p`
can be made to lie in `I^n`.  Read through the presentation, this says that an element of `J`
is approximated modulo `I^n·B` by a polynomial, so the relations `f'_1, …, f'_m` used to build
`C` can be taken polynomial without changing anything modulo `I^n`.

The second is the comparison map.  Given `b, b', b₁, …, b_t ∈ B` with `b'Δ ≡ b` modulo `I^n·B`
and `b·b_k = a_k^c`, and given that each `f'_j` maps into `I^n·B`, there is a surjection

`ψ_n : C ⟶ B/I^nB`,  `x_i ↦ x_i`,  `z_k ↦ b_k b'`.

Surjectivity is the approximation statement again: every element of `B/I^nB` is the image of
a polynomial, because `A⟨x⟩ → B` is surjective and polynomials are dense.

## Main results

* `Rig.exists_mvPolynomial_coefficientProjection_sub_eq_zero` — a restricted power series is
  congruent to a polynomial modulo the coefficient ideal to the power `n`.
* `Rig.exists_mvPolynomial_sub_mem_map_pow` — the same, read through any `A`-algebra map out
  of the completed polynomial algebra: the difference lands in `I^n` times the target.
* `Rig.CompletedPolynomialPresentation.exists_mvPolynomial_approx` and
  `Rig.CompletedPolynomialPresentation.exists_mvPolynomial_approx_mem_restrictedKer` — the
  approximation for a completed polynomial presentation, and the form it takes for a family
  of elements of the kernel: the approximating polynomials map into `I^n·B`.
* `Rig.CompletedPolynomialPresentation.surjective_quotient_polynomial` — `B/I^nB` is generated
  over `A` by the images of the variables.
* `Rig.exists_algHom_multiJacobianAlgebra_quotient` — the surjection `ψ_n : C ⟶ B/I^nB`,
  together with its values on the `z`- and `x`-variables.

## Implementation notes

The approximation is stated through `RestrictedPowerSeries.coefficientProjection`, the
reduction `A⟨σ⟩ ⟶ (A/I^n)[σ]`, rather than through membership in the `n`-th power of the
coefficient ideal: the two agree for finitely generated `I`
(`RestrictedPowerSeries.mem_coefficientIdeal_pow_iff`), but elaborating a power of an ideal of
`A⟨σ⟩` exhausts the typeclass search in this import context, whereas the projection form needs
no instance at all.  The transport to a target ring is
`Rig.mem_map_pow_of_coefficientProjection_eq_zero`, which is where the finite generation of
`I` genuinely enters.

The hypothesis `b'Δ - b ∈ I^n·B` on the comparison map is weaker than the equality `b'Δ = b`,
and deliberately so: in the intended application `Δ` is the Jacobian determinant of the
*approximating* polynomials, which agrees only modulo `I^n` with the determinant of the
original relations that `b` was chosen to be divisible by.  The hypothesis `b·b_k = a_k^c` is
by contrast an exact equality, as it comes from an inclusion `I^c·B ⊆ b·B`.

The variable order follows `Rig.multiJacobianRelations`: the `z`-variables are the initial
segment, indexed by `Fin.castAdd`, and the `x`-variables the trailing one, indexed by
`Fin.natAdd`.  The map is built as `MvPolynomial.aeval` of the family assembled by
`Fin.addCases`, so its two defining properties are read off by `Fin.addCases_left` and
`Fin.addCases_right`.

## References

* [Stacks Project, Tag 0GAW](https://stacks.math.columbia.edu/tag/0GAW)
-/

@[expose] public noncomputable section

open MvPolynomial RestrictedPowerSeries

namespace Rig

universe u v w

section Approximation

variable {A : Type u} [CommRing A]

/-- **Polynomial approximation of a restricted power series.** Every `g ∈ A⟨σ⟩` is congruent
to a polynomial to any prescribed accuracy: there is `p ∈ A[σ]` all of whose differences with
`g` in each coefficient lie in `I^n`, that is, with `g - p` reducing to zero in `(A/I^n)[σ]`. -/
public theorem exists_mvPolynomial_coefficientProjection_sub_eq_zero (I : Ideal A) (σ : Type v)
    (n : ℕ) (g : RestrictedPowerSeries I σ) :
    ∃ p : MvPolynomial σ A,
      coefficientProjection I σ n (g - polynomialRingHom I σ p) = 0 := by
  obtain ⟨p, hp⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk (I ^ n))
    Ideal.Quotient.mk_surjective (coefficientProjection I σ n g)
  exact ⟨p, by rw [map_sub, coefficientProjection_polynomialRingHom, hp, sub_self]⟩

/-- Polynomial approximation read in a target ring: for an `A`-algebra map `F` out of the
completed polynomial algebra and any `g ∈ A⟨σ⟩`, there is a polynomial `p` with
`F(g) - F(p) ∈ I^n · Bc`.  Finite generation of `I` is what makes the `n`-th stage of the
completion the quotient by `I^n`. -/
public theorem exists_mvPolynomial_sub_mem_map_pow (I : Ideal A) (hI : I.FG) {σ : Type v}
    {Bc : Type w} [CommRing Bc] [Algebra A Bc]
    (F : AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
      (MvPolynomial σ A) →ₐ[A] Bc)
    (n : ℕ) (g : RestrictedPowerSeries I σ) :
    ∃ p : MvPolynomial σ A,
      coefficientProjection I σ n (g - polynomialRingHom I σ p) = 0 ∧
      F (adicCompletionAlgEquiv I σ g) - F (adicCompletionAlgEquiv I σ (polynomialAlgHom I σ p))
        ∈ (I ^ n).map (algebraMap A Bc) := by
  obtain ⟨p, hp⟩ := exists_mvPolynomial_coefficientProjection_sub_eq_zero I σ n g
  refine ⟨p, hp, ?_⟩
  have h := mem_map_pow_of_coefficientProjection_eq_zero I hI F n _ hp
  rwa [map_sub, map_sub] at h

end Approximation

section Presentation

variable {A : Type u} [CommRing A] {I : Ideal A} {B : AdicFiniteTypeAlgebra.{u, v} A I}

/-- Polynomial approximation along a completed polynomial presentation: every
`g ∈ A⟨x₁, …, x_r⟩` is congruent to a polynomial `p` modulo `I^n` in the coefficients, and the
images of `g` and `p` in `B` then differ by an element of `I^n·B`. -/
public theorem CompletedPolynomialPresentation.exists_mvPolynomial_approx
    (P : CompletedPolynomialPresentation I B) (hI : I.FG) (n : ℕ)
    (g : RestrictedPowerSeries I (Fin P.variableCount)) :
    ∃ p : MvPolynomial (Fin P.variableCount) A,
      coefficientProjection I (Fin P.variableCount) n
          (g - polynomialRingHom I (Fin P.variableCount) p) = 0 ∧
      P.restrictedToAlgHom g -
          P.restrictedToAlgHom (polynomialAlgHom I (Fin P.variableCount) p) ∈
        (I ^ n).map (algebraMap A B.carrier) :=
  exists_mvPolynomial_sub_mem_map_pow I hI P.toAlgHom n g

/-- **The polynomial relations `f'_1, …, f'_m`.** A family `g₁, …, g_m` of elements of the
kernel `J` of a completed polynomial presentation admits polynomial approximations `f'_j`,
agreeing with `g_j` modulo `I^n` in every coefficient, whose images in `B` lie in `I^n·B`.
These are the polynomials from which the multi-generator Jacobian algebra is built. -/
public theorem CompletedPolynomialPresentation.exists_mvPolynomial_approx_mem_restrictedKer
    (P : CompletedPolynomialPresentation I B) (hI : I.FG) (n : ℕ) {m : ℕ}
    (g : Fin m → RestrictedPowerSeries I (Fin P.variableCount))
    (hg : ∀ j, g j ∈ P.restrictedKer) :
    ∃ p : Fin m → MvPolynomial (Fin P.variableCount) A,
      (∀ j, coefficientProjection I (Fin P.variableCount) n
        (g j - polynomialRingHom I (Fin P.variableCount) (p j)) = 0) ∧
      ∀ j, P.restrictedToAlgHom (polynomialAlgHom I (Fin P.variableCount) (p j)) ∈
        (I ^ n).map (algebraMap A B.carrier) := by
  choose p hp hmem using fun j ↦ P.exists_mvPolynomial_approx hI n (g j)
  refine ⟨p, hp, fun j ↦ ?_⟩
  have h0 : P.restrictedToAlgHom (g j) = 0 := hg j
  simpa [h0] using neg_mem (hmem j)

/-- `B/I^nB` is generated over `A` by the images of the variables of a completed polynomial
presentation: every class is the image of a polynomial.  The completed presentation is
surjective, and a restricted power series is congruent to a polynomial modulo `I^n`. -/
public theorem CompletedPolynomialPresentation.surjective_quotient_polynomial
    (P : CompletedPolynomialPresentation I B) (hI : I.FG) (n : ℕ) :
    Function.Surjective fun p : MvPolynomial (Fin P.variableCount) A ↦
      Ideal.Quotient.mk ((I ^ n).map (algebraMap A B.carrier))
        (P.restrictedToAlgHom (polynomialAlgHom I (Fin P.variableCount) p)) := by
  intro y
  obtain ⟨β, rfl⟩ :=
    Ideal.Quotient.mk_surjective (I := (I ^ n).map (algebraMap A B.carrier)) y
  obtain ⟨g, rfl⟩ := P.restrictedToAlgHom_surjective β
  obtain ⟨p, -, hmem⟩ := P.exists_mvPolynomial_approx hI n g
  exact ⟨p, (Ideal.Quotient.eq.mpr hmem).symm⟩

end Presentation

section Comparison

variable {A : Type u} [CommRing A] {I : Ideal A} {B : AdicFiniteTypeAlgebra.{u, v} A I}

/-- **The comparison map `ψ_n : C ⟶ B/I^nB`.** Let `P` present `B = A⟨x₁, …, x_r⟩/J`, let
`f₁, …, f_m` be polynomials whose images in `B` lie in `I^n·B`, let `Δ` be their Jacobian
determinant formed from the first `m` variables, and let `b, b', b₁, …, b_t ∈ B` satisfy
`b'Δ ≡ b` modulo `I^n·B` and `b·b_k = a_k^c`.  Then the multi-generator Jacobian algebra
`C = A[z₁, …, z_t, x₁, …, x_r]/(z₁Δ - a₁^c, …, z_tΔ - a_t^c, f₁, …, f_m)` maps onto `B/I^nB`
by `x_i ↦ x_i` and `z_k ↦ b_k b'`.

The relation `z_kΔ - a_k^c` dies because `b_k b' Δ ≡ b_k b = a_k^c`, and each `f_j` dies by
hypothesis; surjectivity is that `B/I^nB` is generated by the images of the variables. -/
public theorem exists_algHom_multiJacobianAlgebra_quotient
    (P : CompletedPolynomialPresentation I B) (hI : I.FG) (n : ℕ) {m t : ℕ}
    (hm : m ≤ P.variableCount) (f : Fin m → MvPolynomial (Fin P.variableCount) A)
    (a : Fin t → A) (c : ℕ) (b b' : B.carrier) (bs : Fin t → B.carrier)
    (hf : ∀ j, P.restrictedToAlgHom (polynomialAlgHom I (Fin P.variableCount) (f j)) ∈
      (I ^ n).map (algebraMap A B.carrier))
    (hb : b' * P.restrictedToAlgHom
        (polynomialAlgHom I (Fin P.variableCount) (jacobian hm f).det) - b ∈
      (I ^ n).map (algebraMap A B.carrier))
    (hbs : ∀ k, b * bs k = algebraMap A B.carrier (a k ^ c)) :
    ∃ ψ : MultiJacobianAlgebra hm f a c →ₐ[A]
        B.carrier ⧸ (I ^ n).map (algebraMap A B.carrier),
      Function.Surjective ψ ∧
      (∀ k : Fin t,
        ψ (Ideal.Quotient.mk (Ideal.span (Set.range (multiJacobianRelations hm f a c)))
            (X (Fin.castAdd P.variableCount k))) =
          Ideal.Quotient.mk ((I ^ n).map (algebraMap A B.carrier)) (bs k * b')) ∧
      ∀ i : Fin P.variableCount,
        ψ (Ideal.Quotient.mk (Ideal.span (Set.range (multiJacobianRelations hm f a c)))
            (X (Fin.natAdd t i))) =
          Ideal.Quotient.mk ((I ^ n).map (algebraMap A B.carrier))
            (P.restrictedToAlgHom (polynomialAlgHom I (Fin P.variableCount) (X i))) := by
  classical
  set L : Ideal B.carrier := (I ^ n).map (algebraMap A B.carrier) with hL
  set xB : Fin P.variableCount → B.carrier := fun i ↦
    P.restrictedToAlgHom (polynomialAlgHom I (Fin P.variableCount) (X i)) with hxB
  set v : Fin (t + P.variableCount) → B.carrier ⧸ L :=
    Fin.addCases (fun k : Fin t ↦ Ideal.Quotient.mk L (bs k * b'))
      (fun i : Fin P.variableCount ↦ Ideal.Quotient.mk L (xB i)) with hv
  set φ : MvPolynomial (Fin (t + P.variableCount)) A →ₐ[A] B.carrier ⧸ L :=
    MvPolynomial.aeval v with hφ
  have hvl : ∀ k : Fin t, v (Fin.castAdd P.variableCount k) =
      Ideal.Quotient.mk L (bs k * b') := fun k ↦ Fin.addCases_left k
  have hvr : ∀ i : Fin P.variableCount, v (Fin.natAdd t i) =
      Ideal.Quotient.mk L (xB i) := fun i ↦ Fin.addCases_right i
  have hcomp : φ.comp (MvPolynomial.rename (R := A) (Fin.natAdd t)) =
      (Ideal.Quotient.mkₐ A L).comp
        (P.restrictedToAlgHom.comp (polynomialAlgHom I (Fin P.variableCount))) := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    rw [AlgHom.comp_apply, MvPolynomial.rename_X, hφ, MvPolynomial.aeval_X, hvr i]
    rfl
  have hren : ∀ p : MvPolynomial (Fin P.variableCount) A,
      φ (rename (Fin.natAdd t) p) =
        Ideal.Quotient.mk L
          (P.restrictedToAlgHom (polynomialAlgHom I (Fin P.variableCount) p)) :=
    fun p ↦ DFunLike.congr_fun hcomp p
  have hrel : ∀ j, φ (multiJacobianRelations hm f a c j) = 0 := by
    refine Fin.addCases (fun k ↦ ?_) (fun j ↦ ?_)
    · rw [multiJacobianRelations_castAdd, map_sub, map_mul, hren, hφ, MvPolynomial.aeval_X,
        MvPolynomial.aeval_C, hvl k, ← map_mul]
      have halg : algebraMap A (B.carrier ⧸ L) (a k ^ c) =
          Ideal.Quotient.mk L (algebraMap A B.carrier (a k ^ c)) := rfl
      have hbq : Ideal.Quotient.mk L (b' * P.restrictedToAlgHom
          (polynomialAlgHom I (Fin P.variableCount) (jacobian hm f).det)) =
          Ideal.Quotient.mk L b := Ideal.Quotient.eq.mpr hb
      rw [halg, mul_assoc, map_mul, hbq, ← map_mul, mul_comm (bs k) b, hbs k, sub_self]
    · rw [multiJacobianRelations_natAdd, hren]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr (hf j)
  have hkill : ∀ x ∈ Ideal.span (Set.range (multiJacobianRelations hm f a c)), φ x = 0 := by
    intro x hx
    have hle : Ideal.span (Set.range (multiJacobianRelations hm f a c)) ≤
        RingHom.ker φ.toRingHom := by
      refine Ideal.span_le.mpr ?_
      rintro y ⟨j, rfl⟩
      exact hrel j
    exact hle hx
  have hlift : ∀ x : MvPolynomial (Fin (t + P.variableCount)) A,
      Ideal.Quotient.liftₐ (Ideal.span (Set.range (multiJacobianRelations hm f a c))) φ hkill
        (Ideal.Quotient.mk (Ideal.span (Set.range (multiJacobianRelations hm f a c))) x) =
        φ x := fun _ ↦ rfl
  refine ⟨Ideal.Quotient.liftₐ _ φ hkill, ?_, fun k ↦ ?_, fun i ↦ ?_⟩
  · intro y
    obtain ⟨p, hp⟩ := P.surjective_quotient_polynomial hI n y
    refine ⟨Ideal.Quotient.mk _ (rename (Fin.natAdd t) p), ?_⟩
    rw [hlift, hren p]
    exact hp
  · rw [hlift, hφ, MvPolynomial.aeval_X, hvl k]
  · rw [hlift, hφ, MvPolynomial.aeval_X, hvr i]

end Comparison

end Rig

end
