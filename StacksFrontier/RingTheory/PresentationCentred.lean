module

public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Presentations centred at a rational point

Let `A` be a finitely presented `R`-algebra and let `p` be an ideal of `A` such that every
element of `A` agrees modulo `p` with an element of `R` — a rational point of `Spec A` over
`Spec R`. Then `A` admits a finite presentation over `R` all of whose generators lie in `p`.

Such a presentation is the algebraic form of a closed immersion of an affine neighbourhood into
`A^n_R` taking the point to the origin.

## Main definitions

* `Algebra.Presentation.shiftVars` — the substitution `x_i ↦ x_i + c_i` of a polynomial ring.
* `Algebra.Presentation.shift` — the presentation obtained from `P` by subtracting the constants
  `c_i` from its generators.

## Main results

* `Algebra.Presentation.aeval_shiftVars` — evaluating a shifted polynomial at the generators
  shifted the other way gives the value of the original polynomial at the original generators.
* `Algebra.Presentation.exists_centred` — a finitely presented algebra with a rational point has
  a finite presentation whose generators lie in the corresponding ideal.

## Implementation notes

The substitution `x_i ↦ x_i + c_i` is an algebra automorphism of the polynomial ring, with
inverse `x_i ↦ x_i - c_i`. Composing the structure map of the shifted generators with it is the
structure map of `P`, so the kernel of the former is the image of the kernel of the latter, and
the relations of the shifted presentation are the shifted relations.

The hypothesis is that every element of `A` is congruent modulo `p` to an element of `R`, rather
than that `R → A ⧸ p` is an isomorphism, since that is all the construction uses.

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C4C](https://stacks.math.columbia.edu/tag/0C4C)
-/

@[expose] public section

open MvPolynomial

universe u v

namespace Algebra.Presentation

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- The substitution `x_i ↦ x_i + c_i`, as an algebra automorphism of the polynomial ring. -/
noncomputable def shiftVars {n : ℕ} (c : Fin n → R) :
    MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R :=
  AlgEquiv.ofAlgHom (aeval fun i => X i + C (c i)) (aeval fun i => X i - C (c i))
    (by apply MvPolynomial.algHom_ext; intro i; simp)
    (by apply MvPolynomial.algHom_ext; intro i; simp)

/-- `shiftVars c` evaluates a polynomial at the shifted variables `x_i + c_i`. -/
theorem shiftVars_apply {n : ℕ} (c : Fin n → R) (q : MvPolynomial (Fin n) R) :
    shiftVars c q = aeval (fun i => X i + C (c i)) q := rfl

/-- Evaluating a shifted polynomial at generators shifted the other way gives back the value of
the polynomial at the original generators. -/
theorem aeval_shiftVars {n : ℕ} (v : Fin n → A) (c : Fin n → R)
    (q : MvPolynomial (Fin n) R) :
    aeval (fun i => v i - algebraMap R A (c i)) (shiftVars c q) = aeval v q := by
  have hcomp : (aeval (R := R) fun i => v i - algebraMap R A (c i)).comp
      (shiftVars c).toAlgHom = aeval (R := R) v := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [shiftVars_apply]
  exact DFunLike.congr_fun hcomp q

/-- The generators of `P` shifted by constants still generate. -/
theorem surjective_aeval_sub_algebraMap {n m : ℕ} (P : Presentation R A (Fin n) (Fin m))
    (c : Fin n → R) :
    Function.Surjective (aeval (R := R) fun i => P.val i - algebraMap R A (c i)) := by
  intro a
  obtain ⟨q, hq⟩ := P.aeval_val_surjective a
  exact ⟨shiftVars c q, (aeval_shiftVars P.val c q).trans hq⟩

/-- The presentation obtained from `P` by subtracting the constants `c_i` from its generators.
Its relations are the relations of `P` substituted along `x_i ↦ x_i + c_i`. -/
noncomputable def shift {n m : ℕ} (P : Presentation R A (Fin n) (Fin m)) (c : Fin n → R) :
    Presentation R A (Fin n) (Fin m) where
  __ := Generators.ofSurjective (fun i => P.val i - algebraMap R A (c i))
    (surjective_aeval_sub_algebraMap P c)
  relation j := shiftVars c (P.relation j)
  span_range_relation_eq_ker := by
    have hker : RingHom.ker (aeval (R := R) fun i => P.val i - algebraMap R A (c i)) =
        (RingHom.ker (aeval (R := R) P.val)).map (shiftVars c).toRingHom := by
      refine le_antisymm (fun q hq => ?_) ?_
      · rw [RingHom.mem_ker] at hq
        have hr : (shiftVars c).symm q ∈ RingHom.ker (aeval (R := R) P.val) := by
          rw [RingHom.mem_ker, ← aeval_shiftVars P.val c ((shiftVars c).symm q),
            AlgEquiv.apply_symm_apply]
          exact hq
        have hmem := Ideal.mem_map_of_mem (shiftVars c).toRingHom hr
        rwa [show (shiftVars c).toRingHom ((shiftVars c).symm q) = q from
          (shiftVars c).apply_symm_apply q] at hmem
      · rw [Ideal.map_le_iff_le_comap]
        intro q hq
        rw [RingHom.mem_ker] at hq
        rw [Ideal.mem_comap, RingHom.mem_ker]
        change aeval (R := R) (fun i => P.val i - algebraMap R A (c i)) (shiftVars c q) = 0
        rw [aeval_shiftVars, hq]
    have hval : (Generators.ofSurjective (fun i => P.val i - algebraMap R A (c i))
        (surjective_aeval_sub_algebraMap P c)).val =
        fun i => P.val i - algebraMap R A (c i) := rfl
    rw [Generators.ker_eq_ker_aeval_val, hval, hker, ← Generators.ker_eq_ker_aeval_val,
      ← P.span_range_relation_eq_ker, Ideal.map_span, ← Set.range_comp]
    rfl

/-- The generators of `P.shift c` are the generators of `P` minus the constants `c_i`. -/
@[simp]
theorem shift_val {n m : ℕ} (P : Presentation R A (Fin n) (Fin m)) (c : Fin n → R) (i : Fin n) :
    (P.shift c).val i = P.val i - algebraMap R A (c i) := rfl

/-- **A finitely presented algebra with a rational point has a presentation centred there.** If
every element of `A` is congruent modulo `p` to an element of `R`, then `A` has a finite
presentation over `R` all of whose generators lie in `p`. -/
theorem exists_centred [Algebra.FinitePresentation R A] (p : Ideal A)
    (hp : ∀ a : A, ∃ r : R, a - algebraMap R A r ∈ p) :
    ∃ (n m : ℕ) (P : Presentation R A (Fin n) (Fin m)), ∀ i, P.val i ∈ p := by
  obtain ⟨n, m, ⟨P⟩⟩ := Presentation.exists_presentation_fin R A
  choose c hc using fun i : Fin n => hp (P.val i)
  exact ⟨n, m, P.shift c, fun i => hc i⟩

end Algebra.Presentation

end
