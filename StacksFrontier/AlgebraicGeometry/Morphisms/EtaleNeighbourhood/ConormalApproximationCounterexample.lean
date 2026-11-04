module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ConormalApproximation
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Congruence of the coefficient maps alone does not control the conormal algebra

Stacks 0CAY produces, from a local `𝒪_{S,s}`-algebra map `σ : 𝒪_{T,t} → 𝒪_{S,s}^∧`, a pointed
finite type extension `(T', t') → (T, t)` through which `σ` factors and which controls the
conormal algebra of `Y_t` in `Y_{σ'}` for every `σ'` factoring through it. The extension is built
from a presentation of `Y` over `T` together with a generating set of *syzygies* among the images
of its relations, and only after a second application of Stacks 0CAX, at the level of that
extension, does the source compare two associated graded algebras.

This file shows that the intermediate extension is not an artefact of the proof: a congruence
`σ ≡ σ' mod 𝔪_s^N` between the two maps themselves, however large `N` is taken, never suffices.
Take `D` a commutative ring, `u ∈ D`, `I = (u)`, `C = D[a]` and the one-relation presentation
`B = C[x]/(a x)`. For `σ : a ↦ 0` the fibre `B ⊗_{C, σ} D` is `D[x]`, while for `σ' : a ↦ u^N` it
is `D[x]/(u^N x)`; the two maps agree modulo `I^N`, but multiplication by `x` annihilates the
degree `N` part of `Gr_I(D[x]/(u^N x))` and does not annihilate the degree `N` part of
`Gr_I(D[x])`.

## Main results

* `Stacks.ConormalApproximation.not_exists_uniform_congruence_bound`: no `N` has the property
  that any two ring maps `D[a] → D` agreeing modulo `I^N` give isomorphic `I`-adic associated
  graded modules of the two fibres of `B = D[a][x]/(a x)`, as soon as no power of `u` is divided
  by the next one.
* `Stacks.ConormalApproximation.not_exists_uniform_congruence_bound_of_isDomain`: the hypothesis
  on `u` holds in a domain for any nonzero nonunit, in particular for the uniformizer of a
  discrete valuation ring such as `𝒪_{S,s}^∧` for `S` a smooth curve.
* `Stacks.ConormalApproximation.not_exists_uniform_congruence_bound_int`: a fully explicit
  instance over the Noetherian ring `ℤ` with `I = (2)`, so the hypotheses of
  `exists_finiteType_coefficients_associatedGraded_equiv` are all met.

## Implementation notes

The invariant separating the two fibres is multiplication by the degree `0` class of `x`: the
relation `u^N x = 0` holds in the second fibre, so `x` kills `I^N M/I^{N+1} M` there, whereas in
`D[x]` the element `x u^N` is not in `I^{N+1} D[x]`. An `AssociatedGraded.GradedLinearEquiv` is
linear over the whole associated graded ring and preserves degrees, so it transports the
invariant.

`Stacks.ConormalApproximation.HasUniformConormalBound`, the hypothesis carried by the
scheme-level statement `exists_finiteType_pointed_extension_conormalAlgebra_iso`, is the
scheme-level form of the property refuted here, for the morphisms
`Spec(D[a][x]/(a x)) → Spec(D[a]) → Spec(D)`; the translation between the two forms is not
formalized in this file.

## References

* [Stacks Project, Tag 0CAY](https://stacks.math.columbia.edu/tag/0CAY)
* [Stacks Project, Tag 0CAX](https://stacks.math.columbia.edu/tag/0CAX)
-/

@[expose] public section

universe w

open AssociatedGraded

namespace Stacks.ConormalApproximation

variable {D : Type w} [CommRing D]

/-- The single relation `a * x` of the presentation `D[a][x]/(a x)`. -/
noncomputable def lineRelation (D : Type w) [CommRing D] :
    Fin 1 → MvPolynomial (Fin 1) (Polynomial D) :=
  fun _ => MvPolynomial.C Polynomial.X * MvPolynomial.X 0

/-- Each component of `lineRelation D` is the polynomial `a * x`. -/
@[simp]
theorem lineRelation_apply (j : Fin 1) :
    lineRelation D j = MvPolynomial.C Polynomial.X * MvPolynomial.X 0 := rfl

/-- For a ring map `σ : D[a] → D`, the relation map of `lineRelation D` sends a coefficient
vector `v` to `v 0 * (σ a * x)`. -/
theorem relationMapOfHom_lineRelation (σ : Polynomial D →+* D)
    (v : Fin 1 → MvPolynomial (Fin 1) D) :
    relationMapOfHom σ (lineRelation D) v =
      v 0 * (MvPolynomial.C (σ Polynomial.X) * MvPolynomial.X 0) := by
  simp [relationMapOfHom_apply]

/-- Specialising the coefficient `a` to `0` kills the relation: the fibre is all of `D[x]`. -/
theorem range_relationMapOfHom_eval_zero :
    LinearMap.range (relationMapOfHom (Polynomial.evalRingHom (0 : D)) (lineRelation D)) = ⊥ := by
  rw [LinearMap.range_eq_bot]
  refine LinearMap.ext fun v => ?_
  simp

/-- Specialising the coefficient `a` to `d` puts `d x` into the relation submodule. -/
theorem mem_range_relationMapOfHom_eval (d : D) :
    (MvPolynomial.C d * MvPolynomial.X 0 : MvPolynomial (Fin 1) D) ∈
      LinearMap.range (relationMapOfHom (Polynomial.evalRingHom d) (lineRelation D)) :=
  ⟨fun _ => 1, by simp⟩

/-- The `I`-adic filtration of a quotient module is the image of the filtration upstairs. -/
private theorem power_quotient {A : Type*} [CommRing A] (J R : Ideal A) (n : ℕ) :
    power (M := A ⧸ R) J n = (power (M := A) J n).map R.mkQ := by
  simp only [power, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]

/-- **No uniform congruence bound on the coefficient maps controls the conormal algebra.**
Let `D` be a commutative ring and `u ∈ D` an element no power of which is divisible by the next
power, let `I = (u)` and let `B = D[a][x]/(a x)`. Then for no `N` do all pairs of ring maps
`D[a] → D` agreeing modulo `I^N` give isomorphic `I`-adic associated graded modules of the two
fibres of `B`. In particular the hypothesis `HasUniformConormalBound` carried by the scheme-level
form of Stacks 0CAY cannot be discharged: the pointed finite type extension of the source, over
which it is the congruence of the *syzygy coefficients* that gets controlled, is essential. -/
theorem not_exists_uniform_congruence_bound (u : D) (hu : ∀ n : ℕ, ¬ u ^ (n + 1) ∣ u ^ n) :
    ¬ ∃ N : ℕ, 1 ≤ N ∧
        ∀ σ σ' : Polynomial D →+* D,
          (∀ y, σ y - σ' y ∈ (Ideal.span {u} : Ideal D) ^ N) →
          Nonempty (GradedLinearEquiv
            ((Ideal.span {u} : Ideal D).map
              (MvPolynomial.C : D →+* MvPolynomial (Fin 1) D))
            (MvPolynomial (Fin 1) D ⧸
              LinearMap.range (relationMapOfHom σ (lineRelation D)))
            (MvPolynomial (Fin 1) D ⧸
              LinearMap.range (relationMapOfHom σ' (lineRelation D)))) := by
  classical
  rintro ⟨N, -, h⟩
  set J : Ideal (MvPolynomial (Fin 1) D) :=
    (Ideal.span {u} : Ideal D).map (MvPolynomial.C : D →+* MvPolynomial (Fin 1) D) with hJ
  set R₁ : Ideal (MvPolynomial (Fin 1) D) :=
    LinearMap.range (relationMapOfHom (Polynomial.evalRingHom (0 : D)) (lineRelation D)) with hR₁
  set R₂ : Ideal (MvPolynomial (Fin 1) D) :=
    LinearMap.range (relationMapOfHom (Polynomial.evalRingHom (u ^ N)) (lineRelation D)) with hR₂
  have hJpow : ∀ k : ℕ, J ^ k = Ideal.span {(MvPolynomial.C (u ^ k) : MvPolynomial (Fin 1) D)} := by
    intro k
    have hmap : J = Ideal.span {(MvPolynomial.C u : MvPolynomial (Fin 1) D)} := by
      rw [hJ, Ideal.map_span]; simp
    rw [hmap, Ideal.span_singleton_pow, ← map_pow]
  have hcongr : ∀ y : Polynomial D,
      Polynomial.evalRingHom (0 : D) y - Polynomial.evalRingHom (u ^ N) y ∈
        (Ideal.span {u} : Ideal D) ^ N := by
    have hext : (Ideal.Quotient.mk ((Ideal.span {u} : Ideal D) ^ N)).comp
        (Polynomial.evalRingHom (0 : D)) =
        (Ideal.Quotient.mk ((Ideal.span {u} : Ideal D) ^ N)).comp
          (Polynomial.evalRingHom (u ^ N)) := by
      have hmemN : u ^ N ∈ (Ideal.span {u} : Ideal D) ^ N := by
        rw [Ideal.span_singleton_pow]
        exact Ideal.mem_span_singleton_self _
      refine Polynomial.ringHom_ext (fun a => by simp) ?_
      simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X, map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr hmemN).symm
    intro y
    have hy := RingHom.congr_fun hext y
    simp only [RingHom.comp_apply] at hy
    exact Ideal.Quotient.eq.mp hy
  obtain ⟨e⟩ := h _ _ hcongr
  have hX0mem : (MvPolynomial.X 0 : MvPolynomial (Fin 1) D) ∈
      power (M := MvPolynomial (Fin 1) D) J 0 := by simp
  have hkill : ∀ w : MvPolynomial (Fin 1) D ⧸ R₂,
      w ∈ power (M := MvPolynomial (Fin 1) D ⧸ R₂) J N →
      (MvPolynomial.X 0 : MvPolynomial (Fin 1) D) • w = 0 := by
    intro w hw
    rw [power_quotient] at hw
    obtain ⟨q, hq, rfl⟩ := hw
    rw [SetLike.mem_coe, ring_power_eq, hJpow N, Ideal.mem_span_singleton] at hq
    obtain ⟨c, rfl⟩ := hq
    rw [← map_smul, smul_eq_mul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hre : (MvPolynomial.X 0 : MvPolynomial (Fin 1) D) * (MvPolynomial.C (u ^ N) * c) =
        c * (MvPolynomial.C (u ^ N) * MvPolynomial.X 0) := by ring
    rw [hre, hR₂]
    exact Ideal.mul_mem_left _ _ (mem_range_relationMapOfHom_eval (u ^ N))
  have hzero : ∀ y : piece (M := MvPolynomial (Fin 1) D ⧸ R₂) J N,
      homogeneousSMul J (mk J 0 ⟨MvPolynomial.X 0, hX0mem⟩) y = 0 := by
    intro y
    induction y using Quotient.inductionOn with
    | _ y =>
      rw [show (Quotient.mk _ y : piece (M := MvPolynomial (Fin 1) D ⧸ R₂) J N) = mk J N y from
        rfl, homogeneousSMul_mk]
      refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
      show (MvPolynomial.X 0 : MvPolynomial (Fin 1) D) • (y : MvPolynomial (Fin 1) D ⧸ R₂) ∈
        power (M := MvPolynomial (Fin 1) D ⧸ R₂) J (0 + N + 1)
      rw [hkill _ y.property]
      exact Submodule.zero_mem _
  have hbot : R₁ = ⊥ := range_relationMapOfHom_eval_zero
  have hmem : (R₁.mkQ (MvPolynomial.C (u ^ N))) ∈
      power (M := MvPolynomial (Fin 1) D ⧸ R₁) J N := by
    rw [power_quotient]
    refine Submodule.mem_map_of_mem ?_
    rw [ring_power_eq, hJpow N]
    exact Ideal.mem_span_singleton_self _
  have hznz : homogeneousSMul J (mk J 0 ⟨MvPolynomial.X 0, hX0mem⟩)
      (mk J N ⟨R₁.mkQ (MvPolynomial.C (u ^ N)), hmem⟩) ≠ 0 := by
    rw [homogeneousSMul_mk]
    intro hcon
    have hmem0 := (Submodule.Quotient.mk_eq_zero _).mp hcon
    have hmem1 : (MvPolynomial.X 0 : MvPolynomial (Fin 1) D) •
        (R₁.mkQ (MvPolynomial.C (u ^ N))) ∈
        power (M := MvPolynomial (Fin 1) D ⧸ R₁) J (0 + N + 1) := hmem0
    have hsm : (MvPolynomial.X 0 : MvPolynomial (Fin 1) D) •
        (R₁.mkQ (MvPolynomial.C (u ^ N))) =
        R₁.mkQ (MvPolynomial.X 0 * MvPolynomial.C (u ^ N)) := by
      rw [← map_smul, smul_eq_mul]
    rw [hsm, power_quotient, Submodule.mem_map] at hmem1
    obtain ⟨q, hq, hqeq⟩ := hmem1
    have hsub : q - MvPolynomial.X 0 * MvPolynomial.C (u ^ N) ∈ R₁ :=
      (Submodule.Quotient.eq R₁).mp hqeq
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hsub
    rw [hsub, ring_power_eq, hJpow (0 + N + 1), Ideal.mem_span_singleton] at hq
    obtain ⟨c, hc⟩ := hq
    refine hu N ⟨MvPolynomial.coeff (Finsupp.single 0 1) c, ?_⟩
    have hL : MvPolynomial.coeff (Finsupp.single 0 1)
        (MvPolynomial.X 0 * MvPolynomial.C (u ^ N) : MvPolynomial (Fin 1) D) = u ^ N := by
      rw [mul_comm, MvPolynomial.coeff_C_mul]
      simp
    have hR : MvPolynomial.coeff (Finsupp.single 0 1)
        (MvPolynomial.C (u ^ (0 + N + 1)) * c : MvPolynomial (Fin 1) D) =
        u ^ (N + 1) * MvPolynomial.coeff (Finsupp.single 0 1) c := by
      rw [MvPolynomial.coeff_C_mul, zero_add]
    rw [← hL, ← hR, hc]
  obtain ⟨y, hy⟩ := e.map_grade N (mk J N ⟨R₁.mkQ (MvPolynomial.C (u ^ N)), hmem⟩)
  refine hznz ?_
  have key : DirectSum.of (fun k => piece (M := MvPolynomial (Fin 1) D) J k) 0
        (mk J 0 ⟨MvPolynomial.X 0, hX0mem⟩) •
      DirectSum.of (fun k => piece (M := MvPolynomial (Fin 1) D ⧸ R₁) J k) N
        (mk J N ⟨R₁.mkQ (MvPolynomial.C (u ^ N)), hmem⟩) = 0 := by
    apply e.toLinearEquiv.injective
    rw [map_smul, hy, of_smul_of, hzero y]
    simp
  rw [of_smul_of] at key
  simpa using congrArg (fun z => z (0 + N)) key

/-- In a domain a nonzero nonunit is never divided by its own next power, so
`not_exists_uniform_congruence_bound` applies. This covers the uniformizer of a discrete
valuation ring, hence the completed local ring `𝒪_{S,s}^∧` of a point of codimension one. -/
theorem not_exists_uniform_congruence_bound_of_isDomain [IsDomain D] (u : D) (hu0 : u ≠ 0)
    (hunit : ¬ IsUnit u) :
    ¬ ∃ N : ℕ, 1 ≤ N ∧
        ∀ σ σ' : Polynomial D →+* D,
          (∀ y, σ y - σ' y ∈ (Ideal.span {u} : Ideal D) ^ N) →
          Nonempty (GradedLinearEquiv
            ((Ideal.span {u} : Ideal D).map
              (MvPolynomial.C : D →+* MvPolynomial (Fin 1) D))
            (MvPolynomial (Fin 1) D ⧸
              LinearMap.range (relationMapOfHom σ (lineRelation D)))
            (MvPolynomial (Fin 1) D ⧸
              LinearMap.range (relationMapOfHom σ' (lineRelation D)))) := by
  refine not_exists_uniform_congruence_bound u fun n hdvd => ?_
  obtain ⟨c, hc⟩ := hdvd
  have hzero : u ^ n * (1 - u * c) = 0 := by
    rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ, ← hc, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact pow_ne_zero n hu0 h
  · exact hunit ⟨⟨u, c, (sub_eq_zero.mp h).symm, by
      rw [mul_comm]; exact (sub_eq_zero.mp h).symm⟩, rfl⟩

/-- A fully explicit instance of `not_exists_uniform_congruence_bound`, over the Noetherian ring
`ℤ` with `I = (2)`: every hypothesis of
`exists_finiteType_coefficients_associatedGraded_equiv` is satisfied, and still no uniform
congruence bound on the coefficient maps controls the associated graded module of the fibre. -/
theorem not_exists_uniform_congruence_bound_int :
    ¬ ∃ N : ℕ, 1 ≤ N ∧
        ∀ σ σ' : Polynomial ℤ →+* ℤ,
          (∀ y, σ y - σ' y ∈ (Ideal.span {(2 : ℤ)} : Ideal ℤ) ^ N) →
          Nonempty (GradedLinearEquiv
            ((Ideal.span {(2 : ℤ)} : Ideal ℤ).map
              (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 1) ℤ))
            (MvPolynomial (Fin 1) ℤ ⧸
              LinearMap.range (relationMapOfHom σ (lineRelation ℤ)))
            (MvPolynomial (Fin 1) ℤ ⧸
              LinearMap.range (relationMapOfHom σ' (lineRelation ℤ)))) :=
  not_exists_uniform_congruence_bound_of_isDomain (2 : ℤ) (by norm_num)
    (by simp [Int.isUnit_iff])

end Stacks.ConormalApproximation

end
